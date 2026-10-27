module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81P2

public section

namespace CFSG.ComponentClassification.CatLeafProof.Q81P2

open CFSG Subgroup CFSG.ComponentClassification.CatFactsL4U4.OutInv
open CFSG.ComponentClassification.HarrisLit

variable {X : Type} [Group X]

theorem map_fusionZStar_eq (σ : MulAut X) :
    (Open.fusionZStar X).map (σ : X →* X) = Open.fusionZStar X := by
  have hO : ∀ (τ : MulAut X) (o : X), o ∈ pPrimeCore 2 X → τ o ∈ pPrimeCore 2 X := by
    intro τ o ho
    have h := Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (pPrimeCore 2 X).Characteristic) τ
    rw [← h]
    exact Subgroup.mem_map_of_mem _ ho
  have key : ∀ (τ : MulAut X) (z : X), z ∈ Open.fusionZStar X → τ z ∈ Open.fusionZStar X := by
    intro τ z hz
    rw [FooteLit.mem_fusionZStar_iff_forall] at hz ⊢
    intro g
    have h := hO τ _ (hz (τ.symm g))
    rwa [map_mul, map_inv, map_mul, map_mul, MulEquiv.apply_symm_apply] at h
  refine le_antisymm ?_ fun z hz => ?_
  · rintro _ ⟨z, hz, rfl⟩
    exact key σ z hz
  · exact ⟨σ.symm z, key σ.symm z hz, MulEquiv.apply_symm_apply σ z⟩

@[expose] noncomputable def zStarAut (σ : MulAut X) : MulAut (X ⧸ Open.fusionZStar X) :=
  QuotientGroup.congr (Open.fusionZStar X) (Open.fusionZStar X) σ (map_fusionZStar_eq σ)

theorem zStarAut_mk (σ : MulAut X) (y : X) :
    zStarAut σ (y : X ⧸ Open.fusionZStar X) = (σ y : X ⧸ Open.fusionZStar X) :=
  QuotientGroup.congr_mk _ _ _ _ y

theorem zStarAut_mul_self {σ : MulAut X} (hσ : σ * σ = 1) : zStarAut σ * zStarAut σ = 1 := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.mul_apply, zStarAut_mk, zStarAut_mk, ← MulAut.mul_apply, hσ, MulAut.one_apply,
      MulAut.one_apply]

theorem exists_fixed_mul {σ : MulAut X} (hσ : σ * σ = 1) (y : X)
    (hw : Odd (orderOf (y⁻¹ * σ y))) :
    σ (y * (y⁻¹ * σ y) ^ ((orderOf (y⁻¹ * σ y) + 1) / 2)) =
      y * (y⁻¹ * σ y) ^ ((orderOf (y⁻¹ * σ y) + 1) / 2) := by
  set w := y⁻¹ * σ y with hwdef
  have hσw : σ w = w⁻¹ := by
    rw [hwdef, map_mul, map_inv, ← MulAut.mul_apply, hσ, MulAut.one_apply, mul_inv_rev, inv_inv]
  have hσy : σ y = y * w := by rw [hwdef, mul_inv_cancel_left]
  obtain ⟨k, hk⟩ := hw
  have hk' : (orderOf w + 1) / 2 = k + 1 := by omega
  have h1 : w ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one w
  rw [hk', map_mul, map_pow, hσw, hσy, inv_pow, mul_assoc]
  congr 1
  rw [mul_inv_eq_iff_eq_mul, ← pow_add, show k + 1 + (k + 1) = 2 * k + 1 + 1 by ring, pow_succ,
    h1, one_mul]

variable [Finite X]

theorem isPGroup_fixSub_quotient {σ : MulAut X} (hσ : σ * σ = 1)
    {β : MulAut (X ⧸ Open.fusionZStar X)}
    (hβ : ∀ y : X, β (y : X ⧸ Open.fusionZStar X) = (σ y : X ⧸ Open.fusionZStar X))
    (hC : IsPGroup 2 (↥(fixSub σ) ⧸ pPrimeCore 2 ↥(fixSub σ))) :
    IsPGroup 2 (↥(fixSub β) ⧸ pPrimeCore 2 ↥(fixSub β)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Q81.isPGroup_quotient_iff] at hC ⊢
  set Z := Open.fusionZStar X with hZ
  set O := pPrimeCore 2 X with hOdef
  have hOZ : O ≤ Z := by
    rw [hOdef, hZ, ← UnbalancingLocal.fusionOddCore_eq_pPrimeCore]
    exact FooteLit.fusionOddCore_le_fusionZStar
  have hOodd : Odd (Nat.card O) := Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hπ : ∀ c : ↥(fixSub σ), ((c : X) : X ⧸ Z) ∈ fixSub β := fun c => by
    rw [mem_fixSub, hβ, mem_fixSub.mp c.2]
  set π : ↥(fixSub σ) →* ↥(fixSub β) :=
    ((QuotientGroup.mk' Z).comp (fixSub σ).subtype).codRestrict _ hπ with hπdef
  set I := (pPrimeCore 2 ↥(fixSub σ)).map π with hI
  have hIodd : Nat.Coprime 2 (Nat.card I) :=
    Nat.Coprime.coprime_dvd_right (card_map_dvd _ _) pPrimeCore_coprime_card
  have key : ∀ f : ↥(fixSub β), Odd (orderOf f) → f ∈ I := by
    intro f hf
    have hf' : Odd (orderOf (f : X ⧸ Z)) := by rwa [Subgroup.orderOf_coe]
    obtain ⟨y, hyf, hy⟩ := FooteLit.exists_odd_preimage Z hf'
    have hfix : β (y : X ⧸ Z) = (y : X ⧸ Z) := by rw [hyf]; exact mem_fixSub.mp f.2
    rw [hβ, QuotientGroup.eq] at hfix
    set w := y⁻¹ * σ y with hwdef
    have hwZ : w ∈ Z := by
      have h := inv_mem hfix
      rwa [mul_inv_rev, inv_inv] at h
    have hwO : w ∈ O := by
      set q := QuotientGroup.mk' O with hq
      have hcen : q w ∈ center (X ⧸ O) := by
        rw [mem_center_iff]
        intro g
        obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective O g
        rw [← map_mul, ← map_mul, hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq]
        exact (FooteLit.mem_fusionZStar_iff_forall w).mp hwZ g'
      obtain ⟨k, hk⟩ := isPGroup_center_of_pPrimeCore_eq_bot
        (pPrimeCore_quotient_pPrimeCore_eq_bot 2 (G := X)) ⟨q w, hcen⟩
      have hk' : q w ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        rwa [Subgroup.coe_pow] at this
      have hyw : (y * w) ^ orderOf y = 1 := by
        rw [hwdef, mul_inv_cancel_left, ← map_pow, pow_orderOf_eq_one, map_one]
      have hqn : q w ^ orderOf y = 1 := by
        have h1 := congrArg q hyw
        have hc : Commute (q y) (q w) := mem_center_iff.mp hcen (q y)
        rw [map_pow, map_mul, hc.mul_pow, ← map_pow, pow_orderOf_eq_one, map_one,
          one_mul] at h1
        exact h1
      have hodd : Odd (orderOf (q w)) := Odd.of_dvd_nat hy (orderOf_dvd_of_pow_eq_one hqn)
      have h1 : orderOf (q w) = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hodd))
          (orderOf_dvd_of_pow_eq_one hk')
      rw [orderOf_eq_one_iff, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hwodd : Odd (orderOf w) := by
      have h := orderOf_dvd_natCard (⟨w, hwO⟩ : O)
      rw [Subgroup.orderOf_mk] at h
      exact Odd.of_dvd_nat hOodd h
    set m := w ^ ((orderOf w + 1) / 2) with hm
    have hmO : m ∈ O := pow_mem hwO _
    have hg : σ (y * m) = y * m := exists_fixed_mul hσ y hwodd
    have hgn : (y * m) ^ orderOf y ∈ O := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
        (QuotientGroup.eq_one_iff m).mpr hmO, mul_one, ← QuotientGroup.mk_pow,
        pow_orderOf_eq_one, QuotientGroup.mk_one]
    have hgo : Odd (orderOf (y * m)) := by
      have h1 : (y * m) ^ (orderOf y * Nat.card O) = 1 := by
        rw [pow_mul]
        have h2 := pow_card_eq_one' (G := O) (x := ⟨_, hgn⟩)
        have h3 := congrArg Subtype.val h2
        rwa [Subgroup.coe_pow] at h3
      exact Odd.of_dvd_nat (hy.mul hOodd) (orderOf_dvd_of_pow_eq_one h1)
    have hgC : (⟨y * m, mem_fixSub.mpr hg⟩ : ↥(fixSub σ)) ∈ pPrimeCore 2 ↥(fixSub σ) :=
      hC _ (by rw [Subgroup.orderOf_mk]; exact hgo)
    refine ⟨_, hgC, Subtype.ext ?_⟩
    change ((y * m : X) : X ⧸ Z) = (f : X ⧸ Z)
    rw [← hyf, QuotientGroup.eq, show (y * m)⁻¹ * y = m⁻¹ by group]
    exact hOZ (inv_mem hmO)
  set S : Set ↥(fixSub β) := {f | Odd (orderOf f)} with hS
  have hMI : normalClosure S ≤ I := by
    change closure (Group.conjugatesOfSet S) ≤ I
    rw [closure_le]
    intro c hc
    obtain ⟨a, ha, hac⟩ := Group.mem_conjugatesOfSet_iff.mp hc
    obtain ⟨u, rfl⟩ := isConj_iff.mp hac
    refine key _ ?_
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact ha
  have hMle : normalClosure S ≤ pPrimeCore 2 ↥(fixSub β) :=
    le_sSup ⟨normalClosure_normal, Nat.Coprime.coprime_dvd_right (card_dvd_of_le hMI) hIodd⟩
  intro f hf
  exact hMle (subset_normalClosure hf)

theorem isPGroup_fixSub_zStarAut {σ : MulAut X} (hσ : σ * σ = 1)
    (hC : IsPGroup 2 (↥(fixSub σ) ⧸ pPrimeCore 2 ↥(fixSub σ))) :
    IsPGroup 2 (↥(fixSub (zStarAut σ)) ⧸ pPrimeCore 2 ↥(fixSub (zStarAut σ))) :=
  isPGroup_fixSub_quotient hσ (zStarAut_mk σ) hC

end CFSG.ComponentClassification.CatLeafProof.Q81P2
