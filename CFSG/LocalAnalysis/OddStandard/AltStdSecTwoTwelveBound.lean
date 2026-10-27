module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecFarCent

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv Equiv.Perm CFSG.OddStandard.AltStdBal

section Bound

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {n : ℕ} {Q : Subgroup G} {z u : G}

theorem eq_one_or_eq_of_mem_zpowers_two {X : Type*} [Group X] {y w : X} (hy : orderOf y = 2)
    (hw : w ∈ zpowers y) : w = 1 ∨ w = y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hw
  have hy' : (orderOf y : ℤ) = 2 := by rw [hy]; rfl
  rw [← zpow_mod_orderOf, hy']
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

theorem card_dvd_of_caseI (h : Setting G L n) (d : Cyc L Q z) (T : ShapeTwo L Q z u)
    (e : L ≃* alternatingGroup (Fin n)) (hn : 11 ≤ n) {S₀ : Finset (Fin n)} (hS₀ : S₀.card = 3)
    (hI : CaseIAt e z S₀) {x : G} (hx : x ∈ centralizer ({z} : Set G))
    (hτ : (permOf h d e hx).IsSwap) (hfix : ∀ i ∈ S₀, permOf h d e hx i = i)
    {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPR : P ≤ centralizer (corr (X := G) e (altSub S₀) : Set G))
    (hPx : P ≤ centralizer ({x} : Set G)) : Nat.card P ∣ 4 * (n - 5).factorial := by
  classical
  obtain ⟨ht, hcen⟩ := hI
  set R : Subgroup G := corr (X := G) e (altSub S₀) with hR
  set C : Subgroup G := centralizer (R : Set G) with hC
  set O : Subgroup ↥C := CFSG.oddCore ↥C with hO
  set π : ↥C →* Sec G R := QuotientGroup.mk' O with hπ
  set zb : Sec G R := QuotientGroup.mk ⟨z, ht⟩ with hzb
  have hSc : S₀ᶜ.card = n - 3 := by rw [card_compl_fin, hS₀]
  have hex : ExactShape z L n := exactShape_of_setting h d T.card
  obtain ⟨hzord, ⟨eB⟩, -, hnorm, hcc⟩ := exactShape_section_three hex e hS₀ (by omega) ht
  have hzc : centralizer ({zb} : Set (Sec G R)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [mem_centralizer_singleton_iff]
    exact Subgroup.mem_center_iff.1 hcen y
  have hXcard : Nat.card (Sec G R) ≤ 2 * (n - 3).factorial := by
    have hle := hnorm
    rw [hzc] at hle
    have h1 := card_le_of_le_normalizer eB (by omega) hle
    have h2 := hcc
    rw [hzc, inf_top_eq] at h2
    rw [top_inf_eq, h2, Nat.card_zpowers, hzord, Subgroup.card_top,
      show n - S₀.card = n - 3 by rw [hS₀]] at h1
    exact h1
  set K : Subgroup (Sec G R) := zpowers zb with hK
  have hKc : K ≤ center (Sec G R) := by
    rw [hK, zpowers_le]
    exact hcen
  have hKn : K.Normal := Subgroup.normal_of_le_center hKc
  have hKcard : Nat.card K = 2 := by rw [hK, Nat.card_zpowers, hzord]
  set θ := thetaHom h d T e S₀ with hθ
  have hθinj : Function.Injective θ := thetaHom_injective h d T e (by omega)
  set φ : Perm ↥S₀ᶜ →* Sec G R ⧸ K := (QuotientGroup.mk' K).comp θ with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    have hmem : θ σ ∈ K := (QuotientGroup.eq_one_iff _).1 hσ
    rcases eq_one_or_eq_of_mem_zpowers_two hzord hmem with h1 | h1
    · exact hθinj (h1.trans (map_one θ).symm)
    · exact absurd h1 (thetaHom_ne_z h d T e S₀ ht σ)
  have hφbij : Function.Bijective φ := by
    refine (Nat.bijective_iff_injective_and_card φ).2 ⟨hφinj, le_antisymm ?_ ?_⟩
    · exact Nat.card_le_card_of_injective φ hφinj
    · have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
      rw [hKcard] at h1
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := ↥S₀ᶜ), Fintype.card_coe, hSc]
      omega
  set eφ : Perm ↥S₀ᶜ ≃* Sec G R ⧸ K := MulEquiv.ofBijective φ hφbij with heφ
  obtain ⟨σ, hσ⟩ := exists_ofSubtype_eq_of_fix (F := S₀ᶜ) (f := permOf h d e hx)
    (fun i hi => hfix i (by simpa using hi))
  have hσs : σ.IsSwap := by
    rw [isSwap_iff_cycleType, ← cycleType_ofSubtype, hσ]
    exact isSwap_iff_cycleType.1 hτ
  have hxR : x ∈ C := by
    rw [hC, mem_centralizer_iff]
    intro r hr
    exact (comm_of_mem_corr_of_permOf_fix h d e hx hfix hr).symm
  set xb : Sec G R := π ⟨x, hxR⟩ with hxb
  have hxbφ : QuotientGroup.mk' K xb = eφ σ := by
    rw [heφ, MulEquiv.ofBijective_apply, hφ, MonoidHom.comp_apply]
    have hκ : kappa h d T e S₀ σ = (swapIota h d T e (permOf h d e hx) : G) := by
      rw [kappa_apply, hσ]
    rcases eq_swapIota_or h d T e hx with h1 | h1
    · have h2 : (⟨x, hxR⟩ : ↥C) = ⟨kappa h d T e S₀ σ, kappa_mem_centralizer_root h d T e S₀ σ⟩ :=
        Subtype.ext (h1.trans hκ.symm)
      rw [hxb, h2, hθ, thetaHom_apply]
      rfl
    · have h3 : x = z * kappa h d T e S₀ σ := h1.trans (by rw [← hκ])
      have h2 : (⟨x, hxR⟩ : ↥C) = ⟨z, ht⟩ * ⟨kappa h d T e S₀ σ,
          kappa_mem_centralizer_root h d T e S₀ σ⟩ := Subtype.ext h3
      rw [hxb, h2, map_mul, map_mul]
      have hzK : QuotientGroup.mk' K (π ⟨z, ht⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).2 (mem_zpowers zb)
      rw [hzK, one_mul, hθ, thetaHom_apply]
      rfl
  set P' : Subgroup ↥C := P.subgroupOf C with hP'
  have hP'p : IsPGroup 2 P' := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPR).symm
  have hP'card : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  have hOodd : Odd (Nat.card O) :=
    ClassicalInvolution.QuaternionStructure.odd_natCard_oddCore ↥C
  set f₁ : ↥P' →* Sec G R := π.comp P'.subtype with hf₁
  have hf₁inj : Function.Injective f₁ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hpO : (p : ↥C) ∈ O := (QuotientGroup.eq_one_iff _).1 hp
    have hcop : Nat.Coprime (Nat.card P') (Nat.card O) := by
      obtain ⟨a, ha⟩ := hP'p.exists_card_eq
      rw [ha]
      exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 hOodd)
    have hdisj := Subgroup.disjoint_of_coprime_natCard hcop
    exact Subtype.ext (Subgroup.disjoint_def.1 hdisj p.2 hpO)
  set Pb : Subgroup (Sec G R) := f₁.range with hPb
  have hPbcard : Nat.card Pb = Nat.card P :=
    (Nat.card_congr (MonoidHom.ofInjective hf₁inj).toEquiv).symm.trans hP'card
  have hPbx : ∀ y ∈ Pb, y * xb = xb * y := by
    rintro _ ⟨p, rfl⟩
    rw [hf₁, MonoidHom.comp_apply, hxb, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hpP : ((p : ↥C) : G) ∈ P := p.2
    exact mem_centralizer_singleton_iff.1 (hPx hpP)
  set f₂ : ↥Pb →* Sec G R ⧸ K := (QuotientGroup.mk' K).comp Pb.subtype with hf₂
  have hk : Nat.card f₂.ker ∣ 2 := by
    rw [← hKcard]
    refine Subgroup.card_dvd_of_injective
      ({ toFun := fun k => ⟨((k : ↥Pb) : Sec G R), (QuotientGroup.eq_one_iff _).1 k.2⟩
         map_one' := rfl
         map_mul' := fun _ _ => rfl } : ↥f₂.ker →* ↥K) ?_
    intro a b hab
    have h1 : ((a : ↥Pb) : Sec G R) = ((b : ↥Pb) : Sec G R) :=
      congrArg (fun k : ↥K => (k : Sec G R)) hab
    exact Subtype.ext (Subtype.ext h1)
  have hrange : f₂.range ≤ centralizer ({eφ σ} : Set (Sec G R ⧸ K)) := by
    rintro _ ⟨y, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hxbφ, hf₂, MonoidHom.comp_apply, ← map_mul, ← map_mul]
    congr 1
    exact hPbx y y.2
  have hr : Nat.card f₂.range ∣ 2 * (n - 5).factorial := by
    have h1 : (f₂.range.map eφ.symm.toMonoidHom) ≤ centralizer ({σ} : Set (Perm ↥S₀ᶜ)) := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' := mem_centralizer_singleton_iff.1 (hrange hy)
      rw [mem_centralizer_singleton_iff]
      apply eφ.injective
      simp only [MulEquiv.coe_toMonoidHom, map_mul, MulEquiv.apply_symm_apply]
      exact hy'
    have h2 := Subgroup.card_dvd_of_le h1
    rw [Subgroup.card_map_of_injective eφ.symm.injective, nat_card_centralizer_of_isSwap hσs,
      Fintype.card_coe, hSc, show n - 3 - 2 = n - 5 by omega] at h2
    exact h2
  have hmul : Nat.card Pb = Nat.card f₂.ker * Nat.card f₂.range := by
    have := Subgroup.card_mul_index f₂.ker
    rw [Subgroup.index_ker] at this
    exact this.symm
  rw [← hPbcard, hmul, show 4 * (n - 5).factorial = 2 * (2 * (n - 5).factorial) by ring]
  exact Nat.mul_dvd_mul hk hr

end Bound

end CFSG.OddStandard.AltStdSec
