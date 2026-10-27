module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallA10Act
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aFStar
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerIsoCorrSylowGrowth
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinTransport

public section

namespace CFSG.ComponentClassification.CatFactsSmall

namespace A10

open CFSG Subgroup CFSG.ComponentClassification.GSThmB CFSG.ComponentClassification.UnbalancedLayer
open Equiv

variable {H : Type} [Group H] [Finite H] {h : Hyp52 H} (hKa : conjugate h.K h.a = h.K)
  (eK : OddBar h.K ≃* alternatingGroup (Fin 10))

theorem mem_of_sign_eq_one {w : h.W} (hs : Perm.sign (rhoW h hKa eK w) = 1) :
    (w : H) ∈ h.K ⊔ coreActionKernel h.K := by
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (eK.symm ⟨_, hs⟩)
  have h1 : rhoW h hKa eK (w * (⟨k, K_le_W h k.2⟩ : h.W)⁻¹) = 1 := by
    rw [map_mul, map_inv, rhoW_of_mem_K, hk, MulEquiv.apply_symm_apply]
    exact mul_inv_cancel _
  have h2 := (rhoW_eq_one_iff hKa eK _).1 h1
  have h3 : (w : H) = ((w * (⟨k, K_le_W h k.2⟩ : h.W)⁻¹ : h.W) : H) * (k : H) := by
    simp
  rw [h3]
  exact mul_mem (mem_sup_right h2) (mem_sup_left k.2)

theorem rhoBar_surjective {w : h.W} (hs : Perm.sign (rhoW h hKa eK w) = -1) :
    Function.Surjective (rhoBar hKa eK) := by
  have hA : ∀ τ : Perm (Fin 10), Perm.sign τ = 1 → ∃ y, rhoBar hKa eK y = τ := by
    intro τ hτ
    obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (eK.symm ⟨τ, hτ⟩)
    refine ⟨wbarMk h.B ⟨k, K_le_W h k.2⟩, ?_⟩
    rw [rhoBar_mk, rhoW_of_mem_K, hk, MulEquiv.apply_symm_apply]
  intro σ
  rcases Int.units_eq_one_or (Perm.sign σ) with hσ | hσ
  · exact hA σ hσ
  · obtain ⟨y, hy⟩ := hA ((rhoW h hKa eK w)⁻¹ * σ) (by rw [map_mul, map_inv, hs, hσ]; decide)
    exact ⟨wbarMk h.B w * y, by rw [map_mul, hy, rhoBar_mk, mul_inv_cancel_left]⟩

theorem odd_orderOf_of_rhoBar_eq_one {z : Wbar h.B} (hz : rhoBar hKa eK z = 1) :
    Odd (orderOf z) := by
  by_contra he
  obtain ⟨j, hj⟩ := Nat.not_odd_iff_even.1 he
  have hpos := orderOf_pos z
  have hzj : z ^ j * z ^ j = 1 := by rw [← pow_add, ← hj, pow_orderOf_eq_one]
  have hzj1 : z ^ j ≠ 1 := by
    intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hj] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  exact hzj1 (eq_one_of_rhoBar_eq_one hKa eK (by rw [map_pow, hz, one_pow]) hzj)

theorem exists_lift_involution (hsurj : Function.Surjective (rhoBar hKa eK))
    {σ : Perm (Fin 10)} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    ∃ y : Wbar h.B, rhoBar hKa eK y = σ ∧ y * y = 1 ∧ y ≠ 1 := by
  obtain ⟨y₀, hy₀⟩ := hsurj σ
  have hz : rhoBar hKa eK (y₀ * y₀) = 1 := by rw [map_mul, hy₀, hσ2]
  obtain ⟨j, hj⟩ := odd_orderOf_of_rhoBar_eq_one hKa eK hz
  refine ⟨y₀ ^ (2 * j + 1), ?_, ?_, ?_⟩
  · rw [map_pow, hy₀, pow_succ, pow_mul, sq, hσ2, one_pow, one_mul]
  · rw [← pow_add, show 2 * j + 1 + (2 * j + 1) = 2 * (2 * j + 1) by ring, pow_mul, sq, ← hj,
      pow_orderOf_eq_one]
  · intro h1
    apply hσ1
    have := congrArg (rhoBar hKa eK) h1
    rwa [map_pow, hy₀, pow_succ, pow_mul, sq, hσ2, one_pow, one_mul, map_one] at this

abbrev Kbar (h : Hyp52 H) : Subgroup (Wbar h.B) := wbarImage h.B h.K

include hKa in
theorem Kbar_normal : (Kbar h).Normal := by
  have : (h.K.subgroupOf h.W).Normal :=
    (normal_subgroupOf_iff_le_normalizer (K_le_W h)).2 (W_le_normalizer_K h hKa)
  exact this.map _ (QuotientGroup.mk'_surjective _)

theorem eq_of_rhoBar_eq {u v : Wbar h.B} (hu : u ∈ Kbar h) (hv : v ∈ Kbar h)
    (huv : rhoBar hKa eK u = rhoBar hKa eK v) : u = v := by
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  rw [rhoBar_mk, rhoBar_mk] at huv
  rw [SetLike.mem_coe, mem_subgroupOf] at hu' hv'
  exact wbarMk_eq_of_rhoW_eq hKa eK (k₁ := ⟨u', hu'⟩) (k₂ := ⟨v', hv'⟩) huv

theorem mem_centralizer_of_rhoBar {X : Subgroup (Wbar h.B)} (hX : X ≤ Kbar h) {y : Wbar h.B}
    (hy : rhoBar hKa eK y ∈ centralizer ((X.map (rhoBar hKa eK)) : Set (Perm (Fin 10)))) :
    y ∈ centralizer (X : Set (Wbar h.B)) := by
  rw [mem_centralizer_iff] at hy ⊢
  intro x hx
  have h1 := hy _ ⟨x, hx, rfl⟩
  have hn := Kbar_normal hKa (h := h)
  have hyx : y⁻¹ * x * y ∈ Kbar h := by
    have := hn.conj_mem x (hX hx) y⁻¹
    rwa [inv_inv] at this
  have h2 : rhoBar hKa eK (y⁻¹ * x * y) = rhoBar hKa eK x := by
    rw [map_mul, map_mul, map_inv, mul_assoc, h1, ← mul_assoc, inv_mul_cancel, one_mul]
  have h3 := eq_of_rhoBar_eq hKa eK hyx (hX hx) h2
  calc x * y = y * (y⁻¹ * x * y) := by group
    _ = y * x := by rw [h3]

include hKa in
theorem JB_le_K : GSLit.fixedLayer h.J h.B ≤ h.K := by
  rw [← h.V_eq_K hKa]
  exact B5a.fixedLayer_le_V h

include hKa in
theorem JBbar_le_Kbar : wbarImage h.B (GSLit.fixedLayer h.J h.B) ≤ Kbar h := by
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨x, JB_le_K hKa hx, rfl⟩

noncomputable abbrev Lsub : Subgroup (Perm (Fin 10)) :=
  (wbarImage h.B (GSLit.fixedLayer h.J h.B)).map (rhoBar hKa eK)

theorem L_le_alt : Lsub hKa eK ≤ alternatingGroup (Fin 10) := by
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, mem_subgroupOf] at hx
  have hxK : (x : H) ∈ h.K := JB_le_K hKa hx
  rw [rhoBar_mk]
  show rhoW h hKa eK ⟨(⟨x, hxK⟩ : h.K), K_le_W h hxK⟩ ∈ _
  rw [rhoW_of_mem_K]
  exact (eK _).2

theorem L_perfect : ⁅Lsub hKa eK, Lsub hKa eK⁆ = Lsub hKa eK := by
  have hp : ⁅wbarImage h.B (GSLit.fixedLayer h.J h.B), wbarImage h.B (GSLit.fixedLayer h.J h.B)⁆ =
      wbarImage h.B (GSLit.fixedLayer h.J h.B) :=
    Subgroup.isPerfect_iff.1 h.isStandard_bar.1.1
  rw [Lsub, ← map_commutator, hp]

theorem card_L_core (eJ : OddBar h.J ≃* alternatingGroup (Fin 6)) :
    Nat.card (Lsub hKa eK ⧸ pPrimeCore 2 (Lsub hKa eK)) = 360 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set JB := GSLit.fixedLayer h.J h.B with hJB
  have hJBK : JB ≤ h.K := JB_le_K hKa
  have hBJ : h.B ≤ coreActionKernel h.J := h.B_le.trans inf_le_right
  have hB2 : IsPGroup 2 h.B := (isPGroup_S h).to_le (h.B_le.trans inf_le_left)
  have hsup := (GSLit.fixedLayer_sup_pPrimeCore (B5a.isQuasisimple_J h) hBJ hB2).1
  have hJBJ : JB ≤ h.J := (GSLit.fixedLayer_le_inf h.J h.B).trans inf_le_left
  obtain ⟨-, e1, -⟩ := restriction_quotient_mulEquiv hJBJ hsup
  set JB' := JB.subgroupOf h.K with hJB'
  let e2 : JB ≃* JB' := (subgroupOfEquivOfLe hJBK).symm
  let e3 : JB ⧸ pPrimeCore 2 JB ≃* JB' ⧸ pPrimeCore 2 JB' :=
    QuotientGroup.congr (pPrimeCore 2 JB) (pPrimeCore 2 JB') e2 (pPrimeCore_map_iso 2 e2)
  set π := QuotientGroup.mk' (pPrimeCore 2 h.K) with hπ
  have hπker : ¬ 2 ∣ Nat.card π.ker := by
    rw [hπ, QuotientGroup.ker_mk']
    intro h2
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
      (pPrimeCore_coprime_card (p := 2) (G := h.K)) h2
  obtain ⟨e4, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv π JB'
    (OddQuot.not_two_dvd_card_ker_domRestrict π hπker JB')
  set ι : OddBar h.K →* Perm (Fin 10) :=
    (alternatingGroup (Fin 10)).subtype.comp eK.toMonoidHom with hι
  have hιinj : Function.Injective ι :=
    (alternatingGroup (Fin 10)).subtype_injective.comp eK.injective
  have hLeq : Lsub hKa eK = (JB'.map π).map ι := by
    ext σ
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hx
      refine ⟨π ⟨x, hJBK hx⟩, ⟨⟨x, hJBK hx⟩, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        exact hx
      · rw [rhoBar_mk]
        exact (rhoW_of_mem_K hKa eK ⟨x, hJBK hx⟩).symm
    · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at hk
      refine ⟨wbarMk h.B ⟨k, K_le_W h k.2⟩, ⟨⟨k, K_le_W h k.2⟩, ?_, rfl⟩, ?_⟩
      · rw [SetLike.mem_coe, mem_subgroupOf]
        exact hk
      · rw [rhoBar_mk, rhoW_of_mem_K]
        rfl
  let eL : Lsub hKa eK ≃* JB'.map π :=
    (MulEquiv.subgroupCongr hLeq).trans (equivMapOfInjective (JB'.map π) ι hιinj).symm
  let e5 : Lsub hKa eK ⧸ pPrimeCore 2 (Lsub hKa eK) ≃* (JB'.map π) ⧸ pPrimeCore 2 (JB'.map π) :=
    QuotientGroup.congr _ _ eL (pPrimeCore_map_iso 2 eL)
  calc Nat.card (Lsub hKa eK ⧸ pPrimeCore 2 (Lsub hKa eK))
      = Nat.card ((JB'.map π) ⧸ pPrimeCore 2 (JB'.map π)) := Nat.card_congr e5.toEquiv
    _ = Nat.card (JB' ⧸ pPrimeCore 2 JB') := (Nat.card_congr e4.toEquiv).symm
    _ = Nat.card (JB ⧸ pPrimeCore 2 JB) := (Nat.card_congr e3.toEquiv).symm
    _ = Nat.card (OddBar h.J) := Nat.card_congr e1.toEquiv
    _ = 360 := by
      rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      decide

theorem false_of_sign_eq_neg_one (eJ : OddBar h.J ≃* alternatingGroup (Fin 6)) {w : h.W}
    (hs : Perm.sign (rhoW h hKa eK w) = -1) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj := rhoBar_surjective hKa eK hs
  have hJK := JBbar_le_Kbar hKa
  have hstdJ := h.isStandard_bar
  set Jt := wbarImage h.B (GSLit.fixedLayer h.J h.B) with hJt
  set C := centralizer (Jt : Set (Wbar h.B)) with hC
  refine false_of_standard_s10 (L := Lsub hKa eK) (L_le_alt hKa eK) (L_perfect hKa eK) ?_
    (card_L_core hKa eK eJ) ?_ ?_
  · rw [← card_L_core hKa eK eJ]
    exact card_quotient_dvd_card _
  ·
    intro π σ hσ hπσ hσ2 hσ1
    obtain ⟨y, hy, hy2, hy1⟩ := exists_lift_involution hKa eK hsurj hσ2 hσ1
    obtain ⟨g, rfl⟩ := hsurj π
    have hyC : y ∈ C := mem_centralizer_of_rhoBar hKa eK hJK (by rw [hy]; exact hσ)
    have hgyC : g * y * g⁻¹ ∈ C :=
      mem_centralizer_of_rhoBar hKa eK hJK (by rw [map_mul, map_mul, map_inv, hy]; exact hπσ)
    have hgN : g ∈ normalizer (C : Set (Wbar h.B)) := by
      by_contra hgN
      have hodd := hstdJ.2.2.1 g hgN
      have hmem : y ∈ C ⊓ conjugate C g := by
        refine ⟨hyC, ?_⟩
        show y ∈ C.map (MulAut.conj g⁻¹).toMonoidHom
        refine ⟨g * y * g⁻¹, hgyC, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      have hord : orderOf (⟨y, hmem⟩ : ↥(C ⊓ conjugate C g)) = 2 := by
        rw [Subgroup.orderOf_mk]
        exact orderOf_eq_prime (by rw [sq, hy2]) hy1
      have h2 := orderOf_dvd_natCard (⟨y, hmem⟩ : ↥(C ⊓ conjugate C g))
      rw [hord] at h2
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h2)
    rw [hstdJ.2.2.2.1] at hgN
    exact le_normalizer_map (rhoBar hKa eK) ⟨g, hgN, rfl⟩
  ·
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 2 (even_iff_two_dvd.1 hstdJ.2.1)
    have hc2 : (c : Wbar h.B) * c = 1 := by
      have := pow_orderOf_eq_one c
      rw [hc, sq] at this
      exact congrArg Subtype.val this
    refine ⟨rhoBar hKa eK c, ?_, ?_, ?_⟩
    · rw [mem_centralizer_iff]
      rintro _ ⟨j, hj, rfl⟩
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 c.2 j hj]
    · rw [← map_mul, hc2, map_one]
    · intro h1
      have h3 := eq_one_of_rhoBar_eq_one hKa eK h1 hc2
      have : c = 1 := Subtype.ext h3
      rw [this, orderOf_one] at hc
      exact absurd hc (by norm_num)

end A10

open CFSG.ComponentClassification.GSThmB Equiv A10 in
theorem cfA10NoOuter : CFA10NoOuter := by
  intro H _ _ h hrow
  obtain ⟨⟨eJ⟩, hKa, ⟨eK⟩⟩ := hrow
  intro w hw
  rcases Int.units_eq_one_or (Perm.sign (rhoW h hKa eK ⟨w, hw⟩)) with hs | hs
  · exact mem_of_sign_eq_one hKa eK hs
  · exact (false_of_sign_eq_neg_one hKa eK eJ hs).elim

end CFSG.ComponentClassification.CatFactsSmall
