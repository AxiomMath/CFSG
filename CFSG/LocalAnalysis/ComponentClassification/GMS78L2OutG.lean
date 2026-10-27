module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78L2Out

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem quotAut_mem_inner_of_mem_sup {L : Subgroup G} {n : normalizer (L : Set G)}
    (hn : (n : G) ∈ L ⊔ centralizer (L : Set G)) : quotAutHom L n ∈ inner (rankTwoQuot L) := by
  set H := ((inner (rankTwoQuot L)).comap (quotAutHom L)).map (normalizer (L : Set G)).subtype
  have hL : L ≤ H := by
    intro l hl
    refine ⟨⟨l, le_normalizer hl⟩, ?_, rfl⟩
    show quotAutHom L ⟨l, le_normalizer hl⟩ ∈ inner (rankTwoQuot L)
    have h1 : L.normalizerMonoidHom ⟨l, le_normalizer hl⟩ = MulAut.conj ⟨l, hl⟩ := by
      ext x
      rw [normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
      rfl
    refine ⟨QuotientGroup.mk' (center L) ⟨l, hl⟩, ?_⟩
    change MulAut.conj _ = centerQuotientHom L (L.normalizerMonoidHom ⟨l, le_normalizer hl⟩)
    rw [h1]
    exact (onCenterQuotient_conj _).symm
  have hK : centralizer (L : Set G) ≤ H := by
    intro c hc
    have hcN : c ∈ normalizer (L : Set G) := centralizer_le_normalizer _ hc
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    show quotAutHom L ⟨c, hcN⟩ ∈ inner (rankTwoQuot L)
    have h1 : L.normalizerMonoidHom ⟨c, hcN⟩ = 1 := by
      ext x
      rw [normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
      show c * (x : G) * c⁻¹ = x
      rw [← mem_centralizer_iff.mp hc x x.2, mul_inv_cancel_right]
    refine ⟨1, ?_⟩
    change MulAut.conj 1 = centerQuotientHom L (L.normalizerMonoidHom ⟨c, hcN⟩)
    rw [h1, map_one, map_one]
  obtain ⟨m, hm, hmn⟩ := (sup_le hL hK) hn
  have : m = n := Subtype.ext hmn
  rw [← this]
  exact hm

variable [Finite G] {L : Subgroup G} {f : ℕ}

theorem exists_sylow_quot (hZ : Odd (Nat.card (center L))) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) :
    ∃ R : Sylow 2 (rankTwoQuot L), (∀ x : L, (x : G) ∈ P →
        QuotientGroup.mk' (center L) x ∈ (R : Subgroup (rankTwoQuot L))) ∧
      (∀ x y : L, (x : G) ∈ P → (y : G) ∈ P →
        QuotientGroup.mk' (center L) x = QuotientGroup.mk' (center L) y → x = y) ∧
      Nat.card (R : Subgroup (rankTwoQuot L)) ≤ Nat.card P ∧
      ∀ n : normalizer (L : Set G), (∀ x ∈ P, (n : G) * x * (n : G)⁻¹ ∈ P) →
        ∀ r ∈ (R : Subgroup (rankTwoQuot L)), quotAutHom L n r ∈ (R : Subgroup _) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : L →* rankTwoQuot L := QuotientGroup.mk' (center L) with hπ
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ x : L, x ∈ (Q : Subgroup L) ↔ (x : G) ∈ P := fun x => by
    rw [hQ]
    rfl
  let R : Sylow 2 (rankTwoQuot L) := Q.mapSurjective (f := π) (QuotientGroup.mk'_surjective _)
  have hR : (R : Subgroup (rankTwoQuot L)) = (Q : Subgroup L).map π := rfl
  have hbot : (Q : Subgroup L) ⊓ center L = ⊥ :=
    AschbacherTightEmbedding.two_subgroup_of_odd_eq_bot _ (center L) Q.isPGroup'.to_inf_left hZ
      inf_le_right
  refine ⟨R, fun x hx => ?_, fun x y hx hy hxy => ?_, ?_, fun n hn r hr => ?_⟩
  · rw [hR]
    exact ⟨x, (hmemQ x).mpr hx, rfl⟩
  · have hc : x⁻¹ * y ∈ center L := QuotientGroup.eq.mp hxy
    have h1 : x⁻¹ * y ∈ (Q : Subgroup L) ⊓ center L :=
      mem_inf.mpr ⟨mul_mem (inv_mem ((hmemQ x).mpr hx)) ((hmemQ y).mpr hy), hc⟩
    rw [hbot, mem_bot, inv_mul_eq_one] at h1
    exact h1
  · let ψ : ↥(Q : Subgroup L) → ↥(R : Subgroup (rankTwoQuot L)) := fun x =>
      ⟨π x, by rw [hR]; exact ⟨x, x.2, rfl⟩⟩
    have hψ : Function.Surjective ψ := by
      rintro ⟨r, hr⟩
      rw [hR] at hr
      obtain ⟨x, hx, rfl⟩ := hr
      exact ⟨⟨x, hx⟩, rfl⟩
    have hQP : Nat.card (Q : Subgroup L) = Nat.card P := by
      rw [hQ]
      exact Nat.card_congr (subgroupOfEquivOfLe hP.le).toEquiv
    exact (Nat.card_le_card_of_surjective ψ hψ).trans hQP.le
  · rw [hR] at hr ⊢
    obtain ⟨x, hx, rfl⟩ := hr
    refine ⟨L.normalizerMonoidHom n x, (hmemQ _).mpr ?_, (quotAutHom_apply_mk L n x).symm⟩
    rw [normalizerMonoidHom_apply_apply_coe]
    exact hn _ ((hmemQ x).mp hx)

omit [Finite G] in
theorem quotAut_props (hLp : commutator L = ⊤) {w : G} (hwN : w ∈ normalizer (L : Set G))
    (hwLK : w ∉ L ⊔ centralizer (L : Set G)) (hww : w * w ∈ L ⊔ centralizer (L : Set G)) :
    (∃ y, quotAutHom L ⟨w, hwN⟩ * quotAutHom L ⟨w, hwN⟩ = MulAut.conj y) ∧
      ¬ ∃ y, quotAutHom L ⟨w, hwN⟩ = MulAut.conj y := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := quotAut_mem_inner_of_mem_sup (n := ⟨w, hwN⟩ * ⟨w, hwN⟩) hww
    exact ⟨y, by rw [← map_mul, ← hy]⟩
  · rintro ⟨y, hy⟩
    exact hwLK (mem_sup_centralizer_of_quotAut_mem_inner hLp hwN ⟨y, hy.symm⟩)

theorem card_centralizer_sq_le_of_sq_mem
    (hLp : commutator L = ⊤) (hZ : Odd (Nat.card (center L))) (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) {w : G} (hwN : w ∈ normalizer (L : Set G))
    (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P) (hwLK : w ∉ L ⊔ centralizer (L : Set G))
    (hww : w * w ∈ L ⊔ centralizer (L : Set G)) :
    Nat.card (P ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2 ≤ Nat.card P := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set n : normalizer (L : Set G) := ⟨w, hwN⟩ with hn
  set α := quotAutHom L n with hαdef
  obtain ⟨hαα, hα⟩ := quotAut_props hLp hwN hwLK hww
  obtain ⟨R, hRmem, hRinj, hRcard, hRnorm⟩ := exists_sylow_quot hZ hP
  have h1 := card_fix_sq_le_of_sq_inner_psl2 hf e α hαα hα R (hRnorm n hwP)
  have hxL : ∀ x : (P ⊓ centralizer ({w} : Set G) : Subgroup G), (x : G) ∈ L := fun x =>
    hP.le x.2.1
  let xL : (P ⊓ centralizer ({w} : Set G) : Subgroup G) → L := fun x => ⟨x, hxL x⟩
  have hfix : ∀ x,
      α (QuotientGroup.mk' (center L) (xL x)) = QuotientGroup.mk' (center L) (xL x) := by
    intro x
    rw [hαdef, quotAutHom_apply_mk]
    congr 1
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_apply_coe]
    have hc : w * (x : G) = x * w := (mem_centralizer_singleton_iff.mp x.2.2).symm
    show w * (x : G) * w⁻¹ = x
    rw [hc, mul_inv_cancel_right]
  let φ : (P ⊓ centralizer ({w} : Set G) : Subgroup G) →
      {r : (R : Subgroup (rankTwoQuot L)) // α r = r} :=
    fun x => ⟨⟨QuotientGroup.mk' (center L) (xL x), hRmem _ x.2.1⟩, hfix x⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : QuotientGroup.mk' (center L) (xL x) = QuotientGroup.mk' (center L) (xL y) :=
      congrArg (fun r => ((r.1 : _) : rankTwoQuot L)) hxy
    have h2 := hRinj _ _ x.2.1 y.2.1 h1
    have h3 : ((xL x : L) : G) = ((xL y : L) : G) := congrArg Subtype.val h2
    exact Subtype.ext h3
  calc Nat.card (P ⊓ centralizer ({w} : Set G) : Subgroup G) ^ 2
      ≤ Nat.card {r : (R : Subgroup (rankTwoQuot L)) // α r = r} ^ 2 :=
        Nat.pow_le_pow_left (Nat.card_le_card_of_injective φ hφ) 2
    _ ≤ Nat.card (R : Subgroup (rankTwoQuot L)) := h1
    _ ≤ Nat.card P := hRcard

theorem mul_inv_mem_sup_of_sq_mem
    (hLp : commutator L = ⊤) (hZ : Odd (Nat.card (center L))) (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) {w₁ w₂ : G} (h₁N : w₁ ∈ normalizer (L : Set G))
    (h₂N : w₂ ∈ normalizer (L : Set G)) (h₁P : ∀ x ∈ P, w₁ * x * w₁⁻¹ ∈ P)
    (h₂P : ∀ x ∈ P, w₂ * x * w₂⁻¹ ∈ P) (h₁LK : w₁ ∉ L ⊔ centralizer (L : Set G))
    (h₂LK : w₂ ∉ L ⊔ centralizer (L : Set G)) (h₁₁ : w₁ * w₁ ∈ L ⊔ centralizer (L : Set G))
    (h₂₂ : w₂ * w₂ ∈ L ⊔ centralizer (L : Set G)) :
    w₁ * w₂⁻¹ ∈ L ⊔ centralizer (L : Set G) := by
  obtain ⟨h1sq, h1out⟩ := quotAut_props hLp h₁N h₁LK h₁₁
  obtain ⟨h2sq, h2out⟩ := quotAut_props hLp h₂N h₂LK h₂₂
  obtain ⟨R, -, -, -, hRnorm⟩ := exists_sylow_quot hZ hP
  obtain ⟨y, hy⟩ := mul_inv_inner_of_sq_inner_psl2 hf e h1sq h2sq h1out h2out R
    (hRnorm ⟨w₁, h₁N⟩ h₁P) (hRnorm ⟨w₂, h₂N⟩ h₂P)
  have hmem : w₁ * w₂⁻¹ ∈ normalizer (L : Set G) := mul_mem h₁N (inv_mem h₂N)
  apply mem_sup_centralizer_of_quotAut_mem_inner hLp hmem
  refine ⟨y, ?_⟩
  have : (⟨w₁ * w₂⁻¹, hmem⟩ : normalizer (L : Set G)) = ⟨w₁, h₁N⟩ * ⟨w₂, h₂N⟩⁻¹ := rfl
  rw [this, map_mul, map_inv, hy]

theorem mem_sup_of_commute
    (hLp : commutator L = ⊤) (hZ : Odd (Nat.card (center L))) (hf : 2 ≤ f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) (hP1 : 1 < Nat.card P) {w : G}
    (hwN : w ∈ normalizer (L : Set G)) {m : ℕ} (hwm : w ^ 2 ^ m = 1)
    (hwP : ∀ x ∈ P, w * x = x * w) : w ∈ L ⊔ centralizer (L : Set G) := by
  classical
  by_contra hw
  have hex : ∃ j, w ^ 2 ^ j ∈ L ⊔ centralizer (L : Set G) := ⟨m, by rw [hwm]; exact one_mem _⟩
  set j₀ := Nat.find hex with hj₀
  have hj₀mem : w ^ 2 ^ j₀ ∈ L ⊔ centralizer (L : Set G) := Nat.find_spec hex
  have hj₀pos : j₀ ≠ 0 := by
    intro h0
    apply hw
    have := hj₀mem
    rwa [h0, pow_zero, pow_one] at this
  obtain ⟨i, hi⟩ : ∃ i, j₀ = i + 1 := ⟨j₀ - 1, by omega⟩
  have hnot : w ^ 2 ^ i ∉ L ⊔ centralizer (L : Set G) := Nat.find_min hex (by omega)
  set w' := w ^ 2 ^ i with hw'
  have hw'N : w' ∈ normalizer (L : Set G) := pow_mem hwN _
  have hw'sq : w' * w' ∈ L ⊔ centralizer (L : Set G) := by
    rw [hw', ← pow_add, ← two_mul, ← pow_succ']
    rw [hi] at hj₀mem
    exact hj₀mem
  have hcomm : ∀ x ∈ P, w' * x = x * w' := fun x hx =>
    ((Commute.pow_left (hwP x hx) (2 ^ i)) : Commute (w ^ 2 ^ i) x)
  have hw'P : ∀ x ∈ P, w' * x * w'⁻¹ ∈ P := fun x hx => by
    rw [hcomm x hx, mul_inv_cancel_right]
    exact hx
  have h := card_centralizer_sq_le_of_sq_mem hLp hZ hf e hP hw'N hw'P hnot hw'sq
  have hPC : P ⊓ centralizer ({w'} : Set G) = P := by
    refine inf_eq_left.mpr fun x hx => mem_centralizer_singleton_iff.mpr ?_
    exact (hcomm x hx).symm
  rw [hPC] at h
  have : Nat.card P * Nat.card P ≤ Nat.card P * 1 := by nlinarith
  have := Nat.le_of_mul_le_mul_left this (by omega)
  omega

theorem mem_sup_of_sq_mem_of_odd
    (hLp : commutator L = ⊤) (hZ : Odd (Nat.card (center L))) (hf : 2 ≤ f) (hodd : Odd f)
    (e : rankTwoQuot L ≃* PSL(2, GaloisField 2 f)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P L) {w : G} (hwN : w ∈ normalizer (L : Set G))
    (hwP : ∀ x ∈ P, w * x * w⁻¹ ∈ P) (hww : w * w ∈ L ⊔ centralizer (L : Set G)) :
    w ∈ L ⊔ centralizer (L : Set G) := by
  by_contra hw
  obtain ⟨hαα, hα⟩ := quotAut_props hLp hwN hw hww
  obtain ⟨R, -, -, -, hRnorm⟩ := exists_sylow_quot hZ hP
  exact hα (inner_of_sq_inner_of_odd_psl2 hf hodd e hαα R (hRnorm ⟨w, hwN⟩ hwP))

end CFSG.ComponentClassification.GMS78
