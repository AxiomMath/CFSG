module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Assembly
public import CFSG.Foundations.Catalog

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {X : Type} [Group X] [Finite X] {p : ℕ} {R : Sylow p X} {A X₀ : Subgroup X}

theorem k1Core_exists_isComponentOf (h : D2Reduced p X R A X₀) :
    ∃ K : Subgroup X, IsComponentOf K ⊤ := by
  have : Fact p.Prime := ⟨h.prime⟩
  by_contra hno
  push Not at hno
  have hE : CFSG.layer X = ⊥ := by
    rw [CFSG.layer.eq_sSup, sSup_eq_bot]
    intro M hM
    exact absurd ((CFSG.isComponent_iff_open M).mp hM) (hno M)
  have hF : CFSG.fittingSubgroup X = ⊥ := by
    rw [CFSG.Fitting_eq_pcore X p h.core_eq_bot]
    exact h.pCore_eq_bot
  have hC := CFSG.centralizer_generalizedFitting_le X
  rw [CFSG.generalizedFitting.eq_sup, hF, hE, sup_bot_eq] at hC
  apply h.ne_top
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ Subgroup.centralizer ((⊥ : Subgroup X) : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, Subgroup.mem_bot] at hy
    rw [hy, one_mul, mul_one]
  rw [Subgroup.mem_bot.mp (hC hx)]
  exact X₀.one_mem

theorem k1Core_almostSimple (hK : CFSG.IsKGroup X) (h : D2Reduced p X R A X₀) :
    ∃ K : Subgroup X, D2AlmostSimple p X R A X₀ K := by
  obtain ⟨K, hKc⟩ := k1Core_exists_isComponentOf h
  have hcenter := h.center_eq_bot hKc
  have hsec : CatalogSimpleSections X :=
    catalogSimpleSections_iff_isKGroup.mpr (CFSG.KCore.KGroupAllSimple.kGroupNonab hK)
  have hsimple : IsSimpleGroup (K ⧸ Subgroup.center K) := hKc.2.2.2
  have hnonab := CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian K
    hKc.2.2
  have hcat : IsCatalogGroup (K ⧸ Subgroup.center K) :=
    hsec K (Subgroup.center K) inferInstance hsimple hnonab
  obtain ⟨t, ⟨-, htK⟩, ht, -⟩ :=
    exists_mem_sylow_inf_component h.prime h.ne_two h.core_eq_bot R hKc
  have hdvd : p ∣ Nat.card K := ht ▸ Subgroup.orderOf_dvd_natCard K htK
  exact ⟨K,
    { toD2Reduced := h
      component := hKc
      normal := h.normal_of_isComponentOf hKc
      unique := fun L hL => h.eq_of_isComponentOf hL hKc
      center_eq_bot := hcenter
      centralizer_eq_bot := h.centralizer_eq_bot_of_isComponentOf hKc
      not_le := h.not_le_of_isComponentOf hKc
      dvd := hdvd
      catalog := IsCatalogGroup.of_mulEquiv
        ((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).symm
        hcat }⟩

theorem k1Core_ne_of_conj {B : Subgroup X}
    (hconj : ∀ g : X, B.map (MulAut.conj g).toMonoidHom ≠ A) : B ≠ A := by
  intro hBA
  apply hconj 1
  rw [← hBA]
  ext x
  simp

theorem k1Core_false_of_sylow_eq (h : D2Reduced p X R A X₀) {B : Subgroup X}
    (hBR : B ≤ R) (hBc : Nat.card B = p ^ 2) (hBA : B ≠ A) (hRA : (R : Subgroup X) = A) :
    False :=
  hBA (Subgroup.eq_of_le_of_card_ge (hBR.trans hRA.le) (by rw [hBc, h.card_A]))

theorem k1Core_sylow_eq_of_le {R : Sylow 3 X} (h : D2Reduced 3 X R A X₀) {K : Subgroup X}
    (hRK : (R : Subgroup X) ≤ K) (h27 : ¬ 27 ∣ Nat.card K) : (R : Subgroup X) = A := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := R.isPGroup'.exists_card_eq
  have hRK' : Nat.card (R : Subgroup X) ∣ Nat.card K := Subgroup.card_dvd_of_le hRK
  have hAR : Nat.card A ∣ Nat.card (R : Subgroup X) := Subgroup.card_dvd_of_le h.A_le
  rw [h.card_A, hk] at hAR
  rw [hk] at hRK'
  have hk2 : k ≤ 2 := by
    by_contra hk3
    push Not at hk3
    apply h27
    calc 27 = 3 ^ 3 := by norm_num
      _ ∣ 3 ^ k := pow_dvd_pow 3 hk3
      _ ∣ Nat.card K := hRK'
  have hk2' : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hAR
  have hk' : k = 2 := le_antisymm hk2 hk2'
  exact (Subgroup.eq_of_le_of_card_ge h.A_le (by rw [hk, hk', h.card_A])).symm

theorem k1Core_exists_action {K : Subgroup X} [K.Normal]
    (hC : Subgroup.centralizer (K : Set X) = ⊥) {L : Type*} [Group L] (ψ : K ≃* L) :
    ∃ ι : X →* MulAut L, Function.Injective ι ∧
      (∀ (x : X) (y : L), ((ψ.symm (ι x y) : K) : X) = x * (ψ.symm y : X) * x⁻¹) ∧
      ∀ k : K, ι k = MulAut.conj (ψ k) := by
  let ι : X →* MulAut L := (MulAut.congr ψ).toMonoidHom.comp (MulAut.conjNormal (H := K))
  have hι : ∀ (x : X) (y : L), ((ψ.symm (ι x y) : K) : X) = x * (ψ.symm y : X) * x⁻¹ := by
    intro x y
    simp [ι, MulAut.congr_apply, MulAut.conjNormal_apply]
  refine ⟨ι, ?_, hι, ?_⟩
  · refine (MulAut.congr ψ).injective.comp ?_
    rw [injective_iff_map_eq_one]
    intro g hg
    have hgC : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have h1 := congrArg (fun a : MulAut K => ((a ⟨l, hl⟩ : K) : X)) hg
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
      exact (mul_inv_eq_iff_eq_mul.mp h1).symm
    rw [hC, Subgroup.mem_bot] at hgC
    exact hgC
  · intro k
    ext y
    apply ψ.symm.injective
    apply Subtype.ext
    rw [hι]
    simp

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
