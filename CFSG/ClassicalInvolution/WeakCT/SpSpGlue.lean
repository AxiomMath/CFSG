module

public import CFSG.ClassicalInvolution.Models.SymplecticPairs.ShortRoot
import CFSG.ClassicalInvolution.Models.SymplecticPairs.LongNormalizer
import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCLevi
import CFSG.ClassicalInvolution.Q3.Q3ZAdjSp
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotLeviRootSL2Sp

public section

namespace CFSG.ClassicalInvolution.WeakCT

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs (longBlock shortBlock spEmbed
  spEmbed_comp_shortBlock_of_injective spEmbed_longBlock spEmbed_injective
  spEmbed_castSucc_conj_mem_range_spEmbed_natAdd mat_spEmbed spEmbedMat_apply_image
  spEmbedMat_apply_of_not_mem range_longBlock mem_suppGroup mulVec_eq_self_of_isSupp
  mulVec_conj_apply mulVec_inj mulVec_mulVec_inv mem_coords longBlock_sl2Upper longBlock_sl2Lower)
open CFSG.LieType.Steinberg (sl2Upper sl2Lower)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective mat_apply mat_elt elt E)
open CFSG.ClassicalInvolution.Q3.Q3Z (spMap spMap_comp spMap_injective spMap_longBlock
  spMap_shortBlock spMap_surjective mat_spMap)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp coe_fieldSp)
open CFSG.SeitzReduction.F4Pilot (exists_eq_conj_mul_fieldSp exists_eq_conj_mul_fieldSp_tauSp
  tauIdx tauSp_elt fieldSp_elt)
open Matrix
open scoped MatrixGroups

private theorem fieldSp_eq_spMap {m : ℕ} {K : Type} [Field K] (σ : K ≃+* K) (g : StatedSp m K) :
    fieldSp m K σ g = spMap (n := m) σ.toRingHom g :=
  mat_injective (by rw [mat_spMap, mat_apply, mat_apply, coe_fieldSp]; rfl)

private theorem spMap_spEmbed {m n : ℕ} {K : Type} [Field K] {φ : K →+* K}
    {σ : Fin m → Fin n} (hσ : Function.Injective σ) (x : StatedSp m K) :
    spMap (n := n) φ (spEmbed σ hσ x) = spEmbed σ hσ (spMap (n := m) φ x) := by
  refine mat_injective ?_
  rw [mat_spMap, mat_spEmbed, mat_spEmbed]
  ext a b
  rw [Matrix.map_apply]
  by_cases h : a ∈ Set.range (Sum.map σ σ) ∧ b ∈ Set.range (Sum.map σ σ)
  · obtain ⟨⟨u, rfl⟩, ⟨v, rfl⟩⟩ := h
    rw [spEmbedMat_apply_image hσ, spEmbedMat_apply_image hσ, mat_spMap, Matrix.map_apply]
  · rw [spEmbedMat_apply_of_not_mem _ h, spEmbedMat_apply_of_not_mem _ h]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab]

theorem eq_zero_of_mulVec_elt_difference {K : Type} [Field K] {v : Fin 2 ⊕ Fin 2 → K}
    (h1 : mat 2 K (elt (.difference 0 1 (by decide)) 1) *ᵥ v = v)
    (h2 : mat 2 K (elt (.difference 1 0 (by decide)) 1) *ᵥ v = v) : v = 0 := by
  rw [mat_elt, one_smul, Matrix.add_mulVec, Matrix.one_mulVec, add_eq_left] at h1 h2
  have a1 := congrFun h1 (Sum.inl 0)
  have a2 := congrFun h1 (Sum.inr 1)
  have a3 := congrFun h2 (Sum.inl 1)
  have a4 := congrFun h2 (Sum.inr 0)
  simp [Matrix.mulVec, dotProduct, E, Matrix.single_apply] at a1 a2 a3 a4
  funext x
  rcases x with x | x <;> fin_cases x <;> simp_all

theorem exists_eq_conj_mul_fieldSp_of_longBlock_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (α : MulAut (StatedSp 2 K))
    (hα : ∀ y : SL(2, K), α (longBlock K 2 1 y) ∈ (longBlock K 2 1).range) :
    ∃ (s : StatedSp 2 K) (σ : K ≃+* K), ∀ g : StatedSp 2 K, α g = s * fieldSp 2 K σ g * s⁻¹ := by
  obtain ⟨s, σ, h | h⟩ := exists_eq_conj_mul_fieldSp_tauSp α
  · exact ⟨s, σ, h⟩
  · exfalso
    let e0 : Fin 2 ⊕ Fin 2 → K := Pi.single (Sum.inl 0) 1
    have hmem_pos : elt (.positiveLong 1) 1 ∈ (longBlock K 2 1).range :=
      ⟨sl2Upper 1, longBlock_sl2Upper 1 1⟩
    have hmem_neg : elt (.negativeLong 1) 1 ∈ (longBlock K 2 1).range :=
      ⟨sl2Lower 1, longBlock_sl2Lower 1 1⟩
    have hfix_r : ∀ r : TauCeti.GLSymplecticFin.RootSubgroupIndex 2,
        elt r 1 ∈ (longBlock K 2 1).range →
        mat 2 K (elt (tauIdx r) 1) *ᵥ (mat 2 K s⁻¹ *ᵥ e0) =
          mat 2 K s⁻¹ *ᵥ e0 := by
      intro r hr
      obtain ⟨y, hy⟩ := hr
      have hαr : α (elt r 1) ∈ (longBlock K 2 1).range := by
        rw [← hy]
        exact hα y
      have hαelt : α (elt r 1) = s * elt (tauIdx r) 1 * s⁻¹ := by
        rw [h (elt r 1), tauSp_elt, one_pow, fieldSp_elt, map_one]
      have hmem' : s * elt (tauIdx r) 1 * s⁻¹ ∈ (longBlock K 2 1).range := by
        rw [← hαelt]
        exact hαr
      have hfix : mat 2 K (s * elt (tauIdx r) 1 * s⁻¹) *ᵥ e0 = e0 := by
        rw [range_longBlock] at hmem'
        refine mulVec_eq_self_of_isSupp (mem_suppGroup.mp hmem') fun t ht => ?_
        have ht0 : t ≠ Sum.inl (0 : Fin 2) := by
          rcases mem_coords.1 ht with rfl | rfl <;> decide
        simp [e0, ht0]
      have hconj := mulVec_conj_apply (g := s⁻¹) (c := elt (tauIdx r) 1)
        (v := mat 2 K s⁻¹ *ᵥ e0)
      rw [inv_inv, mulVec_mulVec_inv] at hconj
      rw [hfix] at hconj
      refine mulVec_inj (g := s) ?_
      rw [← hconj, mulVec_mulVec_inv]
    have hv : mat 2 K s⁻¹ *ᵥ e0 = 0 := by
      refine eq_zero_of_mulVec_elt_difference ?_ ?_
      · simpa [tauIdx] using hfix_r (.positiveLong 1) hmem_pos
      · simpa [tauIdx] using hfix_r (.negativeLong 1) hmem_neg
    have he0 : e0 = 0 := by
      calc e0 = mat 2 K s *ᵥ (mat 2 K s⁻¹ *ᵥ e0) := (mulVec_mulVec_inv s e0).symm
        _ = 0 := by rw [hv, Matrix.mulVec_zero]
    have h0 : e0 (Sum.inl (0 : Fin 2)) = 0 := congrFun he0 _
    simp [e0] at h0

private theorem exists_conj_spMap_of_mulAut {s : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hs : 1 ≤ s) (β : MulAut (StatedSp (s+1) K))
    (hβ : ∀ y : SL(2, K), β (longBlock K (s+1) (Fin.last s) y) ∈
      (longBlock K (s+1) (Fin.last s)).range) :
    ∃ (A : StatedSp (s+1) K) (σ : K ≃+* K), ∀ g : StatedSp (s+1) K,
      β g = A * spMap (n := s+1) σ.toRingHom g * A⁻¹ := by
  rcases Nat.lt_or_ge s 2 with hs1 | hs2
  · obtain rfl : s = 1 := by omega
    obtain ⟨A, σ, h⟩ := exists_eq_conj_mul_fieldSp_of_longBlock_one β (by simpa using hβ)
    exact ⟨A, σ, fun g => by rw [h g, fieldSp_eq_spMap]⟩
  · obtain ⟨A, σ, h⟩ := exists_eq_conj_mul_fieldSp (n := s+1) (by omega) β
    exact ⟨A, σ, fun g => by rw [h g, fieldSp_eq_spMap]⟩

private theorem longBlock_map_mem_range {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂ : StatedSp (s+2) F →* G} (hκ₂ : Function.Injective κ₂)
    {α : MulAut (StatedSp (s+1) F)}
    (hα : ∀ g : StatedSp (s+1) F,
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))) (α g) =
        (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))) g)
    (hlong : (κ₁.comp (longBlock F (s+2) (Fin.last (s+1)))).range =
      (κ₂.comp (longBlock F (s+2) (Fin.last s).castSucc)).range) :
    ∀ y : SL(2, F), α (longBlock F (s+1) (Fin.last s) y) ∈
      (longBlock F (s+1) (Fin.last s)).range := by
  have he₂ : Function.Injective
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))) :=
    hκ₂.comp (spEmbed_injective _)
  intro y
  have h1 : (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))))
      (α (longBlock F (s+1) (Fin.last s) y)) =
      κ₁ (longBlock F (s+2) (Fin.last (s+1)) y) := by
    rw [hα, MonoidHom.comp_apply, spEmbed_longBlock]
    rfl
  have hmem : κ₁ (longBlock F (s+2) (Fin.last (s+1)) y) ∈
      (κ₂.comp (longBlock F (s+2) (Fin.last s).castSucc)).range := by
    rw [← hlong]
    exact ⟨y, rfl⟩
  obtain ⟨z, hz⟩ := hmem
  refine ⟨z, ?_⟩
  have h3 : (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))))
      (longBlock F (s+1) (Fin.last s) z) =
      κ₂ (longBlock F (s+2) (Fin.last s).castSucc z) := by
    rw [MonoidHom.comp_apply, spEmbed_longBlock]
  exact (he₂ (h1.trans (h3.trans hz).symm)).symm

private theorem longBlock_normalizes {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂ : StatedSp (s+2) F →* G} (hκ₂ : Function.Injective κ₂)
    {α : MulAut (StatedSp (s+1) F)}
    (hα : ∀ g : StatedSp (s+1) F,
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))) (α g) =
        (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))) g)
    (hlong : (κ₁.comp (longBlock F (s+2) (Fin.last (s+1)))).range =
      (κ₂.comp (longBlock F (s+2) (Fin.last s).castSucc)).range)
    {A₀ : StatedSp (s+1) F} {σ : F ≃+* F}
    (hA₀ : ∀ g : StatedSp (s+1) F, α g = A₀ * spMap (n := s+1) σ.toRingHom g * A₀⁻¹) :
    ∀ x ∈ (longBlock F (s+1) (Fin.last s)).range,
      A₀ * x * A₀⁻¹ ∈ (longBlock F (s+1) (Fin.last s)).range := by
  have hα_mem_all := longBlock_map_mem_range hκ₂ hα hlong
  have hsp : ∀ x : StatedSp (s+1) F,
      spMap (n := s+1) σ.toRingHom (spMap (n := s+1) σ.symm.toRingHom x) = x := by
    intro x
    rw [spMap_comp]
    have hcomp : σ.toRingHom.comp σ.symm.toRingHom = RingHom.id F := by
      ext z
      simp
    rw [hcomp]
    refine mat_injective ?_
    rw [mat_spMap]
    ext i j
    simp
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  have hsp' : spMap (n := s+1) σ.symm.toRingHom (longBlock F (s+1) (Fin.last s) y) =
      longBlock F (s+1) (Fin.last s)
        (Matrix.SpecialLinearGroup.map σ.symm.toRingHom y) :=
    spMap_longBlock σ.symm.toRingHom (Fin.last s) y
  have hconj : A₀ * longBlock F (s+1) (Fin.last s) y * A₀⁻¹ =
      α (spMap (n := s+1) σ.symm.toRingHom (longBlock F (s+1) (Fin.last s) y)) := by
    rw [hA₀ (spMap (n := s+1) σ.symm.toRingHom (longBlock F (s+1) (Fin.last s) y)),
      hsp]
  rw [hconj, hsp']
  exact hα_mem_all (Matrix.SpecialLinearGroup.map σ.symm.toRingHom y)

private theorem exists_overlap_aut {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂ : StatedSp (s+2) F →* G}
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂)
    (hov : (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))).range =
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))).range) :
    ∃ α : MulAut (StatedSp (s+1) F), ∀ g : StatedSp (s+1) F,
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))) (α g) =
        (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))) g := by
  let e₁ : StatedSp (s+1) F →* G := κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))
  let e₂ : StatedSp (s+1) F →* G := κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))
  have he₁ : Function.Injective e₁ := hκ₁.comp (spEmbed_injective _)
  have he₂ : Function.Injective e₂ := hκ₂.comp (spEmbed_injective _)
  let α : MulAut (StatedSp (s+1) F) :=
    (MonoidHom.ofInjective he₁).trans
      ((MulEquiv.subgroupCongr hov).trans (MonoidHom.ofInjective he₂).symm)
  have hα_apply : ∀ g : StatedSp (s+1) F, e₂ (α g) = e₁ g := by
    intro g
    have h1 : (MonoidHom.ofInjective he₂) (α g) =
        (MulEquiv.subgroupCongr hov) ((MonoidHom.ofInjective he₁) g) := by
      dsimp only [α]
      change (MonoidHom.ofInjective he₂)
          ((MonoidHom.ofInjective he₂).symm
            ((MulEquiv.subgroupCongr hov) ((MonoidHom.ofInjective he₁) g))) =
        (MulEquiv.subgroupCongr hov) ((MonoidHom.ofInjective he₁) g)
      rw [MulEquiv.apply_symm_apply]
    have h2 : (((MulEquiv.subgroupCongr hov) ((MonoidHom.ofInjective he₁) g) : e₂.range) : G) =
        e₁ g := by
      rw [MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
    have h3 : (((MonoidHom.ofInjective he₂) (α g) : e₂.range) : G) = e₂ (α g) :=
      MonoidHom.ofInjective_apply he₂
    rw [← h3, h1, h2]
  refine ⟨α, fun g => ?_⟩
  exact hα_apply g

private theorem exists_corrected_chart {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] [Finite F]
    [CharP F 2] {G : Type} [Group G] {κ₁ κ₂ : StatedSp (s+2) F →* G}
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂)
    (hov : (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))).range =
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))).range)
    (hlong : (κ₁.comp (longBlock F (s+2) (Fin.last (s+1)))).range =
      (κ₂.comp (longBlock F (s+2) (Fin.last s).castSucc)).range) :
    ∃ (κ₂' : StatedSp (s+2) F →* G) (A₀ : StatedSp (s+1) F) (σ : F ≃+* F),
      Function.Injective κ₂' ∧ κ₂'.range = κ₂.range ∧
      κ₂' = κ₂.comp ((MulAut.conj (spEmbed Fin.castSucc
        (Fin.castSucc_injective (s+1)) A₀)).toMonoidHom.comp
          (spMap (n := s+2) σ.toRingHom)) ∧
      κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))) =
        κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1))) ∧
      (∀ x ∈ (longBlock F (s+1) (Fin.last s)).range,
        A₀ * x * A₀⁻¹ ∈ (longBlock F (s+1) (Fin.last s)).range) := by
  obtain ⟨α, hα⟩ := exists_overlap_aut hκ₁ hκ₂ hov
  obtain ⟨A₀, σ, hA₀⟩ :=
    exists_conj_spMap_of_mulAut hs α (longBlock_map_mem_range hκ₂ hα hlong)
  let Aemb : StatedSp (s+2) F := spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀
  let β : StatedSp (s+2) F →* StatedSp (s+2) F :=
    (MulAut.conj Aemb).toMonoidHom.comp (spMap (n := s+2) σ.toRingHom)
  let κ₂' : StatedSp (s+2) F →* G := κ₂.comp β
  have hβ_inj : Function.Injective β :=
    (MulAut.conj Aemb).injective.comp (spMap_injective σ.toRingHom)
  have hβ_surj : Function.Surjective β :=
    (MulAut.conj Aemb).surjective.comp (spMap_surjective σ)
  have hκ₂'_inj : Function.Injective κ₂' := hκ₂.comp hβ_inj
  have hκ₂'_range : κ₂'.range = κ₂.range := by
    change (κ₂.comp β).range = κ₂.range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hβ_surj, Subgroup.map_top]
  have hkey : κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))) =
      κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1))) := by
    refine MonoidHom.ext fun g => ?_
    have hβg : β (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) g) =
        spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) (α g) := by
      change Aemb * spMap (n := s+2) σ.toRingHom
          (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) g) * Aemb⁻¹ =
        spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) (α g)
      rw [spMap_spEmbed (φ := σ.toRingHom) (σ := Fin.castSucc)
        (Fin.castSucc_injective (s+1))]
      rw [hA₀ g]
      dsimp only [Aemb]
      rw [map_mul, map_mul, map_inv]
    change κ₂ (β (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) g)) =
      (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))) g
    rw [hβg]
    exact hα g
  refine ⟨κ₂', A₀, σ, hκ₂'_inj, hκ₂'_range, rfl, hkey, ?_⟩
  exact longBlock_normalizes hκ₂ hα hlong hA₀

private theorem shortBlock_range_eq {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂' : StatedSp (s+2) F →* G}
    (hkey : κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))) =
      κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))) :
    ∀ k : Fin s,
      (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
        (κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range := by
  intro k
  let S : SL(2, F) →* StatedSp (s+1) F := shortBlock F (Fin.castSucc_lt_succ (i := k)).ne
  have h1 : (spEmbed Fin.succ (Fin.succ_injective (s+1))).comp S =
      shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne :=
    spEmbed_comp_shortBlock_of_injective (Fin.succ_injective (s+1)) _
  have h2 : (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))).comp S =
      shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne :=
    spEmbed_comp_shortBlock_of_injective (Fin.castSucc_injective (s+1)) _
  have hhom : κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne) =
      κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne) := by
    calc κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)
        = κ₁.comp ((spEmbed Fin.succ (Fin.succ_injective (s+1))).comp S) := by rw [h1]
      _ = (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))).comp S := by
          rw [MonoidHom.comp_assoc]
      _ = (κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))).comp S := by
          rw [← hkey]
      _ = κ₂'.comp ((spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))).comp S) := by
          rw [MonoidHom.comp_assoc]
      _ = κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne) := by rw [h2]
  exact congrArg MonoidHom.range hhom

private theorem longBlock_range_eq {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂' : StatedSp (s+2) F →* G}
    (hkey : κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))) =
      κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))) :
    (κ₁.comp (longBlock F (s+2) (Fin.last (s+1)))).range =
      (κ₂'.comp (longBlock F (s+2) (Fin.last s).castSucc)).range := by
  have h1 : (spEmbed Fin.succ (Fin.succ_injective (s+1))).comp
      (longBlock F (s+1) (Fin.last s)) = longBlock F (s+2) (Fin.last (s+1)) :=
    MonoidHom.ext fun A => spEmbed_longBlock (Fin.succ_injective (s+1)) (Fin.last s) A
  have h2 : (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))).comp
      (longBlock F (s+1) (Fin.last s)) = longBlock F (s+2) (Fin.last s).castSucc :=
    MonoidHom.ext fun A => spEmbed_longBlock (Fin.castSucc_injective (s+1)) (Fin.last s) A
  have hhom : κ₁.comp (longBlock F (s+2) (Fin.last (s+1))) =
      κ₂'.comp (longBlock F (s+2) (Fin.last s).castSucc) := by
    calc κ₁.comp (longBlock F (s+2) (Fin.last (s+1)))
        = κ₁.comp ((spEmbed Fin.succ (Fin.succ_injective (s+1))).comp
            (longBlock F (s+1) (Fin.last s))) := by rw [h1]
      _ = (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s+1)))).comp
            (longBlock F (s+1) (Fin.last s)) := by rw [MonoidHom.comp_assoc]
      _ = (κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)))).comp
            (longBlock F (s+1) (Fin.last s)) := by rw [← hkey]
      _ = κ₂'.comp ((spEmbed Fin.castSucc (Fin.castSucc_injective (s+1))).comp
            (longBlock F (s+1) (Fin.last s))) := by rw [MonoidHom.comp_assoc]
      _ = κ₂'.comp (longBlock F (s+2) (Fin.last s).castSucc) := by rw [h2]
  exact congrArg MonoidHom.range hhom

private theorem shortBlock_last_mem_spEmbed_natAdd {s : ℕ} {F : Type} [Field F]
    (z : SL(2, F)) :
    shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne z ∈
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2)) (Fin.natAdd_injective 2 s)).range := by
  refine ⟨(shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)) z, ?_⟩
  exact DFunLike.congr_fun
    (spEmbed_comp_shortBlock_of_injective (Fin.natAdd_injective 2 s)
      (zero_ne_one : (0 : Fin 2) ≠ 1)) z

private theorem longBlock_last_mem_spEmbed_natAdd {s : ℕ} {F : Type} [Field F]
    (z : SL(2, F)) :
    longBlock F (s+2) (Fin.last (s+1)) z ∈
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2)) (Fin.natAdd_injective 2 s)).range :=
  ⟨longBlock F 2 1 z, spEmbed_longBlock (Fin.natAdd_injective 2 s) 1 z⟩

private theorem mem_range_spEmbed_castLE {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ : StatedSp (s+2) F →* G} {a : G}
    (ha : a ∈ (κ₁.comp (shortBlock F
      (Fin.castSucc_lt_succ (i := (0 : Fin (s+1)))).ne)).range) :
    a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s+2))
      (Fin.castLE_injective _))).range := by
  have h1 : (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s+2))
      (Fin.castLE_injective _)).comp
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)) =
      shortBlock F (Fin.castSucc_lt_succ (i := (0 : Fin (s+1)))).ne :=
    spEmbed_comp_shortBlock_of_injective (Fin.castLE_injective _)
      (zero_ne_one : (0 : Fin 2) ≠ 1)
  have hle : (shortBlock F (Fin.castSucc_lt_succ (i := (0 : Fin (s+1)))).ne).range ≤
      (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s+2))
        (Fin.castLE_injective _)).range := by
    rw [← h1, MonoidHom.range_comp]
    exact Subgroup.map_le_range
      (f := spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s+2))
        (Fin.castLE_injective _)) _
  rw [MonoidHom.range_comp] at ha ⊢
  exact Subgroup.map_mono hle ha

private theorem mem_range_comp_spEmbed_natAdd {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₂ : StatedSp (s+2) F →* G} {A₀ : StatedSp (s+1) F} {σ : F ≃+* F}
    (hA : ∀ x ∈ (longBlock F (s+1) (Fin.last s)).range,
      A₀ * x * A₀⁻¹ ∈ (longBlock F (s+1) (Fin.last s)).range)
    {z : StatedSp (s+2) F}
    (hz : spMap (n := s+2) σ.toRingHom z ∈ (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2))
      (Fin.natAdd_injective 2 s)).range) :
    κ₂ (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀ *
        spMap (n := s+2) σ.toRingHom z *
        (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀)⁻¹) ∈
      (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2))
        (Fin.natAdd_injective 2 s))).range := by
  rw [MonoidHom.range_comp]
  refine Subgroup.mem_map.mpr ⟨_, ?_, rfl⟩
  exact spEmbed_castSucc_conj_mem_range_spEmbed_natAdd hA hz

private theorem cross_short_short {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂ : StatedSp (s+2) F →* G} {A₀ : StatedSp (s+1) F} {σ : F ≃+* F}
    (hA : ∀ x ∈ (longBlock F (s+1) (Fin.last s)).range,
      A₀ * x * A₀⁻¹ ∈ (longBlock F (s+1) (Fin.last s)).range)
    (hcross : ∀ a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s+2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a)
    {κ₂' : StatedSp (s+2) F →* G}
    (hκ₂' : κ₂' = κ₂.comp ((MulAut.conj (spEmbed Fin.castSucc
      (Fin.castSucc_injective (s+1)) A₀)).toMonoidHom.comp
        (spMap (n := s+2) σ.toRingHom))) :
    ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s+1)))).ne)).range,
      ∀ b ∈ (κ₂'.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range, a * b = b * a := by
  intro a ha b hb
  refine hcross a (mem_range_spEmbed_castLE ha) b ?_
  obtain ⟨z, hz⟩ := hb
  rw [← hz, hκ₂']
  have hzmem : spMap (n := s+2) σ.toRingHom
      (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne z) ∈
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2)) (Fin.natAdd_injective 2 s)).range := by
    rw [spMap_shortBlock]
    exact shortBlock_last_mem_spEmbed_natAdd
      (Matrix.SpecialLinearGroup.map σ.toRingHom z)
  change κ₂ (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀ *
      spMap (n := s+2) σ.toRingHom
        (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne z) *
      (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀)⁻¹) ∈
    (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2))
      (Fin.natAdd_injective 2 s))).range
  exact mem_range_comp_spEmbed_natAdd hA hzmem

private theorem cross_short_long {s : ℕ} {F : Type} [Field F] {G : Type} [Group G]
    {κ₁ κ₂ : StatedSp (s+2) F →* G} {A₀ : StatedSp (s+1) F} {σ : F ≃+* F}
    (hA : ∀ x ∈ (longBlock F (s+1) (Fin.last s)).range,
      A₀ * x * A₀⁻¹ ∈ (longBlock F (s+1) (Fin.last s)).range)
    (hcross : ∀ a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s+2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a)
    {κ₂' : StatedSp (s+2) F →* G}
    (hκ₂' : κ₂' = κ₂.comp ((MulAut.conj (spEmbed Fin.castSucc
      (Fin.castSucc_injective (s+1)) A₀)).toMonoidHom.comp
        (spMap (n := s+2) σ.toRingHom))) :
    ∀ a ∈ (κ₁.comp (shortBlock F
        (Fin.castSucc_lt_succ (i := (0 : Fin (s+1)))).ne)).range,
      ∀ b ∈ (κ₂'.comp (longBlock F (s+2) (Fin.last (s+1)))).range, a * b = b * a := by
  intro a ha b hb
  refine hcross a (mem_range_spEmbed_castLE ha) b ?_
  obtain ⟨z, hz⟩ := hb
  rw [← hz, hκ₂']
  have hzmem : spMap (n := s+2) σ.toRingHom
      (longBlock F (s+2) (Fin.last (s+1)) z) ∈
      (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2)) (Fin.natAdd_injective 2 s)).range := by
    rw [spMap_longBlock]
    exact longBlock_last_mem_spEmbed_natAdd
      (Matrix.SpecialLinearGroup.map σ.toRingHom z)
  change κ₂ (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀ *
      spMap (n := s+2) σ.toRingHom
        (longBlock F (s+2) (Fin.last (s+1)) z) *
      (spEmbed Fin.castSucc (Fin.castSucc_injective (s+1)) A₀)⁻¹) ∈
    (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s+2))
      (Fin.natAdd_injective 2 s))).range
  exact mem_range_comp_spEmbed_natAdd hA hzmem

theorem exists_spSpCharts_of_overlap {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F] [Finite F]
    [CharP F 2] {G : Type} [Group G] {κ₁ κ₂ : StatedSp (s + 2) F →* G}
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂)
    (hov : (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range)
    (hlong : (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
      (κ₂.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range)
    (hcross : ∀ a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a) :
    ∃ κ₂' : StatedSp (s + 2) F →* G, Function.Injective κ₂' ∧ κ₂'.range = κ₂.range ∧
      (∀ k : Fin s,
        (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
          (κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range) ∧
      (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
        (κ₂'.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range ∧
      (∀ a ∈ (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
          a * b = b * a) ∧
      ∀ a ∈ (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂'.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a := by
  obtain ⟨κ₂', A₀, σ, hκ₂'_inj, hκ₂'_range, hκ₂'_form, hkey, hA⟩ :=
    exists_corrected_chart hs hκ₁ hκ₂ hov hlong
  exact ⟨κ₂', hκ₂'_inj, hκ₂'_range, shortBlock_range_eq hkey, longBlock_range_eq hkey,
    cross_short_short hA hcross hκ₂'_form, cross_short_long hA hcross hκ₂'_form⟩


section Planes

open CFSG.ClassicalInvolution.Models.SymplecticPairs (suppGroup commute_suppGroup_compl
  map_conj_range_spEmbed_of_longBlock range_spEmbed suppGroup_mono par_inr coords ParClosed)

theorem exists_spSpCharts_of_overlap_of_planes {s : ℕ} (hs : 1 ≤ s) {F : Type} [Field F]
    [Finite F] [CharP F 2] {G : Type} [Group G] {κ₁ κ₂ : StatedSp (s + 2) F →* G}
    (hκ₁ : Function.Injective κ₁) (hκ₂ : Function.Injective κ₂)
    (hov : (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).range =
      (κ₂.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).range)
    (hplane : ∀ j : Fin (s + 1), (κ₁.comp (longBlock F (s + 2) j.succ)).range =
      (κ₂.comp (longBlock F (s + 2) j.castSucc)).range)
    (hcross : ∀ a ∈ (κ₁.comp (spEmbed (Fin.castLE (Nat.le_add_left 2 s) : Fin 2 → Fin (s + 2))
        (Fin.castLE_injective _))).range,
      ∀ b ∈ (κ₂.comp (spEmbed (Fin.natAdd s : Fin 2 → Fin (s + 2))
        (Fin.natAdd_injective 2 s))).range, a * b = b * a) :
    ∃ κ₂' : StatedSp (s + 2) F →* G, Function.Injective κ₂' ∧ κ₂'.range = κ₂.range ∧
      (∀ k : Fin s,
        (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.succ)).ne)).range =
          (κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := k.castSucc)).ne)).range) ∧
      (κ₁.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range =
        (κ₂'.comp (longBlock F (s + 2) (Fin.last s).castSucc)).range ∧
      (∀ a ∈ (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂'.comp (shortBlock F (Fin.castSucc_lt_succ (i := Fin.last s)).ne)).range,
          a * b = b * a) ∧
      (∀ a ∈ (κ₁.comp (shortBlock F (Fin.castSucc_lt_succ (i := (0 : Fin (s + 1)))).ne)).range,
        ∀ b ∈ (κ₂'.comp (longBlock F (s + 2) (Fin.last (s + 1)))).range, a * b = b * a) ∧
      ∀ {k : ℕ} (τ : Fin k → Fin (s + 2)) (hτ : Function.Injective τ),
        (κ₂'.comp (spEmbed τ hτ)).range = (κ₂.comp (spEmbed τ hτ)).range := by
  obtain ⟨κ₂', A₀, σ, hκ₂'_inj, hκ₂'_range, hκ₂'_form, hkey, hA⟩ :=
    exists_corrected_chart hs hκ₁ hκ₂ hov (hplane (Fin.last s))
  refine ⟨κ₂', hκ₂'_inj, hκ₂'_range, shortBlock_range_eq hkey, longBlock_range_eq hkey,
    cross_short_short hA hcross hκ₂'_form, cross_short_long hA hcross hκ₂'_form, ?_⟩
  let Ã : StatedSp (s + 2) F := spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)) A₀
  let T : Set (Fin (s + 2) ⊕ Fin (s + 2)) :=
    Set.range (Sum.map (Fin.castSucc : Fin (s + 1) → Fin (s + 2))
      (Fin.castSucc : Fin (s + 1) → Fin (s + 2)))
  have hT : T = Set.range (Sum.map (Fin.castSucc : Fin (s + 1) → Fin (s + 2))
      (Fin.castSucc : Fin (s + 1) → Fin (s + 2))) := rfl
  have hform : κ₂' = κ₂.comp ((MulAut.conj Ã).toMonoidHom.comp
      (spMap (n := s + 2) σ.toRingHom)) := hκ₂'_form
  have hrange_β : ∀ {M : Type} [Group M] (L : M →* StatedSp (s + 2) F),
      (((MulAut.conj Ã).toMonoidHom.comp (spMap (n := s + 2) σ.toRingHom)).comp L).range =
        (L.range.map (spMap (n := s + 2) σ.toRingHom)).map
          (MulAut.conj Ã).toMonoidHom := by
    intro M _ L
    rw [MonoidHom.comp_assoc, MonoidHom.range_comp, MonoidHom.range_comp]
  have hS : ParClosed T := by
    rw [hT]
    rintro _ ⟨w, rfl⟩
    rcases w with w | w
    · exact ⟨Sum.inr w, rfl⟩
    · exact ⟨Sum.inl w, rfl⟩
  have hÃT : Ã ∈ suppGroup T := by
    rw [hT, ← range_spEmbed (K := F) (Fin.castSucc_injective (s + 1))]
    exact ⟨A₀, rfl⟩
  have hlast_inl : (Sum.inl (Fin.last (s + 1)) : Fin (s + 2) ⊕ Fin (s + 2)) ∉ T := by
    rw [hT]
    rintro ⟨w, hw⟩
    rcases w with i | i
    · rw [Sum.map_inl] at hw
      exact (Fin.castSucc_lt_last i).ne (Sum.inl_injective hw)
    · rw [Sum.map_inr] at hw
      exact Sum.inr_ne_inl hw
  have hlast_not : ∀ a ∈ coords (Fin.last (s + 1)), a ∉ T := by
    intro a ha
    rcases mem_coords.1 ha with rfl | rfl
    · exact hlast_inl
    · intro hmem
      have h := hS _ hmem
      simp only [par_inr] at h
      exact hlast_inl h
  have hcompl : Ã ∈ suppGroup ((coords (Fin.last (s + 1)))ᶜ) :=
    suppGroup_mono (fun a ha hc => hlast_not a hc ha) hÃT
  have hfix : ∀ y ∈ suppGroup (coords (Fin.last (s + 1))), Ã * y * Ã⁻¹ = y := by
    intro y hy
    have hcomm : Commute y Ã := commute_suppGroup_compl hy hcompl
    rw [← hcomm.eq, mul_assoc, mul_inv_cancel, mul_one]
  have hÃblock : ∀ j : Fin (s + 2),
      (longBlock F (s + 2) j).range.map (MulAut.conj Ã).toMonoidHom =
        (longBlock F (s + 2) j).range := by
    intro j
    rcases Fin.eq_castSucc_or_eq_last (n := s + 1) j with ⟨j', rfl⟩ | rfl
    · have hLc : (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1))).comp
          (longBlock F (s + 1) j') = longBlock F (s + 2) j'.castSucc :=
        MonoidHom.ext fun A => spEmbed_longBlock (Fin.castSucc_injective (s + 1)) j' A
      have hLs : (spEmbed Fin.succ (Fin.succ_injective (s + 1))).comp
          (longBlock F (s + 1) j') = longBlock F (s + 2) j'.succ :=
        MonoidHom.ext fun A => spEmbed_longBlock (Fin.succ_injective (s + 1)) j' A
      have hhom : κ₂'.comp (longBlock F (s + 2) j'.castSucc) =
          κ₁.comp (longBlock F (s + 2) j'.succ) := by
        calc κ₂'.comp (longBlock F (s + 2) j'.castSucc)
            = κ₂'.comp ((spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1))).comp
                (longBlock F (s + 1) j')) := by rw [← hLc]
          _ = (κ₂'.comp (spEmbed Fin.castSucc (Fin.castSucc_injective (s + 1)))).comp
                (longBlock F (s + 1) j') := by rw [MonoidHom.comp_assoc]
          _ = (κ₁.comp (spEmbed Fin.succ (Fin.succ_injective (s + 1)))).comp
                (longBlock F (s + 1) j') := by rw [hkey]
          _ = κ₁.comp ((spEmbed Fin.succ (Fin.succ_injective (s + 1))).comp
                (longBlock F (s + 1) j')) := by rw [MonoidHom.comp_assoc]
          _ = κ₁.comp (longBlock F (s + 2) j'.succ) := by rw [hLs]
      have hrange_eq : (κ₂'.comp (longBlock F (s + 2) j'.castSucc)).range =
          (κ₂.comp (longBlock F (s + 2) j'.castSucc)).range := by
        rw [hhom]
        exact hplane j'
      have hspMap_block : ((longBlock F (s + 2) j'.castSucc).range.map
          (spMap (n := s + 2) σ.toRingHom)) =
            (longBlock F (s + 2) j'.castSucc).range := by
        refine le_antisymm ?_ ?_
        · rintro _ ⟨x, hx, rfl⟩
          obtain ⟨A, rfl⟩ := hx
          rw [spMap_longBlock]
          exact ⟨Matrix.SpecialLinearGroup.map σ.toRingHom A, rfl⟩
        · intro y hy
          obtain ⟨A, rfl⟩ := hy
          refine ⟨longBlock F (s + 2) j'.castSucc
            (Matrix.SpecialLinearGroup.map σ.symm.toRingHom A), ⟨_, rfl⟩, ?_⟩
          rw [spMap_longBlock]
          congr 1
          ext i j
          simp
      apply Subgroup.map_injective (f := κ₂) hκ₂
      rw [← hspMap_block, ← hrange_β (longBlock F (s + 2) j'.castSucc),
        ← MonoidHom.range_comp, ← MonoidHom.comp_assoc, ← hform, hrange_eq,
        MonoidHom.range_comp, hspMap_block]
    · have hlastrange : (longBlock F (s + 2) (Fin.last (s + 1))).range =
          suppGroup (coords (Fin.last (s + 1))) := range_longBlock _
      rw [hlastrange]
      refine le_antisymm ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩
        change Ã * y * Ã⁻¹ ∈ suppGroup (coords (Fin.last (s + 1)))
        rw [hfix y hy]
        exact hy
      · intro y hy
        exact ⟨y, hy, by
          change Ã * y * Ã⁻¹ = y
          rw [hfix y hy]⟩
  have hspMap_range : ∀ {k : ℕ} (τ : Fin k → Fin (s + 2)) (hτ : Function.Injective τ),
      (spEmbed τ hτ).range.map (spMap (n := s + 2) σ.toRingHom) =
        (spEmbed τ hτ).range := by
    intro k τ hτ
    refine le_antisymm ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, rfl⟩ := hx
      rw [spMap_spEmbed]
      exact ⟨spMap (n := k) σ.toRingHom y, rfl⟩
    · intro y hy
      obtain ⟨x, rfl⟩ := hy
      obtain ⟨x', rfl⟩ := spMap_surjective (n := k) σ x
      exact ⟨spEmbed τ hτ x', ⟨x', rfl⟩, by rw [spMap_spEmbed]⟩
  intro k τ hτ
  have hconj := map_conj_range_spEmbed_of_longBlock (A := Ã) hÃblock hτ
  have hsp := hspMap_range τ hτ
  calc (κ₂'.comp (spEmbed τ hτ)).range
      = ((κ₂.comp ((MulAut.conj Ã).toMonoidHom.comp
            (spMap (n := s + 2) σ.toRingHom))).comp (spEmbed τ hτ)).range := by rw [hform]
    _ = (κ₂.comp (((MulAut.conj Ã).toMonoidHom.comp
            (spMap (n := s + 2) σ.toRingHom)).comp (spEmbed τ hτ))).range := by
          rw [MonoidHom.comp_assoc]
    _ = ((((MulAut.conj Ã).toMonoidHom.comp
            (spMap (n := s + 2) σ.toRingHom)).comp (spEmbed τ hτ)).range).map κ₂ := by
          rw [MonoidHom.range_comp]
    _ = (((spEmbed τ hτ).range.map (spMap (n := s + 2) σ.toRingHom)).map
            (MulAut.conj Ã).toMonoidHom).map κ₂ := by
          rw [hrange_β (spEmbed τ hτ)]
    _ = ((spEmbed τ hτ).range.map (MulAut.conj Ã).toMonoidHom).map κ₂ := by rw [hsp]
    _ = (spEmbed τ hτ).range.map κ₂ := by rw [hconj]
    _ = (κ₂.comp (spEmbed τ hτ)).range := by rw [MonoidHom.range_comp]

end Planes

end CFSG.ClassicalInvolution.WeakCT

end
