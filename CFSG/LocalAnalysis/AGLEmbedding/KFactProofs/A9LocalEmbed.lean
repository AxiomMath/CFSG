module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA9Defs
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding

open Equiv

theorem exists_embedding_alternating {Y : Type} [Group Y] (K : Subgroup Y) [K.Normal]
    (e : K ≃* alternatingGroup (Fin 9)) (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    ∃ φ : Y →* Perm (Fin 9), Function.Injective φ ∧ alternatingGroup (Fin 9) ≤ φ.range := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  let cEquiv : Perm (Fin 9) ≃* MulAut (alternatingGroup (Fin 9)) := MulEquiv.ofBijective _ hbij
  let ec : Y →* MulAut (alternatingGroup (Fin 9)) :=
    (MulAut.congr e).toMonoidHom.comp (MulAut.conjNormal (H := K))
  refine ⟨cEquiv.symm.toMonoidHom.comp ec, ?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : ec y = 1 := by
      have := congrArg cEquiv hy
      simpa using this
    have h2 : ∀ k : K, y * k * y⁻¹ = k := by
      intro k
      have h3 := congrArg (fun f : MulAut (alternatingGroup (Fin 9)) => f (e k)) h1
      simp only [ec, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
        MulAut.congr_apply, MulAut.one_apply, MulEquiv.trans_apply,
        MulEquiv.symm_apply_apply] at h3
      have h4 : MulAut.conjNormal y k = k := e.injective h3
      have h5 := congrArg Subtype.val h4
      rwa [MulAut.conjNormal_apply] at h5
    have : y ∈ Subgroup.centralizer (K : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := h2 ⟨k, hk⟩
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hC] at this
    exact this
  · intro σ hσ
    let a : alternatingGroup (Fin 9) := ⟨σ, hσ⟩
    refine ⟨((e.symm a : K) : Y), ?_⟩
    apply cEquiv.injective
    have h1 : cEquiv σ = MulAut.conj a := by
      show MulAut.conjNormal σ = MulAut.conj a
      exact MulAut.conjNormal_val (h := a)
    simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
      MulEquiv.apply_symm_apply, ec]
    rw [h1]
    refine MulEquiv.ext fun x => ?_
    have h2 : MulAut.conjNormal ((e.symm a : K) : Y) = MulAut.conj (e.symm a) :=
      MulAut.conjNormal_val
    simp [MulAut.congr_apply, h2]

theorem A9InSitu.of_map {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (φ : Y →* Y') (hφ : Function.Injective φ) {T B Y₀ : Subgroup Y} {T' B' Y₀' : Subgroup Y'}
    (hB : B.map φ = B') (hY₀ : Y₀.map φ = Y₀') (h : A9InSitu T' B' Y₀') :
    A9InSitu T B Y₀ := by
  subst hB hY₀
  have hnorm : ∀ {W : Subgroup Y}, Y₀ ≤ Subgroup.normalizer (W : Set Y) →
      Y₀.map φ ≤ Subgroup.normalizer ((W.map φ : Subgroup Y') : Set Y') := by
    intro W hW y' hy'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
    exact Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ (hW hy))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    rw [Subgroup.mem_set_normalizer_iff]
    intro n
    have h1 := h.le_normalizer (Subgroup.mem_map_of_mem φ hy)
    rw [Subgroup.mem_set_normalizer_iff] at h1
    have h2 := h1 (φ n)
    simp only [SetLike.mem_coe, Subgroup.mem_map_iff_mem hφ] at h2 ⊢
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hφ] at h2
    exact h2
  · intro W hW hN hc
    have := h.primeCore (W.map φ) (Subgroup.map_mono hW) (hnorm hN)
      (by rwa [Subgroup.card_map_of_injective hφ])
    exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1 this
  · intro W hW hN
    rcases h.normal_dichotomy (W.map φ) (Subgroup.map_mono hW) (hnorm hN) with h1 | h1
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ hφ).1 h1)
    · exact Or.inr ((Subgroup.map_le_map_iff_of_injective hφ).1 h1)
  · intro y hy
    obtain ⟨hy, hyc⟩ := Subgroup.mem_inf.1 hy
    have h1 : φ y ∈ Y₀.map φ ⊓ Subgroup.centralizer ((B.map φ : Subgroup Y') : Set Y') := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem φ hy, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ hb'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hb'
      rw [← map_mul, ← map_mul]
      exact congrArg φ ((Subgroup.mem_centralizer_iff.1 hyc) b hb)
    exact (Subgroup.mem_map_iff_mem hφ).1 (h.centralizer_le h1)
  · intro W hW hN hp
    exact (Subgroup.map_le_map_iff_of_injective hφ).1
      (h.pcore_le (W.map φ) (Subgroup.map_mono hW) (hnorm hN) (hp.map φ))
  · have := h.solvable
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective Y₀ φ hφ).toMonoidHom)
      (Subgroup.equivMapOfInjective Y₀ φ hφ).injective
  · exact (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) φ hφ).trans h.pRank_le

end CFSG.AGLEmbedding
