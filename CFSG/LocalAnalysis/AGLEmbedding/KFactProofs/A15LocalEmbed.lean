module

public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA15Defs
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.AGLEmbedding

open Equiv

theorem exists_embedding_alternating_of_ne_six {Y : Type} [Group Y] (n : ℕ) (hn : 5 ≤ n)
    (hn6 : n ≠ 6) (K : Subgroup Y) [K.Normal] (e : K ≃* alternatingGroup (Fin n))
    (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    ∃ φ : Y →* Perm (Fin n), Function.Injective φ ∧ alternatingGroup (Fin n) ≤ φ.range := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6
  let cEquiv : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) := MulEquiv.ofBijective _ hbij
  let ec : Y →* MulAut (alternatingGroup (Fin n)) :=
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
      have h3 := congrArg (fun f : MulAut (alternatingGroup (Fin n)) => f (e k)) h1
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
    let a : alternatingGroup (Fin n) := ⟨σ, hσ⟩
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

theorem A15InSitu.of_map {Y Y' : Type} [Group Y] [Finite Y] [Group Y'] [Finite Y']
    (φ : Y →* Y') (hφ : Function.Injective φ) {T Y₀ : Subgroup Y} {T' Y₀' : Subgroup Y'}
    (hT : T.map φ = T') (hY₀ : Y₀.map φ = Y₀') (h : A15InSitu T' Y₀') :
    A15InSitu T Y₀ := by
  subst hT hY₀
  have hnorm : ∀ {W : Subgroup Y}, Y₀ ≤ Subgroup.normalizer (W : Set Y) →
      Y₀.map φ ≤ Subgroup.normalizer ((W.map φ : Subgroup Y') : Set Y') := by
    intro W hW y' hy'
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hy'
    exact Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ (hW hy))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
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
    have h1 : φ y ∈ Y₀.map φ ⊓ Subgroup.centralizer ((T.map φ : Subgroup Y') : Set Y') := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem φ hy, ?_⟩
      refine Subgroup.mem_centralizer_iff.2 ?_
      rintro _ hb'
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hb'
      rw [← map_mul, ← map_mul]
      exact congrArg φ ((Subgroup.mem_centralizer_iff.1 hyc) b hb)
    exact (Subgroup.mem_map_iff_mem hφ).1 (h.centralizer_le h1)
  · intro W hW hN hp
    exact (Subgroup.map_eq_bot_iff_of_injective _ hφ).1
      (h.pcore (W.map φ) (Subgroup.map_mono hW) (hnorm hN) (hp.map φ))
  · intro U hU V _ hs hna
    let e : U ≃* U.map φ := Subgroup.equivMapOfInjective U φ hφ
    let V' : Subgroup (U.map φ) := V.map e.toMonoidHom
    have : V'.Normal := Subgroup.Normal.map ‹V.Normal› e.toMonoidHom e.surjective
    let E : U ⧸ V ≃* (U.map φ) ⧸ V' := QuotientGroup.congr V V' e rfl
    have hs' : IsSimpleGroup ((U.map φ) ⧸ V') := E.symm.isSimpleGroup
    have hna' : ∃ a b : (U.map φ) ⧸ V', a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := hna
      exact ⟨E a, E b, fun h' => hab (E.injective (by rw [map_mul, map_mul]; exact h'))⟩
    rw [Nat.card_congr E.toEquiv]
    exact h.section_card (U.map φ) (Subgroup.map_mono hU) V' hs' hna'
  · intro W hW hN hTW
    obtain ⟨J', hJ'1, hJ'2, hJ'3⟩ := h.normal_closure (W.map φ) (Subgroup.map_mono hW) (hnorm hN)
      (Subgroup.map_mono hTW)
    have hrange : ∀ i, J' i ≤ φ.range := fun i x hx => by
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.1 ((hJ'1 i).1 hx)
      exact ⟨y, rfl⟩
    have hmap : ∀ i, ((J' i).comap φ).map φ = J' i := fun i =>
      Subgroup.map_comap_eq_self (hrange i)
    refine ⟨fun i => (J' i).comap φ, fun i => ⟨?_, ?_⟩, fun i j hij => ?_, ?_⟩
    · intro x hx
      exact (Subgroup.mem_map_iff_mem hφ).1 ((hJ'1 i).1 hx)
    · obtain ⟨e⟩ := (hJ'1 i).2
      exact ⟨((Subgroup.equivMapOfInjective _ φ hφ).trans
        (MulEquiv.subgroupCongr (hmap i))).trans e⟩
    · rw [← Subgroup.map_eq_bot_iff_of_injective _ hφ, Subgroup.map_commutator, hmap i, hmap j]
      exact hJ'2 i j hij
    · rw [← Subgroup.map_le_map_iff_of_injective hφ, Subgroup.map_iSup]
      simpa only [hmap] using hJ'3

end CFSG.AGLEmbedding
