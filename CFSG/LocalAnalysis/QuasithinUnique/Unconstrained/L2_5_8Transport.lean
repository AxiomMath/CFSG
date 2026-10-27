module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2pFactsTransport

public section

namespace CFSG.QuasithinUnique.Unc25Small

open CFSG.Open CFSG.Quasithin

variable {X Y : Type} [Group X] [Group Y]

theorem congr_conj_apply (e : X ≃* Y) (x : X) (y : Y) :
    MulAut.congr e (MulAut.conj x) y = MulAut.conj (e x) y := by
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem congr_mem_innerAut (e : X ≃* Y) {φ : MulAut X} (h : φ ∈ innerAut X) :
    MulAut.congr e φ ∈ innerAut Y := by
  obtain ⟨x, rfl⟩ := h
  refine ⟨e x, ?_⟩
  ext y
  exact (congr_conj_apply e x y).symm

theorem mem_innerAut_of_congr (e : X ≃* Y) {φ : MulAut X} (h : MulAut.congr e φ ∈ innerAut Y) :
    φ ∈ innerAut X := by
  obtain ⟨y, hy⟩ := h
  refine ⟨e.symm y, ?_⟩
  ext x
  have := congrArg (fun ψ : MulAut Y => e.symm (ψ (e x))) hy
  simp only [MulAut.conj_apply, MulAut.congr_apply] at this
  simpa using this

theorem mem_map_iff (e : X ≃* Y) {P : Subgroup X} (x : X) :
    e x ∈ P.map e.toMonoidHom ↔ x ∈ P := by
  rw [Subgroup.mem_map_equiv]
  simp

theorem isFourSubgroup_map (e : X ≃* Y) {F : Subgroup X} (hF : IsFourSubgroup F) :
    IsFourSubgroup (F.map e.toMonoidHom) := by
  obtain ⟨⟨hc, hexp⟩, hcard⟩ := hF
  have := hc
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩, ?_⟩
  · apply Subtype.ext
    obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    show (a : Y) * b = b * a
    rw [← ha, ← hb]
    show e.toMonoidHom a' * e.toMonoidHom b' = e.toMonoidHom b' * e.toMonoidHom a'
    rw [← map_mul, ← map_mul, setLike_mul_comm ha' hb']
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    show e.toMonoidHom x ^ 2 = 1
    rw [← map_pow, hexp x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hcard

theorem isSylowTwoOf_top_map' [Finite X] [Finite Y] (e : X ≃* Y) {P : Subgroup X}
    (hP : IsSylowTwoOf P ⊤) : IsSylowTwoOf (P.map e.toMonoidHom) ⊤ :=
  Unc25K1.isSylowTwoOf_top_map e hP

theorem normalizer_map (e : X ≃* Y) (P : Subgroup X) :
    (Subgroup.normalizer (P : Set X)).map e.toMonoidHom =
      Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  simp only [MulEquiv.symm_apply_apply]
  constructor
  · intro h z
    obtain ⟨z', rfl⟩ := e.surjective z
    rw [mem_map_iff, ← map_mul, ← map_inv, ← map_mul, mem_map_iff]
    exact h z'
  · intro h z
    have := h (e z)
    rw [mem_map_iff, ← map_mul, ← map_inv, ← map_mul, mem_map_iff] at this
    exact this

theorem SmallListFacts.of_mulEquiv [Finite X] (e : X ≃* Y) (h : SmallListFacts Y) :
    SmallListFacts X := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  have := h.simple
  refine
    { simple := e.isSimpleGroup
      out_two := ?_
      sylow_shape := ?_
      sylow_normalizer := ?_
      four_normalizer := ?_
      four_fixes := ?_ }
  · intro φ
    obtain ⟨k, hk⟩ := h.out_two (MulAut.congr e φ)
    refine ⟨k, mem_innerAut_of_congr e ?_⟩
    rw [map_pow]
    exact hk
  · intro P hP
    have hP' := isSylowTwoOf_top_map' e hP
    let eP : ↥P ≃* ↥(P.map e.toMonoidHom) := Subgroup.equivMapOfInjective P e.toMonoidHom e.injective
    rcases h.sylow_shape _ hP' with ⟨n, hn, ⟨e'⟩⟩ | ⟨⟨e'⟩⟩
    · exact Or.inl ⟨n, hn, ⟨eP.trans e'⟩⟩
    · exact Or.inr ⟨eP.trans e'⟩
  · intro P hP n hn
    have hP' := isSylowTwoOf_top_map' e hP
    have h1 : e n ∈ Subgroup.normalizer ((P.map e.toMonoidHom : Subgroup Y) : Set Y) := by
      rw [← normalizer_map]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hn
    have h2 := h.sylow_normalizer _ hP' h1
    exact (mem_map_iff e n).mp h2
  · intro F hF
    have hF' := isFourSubgroup_map e hF
    obtain ⟨e'⟩ := h.four_normalizer _ hF'
    rw [← normalizer_map] at e'
    exact ⟨(Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans e'⟩
  · intro P hP F hFP hF φ hφ y
    have hP' := isSylowTwoOf_top_map' e hP
    have hF' := isFourSubgroup_map e hF
    have hFP' : F.map e.toMonoidHom ≤ P.map e.toMonoidHom := Subgroup.map_mono hFP
    have hfix : ∀ f ∈ F.map e.toMonoidHom, MulAut.congr e φ f = f := by
      intro f hf
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
      show MulAut.congr e φ (e x) = e x
      rw [MulAut.congr_apply]
      simp [hφ x hx]
    have := h.four_fixes _ hP' _ hFP' hF' (MulAut.congr e φ) hfix (e y)
    have e1 : MulAut.congr e φ (e y) = e (φ y) := by
      rw [MulAut.congr_apply]; simp
    rw [e1, mem_map_iff, mem_map_iff] at this
    exact this

theorem FixPointwiseInner.of_mulEquiv [Finite X] (e : X ≃* Y) (h : FixPointwiseInner Y) :
    FixPointwiseInner X := by
  have : Finite Y := Finite.of_equiv X e.toEquiv
  intro P hP α hα
  have hP' := isSylowTwoOf_top_map' e hP
  refine mem_innerAut_of_congr e (h _ hP' (MulAut.congr e α) ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  show MulAut.congr e α (e x) = e x
  rw [MulAut.congr_apply]
  simp [hα x hx]

end CFSG.QuasithinUnique.Unc25Small
