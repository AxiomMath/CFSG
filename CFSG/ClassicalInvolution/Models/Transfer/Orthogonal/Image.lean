module

public import CFSG.ClassicalInvolution.Models.Transfer.Orthogonal.Center

public section

namespace CFSG.ClassicalInvolution.Models.Transfer

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {X : Type} [Group X]

@[expose] def IsFundamentalImage (θ : ↥(elementaryGroup Q) →* X) (L' : Subgroup X) (i' : X) :
    Prop :=
  ∃ (L : Subgroup (V ≃ₗ[K] V)) (i : V ≃ₗ[K] V) (h : IsFundamental Q L i),
    (L.subgroupOf (elementaryGroup Q)).map θ = L' ∧ θ (fundElt h) = i'

section Perfect

variable [Finite K]

theorem commutator_subgroupOf_eq_of_isFundamental (h4 : 4 ≤ Nat.card K)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    ⁅L.subgroupOf (elementaryGroup Q), L.subgroupOf (elementaryGroup Q)⁆ =
      L.subgroupOf (elementaryGroup Q) := by
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact Subgroup.isPerfect_iff.mp
    (CFSG.ClassicalInvolution.isPerfect_of_equiv_sl2 h4
      ((Subgroup.subgroupOfEquivOfLe h.le_elementaryGroup).trans e.symm))

end Perfect

section Image

variable [Finite K] {θ : ↥(elementaryGroup Q) →* X} (hodd : Odd (Nat.card K))
  (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
  (hdim : 4 < Module.finrank K V)

include hodd hker hZ hdim

theorem IsFundamentalImage.nonempty_mulEquiv {L' : Subgroup X} {i' : X}
    (h : IsFundamentalImage θ L' i') : Nonempty (L' ≃* SL(2, K)) := by
  obtain ⟨L, i, h, rfl, rfl⟩ := h
  obtain ⟨e⟩ := h.nonempty_mulEquiv
  exact ⟨(mulEquivMap (eq_one_of_mem_ker_of_isFundamental hodd hker hZ hdim h)).symm.trans
    ((Subgroup.subgroupOfEquivOfLe h.le_elementaryGroup).trans e.symm)⟩

theorem IsFundamentalImage.orderOf_eq_two {L' : Subgroup X} {i' : X}
    (h : IsFundamentalImage θ L' i') : orderOf i' = 2 := by
  obtain ⟨L, i, h, rfl, rfl⟩ := h
  refine orderOf_map_eq_two (eq_one_of_mem_ker_of_isFundamental hodd hker hZ hdim h)
    (Subgroup.mem_subgroupOf.mpr h.mem) ?_
  rw [show fundElt h = ⟨i, _⟩ from rfl, Subgroup.orderOf_mk]
  exact h.orderOf_eq_two hodd

theorem IsFundamentalImage.eq_of_orderOf_eq_two {L' : Subgroup X} {i' : X}
    (h : IsFundamentalImage θ L' i') {t : X} (ht : t ∈ L') (h2 : orderOf t = 2) : t = i' := by
  obtain ⟨L, i, h, rfl, rfl⟩ := h
  refine eq_map_of_orderOf_eq_two (eq_one_of_mem_ker_of_isFundamental hodd hker hZ hdim h)
    (fun s hs hs2 => ?_) ht h2
  have hs' : orderOf (s : V ≃ₗ[K] V) = 2 := by rw [Subgroup.orderOf_coe]; exact hs2
  exact Subtype.ext (h.eq_of_orderOf_eq_two hodd (Subgroup.mem_subgroupOf.mp hs) hs')

omit [Finite K] hodd hker hZ hdim in
theorem IsFundamentalImage.mem {L' : Subgroup X} {i' : X} (h : IsFundamentalImage θ L' i') :
    i' ∈ L' := by
  obtain ⟨L, i, h, rfl, rfl⟩ := h
  exact ⟨fundElt h, Subgroup.mem_subgroupOf.mpr h.mem, rfl⟩

omit [Finite K] hodd hker hZ hdim in
theorem IsFundamentalImage.le_centralizer {L' : Subgroup X} {i' : X}
    (h : IsFundamentalImage θ L' i') : L' ≤ Subgroup.centralizer ({i'} : Set X) := by
  obtain ⟨L, i, h, rfl, rfl⟩ := h
  rintro _ ⟨x, hx, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp
    (h.le_centralizer (Subgroup.mem_subgroupOf.mp hx)))

omit [Finite K] hodd hker hZ hdim in
theorem IsFundamentalImage.conj (hsurj : Function.Surjective θ) {L' : Subgroup X} {i' : X}
    (h : IsFundamentalImage θ L' i') (x : X) :
    IsFundamentalImage θ (L'.map (MulAut.conj x).toMonoidHom) (x * i' * x⁻¹) := by
  obtain ⟨L, i, h, rfl, rfl⟩ := h
  obtain ⟨g, rfl⟩ := hsurj x
  have h₀ := h.conj (elementaryGroup_le_orthogonalGroup Q g.2)
  refine ⟨_, _, h₀, ?_, ?_⟩
  · have e1 : (L.map (MulAut.conj (g : V ≃ₗ[K] V)).toMonoidHom).subgroupOf (elementaryGroup Q) =
        (L.subgroupOf (elementaryGroup Q)).map (MulAut.conj g).toMonoidHom := by
      ext y
      simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨x, hx, hxy⟩
        exact ⟨⟨x, h.le_elementaryGroup hx⟩, hx, Subtype.ext hxy⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨z, hz, rfl⟩
    rw [e1, Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext y
    simp
  · have : fundElt h₀ = g * fundElt h * g⁻¹ := Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv]

end Image

section Normal

variable [Finite K] [FiniteDimensional K V] {θ : ↥(elementaryGroup Q) →* X}

theorem centralizer_map_eq_of_isFundamental (hodd : Odd (Nat.card K))
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q))
    (hZ : CenterScalar Q) (hdim : 4 < Module.finrank K V)
    (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    Subgroup.centralizer ({θ (fundElt h)} : Set X) =
      (Subgroup.centralizer ({fundElt h} : Set ↥(elementaryGroup Q))).map θ :=
  centralizer_map_eq θ hsurj (kerConjFree_of_isFundamental hodd hker hZ hdim hlift h)

theorem isSubnormal_image (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (hsurj : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q))
    (hZ : CenterScalar Q) (hdim : 4 < Module.finrank K V)
    (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ) {L : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    (((L.subgroupOf (elementaryGroup Q)).map θ).subgroupOf
      (Subgroup.centralizer ({θ (fundElt h)} : Set X))).IsSubnormal := by
  have hCΩ : centralizerΩ Q i ≤ elementaryGroup Q := inf_le_left
  let ψ : ↥(centralizerΩ Q i) →* X := θ.comp (Subgroup.inclusion hCΩ)
  have hrange : ψ.range = Subgroup.centralizer ({θ (fundElt h)} : Set X) := by
    rw [centralizer_map_eq_of_isFundamental hodd hsurj hker hZ hdim hlift h]
    ext y
    constructor
    · rintro ⟨c, rfl⟩
      refine ⟨Subgroup.inclusion hCΩ c, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2)
    · rintro ⟨g, hg, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
      exact ⟨⟨(g : V ≃ₗ[K] V), Subgroup.mem_inf.mpr ⟨g.2,
        Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hg)⟩⟩, rfl⟩
  have hmap := (h.isSubnormal hodd (by omega)).map (f := ψ.rangeRestrict)
    (MonoidHom.rangeRestrict_surjective ψ)
  have e : (L.subgroupOf (centralizerΩ Q i)).map ψ.rangeRestrict =
      ((L.subgroupOf (elementaryGroup Q)).map θ).subgroupOf ψ.range := by
    ext y
    rw [Subgroup.mem_map, Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hCΩ x, hx, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨⟨(z : V ≃ₗ[K] V), h.le_centralizerΩ (Subgroup.mem_subgroupOf.mp hz)⟩,
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hz), ?_⟩
      exact Subtype.ext hzy
  rw [e] at hmap
  exact isSubnormal_subgroupOf_congr hrange hmap

theorem exists_twin_image (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
    (hdim : 4 < Module.finrank K V) (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    ∃ L₂' : Subgroup X, IsFundamentalImage θ L₂' (θ (fundElt h)) ∧
      L₂' ≠ (L.subgroupOf (elementaryGroup Q)).map θ ∧
      (∀ x ∈ (L.subgroupOf (elementaryGroup Q)).map θ, ∀ y ∈ L₂', x * y = y * x) ∧
      ∀ L'' : Subgroup X, IsFundamentalImage θ L'' (θ (fundElt h)) →
        L'' = (L.subgroupOf (elementaryGroup Q)).map θ ∨ L'' = L₂' := by
  obtain ⟨T, hT, hne, hcomm, huniq⟩ := IsFundamental.exists_twin hodd h
  refine ⟨(T.subgroupOf (elementaryGroup Q)).map θ, ⟨T, i, hT, rfl, rfl⟩, ?_, ?_, ?_⟩
  · intro heq
    have h4 : 4 ≤ Nat.card K := by omega
    have := eq_of_map_eq_map hker (commutator_subgroupOf_eq_of_isFundamental h4 hT)
      (commutator_subgroupOf_eq_of_isFundamental h4 h) heq
    have := Subgroup.subgroupOf_inj.mp this
    rw [inf_eq_left.mpr hT.le_elementaryGroup, inf_eq_left.mpr h.le_elementaryGroup] at this
    exact hne this
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg θ (Subtype.ext (hcomm x (Subgroup.mem_subgroupOf.mp hx) y
      (Subgroup.mem_subgroupOf.mp hy)))
  · rintro L'' ⟨L₀, i₀, h₀, rfl, hθ⟩
    have := eq_of_map_eq_of_isFundamental hodd hker hZ hdim hlift h h₀ hθ
    subst this
    rcases huniq L₀ h₀ with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem ncard_isFundamentalImage_eq_two (hodd : Odd (Nat.card K)) (h5 : 5 ≤ Nat.card K)
    (hker : θ.ker ≤ Subgroup.center (elementaryGroup Q)) (hZ : CenterScalar Q)
    (hdim : 4 < Module.finrank K V) (hlift : Module.finrank K V ≠ 8 ∨ KerInvolutionFree θ)
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) :
    {L' : Subgroup X | IsFundamentalImage θ L' (θ (fundElt h))}.ncard = 2 := by
  have hS : {L₀ : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L₀ i}.ncard = 2 :=
    IsFundamental.ncard_eq_two hodd h
  have himg : {L' : Subgroup X | IsFundamentalImage θ L' (θ (fundElt h))} =
      (fun L₀ => (L₀.subgroupOf (elementaryGroup Q)).map θ) ''
        {L₀ : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L₀ i} := by
    ext L'
    constructor
    · rintro ⟨L₀, i₀, h₀, rfl, hθ⟩
      have := eq_of_map_eq_of_isFundamental hodd hker hZ hdim hlift h h₀ hθ
      subst this
      exact ⟨L₀, h₀, rfl⟩
    · rintro ⟨L₀, h₀, rfl⟩
      exact ⟨L₀, i, h₀, rfl, rfl⟩
  have hinj : Set.InjOn (fun L₀ => (L₀.subgroupOf (elementaryGroup Q)).map θ)
      {L₀ : Subgroup (V ≃ₗ[K] V) | IsFundamental Q L₀ i} := by
    intro L₀ h₀ L₁ h₁ heq
    have h4 : 4 ≤ Nat.card K := by omega
    have := eq_of_map_eq_map hker (commutator_subgroupOf_eq_of_isFundamental h4 h₀)
      (commutator_subgroupOf_eq_of_isFundamental h4 h₁) heq
    have := Subgroup.subgroupOf_inj.mp this
    rwa [inf_eq_left.mpr h₀.le_elementaryGroup, inf_eq_left.mpr h₁.le_elementaryGroup] at this
  rw [himg, hinj.ncard_image, hS]

end Normal

end CFSG.ClassicalInvolution.Models.Transfer
