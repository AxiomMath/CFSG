module

public import CFSG.ClassicalInvolution.RouteD.GapsOrthModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.WeakCT
open CFSG.ClassicalInvolution.Generic (Commutes conjSub)
open scoped commutatorElement

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem involution_ne_of_commutes_adj (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    {c l S : Subgroup (V ≃ₗ[K] V)} {ic il iS : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (hl : IsFundamental Q l il) (hS : IsFundamental Q S iS)
    (hadj : ModelAdj (scalars K V) c l) (hSc : Commutes S c) (hSl : Commutes S l) :
    iS ≠ ic ∧ iS ≠ il := by
  have hcl : c ≠ l := hadj.1
  have hnc : ¬ Commutes c l := hadj.2.1
  obtain ⟨hcomm, -, -⟩ := adj_data hodd hdim hc hl hadj
  have hSc' : Commutes c S := commutes_symm hSc
  have hSl' : Commutes l S := commutes_symm hSl
  have hSne_c : S ≠ c := fun h => hnc (h ▸ hSl)
  have hSne_l : S ≠ l := fun h => hnc (commutes_symm (h ▸ hSc))
  have hSic : iS * ic = ic * iS := hSc iS hS.mem ic hc.mem
  have hSil : iS * il = il * iS := hSl iS hS.mem il hl.mem
  have hinv : ∀ {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V}, IsFundamental Q L i → InvOf L i :=
    fun h => ⟨h.mem, h.orderOf_eq_two hodd⟩
  have hsc : ∀ {a b : V ≃ₗ[K] V}, a * b = b * a → ⁅a, b⁆ ∈ scalars K V := fun h => by
    rw [commutatorElement_eq_one_iff_mul_comm.mpr h]
    exact Subgroup.one_mem _
  constructor
  · intro heq
    have hind := indist_of_eq hodd hdim hS hc hSne_c heq.symm
    have := hind.2 l ⟨il, hl⟩ hSne_l.symm hcl.symm
      ⟨il, iS, hinv hl, hinv hS, hsc hSil.symm⟩ ⟨il, ic, hinv hl, hinv hc, hsc hcomm.symm⟩
    exact hnc (commutes_symm (this.mp hSl'))
  · intro heq
    have hind := indist_of_eq hodd hdim hS hl hSne_l heq.symm
    have := hind.2 c ⟨ic, hc⟩ hSne_c.symm hcl
      ⟨ic, iS, hinv hc, hinv hS, hsc hSic.symm⟩ ⟨ic, il, hinv hc, hinv hl, hsc hcomm⟩
    exact hnc (this.mp hSc')

omit [FiniteDimensional K V] in
theorem negSpace_orth_of_ne (hodd : Odd (Nat.card K)) {x S : Subgroup (V ≃ₗ[K] V)}
    {ix iS : V ≃ₗ[K] V} (hx : IsFundamental Q x ix) (hS : IsFundamental Q S iS) (hne : iS ≠ ix)
    (hxS : Commutes x S) : ∀ y ∈ negSpace ix, ∀ w ∈ negSpace iS, polar Q y w = 0 := by
  rcases orth_or_twin hodd hx hS hxS with h | h
  · exact h
  · exact absurd h hne

omit [FiniteDimensional K V] in
theorem star_orth_pair (hodd : Odd (Nat.card K)) {l₁ l₂ l₃ : Subgroup (V ≃ₗ[K] V)}
    {i₁ i₂ i₃ : V ≃ₗ[K] V} (h₁ : IsFundamental Q l₁ i₁) (h₂ : IsFundamental Q l₂ i₂)
    (h₃ : IsFundamental Q l₃ i₃) (n12 : l₁ ≠ l₂) (n13 : l₁ ≠ l₃) (n23 : l₂ ≠ l₃)
    (k12 : Commutes l₁ l₂) (k13 : Commutes l₁ l₃) :
    (∀ x ∈ negSpace i₁, ∀ y ∈ negSpace i₂, polar Q x y = 0) ∨
      (∀ x ∈ negSpace i₁, ∀ y ∈ negSpace i₃, polar Q x y = 0) := by
  rcases orth_or_twin hodd h₁ h₂ k12 with o12 | t12
  · exact Or.inl o12
  rcases orth_or_twin hodd h₁ h₃ k13 with o13 | t13
  · exact Or.inr o13
  exfalso
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd h₁
  have e2 := huniq l₂ (t12 ▸ h₂)
  have e3 := huniq l₃ (t13 ▸ h₃)
  rcases e2 with e2 | e2
  · exact n12 e2.symm
  rcases e3 with e3 | e3
  · exact n13 e3.symm
  exact n23 (e2.trans e3.symm)

omit [Finite K] [FiniteDimensional K V] in
theorem eq_zero_of_mem_negSpace_posSpace (h2 : (2 : K) ≠ 0) {i : V ≃ₗ[K] V} {x : V}
    (hn : x ∈ negSpace i) (hp : x ∈ posSpace i) : x = 0 := by
  have h1 := Module.End.mem_eigenspace_iff.mp hn
  have h2' := Module.End.mem_eigenspace_iff.mp hp
  have h3 : (-1 : K) • x = (1 : K) • x := by
    rw [← h1, ← h2']
  have h4 : (2 : K) • x = 0 := by
    have : (1 : K) • x - (-1 : K) • x = 0 := by rw [h3, sub_self]
    rw [← this, ← sub_smul]
    norm_num
  exact (smul_eq_zero.mp h4).resolve_left h2

theorem finrank_chain_space (hodd : Odd (Nat.card K)) {c : Subgroup (V ≃ₗ[K] V)}
    {ic ia id : V ≃ₗ[K] V} (hc : IsFundamental Q c ic) (pda : PairDecomposition Q ic ia)
    (pdd : PairDecomposition Q ic id)
    (horth : ∀ x ∈ negSpace ia, ∀ y ∈ negSpace id, polar Q x y = 0) :
    Module.finrank K ↥(negSpace ic ⊔
      ((posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id))) = 8 := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  have hd1 : Disjoint (posSpace ic ⊓ negSpace ia) (posSpace ic ⊓ negSpace id) := by
    rw [Submodule.disjoint_def]
    intro x hxa hxd
    refine pda.nondeg₃ x hxa fun y hy => ?_
    rw [polar_comm]
    exact horth y (Submodule.mem_inf.mp hy).2 x (Submodule.mem_inf.mp hxd).2
  have h4 : Module.finrank K ↥((posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id)) = 4 := by
    rw [Frame.finrank_sup_of_disjoint hd1, pda.finrank_U₃, pdd.finrank_U₃]
  have hd2 : Disjoint (negSpace ic)
      ((posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id)) := by
    rw [Submodule.disjoint_def]
    intro x hxn hxs
    refine eq_zero_of_mem_negSpace_posSpace h2 hxn ?_
    have hle : (posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id) ≤ posSpace ic :=
      sup_le inf_le_left inf_le_left
    exact hle hxs
  rw [Frame.finrank_sup_of_disjoint hd2, h4, finrank_negSpace hodd hc]

omit [FiniteDimensional K V] in
theorem negSpace_le_orthogonal_chain (hodd : Odd (Nat.card K)) (hdim : 9 ≤ Module.finrank K V)
    [FiniteDimensional K V]
    {c la ld S : Subgroup (V ≃ₗ[K] V)} {ic ia id iS : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (ha : IsFundamental Q la ia) (hd : IsFundamental Q ld id) (hS : IsFundamental Q S iS)
    (hca : ModelAdj (scalars K V) c la) (hcd : ModelAdj (scalars K V) c ld)
    (hSc : Commutes S c) (hSa : Commutes S la) (hSd : Commutes S ld) :
    negSpace iS ≤ LinearMap.BilinForm.orthogonal (polarBilin Q) (negSpace ic ⊔
      ((posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id))) := by
  obtain ⟨hSic, hSia⟩ := involution_ne_of_commutes_adj hodd hdim hc ha hS hca hSc hSa
  obtain ⟨-, hSid⟩ := involution_ne_of_commutes_adj hodd hdim hc hd hS hcd hSc hSd
  have o_c := negSpace_orth_of_ne hodd hc hS hSic (commutes_symm hSc)
  have o_a := negSpace_orth_of_ne hodd ha hS hSia (commutes_symm hSa)
  have o_d := negSpace_orth_of_ne hodd hd hS hSid (commutes_symm hSd)
  intro w hw
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro y hy
  obtain ⟨v, hv, y', hy', rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨pa, hpa, pd, hpd, rfl⟩ := Submodule.mem_sup.mp hy'
  simp only [polarBilin_apply_apply, polar_add_left]
  rw [o_c v hv w hw, o_a pa (Submodule.mem_inf.mp hpa).2 w hw,
    o_d pd (Submodule.mem_inf.mp hpd).2 w hw]
  simp

theorem chain_centralizer (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) (hdim' : Module.finrank K V ≤ 12)
    {c la ld S : Subgroup (V ≃ₗ[K] V)} {ic ia id iS : V ≃ₗ[K] V} (hc : IsFundamental Q c ic)
    (ha : IsFundamental Q la ia) (hd : IsFundamental Q ld id) (hS : IsFundamental Q S iS)
    (hca : ModelAdj (scalars K V) c la) (hcd : ModelAdj (scalars K V) c ld)
    (horth : ∀ x ∈ negSpace ia, ∀ y ∈ negSpace id, polar Q x y = 0)
    (hSc : Commutes S c) (hSa : Commutes S la) (hSd : Commutes S ld) :
    Module.finrank K V = 12 ∧ negSpace iS = LinearMap.BilinForm.orthogonal (polarBilin Q)
      (negSpace ic ⊔ ((posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id))) := by
  obtain ⟨cm₁, N₁, C₁⟩ := adj_data hodd hdim hc ha hca
  obtain ⟨cm₂, N₂, C₂⟩ := adj_data hodd hdim hc hd hcd
  have pda := (lemma_6_10 hodd hc ha cm₁ N₁ C₁).1
  have pdd := (lemma_6_10 hodd hc hd cm₂ N₂ C₂).1
  have hle := negSpace_le_orthogonal_chain hodd hdim hc ha hd hS hca hcd hSc hSa hSd
  have hU := finrank_chain_space hodd hc pda pdd horth
  have hperp := LinearMap.BilinForm.finrank_orthogonal hQ (negSpace ic ⊔
    ((posSpace ic ⊓ negSpace ia) ⊔ (posSpace ic ⊓ negSpace id)))
  have h4 := finrank_negSpace hodd hS
  have hmono := Submodule.finrank_mono hle
  rw [h4, hperp, hU] at hmono
  have hn : Module.finrank K V = 12 := by omega
  refine ⟨hn, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  rw [h4, hperp, hU, hn]

omit [Finite K] [FiniteDimensional K V] in
theorem involution_eq_of_negSpace_eq (h2 : (2 : K) ≠ 0) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i i' : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h' : IsFundamental Q L' i')
    (e : negSpace i = negSpace i') : i = i' := by
  obtain ⟨F, rfl, rfl⟩ := h
  obtain ⟨F', rfl, rfl⟩ := h'
  rw [negSpace_La_neg_one h2, negSpace_La_neg_one h2] at e
  exact (Frame.La_neg_one_eq_of_span_eq e.symm).symm

theorem chain_twins (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) (hdim' : Module.finrank K V ≤ 12)
    {c la ld S S' : Subgroup (V ≃ₗ[K] V)} {ic ia id iS iS' : V ≃ₗ[K] V}
    (hc : IsFundamental Q c ic) (ha : IsFundamental Q la ia) (hd : IsFundamental Q ld id)
    (hS : IsFundamental Q S iS) (hS' : IsFundamental Q S' iS')
    (hca : ModelAdj (scalars K V) c la) (hcd : ModelAdj (scalars K V) c ld)
    (horth : ∀ x ∈ negSpace ia, ∀ y ∈ negSpace id, polar Q x y = 0) (hne : S ≠ S')
    (hSc : Commutes S c) (hSa : Commutes S la) (hSd : Commutes S ld)
    (hSc' : Commutes S' c) (hSa' : Commutes S' la) (hSd' : Commutes S' ld) :
    ModelIndist (scalars K V) (fundSet Q) S S' := by
  obtain ⟨-, e⟩ := chain_centralizer hodd hQ hdim hdim' hc ha hd hS hca hcd horth hSc hSa hSd
  obtain ⟨-, e'⟩ := chain_centralizer hodd hQ hdim hdim' hc ha hd hS' hca hcd horth hSc' hSa' hSd'
  have hi := involution_eq_of_negSpace_eq (IsFundamental.two_ne_zero_of_odd hodd) hS hS'
    (e.trans e'.symm)
  exact indist_of_eq hodd hdim hS hS' hne hi.symm

theorem orth_d4_centralizer (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) (hdim' : Module.finrank K V ≤ 12) :
    ∀ c ∈ fundSet Q, ∀ l₁ ∈ fundSet Q, ∀ l₂ ∈ fundSet Q, ∀ l₃ ∈ fundSet Q,
      ModelAdj (scalars K V) c l₁ → ModelAdj (scalars K V) c l₂ → ModelAdj (scalars K V) c l₃ →
      l₁ ≠ l₂ → l₁ ≠ l₃ → l₂ ≠ l₃ → Commutes l₁ l₂ → Commutes l₁ l₃ → Commutes l₂ l₃ →
      ∀ S ∈ fundSet Q, ∀ S' ∈ fundSet Q, S ≠ S' →
        Commutes S c → Commutes S l₁ → Commutes S l₂ → Commutes S l₃ →
        Commutes S' c → Commutes S' l₁ → Commutes S' l₂ → Commutes S' l₃ →
        ModelIndist (scalars K V) (fundSet Q) S S' := by
  rintro c ⟨ic, hc⟩ l₁ ⟨i₁, h₁⟩ l₂ ⟨i₂, h₂⟩ l₃ ⟨i₃, h₃⟩ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23 S ⟨iS, hS⟩
    S' ⟨iS', hS'⟩ hne hSc hS1 hS2 hS3 hS'c hS'1 hS'2 hS'3
  rcases star_orth_pair hodd h₁ h₂ h₃ n12 n13 n23 k12 k13 with horth | horth
  · exact chain_twins hodd hQ hdim hdim' hc h₁ h₂ hS hS' a₁ a₂ horth hne hSc hS1 hS2 hS'c hS'1 hS'2
  · exact chain_twins hodd hQ hdim hdim' hc h₁ h₃ hS hS' a₁ a₃ horth hne hSc hS1 hS3 hS'c hS'1 hS'3

theorem orth_d4_centralizer_empty (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) (hdim' : Module.finrank K V ≤ 11) :
    ∀ c ∈ fundSet Q, ∀ l₁ ∈ fundSet Q, ∀ l₂ ∈ fundSet Q, ∀ l₃ ∈ fundSet Q,
      ModelAdj (scalars K V) c l₁ → ModelAdj (scalars K V) c l₂ → ModelAdj (scalars K V) c l₃ →
      l₁ ≠ l₂ → l₁ ≠ l₃ → l₂ ≠ l₃ → Commutes l₁ l₂ → Commutes l₁ l₃ → Commutes l₂ l₃ →
      ∀ S ∈ fundSet Q, ¬ (Commutes S c ∧ Commutes S l₁ ∧ Commutes S l₂ ∧ Commutes S l₃) := by
  rintro c ⟨ic, hc⟩ l₁ ⟨i₁, h₁⟩ l₂ ⟨i₂, h₂⟩ l₃ ⟨i₃, h₃⟩ a₁ a₂ a₃ n12 n13 n23 k12 k13 k23 S ⟨iS, hS⟩
    ⟨hSc, hS1, hS2, hS3⟩
  rcases star_orth_pair hodd h₁ h₂ h₃ n12 n13 n23 k12 k13 with horth | horth
  · have := (chain_centralizer hodd hQ hdim (by omega) hc h₁ h₂ hS a₁ a₂ horth hSc hS1 hS2).1
    omega
  · have := (chain_centralizer hodd hQ hdim (by omega) hc h₁ h₃ hS a₁ a₃ horth hSc hS1 hS3).1
    omega

end Geometry

end CFSG.ClassicalInvolution.RouteD.Gaps
