module

public import CFSG.ClassicalInvolution.SmallCases.DSplitEdge
public import CFSG.ClassicalInvolution.SmallCases.DSplitDefs

public section

namespace CFSG.ClassicalInvolution.Disconnected

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.RouteD
open scoped commutatorElement

@[expose] def tqAdj1 (p f : ℕ) [Fact p.Prime] : Balance.Theorem5.MemberAdj :=
  fun {H} _ M N => ∃ a : H, IsClassicalMember p f M a ∧ ActsTrivOnQuot N a

@[expose] def tqAdjSymm (p f : ℕ) [Fact p.Prime] : Balance.Theorem5.MemberAdj :=
  fun {_} _ M N => tqAdj1 p f M N ∨ tqAdj1 p f N M

section Chain

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem tqChain_of_dConnected (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {K : Subgroup G} {z : G}
    (hz : IsClassicalMember p f K z) (hD : DConnected (CoreAssembly.conjClass K)) :
    ∀ L ∈ CoreAssembly.conjClass K, ∀ L' ∈ CoreAssembly.conjClass K,
      Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ tqAdjSymm p f M N) L L' := by
  intro L hL L' hL'
  have hcl : ∀ M ∈ CoreAssembly.conjClass K, ∃ w, IsClassicalMember p f M w :=
    (inClass_conjugates hz).classical
  have key : ∀ X, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ dAdj (CoreAssembly.conjClass K) M N)
      L X →
      X ∈ CoreAssembly.conjClass K ∧ Relation.ReflTransGen
        (fun M N : Subgroup G => N ∈ CoreAssembly.conjClass K ∧ tqAdjSymm p f M N) L X := by
    intro X hX
    induction hX with
    | refl => exact ⟨hL, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ih.2.tail ⟨hbc.1, ?_⟩⟩
      rcases hbc.2 with h | h
      · exact Or.inl (tq_of_mem_omegaNbr hp2 hq hcl ih.1 h)
      · exact Or.inr (tq_of_mem_omegaNbr hp2 hq hcl hbc.1 h)
  exact (key L' (hD L hL L' hL')).2

end Chain

section Final

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem centralizes_of_actsTrivOnQuot_of_isQuasisimple {N : Subgroup G}
    (hN : CFSG.Open.IsQuasisimple N) {a : G} (ha : ActsTrivOnQuot N a) :
    ∀ x ∈ N, a * x = x * a := by
  have hperf : Group.IsPerfect ↥N := ⟨hN.1⟩
  set α : MulAut ↥N := N.normalizerMonoidHom ⟨a, ha.1⟩ with hα
  have hαapp : ∀ y : ↥N, ((α y : ↥N) : G) = a * (y : G) * a⁻¹ := fun y => by
    rw [hα]
    simp
  have hcent : ∀ y : ↥N, α y * y⁻¹ ∈ Subgroup.center ↥N := by
    intro y
    obtain ⟨c, hc, hcy⟩ := ha.2 y y.2
    have hcZ := Balance.oddCore_le_center_of_isQuasisimple hN hc
    have hcy' : (c : G) = ⁅a, (y : G)⁆ := hcy
    have : c = α y * y⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, hαapp, hcy', commutatorElement_def]
      simp
    rw [← this]
    exact hcZ
  let ψ : ↥N →* ↥(Subgroup.center ↥N) :=
    { toFun := fun y => ⟨α y * y⁻¹, hcent y⟩
      map_one' := by simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have h1 := Subgroup.mem_center_iff.mp (hcent y) (α x)
        have h3 := Subgroup.mem_center_iff.mp (hcent y) (α x * x⁻¹)
        have h2 : α (x * y) * (x * y)⁻¹ = (α x * x⁻¹) * (α y * y⁻¹) := by
          calc α (x * y) * (x * y)⁻¹ = α x * (α y * y⁻¹) * x⁻¹ := by
                rw [map_mul, mul_inv_rev]; group
            _ = (α y * y⁻¹) * α x * x⁻¹ := by rw [h1]
            _ = (α y * y⁻¹) * (α x * x⁻¹) := by group
            _ = _ := h3.symm
        exact h2 }
  have hker : ⁅(⊤ : Subgroup ↥N), ⊤⁆ ≤ ψ.ker := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr
      (Subtype.ext (Subgroup.mem_center_iff.mp (ψ y).2 (ψ x).1))
  have hker' : commutator ↥N ≤ ψ.ker := hker
  rw [hperf.commutator_eq_top] at hker'
  intro x hx
  have h1 : ψ ⟨x, hx⟩ = 1 := MonoidHom.mem_ker.mp (hker' (Subgroup.mem_top _))
  have h2 : α ⟨x, hx⟩ * ⟨x, hx⟩⁻¹ = 1 := congrArg Subtype.val h1
  have h3 : α ⟨x, hx⟩ = ⟨x, hx⟩ := mul_inv_eq_one.mp h2
  have h4 := congrArg Subtype.val h3
  rw [hαapp] at h4
  calc a * x = (a * x * a⁻¹) * a := by group
    _ = x * a := by rw [h4]

theorem commutes_or_eq_of_tq [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J)
    (hP1 : ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z})
    {M N : Subgroup G} (hM : M ∈ Ω) (hN : N ∈ Ω) {a : G} (ha : IsClassicalMember p f M a)
    (hNa : ActsTrivOnQuot N a) : Commutes M N ∨ N = M := by
  have hcN := centralizes_of_actsTrivOnQuot_of_isQuasisimple (hqs N hN) hNa
  have hMx : M ∈ centralizingMembers Ω {a} := ⟨hM, le_centralizer_of_isClassicalMember ha⟩
  have hNx : N ∈ centralizingMembers Ω {a} := ⟨hN, fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcN x hx).symm⟩
  have hP1x := hP1 M hM a ha
  have hxc : ¬ ({a} : Set G) ⊆ Subgroup.center G :=
    CoreAssembly.singleton_not_subset_center hnab ha.ne_one
  obtain ⟨D⟩ : Nonempty (LieSystemData p f (locQuot Ω a) (locFamily Ω a)) := hIH {a} hxc
  obtain ⟨i, ht, hr, hi⟩ := Gaps.locImg_eq_range_of_involution (Gaps.fundNoncentral p) D hMx ha
  have hNmem : locImg Ω a N ∈ locFamily Ω a := mem_locFamily_iff.mpr ⟨N, hNx, rfl⟩
  obtain ⟨j, R, hR, hRN⟩ := D.fundamental _ hNmem
  by_cases hij : j = i
  · subst hij
    right
    have hR1 := Gaps.eq_top_of_psl_two (p := p) (e := D.exp j) ht hr hR
    refine locImg_injOn hΩ hP1x hNx hMx ?_
    rw [hRN, hR1, hi, ← MonoidHom.range_eq_map]
  · left
    refine commutes_of_commutes_locImg hΩ hP1x hMx hNx ?_
    intro u hu v hv
    rw [hi] at hu
    rw [hRN] at hv
    obtain ⟨r, -, rfl⟩ := hv
    exact Gaps.commutes_range D (Ne.symm hij) u hu _ ⟨r, rfl⟩

theorem omegaConnected_of_tqChain [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x)
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) (hIH : LocalLieSystems p f Ω)
    (hqs : ∀ J ∈ Ω, CFSG.Open.IsQuasisimple J)
    (hP1 : ∀ L ∈ Ω, ∀ z : G, IsClassicalMember p f L z → LocalOddCentral Ω {z})
    (hchain : ∀ L ∈ Ω, ∀ L' ∈ Ω, Relation.ReflTransGen
      (fun M N : Subgroup G => N ∈ Ω ∧ tqAdjSymm p f M N) L L') : OmegaConnected Ω := by
  intro L hL L' hL'
  have key : ∀ X, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ tqAdjSymm p f M N) L X →
      X ∈ Ω ∧ Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N) L X := by
    intro X hX
    induction hX with
    | refl => exact ⟨hL, Relation.ReflTransGen.refl⟩
    | @tail b c _ hbc ih =>
      refine ⟨hbc.1, ?_⟩
      rcases hbc.2 with ⟨a, ha, hNa⟩ | ⟨a, ha, hNa⟩
      · rcases commutes_or_eq_of_tq hnab hΩ hIH hqs hP1 ih.1 hbc.1 ha hNa with h | h
        · exact ih.2.tail ⟨hbc.1, h⟩
        · rw [h]
          exact ih.2
      · rcases commutes_or_eq_of_tq hnab hΩ hIH hqs hP1 hbc.1 ih.1 ha hNa with h | h
        · exact ih.2.tail ⟨hbc.1, fun x hx y hy => (h y hy x hx).symm⟩
        · rw [← h]
          exact ih.2
  exact (key L' (hchain L hL L' hL')).2

omit [Finite G] in
theorem routeD_deltaConnected_of_omegaConnected {Ω : Set (Subgroup G)} (hne : Ω.Nonempty)
    (h : OmegaConnected Ω) : RouteD.DeltaConnected Ω := by
  classical
  have : Nonempty Ω := hne.to_subtype
  refine ⟨fun u v => ?_⟩
  have key : ∀ X, Relation.ReflTransGen (fun M N : Subgroup G => N ∈ Ω ∧ Commutes M N)
      (u : Subgroup G) X → ∃ hX : X ∈ Ω, (Models.commGraph Ω).Reachable u ⟨X, hX⟩ := by
    intro X hX
    induction hX with
    | refl => exact ⟨u.2, SimpleGraph.Reachable.refl _⟩
    | @tail b c _ hbc ih =>
      obtain ⟨hb, hreach⟩ := ih
      refine ⟨hbc.1, ?_⟩
      by_cases hbc' : b = c
      · subst hbc'
        exact hreach
      · refine hreach.trans (SimpleGraph.Adj.reachable ?_)
        rw [Models.commGraph_adj]
        exact ⟨fun e => hbc' (congrArg Subtype.val e), hbc.2⟩
  exact (key v (h u u.2 v v.2)).2

end Final

end CFSG.ClassicalInvolution.Disconnected
