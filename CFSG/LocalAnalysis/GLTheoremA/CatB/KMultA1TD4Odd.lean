module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.GroupTheory.IsSubnormal
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1TD4Odd

@[expose] def SubnQuot (G T : Type*) [Group G] [Group T] : Prop :=
  ∃ J : Subgroup G, J.IsSubnormal ∧ ∃ φ : ↥J →* T, Function.Surjective φ

variable {G L T : Type*} [Group G] [Group L] [Group T]

theorem SubnQuot.comap (ψ : L →* G) (hψ : Function.Surjective ψ) (h : SubnQuot G T) :
    SubnQuot L T := by
  obtain ⟨J, hJ, φ, hφ⟩ := h
  exact ⟨J.comap ψ, hJ.comap ψ, φ.comp (ψ.subgroupComap J),
    hφ.comp (ψ.subgroupComap_surjective_of_surjective J hψ)⟩

theorem SubnQuot.of_mulEquiv (e : G ≃* L) (h : SubnQuot G T) : SubnQuot L T :=
  h.comap e.symm.toMonoidHom e.symm.surjective

theorem not_subnQuot_of_isSolvable [Group.IsSolvable G] (hT : ¬ Group.IsSolvable T) :
    ¬ SubnQuot G T := by
  rintro ⟨J, -, φ, hφ⟩
  exact hT (Group.isSolvable_of_surjective hφ)

theorem map_eq_bot_of_isSolvable {J : Type*} [Group J] [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T)
    (φ : J →* T) (hφ : Function.Surjective φ) (M : Subgroup J) [M.Normal] [Group.IsSolvable M] :
    M.map φ = ⊥ := by
  rcases (Subgroup.Normal.map (inferInstance : M.Normal) φ hφ).eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    refine hT (Group.isSolvable_of_surjective (f := φ.comp M.subtype) fun t => ?_)
    have ht : t ∈ M.map φ := h ▸ Subgroup.mem_top t
    obtain ⟨m, hm, rfl⟩ := ht
    exact ⟨⟨m, hm⟩, rfl⟩

theorem SubnQuot.quotient [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T) (N : Subgroup G) [N.Normal]
    [Group.IsSolvable N] (h : SubnQuot G T) : SubnQuot (G ⧸ N) T := by
  obtain ⟨J, hJ, φ, hφ⟩ := h
  set M : Subgroup ↥J := N.subgroupOf J with hM
  let ι : ↥M →* ↥N :=
    { toFun := fun x => ⟨((x : ↥J) : G), x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  haveI : Group.IsSolvable ↥M := by
    refine Group.isSolvable_of_isSolvable_injective (f := ι) ?_
    intro x y hxy
    have h := congrArg (fun z : ↥N => (z : G)) hxy
    exact Subtype.ext (Subtype.ext h)
  have hMφ : M.map φ = ⊥ := map_eq_bot_of_isSolvable hT φ hφ M
  set ψ : ↥J →* ↥(J.map (QuotientGroup.mk' N)) := (QuotientGroup.mk' N).subgroupMap J with hψ
  have hψs : Function.Surjective ψ := (QuotientGroup.mk' N).subgroupMap_surjective J
  have hker : ψ.ker ≤ φ.ker := by
    intro x hx
    have hx1 : (QuotientGroup.mk' N) (x : G) = 1 := congrArg Subtype.val hx
    have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).1 hx1
    have hxM : x ∈ M := hxN
    have : φ x ∈ M.map φ := Subgroup.mem_map_of_mem φ hxM
    rw [hMφ, Subgroup.mem_bot] at this
    exact this
  refine ⟨J.map (QuotientGroup.mk' N), hJ.map (QuotientGroup.mk'_surjective N),
    (QuotientGroup.lift ψ.ker φ hker).comp
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.toMonoidHom, ?_⟩
  intro t
  obtain ⟨j, rfl⟩ := hφ t
  refine ⟨ψ j, ?_⟩
  have h1 : (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm (ψ j) =
      (QuotientGroup.mk j : ↥J ⧸ ψ.ker) := by
    rw [MulEquiv.symm_apply_eq]
    rfl
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply, h1]
  rfl

theorem SubnQuot.normal [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T) (N : Subgroup G) [N.Normal]
    [Group.IsSolvable (G ⧸ N)] (h : SubnQuot G T) : SubnQuot ↥N T := by
  obtain ⟨J, hJ, φ, hφ⟩ := h
  set M : Subgroup ↥J := N.subgroupOf J with hM
  rcases (Subgroup.Normal.map (inferInstance : M.Normal) φ hφ).eq_bot_or_eq_top with hb | ht
  · exfalso
    set χ : ↥J →* G ⧸ N := (QuotientGroup.mk' N).comp J.subtype with hχ
    have hχker : χ.ker ≤ φ.ker := by
      intro x hx
      have hxN : (x : G) ∈ N := (QuotientGroup.eq_one_iff _).1 hx
      have hxM : x ∈ M := hxN
      have : φ x ∈ M.map φ := Subgroup.mem_map_of_mem φ hxM
      rw [hb, Subgroup.mem_bot] at this
      exact this
    haveI : Group.IsSolvable (↥J ⧸ χ.ker) :=
      Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective χ)
    refine hT (Group.isSolvable_of_surjective (f := QuotientGroup.lift χ.ker φ hχker) ?_)
    intro t
    obtain ⟨j, rfl⟩ := hφ t
    exact ⟨QuotientGroup.mk j, rfl⟩
  · let ι : ↥(J.subgroupOf N) →* ↥J :=
      { toFun := fun x => ⟨((x : ↥N) : G), x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    refine ⟨J.subgroupOf N, hJ.subgroupOf, φ.comp ι, ?_⟩
    intro t
    have htM : t ∈ M.map φ := ht ▸ Subgroup.mem_top t
    obtain ⟨m, hm, rfl⟩ := htM
    exact ⟨⟨⟨(m : G), hm⟩, m.2⟩, rfl⟩

theorem SubnQuot.card_eq_of_isSimpleGroup [IsSimpleGroup G] [Nontrivial T] (h : SubnQuot G T) :
    Nat.card T = Nat.card G := by
  obtain ⟨J, hJ, φ, hφ⟩ := h
  rcases hJ.eq_bot_or_top_of_isSimpleGroup inferInstance with rfl | rfl
  · exfalso
    obtain ⟨a, b, hab⟩ := exists_pair_ne T
    obtain ⟨x, rfl⟩ := hφ a
    obtain ⟨y, rfl⟩ := hφ b
    have hx : x = 1 := Subtype.ext ((Subgroup.mem_bot).1 x.2)
    have hy : y = 1 := Subtype.ext ((Subgroup.mem_bot).1 y.2)
    exact hab (by rw [hx, hy])
  · haveI : IsSimpleGroup ↥(⊤ : Subgroup G) := (Subgroup.topEquiv (G := G)).isSimpleGroup
    have hinj : Function.Injective φ := by
      rcases (inferInstance : φ.ker.Normal).eq_bot_or_eq_top with hk | hk
      · exact (MonoidHom.ker_eq_bot_iff φ).1 hk
      · exfalso
        obtain ⟨a, b, hab⟩ := exists_pair_ne T
        obtain ⟨x, rfl⟩ := hφ a
        obtain ⟨y, rfl⟩ := hφ b
        have hx : φ x = 1 := (MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top x)
        have hy : φ y = 1 := (MonoidHom.mem_ker).1 (hk ▸ Subgroup.mem_top y)
        exact hab (by rw [hx, hy])
    rw [← Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hφ⟩)]
    exact Nat.card_congr (Subgroup.topEquiv (G := G)).toEquiv

theorem SubnQuot.card_eq_centerQuot [IsSimpleGroup T] (hT : ¬ Group.IsSolvable T)
    [IsSimpleGroup (G ⧸ Subgroup.center G)] (h : SubnQuot G T) :
    Nat.card T = Nat.card (G ⧸ Subgroup.center G) := by
  haveI : Group.IsSolvable ↥(Subgroup.center G) := Group.isSolvable_of_comm fun a b =>
    Subtype.ext ((Subgroup.mem_center_iff.1 b.2) a)
  haveI : Nontrivial T := IsSimpleGroup.toNontrivial
  exact (h.quotient hT (Subgroup.center G)).card_eq_of_isSimpleGroup

theorem isSolvable_quot_commutator : Group.IsSolvable (G ⧸ commutator G) :=
  Group.isSolvable_of_comm fun a b => by
    have h := mul_comm (show Abelianization G from a) (show Abelianization G from b)
    exact h

end CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1TD4Odd
