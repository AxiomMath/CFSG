module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerConj
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderThree

public section

universe v

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.B6
open scoped commutatorElement

variable {k : Type*} [Field k] {V : Type v} [AddCommGroup V] [Module k V]

section Notation

variable (N A : Subgroup (V ≃ₗ[k] V)) {ι : Type*} (g : ι → V ≃ₗ[k] V)

@[expose] def natL (i : ι) : Subgroup (V ≃ₗ[k] V) := conjR (g i) ⁅N, A⁆

@[expose] def natA (i : ι) : Subgroup (V ≃ₗ[k] V) := conjR (g i) A

@[expose] def natS (i : ι) : Subgroup (V ≃ₗ[k] V) := natL N A g i ⊔ natA A g i

@[expose] def natI (i : ι) : Submodule k V := commGL (natL N A g i) ⊤

@[expose] def natD : Subgroup (V ≃ₗ[k] V) := ⨆ i, natL N A g i

@[expose] def natW : Submodule k V := commGL (natD N A g) ⊤

end Notation

@[expose] def natB (G N A : Subgroup (V ≃ₗ[k] V)) : Subgroup (V ≃ₗ[k] V) :=
  ⨆ x ∈ G, conjR x (⁅N, A⁆ ⊔ A)

structure ConjFamily (G N A : Subgroup (V ≃ₗ[k] V)) {ι : Type*} (g : ι → V ≃ₗ[k] V) : Prop where
  mem : ∀ i, g i ∈ G
  inj : Function.Injective (natL N A g)
  all : ∀ x ∈ G, ∃ i, conjR x ⁅N, A⁆ = natL N A g i

theorem exists_conj_family [Finite (V ≃ₗ[k] V)] (G L : Subgroup (V ≃ₗ[k] V)) :
    ∃ (ι : Type v) (_ : Fintype ι) (g : ι → V ≃ₗ[k] V), (∀ i, g i ∈ G) ∧
      Function.Injective (fun i => conjR (g i) L) ∧
      ∀ x ∈ G, ∃ i, conjR x L = conjR (g i) L := by
  classical
  let f : ↥G → Subgroup (V ≃ₗ[k] V) := fun x => conjR (x : V ≃ₗ[k] V) L
  have hfin : Finite ↥(Set.range f) := (Set.finite_range f).to_subtype
  let _ : Fintype ↥(Set.range f) := Fintype.ofFinite _
  choose rep hrep using fun i : ↥(Set.range f) => (i.2 : ∃ y, f y = i.1)
  refine ⟨↥(Set.range f), inferInstance, fun i => (rep i : V ≃ₗ[k] V), ?_, ?_, ?_⟩
  · intro i
    exact (rep i).2
  · intro i j hij
    apply Subtype.ext
    have h3 : f (rep i) = f (rep j) := hij
    rw [← hrep i, ← hrep j]
    exact h3
  · intro x hx
    refine ⟨⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩, ?_⟩
    have h1 : f (rep ⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩) = f ⟨x, hx⟩ := hrep ⟨f ⟨x, hx⟩, ⟨x, hx⟩, rfl⟩
    exact h1.symm

theorem exists_conjFamily [Finite (V ≃ₗ[k] V)] (G N A : Subgroup (V ≃ₗ[k] V)) :
    ∃ (ι : Type v) (_ : Fintype ι) (g : ι → V ≃ₗ[k] V), ConjFamily G N A g := by
  obtain ⟨ι, hfin, g, hg, hinj, hall⟩ := exists_conj_family G ⁅N, A⁆
  exact ⟨ι, hfin, g, hg, hinj, hall⟩

structure FamData (N : Subgroup (V ≃ₗ[k] V)) {ι : Type*} (L : ι → Subgroup (V ≃ₗ[k] V)) : Prop where
  N_comm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x
  L_le : ∀ i, L i ≤ N
  L_comm : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ y ∈ L j, x * y = y * x
  L_indep : iSupIndep L
  I_indep : iSupIndep fun i => commGL (L i) ⊤
  W_eq : commGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) ⊤ = ⨆ i, commGL (L i) ⊤
  compl : IsCompl (commGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) ⊤)
    (fixGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)))
  L_fix_I : ∀ i j, i ≠ j → ∀ x ∈ L i, ∀ v ∈ commGL (L j) ⊤, x v = v
  L_fix_C : ∀ i, ∀ x ∈ L i, ∀ v ∈ fixGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)), x v = v
  faithful : ∀ d ∈ (⨆ i, L i : Subgroup (V ≃ₗ[k] V)),
    (∀ w ∈ commGL (⨆ i, L i : Subgroup (V ≃ₗ[k] V)) ⊤, d w = w) → d = 1
  D_exp : ∀ d ∈ (⨆ i, L i : Subgroup (V ≃ₗ[k] V)), d ^ 3 = 1

namespace OddAbelianSetting

variable {G N A : Subgroup (V ≃ₗ[k] V)} {ι : Type*} {g : ι → V ≃ₗ[k] V}

theorem planeData_family [CharP k 2] [Finite V] (h : OddAbelianSetting G N A)
    (F : ConjFamily G N A g) (i : ι) :
    PlaneData G N (natA A g i) (natL N A g i) (natI N A g i) :=
  h.planeData_conj (G.inv_mem (F.mem i))

theorem famData [CharP k 2] [Finite V] [Fintype ι] (h : OddAbelianSetting G N A)
    (F : ConjFamily G N A g) : FamData N (natL N A g) := by
  classical
  have : Module.Finite k V := Module.Finite.of_finite
  have pd := h.planeData_family F
  obtain ⟨I0, hI0⟩ := h.planeData (L := ⁅N, A⁆) rfl
  have hk : Nat.card k = 2 := hI0.card_k
  have hcomm : ∀ x ∈ N, ∀ y ∈ N, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.N_abelian ⟨x, hx⟩ ⟨y, hy⟩)
  have hLN : ∀ i, natL N A g i ≤ N := fun i => (pd i).L_le
  have hexp' : ∀ d ∈ (⨆ i, natL N A g i : Subgroup (V ≃ₗ[k] V)), d ∈ N ∧ d ^ 3 = 1 := by
    intro d hd
    refine Subgroup.iSup_induction (natL N A g) hd (C := fun d => d ∈ N ∧ d ^ 3 = 1) ?_ ?_ ?_
    · intro i x hx
      refine ⟨hLN i hx, ?_⟩
      have h3 : Nat.card (natL N A g i) = 3 := (pd i).card_L
      have := pow_card_eq_one' (G := ↥(natL N A g i)) (x := ⟨x, hx⟩)
      rw [h3] at this
      exact congrArg Subtype.val this
    · exact ⟨N.one_mem, one_pow 3⟩
    · rintro x y ⟨hxN, hx3⟩ ⟨hyN, hy3⟩
      refine ⟨N.mul_mem hxN hyN, ?_⟩
      rw [(show Commute x y from hcomm x hxN y hyN).mul_pow, hx3, hy3, one_mul]
  have hexp : ∀ d ∈ (⨆ i, natL N A g i : Subgroup (V ≃ₗ[k] V)), d ^ 3 = 1 := fun d hd =>
    (hexp' d hd).2
  have hD : IsPGroup 3 (⨆ i, natL N A g i : Subgroup (V ≃ₗ[k] V)) := fun d =>
    ⟨1, Subtype.ext (by simpa using hexp d d.2)⟩
  have hcyc : ∀ i, IsCyclic (natL N A g i) := fun i => by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact isCyclic_of_prime_card (pd i).card_L
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    binary_three_group_rank_two_generators_disjoint_natural_planes hk (natL N A g) F.inj hcyc
      (fun i => (pd i).card_L) hD (fun i => (pd i).finrank_I)
  exact
    { N_comm := hcomm
      L_le := hLN
      L_comm := c1
      L_indep := c2
      I_indep := c3
      W_eq := c4
      compl := c5
      L_fix_I := c7
      L_fix_C := c8
      faithful := c9
      D_exp := hexp }

end OddAbelianSetting

end CFSG.QuasithinUnique.Setup.Layer
