module

public import Mathlib.RepresentationTheory.Basic

public section

namespace CFSG.CGT.PushingUpLit.SolKNA

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def restrictRep (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) : Representation (ZMod 2) G W where
  toFun g := (ρ g).restrict (fun w hw => hW g w hw)
  map_one' := by ext w; simp
  map_mul' g h := by ext w; simp

@[simp] theorem restrictRep_apply (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) (g : G) (w : W) :
    ((restrictRep ρ W hW g w : W) : V) = ρ g w := rfl

theorem fpf_restrict (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) {g : G} (hfpf : ∀ v, ρ g v = v → v = 0) :
    ∀ w : W, restrictRep ρ W hW g w = w → w = 0 := by
  intro w hw
  have h1 : ρ g (w : V) = (w : V) := congrArg Subtype.val hw
  exact Subtype.ext (hfpf _ h1)

omit [Module (ZMod 2) V] in
theorem add_self_eq_zero_of_zmod_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] (y : M) :
    y + y = 0 := by
  rw [← two_smul (ZMod 2) y, show (2 : ZMod 2) = 0 from rfl, zero_smul]

theorem fpf_quotient (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) {g : G} (hg5 : g ^ 5 = 1) (hfpf : ∀ v, ρ g v = v → v = 0) :
    ∀ v : V ⧸ W, ρ.quotient W (fun h w hw => hW h w hw) g v = v → v = 0 := by
  intro v hv
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective W v
  have hσ : ∀ y : V, ρ.quotient W (fun h w hw => hW h w hw) g (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (ρ g y) := fun y => by simp
  have h5 : ρ g (ρ g (ρ g (ρ g (ρ g x)))) = x := by
    have : (ρ (g ^ 5)) x = x := by rw [hg5, map_one]; rfl
    simpa [map_pow, pow_succ, Module.End.mul_apply] using this
  set u : V := x + ρ g x + ρ g (ρ g x) + ρ g (ρ g (ρ g x)) + ρ g (ρ g (ρ g (ρ g x))) with hu
  have hfix : ρ g u = u := by
    simp only [hu, map_add, h5]
    abel
  have hu0 : u = 0 := hfpf u hfix
  have m1 : (Submodule.Quotient.mk (ρ g x) : V ⧸ W) = Submodule.Quotient.mk x := by
    rw [← hσ]; exact hv
  have m2 : (Submodule.Quotient.mk (ρ g (ρ g x)) : V ⧸ W) = Submodule.Quotient.mk x := by
    rw [← hσ, m1]; exact hv
  have m3 : (Submodule.Quotient.mk (ρ g (ρ g (ρ g x))) : V ⧸ W) = Submodule.Quotient.mk x := by
    rw [← hσ, m2]; exact hv
  have m4 : (Submodule.Quotient.mk (ρ g (ρ g (ρ g (ρ g x)))) : V ⧸ W) =
      Submodule.Quotient.mk x := by
    rw [← hσ, m3]; exact hv
  have hmk : (Submodule.Quotient.mk u : V ⧸ W) = Submodule.Quotient.mk x := by
    simp only [hu, Submodule.Quotient.mk_add, m1, m2, m3, m4]
    have hd := add_self_eq_zero_of_zmod_two (Submodule.Quotient.mk x : V ⧸ W)
    calc _ = ((Submodule.Quotient.mk x : V ⧸ W) + Submodule.Quotient.mk x) +
          ((Submodule.Quotient.mk x : V ⧸ W) + Submodule.Quotient.mk x) +
            Submodule.Quotient.mk x := by abel
      _ = _ := by rw [hd]; simp
  rw [← hmk, hu0]
  rfl

theorem exists_maximal_invariant [Finite V] [Nontrivial V] (ρ : Representation (ZMod 2) G V) :
    ∃ W : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ W, ρ g w ∈ W) ∧ W ≠ ⊤ ∧
      ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ U, ρ g w ∈ U) → W ≤ U → U = W ∨ U = ⊤ := by
  classical
  have hfin : Finite (Submodule (ZMod 2) V) :=
    Finite.of_injective (fun W : Submodule (ZMod 2) V => (W : Set V)) SetLike.coe_injective
  let S : Set (Submodule (ZMod 2) V) := {W | (∀ g, ∀ w ∈ W, ρ g w ∈ W) ∧ W ≠ ⊤}
  have hne : S.Nonempty := ⟨⊥, fun g w hw => by
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero], bot_ne_top⟩
  obtain ⟨W, hWS, hmax⟩ := Set.Finite.exists_maximalFor id S (Set.toFinite S) hne
  refine ⟨W, hWS.1, hWS.2, fun U hU hWU => ?_⟩
  by_cases hUtop : U = ⊤
  · exact Or.inr hUtop
  · exact Or.inl (le_antisymm (hmax ⟨hU, hUtop⟩ hWU) hWU)

theorem quotient_irreducible (ρ : Representation (ZMod 2) G V) (W : Submodule (ZMod 2) V)
    (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W)
    (hmax : ∀ U : Submodule (ZMod 2) V, (∀ g, ∀ w ∈ U, ρ g w ∈ U) → W ≤ U → U = W ∨ U = ⊤)
    (U' : Submodule (ZMod 2) (V ⧸ W))
    (hU' : ∀ g, ∀ w ∈ U', ρ.quotient W (fun h w hw => hW h w hw) g w ∈ U') :
    U' = ⊥ ∨ U' = ⊤ := by
  have hU'm : U' = (U'.comap W.mkQ).map W.mkQ :=
    (Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective W) U').symm
  have hUinv : ∀ g, ∀ w ∈ U'.comap W.mkQ, ρ g w ∈ U'.comap W.mkQ := by
    intro g w hw
    have h1 : W.mkQ w ∈ U' := hw
    have h2 := hU' g _ h1
    have : ρ.quotient W (fun h w hw => hW h w hw) g (W.mkQ w) = W.mkQ (ρ g w) := by simp
    rw [this] at h2
    exact h2
  have hWU : W ≤ U'.comap W.mkQ := fun w hw => by
    show W.mkQ w ∈ U'
    have h0 : W.mkQ w = 0 := (Submodule.Quotient.mk_eq_zero W).mpr hw
    rw [h0]
    exact U'.zero_mem
  rcases hmax _ hUinv hWU with h | h
  · left
    rw [hU'm, h]
    refine eq_bot_iff.mpr fun x hx => ?_
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    rw [Submodule.mem_bot]
    exact (Submodule.Quotient.mk_eq_zero W).mpr hw
  · right
    rw [hU'm, h, Submodule.map_top, Submodule.range_mkQ]

end CFSG.CGT.PushingUpLit.SolKNA
