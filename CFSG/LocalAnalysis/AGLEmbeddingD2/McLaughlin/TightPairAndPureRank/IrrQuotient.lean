module

public import CFSG.Quasithin.Background.G11Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.CommutingBlocks

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Quasithin.G11 CFSG.AGLEmbeddingD2.McLaughlin

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] noncomputable def quotAct (U : Submodule (ZMod 2) V) (C' : Submodule (ZMod 2) ↥U)
    (f : V →ₗ[ZMod 2] V) (hU : ∀ x ∈ U, f x ∈ U)
    (hC : ∀ x : ↥U, x ∈ C' → (⟨f x, hU x x.2⟩ : ↥U) ∈ C') : Module.End (ZMod 2) (↥U ⧸ C') :=
  C'.mapQ C' (f.restrict hU) (fun x hx => hC x hx)

variable [Finite V]

theorem trivial_on_commSpace_of_irrSec {L K : Subgroup (GLV V)}
    (hLK : ∀ l ∈ L, ∀ k ∈ K, l * k = k * l) (hK : commutator ↥K = ⊤)
    (hperf : commSpace L (commSpace L ⊤) = commSpace L ⊤)
    (hirr : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤)) :
    ∀ k ∈ K, ∀ u ∈ commSpace L ⊤, k u = u := by
  set U : Submodule (ZMod 2) V := commSpace L ⊤ with hU
  set C : Submodule (ZMod 2) V := fixedSpace L ⊓ U with hC
  have hKL : ∀ k' ∈ K, ∀ l ∈ L, k' * l * k'⁻¹ ∈ L := fun k' hk' l hl => by
    have h := hLK l hl k' hk'
    have e : k' * l * k'⁻¹ = l := by rw [← h]; group
    rw [e]; exact hl
  have hLK' : ∀ l' ∈ L, ∀ k ∈ K, l' * k * l'⁻¹ ∈ K := fun l' hl' k hk => by
    have h := hLK l' hl' k hk
    have e : l' * k * l'⁻¹ = k := by rw [h]; group
    rw [e]; exact hk
  have hLL : ∀ l' ∈ L, ∀ l ∈ L, l' * l * l'⁻¹ ∈ L := fun l' hl' l hl =>
    L.mul_mem (L.mul_mem hl' hl) (L.inv_mem hl')
  have hUK : Invariant K U := invariant_commSpace hKL (invariant_top K)
  have hUL : Invariant L U := invariant_commSpace hLL (invariant_top L)
  have hCK : Invariant K C := (invariant_fixedSpace hKL).inf hUK
  have hCL : Invariant L C := (invariant_fixedSpace hLL).inf hUL
  let C' : Submodule (ZMod 2) ↥U := C.comap U.subtype
  have hUk : ∀ k ∈ K, ∀ x ∈ U, k x ∈ U := fun k hk x hx => hUK k hk x hx
  have hUl : ∀ l ∈ L, ∀ x ∈ U, l x ∈ U := fun l hl x hx => hUL l hl x hx
  have hCk : ∀ k (hk : k ∈ K), ∀ x : ↥U, x ∈ C' → (⟨k x, hUk k hk x x.2⟩ : ↥U) ∈ C' := by
    intro k hk x hx
    exact hCK k hk x hx
  have hCl : ∀ l (hl : l ∈ L), ∀ x : ↥U, x ∈ C' → (⟨l x, hUl l hl x x.2⟩ : ↥U) ∈ C' := by
    intro l hl x hx
    exact hCL l hl x hx
  let σ : ↥K →* Module.End (ZMod 2) (↥U ⧸ C') :=
    { toFun := fun k => quotAct U C' (k : GLV V) (hUk k k.2) (hCk k k.2)
      map_one' := by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | H x => rfl
      map_mul' := fun a b => by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | H x => rfl }
  let ρ : ↥L →* Module.End (ZMod 2) (↥U ⧸ C') :=
    { toFun := fun l => quotAct U C' (l : GLV V) (hUl l l.2) (hCl l l.2)
      map_one' := by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | H x => rfl
      map_mul' := fun a b => by
        apply LinearMap.ext
        intro q
        induction q using Submodule.Quotient.induction_on with
        | H x => rfl }
  have hcomm : ∀ (g : ↥K) (a : ↥L), σ g * ρ a = ρ a * σ g := by
    intro g a
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H x =>
      have hxa : (a : GLV V) (x : V) ∈ U := hUl a a.2 x x.2
      have hxg : (g : GLV V) (x : V) ∈ U := hUk g g.2 x x.2
      show (Submodule.Quotient.mk ⟨(g : GLV V) ((a : GLV V) x), hUk g g.2 _ hxa⟩ : ↥U ⧸ C') =
        Submodule.Quotient.mk ⟨(a : GLV V) ((g : GLV V) x), hUl a a.2 _ hxg⟩
      congr 1
      apply Subtype.ext
      have hc : (a : GLV V) ((g : GLV V) (x : V)) = (g : GLV V) ((a : GLV V) (x : V)) :=
        congrArg (fun m : GLV V => m (x : V)) (hLK a a.2 g g.2)
      exact hc.symm
  have hsimple : ∀ W' : Submodule (ZMod 2) (↥U ⧸ C'), (∀ a, ∀ w ∈ W', ρ a w ∈ W') →
      W' = ⊥ ∨ W' = ⊤ := by
    intro W' hW'
    set J : Submodule (ZMod 2) ↥U := W'.comap C'.mkQ with hJ
    set J' : Submodule (ZMod 2) V := J.map U.subtype with hJ'
    have hJinv : Invariant L J' := by
      rintro l hl _ ⟨x, hx, rfl⟩
      refine ⟨⟨l x, hUl l hl x x.2⟩, ?_, rfl⟩
      have := hW' ⟨l, hl⟩ (C'.mkQ x) hx
      exact this
    have hCJ : C ≤ J' := by
      intro c hc
      refine ⟨⟨c, hc.2⟩, ?_, rfl⟩
      show C'.mkQ ⟨c, hc.2⟩ ∈ W'
      have : C'.mkQ ⟨c, hc.2⟩ = 0 := (Submodule.Quotient.mk_eq_zero C').2 hc
      rw [this]
      exact W'.zero_mem
    have hJU : J' ≤ U := Submodule.map_subtype_le U J
    rcases hirr.2 J' hJinv hCJ hJU with h | h
    · left
      have : J = C' := by
        ext x
        constructor
        · intro hx
          have : (x : V) ∈ J' := ⟨x, hx, rfl⟩
          rw [h] at this
          exact this
        · intro hx
          have hx' : (x : V) ∈ C := hx
          have : (x : V) ∈ J' := hCJ hx'
          obtain ⟨y, hy, hyx⟩ := this
          have : y = x := Subtype.ext hyx
          rwa [this] at hy
      rw [← Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective C') W', ← hJ, this]
      simp
    · right
      have : J = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hx : (x : V) ∈ J' := by rw [h]; exact x.2
        obtain ⟨y, hy, hyx⟩ := hx
        have : y = x := Subtype.ext hyx
        rwa [this] at hy
      rw [← Submodule.map_comap_eq_of_surjective (Submodule.mkQ_surjective C') W', ← hJ, this]
      simp
  have hstepA : ∀ k ∈ K, ∀ u ∈ U, k u - u ∈ C := by
    intro k hk u hu
    have h1 := eq_one_of_perfect_of_simple ρ σ hsimple hcomm hK ⟨k, hk⟩
    have h2 := congrArg (fun f : Module.End (ZMod 2) (↥U ⧸ C') => f (Submodule.Quotient.mk ⟨u, hu⟩)) h1
    have h3 : (Submodule.Quotient.mk ⟨k u, hUk k hk u hu⟩ : ↥U ⧸ C') = Submodule.Quotient.mk ⟨u, hu⟩ :=
      h2
    have h4 := (Submodule.Quotient.eq C').1 h3
    have h5 : ((⟨k u, hUk k hk u hu⟩ : ↥U) - ⟨u, hu⟩ : ↥U) ∈ C' := h4
    exact h5
  intro k hk u hu
  rw [hU] at hu
  have hu' : u ∈ commSpace L U := by rw [hperf]; exact hu
  clear hu
  induction hu' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨l, hl, w, hw, rfl⟩ := hy
    have hkw : k w - w ∈ fixedSpace L := (hstepA k hk w hw).1
    have := hkw l hl
    have e : k (l w - w) = (l w - w) + (l (k w - w) - (k w - w)) := by
      have hc : l (k w) = k (l w) := congrArg (fun m : GLV V => m w) (hLK l hl k hk)
      simp only [map_sub, hc]
      abel
    rw [e, show l (k w - w) = k w - w from this, sub_self, add_zero]
  | zero => simp
  | add x y hx hy ihx ihy => rw [map_add, ihx, ihy]
  | smul c x hx ih => rw [map_smul, ih]

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
