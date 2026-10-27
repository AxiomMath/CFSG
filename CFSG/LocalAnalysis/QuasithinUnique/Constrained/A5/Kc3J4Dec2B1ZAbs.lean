module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J4ClassBase

public section

namespace CFSG.QuasithinUnique.A5

section ListData

variable {Y : Type*} [Group Y]

theorem commute_of_mem_closure {s : Set Y} {x : Y} (h : ∀ v ∈ s, x * v = v * x) {b : Y}
    (hb : b ∈ Subgroup.closure s) : x * b = b * x := by
  have key : Commute x b := by
    induction hb using Subgroup.closure_induction with
    | mem v hv => exact h v hv
    | one => exact Commute.one_right x
    | mul a b _ _ ha hb => exact ha.mul_right hb
    | inv a _ ha => exact ha.inv_right
  exact key

theorem closure_commutative_of_pairwise {s : Set Y} (hs : ∀ a ∈ s, ∀ b ∈ s, a * b = b * a) :
    ∀ a ∈ Subgroup.closure s, ∀ b ∈ Subgroup.closure s, a * b = b * a := by
  intro a ha b hb
  have h1 : ∀ v ∈ s, v * b = b * v := fun v hv =>
    commute_of_mem_closure (fun w hw => hs v hv w hw) hb
  exact (commute_of_mem_closure (fun v hv => (h1 v hv).symm) ha).symm

theorem normalizer_closure_of_finite [Finite Y] {s : Set Y} {y : Y}
    (h : ∀ a ∈ s, y * a * y⁻¹ ∈ Subgroup.closure s) :
    y ∈ Subgroup.normalizer (Subgroup.closure s : Set Y) := by
  set V := Subgroup.closure s with hV
  have hf : ∀ b ∈ V, y * b * y⁻¹ ∈ V := by
    intro b hb
    induction hb using Subgroup.closure_induction with
    | mem a ha => exact h a ha
    | one => simp
    | mul a b _ _ ha hb =>
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e]
      exact V.mul_mem ha hb
    | inv a _ ha =>
      have e : y * a⁻¹ * y⁻¹ = (y * a * y⁻¹)⁻¹ := by group
      rw [e]
      exact V.inv_mem ha
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨hf b, fun hb => ?_⟩
  let φ : V → V := fun a => ⟨y * a * y⁻¹, hf a a.2⟩
  have hinj : Function.Injective φ := by
    intro a a' e
    have e' : y * (a : Y) * y⁻¹ = y * (a' : Y) * y⁻¹ := congrArg Subtype.val e
    exact Subtype.ext (by simpa using e')
  obtain ⟨a, ha⟩ := Finite.injective_iff_surjective.1 hinj ⟨y * b * y⁻¹, hb⟩
  have e' : y * (a : Y) * y⁻¹ = y * b * y⁻¹ := congrArg Subtype.val ha
  have hab : (a : Y) = b := by simpa using e'
  rw [← hab]
  exact a.2

theorem classRad_of_centralizer_list [Finite Y] (vs : List Y) (y : Y) (Cl L : List Y) {m : ℕ}
    (hab : ∀ a ∈ vs, ∀ b ∈ vs, a * b = b * a)
    (hnorm : ∀ a ∈ vs, y * a * y⁻¹ ∈ Subgroup.closure {x | x ∈ vs})
    (hy5 : orderOf y = 5)
    (hcl : ∀ x : Y, (∀ v ∈ vs, x * v = v * x) → x ∈ Cl)
    (hsound : ∀ x ∈ Cl, ∀ v ∈ vs, x * v = v * x)
    (h2 : ∀ x ∈ Cl, x ^ (2 ^ m) = 1)
    (hnodup : Cl.Nodup)
    (hL : ∀ x ∈ Cl, x * y = y * x → x ∈ L)
    (hidx : 16 * L.length < Cl.length) :
    ClassRad (Subgroup.closure {x | x ∈ vs}) := by
  classical
  set V := Subgroup.closure {x | x ∈ vs} with hV
  set C := Subgroup.centralizer (V : Set Y) with hC
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a :=
    closure_commutative_of_pairwise (s := {x | x ∈ vs}) hab
  have hy : y ∈ Subgroup.normalizer (V : Set Y) := normalizer_closure_of_finite hnorm
  have hmemC : ∀ x, x ∈ C ↔ ∀ v ∈ vs, x * v = v * x := by
    intro x
    constructor
    · intro hx v hv
      exact (Subgroup.mem_centralizer_iff.1 hx v (Subgroup.subset_closure hv)).symm
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (commute_of_mem_closure (s := {x | x ∈ vs}) hx hg).symm
  have hU : IsPGroup 2 C := by
    intro g
    refine ⟨m, ?_⟩
    have hx : (g : Y) ^ (2 ^ m) = 1 := h2 g (hcl g ((hmemC g).1 g.2))
    exact Subtype.ext (by simpa using hx)
  have hCcard : Nat.card C = Cl.length := by
    have e1 : Nat.card C = Nat.card {x // x ∈ Cl} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x =>
        ⟨fun hx => hcl x ((hmemC x).1 hx), fun hx => (hmemC x).2 (hsound x hx)⟩)
    have e2 : Nat.card {x // x ∈ Cl} = Nat.card {x // x ∈ Cl.toFinset} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm)
    rw [e1, e2, Nat.card_eq_fintype_card, Fintype.card_coe, List.toFinset_card_of_nodup hnodup]
  set K := C ⊓ Subgroup.centralizer ({y} : Set Y) with hK
  have hKmem : ∀ x : K, (x : Y) ∈ L := by
    intro x
    have hxC : (x : Y) ∈ C := x.2.1
    have hxy : (x : Y) * y = y * (x : Y) := Subgroup.mem_centralizer_singleton_iff.1 x.2.2
    exact hL x (hcl x ((hmemC x).1 hxC)) hxy
  have hKcard : Nat.card K ≤ L.length := by
    have hinj : Function.Injective (fun x : K => (⟨(x : Y), hKmem x⟩ : {z // z ∈ L})) := by
      intro a b e
      exact Subtype.ext (Subtype.mk.inj e)
    refine (Nat.card_le_card_of_injective _ hinj).trans ?_
    have e2 : Nat.card {x // x ∈ L} = Nat.card {x // x ∈ L.toFinset} :=
      Nat.card_congr (Equiv.subtypeEquivRight fun x => List.mem_toFinset.symm)
    rw [e2, Nat.card_eq_fintype_card, Fintype.card_coe]
    exact List.toFinset_card_le L
  have hmul : Nat.card K * K.relIndex C = Nat.card C := by
    have h1 : (⊥ : Subgroup Y) ≤ K := bot_le
    have h2 : K ≤ C := inf_le_left
    have := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup Y) K C h1 h2
    rwa [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at this
  have hidx' : 16 < K.relIndex C := by
    by_contra hcon
    have hr : K.relIndex C ≤ 16 := by omega
    have := Nat.mul_le_mul hKcard hr
    omega
  exact classRad_of_centralizer hy hy5 hVab hU hidx'

end ListData

end CFSG.QuasithinUnique.A5
