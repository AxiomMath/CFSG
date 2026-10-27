module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDelta
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs

public section

namespace CFSG.AGLEmbeddingD2.GN

open Equiv Equiv.Perm CFSG.QuasithinUnique CFSG.Quasithin

variable {W : Type*} [CommGroup W] {L : Subgroup (MulAut W)} {N : ℕ}

@[expose] def vec (β : ↥(commV L) ≃* Multiplicative (evenWeight N)) (u : ↥(commV L)) :
    Fin N → ZMod 2 := ((Multiplicative.toAdd (β u) : evenWeight N) : Fin N → ZMod 2)

theorem mem_commV_gen' {x : MulAut W} (hx : x ∈ L) (v : W) : x v * v⁻¹ ∈ commV L :=
  Subgroup.subset_closure ⟨x, hx, v, rfl⟩

theorem act_mem_commV' {h : MulAut W} (hh : h ∈ L) {u : W} (hu : u ∈ commV L) :
    h u ∈ commV L :=
  CFSG.Quasithin.commV_apply_mem_of_mem hh hu

theorem neg_vec (x : Fin N → ZMod 2) : -x = x := by
  funext i
  exact ZMod.neg_eq_self_mod_two _

variable (θ : ↥L ≃* Perm (Fin N)) (β : ↥(commV L) ≃* Multiplicative (evenWeight N))
  (hβ : SymCoreWith L N θ β)

include hβ in
theorem vec_act (h : ↥L) (u : ↥(commV L)) :
    vec β ⟨(h : MulAut W) (u : W), act_mem_commV' h.2 u.2⟩ = permAct (θ h) (vec β u) := by
  funext i
  exact hβ h u (act_mem_commV' h.2 u.2) i

theorem vec_mem_delta (u : ↥(commV L)) : vec β u ∈ evenWeight N :=
  (Multiplicative.toAdd (β u) : evenWeight N).2

theorem vec_injective : Function.Injective (vec β) := by
  intro u v h
  apply β.injective
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact h

theorem vec_mul (u v : ↥(commV L)) : vec β (u * v) = vec β u + vec β v := by
  unfold vec
  simp

theorem vec_surj {y : Fin N → ZMod 2} (hy : y ∈ evenWeight N) : ∃ u, vec β u = y := by
  refine ⟨β.symm (Multiplicative.ofAdd ⟨y, hy⟩), ?_⟩
  simp [vec]

theorem vec_one : vec β (1 : ↥(commV L)) = 0 := by
  unfold vec
  simp

theorem vec_eq_zero {u : ↥(commV L)} (h : vec β u = 0) : u = 1 :=
  vec_injective β (h.trans (vec_one β).symm)

@[expose] def CoversAlt (F : Subgroup (MulAut W)) : Prop :=
  ∀ g ∈ alternatingGroup (Fin N), ∃ h : ↥L, (h : MulAut W) ∈ F ∧ θ h = g

include hβ in
theorem irred_commV (hN : 5 ≤ N) (hodd : Odd N) {F : Subgroup (MulAut W)}
    (hF : CoversAlt θ F) {U : Subgroup W} (hU : U ≤ commV L)
    (hinv : ∀ h ∈ F, ∀ u ∈ U, h u ∈ U) : U = ⊥ ∨ U = commV L := by
  let Uv : AddSubgroup (Fin N → ZMod 2) :=
    { carrier := {v | ∃ u : ↥(commV L), (u : W) ∈ U ∧ vec β u = v}
      zero_mem' := ⟨1, U.one_mem, vec_one β⟩
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', U.mul_mem hu hu', vec_mul β u u'⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u, hu, (neg_vec _).symm⟩ }
  have hUv : Uv ≤ evenWeight N := by
    rintro _ ⟨u, -, rfl⟩
    exact vec_mem_delta β u
  have hUinv : ∀ g ∈ alternatingGroup (Fin N), ∀ x ∈ Uv, permAct g x ∈ Uv := by
    rintro g hg _ ⟨u, hu, rfl⟩
    obtain ⟨h, hhF, hθ⟩ := hF g hg
    refine ⟨⟨(h : MulAut W) (u : W), act_mem_commV' h.2 u.2⟩, hinv _ hhF _ hu, ?_⟩
    rw [vec_act θ β hβ h u, hθ]
  rcases delta_irred hN hodd hUv hUinv with hbot | htop
  · left
    refine eq_bot_iff.2 fun u hu => ?_
    have hmem : (⟨u, hU hu⟩ : ↥(commV L)) = 1 := by
      apply vec_eq_zero β
      have : vec β ⟨u, hU hu⟩ ∈ Uv := ⟨⟨u, hU hu⟩, hu, rfl⟩
      rw [hbot] at this
      simpa using this
    have := congrArg Subtype.val hmem
    simpa using this
  · right
    refine le_antisymm hU fun w hw => ?_
    have : vec β ⟨w, hw⟩ ∈ Uv := htop ▸ vec_mem_delta β ⟨w, hw⟩
    obtain ⟨u, hu, hv⟩ := this
    have h3 : u = ⟨w, hw⟩ := vec_injective β hv
    have h4 : (u : W) = w := congrArg Subtype.val h3
    rw [← h4]
    exact hu

include hβ in
theorem fix_commV (hN : 5 ≤ N) (hodd : Odd N) {F : Subgroup (MulAut W)} (hF : CoversAlt θ F)
    {u : W} (hu : u ∈ commV L) (hfix : ∀ h ∈ F, h u = u) : u = 1 := by
  have hx : vec β ⟨u, hu⟩ = 0 := by
    apply delta_fix (by omega) hodd (vec_mem_delta β _)
    intro g hg
    obtain ⟨h, hhF, hθ⟩ := hF g hg
    rw [← hθ, ← vec_act θ β hβ h ⟨u, hu⟩]
    congr 1
    exact Subtype.ext (hfix _ hhF)
  exact congrArg Subtype.val (vec_eq_zero β hx)

include hβ in
theorem four_commutators [Finite W] (hN : 5 ≤ N) {a b p : Fin N} (hab : a ≠ b) (hbp : b ≠ p)
    (hap : a ≠ p) {h : ↥L} (hθ : θ h = c3 a b p) :
    4 ≤ (Set.range fun w : ↥(commV L) => ((h : MulAut W) (w : W)) * (w : W)⁻¹).ncard := by
  let Ψ : ↥(commV L) → ↥(commV L) := fun w =>
    ⟨(h : MulAut W) (w : W) * (w : W)⁻¹,
      (commV L).mul_mem (act_mem_commV' h.2 w.2) ((commV L).inv_mem w.2)⟩
  have hvec : ∀ w, vec β (Ψ w) = permAct (c3 a b p) (vec β w) + vec β w := by
    intro w
    have h1 : Ψ w = ⟨(h : MulAut W) (w : W), act_mem_commV' h.2 w.2⟩ * w⁻¹ := rfl
    have h2 : vec β w⁻¹ = vec β w := by
      have := vec_mul β w w⁻¹
      rw [mul_inv_cancel, vec_one] at this
      have h3 : vec β w⁻¹ = -vec β w := eq_neg_of_add_eq_zero_right this.symm
      rw [h3, neg_vec]
    rw [h1, vec_mul, vec_act θ β hβ h w, hθ, h2]
  have hrange : Set.range (fun w : ↥(commV L) => ((h : MulAut W) (w : W)) * (w : W)⁻¹) =
      Subtype.val '' Set.range Ψ := by
    ext y; constructor
    · rintro ⟨w, rfl⟩; exact ⟨Ψ w, ⟨w, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨w, rfl⟩, rfl⟩; exact ⟨w, rfl⟩
  rw [hrange, Set.ncard_image_of_injective _ Subtype.val_injective]
  have hsub : {y : Fin N → ZMod 2 | ∃ v ∈ evenWeight N, permAct (c3 a b p) v + v = y} ⊆
      vec β '' Set.range Ψ := by
    rintro y ⟨v, hv, rfl⟩
    obtain ⟨w, hw⟩ := vec_surj β hv
    exact ⟨Ψ w, ⟨w, rfl⟩, by rw [hvec, hw]⟩
  calc 4 ≤ {y : Fin N → ZMod 2 | ∃ v ∈ evenWeight N, permAct (c3 a b p) v + v = y}.ncard :=
        delta_four hN hab hbp hap
    _ ≤ (vec β '' Set.range Ψ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (Set.range Ψ).ncard := Set.ncard_image_le (Set.toFinite _)

end CFSG.AGLEmbeddingD2.GN
