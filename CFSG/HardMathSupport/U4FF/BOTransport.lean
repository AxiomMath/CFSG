module

public import CFSG.Quasithin.Background.Module
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.HardMathSupport.U4FF

open CFSG.Quasithin Subgroup

variable {S : Type} [CommGroup S] {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]

@[expose] def boAdd (ψ : S ≃* Multiplicative (ι → F)) (g : MulAut S) : AddAut (ι → F) where
  toFun x := Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd x))))
  invFun x := Multiplicative.toAdd (ψ (g⁻¹ (ψ.symm (Multiplicative.ofAdd x))))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [ofAdd_add, map_mul, toAdd_mul]

theorem boAdd_apply (ψ : S ≃* Multiplicative (ι → F)) (g : MulAut S) (x : ι → F) :
    boAdd ψ g x = Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd x)))) :=
  rfl

theorem boAdd_toAdd (ψ : S ≃* Multiplicative (ι → F)) (g : MulAut S) (s : S) :
    boAdd ψ g (Multiplicative.toAdd (ψ s)) = Multiplicative.toAdd (ψ (g s)) := by
  rw [boAdd_apply]
  simp

theorem boAdd_mul (ψ : S ≃* Multiplicative (ι → F)) (g h : MulAut S) :
    boAdd ψ (g * h) = boAdd ψ g + boAdd ψ h :=
  AddEquiv.ext fun x => by
    show boAdd ψ (g * h) x = boAdd ψ g (boAdd ψ h x)
    rw [boAdd_apply ψ h x, boAdd_toAdd]
    exact boAdd_apply ψ (g * h) x

theorem boAdd_one (ψ : S ≃* Multiplicative (ι → F)) : boAdd ψ 1 = 0 :=
  AddEquiv.ext fun x => by
    show boAdd ψ 1 x = x
    rw [boAdd_apply]
    simp

theorem boAdd_inv (ψ : S ≃* Multiplicative (ι → F)) (g : MulAut S) :
    boAdd ψ g⁻¹ = -boAdd ψ g :=
  AddEquiv.ext fun _ => rfl

theorem boAdd_injective (ψ : S ≃* Multiplicative (ι → F)) :
    Function.Injective (boAdd ψ) := by
  intro g h hgh
  refine MulEquiv.ext fun s => ?_
  have h1 := congrArg (fun e : AddAut (ι → F) => e (Multiplicative.toAdd (ψ s))) hgh
  simp only [boAdd_toAdd] at h1
  exact ψ.injective (Multiplicative.toAdd.injective h1)

@[expose] def boSub (ψ : S ≃* Multiplicative (ι → F)) (Q : Subgroup (MulAut S)) :
    AddSubgroup (AddAut (ι → F)) where
  carrier := {a | ∃ g ∈ Q, boAdd ψ g = a}
  add_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    exact ⟨g * h, Q.mul_mem hg hh, boAdd_mul ψ g h⟩
  zero_mem' := ⟨1, Q.one_mem, boAdd_one ψ⟩
  neg_mem' := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, Q.inv_mem hg, boAdd_inv ψ g⟩

theorem boSub_card (ψ : S ≃* Multiplicative (ι → F)) (Q : Subgroup (MulAut S)) :
    Nat.card (boSub ψ Q) = Nat.card Q := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g : Q => (⟨boAdd ψ g.1, g.1, g.2, rfl⟩ : boSub ψ Q)) ⟨?_, ?_⟩).symm
  · intro g h hgh
    exact Subtype.ext (boAdd_injective ψ (congrArg Subtype.val hgh))
  · rintro ⟨a, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem bo_fix_iff (ψ : S ≃* Multiplicative (ι → F)) (Q : Subgroup (MulAut S))
    (x : ι → F) :
    (∀ a ∈ boSub ψ Q, a x = x) ↔ ψ.symm (Multiplicative.ofAdd x) ∈ fixV Q := by
  have hx : x = Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd x))) := by simp
  constructor
  · intro h
    refine mem_fixV.mpr fun g hg => ?_
    have h1 : Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd x)))) = x :=
      h (boAdd ψ g) ⟨g, hg, rfl⟩
    exact ψ.injective (Multiplicative.toAdd.injective (h1.trans hx))
  · intro h a ha
    obtain ⟨g, hg, rfl⟩ := ha
    have hgs : g (ψ.symm (Multiplicative.ofAdd x)) = ψ.symm (Multiplicative.ofAdd x) :=
      mem_fixV.mp h g hg
    show boAdd ψ g x = x
    rw [boAdd_apply, hgs]
    simp

theorem bo_add_self (ψ : S ≃* Multiplicative (ι → F)) {Q : Subgroup (MulAut S)}
    (hQ : IsElemAbelian2 Q) : ∀ a ∈ boSub ψ Q, a + a = 0 := by
  rintro _ ⟨g, hg, rfl⟩
  have hgg : g * g = 1 := by
    rw [← sq]
    exact hQ.2 g hg
  rw [← boAdd_mul ψ g g, hgg, boAdd_one]

theorem bo_comm (ψ : S ≃* Multiplicative (ι → F)) {Q : Subgroup (MulAut S)}
    (hQ : IsElemAbelian2 Q) : ∀ a ∈ boSub ψ Q, ∀ b ∈ boSub ψ Q, a + b = b + a := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
  rw [← boAdd_mul ψ g h, ← boAdd_mul ψ h g, hQ.1 g hg h hh]

theorem bo_quad (ψ : S ≃* Multiplicative (ι → F)) {Q : Subgroup (MulAut S)}
    (hQq : IsQuadratic Q) :
    ∀ a ∈ boSub ψ Q, ∀ b ∈ boSub ψ Q, ∀ x : ι → F,
      a (b x - x) = b x - x := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ x
  obtain ⟨s, rfl⟩ : ∃ s : S, x = Multiplicative.toAdd (ψ s) :=
    ⟨ψ.symm (Multiplicative.ofAdd x), by simp⟩
  have hsub : boAdd ψ h (Multiplicative.toAdd (ψ s)) - Multiplicative.toAdd (ψ s) =
      Multiplicative.toAdd (ψ (h s * s⁻¹)) := by
    rw [boAdd_toAdd]
    simp [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hcomm : h s * s⁻¹ ∈ commV Q := by
    unfold commV
    exact Subgroup.subset_closure ⟨h, hh, s, rfl⟩
  have hq' : commV Q ≤ fixV Q := hQq
  have hfix : g (h s * s⁻¹) = h s * s⁻¹ := mem_fixV.mp (hq' hcomm) g hg
  rw [hsub, boAdd_toAdd, hfix]

theorem bo_normalizes {G : Subgroup (GL ι F)} {L A : Subgroup (MulAut S)}
    (ε : ↥L ≃* ↥G) (ψ : S ≃* Multiplicative (ι → F))
    (hεψ : ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
      (((ε l : GL ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (ψ s))))
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) {Q : Subgroup (MulAut S)}
    (hQA : Q ≤ A) :
    ∀ a ∈ boSub ψ Q, ∀ g ∈ G, ∃ g' ∈ G, ∀ x : ι → F,
      a (((g : GL ι F) : Matrix ι ι F).mulVec x) =
        ((g' : GL ι F) : Matrix ι ι F).mulVec (a x) := by
  rintro _ ⟨k, hk, rfl⟩ g hg
  have hkN : k ∈ Subgroup.normalizer (L : Set (MulAut S)) := hAN (hQA hk)
  obtain ⟨l, hl⟩ : ∃ l : ↥L, ε l = ⟨g, hg⟩ := ⟨ε.symm ⟨g, hg⟩, ε.apply_symm_apply _⟩
  have hgl : ((ε l : GL ι F)) = g := congrArg Subtype.val hl
  have hlN : k * (l : MulAut S) * k⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hkN (l : MulAut S)).mp l.2
  obtain ⟨l', hl'⟩ : ∃ l' : ↥L, (l' : MulAut S) = k * (l : MulAut S) * k⁻¹ :=
    ⟨⟨_, hlN⟩, rfl⟩
  refine ⟨(ε l' : GL ι F), (ε l').2, fun x => ?_⟩
  obtain ⟨v, rfl⟩ : ∃ v : S, x = Multiplicative.toAdd (ψ v) :=
    ⟨ψ.symm (Multiplicative.ofAdd x), by simp⟩
  have e1 : Multiplicative.toAdd (ψ ((l : MulAut S) v)) =
      ((g : GL ι F) : Matrix ι ι F).mulVec (Multiplicative.toAdd (ψ v)) := by
    rw [hεψ l v, toAdd_ofAdd, hgl]
  have e2 : Multiplicative.toAdd (ψ ((l' : MulAut S) (k v))) =
      ((ε l' : GL ι F) : Matrix ι ι F).mulVec
        (Multiplicative.toAdd (ψ (k v))) := by
    rw [hεψ l' (k v), toAdd_ofAdd]
  have e3 : (l' : MulAut S) (k v) = k ((l : MulAut S) v) := by
    rw [hl']
    simp
  rw [← e1, boAdd_toAdd, boAdd_toAdd, ← e2, e3]

theorem bo_card_fix (ψ : S ≃* Multiplicative (ι → F)) (Q : Subgroup (MulAut S)) :
    Nat.card {x : ι → F // ∀ a ∈ boSub ψ Q, a x = x} = Nat.card (fixV Q) := by
  let e : (ι → F) ≃ S := (Multiplicative.ofAdd : (ι → F) ≃ Multiplicative (ι → F)).trans
    ψ.symm.toEquiv
  exact Nat.card_congr (Equiv.subtypeEquiv e fun x => bo_fix_iff ψ Q x)

theorem bo_card_space (ψ : S ≃* Multiplicative (ι → F)) : Nat.card (ι → F) = Nat.card S :=
  Nat.card_congr ((Multiplicative.ofAdd : (ι → F) ≃ Multiplicative (ι → F)).trans
    ψ.symm.toEquiv)

end CFSG.HardMathSupport.U4FF
