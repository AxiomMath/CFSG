module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFBNQuad
public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFDefs
public import CFSG.Quasithin.Background.B15P4Repl

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

section Transport

variable {S : Type} [CommGroup S] {F : Type} [Field F]

@[expose] def partBAdd (ψ : S ≃* Multiplicative (Fin 4 → F)) (g : MulAut S) :
    AddAut (Fin 4 → F) where
  toFun x := Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd x))))
  invFun x := Multiplicative.toAdd (ψ (g⁻¹ (ψ.symm (Multiplicative.ofAdd x))))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp only [ofAdd_add, map_mul, toAdd_mul]

theorem partBAdd_apply (ψ : S ≃* Multiplicative (Fin 4 → F)) (g : MulAut S) (x : Fin 4 → F) :
    partBAdd ψ g x = Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd x)))) :=
  rfl

theorem partBAdd_toAdd (ψ : S ≃* Multiplicative (Fin 4 → F)) (g : MulAut S) (s : S) :
    partBAdd ψ g (Multiplicative.toAdd (ψ s)) = Multiplicative.toAdd (ψ (g s)) := by
  rw [partBAdd_apply]
  simp

theorem partBAdd_mul (ψ : S ≃* Multiplicative (Fin 4 → F)) (g h : MulAut S) :
    partBAdd ψ (g * h) = partBAdd ψ g + partBAdd ψ h :=
  AddEquiv.ext fun x => by
    show partBAdd ψ (g * h) x = partBAdd ψ g (partBAdd ψ h x)
    rw [partBAdd_apply ψ h x, partBAdd_toAdd]
    exact partBAdd_apply ψ (g * h) x

theorem partBAdd_one (ψ : S ≃* Multiplicative (Fin 4 → F)) : partBAdd ψ 1 = 0 :=
  AddEquiv.ext fun x => by
    show partBAdd ψ 1 x = x
    rw [partBAdd_apply]
    simp

theorem partBAdd_inv (ψ : S ≃* Multiplicative (Fin 4 → F)) (g : MulAut S) :
    partBAdd ψ g⁻¹ = -partBAdd ψ g :=
  AddEquiv.ext fun _ => rfl

theorem partBAdd_injective (ψ : S ≃* Multiplicative (Fin 4 → F)) :
    Function.Injective (partBAdd ψ) := by
  intro g h hgh
  refine MulEquiv.ext fun s => ?_
  have h1 := congrArg (fun e : AddAut (Fin 4 → F) => e (Multiplicative.toAdd (ψ s))) hgh
  simp only [partBAdd_toAdd] at h1
  exact ψ.injective (Multiplicative.toAdd.injective h1)

@[expose] def partBSub (ψ : S ≃* Multiplicative (Fin 4 → F)) (Q : Subgroup (MulAut S)) :
    AddSubgroup (AddAut (Fin 4 → F)) where
  carrier := {a | ∃ g ∈ Q, partBAdd ψ g = a}
  add_mem' := by
    rintro _ _ ⟨g, hg, rfl⟩ ⟨h, hh, rfl⟩
    exact ⟨g * h, Q.mul_mem hg hh, partBAdd_mul ψ g h⟩
  zero_mem' := ⟨1, Q.one_mem, partBAdd_one ψ⟩
  neg_mem' := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨g⁻¹, Q.inv_mem hg, partBAdd_inv ψ g⟩

theorem partBSub_card (ψ : S ≃* Multiplicative (Fin 4 → F)) (Q : Subgroup (MulAut S)) :
    Nat.card (partBSub ψ Q) = Nat.card Q := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun g : Q => (⟨partBAdd ψ g.1, g.1, g.2, rfl⟩ : partBSub ψ Q)) ⟨?_, ?_⟩).symm
  · intro g h hgh
    exact Subtype.ext (partBAdd_injective ψ (congrArg Subtype.val hgh))
  · rintro ⟨a, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩

theorem partB_fix_iff (ψ : S ≃* Multiplicative (Fin 4 → F)) (Q : Subgroup (MulAut S))
    (x : Fin 4 → F) :
    (∀ a ∈ partBSub ψ Q, a x = x) ↔ ψ.symm (Multiplicative.ofAdd x) ∈ fixV Q := by
  have hx : x = Multiplicative.toAdd (ψ (ψ.symm (Multiplicative.ofAdd x))) := by simp
  constructor
  · intro h
    refine mem_fixV.mpr fun g hg => ?_
    have h1 : Multiplicative.toAdd (ψ (g (ψ.symm (Multiplicative.ofAdd x)))) = x :=
      h (partBAdd ψ g) ⟨g, hg, rfl⟩
    exact ψ.injective (Multiplicative.toAdd.injective (h1.trans hx))
  · intro h a ha
    obtain ⟨g, hg, rfl⟩ := ha
    have hgs : g (ψ.symm (Multiplicative.ofAdd x)) = ψ.symm (Multiplicative.ofAdd x) :=
      mem_fixV.mp h g hg
    show partBAdd ψ g x = x
    rw [partBAdd_apply, hgs]
    simp

theorem partB_add_self (ψ : S ≃* Multiplicative (Fin 4 → F)) {Q : Subgroup (MulAut S)}
    (hQ : IsElemAbelian2 Q) : ∀ a ∈ partBSub ψ Q, a + a = 0 := by
  rintro _ ⟨g, hg, rfl⟩
  have hgg : g * g = 1 := by
    rw [← sq]
    exact hQ.2 g hg
  rw [← partBAdd_mul ψ g g, hgg, partBAdd_one]

theorem partB_quad (ψ : S ≃* Multiplicative (Fin 4 → F)) {Q : Subgroup (MulAut S)}
    (hQq : IsQuadratic Q) :
    ∀ a ∈ partBSub ψ Q, ∀ b ∈ partBSub ψ Q, ∀ x : Fin 4 → F,
      a (b x - x) = b x - x := by
  rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩ x
  obtain ⟨s, rfl⟩ : ∃ s : S, x = Multiplicative.toAdd (ψ s) :=
    ⟨ψ.symm (Multiplicative.ofAdd x), by simp⟩
  have hsub : partBAdd ψ h (Multiplicative.toAdd (ψ s)) - Multiplicative.toAdd (ψ s) =
      Multiplicative.toAdd (ψ (h s * s⁻¹)) := by
    rw [partBAdd_toAdd]
    simp [map_mul, map_inv, toAdd_mul, toAdd_inv, sub_eq_add_neg]
  have hcomm : h s * s⁻¹ ∈ commV Q := by
    unfold commV
    exact Subgroup.subset_closure ⟨h, hh, s, rfl⟩
  have hq' : commV Q ≤ fixV Q := hQq
  have hfix : g (h s * s⁻¹) = h s * s⁻¹ := mem_fixV.mp (hq' hcomm) g hg
  rw [hsub, partBAdd_toAdd, hfix]

theorem partB_statedSU {n : ℕ} {L A : Subgroup (MulAut S)}
    (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (ψ : S ≃* Multiplicative (Fin 4 → F))
    (hεψ : ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
      (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (ψ s))))
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) {Q : Subgroup (MulAut S)}
    (hQA : Q ≤ A) :
    ∀ a ∈ partBSub ψ Q, ∀ G ∈ StatedSU 4 (2 ^ n) F, ∃ G' ∈ StatedSU 4 (2 ^ n) F,
      ∀ x : Fin 4 → F, a (((G : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec x) =
        ((G' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (a x) := by
  rintro _ ⟨g, hg, rfl⟩ G hG
  have hgN : g ∈ Subgroup.normalizer (L : Set (MulAut S)) := hAN (hQA hg)
  obtain ⟨l, hl⟩ : ∃ l : ↥L, ε l = ⟨G, hG⟩ := ⟨ε.symm ⟨G, hG⟩, ε.apply_symm_apply _⟩
  have hGl : ((ε l : GL (Fin 4) F)) = G := congrArg Subtype.val hl
  have hlN : g * (l : MulAut S) * g⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hgN (l : MulAut S)).mp l.2
  obtain ⟨l', hl'⟩ : ∃ l' : ↥L, (l' : MulAut S) = g * (l : MulAut S) * g⁻¹ :=
    ⟨⟨_, hlN⟩, rfl⟩
  refine ⟨(ε l' : GL (Fin 4) F), (ε l').2, fun x => ?_⟩
  obtain ⟨v, rfl⟩ : ∃ v : S, x = Multiplicative.toAdd (ψ v) :=
    ⟨ψ.symm (Multiplicative.ofAdd x), by simp⟩
  have e1 : Multiplicative.toAdd (ψ ((l : MulAut S) v)) =
      ((G : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (ψ v)) := by
    rw [hεψ l v, toAdd_ofAdd, hGl]
  have e2 : Multiplicative.toAdd (ψ ((l' : MulAut S) (g v))) =
      ((ε l' : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec
        (Multiplicative.toAdd (ψ (g v))) := by
    rw [hεψ l' (g v), toAdd_ofAdd]
  have e3 : (l' : MulAut S) (g v) = g ((l : MulAut S) v) := by
    rw [hl']
    simp
  rw [← e1, partBAdd_toAdd, partBAdd_toAdd, ← e2, e3]

end Transport

theorem partB_N_sub {S : Type} [CommGroup S] {n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2) {L A : Subgroup (MulAut S)}
    (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F)) (ψ : S ≃* Multiplicative (Fin 4 → F))
    (hεψ : ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
      (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (ψ s))))
    (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) {Q : Subgroup (MulAut S)}
    (hQA : Q ≤ A) (hQ : IsElemAbelian2 Q) (hQq : IsQuadratic Q) :
    Nat.card Q * Nat.card (fixV Q) ≤ Nat.card S := by
  let e : (Fin 4 → F) ≃ S := (Multiplicative.ofAdd : (Fin 4 → F) ≃ Multiplicative (Fin 4 → F)).trans
    ψ.symm.toEquiv
  have hquadN := partB_N_quadratic hn hF (partBSub ψ Q) (partB_add_self ψ hQ)
    (partB_quad ψ hQq) (partB_statedSU ε ψ hεψ hAN hQA)
  have hfix : Nat.card {x : Fin 4 → F // ∀ a ∈ partBSub ψ Q, a x = x} =
      Nat.card (fixV Q) :=
    Nat.card_congr (Equiv.subtypeEquiv e fun x => partB_fix_iff ψ Q x)
  have hS' : Nat.card (Fin 4 → F) = Nat.card S := Nat.card_congr e
  rw [partBSub_card, hfix, hS'] at hquadN
  exact hquadN

theorem partB_N {S : Type} [CommGroup S] [Finite S] (hS : ∀ s : S, s ^ 2 = 1) {n : ℕ}
    (hn : 1 ≤ n) {F : Type} [Field F] [Finite F] (hF : Nat.card F = (2 ^ n) ^ 2)
    {L A : Subgroup (MulAut S)} (ε : ↥L ≃* ↥(StatedSU 4 (2 ^ n) F))
    (ψ : S ≃* Multiplicative (Fin 4 → F))
    (hεψ : ∀ (l : ↥L) (s : S), ψ ((l : MulAut S) s) = Multiplicative.ofAdd
      (((ε l : GL (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).mulVec (Multiplicative.toAdd (ψ s))))
    (hA : IsElemAbelian2 A) (hAN : A ≤ Subgroup.normalizer (L : Set (MulAut S))) :
    Nat.card A * Nat.card (fixV A) ≤ Nat.card S := by
  by_contra hcon
  rw [not_le] at hcon
  have hne : A ≠ ⊥ := by
    rintro rfl
    rw [B1.card_bot_mul_card_fixV] at hcon
    exact lt_irrefl _ hcon
  obtain ⟨B, -, hB, hBc⟩ := B1.exists_offender_below (X := A) (A := A)
    ⟨le_rfl, hne, hA⟩ 1 (Nat.succ_le_of_lt hcon)
  obtain ⟨Q, -, hQ, hQq, hQc, -, -⟩ := exists_quadratic_offender_le hS hB
  have hle := partB_N_sub hn hF ε ψ hεψ hAN hQ.1 hQ.2.2.1 hQq
  rw [← hQc] at hBc
  exact absurd (le_trans hBc hle) (by omega)

end CFSG.LocalAnalysis.RankThreeUC
