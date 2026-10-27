module

public import CFSG.GroupTheory.CentralExtensionPGroup
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.GroupTheory

open CFSG.CGT.Timmesfeld75

theorem map_conjSubgroup {G K : Type*} [Group G] [Group K] (f : G →* K) (A : Subgroup G) (x : G) :
    conjSubgroup (f x) (A.map f) = (conjSubgroup x A).map f := by
  ext y
  rw [mem_conjSubgroup, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, hay⟩
    refine ⟨x * a * x⁻¹, ?_, ?_⟩
    · rw [mem_conjSubgroup, show x⁻¹ * (x * a * x⁻¹) * x = a by group]; exact ha
    · rw [map_mul, map_mul, map_inv, hay]; group
  · rintro ⟨a, ha, rfl⟩
    refine ⟨x⁻¹ * a * x, mem_conjSubgroup.mp ha, ?_⟩
    rw [map_mul, map_mul, map_inv]

theorem isPGroup_closure_of_le_nilpotent {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    [Group.IsNilpotent A] {S : Set Y} (hSA : S ⊆ A) (hS : ∀ s ∈ S, s * s = 1) :
    IsPGroup 2 (Subgroup.closure S) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S' : Set A := {a | (a : Y) ∈ S} with hS'
  have h1 : IsPGroup 2 (Subgroup.closure S') :=
    CFSG.GroupTheory.isPGroup_closure_of_isNilpotent (p := 2) (S := S') fun s hs => by
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simpa [pow_two] using hS _ hs
  have himg : A.subtype '' S' = S := by
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ha
    · intro hy
      exact ⟨⟨y, hSA hy⟩, hy, rfl⟩
  have hmap : (Subgroup.closure S').map A.subtype = Subgroup.closure S := by
    rw [MonoidHom.map_closure, himg]
  rw [← hmap]
  exact h1.of_equiv (Subgroup.equivMapOfInjective _ A.subtype A.subtype_injective)

theorem isPGroup_sup_iff_map_center {Y : Type} [Group Y] [Finite Y] {A : Subgroup Y}
    (hA : ∀ a ∈ A, a * a = 1) (y : Y) :
    IsPGroup 2 ↥(A ⊔ conjSubgroup y A) ↔
      IsPGroup 2 ↥(A.map (QuotientGroup.mk' (Subgroup.center Y)) ⊔
        conjSubgroup (QuotientGroup.mk' (Subgroup.center Y) y)
          (A.map (QuotientGroup.mk' (Subgroup.center Y)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (Subgroup.center Y) with hπ
  have hmap : (A ⊔ conjSubgroup y A).map π =
      A.map π ⊔ conjSubgroup (π y) (A.map π) := by
    rw [Subgroup.map_sup, ← map_conjSubgroup]
  rw [← hmap]
  constructor
  · intro h
    exact h.of_surjective (π.subgroupMap (A ⊔ conjSubgroup y A))
      (MonoidHom.subgroupMap_surjective _ _)
  · intro h
    have hcl : Subgroup.closure ((A : Set Y) ∪ (conjSubgroup y A : Set Y)) =
        A ⊔ conjSubgroup y A := by
      rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
    rw [← hcl] at h ⊢
    refine CFSG.GroupTheory.isPGroup_closure_of_map_center (p := 2) ?_ h
    rintro s (hs | hs)
    · exact ⟨1, by simpa [pow_two] using hA s hs⟩
    · refine ⟨1, ?_⟩
      have h1 := hA _ (mem_conjSubgroup.mp hs)
      have : s * s = y * ((y⁻¹ * s * y) * (y⁻¹ * s * y)) * y⁻¹ := by group
      rw [pow_one, pow_two, this, h1]
      group

section Inv

variable {N : Type} [Group N]

@[expose] def invGroup (V E : Subgroup N) : Subgroup N :=
  ⨆ (W : Subgroup N) (_ : (∃ g : N, W = conjSubgroup g V) ∧
    E ≤ Subgroup.normalizer (W : Set N)), W

theorem le_invGroup {V E W : Subgroup N} (hW : ∃ g : N, W = conjSubgroup g V)
    (hE : E ≤ Subgroup.normalizer (W : Set N)) : W ≤ invGroup V E :=
  le_iSup₂_of_le W ⟨hW, hE⟩ le_rfl

theorem invGroup_map_le (V E : Subgroup N) (hEV : E ≤ V) (α : N ≃* N)
    (hα : ∀ v ∈ V, α v = v) : (invGroup V E).map α.toMonoidHom ≤ invGroup V E := by
  have hmapV : V.map α.toMonoidHom = V := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      simpa [hα v hv] using hv
    · intro hx
      exact ⟨x, hx, hα x hx⟩
  rw [invGroup, Subgroup.map_iSup]
  refine iSup_le fun W => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hW => ?_
  apply le_invGroup
  · obtain ⟨g, rfl⟩ := hW.1
    refine ⟨α g, ?_⟩
    rw [← map_conjSubgroup α.toMonoidHom V g, hmapV]
    rfl
  · intro e he
    have heV : α e = e := hα e (hEV he)
    have hesymm : α.symm e = e := by rw [MulEquiv.symm_apply_eq]; exact heV.symm
    have hn := Subgroup.mem_normalizer_iff.mp (hW.2 he)
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 : ∀ x, x ∈ W.map α.toMonoidHom ↔ α.symm x ∈ W := fun x =>
      Subgroup.mem_map_equiv
    rw [h1, h1, map_mul, map_mul, map_inv, hesymm]
    exact hn _

end Inv

theorem transfer_inv_data {A B : Type} [Group A] [Group B] (e : A ≃* B) (Va : Subgroup A)
    (xB : B) (ΛB : Subgroup B)
    (hnp : ¬ IsPGroup 2 ↥(Va.map e.toMonoidHom ⊔ conjSubgroup xB (Va.map e.toMonoidHom)))
    (hxΛ : conjSubgroup xB (Va.map e.toMonoidHom) ≤ ΛB) (hΛ : ΛB ≠ ⊤)
    (hinv : ∀ β : MulAut B, (∀ v ∈ Va.map e.toMonoidHom, β v = v) →
      ΛB.map β.toMonoidHom ≤ ΛB) :
    ∃ (xA : A) (ΛA : Subgroup A), ¬ IsPGroup 2 ↥(Va ⊔ conjSubgroup xA Va) ∧
      conjSubgroup xA Va ≤ ΛA ∧ ΛA ≠ ⊤ ∧
      ∀ α : MulAut A, (∀ v ∈ Va, α v = v) → ΛA.map α.toMonoidHom ≤ ΛA := by
  have hmapconj : (conjSubgroup (e.symm xB) Va).map e.toMonoidHom =
      conjSubgroup xB (Va.map e.toMonoidHom) := by
    rw [← map_conjSubgroup e.toMonoidHom Va (e.symm xB)]
    simp
  refine ⟨e.symm xB, ΛB.map e.symm.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h2
    apply hnp
    have hm : (Va ⊔ conjSubgroup (e.symm xB) Va).map e.toMonoidHom =
        Va.map e.toMonoidHom ⊔ conjSubgroup xB (Va.map e.toMonoidHom) := by
      rw [Subgroup.map_sup, hmapconj]
    rw [← hm]
    exact h2.of_surjective (e.toMonoidHom.subgroupMap _)
      (MonoidHom.subgroupMap_surjective _ _)
  · intro y hy
    have h1 : e y ∈ conjSubgroup xB (Va.map e.toMonoidHom) := by
      rw [← hmapconj]
      exact ⟨y, hy, rfl⟩
    exact ⟨e y, hxΛ h1, by simp⟩
  · intro htop
    apply hΛ
    rw [eq_top_iff]
    intro b _
    have hb : e.symm b ∈ ΛB.map e.symm.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨l, hl, hlb⟩ := hb
    have : l = b := e.symm.injective hlb
    exact this ▸ hl
  · intro α hα
    set β : MulAut B := e.symm.trans (α.trans e) with hβ
    have hβfix : ∀ v ∈ Va.map e.toMonoidHom, β v = v := by
      rintro _ ⟨a, ha, rfl⟩
      simp [hβ, hα a ha]
    have hle := hinv β hβfix
    rintro _ ⟨_, ⟨l, hl, rfl⟩, rfl⟩
    have h1 : β l ∈ ΛB := hle ⟨l, hl, rfl⟩
    refine ⟨β l, h1, ?_⟩
    simp [hβ]

end CFSG.GroupTheory
