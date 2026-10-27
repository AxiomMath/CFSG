module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7Sec7Basic

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup DihedralGroup

namespace Sec8

open Sec7

variable {X : Type} [Group X] [Finite X] {S : A7Base X} {F : S.Frame}

noncomputable def coordsPre (S : A7Base X) (Q : Subgroup (DihedralGroup 4 × DihedralGroup 2)) :
    Subgroup X :=
  (Q.comap S.coords.toMonoidHom).map S.data.T.subtype

theorem mem_coordsPre {Q : Subgroup (DihedralGroup 4 × DihedralGroup 2)} {g : X}
    (hg : g ∈ S.data.T) : g ∈ coordsPre S Q ↔ S.coords ⟨g, hg⟩ ∈ Q := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact hh
  · intro h
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem R_eq_sup : S.data.R = zpowers S.x ⊔ zpowers S.y := by
  set f := dihedralLift 4 S.x S.y S.x_pow_four S.y_mul_y S.y_x_y with hf
  have hinj : Function.Injective f :=
    injective_dihedralLift 4 _ _ _ _ _ S.orderOf_x S.y_not_mem_zpowers_x
  refine (Subgroup.eq_of_le_of_card_ge (sup_le (zpowers_le.mpr S.x_mem)
    (zpowers_le.mpr S.y_mem)) ?_).symm
  rw [S.data.card_R, ← range_dihedralLift 4 S.x S.y S.x_pow_four S.y_mul_y S.y_x_y,
    ← hf, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]

def QR : Subgroup (DihedralGroup 4 × DihedralGroup 2) where
  carrier := {q | q.2 = 1}
  mul_mem' {a b} ha hb := by simp_all
  one_mem' := rfl
  inv_mem' {a} ha := by simp_all

def QB : Subgroup (DihedralGroup 4 × DihedralGroup 2) where
  carrier := {q | q.1 = 1 ∨ q.1 = r 2}
  mul_mem' {a b} ha hb := by
    revert ha hb
    obtain ⟨a1, a2⟩ := a
    obtain ⟨b1, b2⟩ := b
    simp only [Set.mem_ofPred_eq, Prod.fst_mul]
    revert a1 b1
    decide
  one_mem' := Or.inl rfl
  inv_mem' {a} ha := by
    revert ha
    obtain ⟨a1, a2⟩ := a
    simp only [Set.mem_ofPred_eq, Prod.fst_inv]
    revert a1
    decide

theorem R_le_coordsPre : S.data.R ≤ coordsPre S QR := by
  rw [R_eq_sup]
  refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
  · rw [mem_coordsPre S.x_mem.1, S.coords_x]; rfl
  · rw [mem_coordsPre S.y_mem.1, S.coords_y]; rfl

theorem B_le_coordsPre : S.B ≤ coordsPre S QB := by
  rw [A7Base.B, closure_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [SetLike.mem_coe, mem_coordsPre S.z_mem.1, S.coords_z]; exact Or.inr rfl
  · rw [SetLike.mem_coe, mem_coordsPre S.data.t_mem_T, S.coords_t]; exact Or.inl rfl
  · rw [SetLike.mem_coe, mem_coordsPre S.k_mem, S.coords_k]; exact Or.inl rfl

theorem coords_of_mem_R {g : X} (hg : g ∈ S.data.R) : (S.coords ⟨g, hg.1⟩).2 = 1 :=
  (mem_coordsPre hg.1).mp (R_le_coordsPre hg)

theorem coords_mul {a b : X} (ha : a ∈ S.data.T) (hb : b ∈ S.data.T) :
    S.coords ⟨a * b, mul_mem ha hb⟩ = S.coords ⟨a, ha⟩ * S.coords ⟨b, hb⟩ :=
  map_mul S.coords ⟨a, ha⟩ ⟨b, hb⟩

theorem coords_inv {a : X} (ha : a ∈ S.data.T) :
    S.coords ⟨a⁻¹, inv_mem ha⟩ = (S.coords ⟨a, ha⟩)⁻¹ :=
  map_inv S.coords ⟨a, ha⟩

theorem coords_pow {a : X} (ha : a ∈ S.data.T) (n : ℕ) :
    S.coords ⟨a ^ n, pow_mem ha n⟩ = (S.coords ⟨a, ha⟩) ^ n :=
  map_pow S.coords ⟨a, ha⟩ n

theorem coords_xF (F : S.Frame) :
    S.coords ⟨F.xF, xF_mem_T F⟩ = (r 1, 1) ∨ S.coords ⟨F.xF, xF_mem_T F⟩ = (r 3, 1) := by
  have h2 := coords_of_mem_R F.xF_mem
  have hsq : (S.coords ⟨F.xF, xF_mem_T F⟩) ^ 2 = (r 2, 1) := by
    rw [← coords_pow, ← S.coords_z]
    congr 1
    exact Subtype.ext F.xF_sq
  revert h2 hsq
  obtain ⟨d, e⟩ := S.coords ⟨F.xF, xF_mem_T F⟩
  revert d e
  decide

theorem coords_refl {a : X} (h : IsRefl F a) :
    ∃ i : ZMod 4, S.coords ⟨a, h.mem_T⟩ = (sr i, 1) := by
  have h2 := coords_of_mem_R h.mem
  have hinv : S.coords ⟨a, h.mem_T⟩ * S.coords ⟨F.xF, xF_mem_T F⟩ *
      (S.coords ⟨a, h.mem_T⟩)⁻¹ = (S.coords ⟨F.xF, xF_mem_T F⟩)⁻¹ := by
    rw [← coords_inv, ← coords_mul, ← coords_mul, ← coords_inv]
    congr 1
    exact Subtype.ext h.inv
  rcases coords_xF F with hx | hx <;> rw [hx] at hinv <;>
  · revert h2 hinv
    obtain ⟨d, e⟩ := S.coords ⟨a, h.mem_T⟩
    revert d e
    decide

theorem card_coordsPre (Q : Subgroup (DihedralGroup 4 × DihedralGroup 2)) :
    Nat.card (coordsPre S Q) = Nat.card Q := by
  have h : Q.comap S.coords.toMonoidHom = Q.map S.coords.symm.toMonoidHom := by
    ext g
    simp only [mem_comap, mem_map, MulEquiv.coe_toMonoidHom]
    exact ⟨fun hg => ⟨S.coords g, hg, by simp⟩, fun ⟨q, hq, hqg⟩ => hqg ▸ by simpa using hq⟩
  rw [coordsPre, card_map_of_injective (subtype_injective _), h,
    card_map_of_injective S.coords.symm.injective]

instance : DecidablePred (· ∈ QB) := fun q => inferInstanceAs (Decidable (q.1 = 1 ∨ q.1 = r 2))

theorem card_QB : Nat.card QB = 8 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem coordsPre_QB : coordsPre S QB = S.B :=
  (Subgroup.eq_of_le_of_card_ge B_le_coordsPre (by rw [card_coordsPre, card_QB, S.card_B])).symm

theorem mem_B_of_coords_fst {g : X} (hg : g ∈ S.data.T)
    (h : (S.coords ⟨g, hg⟩).1 = 1 ∨ (S.coords ⟨g, hg⟩).1 = r 2) : g ∈ S.B := by
  rw [← coordsPre_QB, mem_coordsPre hg]
  exact h

theorem mem_xB_of_conj_refl {a τ : X} (h : IsRefl F a) (hτ : τ ∈ S.data.T)
    (hc : τ * a * τ⁻¹ = S.z * a) :
    F.xF⁻¹ * τ ∈ S.B ∨ (F.xF * a)⁻¹ * τ ∈ S.B := by
  obtain ⟨i, hi⟩ := coords_refl h
  have hx := coords_xF F
  have hcc : S.coords ⟨τ, hτ⟩ * S.coords ⟨a, h.mem_T⟩ * (S.coords ⟨τ, hτ⟩)⁻¹ =
      (r 2, 1) * S.coords ⟨a, h.mem_T⟩ := by
    rw [← coords_inv, ← coords_mul, ← coords_mul, ← S.coords_z, ← coords_mul]
    congr 1
    exact Subtype.ext hc
  have key : ∀ (c : DihedralGroup 4 × DihedralGroup 2) (cx : DihedralGroup 4 × DihedralGroup 2)
      (j : ZMod 4), (cx = (r 1, 1) ∨ cx = (r 3, 1)) →
      c * (sr j, 1) * c⁻¹ = (r 2, 1) * (sr j, 1) →
      ((cx⁻¹ * c).1 = 1 ∨ (cx⁻¹ * c).1 = r 2) ∨
        (((cx * (sr j, 1))⁻¹ * c).1 = 1 ∨ ((cx * (sr j, 1))⁻¹ * c).1 = r 2) := by
    decide
  rw [hi] at hcc
  rcases key _ _ i hx hcc with h1 | h1
  · left
    refine mem_B_of_coords_fst (mul_mem (inv_mem (xF_mem_T F)) hτ) ?_
    rwa [coords_mul (inv_mem (xF_mem_T F)) hτ, coords_inv (xF_mem_T F)]
  · right
    refine mem_B_of_coords_fst (mul_mem (inv_mem (mul_mem (xF_mem_T F) h.mem_T)) hτ) ?_
    rwa [coords_mul (inv_mem (mul_mem (xF_mem_T F) h.mem_T)) hτ,
      coords_inv (mul_mem (xF_mem_T F) h.mem_T), coords_mul (xF_mem_T F) h.mem_T, hi]

end Sec8

end CFSG.ComponentClassification.HSFLit
