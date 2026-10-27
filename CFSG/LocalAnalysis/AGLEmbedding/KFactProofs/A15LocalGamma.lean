module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.A15LocalPerm
public import CFSG.Open.GLBDefs
import CFSG.LocalAnalysis.SectionRank.PRank

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A15Local

open Equiv CFSG.Open

open Equiv CFSG.Open

theorem shiftPerm_inv (f : ZMod 3 → ZMod 5) : (shiftPerm f)⁻¹ = shiftPerm (-f) :=
  inv_eq_of_mul_eq_one_right (by rw [← shiftPerm_add, add_neg_cancel, shiftPerm_zero])

@[expose] def qPair (k : ZMod 3) : Subgroup (Perm Pt) where
  carrier := {g | ∃ f : ZMod 3 → ZMod 5, f k = 0 ∧ g = shiftPerm f}
  one_mem' := ⟨0, rfl, shiftPerm_zero.symm⟩
  mul_mem' := by
    rintro _ _ ⟨f, hf, rfl⟩ ⟨f', hf', rfl⟩
    exact ⟨f + f', by simp [hf, hf'], (shiftPerm_add f f').symm⟩
  inv_mem' := by
    rintro _ ⟨f, hf, rfl⟩
    exact ⟨-f, by simp [hf], shiftPerm_inv f⟩

theorem qPair_le_sylowT (k : ZMod 3) : qPair k ≤ sylowT := by
  rintro _ ⟨f, -, rfl⟩
  exact shiftPerm_mem_sylowT f

theorem card_fun_vanishing (k : ZMod 3) :
    Nat.card {f : ZMod 3 → ZMod 5 // f k = 0} = 5 ^ 2 := by
  rw [Nat.card_eq_fintype_card]
  revert k
  decide +kernel

theorem card_qPair (k : ZMod 3) : Nat.card (qPair k) = 5 ^ 2 := by
  have h : Function.Bijective (fun f : {f : ZMod 3 → ZMod 5 // f k = 0} =>
      (⟨shiftPerm f.1, f.1, f.2, rfl⟩ : qPair k)) := by
    constructor
    · intro f f' hff'
      exact Subtype.ext (shiftPerm_injective (congrArg Subtype.val hff'))
    · rintro ⟨_, f, hf, rfl⟩
      exact ⟨⟨f, hf⟩, rfl⟩
  rw [← Nat.card_eq_of_bijective _ h]
  exact card_fun_vanishing k

theorem isElemAbelian_of_forall {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hp : ∀ x ∈ E, x ^ p = 1) : IsElemAbelian p E :=
  ⟨⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩, hp⟩

theorem mul_comm_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (hel : IsElemAbelian p E) : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
  congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem isElemAbelian_qPair (k : ZMod 3) : IsElemAbelian 5 (qPair k) :=
  isElemAbelian_of_forall (fun x hx y hy => mul_comm_of_isElemAbelian isElemAbelian_sylowT
    x (qPair_le_sylowT k hx) y (qPair_le_sylowT k hy))
    (fun x hx => isElemAbelian_sylowT.2 x (qPair_le_sylowT k hx))

theorem blockAlt_commute_qPair {k : ZMod 3} {g h : Perm Pt} (hg : g ∈ blockAlt k)
    (hh : h ∈ qPair k) : g * h = h * g := by
  obtain ⟨f, hf, rfl⟩ := hh
  have hgf := (mem_blockAlt_iff.1 hg).1
  have hg1 := fst_apply_iff_of_fix hgf
  refine Equiv.ext fun p => ?_
  simp only [Perm.mul_apply, shiftPerm_apply]
  by_cases hp : p.1 = k
  · have h1 : (g p).1 = k := (hg1 p).2 hp
    have e1 : (p.1, p.2 + f p.1) = p := by rw [hp, hf]; simp [← hp]
    rw [e1]
    have e2 : ((g p).1, (g p).2 + f (g p).1) = g p := by rw [h1, hf]; simp [← h1]
    rw [e2]
  · rw [hgf p hp]
    have h2 : ((p.1, p.2 + f p.1) : Pt).1 ≠ k := hp
    rw [hgf _ h2]

theorem blockAlt_le_normalizer_qPair (k : ZMod 3) :
    blockAlt k ≤ Subgroup.normalizer (qPair k : Set (Perm Pt)) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg h hh
  rw [blockAlt_commute_qPair hg hh, mul_inv_cancel_right]
  exact hh

theorem mem_normalizer_sylowT_of_conj {g : Perm Pt}
    (h : ∀ f, ∃ f', g * shiftPerm f * g⁻¹ = shiftPerm f')
    (h' : ∀ f, ∃ f', g⁻¹ * shiftPerm f * g = shiftPerm f') :
    g ∈ Subgroup.normalizer (sylowT : Set (Perm Pt)) := by
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  simp only [SetLike.mem_coe, mem_sylowT_iff]
  constructor
  · rintro ⟨f, rfl⟩
    exact h f
  · rintro ⟨f, hf⟩
    obtain ⟨f', hf'⟩ := h' f
    refine ⟨f', ?_⟩
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = g⁻¹ * shiftPerm f * g := by rw [hf]
      _ = shiftPerm f' := hf'

theorem blockShift_inv_conj_shiftPerm (f : ZMod 3 → ZMod 5) :
    blockShift⁻¹ * shiftPerm f * blockShift = shiftPerm (fun i => f (i + 1)) := by
  ext p <;> simp [Perm.inv_def]

theorem blockShift_mem_normalizer : blockShift ∈ Subgroup.normalizer (sylowT : Set (Perm Pt)) :=
  mem_normalizer_sylowT_of_conj (fun f => ⟨_, blockShift_conj_shiftPerm f⟩)
    (fun f => ⟨_, blockShift_inv_conj_shiftPerm f⟩)

@[expose] def mulTwo : Perm Pt where
  toFun p := (p.1, 2 * p.2)
  invFun p := (p.1, 3 * p.2)
  left_inv p := by
    obtain ⟨i, z⟩ := p
    simp only [Prod.mk.injEq, true_and]
    revert z
    decide
  right_inv p := by
    obtain ⟨i, z⟩ := p
    simp only [Prod.mk.injEq, true_and]
    revert z
    decide

@[simp] theorem mulTwo_apply (p : Pt) : mulTwo p = (p.1, 2 * p.2) := rfl

theorem sign_mulTwo : Perm.sign mulTwo = -1 := by
  decide +kernel

theorem mulTwo_conj_shiftPerm (f : ZMod 3 → ZMod 5) :
    mulTwo * shiftPerm f * mulTwo⁻¹ = shiftPerm (fun i => 2 * f i) := by
  have h3 : ∀ z : ZMod 5, 2 * (3 * z) = z := by decide
  ext p
  · simp [Perm.inv_def, mulTwo]
  · simp [Perm.inv_def, mulTwo, mul_add, h3]

theorem mulTwo_inv_conj_shiftPerm (f : ZMod 3 → ZMod 5) :
    mulTwo⁻¹ * shiftPerm f * mulTwo = shiftPerm (fun i => 3 * f i) := by
  have h3 : ∀ z : ZMod 5, 3 * (2 * z) = z := by decide
  ext p
  · simp [Perm.inv_def, mulTwo]
  · simp [Perm.inv_def, mulTwo, mul_add, h3]

theorem mulTwo_mem_normalizer : mulTwo ∈ Subgroup.normalizer (sylowT : Set (Perm Pt)) :=
  mem_normalizer_sylowT_of_conj (fun f => ⟨_, mulTwo_conj_shiftPerm f⟩)
    (fun f => ⟨_, mulTwo_inv_conj_shiftPerm f⟩)

theorem range_inf_normalizer_le {Y : Type} [Group Y] [Finite Y] {φ : Y →* Perm Pt}
    (hφ : Function.Injective φ) {T Y₀ : Subgroup Y} (hT : T.map φ = sylowT)
    (hW : GLBWeakCore 5 T ≤ Y₀) {Q' : Subgroup (Perm Pt)} (hQT : Q' ≤ sylowT)
    (hQ' : IsElemAbelian 5 Q') {m : ℕ} (hm : 2 ≤ m) (hcard : Nat.card Q' = 5 ^ m) :
    φ.range ⊓ Subgroup.normalizer (Q' : Set (Perm Pt)) ≤ Y₀.map φ := by
  have hQr : Q' ≤ φ.range := fun x hx => by
    obtain ⟨t, -, ht⟩ := Subgroup.mem_map.1 (hT ▸ hQT hx)
    exact ⟨t, ht⟩
  set Q : Subgroup Y := Q'.comap φ with hQdef
  have hQmap : Q.map φ = Q' := Subgroup.map_comap_eq_self hQr
  have hQle : Q ≤ T := fun x hx => by
    obtain ⟨t, ht, hte⟩ := Subgroup.mem_map.1 (hT ▸ hQT (show φ x ∈ Q' from hx))
    rw [← hφ hte]
    exact ht
  have hQel : IsElemAbelian 5 Q :=
    isElemAbelian_of_forall (fun x hx y hy => hφ (by
      rw [map_mul, map_mul]
      exact mul_comm_of_isElemAbelian hQ' _ hx _ hy))
      (fun x hx => hφ (by rw [map_pow, hQ'.2 _ hx, map_one]))
  have hQcard : Nat.card Q = 5 ^ m := by
    rw [← hcard, ← hQmap, Subgroup.card_map_of_injective hφ]
  have hTel : IsElemAbelian 5 T :=
    isElemAbelian_of_forall (fun x hx y hy => hφ (by
      rw [map_mul, map_mul]
      exact mul_comm_of_isElemAbelian isElemAbelian_sylowT _ (hT ▸ Subgroup.mem_map_of_mem φ hx)
        _ (hT ▸ Subgroup.mem_map_of_mem φ hy)))
      (fun x hx => hφ (by
        rw [map_pow, isElemAbelian_sylowT.2 _ (hT ▸ Subgroup.mem_map_of_mem φ hx), map_one]))
  have hTcard : Nat.card T = 5 ^ 3 := by
    rw [← card_sylowT, ← hT, Subgroup.card_map_of_injective hφ]
  have h2 : 2 ≤ CFSG.Open.pRank 5 Q :=
    hm.trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl hQel hQcard)
  have hTle : T ≤ Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set Y)) := fun t ht =>
    Subgroup.mem_sup_right ⟨ht, Subgroup.mem_centralizer_iff.2 fun q hq =>
      mul_comm_of_isElemAbelian hTel q (hQle hq) t ht⟩
  have h3 : 3 ≤ CFSG.Open.pRank 5 (Q ⊔ (T ⊓ Subgroup.centralizer (Q : Set Y))) :=
    CFSG.SectionRank.le_pRank (by norm_num) hTle hTel hTcard
  have hN : Subgroup.normalizer (Q : Set Y) ≤ Y₀ := by
    refine le_trans ?_ hW
    exact le_sSup ⟨Q, hQle, h2, h3, rfl⟩
  intro x hx
  obtain ⟨hxr, hxn⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, rfl⟩ := hxr
  refine Subgroup.mem_map.2 ⟨y, hN ?_, rfl⟩
  rw [Subgroup.mem_set_normalizer_iff]
  intro n
  have h1 := (Subgroup.mem_set_normalizer_iff.1 hxn) (φ n)
  simp only [SetLike.mem_coe, hQdef, Subgroup.mem_comap, map_mul, map_inv]
  exact h1

end CFSG.AGLEmbedding.A15Local
