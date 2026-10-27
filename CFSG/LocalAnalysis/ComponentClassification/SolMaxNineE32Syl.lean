module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxNineE32Model
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.ComponentClassification.SolMax.NineE32

open Equiv Subgroup

abbrev A9 := ↥(alternatingGroup (Fin 9))

@[expose] def e16 : Subgroup A9 := (A₀.map (MonoidHom.fst _ _))

theorem mem_e16_iff (x : A9) : x ∈ e16 ↔ ∃ v : W, (x : Perm (Fin 9)) = encPerm v := by
  constructor
  · rintro ⟨y, ⟨v, rfl⟩, rfl⟩
    exact ⟨Multiplicative.toAdd v, rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨enc (Multiplicative.ofAdd v), ⟨_, rfl⟩, Subtype.ext hv.symm⟩

theorem encPerm_eq_one_iff : ∀ v : W, encPerm v = 1 ↔ v = 0 ∨ v = tW := by decide

theorem card_e16 : Nat.card e16 = 16 := by
  set f : Multiplicative W →* A9 := (MonoidHom.fst _ _).comp enc with hf
  have hrange : e16 = f.range := by
    rw [MonoidHom.range_comp]
    rfl
  have hker : Nat.card f.ker = 2 := by
    have : (f.ker : Set (Multiplicative W)) =
        {Multiplicative.ofAdd 0, Multiplicative.ofAdd tW} := by
      ext v
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [Subtype.ext_iff]
      show encPerm (Multiplicative.toAdd v) = 1 ↔ _
      rw [encPerm_eq_one_iff]
      constructor
      · rintro (h | h)
        · exact Or.inl (by rw [← h]; rfl)
        · exact Or.inr (by rw [← h]; rfl)
      · rintro (h | h)
        · exact Or.inl (by rw [h]; rfl)
        · exact Or.inr (by rw [h]; rfl)
    rw [← SetLike.coe_sort_coe, this, Nat.card_eq_fintype_card, Set.card_insert, Set.card_singleton]
    · rintro h
      exact absurd (congrArg Multiplicative.toAdd h) (by decide)
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, hker] at h1
  have h2 : Nat.card (Multiplicative W) = 32 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  rw [hrange]
  omega

@[expose] def dP (a b : ZMod 2) : Perm (Fin 9) := pw (xPerm 2) a * pw (xPerm 3) b

theorem dP_mem (a b : ZMod 2) : dP a b ∈ alternatingGroup (Fin 9) :=
  mul_mem (pw_mem (xPerm_mem 2) a) (pw_mem (xPerm_mem 3) b)

theorem dP_add : ∀ a b a' b' : ZMod 2, dP (a + a') (b + b') = dP a b * dP a' b' := by decide

theorem dP_inj : ∀ a b a' b' : ZMod 2, dP a b = dP a' b' → a = a' ∧ b = b' := by decide

@[expose] def dHom : Multiplicative (ZMod 2 × ZMod 2) →* A9 where
  toFun p := ⟨dP (Multiplicative.toAdd p).1 (Multiplicative.toAdd p).2, dP_mem _ _⟩
  map_one' := Subtype.ext (by decide)
  map_mul' p q := Subtype.ext (dP_add _ _ _ _)

@[expose] def dSub : Subgroup A9 := dHom.range

theorem card_dSub : Nat.card dSub = 4 := by
  have hinj : Function.Injective dHom := by
    intro p q h
    have := dP_inj _ _ _ _ (congrArg Subtype.val h)
    exact Multiplicative.toAdd.injective (Prod.ext this.1 this.2)
  have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  show Nat.card dHom.range = 4
  rw [← h, Nat.card_eq_fintype_card]
  rfl

theorem dP_conj (a b : ZMod 2) (v : W) :
    dP a b * encPerm v * (dP a b)⁻¹ =
      encPerm ((if a = 1 then gW 2 else id) ((if b = 1 then gW 3 else id) v)) := by
  have h2 : ∀ v, xPerm 2 * encPerm v * (xPerm 2)⁻¹ = encPerm (gW 2 v) := xPerm_conj 2
  have h3 : ∀ v, xPerm 3 * encPerm v * (xPerm 3)⁻¹ = encPerm (gW 3 v) := xPerm_conj 3
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  have hb : b = 0 ∨ b = 1 := by revert b; decide
  have h01 : ¬ (0 : ZMod 2) = 1 := by decide
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp only [dP, pw, h01, ite_false, ite_true, id, mul_one, one_mul, inv_one]
  · rw [h3]
  · rw [h2]
  · rw [mul_inv_rev, show xPerm 2 * xPerm 3 * encPerm v * ((xPerm 3)⁻¹ * (xPerm 2)⁻¹) =
      xPerm 2 * (xPerm 3 * encPerm v * (xPerm 3)⁻¹) * (xPerm 2)⁻¹ by group, h3, h2]

theorem dSub_le_normalizer : dSub ≤ normalizer (e16 : Set A9) := by
  have hfwd : ∀ y ∈ dSub, ∀ h ∈ e16, y * h * y⁻¹ ∈ e16 := by
    rintro _ ⟨p, rfl⟩ h hh
    obtain ⟨v, hv⟩ := (mem_e16_iff h).mp hh
    refine (mem_e16_iff _).mpr ⟨(if (Multiplicative.toAdd p).1 = 1 then gW 2 else id)
      ((if (Multiplicative.toAdd p).2 = 1 then gW 3 else id) v), ?_⟩
    show dP _ _ * (h : Perm (Fin 9)) * (dP _ _)⁻¹ = _
    rw [hv, dP_conj]
  intro y hy
  rw [mem_normalizer_iff]
  intro h
  refine ⟨hfwd y hy h, fun hh => ?_⟩
  have := hfwd y⁻¹ (inv_mem hy) _ hh
  simpa [mul_assoc] using this

theorem dP_eq_encPerm : ∀ (a b : ZMod 2) (v : W), dP a b = encPerm v → a = 0 ∧ b = 0 := by
  decide

theorem e16_inf_dSub : e16 ⊓ dSub = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx1, ⟨p, rfl⟩⟩
  obtain ⟨v, hv⟩ := (mem_e16_iff _).mp hx1
  obtain ⟨ha, hb⟩ := dP_eq_encPerm _ _ _ hv
  rw [mem_bot]
  refine Subtype.ext ?_
  show dP _ _ = 1
  rw [ha, hb]
  decide

@[expose] def S₀ : Subgroup A9 := dSub ⊔ e16

private theorem card_sup_mul_card_inf_normal' {G : Type*} [Group G] (A B : Subgroup G)
    [B.Normal] :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have h1 := relIndex_mul_card (H := B) (K := A ⊔ B)
  have h2 := relIndex_mul_card (H := B) (K := A)
  rw [relIndex_sup_right, inf_of_le_left (le_sup_right : B ≤ A ⊔ B)] at h1
  rw [inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem card_sup_mul_card_inf_normalizer' {A B : Subgroup A9}
    (hB : B ≤ normalizer (A : Set A9)) :
    Nat.card (A ⊔ B : Subgroup A9) * Nat.card (A ⊓ B : Subgroup A9) = Nat.card A * Nat.card B := by
  set N := normalizer (A : Set A9)
  have hAN : A ≤ N := le_normalizer
  have : (A.subgroupOf N).Normal := normal_in_normalizer
  have h := card_sup_mul_card_inf_normal' (B.subgroupOf N) (A.subgroupOf N)
  have hc : ∀ X : Subgroup A9, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X := fun X hX =>
    Nat.card_congr (subgroupOfEquivOfLe hX).toEquiv
  have hsup : B.subgroupOf N ⊔ A.subgroupOf N = (A ⊔ B).subgroupOf N := by
    rw [sup_comm]
    exact (subgroupOf_sup hAN hB).symm
  have hinf : B.subgroupOf N ⊓ A.subgroupOf N = (A ⊓ B).subgroupOf N := by
    rw [inf_comm]
    exact Subgroup.ext fun _ => Iff.rfl
  rw [hsup, hinf, hc _ (sup_le hAN hB), hc _ (inf_le_left.trans hAN), hc A hAN, hc B hB] at h
  rw [h, mul_comm]

theorem card_S₀ : Nat.card S₀ = 64 := by
  have h := card_sup_mul_card_inf_normalizer' dSub_le_normalizer
  rw [e16_inf_dSub, card_bot, mul_one, card_e16, card_dSub, sup_comm] at h
  exact h

theorem mem_S₀ {x : A9} (hx : x ∈ S₀) :
    ∃ (a b : ZMod 2) (v : W), v.2.2.2.2 = 0 ∧ (x : Perm (Fin 9)) = dP a b * encPerm v := by
  have hx' : x ∈ (↑(dSub ⊔ e16) : Set A9) := hx
  rw [coe_mul_of_left_le_normalizer_right dSub e16 dSub_le_normalizer] at hx'
  obtain ⟨_, ⟨p, rfl⟩, e, he, rfl⟩ := hx'
  obtain ⟨v, hv⟩ := (mem_e16_iff e).mp he
  refine ⟨(Multiplicative.toAdd p).1, (Multiplicative.toAdd p).2,
    (v.1, v.2.1, v.2.2.1, v.2.2.2.1, 0), rfl, ?_⟩
  show dP _ _ * (e : Perm (Fin 9)) = _
  rw [hv]
  rfl

theorem twelve : ∀ (a b : ZMod 2) (v : W), v.2.2.2.2 = 0 → (a, b) ≠ (0, 0) →
    dP a b * encPerm v * (dP a b * encPerm v) = 1 →
    (Finset.univ.filter fun p : ZMod 2 × ZMod 2 × W => p.2.2.2.2.2.2 = 0 ∧
      dP p.1 p.2.1 * encPerm p.2.2 * (dP p.1 p.2.1 * encPerm p.2.2) = 1 ∧
      dP a b * encPerm v * (dP p.1 p.2.1 * encPerm p.2.2) =
        dP p.1 p.2.1 * encPerm p.2.2 * (dP a b * encPerm v)).card ≤ 12 := by
  decide +kernel

theorem eq_e16_of_le_S₀ {B : Subgroup A9} (hB : B ≤ S₀) (h2 : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 16) : B = e16 := by
  classical
  by_cases hle : B ≤ e16
  · exact eq_of_le_of_card_ge hle (by rw [hcard, card_e16])
  exfalso
  obtain ⟨x, hxB, hxe⟩ : ∃ x ∈ B, x ∉ e16 := by
    by_contra hcon
    push Not at hcon
    exact hle fun x hx => hcon x hx
  obtain ⟨a, b, v, hv4, hxv⟩ := mem_S₀ (hB hxB)
  have hab : (a, b) ≠ (0, 0) := by
    intro hab
    obtain ⟨rfl, rfl⟩ := Prod.ext_iff.mp hab
    exact hxe ((mem_e16_iff x).mpr ⟨v, by rw [hxv]; simp [dP, pw]⟩)
  have hx2 : dP a b * encPerm v * (dP a b * encPerm v) = 1 := by
    rw [← hxv]
    exact congrArg Subtype.val (h2 x hxB)
  set T := Finset.univ.filter fun p : ZMod 2 × ZMod 2 × W => p.2.2.2.2.2.2 = 0 ∧
      dP p.1 p.2.1 * encPerm p.2.2 * (dP p.1 p.2.1 * encPerm p.2.2) = 1 ∧
      dP a b * encPerm v * (dP p.1 p.2.1 * encPerm p.2.2) =
        dP p.1 p.2.1 * encPerm p.2.2 * (dP a b * encPerm v) with hT
  have hT12 : T.card ≤ 12 := twelve a b v hv4 hab hx2
  have hcomm : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := by
    intro y hy y' hy'
    have h1 := h2 _ (mul_mem hy hy')
    have hy1 := h2 y hy
    have hy1' := h2 y' hy'
    calc y * y' = y * y' * (y' * y * (y' * y)) := by rw [h2 _ (mul_mem hy' hy), mul_one]
      _ = y' * y := by
        rw [show y * y' * (y' * y * (y' * y)) = y * (y' * y') * y * (y' * y) by group, hy1',
          mul_one, hy1, one_mul]
  have hsub : ∀ y : B, ((y : A9) : Perm (Fin 9)) ∈ T.image
      (fun p : ZMod 2 × ZMod 2 × W => dP p.1 p.2.1 * encPerm p.2.2) := by
    intro y
    obtain ⟨a', b', v', hv4', hyv⟩ := mem_S₀ (hB y.2)
    refine Finset.mem_image.mpr ⟨(a', b', v'), ?_, hyv.symm⟩
    rw [hT, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hv4', ?_, ?_⟩
    · rw [← hyv]
      exact congrArg Subtype.val (h2 y y.2)
    · rw [← hyv, ← hxv]
      exact congrArg Subtype.val (hcomm x hxB y y.2)
  have hle' : Nat.card B ≤ (T.image fun p : ZMod 2 × ZMod 2 × W =>
      dP p.1 p.2.1 * encPerm p.2.2).card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_le_card_of_injective (fun y => ⟨((y : A9) : Perm (Fin 9)), hsub y⟩)
      (fun y y' h => by
        have h' := congrArg Subtype.val h
        simp only at h'
        exact Subtype.ext (Subtype.ext h'))
  have := (hle'.trans Finset.card_image_le).trans hT12
  omega

theorem card_A9 : Nat.card A9 = 2 ^ 6 * 2835 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

theorem factorization_card_A9 : (Nat.card A9).factorization 2 = 6 := by
  rw [card_A9, Nat.factorization_mul (by decide) (by decide), Finsupp.add_apply,
    Nat.factorization_pow_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by decide : ¬2 ∣ 2835)]

theorem exists_conj_e16 {B : Subgroup A9} (h2 : ∀ x ∈ B, x * x = 1) (hcard : Nat.card B = 16) :
    ∃ c : A9, B.map (MulAut.conj c).toMonoidHom = e16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hB2 : IsPGroup 2 B := IsPGroup.of_card (n := 4) (by rw [hcard]; norm_num)
  have hS : Nat.card S₀ = 2 ^ (Nat.card A9).factorization 2 := by
    rw [card_S₀, factorization_card_A9]
    norm_num
  obtain ⟨P, hP⟩ := hB2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq A9 (Sylow.ofCard S₀ hS) P
  refine ⟨g⁻¹, eq_e16_of_le_S₀ ?_ ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hyP : y ∈ (P : Subgroup A9) := hP hy
    rw [← hg, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hyP
    simpa [MulAut.smul_def, MulAut.conj_apply] using hyP
  · rintro _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (y * y) * g⁻¹⁻¹ by group, h2 y hy]
    group
  · rw [← hcard]
    exact Nat.card_congr ((MulAut.conj g⁻¹).subgroupMap B).toEquiv.symm

theorem exists_conj_A₀ {B : Subgroup (A9 × Multiplicative (ZMod 2))} (h2 : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 32) (hz : ((1 : A9), Multiplicative.ofAdd (1 : ZMod 2)) ∈ B) :
    ∃ c : A9 × Multiplicative (ZMod 2), B.map (MulAut.conj c).toMonoidHom = A₀ := by
  classical
  set f : B →* A9 := (MonoidHom.fst _ _).comp B.subtype with hf
  have hker : Nat.card f.ker = 2 := by
    have hkerset : (f.ker : Set B) = {1, ⟨_, hz⟩} := by
      ext y
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · intro hy
        have hy1 : (y : A9 × Multiplicative (ZMod 2)).1 = 1 := hy
        have hy2 : (y : A9 × Multiplicative (ZMod 2)).2 = 1 ∨
            (y : A9 × Multiplicative (ZMod 2)).2 = Multiplicative.ofAdd 1 := by
          generalize (y : A9 × Multiplicative (ZMod 2)).2 = c
          revert c
          decide
        rcases hy2 with hy2 | hy2
        · exact Or.inl (Subtype.ext (Prod.ext hy1 hy2))
        · exact Or.inr (Subtype.ext (Prod.ext hy1 hy2))
      · rintro (rfl | rfl)
        · exact map_one f
        · rfl
    rw [← SetLike.coe_sort_coe, hkerset, Nat.card_eq_fintype_card, Set.card_insert,
      Set.card_singleton]
    rintro h
    have h' := congrArg (fun y : B => Multiplicative.toAdd (y : A9 × Multiplicative (ZMod 2)).2) h
    simp at h'
  have hrange : Nat.card f.range = 16 := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hker, hcard] at h1
    omega
  obtain ⟨c₁, hc₁⟩ := exists_conj_e16 (B := f.range)
    (by rintro _ ⟨y, rfl⟩; exact congrArg Prod.fst (h2 y y.2)) hrange
  refine ⟨(c₁, 1), eq_of_le_of_card_ge ?_ ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    have hmem : MulAut.conj c₁ y.1 ∈ e16 := by
      rw [← hc₁]
      exact ⟨y.1, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
    obtain ⟨v, hv⟩ := (mem_e16_iff _).mp hmem
    refine ⟨Multiplicative.ofAdd (v.1, v.2.1, v.2.2.1, v.2.2.2.1, Multiplicative.toAdd y.2), ?_⟩
    refine Prod.ext (Subtype.ext ?_) ?_
    · rw [enc_apply_fst]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Prod.fst_mul, Prod.fst_inv]
      exact hv.symm
    · rw [enc_apply_snd]
      simp [MulAut.conj_apply]
  · rw [card_A₀, ← hcard]
    exact le_of_eq (Nat.card_congr ((MulAut.conj (c₁, (1 : Multiplicative (ZMod 2)))).subgroupMap
      B).toEquiv)

end CFSG.ComponentClassification.SolMax.NineE32
