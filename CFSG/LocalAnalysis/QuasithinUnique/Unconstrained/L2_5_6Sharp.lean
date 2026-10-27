module

public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.M11Order

public section

namespace CFSG.QuasithinUnique.Unc25G2

open Equiv CFSG.Sporadic.Bridge

theorem m11_stab_card_le :
    Nat.card ↥CFSG.Sporadic.Bridge.M11.stab1 ≤ 720 ∧ Nat.card ↥CFSG.Sporadic.Bridge.M11.stab2 ≤ 72 ∧
      Nat.card ↥CFSG.Sporadic.Bridge.M11.stab3 ≤ 8 ∧
      Nat.card ↥CFSG.Sporadic.Bridge.M11.stab4 ≤ 1 := by
  have h0 := le_card_of_witnesses (K := CFSG.Blueprint.NativeSporadic.M11)
    CFSG.Sporadic.Bridge.M11.gen 0 CFSG.Sporadic.Bridge.M11.witnesses0
    (fun x _ => CFSG.Sporadic.Bridge.M11.nativeWord_mem x.2)
    (fun x hx => CFSG.Sporadic.Bridge.M11.witnesses_ok0 x hx)
    CFSG.Sporadic.Bridge.M11.witnesses_nodup.1
  have h1 := le_card_of_witnesses (K := CFSG.Sporadic.Bridge.M11.stab1)
    CFSG.Sporadic.Bridge.M11.gen 1 CFSG.Sporadic.Bridge.M11.witnesses1
    (fun x hx => ⟨CFSG.Sporadic.Bridge.M11.nativeWord_mem x.2,
      mem_stabilizer_iff_apply.mpr (CFSG.Sporadic.Bridge.M11.witnesses_ok1 x hx).1⟩)
    (fun x hx => (CFSG.Sporadic.Bridge.M11.witnesses_ok1 x hx).2)
    CFSG.Sporadic.Bridge.M11.witnesses_nodup.2.1
  have h2 := le_card_of_witnesses (K := CFSG.Sporadic.Bridge.M11.stab2)
    CFSG.Sporadic.Bridge.M11.gen 2 CFSG.Sporadic.Bridge.M11.witnesses2
    (fun x hx => ⟨⟨CFSG.Sporadic.Bridge.M11.nativeWord_mem x.2,
      mem_stabilizer_iff_apply.mpr (CFSG.Sporadic.Bridge.M11.witnesses_ok2 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (CFSG.Sporadic.Bridge.M11.witnesses_ok2 x hx).2.1⟩)
    (fun x hx => (CFSG.Sporadic.Bridge.M11.witnesses_ok2 x hx).2.2)
    CFSG.Sporadic.Bridge.M11.witnesses_nodup.2.2.1
  have h3 := le_card_of_witnesses (K := CFSG.Sporadic.Bridge.M11.stab3)
    CFSG.Sporadic.Bridge.M11.gen 3 CFSG.Sporadic.Bridge.M11.witnesses3
    (fun x hx => ⟨⟨⟨CFSG.Sporadic.Bridge.M11.nativeWord_mem x.2,
      mem_stabilizer_iff_apply.mpr (CFSG.Sporadic.Bridge.M11.witnesses_ok3 x hx).1⟩,
      mem_stabilizer_iff_apply.mpr (CFSG.Sporadic.Bridge.M11.witnesses_ok3 x hx).2.1⟩,
      mem_stabilizer_iff_apply.mpr (CFSG.Sporadic.Bridge.M11.witnesses_ok3 x hx).2.2.1⟩)
    (fun x hx => (CFSG.Sporadic.Bridge.M11.witnesses_ok3 x hx).2.2.2)
    CFSG.Sporadic.Bridge.M11.witnesses_nodup.2.2.2
  obtain ⟨l0, l1, l2, l3⟩ := CFSG.Sporadic.Bridge.M11.witnesses_length
  rw [l0] at h0
  rw [l1] at h1
  rw [l2] at h2
  rw [l3] at h3
  have hM : Nat.card CFSG.Blueprint.NativeSporadic.M11 = 7920 :=
    CFSG.Semidihedral.GL2Recognition.card_nativeM11
  change 11 * Nat.card ↥CFSG.Sporadic.Bridge.M11.stab1 ≤
    Nat.card ↥CFSG.Blueprint.NativeSporadic.M11 at h0
  change 10 * Nat.card ↥CFSG.Sporadic.Bridge.M11.stab2 ≤
    Nat.card ↥CFSG.Sporadic.Bridge.M11.stab1 at h1
  change 9 * Nat.card ↥CFSG.Sporadic.Bridge.M11.stab3 ≤
    Nat.card ↥CFSG.Sporadic.Bridge.M11.stab2 at h2
  change 8 * Nat.card ↥CFSG.Sporadic.Bridge.M11.stab4 ≤
    Nat.card ↥CFSG.Sporadic.Bridge.M11.stab3 at h3
  omega

theorem m11_stab4_eq_bot : CFSG.Sporadic.Bridge.M11.stab4 = ⊥ :=
  Subgroup.eq_bot_of_card_le _ m11_stab_card_le.2.2.2

theorem perm_inv_apply_self (f : Perm (Fin 11)) (x : Fin 11) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem m11_eq_one_of_fix_base
    {g : Perm (Fin 11)} (hg : g ∈ CFSG.Blueprint.NativeSporadic.M11)
    (h0 : g 0 = 0) (h1 : g 1 = 1) (h2 : g 2 = 2) (h3 : g 3 = 3) : g = 1 := by
  have hmem : g ∈ CFSG.Sporadic.Bridge.M11.stab4 :=
    ⟨⟨⟨⟨hg, mem_stabilizer_iff_apply.mpr h0⟩, mem_stabilizer_iff_apply.mpr h1⟩,
      mem_stabilizer_iff_apply.mpr h2⟩, mem_stabilizer_iff_apply.mpr h3⟩
  rw [m11_stab4_eq_bot] at hmem
  exact Subgroup.mem_bot.mp hmem

@[expose] def baseEmb : Fin 4 ↪ Fin 11 := Fin.castLEEmb (by norm_num)

@[expose] def baseMap (g : ↥CFSG.Blueprint.NativeSporadic.M11) : Fin 4 ↪ Fin 11 :=
  baseEmb.trans (g : Perm (Fin 11)).toEmbedding

theorem baseMap_apply (g : ↥CFSG.Blueprint.NativeSporadic.M11) (i : Fin 4) :
    baseMap g i = (g : Perm (Fin 11)) (baseEmb i) := rfl

theorem baseMap_injective : Function.Injective baseMap := by
  intro g g' h
  have hk : ∀ i : Fin 4, (g : Perm (Fin 11)) (baseEmb i) = (g' : Perm (Fin 11)) (baseEmb i) :=
    fun i => by simpa only [baseMap_apply] using DFunLike.congr_fun h i
  have hfix : ∀ i : Fin 4,
      ((g'⁻¹ * g : ↥CFSG.Blueprint.NativeSporadic.M11) : Perm (Fin 11)) (baseEmb i) =
        baseEmb i := by
    intro i
    show (g' : Perm (Fin 11))⁻¹ ((g : Perm (Fin 11)) (baseEmb i)) = baseEmb i
    rw [hk i, perm_inv_apply_self]
  have key := m11_eq_one_of_fix_base (g'⁻¹ * g).2 (hfix 0) (hfix 1) (hfix 2) (hfix 3)
  have h1 : g'⁻¹ * g = 1 := Subtype.ext key
  exact (inv_mul_eq_one.mp h1).symm

theorem card_fin4_embedding : Nat.card (Fin 4 ↪ Fin 11) = 7920 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_embedding_eq]
  simp only [Fintype.card_fin]
  decide

theorem baseMap_bijective : Function.Bijective baseMap := by
  refine baseMap_injective.bijective_of_nat_card_le ?_
  rw [card_fin4_embedding, CFSG.Semidihedral.GL2Recognition.card_nativeM11]

theorem m11_exists_images (p : Fin 4 ↪ Fin 11) :
    ∃ g : ↥CFSG.Blueprint.NativeSporadic.M11, ∀ i, (g : Perm (Fin 11)) (baseEmb i) = p i := by
  obtain ⟨g, hg⟩ := baseMap_bijective.2 p
  exact ⟨g, fun i => by simpa only [baseMap_apply] using DFunLike.congr_fun hg i⟩

theorem m11_fix_eq_one
    (g : ↥CFSG.Blueprint.NativeSporadic.M11) {a b c d : Fin 11}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (ha : (g : Perm (Fin 11)) a = a) (hb : (g : Perm (Fin 11)) b = b)
    (hc : (g : Perm (Fin 11)) c = c) (hd : (g : Perm (Fin 11)) d = d) : g = 1 := by
  let p : Fin 4 ↪ Fin 11 := ⟨![a, b, c, d], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨h, hh⟩ := m11_exists_images p
  have e2 : ∀ i : Fin 4, (g : Perm (Fin 11)) (p i) = p i := by
    intro i
    fin_cases i
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hfix : ∀ i : Fin 4,
      ((h⁻¹ * g * h : ↥CFSG.Blueprint.NativeSporadic.M11) : Perm (Fin 11)) (baseEmb i) =
        baseEmb i := by
    intro i
    have e1 : (h : Perm (Fin 11)) (baseEmb i) = p i := hh i
    show (h : Perm (Fin 11))⁻¹ ((g : Perm (Fin 11)) ((h : Perm (Fin 11)) (baseEmb i))) =
      baseEmb i
    rw [e1, e2 i, ← e1, perm_inv_apply_self]
  have key := m11_eq_one_of_fix_base (h⁻¹ * g * h).2 (hfix 0) (hfix 1) (hfix 2) (hfix 3)
  have h1 : h⁻¹ * g * h = 1 := Subtype.ext key
  have h2 : g = h * 1 * h⁻¹ := by
    rw [← h1]
    group
  rw [h2]
  group

theorem m11_trans (x y : Fin 11) :
    ∃ g : ↥CFSG.Blueprint.NativeSporadic.M11, (g : Perm (Fin 11)) x = y := by
  have hinj : ∀ z : Fin 11, Function.Injective ![z, z + 1, z + 2, z + 3] := by decide
  obtain ⟨g₁, h₁⟩ := m11_exists_images ⟨![x, x + 1, x + 2, x + 3], hinj x⟩
  obtain ⟨g₂, h₂⟩ := m11_exists_images ⟨![y, y + 1, y + 2, y + 3], hinj y⟩
  have e1 : (g₁ : Perm (Fin 11)) 0 = x := h₁ 0
  have e2 : (g₂ : Perm (Fin 11)) 0 = y := h₂ 0
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  show (g₂ : Perm (Fin 11)) ((g₁ : Perm (Fin 11))⁻¹ x) = y
  rw [← e1, perm_inv_apply_self, e2]

end CFSG.QuasithinUnique.Unc25G2
