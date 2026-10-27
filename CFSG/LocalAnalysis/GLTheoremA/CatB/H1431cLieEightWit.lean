module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalNoNormal
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1431c

open Matrix CFSG.Open

@[expose] def LieSEightWit27 (G : Type) [Group G] : Prop :=
  ∃ U E : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ IsElemAbelian 3 E ∧ 27 ≤ Nat.card E ∧
    E ≤ Subgroup.normalizer (U : Set G)

theorem LieSEightWit27.of_injective {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (h : LieSEightWit27 G) : LieSEightWit27 H := by
  obtain ⟨U, E, hU1, hU2, hE, hc, hN⟩ := h
  refine ⟨U.map f, E.map f, fun h' => hU1 ((Subgroup.map_eq_bot_iff_of_injective U hf).mp h'),
    hU2.map f, hE.map f, ?_, (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map f)⟩
  rw [Subgroup.card_map_of_injective hf]
  exact hc

namespace LieSEightSp8Wit

abbrev Idx : Type := Fin 4 ⊕ Fin 4

@[expose] def rotM (i : Fin 4) : Matrix Idx Idx (ZMod 2) := Matrix.of fun r c =>
  if r = Sum.inl i then (if c = Sum.inr i then 1 else 0)
  else if r = Sum.inr i then (if c = Sum.inl i ∨ c = Sum.inr i then 1 else 0)
  else (if r = c then 1 else 0)

@[expose] def trM (i : Fin 4) : Matrix Idx Idx (ZMod 2) := Matrix.of fun r c =>
  if r = Sum.inl i then (if c = Sum.inl i ∨ c = Sum.inr i then 1 else 0)
  else (if r = c then 1 else 0)

@[expose] def JJ : Matrix Idx Idx (ZMod 2) := fromBlocks 0 1 (-1) 0

theorem rotM_cube : ∀ i : Fin 4, rotM i * rotM i * rotM i = 1 := by decide +kernel

theorem rotM_symp : ∀ i : Fin 4, (rotM i)ᵀ * JJ * rotM i = JJ := by decide +kernel

theorem trM_sq : ∀ i : Fin 4, trM i * trM i = 1 := by decide +kernel

theorem trM_symp : ∀ i : Fin 4, (trM i)ᵀ * JJ * trM i = JJ := by decide +kernel

theorem rotM_comm : ∀ i j : Fin 4, i ≠ j → rotM i * rotM j = rotM j * rotM i := by
  decide +kernel

theorem rotM_trM_comm : ∀ i j : Fin 4, i ≠ j → rotM i * trM j = trM j * rotM i := by
  decide +kernel

theorem trM_ne_one : trM 3 ≠ 1 := by decide +kernel

theorem rotM_inj : Function.Injective
    (fun t : Fin 3 × Fin 3 × Fin 3 =>
      rotM 0 ^ t.1.val * rotM 1 ^ t.2.1.val * rotM 2 ^ t.2.2.val) := by
  decide +kernel

theorem rotM_cube' (i : Fin 4) : rotM i * (rotM i * rotM i) = 1 :=
  (mul_assoc _ _ _).symm.trans (rotM_cube i)

@[expose] def rotU (i : Fin 4) : GL Idx (ZMod 2) :=
  ⟨rotM i, rotM i * rotM i, rotM_cube' i, rotM_cube i⟩

@[expose] def trU (i : Fin 4) : GL Idx (ZMod 2) :=
  ⟨trM i, trM i, trM_sq i, trM_sq i⟩

@[expose] def rotG (i : Fin 4) : StatedSp 4 (ZMod 2) :=
  ⟨rotU i, CFSG.Open.StatedAPI.mem_statedSp_iff.2 (rotM_symp i)⟩

@[expose] def trG (i : Fin 4) : StatedSp 4 (ZMod 2) :=
  ⟨trU i, CFSG.Open.StatedAPI.mem_statedSp_iff.2 (trM_symp i)⟩

theorem coe_rotG (i : Fin 4) :
    (((rotG i : StatedSp 4 (ZMod 2)) : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) = rotM i :=
  rfl

theorem coe_trG (i : Fin 4) :
    (((trG i : StatedSp 4 (ZMod 2)) : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) = trM i :=
  rfl

theorem coe_pow_val (g : StatedSp 4 (ZMod 2)) (n : ℕ) :
    ((((g ^ n : StatedSp 4 (ZMod 2)) : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2))) =
      ((g : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, pow_succ, Subgroup.coe_mul, Units.val_mul, ih]

theorem coe_mul_val (g h : StatedSp 4 (ZMod 2)) :
    ((((g * h : StatedSp 4 (ZMod 2)) : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2))) =
      ((g : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) *
        ((h : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)) := rfl

theorem rotG_pow_three (i : Fin 4) : rotG i ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_pow_val, coe_rotG]
  show rotM i ^ 3 = 1
  rw [pow_succ, pow_succ, pow_one]
  exact rotM_cube i

theorem trG_sq : trG 3 ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [coe_pow_val, coe_trG]
  show trM 3 ^ 2 = 1
  rw [pow_two]
  exact trM_sq 3

theorem trG_ne_one : trG 3 ≠ 1 := by
  intro h
  apply trM_ne_one
  have h' := congrArg (fun g : StatedSp 4 (ZMod 2) =>
    (((g : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)))) h
  exact h'

theorem rotG_comm {i j : Fin 4} (h : i ≠ j) : Commute (rotG i) (rotG j) := by
  apply Subtype.ext
  apply Units.ext
  show rotM i * rotM j = rotM j * rotM i
  exact rotM_comm i j h

theorem rotG_trG_comm {i : Fin 4} (h : i ≠ 3) : Commute (rotG i) (trG 3) := by
  apply Subtype.ext
  apply Units.ext
  show rotM i * trM 3 = trM 3 * rotM i
  exact rotM_trM_comm i 3 h

@[expose] def «gens» : Set (StatedSp 4 (ZMod 2)) := Set.range fun i : Fin 3 => rotG i.castSucc

@[expose] def E3 : Subgroup (StatedSp 4 (ZMod 2)) := Subgroup.closure «gens»

theorem gens_comm : «gens».Pairwise Commute := by
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hij
  exact rotG_comm fun h => hij (by rw [Fin.castSucc_inj.1 h])

theorem E3_comm : IsMulCommutative E3 := Subgroup.isMulCommutative_closure gens_comm

theorem E3_exp : ∀ x ∈ E3, x ^ 3 = 1 := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact rotG_pow_three _
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hc : Commute x y := by
      have := E3_comm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hc.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

@[expose] def eltG (t : Fin 3 × Fin 3 × Fin 3) : StatedSp 4 (ZMod 2) :=
  rotG 0 ^ t.1.val * rotG 1 ^ t.2.1.val * rotG 2 ^ t.2.2.val

theorem rotG_mem_E3 (i : Fin 3) : rotG i.castSucc ∈ E3 := Subgroup.subset_closure ⟨i, rfl⟩

theorem eltG_mem (t : Fin 3 × Fin 3 × Fin 3) : eltG t ∈ E3 :=
  E3.mul_mem (E3.mul_mem (E3.pow_mem (rotG_mem_E3 0) _) (E3.pow_mem (rotG_mem_E3 1) _))
    (E3.pow_mem (rotG_mem_E3 2) _)

theorem eltG_injective : Function.Injective eltG := by
  intro t t' h
  apply rotM_inj
  have h' := congrArg (fun g : StatedSp 4 (ZMod 2) =>
    (((g : GL Idx (ZMod 2)) : Matrix Idx Idx (ZMod 2)))) h
  simpa only [eltG, coe_mul_val, coe_pow_val, coe_rotG] using h'

theorem card_E3 : 27 ≤ Nat.card E3 := by
  have h : Function.Injective fun t : Fin 3 × Fin 3 × Fin 3 => (⟨eltG t, eltG_mem t⟩ : E3) :=
    fun t t' h' => eltG_injective (congrArg Subtype.val h')
  have := Nat.card_le_card_of_injective _ h
  simpa [Nat.card_prod] using this

theorem E3_le_normalizer :
    E3 ≤ Subgroup.normalizer ((Subgroup.zpowers (trG 3) : Subgroup (StatedSp 4 (ZMod 2))) :
      Set (StatedSp 4 (ZMod 2))) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, rfl⟩
  have hc : ∀ y ∈ Subgroup.zpowers (trG 3), rotG i.castSucc * y = y * rotG i.castSucc := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((rotG_trG_comm (i := i.castSucc) (by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega)).zpow_right k).eq
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [mul_inv_eq_iff_eq_mul.2 (hc h hh)] 
    exact hh
  · intro hh
    have h2 : rotG i.castSucc * (rotG i.castSucc * h * (rotG i.castSucc)⁻¹) =
        (rotG i.castSucc * h * (rotG i.castSucc)⁻¹) * rotG i.castSucc := hc _ hh
    have h3 : h = (rotG i.castSucc)⁻¹ * (rotG i.castSucc * h * (rotG i.castSucc)⁻¹) *
        rotG i.castSucc := by group
    rw [h3]
    have h4 : (rotG i.castSucc)⁻¹ * (rotG i.castSucc * h * (rotG i.castSucc)⁻¹) *
        rotG i.castSucc = rotG i.castSucc * h * (rotG i.castSucc)⁻¹ := by
      rw [mul_assoc, ← h2]
      group
    rw [h4]
    exact hh

end LieSEightSp8Wit

theorem lieSEight_wit27_statedSp_two : LieSEightWit27 (StatedSp 4 (ZMod 2)) := by
  refine ⟨Subgroup.zpowers (LieSEightSp8Wit.trG 3), LieSEightSp8Wit.E3, ?_, ?_,
    ⟨LieSEightSp8Wit.E3_comm, LieSEightSp8Wit.E3_exp⟩, LieSEightSp8Wit.card_E3,
    LieSEightSp8Wit.E3_le_normalizer⟩
  · intro h
    exact LieSEightSp8Wit.trG_ne_one (Subgroup.zpowers_eq_bot.1 h)
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime LieSEightSp8Wit.trG_sq LieSEightSp8Wit.trG_ne_one]
    norm_num

@[expose] def LieSEightWitIn {G : Type} [Group G] (C : Subgroup G) : Prop :=
  ∃ U E : Subgroup G, U ≠ ⊥ ∧ IsPGroup 2 U ∧ IsElemAbelian 3 E ∧ 27 ≤ Nat.card E ∧ U ≤ C ∧
    E ≤ C ∧ E ≤ Subgroup.normalizer (U : Set G)

theorem LieSEightWit27.witIn {G : Type} [Group G] {C : Subgroup G} (h : LieSEightWit27 ↥C) :
    LieSEightWitIn C := by
  obtain ⟨U, E, hU1, hU2, hE, hc, hN⟩ := h
  refine ⟨U.map C.subtype, E.map C.subtype, fun h' => hU1
    ((Subgroup.map_eq_bot_iff_of_injective U C.subtype_injective).mp h'), hU2.map _, hE.map _, ?_,
    Subgroup.map_subtype_le U, Subgroup.map_subtype_le E,
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map C.subtype)⟩
  rw [Subgroup.card_map_of_injective C.subtype_injective]
  exact hc

theorem LieSEightWitIn.map {G H : Type} [Group G] [Group H] {C : Subgroup G} (f : G →* H)
    (hf : Function.Injective f) (h : LieSEightWitIn C) : LieSEightWitIn (C.map f) := by
  obtain ⟨U, E, hU1, hU2, hE, hc, hUC, hEC, hN⟩ := h
  refine ⟨U.map f, E.map f, fun h' => hU1 ((Subgroup.map_eq_bot_iff_of_injective U hf).mp h'),
    hU2.map f, hE.map f, ?_, Subgroup.map_mono hUC, Subgroup.map_mono hEC,
    (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map f)⟩
  rw [Subgroup.card_map_of_injective hf]
  exact hc

@[expose] def lieSEight_spMapHom {k K : Type} [Field k] [Field K] (f : k →+* K) (r : ℕ) :
    StatedSp r k →* StatedSp r K :=
  ((Matrix.GeneralLinearGroup.map f).comp (StatedSp r k).subtype).codRestrict (StatedSp r K)
    fun g => CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_mem_statedSp f g.2

theorem lieSEight_spMapHom_injective {k K : Type} [Field k] [Field K] (f : k →+* K) (r : ℕ) :
    Function.Injective (lieSEight_spMapHom f r) := by
  intro g h hgh
  have h1 := congrArg (fun x : StatedSp r K =>
    (((x : GL (Fin r ⊕ Fin r) K)) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hgh
  exact Subtype.ext (Units.ext (Matrix.map_injective f.injective h1))

theorem lieSEight_wit27_statedSp_of_charP_two (K : Type) [Field K] [CharP K 2] :
    LieSEightWit27 (StatedSp 4 K) :=
  LieSEightWit27.of_injective (lieSEight_spMapHom (ZMod.castHom (dvd_refl 2) K) 4)
    (lieSEight_spMapHom_injective _ 4) lieSEight_wit27_statedSp_two

theorem lieSEight_wit27_statedProj_of_charP_two (K : Type) [Field K] [Finite K] [CharP K 2] :
    LieSEightWit27 (StatedProj (StatedSp 4 K)) := by
  refine LieSEightWit27.of_injective
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 4 K) ?_
    (lieSEight_wit27_statedSp_of_charP_two K)
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 : x ∈ (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 4 K).ker := hx
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj] at h1
  have h2 := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars_le_center h1
  rw [CFSG.HardMathSupport.Dickson.Bal207.center_statedSp_eq_bot_of_charP_two 4] at h2
  exact h2

end CFSG.LocalAnalysis.GLTheoremA.H1431c

end
