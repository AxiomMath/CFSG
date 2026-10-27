module

public import CFSG.Certificates.Kernel.KDense.SepMat
public import CFSG.Certificates.Kernel.KDense.Glue

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.KC.KDense

namespace SepAux

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.Benes CFSG.KC.KDense.InitAux
  CFSG.KC.KDense.P15 CFSG.KC.KDense.SortAux CFSG.Monster.AxisCount CFSG.Monster.B.Rep4371
  CFSG.YGroups.Y443Native

@[expose] noncomputable def sStep (QS : ℕ → ℕ) (NS : ℕ) : ℕ → ℕ × ℕ → ℕ × ℕ :=
  fun j ih => Prod.rec (motive := fun _ => Nat × Nat) (fun lt eq =>
    (fun d => lexStep lt eq d (Nat.land (Nat.shiftRight d (nat_lit 1)) (repP SX (nat_lit 3) (ones (Nat.sub SX 1)))))
      (dig5 (netP SX (nat_lit 17) (nat_lit 4) NS (QS (Nat.sub (nat_lit 14) j))))) ih

@[expose] noncomputable def sST (QS : ℕ → ℕ) (NS j : ℕ) : ℕ × ℕ :=
  Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, ones SX) (sStep QS NS) j

theorem sST_succ (QS : ℕ → ℕ) (NS j : ℕ) : sST QS NS (j + 1) = sStep QS NS j (sST QS NS j) := rfl

theorem sortOK_eq (QS : ℕ → ℕ) (NS : ℕ) : sortOK QS NS =
    andB (netOK (nat_lit 17) NS) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 1) NS validX)
      (ones (nat_lit 98280)))
    (Prod.rec (motive := fun _ => Bool)
      (fun lt _ => Nat.beq (Nat.land lt (ones (nat_lit 98279))) (ones (nat_lit 98279)))
      (sST QS NS (nat_lit 14)))) :=
  rfl

theorem sortOK_eq' (QS : ℕ → ℕ) (NS : ℕ) : sortOK QS NS =
    andB (netOK (nat_lit 17) NS) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 1) NS validX)
      (ones (nat_lit 98280)))
    (Nat.beq (Nat.land (sST QS NS 14).1 (ones (nat_lit 98279))) (ones (nat_lit 98279)))) := by
  have e : ∀ (f : ℕ → ℕ → Bool) (s : ℕ × ℕ), Prod.rec (motive := fun _ => Bool) f s = f s.1 s.2 :=
    fun f s => by cases s; rfl
  rw [sortOK_eq]

@[expose] noncomputable def sD (QS : ℕ → ℕ) (NS j r : ℕ) : ℕ :=
  dig3 SX (dig5 (netP SX (nat_lit 17) (nat_lit 4) NS (QS (Nat.sub (nat_lit 14) j)))) r

theorem sStep_bits (QS : ℕ → ℕ) (NS j : ℕ) (s : ℕ × ℕ) {r : ℕ} (hr : r < SX - 1) :
    (sStep QS NS j s).1.testBit r =
        (s.1.testBit r || (s.2.testBit r && decide (sD QS NS j r < sD QS NS j (r + 1)))) ∧
      (sStep QS NS j s).2.testBit r = (s.2.testBit r && decide (sD QS NS j r = sD QS NS j (r + 1))) := by
  obtain ⟨lt, eq⟩ := s
  unfold sStep sD
  dsimp only
  generalize dig5 (netP SX (nat_lit 17) (nat_lit 4) NS (QS (Nat.sub (nat_lit 14) j))) = d
  refine lexStep_bits (r := r) (by omega) fun b hb => ?_
  have hrep := rep_repP (S := SX) (m := ones (Nat.sub SX 1)) (fun p hp => by
    rw [SortAux.testBit_ones] at hp
    have := of_decide_eq_true hp
    change p < SX - 1 at this
    omega) 3
  rw [testBit_plane (S := SX) (p := r) (by omega), nland, nshr, Nat.testBit_and, Nat.testBit_shiftRight, hrep,
    SortAux.testBit_ones]
  have hS : SX = 131072 := rfl
  have e1 : (b * SX + r) % SX = r := by rw [hS] at hr ⊢; omega
  rw [e1, decide_eq_true (by rw [hS] at hr ⊢; omega), decide_eq_true (by exact hr), Bool.true_and,
    Bool.and_true]
  congr 1
  omega

theorem dg_netP {NS x r : ℕ} (hN : netOK 17 NS = true) (hr : r < SX) :
    dg SX (netP SX 17 4 NS x) r = dg SX x (benesPerm 17 NS r) := by
  have h := (testBit_netP (n := 4) SX_pow hN x).1
  unfold dg
  have h0 := h 0 (by decide) r hr
  have h1 := h 1 (by decide) r hr
  have h2 := h 2 (by decide) r hr
  have h3 := h 3 (by decide) r hr
  rw [Nat.mul_zero, Nat.zero_add, Nat.zero_add] at h0
  rw [Nat.mul_one] at h1
  rw [Nat.mul_comm SX 2] at h2
  rw [Nat.mul_comm SX 3] at h3
  rw [h0, h1, h2, h3]

theorem mod5_eq {x y : ℕ} {X Y : ℤ} (hx : (x : ZMod 15) = (X : ZMod 15))
    (hy : (y : ZMod 15) = (Y : ZMod 15)) (h5 : (5 : ℤ) ∣ X - Y) : x % 15 % 5 = y % 15 % 5 := by
  have hx' : ((x : ℤ) : ZMod 15) = (X : ZMod 15) := by exact_mod_cast hx
  have hy' : ((y : ℤ) : ZMod 15) = (Y : ZMod 15) := by exact_mod_cast hy
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hx' hy'
  obtain ⟨a, ha⟩ := hx'
  obtain ⟨b, hb⟩ := hy'
  obtain ⟨c, hc⟩ := h5
  push_cast at ha hb
  omega

@[expose] def Zv (tab : Array ℤ) (k q : ℕ) : ℤ :=
  ∑ i : Fin 24, ∑ j : Fin 24, apow tab k i j * ((shortVecN q)[(i : ℕ)]! * (shortVecN q)[(j : ℕ)]!)

theorem Zv_range (tab : Array ℤ) (k q : ℕ) : Zv tab k q =
    ∑ l ∈ Finset.range 24, ∑ m ∈ Finset.range 24,
      apow tab k l m * ((shortVecN q)[l]! * (shortVecN q)[m]!) := by
  unfold Zv
  rw [Fin.sum_univ_eq_sum_range (fun l => ∑ j : Fin 24,
    apow tab k l j * ((shortVecN q)[l]! * (shortVecN q)[(j : ℕ)]!))]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun m => apow tab k l m * ((shortVecN q)[l]! * (shortVecN q)[m]!))]

theorem dg_QS {tab : Array ℤ} {OCT UT U MK : ℕ} {QS : ℕ → ℕ}
    (h1 : octOK OCT = true) (h2 : utOK OCT UT = true) (h3 : uPlanesOK UT U = true)
    (h4 : mkOK tab MK = true) {k : ℕ} (hk : k ≤ 14) (h5 : qOK U MK k (QS k) = true) {q : ℕ}
    (hq : q < 98280) : (dg SX (QS k) (xposK q) : ZMod 15) = (Zv tab k q : ZMod 15) := by
  have hp := xposK_lt' hq
  rw [← resP_dg, resP_congr hp (Nat.eq_of_beq_eq_true h5), (resP_qVec U MK k hp).2, Zv_range]
  push_cast
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' := Finset.mem_range.1 hl
  rw [resP_uVec h1 h2 h3 hq hl', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' := Finset.mem_range.1 hm
  rw [resP_uVec h1 h2 h3 hq hm', mEnt_pow h4 k hk l hl' m hm']
  ring

theorem interpA_pow (tab : Array ℤ) : ∀ k (i j : Fin 24),
    ((interpA (ofATab tab) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) i j = (apow tab k i j : ℚ)
  | 0, i, j => by
    rw [pow_zero, Matrix.one_apply, apow]
    by_cases h : i = j
    · rw [ite_eq_left h, ite_eq_left (congrArg Fin.val h)]
      simp
    · rw [ite_eq_right h, ite_eq_right (fun e => h (Fin.ext e))]
      simp
  | k + 1, i, j => by
    rw [pow_succ, Matrix.mul_apply, apow]
    push_cast
    rw [← Fin.sum_univ_eq_sum_range (fun m => (apow tab k i m : ℚ) * ((tab[Native.aIdx m j]! : ℤ) : ℚ))]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [interpA_pow tab k i m]
    congr 1
    change ((ofATab tab).D.getD (Native.aIdx m j) 0 : ℚ) / 2 ^ (ofATab tab).e = _
    have ha := aIdx_lt m m.2 j j.2
    unfold ofATab
    simp only []
    rw [Native.getD_ofFn _ _ (by omega), ite_eq_left ha, pow_zero, div_one]

theorem qf_pow (tab : Array ℤ) (k : ℕ)
    (c : CFSG.Monster.Griess.ShortIdx) :
    CFSG.Monster.Griess.qf c ((interpA (ofATab tab) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) = (Zv tab k (posOf c) : ℚ) := by
  rw [← shortOf_posOf c, CFSG.YGroups.Y443.qf_shortOf, posOf_shortOf]
  unfold Zv
  push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [interpA_pow]

end SepAux

open CFSG.Monster CFSG.Monster.Griess CFSG.Monster.Griess.ModFive CFSG.Monster.AxisCount
open SepAux SortAux CFSG.KC.Benes CFSG.KC.MonsterConv.Perm P15 InitAux

theorem sep_sound (tab : Array Int) (OCT UT U MK NS : Nat)
    (QS : Nat → Nat)
    (h1 : octOK OCT = true) (h2 : utOK OCT UT = true)
    (h3 : uPlanesOK UT U = true) (h4 : mkOK tab MK = true)
    (h5 : ∀ k ∈ Finset.Icc 1 14, qOK U MK k (QS k) = true) (h6 : sortOK QS NS = true) :
    ∀ c d : ShortIdx, (∀ k ∈ Finset.Icc 1 14,
      qf c ((interpA (ofATab tab) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) -
        qf d ((interpA (ofATab tab) : Matrix (Fin 24) (Fin 24) ℚ) ^ k) ∈ D5) → c = d := by
  intro c d hcd
  rw [sortOK_eq'] at h6
  obtain ⟨hN, h6'⟩ := andB_true' h6
  obtain ⟨hV, hL⟩ := andB_true' h6'
  have hV' := Nat.eq_of_beq_eq_true hV
  have hL' := Nat.eq_of_beq_eq_true hL
  have hlex := lex_inv (M := SX - 1) (B := 8) (N := 14) (sD QS NS)
    (fun j _ r => dig3_lt _ _ _) (sST QS NS)
    (fun r hr => by
      refine ⟨Nat.zero_testBit r, ?_⟩
      change (ones SX).testBit r = true
      rw [SortAux.testBit_ones, decide_eq_true (by omega)])
    (fun j hj r hr => by
      rw [sST_succ]
      exact sStep_bits QS NS j _ hr) 14 le_rfl
  have hinc : ∀ r, r + 1 < 98280 → lexV (sD QS NS) 8 14 r < lexV (sD QS NS) 8 14 (r + 1) := by
    intro r hr
    have h1' := (hlex r (by rw [SX_eq]; omega)).1
    have h2' : (Nat.land (sST QS NS 14).1 (ones 98279)).testBit r = (ones 98279).testBit r := by
      rw [hL']
    rw [nland, Nat.testBit_and, SortAux.testBit_ones, decide_eq_true (by omega : r < 98279),
      Bool.and_true, h1'] at h2'
    exact of_decide_eq_true h2'
  obtain ⟨hc1, hc2⟩ := validX_perm hN hV' (posOf_lt c)
  obtain ⟨hd1, hd2⟩ := validX_perm hN hV' (posOf_lt d)
  have hdig : ∀ j < 14, sD QS NS j (benesInv 17 NS (xposK (posOf c))) =
      sD QS NS j (benesInv 17 NS (xposK (posOf d))) := by
    intro j hj
    have hk : 14 - j ∈ Finset.Icc 1 14 := Finset.mem_Icc.2 ⟨by omega, by omega⟩
    have hSX : ∀ r, r < 98280 → r < SX := fun r hr => by rw [SX_eq]; omega
    unfold sD
    rw [dig3_dig5 (hSX _ hc1), dig3_dig5 (hSX _ hd1), dg_netP hN (hSX _ hc1), dg_netP hN (hSX _ hd1),
      hc2, hd2]
    have hc := hcd _ hk
    rw [qf_pow, qf_pow, ← Int.cast_sub, intCast_mem_D5_iff] at hc
    exact mod5_eq (dg_QS h1 h2 h3 h4 (by omega) (h5 _ hk) (posOf_lt c))
      (dg_QS h1 h2 h3 h4 (by omega) (h5 _ hk) (posOf_lt d)) hc
  have e := lexV_inj hinc _ _ hc1 hd1 (lexV_congr (sD QS NS) 8 14 hdig)
  have e2 : xposK (posOf c) = xposK (posOf d) := by rw [← hc2, e, hd2]
  have e3 := xposK_inj (posOf_lt c) (posOf_lt d) e2
  rw [← shortOf_posOf c, ← shortOf_posOf d]
  exact congrArg shortOf (Fin.ext e3)

end CFSG.KC.KDense

end
