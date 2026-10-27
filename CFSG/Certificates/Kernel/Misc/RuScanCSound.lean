module

public import Certificates.Data.Kernel.Misc.RuScanC
public import CFSG.Certificates.Kernel.Misc.RuScanSound

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KC.Misc.RuInv CFSG.KC.Misc.RuInv.P
  CFSG.KC.Misc.RuBase CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Quasithin.KGC31

section Masks

variable {M : Type} [Group M]

@[expose] def tj (y τ : M) (j : Nat) : M := y ^ j * τ * (y ^ j)⁻¹

@[expose] def mP (y τ : M) (m n : Nat) : M :=
  ((List.range (n + 1)).map fun j => if m.testBit j then tj y τ j else 1).prod

@[expose] def mQ (xs : Nat → M) (m r : Nat) : M :=
  ((List.range r).map fun k => if m.testBit k then xs k else 1).prod

theorem mP_zero (y τ : M) (m : Nat) : mP y τ m 0 = if m.testBit 0 then τ else 1 := by
  simp [mP, tj]

theorem mP_succ (y τ : M) (m n : Nat) :
    mP y τ m (n + 1) = mP y τ m n * if m.testBit (n + 1) then tj y τ (n + 1) else 1 := by
  rw [mP, List.range_succ, List.map_append, List.prod_append]
  simp [mP]

theorem mQ_succ (xs : Nat → M) (m r : Nat) :
    mQ xs m (r + 1) = mQ xs m r * if m.testBit r then xs r else 1 := by
  rw [mQ, List.range_succ, List.map_append, List.prod_append]
  simp [mQ]

theorem mP_mul_pow_succ (y τ : M) (m n : Nat) :
    mP y τ m (n + 1) * y ^ (n + 1) =
      mP y τ m n * y ^ n * (y * if m.testBit (n + 1) then τ else 1) := by
  rw [mP_succ]
  split_ifs
  · simp only [tj]
    group
  · group

theorem mem_orbSub_mP (y τ : M) (m n : Nat) : mP y τ m n ∈ orbSub y τ := by
  rw [mP]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact conj_mem_orbSub y τ j
  · exact Subgroup.one_mem _

theorem conj_mP (y τ : M) (m n : Nat) :
    y * mP y τ m n * y⁻¹ =
      ((List.range (n + 1)).map fun j => if m.testBit j then tj y τ (j + 1) else 1).prod := by
  rw [mP]
  induction (List.range (n + 1)) with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← ih]
    split_ifs
    · simp only [tj, pow_succ']
      group
    · group

theorem mQ_mem (xs : Nat → M) (m r : Nat) {K : Subgroup M} (hK : ∀ k < r, xs k ∈ K) :
    mQ xs m r ∈ K := by
  rw [mQ]
  refine Subgroup.list_prod_mem _ ?_
  intro x hx
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
  split_ifs
  · exact hK k (List.mem_range.mp hk)
  · exact Subgroup.one_mem _

end Masks

theorem bit_beq (m j : Nat) : Nat.beq (Nat.land (Nat.shiftRight m j) 1) 1 = m.testBit j := by
  change Nat.beq ((m >>> j) &&& 1) 1 = _
  rw [Nat.testBit_eq_decide_div_mod_eq, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
  rcases Nat.mod_two_eq_zero_or_one (m / 2 ^ j) with h | h <;> rw [h] <;> rfl

theorem tIf_eq {T : Nat} {τ : G} (hT : PRep 4060 12 T τ) (m j : Nat) (x : Fin 4060) :
    tIf T m j x = (((if m.testBit j then τ else 1 : G)) x : Nat) := by
  unfold tIf
  rw [bit_beq]
  cases m.testBit j
  · rfl
  · exact apP_eq hT x

theorem walkE_eq {ys : List Nat} {gs : List G} (h : PL ys gs) {T : Nat} {τ : G}
    (hT : PRep 4060 12 T τ) (m : Nat) :
    ∀ n (x : Fin 4060), walkE ys T m n x = ((mP gs.prod τ m n * gs.prod ^ n) x : Nat)
  | 0, x => by
    change tIf T m 0 x = _
    rw [tIf_eq hT, mP_zero, pow_zero, mul_one]
  | n + 1, x => by
    change walkE ys T m n (yAp ys (tIf T m (n + 1) x)) = _
    rw [tIf_eq hT, yAp_eq h, walkE_eq h hT m n, mP_mul_pow_succ]
    simp only [Equiv.Perm.mul_apply]

theorem cAp_eq {XP : Nat → Nat} {g o : Nat} {K B KI : G} (hK : PRep 4060 12 (XP (2 * g)) K)
    (hB : PRep 4060 12 (XP o) B) (hKI : PRep 4060 12 (XP (2 * g + 1)) KI) (x : Fin 4060) :
    cAp XP g o x = ((K * B * KI) x : Nat) := by
  change apP (XP (2 * g)) (apP (XP o) (apP (XP (2 * g + 1)) x)) = _
  rw [apP_eq hKI, apP_eq hB, apP_eq hK]
  rfl

theorem prodT_eq {XP : Nat → Nat} {g ob m r : Nat} {xs : Nat → G}
    (hx : ∀ k < r, ∀ v : Fin 4060, cAp XP g (ob + k) v = (xs k v : Nat)) :
    ∀ r' ≤ r, ∀ v : Fin 4060, prodT XP g ob m r' v = ((mQ xs m r') v : Nat)
  | 0, _, v => by simp [prodT, mQ]
  | r' + 1, hr, v => by
    change prodT XP g ob m r'
      (nIf(Nat.beq (Nat.land (Nat.shiftRight m r') 1) 1, cAp XP g (ob + r') v, v)) = _
    rw [bit_beq, mQ_succ]
    cases hb : m.testBit r'
    · exact (prodT_eq hx r' (by omega) v).trans (by simp)
    · change prodT XP g ob m r' (cAp XP g (ob + r') v) = _
      rw [hx r' (by omega) v, prodT_eq hx r' (by omega)]
      simp

theorem elemOK_sound {ys : List Nat} {gs : List G} (h : PL ys gs) {T : Nat} {τ : G}
    (hT : PRep 4060 12 T τ) {Kh XP : Nat → Nat} {g ob q ko S Tm r k : Nat} {xs : Nat → G}
    (hx : ∀ k' < r, ∀ v : Fin 4060, cAp XP g (ob + k') v = (xs k' v : Nat)) (hk : k < r)
    (hc : elemOK ys T Kh XP g ob q ko S Tm r k = true) :
    ∀ b (hb : b < 4), ((mP gs.prod τ S q) ⟨b, by omega⟩ : Nat) = (xs k ⟨b, by omega⟩ : Nat) ∧
      ((gs.prod * xs k * gs.prod⁻¹) ⟨b, by omega⟩ : Nat) = ((mQ xs Tm r) ⟨b, by omega⟩ : Nat) := by
  intro b hb
  unfold elemOK at hc
  have hcb := RuBase.allN_iff.1 hc b hb
  simp only [strictB_eq, RuBase.bAnd_eq', Bool.and_eq_true] at hcb
  obtain ⟨h1, hq, hy1, hyq, hw, hp⟩ := hcb
  have hu1 : Kh (ko + b) < 4060 := Nat.blt_eq.mp h1
  have huq : Kh (ko + (4 * (q - 1) + b)) < 4060 := Nat.blt_eq.mp hq
  have E1 : gs.prod ⟨Kh (ko + b), hu1⟩ = ⟨b, by omega⟩ :=
    Fin.ext ((yAp_eq h ⟨_, hu1⟩).symm.trans (Nat.eq_of_beq_eq_true hy1))
  have Eq : (gs.prod ^ q) ⟨_, huq⟩ = ⟨b, by omega⟩ :=
    Fin.ext ((yPow_eq h q ⟨_, huq⟩).symm.trans (Nat.eq_of_beq_eq_true hyq))
  constructor
  · have hw' := (walkE_eq h hT S q ⟨_, huq⟩).symm.trans (Nat.eq_of_beq_eq_true hw)
    rw [Equiv.Perm.mul_apply, Eq] at hw'
    exact hw'.trans (hx k hk ⟨b, by omega⟩)
  · have hinv : gs.prod⁻¹ ⟨b, by omega⟩ = ⟨Kh (ko + b), hu1⟩ := by
      rw [← E1]
      simp
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hinv]
    have a1 : cAp XP g (ob + k) (Kh (ko + b)) = (xs k ⟨_, hu1⟩ : Nat) := hx k hk ⟨_, hu1⟩
    calc ((gs.prod (xs k ⟨_, hu1⟩)) : Nat) = yAp ys (xs k ⟨_, hu1⟩) := (yAp_eq h _).symm
      _ = yAp ys (cAp XP g (ob + k) (Kh (ko + b))) := by rw [a1]
      _ = prodT XP g ob Tm r b := Nat.eq_of_beq_eq_true hp
      _ = _ := prodT_eq hx r le_rfl ⟨b, by omega⟩

theorem candOK_sound {ys : List Nat} {T : Nat} {Kh V XP CT D : Nat → Nat} {nc go l o : Nat}
    (hc : candOK ys T Kh V XP CT nc go D l o = true) :
    (∀ i < 28, Kh (32 * D (o + 1) + i) < 4060) ∧ leafOK ys T Kh V l (D (o + 1)) = true ∧
      D (o + 2) < nc ∧ CT (D (o + 2)) < 5 ∧
      (if CT (D (o + 2)) < 3 then 7 else 5) = V (64 + 32 * l + 28) ∧
      ∀ k < rk (CT (D (o + 2))), elemOK ys T Kh XP (go + D (o + 2)) (46 + boff (CT (D (o + 2))))
        (V (64 + 32 * l + 28)) (32 * D (o + 1)) (D (o + (3 + 2 * k))) (D (o + (4 + 2 * k)))
        (rk (CT (D (o + 2)))) k = true := by
  unfold candOK at hc
  simp only [strictB_eq, RuBase.bAnd_eq', Bool.and_eq_true] at hc
  obtain ⟨hk, hl, hci, ht, hq, he⟩ := hc
  refine ⟨fun i hi => ?_, hl, Nat.blt_eq.mp hci, Nat.blt_eq.mp ht, ?_,
    fun k hk' => RuBase.allN_iff.1 he k hk'⟩
  · unfold kbndK at hk
    exact Nat.blt_eq.mp (RuBase.allN_iff.1 hk i hi)
  · have e : Bool.rec (motive := fun _ => Nat) 5 7 (Nat.blt (CT (D (o + 2))) 3) =
        V (64 + 32 * l + 28) := Nat.eq_of_beq_eq_true hq
    rw [← e]
    by_cases h3 : CT (D (o + 2)) < 3
    · rw [if_pos h3, Nat.blt_eq.mpr h3]
    · rw [if_neg h3, Bool.eq_false_iff.mpr (fun h => h3 (Nat.blt_eq.mp h))]

theorem candC3_sound {LR TR D Kh V XP CT : Nat → Nat} {nc go H T N dofs lo cnt : Nat}
    (hc : candC3 LR TR D Kh V XP CT nc go H T N dofs lo cnt = true) :
    ∀ d < cnt, D (16 * (dofs + (lo + d))) < N ∧
      candOK [H, TR (roff 4060 48720 (LR 0) + D (16 * (dofs + (lo + d))) / rcnt (LR 2) / rcnt (LR 1)),
        TR (roff 4060 48720 (LR 1) + D (16 * (dofs + (lo + d))) / rcnt (LR 2) % rcnt (LR 1)),
        TR (roff 4060 48720 (LR 2) + D (16 * (dofs + (lo + d))) % rcnt (LR 2))] T Kh V XP CT nc go D
        (lo + d) (16 * (dofs + (lo + d))) = true := by
  intro d hd
  unfold candC3 at hc
  simp only [strictB_eq] at hc
  have h := RuBase.allN_iff.1 hc d hd
  rw [RuBase.bAnd_eq', Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, h.2⟩

theorem candC2_sound {LR TR D Kh V XP CT : Nat → Nat} {nc go H T N dofs lo cnt : Nat}
    (hc : candC2 LR TR D Kh V XP CT nc go H T N dofs lo cnt = true) :
    ∀ d < cnt, D (16 * (dofs + (lo + d))) < N ∧
      candOK [H, TR (roff 4060 48720 (LR 0) + D (16 * (dofs + (lo + d))) / rcnt (LR 1)),
        TR (roff 4060 48720 (LR 1) + D (16 * (dofs + (lo + d))) % rcnt (LR 1))] T Kh V XP CT nc go
        D (lo + d) (16 * (dofs + (lo + d))) = true := by
  intro d hd
  unfold candC2 at hc
  simp only [strictB_eq] at hc
  have h := RuBase.allN_iff.1 hc d hd
  rw [RuBase.bAnd_eq', Bool.and_eq_true] at h
  exact ⟨Nat.blt_eq.mp h.1, h.2⟩

end CFSG.KC.Misc.RuScan

end
