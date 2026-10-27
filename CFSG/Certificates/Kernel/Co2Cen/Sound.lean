module

public import Certificates.Data.Kernel.Co2Cen
public import CFSG.Certificates.Kernel.Co2Cls.Sound
public import CFSG.Certificates.Kernel.Co2J.Sound
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.Kernel.BSeed.Sound
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Open.Defs
public import CFSG.Perm.ChainSpec

set_option exponentiation.threshold 600

public section

namespace CFSG.KC.Co2Cen

open CFSG.KC.Loop CFSG.KC.F2W CFSG.KC.Co2InvS CFSG.KC.Co2Syl CFSG.KC.Co2Cls CFSG.KC.Co2J
  CFSG.KC.TabMatGrp CFSG.KLie.CT CFSG.KC.M1F2

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem allK_of {n : Nat} {f : Nat → Bool} (h : ∀ k < n, f k = true) : allK n f = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change andK (f n) (allK n f) = true
    rw [andK_eq, Bool.and_eq_true]
    exact ⟨h n (by omega), ih fun k hk => h k (by omega)⟩

theorem beq_of_eq {a b : Nat} (h : a = b) : Nat.beq a b = true := by rw [h, Nat.beq_refl]

theorem elemOf_eq (x : Nat) : elemOf x = x % 2 ^ 484 := by
  have e : elemOf x = x &&& (2 ^ 484 - 1) := rfl
  rw [e, Nat.and_two_pow_sub_one_eq_mod]

theorem elemOf_lt (x : Nat) : elemOf x < 2 ^ 484 := by
  rw [elemOf_eq]
  exact Nat.mod_lt _ (by positivity)

theorem scRank_sound {M bad q : Nat} (h : scRank M bad q = true) : (MatP 22 M).rank ≠ bad := by
  unfold scRank at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true, notK_eq, Bool.not_eq_true'] at h
  obtain ⟨h1, h2, h3⟩ := h
  rw [rankL_sound (Nat.le_of_ble_eq_true h1) h3]
  intro e
  rw [e, Nat.beq_refl] at h2
  exact Bool.noConfusion h2

theorem scanC_sound {CF CR : Nat → Nat} {ex : Nat → Nat → Bool} {T bad k : Nat}
    (h : scanC CF CR ex T bad k = true)
    (hc : MatP 22 (elemAt CF k) * MatP 22 T = MatP 22 T * MatP 22 (elemAt CF k)) :
    (scFlag (CR k) = true ∧ ex (elemAt CF k) (CR k) = true) ∨
      (MatP 22 (elemAt CF k) * MatP 22 T + 1).rank ≠ bad := by
  unfold scanC at h
  simp only [letB_eq] at h
  have hb : Nat.beq (mulV (elemAt CF k) T) (mulV T (elemAt CF k)) = true := by
    rw [← MatP_mulV, ← MatP_mulV] at hc
    rw [MatP_inj' (mulV_lt _ _) (mulV_lt _ _) hc, Nat.beq_refl]
  rw [implK_eq, hb, iteT rfl, bIf_eq'] at h
  by_cases hf : scFlag (CR k) = true
  · rw [iteT hf] at h
    exact Or.inl ⟨hf, h⟩
  · rw [iteF hf] at h
    right
    have e : MatP 22 (Nat.xor (mulV (elemAt CF k) T) IDP) =
        MatP 22 (elemAt CF k) * MatP 22 T + 1 := by
      rw [← MatP_IDP, ← MatP_mulV]
      exact MatP_xor _ _
    rw [← e]
    exact scRank_sound h

theorem MatP_bitMul (G : Nat → Nat) (u : Nat) : ∀ n,
    MatP 22 (bitMul G n u) = bitProd (fun i => MatP 22 (G i)) n u
  | 0 => MatP_IDP
  | n + 1 => by
    change MatP 22 (nIf(bit u n, mulV (bitMul G n u) (G n), bitMul G n u)) = _
    rw [nIf_eq', bit_eq]
    simp only [bitProd]
    rw [← MatP_bitMul G u n]
    cases u.testBit n
    · simp
    · simp [MatP_mulV]

theorem exW_sound {G : Nat → Nat} {n X q : Nat} (h : exW G n X q = true) :
    MatP 22 X = bitProd (fun i => MatP 22 (G i)) n (q >>> 974) := by
  rw [← MatP_bitMul]
  exact congrArg _ (Nat.eq_of_beq_eq_true h)

theorem fixV_iff {MK : Nat → Nat} {v : Nat} :
    fixV MK v = true ↔ ∀ k < 5, vmF 10 (MK k) v = v :=
  ⟨fun h k hk => Nat.eq_of_beq_eq_true (allK_spec h k hk),
    fun h => allK_of fun k hk => beq_of_eq (h k hk)⟩

theorem fixK_sound {MK F : Nat → Nat} {nF : Nat} (h : fixK MK F nF = true) :
    (∀ i < nF, F i < 1024 ∧ ∀ k < 5, vmF 10 (MK k) (F i) = F i) ∧
      ∀ v < 1024, (∀ k < 5, vmF 10 (MK k) v = v) → ∃ i < nF, F i = v := by
  unfold fixK at h
  rw [andK_eq, Bool.and_eq_true] at h
  refine ⟨fun i hi => ?_, fun v hv hfix => ?_⟩
  · have e := allK_spec h.1 i hi
    simp only [andK_eq, Bool.and_eq_true] at e
    exact ⟨blt_iff.1 e.1, fixV_iff.1 e.2⟩
  · have e := allK_spec h.2 v hv
    simp only [implK_eq] at e
    rw [iteT (fixV_iff.2 hfix)] at e
    exact invHit_spec e

section Tuple

variable {R G WG : Nat → Nat} {NG N : Nat}

theorem recW_spec {s : Nat} (h : recW R G WG NG N s = true) :
    R s >>> 2460 = 0 ∧ twSort R N s = true ∧ (s = 0 → ∀ i < 5, twComp (R s) i = WG i) ∧
    (s ≠ 0 → twPar (R s) < s ∧ twLet (R s) < NG ∧ ∀ i < 5,
      mulV (twComp (R s) i) (G (twLet (R s))) =
        mulV (G (twLet (R s))) (twComp (R (twPar (R s))) i)) := by
  unfold recW at h
  simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
  obtain ⟨h0, hs, h⟩ := h
  rw [bIf_eq'] at h
  refine ⟨Nat.eq_of_beq_eq_true h0, hs, fun e => ?_, fun e => ?_⟩
  · subst e
    rw [iteT (Nat.beq_refl 0)] at h
    exact fun i hi => Nat.eq_of_beq_eq_true (allK_spec h i hi)
  · rw [iteF (by rw [beq_false e]; exact Bool.false_ne_true)] at h
    simp only [Bool.and_eq_true] at h
    have he : twEdge (R s) (R (twPar (R s))) (G (twLet (R s))) = true := h.2.2
    exact ⟨blt_iff.1 h.1, blt_iff.1 h.2.1, fun i hi => Nat.eq_of_beq_eq_true (allK_spec he i hi)⟩

theorem tw_conj (hok : ∀ s < N, recW R G WG NG N s = true) :
    ∀ s < N, ∃ g ∈ genMonN NG G, ∀ i < 5,
      g * MatP 22 (WG i) = MatP 22 (twComp (R s) i) * g := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
  intro hs
  obtain ⟨-, -, h0, h1⟩ := recW_spec (hok s hs)
  rcases Nat.eq_zero_or_pos s with e | e
  · exact ⟨1, (genMonN NG G).one_mem, fun i hi => by rw [h0 e i hi, one_mul, mul_one]⟩
  · obtain ⟨hp, hj, he⟩ := h1 (by omega)
    obtain ⟨g, hg, hgx⟩ := ih _ hp (by omega)
    refine ⟨MatP 22 (G (twLet (R s))) * g, (genMonN NG G).mul_mem (genN_mem G hj) hg,
      fun i hi => ?_⟩
    have e2 := congrArg (MatP 22) (he i hi)
    rw [MatP_mulV, MatP_mulV] at e2
    rw [mul_assoc, hgx i hi, ← mul_assoc, ← e2, mul_assoc]

theorem twKey_eq {q q' : Nat} (h : q >>> 2460 = 0) (h' : q' >>> 2460 = 0)
    (hc : ∀ i < 5, twComp q i = twComp q' i) : twKey q = twKey q' := by
  apply Nat.eq_of_testBit_eq
  intro p
  change (q >>> 40).testBit p = (q' >>> 40).testBit p
  rw [Nat.testBit_shiftRight, Nat.testBit_shiftRight]
  by_cases hp : p < 2420
  · have hi : p / 484 < 5 := by omega
    have e := congrArg (fun x => x.testBit (p % 484)) (hc _ hi)
    have hq : ∀ x : Nat, twComp x (p / 484) = (x >>> (40 + 484 * (p / 484))) % 2 ^ 484 :=
      fun x => elemOf_eq _
    simp only [hq, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight,
      decide_eq_true (Nat.mod_lt p (by norm_num : 0 < 484)), Bool.true_and] at e
    have e3 : 40 + 484 * (p / 484) + p % 484 = 40 + p := by omega
    rwa [e3] at e
  · have hz : ∀ x : Nat, x >>> 2460 = 0 → x.testBit (40 + p) = false := by
      intro x hx
      have e := congrArg (fun y => y.testBit (p - 2420)) hx
      simp only [Nat.testBit_shiftRight, Nat.zero_testBit] at e
      have e3 : 2460 + (p - 2420) = 40 + p := by omega
      rwa [e3] at e
    rw [hz q h, hz q' h']

theorem tw_inj (hok : ∀ s < N, recW R G WG NG N s = true) :
    ∀ a < N, ∀ b < N, (∀ i < 5, MatP 22 (twComp (R a) i) = MatP 22 (twComp (R b) i)) →
      a = b := by
  have hs : ∀ i < N, twSrt (R i) < N := by
    intro i hi
    have h := (recW_spec (hok i hi)).2.1
    unfold twSort at h
    simp only [letB_eq, andK_eq, Bool.and_eq_true] at h
    exact blt_iff.1 h.1
  have hlt : ∀ i, i + 1 < N → twKey (R (twSrt (R i))) < twKey (R (twSrt (R (i + 1)))) := by
    intro i hi
    have h := (recW_spec (hok i (by omega))).2.1
    unfold twSort at h
    simp only [letB_eq] at h
    rw [andK_eq, Bool.and_eq_true, implK_eq, blt_iff.2 hi, iteT rfl] at h
    exact blt_iff.1 h.2
  intro a ha b hb e
  refine sorted_inj (σ := fun i => twSrt (R i)) (f := fun i => twKey (R i)) hs hlt a ha b hb ?_
  exact twKey_eq (recW_spec (hok a ha)).1 (recW_spec (hok b hb)).1 fun i hi =>
    MatP_inj' (elemOf_lt _) (elemOf_lt _) (e i hi)

end Tuple

end CFSG.KC.Co2Cen

end
