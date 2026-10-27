module

public import CFSG.Certificates.Kernel.Co1Three.ActSound
public import Certificates.Data.Kernel.Co1Three.Dual
import CFSG.Certificates.Kernel.Spor.Loops

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2

def dgK (p c i : Nat) : ZMod p := ((c / p ^ i : Nat) : ZMod p)

theorem dgK_succ (p c i : Nat) : dgK p c (i + 1) = dgK p (c / p) i := by
  unfold dgK
  rw [pow_succ', Nat.div_div_eq_div_mul]

theorem dgK_zero_left (p i : Nat) : dgK p 0 i = 0 := by
  unfold dgK
  rw [Nat.zero_div, Nat.cast_zero]

theorem dgK_addVK {p : Nat} (hp : 0 < p) : ∀ (n x y i : Nat), i < n →
    dgK p (addVK p n x y) i = dgK p x i + dgK p y i
  | 0, _, _, _, hi => absurd hi (Nat.not_lt_zero _)
  | n + 1, x, y, i, hi => by
    have ha : (x % p + y % p) % p < p := Nat.mod_lt _ hp
    rw [addVK_succ]
    cases i with
    | zero =>
      unfold dgK
      simp only [pow_zero, Nat.div_one]
      push_cast
      rw [ZMod.natCast_self, zero_mul, add_zero, ZMod.natCast_mod, Nat.cast_add, ZMod.natCast_mod,
        ZMod.natCast_mod]
    | succ i =>
      rw [dgK_succ, dgK_succ, dgK_succ, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt ha,
        Nat.zero_add]
      exact dgK_addVK hp n _ _ i (by omega)

theorem dotK_succ (p n x y : Nat) :
    dotK p (n + 1) x y = (x % p * (y % p) + dotK p n (x / p) (y / p)) % p := rfl

theorem dotK_lt {p : Nat} (hp : 0 < p) : ∀ (n x y : Nat), dotK p n x y < p
  | 0, _, _ => hp
  | n + 1, x, y => by
    rw [dotK_succ]
    exact Nat.mod_lt _ hp

theorem dotK_cast (p : Nat) : ∀ (n x y : Nat),
    (dotK p n x y : ZMod p) = ∑ i ∈ Finset.range n, dgK p x i * dgK p y i
  | 0, x, y => by
    have e : dotK p 0 x y = 0 := rfl
    rw [Finset.sum_range_zero, e, Nat.cast_zero]
  | n + 1, x, y => by
    rw [dotK_succ, ZMod.natCast_mod, Finset.sum_range_succ']
    simp only [dgK_succ]
    rw [← dotK_cast p n (x / p) (y / p)]
    unfold dgK
    push_cast
    rw [ZMod.natCast_mod, ZMod.natCast_mod, pow_zero, Nat.div_one, Nat.div_one, add_comm]

theorem dgK_iter {p : Nat} (hp : 0 < p) (n r i : Nat) (hi : i < n) : ∀ (a e : Nat),
    dgK p (Nat.rec (motive := fun _ => Nat) a
      (fun _ b => strictN b fun b => addVK p n b r) e) i = dgK p a i + e * dgK p r i
  | a, 0 => by
    rw [Nat.cast_zero, zero_mul, add_zero]
    rfl
  | a, e + 1 => by
    change dgK p (strictN (Nat.rec (motive := fun _ => Nat) a
      (fun _ b => strictN b fun b => addVK p n b r) e) fun b => addVK p n b r) i = _
    rw [strictN_eq, dgK_addVK hp n _ _ i hi, dgK_iter hp n r i hi a e]
    push_cast
    ring

theorem dgK_actK {p : Nat} (hp : 0 < p) (n i : Nat) (hi : i < n) : ∀ (rows : List Nat) (v acc : Nat),
    dgK p (actK p n rows v acc) i =
      dgK p acc i + ∑ j ∈ Finset.range rows.length, dgK p v j * dgK p (rows.getD j 0) i
  | [], _, acc => by
    rw [List.length_nil, Finset.sum_range_zero, add_zero]
    rfl
  | r :: rows, v, acc => by
    change dgK p (strictN (v % p) fun e => strictN (Nat.rec (motive := fun _ => Nat) acc
      (fun _ b => strictN b fun b => addVK p n b r) e) fun acc' => actK p n rows (v / p) acc') i = _
    rw [strictN_eq, strictN_eq, dgK_actK hp n i hi rows, dgK_iter hp n r i hi, List.length_cons,
      Finset.sum_range_succ']
    simp only [dgK_succ, List.getD_cons_succ, List.getD_cons_zero]
    have e : ((v % p : Nat) : ZMod p) = dgK p v 0 := by
      unfold dgK
      rw [ZMod.natCast_mod, pow_zero, Nat.div_one]
    rw [e]
    ring

theorem dualRowK_sound {p n : Nat} (hp : 0 < p) {M D : List Nat} (h : dualRowK p n M D = true)
    (f v : Nat) : dotK p n (actK p n D f 0) (actK p n M v 0) = dotK p n f v := by
  unfold dualRowK at h
  simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false] at h
  obtain ⟨hM, hD, hall⟩ := h
  have hMl : M.length = n := by
    rw [← lenL_eq]
    exact Nat.eq_of_beq_eq_true hM
  have hDl : D.length = n := by
    rw [← lenL_eq]
    exact Nat.eq_of_beq_eq_true hD
  have hdual : ∀ i < n, ∀ j < n,
      (dotK p n (M.getD i 0) (D.getD j 0) : ZMod p) = if j = i then 1 else 0 := by
    intro i hi j hj
    have e := Nat.eq_of_beq_eq_true (CFSG.KS.allN_spec (CFSG.KS.allN_spec hall i hi) j hj)
    rw [getL_eq, getL_eq, nrec_eq] at e
    rw [e]
    by_cases hij : i = j
    · rw [if_pos (by rw [hij]; exact Nat.beq_refl j), if_pos hij.symm, Nat.cast_one]
    · rw [if_neg (fun h' => hij (Nat.eq_of_beq_eq_true h')), if_neg (Ne.symm hij), Nat.cast_zero]
  have key : (dotK p n (actK p n D f 0) (actK p n M v 0) : ZMod p) = (dotK p n f v : ZMod p) := by
    rw [dotK_cast, dotK_cast]
    calc ∑ i ∈ Finset.range n, dgK p (actK p n D f 0) i * dgK p (actK p n M v 0) i
        = ∑ i ∈ Finset.range n, ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n,
            dgK p f a * dgK p v b * (dgK p (M.getD b 0) i * dgK p (D.getD a 0) i) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' := Finset.mem_range.mp hi
          rw [dgK_actK hp n i hi', dgK_actK hp n i hi', dgK_zero_left, zero_add, zero_add, hDl, hMl,
            Finset.sum_mul_sum]
          refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
          ring
      _ = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, dgK p f a * dgK p v b *
            ∑ i ∈ Finset.range n, dgK p (M.getD b 0) i * dgK p (D.getD a 0) i := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun b _ => ?_
          rw [Finset.mul_sum]
      _ = ∑ a ∈ Finset.range n, dgK p f a * dgK p v a := by
          refine Finset.sum_congr rfl fun a ha => ?_
          have ha' := Finset.mem_range.mp ha
          have e : ∀ b ∈ Finset.range n, dgK p f a * dgK p v b *
              ∑ i ∈ Finset.range n, dgK p (M.getD b 0) i * dgK p (D.getD a 0) i =
              if a = b then dgK p f a * dgK p v b else 0 := by
            intro b hb
            rw [← dotK_cast, hdual b (Finset.mem_range.mp hb) a ha']
            by_cases hab : a = b
            · rw [if_pos hab, if_pos hab, mul_one]
            · rw [if_neg hab, if_neg hab, mul_zero]
          rw [Finset.sum_congr rfl e, Finset.sum_ite_eq, if_pos ha]
  have h1 := (ZMod.natCast_eq_natCast_iff' _ _ _).mp key
  rwa [Nat.mod_eq_of_lt (dotK_lt hp _ _ _), Nat.mod_eq_of_lt (dotK_lt hp _ _ _)] at h1

theorem dualsK_sound {p n : Nat} : ∀ {NZ DZ : List (Nat × List Nat)}, dualsK p n NZ DZ = true →
    ∀ y ∈ DZ, ∃ x ∈ NZ, x.1 = y.1 ∧ dualRowK p n x.2 y.2 = true
  | [], [], _, y, hy => absurd hy List.not_mem_nil
  | [], _ :: _, h, _, _ => absurd (h : false = true) Bool.false_ne_true
  | _ :: _, [], h, _, _ => absurd (h : false = true) Bool.false_ne_true
  | x :: NZ, y₀ :: DZ, h, y, hy => by
    have h' : Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
        (dualsK p n NZ DZ) (dualRowK p n x.2 y₀.2)) (Nat.beq x.1 y₀.1) = true := h
    simp only [brec_eq_true, Bool.false_eq_true, and_false, or_false] at h'
    rcases List.mem_cons.1 hy with rfl | hy
    · exact ⟨x, List.mem_cons_self, Nat.eq_of_beq_eq_true h'.1, h'.2.1⟩
    · obtain ⟨x', hx', e, hd⟩ := dualsK_sound h'.2.2 y hy
      exact ⟨x', List.mem_cons_of_mem _ hx', e, hd⟩

theorem forest_hyp {M : Type*} [Group M] (E k : Nat → M) {p n : Nat} (hp : 0 < p)
    {NZ DZ : List (Nat × List Nat)} {RT : List Nat} {DP : Nat} {FT : List Nat}
    (hf : forestK p n DZ RT DP FT = true) (hd : dualsK p n NZ DZ = true)
    (hconj : ∀ x ∈ NZ, ∀ v, (k x.1)⁻¹ * E v * k x.1 = E (actK p n x.2 v 0)) :
    ∀ c, 1 ≤ c → c < p ^ n → ∃ r ∈ RT, ∃ h : M, ∀ v, dotK p n r v = 0 →
      ∃ w, dotK p n c w = 0 ∧ h⁻¹ * E v * h = E w := by
  intro c h1 h2
  obtain ⟨r, hr, hrt⟩ := forestK_sound hf c h1 h2
  refine ⟨r, hr, ?_⟩
  clear h1 h2
  induction hrt with
  | refl => exact ⟨1, fun v hv => ⟨v, hv, by group⟩⟩
  | tail _ hab ih =>
    obtain ⟨h, hh⟩ := ih
    obtain ⟨g, hg, hact⟩ := hab
    rw [nzRows_eq] at hact
    have hy : DZ.getD g (0, []) ∈ DZ := by
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem hg
    obtain ⟨x, hx, -, hdual⟩ := dualsK_sound hd _ hy
    refine ⟨h * k x.1, fun v hv => ?_⟩
    obtain ⟨w, hw, hvw⟩ := hh v hv
    refine ⟨actK p n x.2 w 0, ?_, ?_⟩
    · rw [← hact, dualRowK_sound hp hdual]
      exact hw
    · have e : (h * k x.1)⁻¹ * E v * (h * k x.1) = (k x.1)⁻¹ * (h⁻¹ * E v * h) * k x.1 := by
        group
      rw [e, hvw, hconj x hx w]

end CFSG.KC.Co1Cl

end
