module

public import CFSG.LieType.Steinberg.Minuscule.Cert
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115

public noncomputable section

namespace CFSG.LieType.Steinberg.Minuscule

theorem dig_lt (M a : ℕ) : dig M a < 256 := Nat.mod_lt _ (by norm_num)

theorem ofDigits_succ (d : ℕ) (f : ℕ → ℕ) :
    ofDigits (d + 1) f = ofDigits d f + f d * 256 ^ d := by
  simp [ofDigits, List.range_succ]

theorem ofDigits_lt {d : ℕ} {f : ℕ → ℕ} (hf : ∀ b < d, f b < 256) :
    ofDigits d f < 256 ^ d := by
  induction d with
  | zero => simp [ofDigits]
  | succ d ih =>
    rw [ofDigits_succ, pow_succ]
    have h1 := ih fun b hb => hf b (by omega)
    have h2 := hf d (by omega)
    nlinarith

theorem dig_ofDigits {d : ℕ} {f : ℕ → ℕ} (hf : ∀ b < d, f b < 256) {a : ℕ} (ha : a < d) :
    dig (ofDigits d f) a = f a := by
  induction d with
  | zero => omega
  | succ d ih =>
    have hf' : ∀ b < d, f b < 256 := fun b hb => hf b (by omega)
    rw [ofDigits_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.1 ha with ha | rfl
    · have hpow : f d * 256 ^ d = 256 ^ a * (f d * 256 ^ (d - a - 1) * 256) := by
        have : 256 ^ d = 256 ^ a * 256 ^ (d - a - 1) * 256 := by
          rw [← pow_add, ← pow_succ]
          congr 1
          omega
        rw [this]
        ring
      rw [dig, hpow, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_right]
      exact ih hf' ha
    · rw [dig, Nat.add_mul_div_right _ _ (by positivity),
        Nat.div_eq_of_lt (ofDigits_lt hf'), zero_add]
      exact Nat.mod_eq_of_lt (hf a (by omega))

theorem sum_map_range_eq_sum_fin {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℕ → M) :
    ((List.range d).map f).sum = ∑ i : Fin d, f i := by
  induction d with
  | zero => simp
  | succ d ih => rw [List.sum_range_succ, ih, Fin.sum_univ_castSucc]; rfl

theorem ofDigits_eq_sum (d : ℕ) (f : ℕ → ℕ) : ofDigits d f = ∑ b : Fin d, f b * 256 ^ (b : ℕ) :=
  sum_map_range_eq_sum_fin d _

instance instRingEnd (R : Type*) [CommRing R] (d : ℕ) : Ring (Module.End R (Fin d →₀ R)) :=
  Module.End.instRing

variable (R : Type*) [CommRing R] (d : ℕ)

@[expose] def digVec (c : ℕ) : Fin d →₀ R :=
  if h : 2 ≤ c ∧ c / 2 - 1 < d then (-1 : R) ^ c • Finsupp.single ⟨c / 2 - 1, h.2⟩ 1 else 0

@[expose] def toEnd (M : ℕ) : Module.End R (Fin d →₀ R) :=
  Finsupp.linearCombination R fun a : Fin d => digVec R d (dig M a)

variable {R d}

theorem toEnd_single (M : ℕ) (a : Fin d) :
    toEnd R d M (Finsupp.single a 1) = digVec R d (dig M a) := by
  simp [toEnd]

theorem ext_single {f g : Module.End R (Fin d →₀ R)}
    (h : ∀ a : Fin d, f (Finsupp.single a 1) = g (Finsupp.single a 1)) : f = g :=
  Finsupp.lhom_ext' fun a => LinearMap.ext_ring (h a)

theorem digVec_of_lt_two {c : ℕ} (hc : c < 2) : digVec R d c = 0 := by
  rw [digVec, dite_eq_right (by omega)]

theorem digVec_zero : digVec R d 0 = 0 := digVec_of_lt_two (by norm_num)

theorem digVec_of_le {c : ℕ} (hc : 2 ≤ c) (hd : c / 2 - 1 < d) :
    digVec R d c = (-1 : R) ^ c • Finsupp.single ⟨c / 2 - 1, hd⟩ 1 := by
  rw [digVec, dite_eq_left ⟨hc, hd⟩]

theorem digVec_of_ge {c : ℕ} (hd : d ≤ c / 2 - 1) : digVec R d c = 0 := by
  rw [digVec, dite_eq_right (by omega)]

theorem toEnd_zero : toEnd R d 0 = 0 :=
  ext_single fun a => by simp [toEnd_single, dig, digVec_zero]

theorem neg_one_pow_of_mod_two {g c e : ℕ} (h : g % 2 = (c + e) % 2) :
    (-1 : R) ^ g = (-1) ^ c * (-1) ^ e := by
  rw [← pow_add, neg_one_pow_eq_pow_mod_two, h, ← neg_one_pow_eq_pow_mod_two]

theorem neg_one_pow_mul_self (n : ℕ) : (-1 : R) ^ n * (-1) ^ n = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]

theorem digVec_comb (c e : ℕ) :
    digVec R d (2 * (e / 2) + (c % 2 + e % 2) % 2) = (-1 : R) ^ c • digVec R d e := by
  rcases Nat.lt_or_ge e 2 with he2 | he2
  · rw [digVec_of_lt_two (by omega), digVec_of_lt_two he2, smul_zero]
  have hg : (2 * (e / 2) + (c % 2 + e % 2) % 2) / 2 = e / 2 := by omega
  by_cases hd : e / 2 - 1 < d
  · rw [digVec_of_le (by omega) (by omega), digVec_of_le he2 hd, smul_smul,
      ← neg_one_pow_of_mod_two (g := 2 * (e / 2) + (c % 2 + e % 2) % 2) (by omega)]
    congr 2
    exact Fin.ext (by simp only; omega)
  · rw [digVec_of_ge (by omega), digVec_of_ge (by omega), smul_zero]

@[expose] def WF (d M : ℕ) : Prop :=
  ∀ a < d, dig M a = 0 ∨ 2 ≤ dig M a ∧ dig M a / 2 - 1 < d

theorem compDigit_lt (M N a : ℕ) : compDigit M N a < 256 := by
  have := dig_lt M (dig N a / 2 - 1)
  unfold compDigit
  split_ifs <;> omega

theorem dig_comp (M N : ℕ) {a : ℕ} (ha : a < d) : dig (comp d M N) a = compDigit M N a :=
  dig_ofDigits (fun b _ => compDigit_lt M N b) ha

theorem toEnd_comp {M N : ℕ} (hN : WF d N) :
    toEnd R d (comp d M N) = toEnd R d M * toEnd R d N := by
  refine ext_single fun a => ?_
  rw [Module.End.mul_apply, toEnd_single, toEnd_single, dig_comp M N a.2]
  rcases hN a a.2 with h0 | ⟨h2, hlt⟩
  · rw [compDigit, ite_eq_left h0, h0, digVec_zero, map_zero]
  · rw [digVec_of_le h2 hlt, map_smul, toEnd_single, compDigit, ite_eq_right (by omega)]
    split_ifs with he
    · rw [he, digVec_zero, smul_zero]
    · exact digVec_comb _ _

theorem WF.comp {M N : ℕ} (hM : WF d M) (hN : WF d N) : WF d (comp d M N) := by
  intro a ha
  rw [dig_comp M N ha, compDigit]
  rcases hN a ha with h0 | ⟨h2, hlt⟩
  · exact Or.inl (ite_eq_left h0)
  rw [ite_eq_right (by omega)]
  rcases hM _ hlt with h0' | ⟨h2', hlt'⟩
  · exact Or.inl (ite_eq_left h0')
  rw [ite_eq_right (by omega)]
  right
  omega

theorem WF.zero : WF d 0 := fun a _ => Or.inl (by simp [dig])

theorem negDigit_lt {c : ℕ} (hc : c < 256) : negDigit c < 256 := by
  unfold negDigit
  split_ifs <;> omega

theorem dig_neg (M : ℕ) {a : ℕ} (ha : a < d) : dig (neg d M) a = negDigit (dig M a) :=
  dig_ofDigits (fun b _ => negDigit_lt (dig_lt M b)) ha

theorem digVec_negDigit (c : ℕ) : digVec R d (negDigit c) = -digVec R d c := by
  rcases Nat.lt_or_ge c 2 with hc | hc
  · rw [digVec_of_lt_two hc, neg_zero, negDigit]
    split_ifs
    · exact digVec_zero
    · exact digVec_of_lt_two (by omega)
  have hn : negDigit c = c / 2 * 2 + (1 - c % 2) := by rw [negDigit, ite_eq_right (by omega)]
  have hn2 : (c / 2 * 2 + (1 - c % 2)) / 2 = c / 2 := by omega
  by_cases hd : c / 2 - 1 < d
  · rw [hn, digVec_of_le (by omega) (by omega), digVec_of_le hc hd, ← neg_smul]
    have hs : (-1 : R) ^ (c / 2 * 2 + (1 - c % 2)) = -(-1) ^ c := by
      rw [← neg_one_mul ((-1 : R) ^ c), ← pow_succ', neg_one_pow_eq_pow_mod_two,
        neg_one_pow_eq_pow_mod_two (n := c + 1)]
      congr 1
      omega
    rw [hs]
    congr 2
    exact Fin.ext (by simp only; omega)
  · rw [hn, digVec_of_ge (by omega), digVec_of_ge (by omega), neg_zero]

theorem toEnd_neg (M : ℕ) : toEnd R d (neg d M) = -toEnd R d M :=
  ext_single fun a => by
    rw [LinearMap.neg_apply, toEnd_single, toEnd_single, dig_neg M a.2, digVec_negDigit]

theorem WF.neg {M : ℕ} (hM : WF d M) : WF d (neg d M) := by
  intro a ha
  rw [dig_neg M ha, negDigit]
  rcases hM a ha with h0 | ⟨h2, hlt⟩
  · exact Or.inl (ite_eq_left h0)
  · rw [ite_eq_right (by omega)]
    right
    omega

theorem dig_union (M N : ℕ) {a : ℕ} (ha : a < d) :
    dig (union d M N) a = if dig M a = 0 then dig N a else dig M a :=
  dig_ofDigits (fun b _ => by split_ifs <;> exact dig_lt _ _) ha

theorem toEnd_union {M N : ℕ} (h : ∀ a < d, dig M a = 0 ∨ dig N a = 0) :
    toEnd R d (union d M N) = toEnd R d M + toEnd R d N :=
  ext_single fun a => by
    rw [LinearMap.add_apply, toEnd_single, toEnd_single, toEnd_single, dig_union M N a.2]
    split_ifs with hM
    · rw [hM, digVec_zero, zero_add]
    · rw [(h a a.2).resolve_left hM, digVec_zero, add_zero]

theorem disjointDom_iff {M N : ℕ} :
    disjointDom d M N = true ↔ ∀ a < d, dig M a = 0 ∨ dig N a = 0 := by
  simp [disjointDom]

theorem toEnd_union_neg {M N : ℕ} (h : disjointDom d M N = true) :
    toEnd R d (union d M (neg d N)) = toEnd R d M - toEnd R d N := by
  have hdisj : ∀ a < d, dig M a = 0 ∨ dig (neg d N) a = 0 := fun a ha => by
    rcases disjointDom_iff.1 h a ha with h0 | h0
    · exact Or.inl h0
    · right
      rw [dig_neg N ha, h0, negDigit, ite_eq_left rfl]
  rw [toEnd_union hdisj, toEnd_neg]
  exact (sub_eq_add_neg (toEnd R d M) (toEnd R d N)).symm

@[expose] def IsSPerm (d P : ℕ) : Prop :=
  (∀ a < d, 2 ≤ dig P a ∧ dig P a / 2 - 1 < d) ∧
    ∀ a < d, ∀ b < d, dig P a / 2 = dig P b / 2 → a = b

namespace IsSPerm

variable {P : ℕ} (hP : IsSPerm d P)
include hP

theorem wf : WF d P := fun a ha => Or.inr (hP.1 a ha)

@[expose] def perm : Equiv.Perm (Fin d) :=
  Equiv.ofBijective (fun a : Fin d => ⟨dig P a / 2 - 1, (hP.1 a a.2).2⟩)
    (Finite.injective_iff_bijective.1 fun a b h => Fin.ext <| hP.2 a a.2 b b.2 <| by
      have := congrArg Fin.val h
      have := (hP.1 a a.2).1
      have := (hP.1 b b.2).1
      simp only at *
      omega)

theorem perm_val (a : Fin d) : (hP.perm a : ℕ) = dig P a / 2 - 1 := rfl

theorem toEnd_single (a : Fin d) :
    toEnd R d P (Finsupp.single a 1) = (-1 : R) ^ dig P a • Finsupp.single (hP.perm a) 1 := by
  rw [Minuscule.toEnd_single, digVec_of_le (hP.1 a a.2).1 (hP.1 a a.2).2]
  rfl

theorem inv_eq :
    inv d P = ofDigits d fun b => if h : b < d then
      2 * ((hP.perm.symm ⟨b, h⟩ : ℕ) + 1) + dig P (hP.perm.symm ⟨b, h⟩) % 2 else 0 := by
  rw [inv, sum_map_range_eq_sum_fin, ofDigits_eq_sum]
  refine (Fintype.sum_equiv hP.perm _ _ fun a => ?_)
  rw [dite_eq_left (hP.perm a).2, Fin.eta, Equiv.symm_apply_apply, perm_val]

theorem dig_inv (hd : d ≤ 127) (b : Fin d) :
    dig (inv d P) b = 2 * ((hP.perm.symm b : ℕ) + 1) + dig P (hP.perm.symm b) % 2 := by
  have hf : ∀ c < d, (if h : c < d then 2 * ((hP.perm.symm ⟨c, h⟩ : ℕ) + 1) +
      dig P (hP.perm.symm ⟨c, h⟩) % 2 else 0) < 256 := fun c hc => by
    rw [dite_eq_left hc]
    have := (hP.perm.symm ⟨c, hc⟩).2
    omega
  rw [hP.inv_eq, dig_ofDigits hf b.2, dite_eq_left b.2]

theorem toEnd_inv_single (hd : d ≤ 127) (b : Fin d) :
    toEnd R d (inv d P) (Finsupp.single b 1) =
      (-1 : R) ^ dig P (hP.perm.symm b) • Finsupp.single (hP.perm.symm b) 1 := by
  have hb := (hP.perm.symm b).2
  rw [Minuscule.toEnd_single, hP.dig_inv hd, digVec_of_le (by omega) (by omega)]
  have hs : (-1 : R) ^ (2 * ((hP.perm.symm b : ℕ) + 1) + dig P (hP.perm.symm b) % 2) =
      (-1) ^ dig P (hP.perm.symm b) := by
    rw [neg_one_pow_eq_pow_mod_two, neg_one_pow_eq_pow_mod_two (n := dig P _)]
    congr 1
    omega
  rw [hs]
  congr 2
  exact Fin.ext (by simp only; omega)

theorem wf_inv (hd : d ≤ 127) : WF d (inv d P) := fun b hb => by
  have h := hP.dig_inv hd ⟨b, hb⟩
  simp only at h
  rw [h]
  right
  have := (hP.perm.symm ⟨b, hb⟩).2
  omega

theorem toEnd_inv_mul (hd : d ≤ 127) : toEnd R d (inv d P) * toEnd R d P = 1 :=
  ext_single fun a => by
    rw [Module.End.mul_apply, hP.toEnd_single, map_smul, hP.toEnd_inv_single hd,
      Equiv.symm_apply_apply, smul_smul, neg_one_pow_mul_self, one_smul, Module.End.one_apply]

theorem toEnd_mul_inv (hd : d ≤ 127) : toEnd R d P * toEnd R d (inv d P) = 1 :=
  ext_single fun b => by
    rw [Module.End.mul_apply, hP.toEnd_inv_single hd, map_smul, hP.toEnd_single,
      Equiv.apply_symm_apply, smul_smul, neg_one_pow_mul_self, one_smul, Module.End.one_apply]

theorem toEnd_conj (hd : d ≤ 127) {M : ℕ} (hM : WF d M) :
    toEnd R d (conj d P M) = toEnd R d P * toEnd R d M * toEnd R d (inv d P) := by
  rw [conj, toEnd_comp (hP.wf_inv hd), toEnd_comp hM]

end IsSPerm

end CFSG.LieType.Steinberg.Minuscule
