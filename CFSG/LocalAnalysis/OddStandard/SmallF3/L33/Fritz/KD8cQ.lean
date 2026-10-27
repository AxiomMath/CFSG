module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD8cD
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8cCube

public section

namespace CFSG.OddStandard.SmallF3.L33.KD
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace KD8c
open CFSG.ComponentClassification.HSFLit.KD8c

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

theorem pi_d_aux₁ : ∀ b : Fin 8, interCard b 1 = 8 → b ≠ 0 → b ≠ 7 → b = 2 := by decide

theorem pi_d_aux₂ : ∀ b : Fin 8, interCard b 2 = 8 → interCard b 7 = 8 → b ≠ 1 → b = 3 := by
  decide

theorem sig21_sig21 : ∀ i : Fin 8, sig21 (sig21 i) = i := by decide

@[expose] def HasT (t : X) (H : Subgroup X) : Prop := ∃ e ∈ H, ConjTo t e

omit [Finite X] in
theorem exists_pow_eq_one {P : Subgroup X} (hP : IsPGroup 2 P) {g : X} (hg : g ∈ P) :
    ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨g, hg⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

namespace Conf

variable (K : Conf S T₁)

theorem pi_d_4 : K.pi K.normR1_d 4 = 2 := by
  refine pi_d_aux₁ _ ?_ ?_ ?_
  · rw [← K.pi_d_0, K.interCard_pi]; decide
  · rw [← K.pi_d_1]; exact fun h => absurd (K.pi_injective _ h) (by decide)
  · rw [← K.pi_d_6]; exact fun h => absurd (K.pi_injective _ h) (by decide)

theorem pi_d_5 : K.pi K.normR1_d 5 = 3 := by
  refine pi_d_aux₂ _ ?_ ?_ ?_
  · rw [← K.pi_d_4, K.interCard_pi]; decide
  · rw [← K.pi_d_6, K.interCard_pi]; decide
  · rw [← K.pi_d_0]; exact fun h => absurd (K.pi_injective _ h) (by decide)

theorem hasT_pi {n : X} (hn : K.NormR1 n) (i : Fin 8) :
    HasT t (K.Ex (K.pi hn i)) ↔ HasT t (K.Ex i) := by
  constructor
  · rintro ⟨e, he, hc⟩
    rw [← K.pi_spec hn i] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact ⟨f, hf, (conjTo_conj_iff n f).mp hc⟩
  · rintro ⟨e, he, hc⟩
    exact ⟨n * e * n⁻¹, K.conj_mem_pi hn he, (conjTo_conj_iff n e).mpr hc⟩

theorem hasT_0 : HasT t (K.Ex 0) :=
  ⟨t, by rw [← K.E₁_eq]; exact KD46.mem_E_t S _, ⟨1, by group⟩⟩

theorem hasT_1 : HasT t (K.Ex 1) :=
  ⟨t, by rw [← K.E₂_eq]; exact KD46.mem_E_t S _, ⟨1, by group⟩⟩

theorem hasT_4 : HasT t (K.Ex 4) := by
  have := (K.hasT_pi K.normR1_w₂ 1).mpr K.hasT_1
  rwa [K.pi_w₂, show sig21 1 = 4 from rfl] at this

theorem hasT_2 : HasT t (K.Ex 2) := by
  have := (K.hasT_pi K.normR1_d 4).mpr K.hasT_4
  rwa [K.pi_d_4] at this

theorem hasT_5 : HasT t (K.Ex 5) := by
  have := (K.hasT_pi K.normR1_w₂ 2).mpr K.hasT_2
  rwa [K.pi_w₂, show sig21 2 = 5 from rfl] at this

theorem hasT_3 : HasT t (K.Ex 3) := by
  have := (K.hasT_pi K.normR1_d 5).mpr K.hasT_5
  rwa [K.pi_d_5] at this

theorem not_hasT_7 : ¬ HasT t (K.Ex 7) := fun ⟨_, he, hc⟩ => K.not_conjTo_of_mem_F₂ he hc

theorem not_hasT_6 : ¬ HasT t (K.Ex 6) := by
  rw [← K.hasT_pi K.normR1_d 6, K.pi_d_6]
  exact K.not_hasT_7

theorem eq_of_not_hasT {j : Fin 8} (hj : ¬ HasT t (K.Ex j)) : j = 6 ∨ j = 7 := by
  fin_cases j
  · exact absurd K.hasT_0 hj
  · exact absurd K.hasT_1 hj
  · exact absurd K.hasT_2 hj
  · exact absurd K.hasT_3 hj
  · exact absurd K.hasT_4 hj
  · exact absurd K.hasT_5 hj
  · exact Or.inl rfl
  · exact Or.inr rfl

abbrev NR : Subgroup X := normalizer (K.R1 : Set X)

theorem normR1_of_mem {n : X} (hn : n ∈ K.NR) : K.NormR1 n := fun g hg =>
  (mem_normalizer_iff.mp hn g).mp hg

@[expose] noncomputable def pN {n : X} (hn : n ∈ K.NR) (i : Fin 8) : Fin 8 :=
  K.pi (K.normR1_of_mem hn) i

theorem pN_spec {n : X} (hn : n ∈ K.NR) (i : Fin 8) :
    (K.Ex i).map (MulAut.conj n).toMonoidHom = K.Ex (K.pN hn i) := K.pi_spec _ i

theorem conj_mem_pN {n : X} (hn : n ∈ K.NR) {i : Fin 8} {e : X} (he : e ∈ K.Ex i) :
    n * e * n⁻¹ ∈ K.Ex (K.pN hn i) := K.conj_mem_pi _ he

theorem pN_eq_of {n : X} (hn : n ∈ K.NR) {i j : Fin 8} (h : ∀ e ∈ K.Ex i, n * e * n⁻¹ ∈ K.Ex j) :
    K.pN hn i = j := K.pi_eq_of _ h

theorem interCard_pN {n : X} (hn : n ∈ K.NR) (i j : Fin 8) :
    interCard (K.pN hn i) (K.pN hn j) = interCard i j := K.interCard_pi _ i j

theorem pN_injective {n : X} (hn : n ∈ K.NR) : Function.Injective (K.pN hn) := K.pi_injective _

theorem pN_mul {n m : X} (hn : n ∈ K.NR) (hm : m ∈ K.NR) (i : Fin 8) :
    K.pN (mul_mem hn hm) i = K.pN hn (K.pN hm i) := K.pi_mul _ _ i

theorem pN_congr {n m : X} (hn : n ∈ K.NR) (hm : m ∈ K.NR) (h : n = m) (i : Fin 8) :
    K.pN hn i = K.pN hm i := by
  subst h; rfl

theorem pN_one (i : Fin 8) : K.pN (one_mem K.NR) i = i :=
  K.pN_eq_of _ fun e he => by simpa using he

theorem pN_inv {n : X} (hn : n ∈ K.NR) (i : Fin 8) : K.pN (inv_mem hn) (K.pN hn i) = i :=
  (K.pN_mul (inv_mem hn) hn i).symm.trans
    ((K.pN_congr _ (one_mem _) (inv_mul_cancel n) i).trans (K.pN_one i))

theorem pN_inv' {n : X} (hn : n ∈ K.NR) (i : Fin 8) : K.pN hn (K.pN (inv_mem hn) i) = i :=
  (K.pN_mul hn (inv_mem hn) i).symm.trans
    ((K.pN_congr _ (one_mem _) (mul_inv_cancel n) i).trans (K.pN_one i))

theorem pN_pow {n : X} (hn : n ∈ K.NR) (k : ℕ) (i : Fin 8) :
    K.pN (pow_mem hn k) i = (K.pN hn)^[k] i := by
  induction k generalizing i with
  | zero => exact (K.pN_congr _ (one_mem _) (pow_zero n) i).trans (K.pN_one i)
  | succ k ih =>
    rw [K.pN_congr _ (mul_mem (pow_mem hn k) hn) (pow_succ n k) i, K.pN_mul (pow_mem hn k) hn,
      ih, Function.iterate_succ_apply]

theorem hasT_pN {n : X} (hn : n ∈ K.NR) (i : Fin 8) :
    HasT t (K.Ex (K.pN hn i)) ↔ HasT t (K.Ex i) := K.hasT_pi _ i

theorem pN_d6 {n : X} (hn : n ∈ K.NR) : ∃ m : Fin 12, ∀ i, K.pN hn i = d6 m i := by
  refine d6_cases (K.interCard_pN hn) (K.eq_of_not_hasT ?_)
  rw [K.hasT_pN]
  exact K.not_hasT_6

theorem S1_le_NR : K.D₁.S₁ ≤ K.NR := by
  have hc : Nat.card K.D₁.S₁ = 256 := K.P.card_S₁
  have h1 : K.R1.relIndex K.D₁.S₁ = 2 := by
    have := relIndex_mul_card K.R1 K.D₁.S₁
    rw [inf_of_le_left K.R1_le_S1, K.card_R1, hc] at this
    omega
  have : (K.R1.subgroupOf K.D₁.S₁).Normal := Subgroup.normal_of_index_eq_two h1
  exact le_normalizer_of_normal_subgroupOf K.R1_le_S1

theorem T1_le_NR : T₁ ≤ K.NR := by
  have : (K.R1.subgroupOf T₁).Normal := Subgroup.normal_of_index_eq_two K.relIndex_R1
  exact le_normalizer_of_normal_subgroupOf K.R1_le_T₁

theorem w₂_mem_S1 : K.ι MC.w₂ ∈ K.D₁.S₁ := by
  rw [← K.range_ι]; exact ⟨_, rfl⟩

theorem pN_w₂ (h : K.ι MC.w₂ ∈ K.NR) (i : Fin 8) : K.pN h i = sig21 i := K.pi_w₂ i

theorem pN_S1 {s : X} (hs : s ∈ K.D₁.S₁) (h : s ∈ K.NR) : K.pN h 0 = 0 :=
  K.pN_eq_of _ fun e he => by
    rw [← K.E₁_eq] at he ⊢
    exact (mem_normalizer_iff.mp (K.D₁.S₁_le hs) e).mp he

theorem pN_S1_3 {s : X} (hs : s ∈ K.D₁.S₁) (h : s ∈ K.NR) : K.pN h 3 = 3 := by
  rcases K.mem_S1_cases hs with hR | hR
  · exact K.pi_of_mem_R1 hR 3
  · have hW := K.S1_le_NR K.w₂_mem_S1
    have hR' := K.S1_le_NR (K.R1_le_S1 hR)
    rw [K.pN_congr h (mul_mem hW hR') (by group), K.pN_mul hW hR', K.pN_w₂]
    rw [show K.pN hR' 3 = 3 from K.pi_of_mem_R1 hR 3]
    rfl

theorem mem_S1_of {P : Subgroup X} (hP : IsPGroup 2 P) (hS : K.D₁.S₁ ≤ P) (hPN : P ≤ K.NR)
    {g : X} (hg : g ∈ P) (h0 : K.pN (hPN hg) 0 = 0) : g ∈ K.D₁.S₁ := by
  have hgE : g ∈ normalizer (S.E S.y : Set X) := by
    refine Sec7.mem_normalizer_of_map_eq ?_
    rw [K.E₁_eq, K.pN_spec (hPN hg) 0, h0]
  have hmax := K.D₁.S₁_maximal (P ⊓ normalizer (S.E S.y : Set X)) (hP.to_le inf_le_left)
    (le_inf hS K.D₁.S₁_le) inf_le_right
  rw [← hmax]
  exact ⟨hg, hgE⟩

theorem three_absurd {h : X} (hh : h ∈ K.NR) (h2 : ∃ k : ℕ, h ^ 2 ^ k = 1) {a : Fin 8}
    (ha1 : K.pN hh a ≠ a) (ha3 : K.pN hh (K.pN hh (K.pN hh a)) = a) : False := by
  obtain ⟨k, hk⟩ := h2
  set f := K.pN hh with hf
  have h1 : f^[2 ^ k] a = a := by
    rw [← K.pN_pow hh, K.pN_congr _ (one_mem _) hk a, K.pN_one]
  have hper : ∀ m : ℕ, f^[3 * m] a = a := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [show 3 * (m + 1) = 3 + 3 * m by ring, Function.iterate_add_apply, ih]
      exact ha3
  have hmod : f^[2 ^ k] a = f^[2 ^ k % 3] a := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ k) 3, add_comm, Function.iterate_add_apply,
      hper]
  have hne : 2 ^ k % 3 ≠ 0 := by
    intro h0
    have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_three.dvd_of_dvd_pow h3)
    omega
  have hlt : 2 ^ k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rw [hmod] at h1
  interval_cases hr : 2 ^ k % 3
  · exact hne rfl
  · exact ha1 h1
  · apply ha1
    have h2 : f (f a) = a := h1
    calc f a = f (f (f a)) := by rw [h2]
      _ = a := ha3

theorem pN_cases {P : Subgroup X} (hP : IsPGroup 2 P) (hW : K.ι MC.w₂ ∈ P) (hPN : P ≤ K.NR)
    {g : X} (hg : g ∈ P) : K.pN (hPN hg) 0 = 0 ∨ (∀ i, K.pN (hPN hg) i = antip i) ∨
      ∀ i, K.pN (hPN hg) i = sig21 (antip i) := by
  obtain ⟨m, hm⟩ := K.pN_d6 (hPN hg)
  rcases d6_three m with h0 | h3 | ⟨w, a, ha1, ha3⟩
  · exact Or.inl ((hm 0).trans h0)
  · right
    rcases d6_antip m h3 with h | h
    · exact Or.inl fun i => (hm i).trans (h i)
    · exact Or.inr fun i => (hm i).trans (h i)
  · exfalso
    have hWN := hPN hW
    obtain ⟨h, hhP, hh⟩ : ∃ h : X, ∃ hhP : h ∈ P, ∀ i, K.pN (hPN hhP) i = wd (d6 m) w i := by
      match w with
      | 0 => exact ⟨g, hg, hm⟩
      | 1 =>
        refine ⟨g * g, mul_mem hg hg, fun i => ?_⟩
        refine (K.pN_mul (hPN hg) (hPN hg) i).trans ?_
        simp only [wd, hm]
      | 2 =>
        refine ⟨g * K.ι MC.w₂, mul_mem hg hW, fun i => ?_⟩
        refine (K.pN_mul (hPN hg) hWN i).trans ?_
        simp only [wd, hm, K.pN_w₂]
      | 3 =>
        refine ⟨g * K.ι MC.w₂ * (g * K.ι MC.w₂), mul_mem (mul_mem hg hW) (mul_mem hg hW),
          fun i => ?_⟩
        refine (K.pN_mul (mul_mem (hPN hg) hWN) (mul_mem (hPN hg) hWN) i).trans ?_
        rw [K.pN_mul (hPN hg) hWN, K.pN_mul (hPN hg) hWN]
        simp only [wd, hm, K.pN_w₂]
    refine K.three_absurd (hPN hhP) (exists_pow_eq_one hP hhP) (a := a) ?_ ?_
    · rwa [hh]
    · rwa [hh, hh, hh]

theorem exists_max : ∃ P : Subgroup X, IsPGroup 2 P ∧ K.D₁.S₁ ≤ P ∧ P ≤ K.NR ∧
    ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → Q ≤ K.NR → Q = P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (K.D₁.S₁.subgroupOf K.NR) :=
    K.D₁.isPGroup_S₁.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hS'.exists_le_sylow
  refine ⟨(Q : Subgroup K.NR).map K.NR.subtype, Q.isPGroup'.map _, fun x hx =>
    ⟨⟨x, K.S1_le_NR hx⟩, hQ hx, rfl⟩, map_subtype_le _, fun R hR hle hRN => ?_⟩
  have hR' : IsPGroup 2 (R.subgroupOf K.NR) := hR.comap_of_injective _ (subtype_injective _)
  have hQR : (Q : Subgroup K.NR) ≤ R.subgroupOf K.NR := fun x hx => hle ⟨x, hx, rfl⟩
  rw [← Q.is_maximal' hR' hQR, subgroupOf_map_subtype, inf_of_le_left hRN]

theorem not_max_S1 (hmax : ∀ Q : Subgroup X, IsPGroup 2 Q → K.D₁.S₁ ≤ Q → Q ≤ K.NR →
    Q = K.D₁.S₁) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Ps : Sylow 2 K.NR :=
    { toSubgroup := K.D₁.S₁.subgroupOf K.NR
      isPGroup' := K.D₁.isPGroup_S₁.comap_of_injective _ (subtype_injective _)
      is_maximal' := fun {Q} hQ hle => by
        have h := hmax (Q.map K.NR.subtype) (hQ.map _)
          (fun x hx => ⟨⟨x, K.S1_le_NR hx⟩, hle hx, rfl⟩) (map_subtype_le _)
        rw [← h]
        exact (comap_map_eq_self_of_injective (subtype_injective _) Q).symm }
  have hT' : IsPGroup 2 (T₁.subgroupOf K.NR) :=
    K.h4.isPGroup.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K.NR Q Ps
  have hdN : C.d ∈ K.NR := K.T1_le_NR (d_mem_T₁ K)
  have hdQ : (⟨C.d, hdN⟩ : K.NR) ∈ (Q : Subgroup K.NR) := hQ (d_mem_T₁ K)
  have hgd : g * ⟨C.d, hdN⟩ * g⁻¹ ∈ (Ps : Subgroup K.NR) := by
    rw [← hg, Sylow.coe_subgroup_smul]
    exact ⟨_, hdQ, rfl⟩
  have he : (g : X) * C.d * (g : X)⁻¹ ∈ K.D₁.S₁ := hgd
  have hn := g.2
  have h1 := K.pN_S1 he (mul_mem (mul_mem hn hdN) (inv_mem hn))
  rw [K.pN_mul (mul_mem hn hdN) (inv_mem hn), K.pN_mul hn hdN] at h1
  have h3 := K.pN_inv' hn 0
  exact K.pi_d_ne _ (K.pN_injective hn (h1.trans h3.symm))

structure T2 (K : Conf S T₁) where
  P : Subgroup X
  isPGroup : IsPGroup 2 P
  S1_le : K.D₁.S₁ ≤ P
  le_NR : P ≤ K.NR
  maximal : ∀ Q : Subgroup X, IsPGroup 2 Q → P ≤ Q → Q ≤ K.NR → Q = P
  q : X
  q_mem : q ∈ P
  pN_q : ∀ i, K.pN (le_NR q_mem) i = antip i

theorem nonempty_T2 : Nonempty (T2 K) := by
  obtain ⟨P, hP, hS, hPN, hmax⟩ := K.exists_max
  have hne : ¬ P ≤ K.D₁.S₁ := by
    intro hle
    have hPS : P = K.D₁.S₁ := le_antisymm hle hS
    apply K.not_max_S1
    intro Q hQ hSQ hQN
    rw [← hPS] at hSQ ⊢
    exact hmax Q hQ hSQ hQN
  obtain ⟨g, hg, hgS⟩ := IsConcreteLE.not_le_iff_exists.mp hne
  have hW : K.ι MC.w₂ ∈ P := hS K.w₂_mem_S1
  rcases K.pN_cases hP hW hPN hg with h0 | ha | hsa
  · exact absurd (K.mem_S1_of hP hS hPN hg h0) hgS
  · exact ⟨⟨P, hP, hS, hPN, hmax, g, hg, ha⟩⟩
  · refine ⟨⟨P, hP, hS, hPN, hmax, K.ι MC.w₂ * g, mul_mem hW hg, fun i => ?_⟩⟩
    refine (K.pN_mul (hPN hW) (hPN hg) i).trans ?_
    rw [hsa, K.pN_w₂, sig21_sig21]

end Conf

end KD8c

end CFSG.OddStandard.SmallF3.L33.KD
