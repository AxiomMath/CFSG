module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreBasic
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreDih

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable (Δ : LocalDatum X A)

omit [Finite X] in
theorem exists_QD {s : X} (hs : s ∈ Δ.S) (hD : Δ.ψe s ∈ Δ.Dbar) :
    ∃ q ∈ Δ.Q, ∃ d ∈ Δ.D, s = q * d := by
  obtain ⟨d, hd, hdψ⟩ := (Δ.mem_Dbar_iff).mp hD
  refine ⟨s * d⁻¹, (Δ.mem_Q_iff).mpr ⟨mul_mem hs (inv_mem (Δ.D_le hd)), ?_⟩, d, hd, by group⟩
  rw [Δ.ψe_mul hs (inv_mem (Δ.D_le hd)), Δ.ψe_inv (Δ.D_le hd), hdψ, mul_inv_cancel]

omit [Finite X] in
theorem QD_unique {q q' d d' : X} (hq : q ∈ Δ.Q) (hq' : q' ∈ Δ.Q) (hd : d ∈ Δ.D)
    (hd' : d' ∈ Δ.D) (h : q * d = q' * d') : q = q' ∧ d = d' := by
  have h1 : q'⁻¹ * q = d' * d⁻¹ := by
    calc q'⁻¹ * q = q'⁻¹ * (q * d) * d⁻¹ := by group
      _ = q'⁻¹ * (q' * d') * d⁻¹ := by rw [h]
      _ = d' * d⁻¹ := by group
  have hQ : q'⁻¹ * q ∈ Δ.Q := mul_mem (inv_mem hq') hq
  have hD : q'⁻¹ * q ∈ Δ.D := h1 ▸ mul_mem hd' (inv_mem hd)
  have h2 := Δ.eq_one_of_mem_Q_D hQ hD
  refine ⟨(inv_mul_eq_one.mp h2).symm, ?_⟩
  rw [h2] at h1
  exact (mul_inv_eq_one.mp h1.symm).symm

theorem exists_pow_sq_eq_t {y : X} (hy : y ∈ Δ.Q) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) :
    ∃ n : ℕ, (y ^ n) ^ 2 = Δ.t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 Δ.Q := Δ.sylow.isPGroup.to_le Δ.Q_le
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨y, hy⟩
  rw [Subgroup.orderOf_mk] at hm
  have hm2 : 2 ≤ m := by
    rcases m with _ | _ | m
    · rw [pow_zero, orderOf_eq_one_iff] at hm
      exact absurd hm hy1
    · exfalso
      rw [pow_one] at hm
      have hy2 : y ^ 2 = 1 := by rw [← hm, pow_orderOf_eq_one]
      exact hyt (Δ.eq_t_of_mem_Q hy hy2 hy1)
    · omega
  refine ⟨2 ^ (m - 2), ?_⟩
  have hinv : (y ^ 2 ^ (m - 2)) ^ 2 ^ 2 = 1 := by
    rw [← pow_mul, ← pow_add, show m - 2 + 2 = m by omega, ← hm, pow_orderOf_eq_one]
  have hne : (y ^ 2 ^ (m - 2)) ^ 2 ≠ 1 := by
    rw [← pow_mul, ← pow_succ]
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [hm] at this
    have := Nat.le_of_dvd (by positivity) this
    have : 2 ^ m ≤ 2 ^ (m - 2 + 1) := this
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    omega
  refine Δ.eq_t_of_mem_Q (pow_mem (pow_mem hy _) _) ?_ hne
  rw [← pow_mul, show 2 * 2 = 2 ^ 2 by norm_num]
  exact hinv

theorem exists_sq_eq_t {y : X} (hy : y ∈ Δ.Q) (hy1 : y ≠ 1) (hyt : y ≠ Δ.t) :
    ∃ q ∈ Δ.Q, q ^ 2 = Δ.t := by
  obtain ⟨n, hn⟩ := Δ.exists_pow_sq_eq_t hy hy1 hyt
  exact ⟨y ^ n, pow_mem hy n, hn⟩

omit [Finite X] in
theorem commute_Q {q q' : X} (hq : q ∈ Δ.Q) (hq' : q' ∈ Δ.Q) : q * q' = q' * q := by
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨b, hb, rfl⟩ := hq'
  have := Δ.isCyclic_ker
  have h := (IsCyclic.commGroup : CommGroup ↥Δ.ψ.ker).mul_comm ⟨a, ha⟩ ⟨b, hb⟩
  exact congrArg (fun v : ↥Δ.ψ.ker => ((v : ↥Δ.S) : X)) h

omit [Finite X] in
theorem eq_of_mem_card_le_two {E : Subgroup A} [Finite E] (hE : Nat.card E ≤ 2) {a b : A}
    (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have hne : E ≠ ⊥ := fun h => ha1 (by rw [h] at ha; exact (mem_bot.mp ha))
  have h2 : Nat.card E = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot E).mpr hne
    omega
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E)).mp h2
  have h1 := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
  have h1' := hy ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h1'.symm)

theorem exists_central_inv_D :
    ∃ z ∈ Δ.D, z ≠ 1 ∧ z ^ 2 = 1 ∧ ∀ s ∈ Δ.S, s * z = z * s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2 : IsPGroup 2 ↥Δ.S := Δ.sylow.isPGroup
  have : Group.IsNilpotent ↥Δ.S := hS2.isNilpotent
  set D' := Δ.D.subgroupOf Δ.S
  have hD'n : D'.Normal := ⟨fun x hx s => by
    rw [mem_subgroupOf] at hx ⊢
    exact Δ.conj_mem_D s s.2 x hx⟩
  have hD'ne : D' ≠ ⊥ := by
    intro h
    have : (⟨Δ.db, Δ.D_le Δ.db_mem⟩ : ↥Δ.S) ∈ D' := mem_subgroupOf.mpr Δ.db_mem
    rw [h, mem_bot] at this
    exact Δ.db_ne_one (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hD'ne
  have h2 : IsPGroup 2 ↥(D' ⊓ center ↥Δ.S) := hS2.to_subgroup _
  have hnt : Nontrivial ↥(D' ⊓ center ↥Δ.S) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨n, hn⟩ := h2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card (α := ↥(D' ⊓ center ↥Δ.S))).ne' hn
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [hn]; exact dvd_pow_self 2 hn0)
  obtain ⟨huD, huZ⟩ := mem_inf.mp u.2
  refine ⟨((u : ↥Δ.S) : X), mem_subgroupOf.mp huD, ?_, ?_, ?_⟩
  · intro h1
    have : u = 1 := Subtype.ext (Subtype.ext h1)
    rw [this, orderOf_one] at hu
    norm_num at hu
  · have := pow_orderOf_eq_one u
    rw [hu] at this
    exact congrArg (fun v : ↥(D' ⊓ center ↥Δ.S) => ((v : ↥Δ.S) : X)) this
  · intro s hs
    exact (congrArg Subtype.val ((mem_center_iff.mp huZ) ⟨s, hs⟩))

omit [Finite X] in
theorem commute_of_commute_inv {w : X} (hw : ∀ i ∈ Δ.D, i ^ 2 = 1 → w * i = i * w) {d : X}
    (hd : d ∈ Δ.D) : w * d = d * w := by
  obtain ⟨g, rfl⟩ := Δ.exists_dE hd
  have hsr : ∀ j : ZMod Δ.dn, w * Δ.dE (sr j) = Δ.dE (sr j) * w := fun j =>
    hw _ (Δ.dE_mem _) (by rw [← Δ.dE_pow, sr_sq, Δ.dE_one])
  rcases g with j | j
  · rw [r_eq_sr_mul_sr j, Δ.dE_mul]
    calc w * (Δ.dE (sr 0) * Δ.dE (sr j)) = Δ.dE (sr 0) * (w * Δ.dE (sr j)) := by
          rw [← mul_assoc, hsr 0, mul_assoc]
      _ = Δ.dE (sr 0) * Δ.dE (sr j) * w := by rw [hsr j, mul_assoc]
  · exact hsr j

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
