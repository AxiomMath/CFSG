module

public import CFSG.GH74.GLS.C3.Layer1.St1P89D8
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.GH74.GLS.C3.Layer1.P89

section DA

variable {G : Type} [Group G] [Finite G] {T P Q S : Subgroup G} {u z x f r s a : G}

theorem exists_central_inv_of_normal (hT2 : IsPGroup 2 ↥T) {N : Subgroup G} (hNT : N ≤ T)
    (hN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) {g : G} (hg : g ∈ N) (hg1 : g ≠ 1) :
    ∃ w ∈ N, w ≠ 1 ∧ w ^ 2 = 1 ∧ ∀ t ∈ T, t * w = w * t := by
  classical
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  let N' : Subgroup ↥T := N.subgroupOf T
  have : N'.Normal := ⟨fun n hn t => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hN t t.2 n hn⟩
  have hN'ne : N' ≠ ⊥ := by
    intro h
    have : (⟨g, hNT hg⟩ : ↥T) ∈ N' := Subgroup.mem_subgroupOf.mpr hg
    rw [h, Subgroup.mem_bot] at this
    exact hg1 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  obtain ⟨⟨v, hvN, hvc⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hvc' : ∀ t : ↥T, t * v = v * t := fun t => by
    have := Subgroup.mem_center_iff.mp hvc t
    exact this
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvN' : (v : G) ∈ N := Subgroup.mem_subgroupOf.mp hvN
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) v
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
    exact hv1' hk
  have hdvd : 2 ^ (k - 1) ∣ orderOf v := by rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have hord : orderOf (v ^ 2 ^ (k - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk]
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  refine ⟨((v ^ 2 ^ (k - 1) : ↥T) : G), N.pow_mem hvN' _, ?_, ?_, ?_⟩
  · intro h
    have : v ^ 2 ^ (k - 1) = 1 := Subtype.ext h
    rw [this, orderOf_one] at hord
    omega
  · have : (v ^ 2 ^ (k - 1)) ^ 2 = 1 := by
      have h2 := pow_orderOf_eq_one (v ^ 2 ^ (k - 1))
      rwa [hord] at h2
    exact congrArg Subtype.val this
  · intro t ht
    have := ((Commute.pow_right (show Commute (⟨t, ht⟩ : ↥T) v from hvc' ⟨t, ht⟩) (2 ^ (k - 1)))).eq
    exact congrArg Subtype.val this

theorem Cfg89S.a_inv_mem (sc : Cfg89S G T u S a) : a⁻¹ ∈ S := S.inv_mem sc.a_mem

theorem Cfg89S.aa_mem (sc : Cfg89S G T u S a) : a * a ∈ T := by
  rcases sc.S_split (a * a) (S.mul_mem sc.a_mem sc.a_mem) with h | h
  · exact h
  · exfalso
    apply sc.a_nmem
    simpa using h

theorem Cfg89S.conj_mem (sc : Cfg89S G T u S a) {t : G} (ht : t ∈ T) : a * t * a⁻¹ ∈ T :=
  sc.T_norm a sc.a_mem t ht

theorem Cfg89S.conj_inv_mem (sc : Cfg89S G T u S a) {t : G} (ht : t ∈ T) : a⁻¹ * t * a ∈ T := by
  have := sc.T_norm a⁻¹ sc.a_inv_mem t ht
  simpa using this

theorem Cfg89S.conjSub_le (sc : Cfg89S G T u S a) {H : Subgroup G} (hH : H ≤ T) : conjSub a H ≤ T := by
  intro g hg
  obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hg
  exact sc.conj_mem (hH hh)

theorem Cfg89S.conjSub_norm (sc : Cfg89S G T u S a) {H : Subgroup G} (hn : ∀ t ∈ T, ∀ h ∈ H, t * h * t⁻¹ ∈ H) :
    ∀ t ∈ T, ∀ g ∈ conjSub a H, t * g * t⁻¹ ∈ conjSub a H := by
  intro t ht g hg
  obtain ⟨h, hh, rfl⟩ := mem_conjSub.mp hg
  refine mem_conjSub.mpr ⟨(a⁻¹ * t * a) * h * (a⁻¹ * t * a)⁻¹, hn _ (sc.conj_inv_mem ht) h hh, ?_⟩
  group

theorem Cfg89S.u_a_ne (sc : Cfg89S G T u S a) : a * u * a⁻¹ ≠ u := by
  intro h
  apply sc.a_nmem
  apply sc.T_cent a sc.a_mem
  calc a * u = a * u * a⁻¹ * a := by group
    _ = u * a := by rw [h]

theorem Cfg89S.u_a_central (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a) {t : G} (ht : t ∈ T) :
    t * (a * u * a⁻¹) = (a * u * a⁻¹) * t := by
  have h := c.u_central (a⁻¹ * t * a) (sc.conj_inv_mem ht)
  calc t * (a * u * a⁻¹) = a * ((a⁻¹ * t * a) * u) * a⁻¹ := by group
    _ = a * (u * (a⁻¹ * t * a)) * a⁻¹ := by rw [h]
    _ = (a * u * a⁻¹) * t := by group

theorem Cfg89T.inv_cases_of_ZTQ (c : Cfg89T G T P Q u z x f r s) {w : G} (hw : w ∈ T) (hw2 : w ^ 2 = 1)
    (hc : ∀ t' ∈ T, w * t' * w⁻¹ * t'⁻¹ ∈ Q) : w = 1 ∨ w = u ∨ w = z ∨ w = u * z := by
  have hzT : z ∈ T := c.P_le c.z_mem
  obtain ⟨i, q, hq, hwq⟩ := c.ZTQ w hw hc
  have hzq : Commute z q := c.PQ_comm z c.z_mem q hq
  have hsq : q ^ 2 = 1 := by
    have h1 : w ^ 2 = (z ^ i) ^ 2 * q ^ 2 := by rw [hwq]; exact ((hzq.pow_left i).mul_pow 2)
    have hz2i : (z ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, c.z_sq, one_pow]
    rw [h1, hz2i, one_mul] at hw2; exact hw2
  rw [hwq, pow_eq_pow_mod i c.z_sq]
  have hi : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  generalize i % 2 = b at hi
  interval_cases b <;> rcases c.Q_inv q hq hsq with rfl | rfl <;> simp [c.u_central z hzT]

theorem Cfg89T.central_inv_cases (c : Cfg89T G T P Q u z x f r s) {w : G} (hw : w ∈ T) (hw2 : w ^ 2 = 1)
    (hc : ∀ t ∈ T, t * w = w * t) : w = 1 ∨ w = u ∨ w = z ∨ w = u * z :=
  c.inv_cases_of_ZTQ hw hw2 (fun t' ht' => by
    have : w * t' * w⁻¹ * t'⁻¹ = 1 := by rw [← hc t' ht']; group
    rw [this]; exact Q.one_mem)

theorem Cfg89T.u_a_cases (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a) :
    a * u * a⁻¹ = z ∨ a * u * a⁻¹ = u * z := by
  have hw : a * u * a⁻¹ ∈ T := sc.conj_mem (c.Q_le c.u_mem)
  have hw2 : (a * u * a⁻¹) ^ 2 = 1 := by
    rw [conj_pow, c.u2]; group
  rcases c.central_inv_cases hw hw2 (fun t ht => Cfg89S.u_a_central c sc ht) with h | h | h | h
  · exfalso
    have : u = 1 := by
      calc u = a⁻¹ * (a * u * a⁻¹) * a := by group
        _ = 1 := by rw [h]; group
    exact c.u_ne this
  · exact absurd h sc.u_a_ne
  · exact Or.inl h
  · exact Or.inr h

omit [Finite G] in
theorem exists_inv_pow (hT2 : IsPGroup 2 ↥T) {g : G} (hg : g ∈ T) (hg1 : g ≠ 1) :
    ∃ k : ℕ, (g ^ k) ^ 2 = 1 ∧ g ^ k ≠ 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) (⟨g, hg⟩ : ↥T)
  have hk' : orderOf g = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk g hg).symm
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk'
    exact hg1 hk'
  have hdvd : 2 ^ (k - 1) ∣ orderOf g := by rw [hk']; exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have hord : orderOf (g ^ 2 ^ (k - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk']
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  refine ⟨2 ^ (k - 1), ?_, ?_⟩
  · have h2 := pow_orderOf_eq_one (g ^ 2 ^ (k - 1))
    rwa [hord] at h2
  · intro h
    rw [h, orderOf_one] at hord
    omega

omit [Finite G] in
theorem commute_of_inf_trivial {H K : Subgroup G} (hHT : H ≤ T) (hKT : K ≤ T)
    (hH : ∀ t ∈ T, ∀ h ∈ H, t * h * t⁻¹ ∈ H) (hK : ∀ t ∈ T, ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hinf : ∀ g : G, g ∈ H → g ∈ K → g = 1) {h k : G} (hh : h ∈ H) (hk : k ∈ K) :
    h * k = k * h := by
  have h1 : h * k * h⁻¹ * k⁻¹ ∈ K := K.mul_mem (hK h (hHT hh) k hk) (K.inv_mem hk)
  have h2 : h * (k * h⁻¹ * k⁻¹) ∈ H := H.mul_mem hh (hH k (hKT hk) h⁻¹ (H.inv_mem hh))
  have h3 : h * k * h⁻¹ * k⁻¹ = 1 := hinf _ (by simpa [mul_assoc] using h2) h1
  calc h * k = (h * k * h⁻¹ * k⁻¹) * (k * h) := by group
    _ = k * h := by rw [h3, one_mul]

theorem Cfg89T.Q_inf_Qa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a) {g : G} (hg : g ∈ Q)
    (hga : g ∈ conjSub a Q) : g = 1 := by
  by_contra hg1
  obtain ⟨k, hk2, hk1⟩ := exists_inv_pow c.T_two (c.Q_le hg) hg1
  have hgk : g ^ k ∈ Q := Q.pow_mem hg k
  have hgka : g ^ k ∈ conjSub a Q := (conjSub a Q).pow_mem hga k
  have hu : g ^ k = u := by
    rcases c.Q_inv _ hgk hk2 with h | h
    · exact absurd h hk1
    · exact h
  obtain ⟨q, hq, hqe⟩ := mem_conjSub.mp hgka
  have hq2 : q ^ 2 = 1 := by
    have h1 : (g ^ k) ^ 2 = a * q ^ 2 * a⁻¹ := by rw [hqe, conj_pow]
    rw [hk2] at h1
    have h2 : q ^ 2 = a⁻¹ * 1 * a := by rw [h1]; group
    simpa using h2
  rcases c.Q_inv q hq hq2 with h | h
  · apply hk1
    rw [hqe, h]; group
  · apply sc.u_a_ne
    calc a * u * a⁻¹ = a * q * a⁻¹ := by rw [h]
      _ = g ^ k := hqe.symm
      _ = u := hu

theorem Cfg89T.exists_sq_eq_u (c : Cfg89T G T P Q u z x f r s) (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) :
    ∃ q4 ∈ Q, q4 ^ 2 = u := by
  obtain ⟨q, hq, hq1, hqu⟩ := hQ
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp c.T_two) (⟨q, c.Q_le hq⟩ : ↥T)
  have hk' : orderOf q = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk q (c.Q_le hq)).symm
  have hk2 : 2 ≤ k := by
    by_contra hlt
    interval_cases k
    · simp at hk'; exact hq1 hk'
    · have : q ^ 2 = 1 := by have h2 := pow_orderOf_eq_one q; rwa [hk'] at h2
      rcases c.Q_inv q hq this with h | h
      · exact hq1 h
      · exact hqu h
  have hdvd : 2 ^ (k - 1) ∣ orderOf q := by rw [hk']; exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have hord : orderOf (q ^ 2 ^ (k - 1)) = 2 := by
    rw [orderOf_pow_of_dvd (by positivity) hdvd, hk']
    have : 2 ^ k = 2 ^ (k - 1) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
    exact Nat.mul_div_cancel_left 2 (by positivity)
  have hsq : (q ^ 2 ^ (k - 2)) ^ 2 = q ^ 2 ^ (k - 1) := by
    rw [← pow_mul]
    congr 1
    have : 2 ^ (k - 1) = 2 ^ (k - 2) * 2 := by
      rw [← pow_succ]; congr 1; omega
    rw [this]
  refine ⟨q ^ 2 ^ (k - 2), Q.pow_mem hq _, ?_⟩
  rw [hsq]
  have hmem : q ^ 2 ^ (k - 1) ∈ Q := Q.pow_mem hq _
  have hsq1 : (q ^ 2 ^ (k - 1)) ^ 2 = 1 := by
    have h2 := pow_orderOf_eq_one (q ^ 2 ^ (k - 1))
    rwa [hord] at h2
  rcases c.Q_inv _ hmem hsq1 with h | h
  · rw [h, orderOf_one] at hord; omega
  · exact h

omit [Finite G] in
theorem sq_mul_pow_mem {N : Subgroup G} (hN : ∀ t ∈ T, ∀ n ∈ N, t * n * t⁻¹ ∈ N) {y : G} (hy : y ∈ T)
    (hy2 : y ^ 2 = 1) {q : G} (hq : q ∈ N) (j : ℕ) : (q * y ^ j) ^ 2 ∈ N := by
  have hfi : y ^ j * y ^ j = 1 := by rw [← pow_add, ← two_mul, pow_mul, hy2, one_pow]
  have hq'' : y ^ j * q * (y ^ j)⁻¹ ∈ N := hN (y ^ j) (T.pow_mem hy j) q hq
  have : (q * y ^ j) ^ 2 = q * (y ^ j * q * (y ^ j)⁻¹) * (y ^ j * y ^ j) := by rw [sq]; group
  rw [this, hfi, mul_one]
  exact N.mul_mem hq hq''

theorem sq_qf_mem_Q (c : Cfg89T G T P Q u z x f r s) {q : G} (hq : q ∈ Q) (j : ℕ) :
    (q * f ^ j) ^ 2 ∈ Q := sq_mul_pow_mem c.Q_norm c.f_mem c.f2 hq j

theorem Cfg89T.sq_mem_Q_of_cent (c : Cfg89T G T P Q u z x f r s) {t : G} (ht : t ∈ T)
    (hc : ∀ p ∈ P, t * p = p * t) : t ^ 2 ∈ Q := by
  obtain ⟨i, q, hq, j, rfl⟩ := c.CTP t ht hc
  have hyT : q * f ^ j ∈ T := T.mul_mem (c.Q_le hq) (T.pow_mem c.f_mem j)
  have hzc : Commute (z ^ i) (q * f ^ j) := by
    have := c.z_central (q * f ^ j) hyT
    exact (Commute.pow_left (show Commute z (q * f ^ j) from this.symm) i)
  have hz2 : (z ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, c.z_sq, one_pow]
  have e : (z ^ i * q * f ^ j) ^ 2 = (z ^ i) ^ 2 * (q * f ^ j) ^ 2 := by
    rw [mul_assoc]; exact hzc.mul_pow 2
  rw [e, hz2, one_mul]
  exact sq_qf_mem_Q c hq j

theorem Cfg89S.conj_conj (sc : Cfg89S G T u S a) {h : G} (hz : ∀ t ∈ T, t * h = h * t) :
    a * (a * h * a⁻¹) * a⁻¹ = h := by
  have := hz (a * a) sc.aa_mem
  calc a * (a * h * a⁻¹) * a⁻¹ = (a * a) * h * (a * a)⁻¹ := by group
    _ = h := by rw [this]; group

theorem Cfg89T.z_not_mem_Pa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : z ∉ conjSub a P := by
  intro hzPa
  have hd := (c.isD8).conj a
  have hzcomm : ∀ p' ∈ conjSub a P, z * p' = p' * z := fun p' hp' =>
    (c.z_central p' (sc.conjSub_le c.P_le hp')).symm
  have hz_eq : z = a * z * a⁻¹ := by
    rcases hd.P_center hzPa hzcomm with h | h
    · exact absurd h c.z_ne_one
    · exact h
  have hua : a * u * a⁻¹ = u * z := by
    rcases c.u_a_cases sc with h | h
    · exfalso
      apply c.u_ne_z
      have h1 := Cfg89S.conj_conj sc (h := u) c.u_central
      rw [h] at h1
      calc u = a * z * a⁻¹ := h1.symm
        _ = z := hz_eq.symm
    · exact h
  have hQaP : ∀ g : G, g ∈ conjSub a Q → g ∈ P → g = 1 := by
    intro g hgQa hgP
    by_contra hg1
    obtain ⟨k, hk2, hk1⟩ := exists_inv_pow c.T_two (sc.conjSub_le c.Q_le hgQa) hg1
    have hgk : g ^ k ∈ conjSub a Q := (conjSub a Q).pow_mem hgQa k
    have hgkP : g ^ k ∈ P := P.pow_mem hgP k
    obtain ⟨q, hq, hqe⟩ := mem_conjSub.mp hgk
    have hq2 : q ^ 2 = 1 := by
      have h1 : (g ^ k) ^ 2 = a * q ^ 2 * a⁻¹ := by rw [hqe, conj_pow]
      rw [hk2] at h1
      have h2 : q ^ 2 = a⁻¹ * 1 * a := by rw [h1]; group
      simpa using h2
    rcases c.Q_inv q hq hq2 with h | h
    · apply hk1; rw [hqe, h]; group
    · rw [h, hua] at hqe
      apply c.u_ne
      have huP : u ∈ P := by
        have : u = (g ^ k) * z⁻¹ := by rw [hqe]; group
        rw [this]; exact P.mul_mem hgkP (P.inv_mem c.z_mem)
      exact c.PQ_inf u huP c.u_mem
  have hcomm : ∀ q' ∈ conjSub a Q, ∀ p ∈ P, q' * p = p * q' := fun q' hq' p hp =>
    (commute_of_inf_trivial c.P_le (sc.conjSub_le c.Q_le) c.P_norm (sc.conjSub_norm c.Q_norm)
      (fun g hg1 hg2 => hQaP g hg2 hg1) hp hq').symm
  obtain ⟨q4, hq4, hq4sq⟩ := c.exists_sq_eq_u hQ
  have h1 : a * q4 * a⁻¹ ∈ conjSub a Q := conj_mem_conjSub hq4
  have h2 : (a * q4 * a⁻¹) ^ 2 ∈ Q := c.sq_mem_Q_of_cent (sc.conjSub_le c.Q_le h1) (hcomm _ h1)
  rw [conj_pow, hq4sq, hua] at h2
  apply c.z_ne_one
  exact c.PQ_inf z c.z_mem (by
    have : z = u⁻¹ * (u * z) := by group
    rw [this]; exact Q.mul_mem (Q.inv_mem c.u_mem) h2)

theorem Cfg89T.P_inf_Pa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : ∀ g : G, g ∈ P → g ∈ conjSub a P → g = 1 := by
  intro g hgP hgPa
  by_contra hg1
  have hNT : P ⊓ conjSub a P ≤ T := inf_le_left.trans c.P_le
  have hN : ∀ t ∈ T, ∀ n ∈ P ⊓ conjSub a P, t * n * t⁻¹ ∈ P ⊓ conjSub a P := fun t ht n hn =>
    Subgroup.mem_inf.mpr ⟨c.P_norm t ht n (Subgroup.mem_inf.mp hn).1,
      sc.conjSub_norm c.P_norm t ht n (Subgroup.mem_inf.mp hn).2⟩
  obtain ⟨w, hwN, hw1, hw2, hwc⟩ := exists_central_inv_of_normal c.T_two hNT hN
    (Subgroup.mem_inf.mpr ⟨hgP, hgPa⟩) hg1
  have hwP := (Subgroup.mem_inf.mp hwN).1
  have hwPa := (Subgroup.mem_inf.mp hwN).2
  rcases c.central_inv_cases (hNT hwN) hw2 hwc with h | h | h | h
  · exact hw1 h
  · have : u ∈ P := by rw [← h]; exact hwP
    exact c.u_ne (c.PQ_inf u this c.u_mem)
  · exact c.z_not_mem_Pa sc hQ (by rw [← h]; exact hwPa)
  · have h' : u * z ∈ P := by rw [← h]; exact hwP
    have : u ∈ P := by
      have : u = (u * z) * z⁻¹ := by group
      rw [this]; exact P.mul_mem h' (P.inv_mem c.z_mem)
    exact c.u_ne (c.PQ_inf u this c.u_mem)

theorem Cfg89T.P_Pa_comm (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : ∀ p ∈ P, ∀ p' ∈ conjSub a P, p * p' = p' * p := fun _ hp _ hp' =>
  commute_of_inf_trivial c.P_le (sc.conjSub_le c.P_le) c.P_norm (sc.conjSub_norm c.P_norm)
    (fun g h1 h2 => c.P_inf_Pa sc hQ g h1 h2) hp hp'

theorem Cfg89T.aza (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : a * z * a⁻¹ = u := by
  have hr' : a * r * a⁻¹ ∈ conjSub a P := conj_mem_conjSub c.r_mem
  have hrT : a * r * a⁻¹ ∈ T := sc.conjSub_le c.P_le hr'
  have hcomm : ∀ p ∈ P, (a * r * a⁻¹) * p = p * (a * r * a⁻¹) := fun p hp =>
    (c.P_Pa_comm sc hQ p hp _ hr').symm
  have hsq : (a * r * a⁻¹) ^ 2 ∈ Q := c.sq_mem_Q_of_cent hrT hcomm
  rw [conj_pow, ← c.z_eq] at hsq
  have hz2 : (a * z * a⁻¹) ^ 2 = 1 := by rw [conj_pow, c.z_sq]; group
  rcases c.Q_inv _ hsq hz2 with h | h
  · exfalso; apply c.z_ne_one
    calc z = a⁻¹ * (a * z * a⁻¹) * a := by group
      _ = 1 := by rw [h]; group
  · exact h

theorem Cfg89T.aua (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : a * u * a⁻¹ = z := by
  have h1 := Cfg89S.conj_conj sc (h := z) c.z_central
  rw [c.aza sc hQ] at h1
  exact h1

theorem Cfg89T.isD8_Pa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : IsD8 (conjSub a P) (a * r * a⁻¹) (a * s * a⁻¹) u := by
  have := (c.isD8).conj a
  rwa [c.aza sc hQ] at this

theorem Cfg89T.Q_Pa_sq (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {q : G} (hq : q ∈ Q) (hqPa : q ∈ conjSub a P) : q ^ 2 = 1 := by
  by_contra hq2
  obtain ⟨r', s', hd⟩ : ∃ r' s', IsD8 (conjSub a P) r' s' u := ⟨_, _, c.isD8_Pa sc hQ⟩
  have hr'Q : r' ∈ Q := by
    rcases hd.sq_ne_one hqPa hq2 with h | h
    · rw [← h]; exact hq
    · have h9 : r' ^ 9 = r' := by
        calc r' ^ 9 = (r' ^ 4) ^ 2 * r' := by group
          _ = r' := by rw [hd.r4]; group
      have : r' = q ^ 3 := by rw [h, ← pow_mul]; exact h9.symm
      rw [this]; exact Q.pow_mem hq 3
  have hs'Q : s' ∉ Q := by
    intro h
    rcases c.Q_inv s' h hd.s2 with h1 | h1
    · exact hd.s_ne_one h1
    · exact hd.s_ne_z h1
  have hconj : ∀ t ∈ T, t * s' * t⁻¹ * s'⁻¹ ∈ Q := by
    intro t ht
    have hmem : t * s' * t⁻¹ ∈ conjSub a P := sc.conjSub_norm c.P_norm t ht s' hd.s_mem
    obtain ⟨i, j, hij⟩ := hd.P_gen _ hmem
    rw [pow_eq_pow_mod j hd.s2] at hij
    have hj : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
    generalize j % 2 = b at hj hij
    interval_cases b
    · exfalso
      apply hs'Q
      have h1 : t * s' * t⁻¹ ∈ Q := by rw [hij, pow_zero, mul_one]; exact Q.pow_mem hr'Q i
      have h2 := c.Q_norm t⁻¹ (T.inv_mem ht) _ h1
      have e : t⁻¹ * (t * s' * t⁻¹) * t⁻¹⁻¹ = s' := by group
      rwa [e] at h2
    · have : t * s' * t⁻¹ * s'⁻¹ = r' ^ i := by rw [hij]; group
      rw [this]; exact Q.pow_mem hr'Q i
  have hs'T : s' ∈ T := sc.conjSub_le c.P_le hd.s_mem
  have hZ : ∀ t' ∈ T, s' * t' * s'⁻¹ * t'⁻¹ ∈ Q := by
    intro t' ht'
    have h := Q.inv_mem (hconj t' ht')
    have e : (t' * s' * t'⁻¹ * s'⁻¹)⁻¹ = s' * t' * s'⁻¹ * t'⁻¹ := by group
    rwa [e] at h
  rcases c.inv_cases_of_ZTQ hs'T hd.s2 hZ with h | h | h | h
  · exact hd.s_ne_one h
  · exact hd.s_ne_z h
  · exact c.z_not_mem_Pa sc hQ (by rw [← h]; exact hd.s_mem)
  · apply c.z_not_mem_Pa sc hQ
    have : z = u⁻¹ * s' := by rw [h]; group
    rw [this]
    exact (conjSub a P).mul_mem ((conjSub a P).inv_mem hd.z_mem) hd.s_mem

theorem Cfg89T.exists_inner_Pa (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {q : G} (hq : q ∈ Q) :
    ∃ d ∈ conjSub a P, ∀ p' ∈ conjSub a P, q * p' * q⁻¹ = d * p' * d⁻¹ := by
  obtain ⟨r', s', hd⟩ : ∃ r' s', IsD8 (conjSub a P) r' s' u := ⟨_, _, c.isD8_Pa sc hQ⟩
  have hqT : q ∈ T := c.Q_le hq
  have hcomm : ∀ p' ∈ conjSub a P, q * p' * q⁻¹ = p' ∨ q * p' * q⁻¹ = u * p' := by
    intro p' hp'
    have h1 : q * p' * q⁻¹ * p'⁻¹ ∈ Q := by
      have h := c.Q_norm p' (sc.conjSub_le c.P_le hp') q⁻¹ (Q.inv_mem hq)
      have e : q * p' * q⁻¹ * p'⁻¹ = q * (p' * q⁻¹ * p'⁻¹) := by group
      rw [e]; exact Q.mul_mem hq h
    have h2 : q * p' * q⁻¹ * p'⁻¹ ∈ conjSub a P :=
      (conjSub a P).mul_mem (sc.conjSub_norm c.P_norm q hqT p' hp') ((conjSub a P).inv_mem hp')
    have h3 := c.Q_Pa_sq sc hQ h1 h2
    rcases c.Q_inv _ h1 h3 with h | h
    · left
      calc q * p' * q⁻¹ = (q * p' * q⁻¹ * p'⁻¹) * p' := by group
        _ = p' := by rw [h, one_mul]
    · right
      calc q * p' * q⁻¹ = (q * p' * q⁻¹ * p'⁻¹) * p' := by group
        _ = u * p' := by rw [h]
  have hr : q * r' * q⁻¹ = r' ∨ q * r' * q⁻¹ = r' ^ 3 := by
    rcases hcomm r' hd.r_mem with h | h
    · exact Or.inl h
    · right; rw [h, hd.z_eq]; group
  exact hd.exists_inner hr (hcomm s' hd.s_mem)

theorem Cfg89T.cent_Pa_form (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {t : G} (ht : t ∈ T) (hc : ∀ p' ∈ conjSub a P, t * p' = p' * t) :
    ∃ i : ℕ, ∃ q' ∈ conjSub a Q, ∃ j : ℕ, t = u ^ i * q' * (a * f * a⁻¹) ^ j := by
  have hc' : a⁻¹ * t * a ∈ T := sc.conj_inv_mem ht
  have hcomm : ∀ p ∈ P, (a⁻¹ * t * a) * p = p * (a⁻¹ * t * a) := by
    intro p hp
    have h := hc (a * p * a⁻¹) (conj_mem_conjSub hp)
    calc (a⁻¹ * t * a) * p = a⁻¹ * (t * (a * p * a⁻¹)) * a := by group
      _ = a⁻¹ * ((a * p * a⁻¹) * t) * a := by rw [h]
      _ = p * (a⁻¹ * t * a) := by group
  obtain ⟨i, q, hq, j, hqe⟩ := c.CTP _ hc' hcomm
  refine ⟨i, a * q * a⁻¹, conj_mem_conjSub hq, j, ?_⟩
  have e1 : t = a * (a⁻¹ * t * a) * a⁻¹ := by group
  have e2 : a * (z ^ i * q * f ^ j) * a⁻¹ = (a * z * a⁻¹) ^ i * (a * q * a⁻¹) * (a * f * a⁻¹) ^ j := by
    rw [conj_pow, conj_pow]; group
  rw [e1, hqe, e2, c.aza sc hQ]

theorem Cfg89T.sq_form (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a) (i j : ℕ) {q' : G}
    (hq' : q' ∈ conjSub a Q) : (u ^ i * q' * (a * f * a⁻¹) ^ j) ^ 2 ∈ conjSub a Q := by
  have hyT : a * f * a⁻¹ ∈ T := sc.conj_mem c.f_mem
  have hy2 : (a * f * a⁻¹) ^ 2 = 1 := by rw [conj_pow, c.f2]; group
  have h1 := sq_mul_pow_mem (sc.conjSub_norm c.Q_norm) hyT hy2 hq' j
  have hq'T : q' * (a * f * a⁻¹) ^ j ∈ T :=
    T.mul_mem (sc.conjSub_le c.Q_le hq') (T.pow_mem hyT j)
  have hcm : Commute (u ^ i) (q' * (a * f * a⁻¹) ^ j) :=
    (Commute.pow_left (show Commute u _ from (c.u_central _ hq'T).symm) i)
  have hu2i : (u ^ i) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul, c.u2, one_pow]
  have : (u ^ i * q' * (a * f * a⁻¹) ^ j) ^ 2 = (q' * (a * f * a⁻¹) ^ j) ^ 2 := by
    rw [mul_assoc, hcm.mul_pow, hu2i, one_mul]
  rw [this]; exact h1

omit [Finite G] in
theorem comm_central_left {z a b : G} (hza : Commute z a) (hzb : Commute z b) :
    (z * a) * b * (z * a)⁻¹ * b⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute z (a * b * a⁻¹) := (hza.mul_right hzb).mul_right hza.inv_right
  calc (z * a) * b * (z * a)⁻¹ * b⁻¹ = z * (a * b * a⁻¹) * z⁻¹ * b⁻¹ := by group
    _ = (a * b * a⁻¹) * z * z⁻¹ * b⁻¹ := by rw [hc.eq]
    _ = a * b * a⁻¹ * b⁻¹ := by group

omit [Finite G] in
theorem comm_central_right {z a b : G} (hza : Commute z a) (hzb : Commute z b) :
    a * (z * b) * a⁻¹ * (z * b)⁻¹ = a * b * a⁻¹ * b⁻¹ := by
  have hc : Commute z (a * b * a⁻¹ * b⁻¹) :=
    ((hza.mul_right hzb).mul_right hza.inv_right).mul_right hzb.inv_right
  calc a * (z * b) * a⁻¹ * (z * b)⁻¹ = (a * z) * b * a⁻¹ * b⁻¹ * z⁻¹ := by group
    _ = (z * a) * b * a⁻¹ * b⁻¹ * z⁻¹ := by rw [← hza.eq]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [hc.eq]; group

theorem Cfg89T.comm_form (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    {i1 i2 j1 j2 : ℕ} {q1 q2 : G} (hq1 : q1 ∈ conjSub a Q) (hq2 : q2 ∈ conjSub a Q) :
    (u ^ i1 * q1 * (a * f * a⁻¹) ^ j1) * (u ^ i2 * q2 * (a * f * a⁻¹) ^ j2) *
      (u ^ i1 * q1 * (a * f * a⁻¹) ^ j1)⁻¹ * (u ^ i2 * q2 * (a * f * a⁻¹) ^ j2)⁻¹ ∈ conjSub a Q := by
  set y := a * f * a⁻¹ with hy
  have hyT : y ∈ T := sc.conj_mem c.f_mem
  have hQa := sc.conjSub_norm c.Q_norm
  have hn1 : y ^ j1 * q2 * (y ^ j1)⁻¹ ∈ conjSub a Q := hQa _ (T.pow_mem hyT j1) q2 hq2
  have hn2 : y ^ j2 * q1⁻¹ * (y ^ j2)⁻¹ ∈ conjSub a Q :=
    hQa _ (T.pow_mem hyT j2) q1⁻¹ ((conjSub a Q).inv_mem hq1)
  have hq1T : q1 ∈ T := sc.conjSub_le c.Q_le hq1
  have hq2T : q2 ∈ T := sc.conjSub_le c.Q_le hq2
  have hu : ∀ (i : ℕ) {w : G}, w ∈ T → Commute (u ^ i) w := fun i w hw =>
    Commute.pow_left (show Commute u w from (c.u_central w hw).symm) i
  have hX1 : q1 * y ^ j1 ∈ T := T.mul_mem hq1T (T.pow_mem hyT j1)
  have hX2 : q2 * y ^ j2 ∈ T := T.mul_mem hq2T (T.pow_mem hyT j2)
  have hu1 : Commute (u ^ i1) (q1 * y ^ j1) := hu i1 hX1
  have hu2 : Commute (u ^ i2) (q2 * y ^ j2) := hu i2 hX2
  have hu12 : Commute (u ^ i1) (u ^ i2) := Commute.pow_pow_self u i1 i2
  have hu1' : Commute (u ^ i1) (q2 * y ^ j2) := hu i1 hX2
  have hu2' : Commute (u ^ i2) (q1 * y ^ j1) := hu i2 hX1
  have hy12 : y ^ j2 * (y ^ j1)⁻¹ = (y ^ j1)⁻¹ * y ^ j2 :=
    (Commute.pow_pow_self y j2 j1).inv_right.eq
  have key : (u ^ i1 * q1 * y ^ j1) * (u ^ i2 * q2 * y ^ j2) * (u ^ i1 * q1 * y ^ j1)⁻¹ *
      (u ^ i2 * q2 * y ^ j2)⁻¹ =
      (q1 * (y ^ j1 * q2 * (y ^ j1)⁻¹)) * (y ^ j2 * q1⁻¹ * (y ^ j2)⁻¹) * q2⁻¹ := by
    have e1 : u ^ i1 * q1 * y ^ j1 = u ^ i1 * (q1 * y ^ j1) := by rw [mul_assoc]
    have e2 : u ^ i2 * q2 * y ^ j2 = u ^ i2 * (q2 * y ^ j2) := by rw [mul_assoc]
    rw [e1, e2, comm_central_left hu1 (hu12.mul_right hu1'), comm_central_right hu2' hu2]
    calc q1 * y ^ j1 * (q2 * y ^ j2) * (q1 * y ^ j1)⁻¹ * (q2 * y ^ j2)⁻¹
        = q1 * y ^ j1 * q2 * (y ^ j2 * (y ^ j1)⁻¹) * q1⁻¹ * (y ^ j2)⁻¹ * q2⁻¹ := by group
      _ = q1 * y ^ j1 * q2 * ((y ^ j1)⁻¹ * y ^ j2) * q1⁻¹ * (y ^ j2)⁻¹ * q2⁻¹ := by rw [hy12]
      _ = _ := by group
  rw [key]
  exact (conjSub a Q).mul_mem ((conjSub a Q).mul_mem ((conjSub a Q).mul_mem hq1 hn1) hn2)
    ((conjSub a Q).inv_mem hq2)

theorem Cfg89T.decomp (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {q : G} (hq : q ∈ Q) :
    ∃ d ∈ conjSub a P, ∃ c0 : G, c0 ∈ T ∧ (∀ p' ∈ conjSub a P, c0 * p' = p' * c0) ∧ q = d * c0 ∧
      c0 ^ 2 = 1 ∧ ∃ i : ℕ, ∃ q' ∈ conjSub a Q, ∃ j : ℕ, c0 = u ^ i * q' * (a * f * a⁻¹) ^ j := by
  obtain ⟨d, hd, hdq⟩ := c.exists_inner_Pa sc hQ hq
  have hdT : d ∈ T := sc.conjSub_le c.P_le hd
  have hc0T : d⁻¹ * q ∈ T := T.mul_mem (T.inv_mem hdT) (c.Q_le hq)
  have hc0c : ∀ p' ∈ conjSub a P, (d⁻¹ * q) * p' = p' * (d⁻¹ * q) := by
    intro p' hp'
    have h := hdq p' hp'
    calc d⁻¹ * q * p' = d⁻¹ * (q * p' * q⁻¹) * q := by group
      _ = d⁻¹ * (d * p' * d⁻¹) * q := by rw [h]
      _ = p' * (d⁻¹ * q) := by group
  obtain ⟨i, q', hq', j, hc0e⟩ := c.cent_Pa_form sc hQ hc0T hc0c
  refine ⟨d, hd, d⁻¹ * q, hc0T, hc0c, by group, ?_, i, q', hq', j, hc0e⟩
  obtain ⟨r', s', hD⟩ : ∃ r' s', IsD8 (conjSub a P) r' s' u := ⟨_, _, c.isD8_Pa sc hQ⟩
  have hdc : Commute d (d⁻¹ * q) := (hc0c d hd).symm
  have h1 : q ^ 2 = d ^ 2 * (d⁻¹ * q) ^ 2 := by rw [← hdc.mul_pow, mul_inv_cancel_left]
  have hd2Q : d ^ 2 ∈ Q := by
    rcases hD.sq_mem hd with h | h
    · rw [h]; exact Q.one_mem
    · rw [h]; exact c.u_mem
  have hc2Q : (d⁻¹ * q) ^ 2 ∈ Q := by
    have : (d⁻¹ * q) ^ 2 = (d ^ 2)⁻¹ * q ^ 2 := by rw [h1]; group
    rw [this]; exact Q.mul_mem (Q.inv_mem hd2Q) (Q.pow_mem hq 2)
  have hc2Qa : (d⁻¹ * q) ^ 2 ∈ conjSub a Q := by rw [hc0e]; exact c.sq_form sc i j hq'
  exact c.Q_inf_Qa sc hc2Q hc2Qa

theorem Cfg89T.sq_Q (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {q : G} (hq : q ∈ Q) : q ^ 2 = 1 ∨ q ^ 2 = u := by
  obtain ⟨d, hd, c0, -, hc0c, hqe, hc02, -⟩ := c.decomp sc hQ hq
  obtain ⟨r', s', hD⟩ : ∃ r' s', IsD8 (conjSub a P) r' s' u := ⟨_, _, c.isD8_Pa sc hQ⟩
  have hdc : Commute d c0 := (hc0c d hd).symm
  have : q ^ 2 = d ^ 2 := by rw [hqe, hdc.mul_pow, hc02, mul_one]
  rw [this]; exact hD.sq_mem hd

theorem Cfg89T.Q_comm_of_sq (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) {q1 q2 : G} (hq1 : q1 ∈ Q) (hq2 : q2 ∈ Q) (h1 : q1 ^ 2 = u)
    (h2 : q2 ^ 2 = u) : q1 * q2 = q2 * q1 := by
  obtain ⟨d1, hd1, c1, hc1T, hc1c, hq1e, hc12, i1, q1', hq1', j1, hc1e⟩ := c.decomp sc hQ hq1
  obtain ⟨d2, hd2, c2, hc2T, hc2c, hq2e, hc22, i2, q2', hq2', j2, hc2e⟩ := c.decomp sc hQ hq2
  obtain ⟨r', s', hD⟩ : ∃ r' s', IsD8 (conjSub a P) r' s' u := ⟨_, _, c.isD8_Pa sc hQ⟩
  have hd1sq : d1 ^ 2 = u := by
    rw [← h1, hq1e, (show Commute d1 c1 from (hc1c d1 hd1).symm).mul_pow, hc12, mul_one]
  have hd2sq : d2 ^ 2 = u := by
    rw [← h2, hq2e, (show Commute d2 c2 from (hc2c d2 hd2).symm).mul_pow, hc22, mul_one]
  have hd12 : d1 * d2 = d2 * d1 := by
    rcases hD.sq_eq_z hd1 hd1sq with h | h <;> rcases hD.sq_eq_z hd2 hd2sq with h' | h' <;>
      rw [h, h'] <;> first | rfl | exact (Commute.self_pow r' 3).eq | exact (Commute.pow_self r' 3).eq
  have hq12 : q1 * q2 = d1 * d2 * (c1 * c2) := by
    rw [hq1e, hq2e]
    calc d1 * c1 * (d2 * c2) = d1 * (c1 * d2) * c2 := by group
      _ = d1 * (d2 * c1) * c2 := by rw [hc1c d2 hd2]
      _ = d1 * d2 * (c1 * c2) := by group
  have hq21 : q2 * q1 = d1 * d2 * (c2 * c1) := by
    rw [hq1e, hq2e]
    calc d2 * c2 * (d1 * c1) = d2 * (c2 * d1) * c1 := by group
      _ = d2 * (d1 * c2) * c1 := by rw [hc2c d1 hd1]
      _ = d2 * d1 * (c2 * c1) := by group
      _ = d1 * d2 * (c2 * c1) := by rw [hd12]
  have hdPa : d1 * d2 ∈ conjSub a P := (conjSub a P).mul_mem hd1 hd2
  have hκd : Commute (d1 * d2) (c1 * c2 * c1⁻¹ * c2⁻¹) := by
    have e1 : Commute (d1 * d2) c1 := (hc1c _ hdPa).symm
    have e2 : Commute (d1 * d2) c2 := (hc2c _ hdPa).symm
    exact ((e1.mul_right e2).mul_right e1.inv_right).mul_right e2.inv_right
  have hκ : q1 * q2 * (q2 * q1)⁻¹ = c1 * c2 * c1⁻¹ * c2⁻¹ := by
    rw [hq12, hq21]
    calc d1 * d2 * (c1 * c2) * (d1 * d2 * (c2 * c1))⁻¹
        = (d1 * d2) * (c1 * c2 * c1⁻¹ * c2⁻¹) * (d1 * d2)⁻¹ := by group
      _ = c1 * c2 * c1⁻¹ * c2⁻¹ := by rw [hκd.eq]; group
  have hκQ : c1 * c2 * c1⁻¹ * c2⁻¹ ∈ Q := by
    rw [← hκ]; exact Q.mul_mem (Q.mul_mem hq1 hq2) (Q.inv_mem (Q.mul_mem hq2 hq1))
  have hκQa : c1 * c2 * c1⁻¹ * c2⁻¹ ∈ conjSub a Q := by
    rw [hc1e, hc2e]; exact c.comm_form sc hq1' hq2'
  have hκ1 := c.Q_inf_Qa sc hκQ hκQa
  have hcc : c1 * c2 = c2 * c1 := by
    calc c1 * c2 = (c1 * c2 * c1⁻¹ * c2⁻¹) * (c2 * c1) := by group
      _ = c2 * c1 := by rw [hκ1, one_mul]
  calc q1 * q2 = d1 * d2 * (c1 * c2) := hq12
    _ = d1 * d2 * (c2 * c1) := by rw [hcc]
    _ = q2 * q1 := hq21.symm

theorem Cfg89T.card_Q (c : Cfg89T G T P Q u z x f r s) (sc : Cfg89S G T u S a)
    (hQ : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u) : Nat.card ↥Q = 4 := by
  obtain ⟨q1, hq1, hq11, hq1u⟩ := hQ
  have hQ' : ∃ q ∈ Q, q ≠ 1 ∧ q ≠ u := ⟨q1, hq1, hq11, hq1u⟩
  have hq1sq : q1 ^ 2 = u := by
    rcases c.sq_Q sc hQ' hq1 with h | h
    · rcases c.Q_inv q1 hq1 h with h' | h'
      · exact absurd h' hq11
      · exact absurd h' hq1u
    · exact h
  have hsub : ∀ q ∈ Q, q = 1 ∨ q = u ∨ q = q1 ∨ q = q1 * u := by
    intro q hq
    rcases c.sq_Q sc hQ' hq with h | h
    · rcases c.Q_inv q hq h with h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
    · have hcomm := c.Q_comm_of_sq sc hQ' hq1 hq hq1sq h
      have hsq : (q1⁻¹ * q) ^ 2 = 1 := by
        have hc : Commute q1⁻¹ q := (show Commute q1 q from hcomm).inv_left
        rw [hc.mul_pow, inv_pow, hq1sq, h]
        exact inv_mul_cancel u
      rcases c.Q_inv _ (Q.mul_mem (Q.inv_mem hq1) hq) hsq with h' | h'
      · right; right; left
        calc q = q1 * (q1⁻¹ * q) := by group
          _ = q1 := by rw [h', mul_one]
      · right; right; right
        calc q = q1 * (q1⁻¹ * q) := by group
          _ = q1 * u := by rw [h']
  have hset : (Q : Set G) = {1, u, q1, q1 * u} := by
    ext g
    constructor
    · intro hg
      simpa [Set.mem_insert_iff] using hsub g hg
    · intro hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl | rfl
      · exact Q.one_mem
      · exact c.u_mem
      · exact hq1
      · exact Q.mul_mem hq1 c.u_mem
  have hcard : Nat.card ↥Q = Set.ncard (Q : Set G) := Nat.card_coe_set_eq _
  have hq1u' : q1 * u ≠ 1 := by
    intro h
    apply hq1u
    calc q1 = (q1 * u) * u⁻¹ := by group
      _ = u⁻¹ := by rw [h, one_mul]
      _ = u := by
        rw [inv_eq_iff_mul_eq_one, ← sq]; exact c.u2
  have hne : q1 ≠ q1 * u := by
    intro h
    apply c.u_ne
    exact (mul_eq_left.mp h.symm)
  have n1 : (1 : G) ∉ ({u, q1, q1 * u} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨c.u_ne.symm, hq11.symm, hq1u'.symm⟩
  have n2 : u ∉ ({q1, q1 * u} : Set G) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hq1u.symm, fun h => hq11 (mul_eq_right.mp h.symm)⟩
  rw [hcard, hset, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair hne]

end DA

end CFSG.GH74.GLS.C3.Layer1.P89
