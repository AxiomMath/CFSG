module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD46TE

public section

namespace CFSG.ComponentClassification.HSFLit.KD46

open CFSG Subgroup Equiv L2K L2KD

section Generic

variable {G : Type*} [Group G]

theorem conj_mem_of_cycle {z w s κ g j : G} (hz : z ^ 2 = 1) (hw : w ^ 2 = 1) (hs : s ^ 2 = 1)
    (hκ : κ ^ 2 = 1) (hzw : z * w = w * z) (hzs : z * s = s * z) (hzκ : z * κ = κ * z)
    (hws : w * s = s * w) (hwκ : w * κ = κ * w) (hsκ : s * κ = κ * s) (hgz : g * z * g⁻¹ = w)
    (hgw : g * w * g⁻¹ = z * w) (hgs : g * s * g⁻¹ = s) (hgκ : g * κ * g⁻¹ = κ)
    (hj : j ∈ closure ({z, w, s, κ} : Set G)) :
    j ∈ closure ({z, s, κ} : Set G) ∨ g * j * g⁻¹ ∈ closure ({z, s, κ} : Set G) ∨
      g⁻¹ * j * g ∈ closure ({z, s, κ} : Set G) := by
  obtain ⟨a, b, c, l, ha, hb, -, -, rfl⟩ := mem_closure_four hz hw hs hκ hzw hzs hzκ hws hwκ hsκ hj
  have hzm : z ∈ closure ({z, s, κ} : Set G) := subset_closure (by simp)
  have hsm : s ∈ closure ({z, s, κ} : Set G) := subset_closure (by simp)
  have hκm : κ ∈ closure ({z, s, κ} : Set G) := subset_closure (by simp)
  set f := s ^ c * κ ^ l with hf
  have hfm : f ∈ closure ({z, s, κ} : Set G) := mul_mem (pow_mem hsm _) (pow_mem hκm _)
  have hgs' : g * s ^ c * g⁻¹ = s ^ c := by rw [← conj_pow, hgs]
  have hgκ' : g * κ ^ l * g⁻¹ = κ ^ l := by rw [← conj_pow, hgκ]
  have hgf : g * f * g⁻¹ = f := by
    calc g * f * g⁻¹ = (g * s ^ c * g⁻¹) * (g * κ ^ l * g⁻¹) := by rw [hf]; group
      _ = f := by rw [hgs', hgκ']
  have hgf' : g⁻¹ * f * g = f := by
    calc g⁻¹ * f * g = g⁻¹ * (g * f * g⁻¹) * g := by rw [hgf]
      _ = f := by group
  have hgw' : g⁻¹ * w * g = z := by
    calc g⁻¹ * w * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hgz]
      _ = z := by group
  have hj' : z ^ a * w ^ b * s ^ c * κ ^ l = z ^ a * w ^ b * f := by rw [hf]; group
  rw [hj']
  rcases pow_lt_two_eq (g := w) hb with hb' | hb' <;> rw [hb']
  · left
    rw [mul_one]
    exact mul_mem (pow_mem hzm _) hfm
  right
  rcases pow_lt_two_eq (g := z) ha with ha' | ha' <;> rw [ha']
  · right
    have e : g⁻¹ * (1 * w * f) * g = (g⁻¹ * w * g) * (g⁻¹ * f * g) := by group
    rw [e, hgw', hgf']
    exact mul_mem hzm hfm
  · left
    have hwzw : w * (z * w) = z := by
      calc w * (z * w) = z * (w * w) := by rw [← mul_assoc, ← hzw, mul_assoc]
        _ = z := by rw [← pow_two, hw, mul_one]
    have e : g * (z * w * f) * g⁻¹ = (g * z * g⁻¹) * (g * w * g⁻¹) * (g * f * g⁻¹) := by group
    rw [e, hgz, hgw, hgf, hwzw]
    exact mul_mem hzm hfm

end Generic

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem closure_zk_eq (yi : X) :
    closure ({S.z, yi, t, S.z * S.k} : Set X) = closure ({S.z, yi, t, S.k} : Set X) := by
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have h := mul_mem (inv_mem (subset_closure (show S.z ∈ ({S.z, yi, t, S.z * S.k} : Set X) by
        simp))) (subset_closure (show S.z * S.k ∈ ({S.z, yi, t, S.z * S.k} : Set X) by simp))
      rwa [inv_mul_cancel_left] at h

theorem closure_zk_eq_B : closure ({S.z, t, S.z * S.k} : Set X) = S.B := by
  rw [KDBase.B]
  apply le_antisymm
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · exact mul_mem (subset_closure (by simp)) (subset_closure (by simp))
  · rw [closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact subset_closure (by simp)
    · exact subset_closure (by simp)
    · have h := mul_mem (inv_mem (subset_closure (show S.z ∈ ({S.z, t, S.z * S.k} : Set X) by
        simp))) (subset_closure (show S.z * S.k ∈ ({S.z, t, S.z * S.k} : Set X) by simp))
      rwa [inv_mul_cancel_left] at h

theorem exists_conj_B_of_mem_E₁ {j : X} (hj : j ∈ S.E S.y) :
    ∃ g ∈ centralizer ({t} : Set X), g * j * g⁻¹ ∈ S.B := by
  obtain ⟨g, hgC, -, hgz, hgy, hgk⟩ := S.d_y
  have hgt : g * t * g⁻¹ = t := by rw [mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]
  have hyR := S.y_mem
  rcases conj_mem_of_cycle (z_sq S) S.y_sq (t_sq' (A := A)) (k_sq S) (z_comm_y S) (z_comm_t S)
      (z_comm_k S) (comm_t hyR.1) (k_comm_R S hyR).symm (k_comm_t S).symm hgz hgy hgt hgk
      (show j ∈ closure ({S.z, S.y, t, S.k} : Set X) from hj) with h | h | h
  · exact ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact h⟩
  · exact ⟨g, hgC, h⟩
  · exact ⟨g⁻¹, inv_mem hgC, by rw [inv_inv]; exact h⟩

theorem exists_conj_B_of_mem_E₂ {j : X} (hj : j ∈ S.E (S.x * S.y)) :
    ∃ g ∈ centralizer ({t} : Set X), g * j * g⁻¹ ∈ S.B := by
  obtain ⟨g, hgC, -, hgz, hgy, hgk⟩ := S.d_xy
  have hgt : g * t * g⁻¹ = t := by rw [mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]
  have hxyR := xy_mem S
  have hzk2 : (S.z * S.k) ^ 2 = 1 := B_sq S (mul_mem (mem_B_z S) (mem_B_k S))
  have hzzk : S.z * (S.z * S.k) = S.z * S.k * S.z := by rw [mul_assoc S.z S.k S.z, ← z_comm_k S]
  have hxyzk : S.x * S.y * (S.z * S.k) = S.z * S.k * (S.x * S.y) :=
    (Commute.mul_right (z_comm_xy S).symm (k_comm_R S hxyR).symm).eq
  have htzk : t * (S.z * S.k) = S.z * S.k * t := (comm_t (mul_mem (z_mem_T S) (k_mem_T S))).symm
  have hj' : j ∈ closure ({S.z, S.x * S.y, t, S.z * S.k} : Set X) := by
    rw [closure_zk_eq]
    exact hj
  rcases conj_mem_of_cycle (z_sq S) (xy_sq S) (t_sq' (A := A)) hzk2 (z_comm_xy S) (z_comm_t S)
      hzzk (comm_t hxyR.1) hxyzk htzk hgz hgy hgt hgk hj' with h | h | h <;>
    rw [closure_zk_eq_B] at h
  · exact ⟨1, one_mem _, by rw [one_mul, inv_one, mul_one]; exact h⟩
  · exact ⟨g, hgC, h⟩
  · exact ⟨g⁻¹, inv_mem hgC, by rw [inv_inv]; exact h⟩

theorem mem_E_of_mem_TE {j : X} (hj : j ∈ S.TE) (hj2 : j ^ 2 = 1) :
    j ∈ S.E S.y ∨ j ∈ S.E (S.x * S.y) := by
  obtain ⟨hjT, hjP⟩ := (mem_TE_iff S).mp hj
  have h2 : ψX A j ^ 2 = 1 := by rw [← ψX_pow hjT, hj2, ψX_one]
  rcases mem_PE_of_sq hjP h2 with h | h <;> rcases E_cases S with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl (h1 ▸ mem_pre.mpr ⟨hjT, h⟩)
  · exact Or.inr (h2 ▸ mem_pre.mpr ⟨hjT, h⟩)
  · exact Or.inr (h2 ▸ mem_pre.mpr ⟨hjT, h⟩)
  · exact Or.inl (h1 ▸ mem_pre.mpr ⟨hjT, h⟩)

theorem exists_conj_B_or_out {i : X} (hi : i ∈ centralizer ({t} : Set X)) (hi2 : i ^ 2 = 1) :
    ∃ g ∈ centralizer ({t} : Set X),
      g * i * g⁻¹ ∈ S.B ∨ (g * i * g⁻¹ ∈ A.T ∧ g * i * g⁻¹ ∉ S.TE) := by
  obtain ⟨h, hh, hhT⟩ := exists_conj_le_T (A := A) (isPGroup_zpowers_of_sq hi2)
    (zpowers_le.mpr hi)
  have hjT : h * i * h⁻¹ ∈ A.T := hhT ⟨i, mem_zpowers i, rfl⟩
  have hj2 : (h * i * h⁻¹) ^ 2 = 1 := by rw [conj_pow, hi2]; group
  by_cases hjE : h * i * h⁻¹ ∈ S.TE
  · have key : ∃ g ∈ centralizer ({t} : Set X), g * (h * i * h⁻¹) * g⁻¹ ∈ S.B := by
      rcases mem_E_of_mem_TE S hjE hj2 with hE | hE
      · exact exists_conj_B_of_mem_E₁ S hE
      · exact exists_conj_B_of_mem_E₂ S hE
    obtain ⟨g, hg, hgB⟩ := key
    refine ⟨g * h, mul_mem hg hh, Or.inl ?_⟩
    have e : g * h * i * (g * h)⁻¹ = g * (h * i * h⁻¹) * g⁻¹ := by group
    rw [e]
    exact hgB
  · exact ⟨h, hh, Or.inr ⟨hjT, hjE⟩⟩

theorem exists_conj_d {f : X} (hf : f ∈ A.T) (hfE : f ∉ S.TE) (hf2 : f ^ 2 = 1) :
    ∃ r ∈ A.R, r * f * r⁻¹ = S.d ∨ r * f * r⁻¹ = S.d * t := by
  obtain ⟨u, b, hψ, hb⟩ := odd_of_not_mem_TE S hf hfE
  have h2 : aff8 u b ^ 2 = 1 := by rw [← hψ, ← ψX_pow hf, hf2, ψX_one]
  obtain ⟨ρ, hρ, hρd⟩ := exists_conj_d8 hb h2
  obtain ⟨r, hr, hrψ⟩ := exists_mem_R_ψX_eq (A := A) hρ
  refine ⟨r, hr, eq_or_eq_mul_t C (mul_mem (mul_mem hr.1 hf) (inv_mem hr.1)) (d_mem_T S) ?_⟩
  rw [ψX_conj hr.1 hf, hrψ, hψ, hρd, ψ_d]

@[expose] def cls (t b : X) : Set X := {a | ∃ g ∈ centralizer ({t} : Set X), g * b * g⁻¹ = a}

omit [Finite X] in
theorem mem_cls_self (b : X) : b ∈ cls t b := ⟨1, one_mem _, by group⟩

omit [Finite X] in
theorem cls_eq_of_mem {a b : X} (h : a ∈ cls t b) : cls t a = cls t b := by
  obtain ⟨g, hg, rfl⟩ := h
  ext c
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g' * g, mul_mem hg' hg, by group⟩
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), by group⟩

omit [Finite X] in
theorem cls_t_mul (b : X) : cls t (t * b) = (fun a => t * a) '' cls t b := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * b * g⁻¹, ⟨g, hg, rfl⟩, ?_⟩
    have := mem_centralizer_singleton_iff.mp hg
    calc t * (g * b * g⁻¹) = (t * g) * b * g⁻¹ := by group
      _ = g * t * b * g⁻¹ := by rw [← this]
      _ = g * (t * b) * g⁻¹ := by group
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    have := mem_centralizer_singleton_iff.mp hg
    calc g * (t * b) * g⁻¹ = g * t * b * g⁻¹ := by group
      _ = t * g * b * g⁻¹ := by rw [this]
      _ = t * (g * b * g⁻¹) := by group

omit [Finite X] in
theorem ncard_cls_t_mul (b : X) : (cls t (t * b)).ncard = (cls t b).ncard := by
  rw [cls_t_mul, Set.ncard_image_of_injective _ (mul_right_injective t)]

omit [Finite X] in
theorem ncard_cls_eq (b : X) :
    (cls t b).ncard = (centralizer ({t} : Set X) ⊓ centralizer ({b} : Set X)).relIndex
      (centralizer ({t} : Set X)) :=
  (relIndex_inf_centralizer_eq_ncard _ b).symm

theorem odd_ncard_cls {b : X} (hTb : A.T ≤ centralizer ({b} : Set X)) : Odd (cls t b).ncard := by
  rw [ncard_cls_eq]
  set H := centralizer ({t} : Set X) ⊓ centralizer ({b} : Set X) with hH
  have hTH : A.T ≤ H := le_inf A.T_le_centralizer hTb
  have h1 := card_T_eq_two_pow (A := A)
  have h2 := card_T_eq_of_le (A := A) hTH inf_le_left
  have h3 := card_eq_mul_two_pow (P := A.T) (Q := A.T) (inf_le_left : H ≤ _) h1 h2
  have hpos : 0 < Nat.card A.T := Nat.card_pos
  have h4 : 2 ^ (H.relIndex (centralizer ({t} : Set X))).factorization 2 = 1 := by
    have : Nat.card A.T * 2 ^ (H.relIndex (centralizer ({t} : Set X))).factorization 2 =
        Nat.card A.T * 1 := by rw [mul_one]; exact h3.symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h5 : (H.relIndex (centralizer ({t} : Set X))).factorization 2 = 0 := by
    rcases Nat.eq_zero_or_pos ((H.relIndex (centralizer ({t} : Set X))).factorization 2) with h | h
    · exact h
    · exfalso
      have : 2 ≤ 2 ^ (H.relIndex (centralizer ({t} : Set X))).factorization 2 :=
        Nat.le_self_pow (by omega) 2
      omega
  have h6 : H.relIndex (centralizer ({t} : Set X)) ≠ 0 := by
    intro h0
    have := relIndex_mul_card H (centralizer ({t} : Set X))
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  rw [Nat.odd_iff]
  by_contra hne
  have h2d : 2 ∣ H.relIndex (centralizer ({t} : Set X)) := by omega
  have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two h6).mp h2d
  omega

theorem ncard_cls_k : (cls t S.k).ncard ≡ 2 [MOD 4] := S.card_conj_k

theorem ncard_cls_tk : (cls t (t * S.k)).ncard ≡ 2 [MOD 4] := by
  rw [ncard_cls_t_mul]
  exact S.card_conj_k

theorem ncard_cls_d (hd : S.d ^ 2 = 1) : (cls t S.d).ncard ≡ 0 [MOD 4] := S.card_conj_d hd

theorem ncard_cls_dt (hd : S.d ^ 2 = 1) : (cls t (S.d * t)).ncard ≡ 0 [MOD 4] := by
  rw [comm_t (d_mem_T S), ncard_cls_t_mul]
  exact S.card_conj_d hd

end CFSG.ComponentClassification.HSFLit.KD46
