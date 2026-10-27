module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreTools
public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralCoreFusion

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ABGLocalTools DihedralGroup
open CFSG.ComponentClassification.HarrisLit (SectionalRankLeFour)

variable {X : Type} [Group X] [Finite X] {A : Type} [Group A]

namespace LocalDatum

variable (Δ : LocalDatum X A)

structure Fusion where
  T : Sylow 2 X
  le : Δ.S ≤ T
  x : X
  mem : x ∈ (T : Subgroup X)
  not_mem : x ∉ Δ.S
  conj_mem : ∀ s ∈ Δ.S, x * s * x⁻¹ ∈ Δ.S
  sq_mem : x ^ 2 ∈ Δ.S

theorem nonempty_fusion (hA : AutFacts Δ) (hX : ¬ SectionalRankLeFour X) :
    Nonempty Δ.Fusion := by
  classical
  obtain ⟨T, hST, x, hxT, hxS, hx⟩ := Δ.exists_fusion hA hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨N, hN⟩ := (IsPGroup.iff_orderOf.mp T.isPGroup') ⟨x, hxT⟩
  rw [Subgroup.orderOf_mk] at hN
  have hP : ∃ n : ℕ, x ^ 2 ^ n ∈ Δ.S := ⟨N, by rw [← hN, pow_orderOf_eq_one]; exact one_mem _⟩
  set n₀ := Nat.find hP with hn₀
  have hn₀S : x ^ 2 ^ n₀ ∈ Δ.S := Nat.find_spec hP
  have hn₀pos : n₀ ≠ 0 := fun h => hxS (by rw [h, pow_zero, pow_one] at hn₀S; exact hn₀S)
  have hmin : x ^ 2 ^ (n₀ - 1) ∉ Δ.S := Nat.find_min hP (by omega)
  have hconj : ∀ m : ℕ, ∀ s ∈ Δ.S, x ^ m * s * (x ^ m)⁻¹ ∈ Δ.S := by
    intro m
    induction m with
    | zero => intro s hs; simpa using hs
    | succ m ih =>
      intro s hs
      have := hx _ (ih s hs)
      rw [pow_succ']
      simpa [mul_assoc] using this
  refine ⟨⟨T, hST, x ^ 2 ^ (n₀ - 1), pow_mem hxT _, hmin, hconj _, ?_⟩⟩
  rw [← pow_mul, ← pow_succ, show n₀ - 1 + 1 = n₀ by omega]
  exact hn₀S

variable {Δ}

namespace Fusion

variable (φ : Δ.Fusion)

omit [Finite X] in
theorem isPGroup : IsPGroup 2 (φ.T : Subgroup X) := φ.T.isPGroup'

theorem conj_inv_mem {s : X} (hs : s ∈ Δ.S) : φ.x⁻¹ * s * φ.x ∈ Δ.S := by
  have hle : Δ.S.map (MulAut.conj φ.x).toMonoidHom ≤ Δ.S := by
    rintro _ ⟨y, hy, rfl⟩
    exact φ.conj_mem y hy
  have hcard : Nat.card Δ.S ≤ Nat.card (Δ.S.map (MulAut.conj φ.x).toMonoidHom) := by
    rw [card_map_of_injective (MulAut.conj φ.x).injective]
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard
  have hs' : s ∈ Δ.S.map (MulAut.conj φ.x).toMonoidHom := by rw [heq]; exact hs
  obtain ⟨y, hy, hys⟩ := hs'
  have : y = φ.x⁻¹ * s * φ.x := by
    rw [← hys]
    simp [MulAut.conj_apply]
    group
  rw [← this]
  exact hy

theorem conj_t_ne : φ.x * Δ.t * φ.x⁻¹ ≠ Δ.t := fun h =>
  φ.not_mem (Δ.mem_S_of_conj_t φ.isPGroup φ.le φ.mem h)

theorem conj_t_mem : φ.x * Δ.t * φ.x⁻¹ ∈ Δ.S := φ.conj_mem _ Δ.t_mem

omit [Finite X] in
theorem conj_t_sq : (φ.x * Δ.t * φ.x⁻¹) ^ 2 = 1 := by
  rw [pow_two, show φ.x * Δ.t * φ.x⁻¹ * (φ.x * Δ.t * φ.x⁻¹) = φ.x * (Δ.t * Δ.t) * φ.x⁻¹ by
    group, ← pow_two, Δ.t_sq]
  group

omit [Finite X] in
theorem conj_t_ne_one : φ.x * Δ.t * φ.x⁻¹ ≠ 1 := by
  intro h
  apply Δ.t_ne_one
  calc Δ.t = φ.x⁻¹ * (φ.x * Δ.t * φ.x⁻¹) * φ.x := by group
    _ = 1 := by rw [h]; group

theorem false_of_char (M : Set X) (hMx : ∀ c ∈ M, φ.x * c * φ.x⁻¹ ∈ M)
    (hsq : ∀ c ∈ M, c ^ 2 ∈ Δ.Q) {c : X} (hc : c ∈ M) (hct : c ^ 2 = Δ.t) : False := by
  have h1 := hsq _ (hMx c hc)
  have h2 : (φ.x * c * φ.x⁻¹) ^ 2 = φ.x * Δ.t * φ.x⁻¹ := by
    rw [← hct, pow_two, pow_two]
    group
  rw [h2] at h1
  exact φ.conj_t_ne (Δ.eq_t_of_mem_Q h1 φ.conj_t_sq φ.conj_t_ne_one)

include φ in
theorem false_of_char_center (hsq : ∀ c ∈ Δ.S, (∀ s ∈ Δ.S, c * s = s * c) → c ^ 2 ∈ Δ.Q)
    {c : X} (hcS : c ∈ Δ.S) (hcZ : ∀ s ∈ Δ.S, c * s = s * c) (hct : c ^ 2 = Δ.t) : False := by
  refine φ.false_of_char {c | c ∈ Δ.S ∧ ∀ s ∈ Δ.S, c * s = s * c}
    (fun c hc => ⟨φ.conj_mem c hc.1, fun s hs => ?_⟩) (fun c hc => hsq c hc.1 hc.2) ⟨hcS, hcZ⟩
    hct
  have h := hc.2 _ (φ.conj_inv_mem hs)
  calc φ.x * c * φ.x⁻¹ * s = φ.x * (c * (φ.x⁻¹ * s * φ.x)) * φ.x⁻¹ := by group
    _ = φ.x * ((φ.x⁻¹ * s * φ.x) * c) * φ.x⁻¹ := by rw [h]
    _ = s * (φ.x * c * φ.x⁻¹) := by group

include φ in
theorem false_of_char_inv
    (hsq : ∀ c ∈ Δ.S, (∀ i ∈ Δ.S, i ^ 2 = 1 → c * i = i * c) → c ^ 2 ∈ Δ.Q)
    {c : X} (hcS : c ∈ Δ.S) (hcI : ∀ i ∈ Δ.S, i ^ 2 = 1 → c * i = i * c) (hct : c ^ 2 = Δ.t) :
    False := by
  refine φ.false_of_char {c | c ∈ Δ.S ∧ ∀ i ∈ Δ.S, i ^ 2 = 1 → c * i = i * c}
    (fun c hc => ⟨φ.conj_mem c hc.1, fun i hi hi2 => ?_⟩) (fun c hc => hsq c hc.1 hc.2)
    ⟨hcS, hcI⟩ hct
  have hi2' : (φ.x⁻¹ * i * φ.x) ^ 2 = 1 := by
    rw [pow_two, show φ.x⁻¹ * i * φ.x * (φ.x⁻¹ * i * φ.x) = φ.x⁻¹ * (i * i) * φ.x by group,
      ← pow_two, hi2]
    group
  have h := hc.2 _ (φ.conj_inv_mem hi) hi2'
  calc φ.x * c * φ.x⁻¹ * i = φ.x * (c * (φ.x⁻¹ * i * φ.x)) * φ.x⁻¹ := by group
    _ = φ.x * ((φ.x⁻¹ * i * φ.x) * c) * φ.x⁻¹ := by rw [h]
    _ = i * (φ.x * c * φ.x⁻¹) := by group

end Fusion

variable (Δ)

theorem sq_eq_one_of_commute_db {d : X} (hd : d ∈ Δ.D) (hc : d * Δ.db = Δ.db * d) :
    d ^ 2 = 1 := by
  rcases Δ.mem_of_commute_db hd hc with rfl | rfl | rfl | rfl
  · exact one_pow 2
  · exact Δ.dz_sq
  · exact Δ.db_sq
  · rw [(show Commute Δ.db Δ.dz from Δ.commute_db_dz).mul_pow, Δ.db_sq, Δ.dz_sq, one_mul]

theorem sq_mem_Q_of_caseOne (h1 : Δ.CaseOne) {c : X} (hc : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) : c ^ 2 ∈ Δ.Q := by
  have hmem : Δ.ψe c ∈ Δ.Dbar := h1 _ (Δ.ψe_mem_R hc) fun d hd => by
    obtain ⟨d', hd', rfl⟩ := (Δ.mem_Dbar_iff).mp hd
    exact (Δ.commute_iff hc hd').mp (hcD d' hd')
  obtain ⟨q, hq, d, hd, rfl⟩ := Δ.exists_QD hc hmem
  have hqd : q * d = d * q := Δ.commute_of_mem_Q_D hq hd
  have hdb : d * Δ.db = Δ.db * d := by
    have h := hcD _ Δ.db_mem
    have hqb : q * Δ.db = Δ.db * q := Δ.commute_of_mem_Q_D hq Δ.db_mem
    have : q * (d * Δ.db) = q * (Δ.db * d) := by
      calc q * (d * Δ.db) = q * d * Δ.db := by group
        _ = Δ.db * (q * d) := h
        _ = q * (Δ.db * d) := by rw [← mul_assoc, ← hqb, mul_assoc]
    exact mul_left_cancel this
  have hd2 := Δ.sq_eq_one_of_commute_db hd hdb
  rw [(show Commute q d from hqd).mul_pow, hd2, mul_one]
  exact pow_mem hq 2

theorem sq_mem_Q_of_caseTwo {k : A} (h2 : Δ.CaseTwo k) {c : X} (hc : c ∈ Δ.S)
    (hcD : ∀ d ∈ Δ.D, c * d = d * c) : c ^ 2 ∈ Δ.Q := by
  obtain ⟨-, hkD, hkn, hk2, -, hC⟩ := h2
  have hcomm : ∀ d ∈ Δ.Dbar, Δ.ψe c * d = d * Δ.ψe c := fun d hd => by
    obtain ⟨d', hd', rfl⟩ := (Δ.mem_Dbar_iff).mp hd
    exact (Δ.commute_iff hc hd').mp (hcD d' hd')
  refine (Δ.mem_Q_iff).mpr ⟨pow_mem hc 2, ?_⟩
  rw [Δ.ψe_pow hc]
  have key : ∀ y ∈ Δ.Dbar, (∀ d ∈ Δ.Dbar, y * d = d * y) → y ^ 2 = 1 := by
    intro y hy hyc
    obtain ⟨d, hd, rfl⟩ := (Δ.mem_Dbar_iff).mp hy
    have hdb : d * Δ.db = Δ.db * d := Δ.eq_of_ψe_eq (mul_mem hd Δ.db_mem)
      (mul_mem Δ.db_mem hd) (by
        rw [Δ.ψe_mul (Δ.D_le hd) (Δ.D_le Δ.db_mem), Δ.ψe_mul (Δ.D_le Δ.db_mem) (Δ.D_le hd)]
        exact hyc _ (Δ.ψe_mem_Dbar Δ.db_mem))
    rw [← Δ.ψe_pow (Δ.D_le hd), Δ.sq_eq_one_of_commute_db hd hdb, Δ.ψe_one]
  rcases hC _ (Δ.ψe_mem_R hc) hcomm with h | h
  · exact key _ h hcomm
  · have h' := key _ h fun d hd => by
      calc Δ.ψe c * k * d = Δ.ψe c * (k * d) := by group
        _ = Δ.ψe c * (d * k) := by rw [hkD d hd]
        _ = d * (Δ.ψe c * k) := by rw [← mul_assoc, hcomm d hd, mul_assoc]
    have hck : Δ.ψe c * k = k * Δ.ψe c := by
      have := hkD _ h
      calc Δ.ψe c * k = (Δ.ψe c * k) * k * k⁻¹ := by group
        _ = k * (Δ.ψe c * k) * k⁻¹ := by rw [← this]
        _ = k * Δ.ψe c := by group
    rw [(show Commute (Δ.ψe c) k from hck).mul_pow, hk2, mul_one] at h'
    exact h'

end LocalDatum

end CFSG.ComponentClassification.HSDihedral
