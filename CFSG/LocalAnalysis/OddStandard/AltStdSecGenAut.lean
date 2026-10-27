module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.LocalAnalysis.OddStandard.AltStdSecGenFpf

public section

namespace CFSG.OddStandard.AltStdSec

open Subgroup Equiv

section Inner

variable {X : Type*} [Group X]

theorem hom_trivial_of_perfect {P : Type*} [Group P] (hP : commutator P = ⊤) {M : Type*}
    [CommGroup M] (f : P →* M) (x : P) : f x = 1 := by
  have h := Abelianization.commutator_subset_ker f
  rw [hP] at h
  exact MonoidHom.mem_ker.1 (h (Subgroup.mem_top x))

theorem exists_inner_hom {K P : Subgroup X} {m : ℕ} (hm5 : 5 ≤ m) (hm6 : m ≠ 6)
    (eK : ↥K ≃* alternatingGroup (Fin m)) (hP : ⁅P, P⁆ = P)
    (hN : ∀ p ∈ P, ∀ k ∈ K, p * k * p⁻¹ ∈ K) :
    ∃ κ : ↥P →* ↥K, ∀ (p : ↥P) (k : ↥K),
      (p : X) * (k : X) * (p : X)⁻¹ = (κ p : X) * (k : X) * (κ p : X)⁻¹ := by
  have hPN : P ≤ (normalizer (K : Set X) : Subgroup X) := by
    intro p hp
    rw [mem_normalizer_iff]
    intro k
    constructor
    · intro hk; exact hN p hp k hk
    · intro hk
      have := hN p⁻¹ (P.inv_mem hp) (p * k * p⁻¹) hk
      simpa [mul_assoc] using this
  let φ : ↥P →* MulAut ↥K := (K.normalizerMonoidHom).comp (Subgroup.inclusion hPN)
  have hφ : ∀ (p : ↥P) (k : ↥K), (((φ p) k : ↥K) : X) = (p : X) * k * (p : X)⁻¹ := fun p k => rfl
  let ι : Perm (Fin m) ≃* MulAut (alternatingGroup (Fin m)) :=
    MulEquiv.ofBijective _ (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj
      m hm5 hm6)
  let ϑ : ↥P →* Perm (Fin m) := ι.symm.toMonoidHom.comp ((MulAut.congr eK).toMonoidHom.comp φ)
  have hperf : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hP
  have hsign : ∀ p, ϑ p ∈ alternatingGroup (Fin m) := by
    intro p
    rw [Perm.mem_alternatingGroup]
    exact hom_trivial_of_perfect hperf.commutator_eq_top (Perm.sign.comp ϑ) p
  let κ : ↥P →* ↥K := eK.symm.toMonoidHom.comp (ϑ.codRestrict (alternatingGroup (Fin m)) hsign)
  refine ⟨κ, fun p k => ?_⟩
  have h1 : ι (ϑ p) = (MulAut.congr eK) (φ p) := ι.apply_symm_apply _
  have h2 := congrArg (fun f : MulAut (alternatingGroup (Fin m)) => f (eK k)) h1
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
  have h3 : (φ p) k = κ p * k * (κ p)⁻¹ := by
    apply eK.injective
    rw [← h2, map_mul, map_mul, map_inv]
    have h4 : eK (κ p) = ⟨ϑ p, hsign p⟩ := by simp [κ]
    rw [h4]
    apply Subtype.ext
    simp [ι]
  have h5 := congrArg Subtype.val h3
  rw [hφ] at h5
  simpa using h5

end Inner

section Lagrange

theorem two_mul_succ_lt_factorial : ∀ k : ℕ, 7 ≤ k →
    2 * ((k + 1) * (k + 2) * (k + 3)) < k.factorial := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [Nat.factorial_succ]
    have h1 : (k + 1) * (2 * ((k + 1) * (k + 2) * (k + 3))) < (k + 1) * k.factorial :=
      Nat.mul_lt_mul_of_pos_left ih (by omega)
    have h2 : k + 4 ≤ (k + 1) * (k + 1) := by nlinarith
    calc 2 * ((k + 1 + 1) * (k + 1 + 2) * (k + 1 + 3))
        = 2 * ((k + 2) * (k + 3)) * (k + 4) := by ring
      _ ≤ 2 * ((k + 2) * (k + 3)) * ((k + 1) * (k + 1)) := Nat.mul_le_mul_left _ h2
      _ = (k + 1) * (2 * ((k + 1) * (k + 2) * (k + 3))) := by ring
      _ < (k + 1) * k.factorial := h1

theorem not_dvd_sq_card_alt {k m : ℕ} (hk : 5 ≤ k) (hkm : k ≤ m) (hmk : m ≤ k + 3) :
    ¬ (Nat.card (alternatingGroup (Fin k))) ^ 2 ∣ Nat.card (alternatingGroup (Fin m)) := by
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.2 (by omega)
  rw [nat_card_alternatingGroup, nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨r, hr, hrb⟩ : ∃ r, m.factorial = k.factorial * r ∧ r ≤ (k + 1) * (k + 2) * (k + 3) := by
    have h : m = k ∨ m = k + 1 ∨ m = k + 2 ∨ m = k + 3 := by omega
    have h1 : 1 ≤ k + 1 := by omega
    have h2 : 1 ≤ (k + 1) * (k + 2) := Nat.mul_pos (by omega) (by omega)
    rcases h with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, Nat.mul_pos h2 (by omega)⟩
    · refine ⟨k + 1, by rw [Nat.factorial_succ]; ring, ?_⟩
      calc k + 1 ≤ (k + 1) * (k + 2) := Nat.le_mul_of_pos_right _ (by omega)
        _ ≤ (k + 1) * (k + 2) * (k + 3) := Nat.le_mul_of_pos_right _ (by omega)
    · refine ⟨(k + 1) * (k + 2), by rw [Nat.factorial_succ, Nat.factorial_succ]; ring, ?_⟩
      exact Nat.le_mul_of_pos_right _ (by omega)
    · refine ⟨(k + 1) * (k + 2) * (k + 3), by
        rw [Nat.factorial_succ, Nat.factorial_succ, Nat.factorial_succ]; ring, le_rfl⟩
  have hk2 : 2 ∣ k.factorial := Nat.dvd_factorial (by norm_num) (by omega)
  obtain ⟨a, ha⟩ := hk2
  have hapos : 0 < a := by
    have := Nat.factorial_pos k
    omega
  have hkd : k.factorial / 2 = a := by omega
  have hmd : m.factorial / 2 = a * r := by
    rw [hr, ha]
    have : 2 * a * r = 2 * (a * r) := by ring
    omega
  rw [hkd, hmd]
  intro hdiv
  have hdiv' : a ∣ r := by
    have h1 : a * a ∣ a * r := by simpa [pow_two] using hdiv
    exact (Nat.mul_dvd_mul_iff_left hapos).1 h1
  have hrpos : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      have := Nat.factorial_pos m
      rw [hr, h] at this
      simp at this
    · exact h
  have hle : a ≤ r := Nat.le_of_dvd hrpos hdiv'
  by_cases hk7 : 7 ≤ k
  · have := two_mul_succ_lt_factorial k hk7
    omega
  · rcases (by omega : k = 5 ∨ k = 6) with hk5 | hk6
    · subst hk5
      have h120 : (5 : ℕ).factorial = 120 := by decide
      have ha' : a = 60 := by omega
      subst ha'
      have h : m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 := by omega
      rcases h with rfl | rfl | rfl | rfl
      · have : r = 1 := by simp [Nat.factorial] at hr; omega
        omega
      · have : r = 6 := by simp [Nat.factorial] at hr; omega
        omega
      · have : r = 42 := by simp [Nat.factorial] at hr; omega
        omega
      · have : r = 336 := by simp [Nat.factorial] at hr; omega
        subst this
        exact absurd hdiv' (by decide)
    subst hk6
    have h720 : (6 : ℕ).factorial = 720 := by decide
    have ha' : a = 360 := by omega
    subst ha'
    have h : m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · have : r = 1 := by simp [Nat.factorial] at hr; omega
      omega
    · have : r = 7 := by simp [Nat.factorial] at hr; omega
      omega
    · have : r = 56 := by simp [Nat.factorial] at hr; omega
      omega
    · have : r = 504 := by simp [Nat.factorial] at hr; omega
      subst this
      exact absurd hdiv' (by decide)

end Lagrange

section Toggle

variable {X : Type*} [Group X]

theorem map_conj_mul (p q : X) (K : Subgroup X) :
    K.map (MulAut.conj (p * q)).toMonoidHom =
      (K.map (MulAut.conj q).toMonoidHom).map (MulAut.conj p).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (K : Subgroup X) : K.map (MulAut.conj (1 : X)).toMonoidHom = K := by
  ext x
  simp

theorem map_conj_inj (p : X) {A B : Subgroup X}
    (h : A.map (MulAut.conj p).toMonoidHom = B.map (MulAut.conj p).toMonoidHom) : A = B :=
  Subgroup.map_injective (MulAut.conj p).injective h

theorem perfect_normalizes_of_two {K K' P : Subgroup X} (hne : K ≠ K') (hP : ⁅P, P⁆ = P)
    (hK : ∀ p ∈ P, K.map (MulAut.conj p).toMonoidHom = K ∨
      K.map (MulAut.conj p).toMonoidHom = K')
    (hK' : ∀ p ∈ P, K'.map (MulAut.conj p).toMonoidHom = K ∨
      K'.map (MulAut.conj p).toMonoidHom = K') :
    ∀ p ∈ P, ∀ x ∈ K, p * x * p⁻¹ ∈ K := by
  let c : X → Subgroup X → Subgroup X := fun g J => J.map (MulAut.conj g).toMonoidHom
  let F : X → Prop := fun g => c g K = K
  have hF1 : ∀ p ∈ P, F p → c p K' = K' := by
    intro p hp hf
    rcases hK' p hp with h | h
    · exact absurd (map_conj_inj p (h.trans hf.symm)).symm hne
    · exact h
  have hF2 : ∀ p ∈ P, ¬ F p → c p K = K' ∧ c p K' = K := by
    intro p hp hf
    have h1 : c p K = K' := (hK p hp).resolve_left hf
    refine ⟨h1, (hK' p hp).resolve_right fun h => hne ?_⟩
    exact map_conj_inj p (h1.trans h.symm)
  have hmul : ∀ p ∈ P, ∀ q ∈ P, F (p * q) ↔ (F p ↔ F q) := by
    intro p hp q hq
    have hpq : c (p * q) K = c p (c q K) := map_conj_mul p q K
    by_cases hfq : F q
    · have : c (p * q) K = c p K := by rw [hpq]; exact congrArg (c p) hfq
      simp only [F, this]
      tauto
    · have h2 := hF2 q hq hfq
      have : c (p * q) K = c p K' := by rw [hpq, h2.1]
      by_cases hfp : F p
      · have h3 := hF1 p hp hfp
        have : ¬ F (p * q) := by
          intro h
          apply hne
          have : c (p * q) K = c p K' := by rw [hpq, h2.1]
          exact h.symm.trans (this.trans h3)
        tauto
      · have h3 := hF2 p hp hfp
        have : F (p * q) := by
          show c (p * q) K = K
          rw [hpq, h2.1, h3.2]
        tauto
  have hone : F 1 := map_conj_one K
  have hinv : ∀ p ∈ P, F p⁻¹ ↔ F p := by
    intro p hp
    have := hmul p hp p⁻¹ (P.inv_mem hp)
    rw [mul_inv_cancel] at this
    tauto
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, F (a * b * a⁻¹ * b⁻¹) := by
    intro a ha b hb
    have h1 := hmul (a * b * a⁻¹) (P.mul_mem (P.mul_mem ha hb) (P.inv_mem ha)) b⁻¹ (P.inv_mem hb)
    have h2 := hmul (a * b) (P.mul_mem ha hb) a⁻¹ (P.inv_mem ha)
    have h3 := hmul a ha b hb
    have h4 := hinv a ha
    have h5 := hinv b hb
    tauto
  have hnorm : ∀ g, F g → g ∈ normalizer (K : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have : g * h * g⁻¹ ∈ c g K := ⟨h, hh, by simp⟩
      rwa [hg] at this
    · intro hh
      have : g * h * g⁻¹ ∈ c g K := by rwa [hg]
      obtain ⟨k, hk, hkh⟩ := this
      have : k = h := by
        have h1 : g * k * g⁻¹ = g * h * g⁻¹ := hkh
        simpa using h1
      rwa [← this]
  have hle : P ≤ (normalizer (K : Set X) : Subgroup X) :=
    le_of_comm_mem hP fun a ha b hb => hnorm _ (hcomm a ha b hb)
  intro p hp x hx
  exact (mem_normalizer_iff.1 (hle hp) x).1 hx

end Toggle

end CFSG.OddStandard.AltStdSec
