module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm4

open Subgroup CFSG
open scoped commutatorElement

section Abstract

variable {G : Type*} [Group G]

theorem zpow_eq_one_or_self {t : G} (ht2 : t ^ 2 = 1) (n : ℤ) : t ^ n = 1 ∨ t ^ n = t := by
  obtain ⟨k, hk | hk⟩ := Int.even_or_odd' n
  · left
    rw [hk, zpow_mul]
    simp [ht2]
  · right
    rw [hk, zpow_add_one, zpow_mul]
    simp [ht2]

theorem commute_of_conj_eq {c x : G} (h : c * x * c⁻¹ = x) : x * c = c * x := by
  calc x * c = (c * x * c⁻¹) * c := by rw [h]
    _ = c * x := by group

theorem commutator_zpowers_le_centralizer_of_inv {M R : Subgroup G} {t : G} (htM : t ∈ M) (ht2 : t ^ 2 = 1)
    (hRM : ∀ m ∈ M, ∀ x ∈ R, m * x * m⁻¹ ∈ R) (hinv : ∀ x ∈ R, t * x * t⁻¹ = x⁻¹) :
    ⁅M, Subgroup.zpowers t⁆ ≤ Subgroup.centralizer (R : Set G) := by
  rw [Subgroup.commutator_le]
  intro g hg τ hτ
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
  rcases zpow_eq_one_or_self ht2 n with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    apply commute_of_conj_eq
    have hy : g⁻¹ * x * g ∈ R := by simpa using hRM g⁻¹ (M.inv_mem hg) x hx
    have ht' : t⁻¹ * x * t = x⁻¹ := by
      have hz : t⁻¹ * x * t⁻¹⁻¹ ∈ R := hRM t⁻¹ (M.inv_mem htM) x hx
      have h3 := hinv _ hz
      have h4 : t * (t⁻¹ * x * t⁻¹⁻¹) * t⁻¹ = x := by group
      rw [h4] at h3
      calc t⁻¹ * x * t = ((t⁻¹ * x * t⁻¹⁻¹)⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [← h3]
    have h2 : t * (g⁻¹ * x * g) * t⁻¹ = (g⁻¹ * x * g)⁻¹ := hinv _ hy
    rw [commutatorElement_def]
    calc (g * t * g⁻¹ * t⁻¹) * x * (g * t * g⁻¹ * t⁻¹)⁻¹
        = g * (t * (g⁻¹ * (t⁻¹ * x * t) * g) * t⁻¹) * g⁻¹ := by group
      _ = g * (t * (g⁻¹ * x⁻¹ * g) * t⁻¹) * g⁻¹ := by rw [ht']
      _ = g * (t * (g⁻¹ * x * g) * t⁻¹)⁻¹ * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g)⁻¹)⁻¹ * g⁻¹ := by rw [h2]
      _ = x := by group

theorem commutator_le_centralizer_of_cyclic {M R : Subgroup G} (hRM : ∀ m ∈ M, ∀ x ∈ R, m * x * m⁻¹ ∈ R)
    (hcyc : IsCyclic ↥R) : ⁅M, M⁆ ≤ Subgroup.centralizer (R : Set G) := by
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  have hpow : ∀ m ∈ M, ∃ k : ℤ, m * (g : G) * m⁻¹ = (g : G) ^ k := by
    intro m hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨m * (g : G) * m⁻¹, hRM m hm g g.2⟩)
    exact ⟨k, (congrArg Subtype.val hk).symm⟩
  have hexp : ∀ x ∈ R, ∃ j : ℤ, x = (g : G) ^ j := by
    intro x hx
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨j, (congrArg Subtype.val hj).symm⟩
  have hcomm : ∀ a ∈ M, ∀ b ∈ M, ∀ x ∈ R, a * (b * x * b⁻¹) * a⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by
    intro a ha b hb x hx
    obtain ⟨ka, hka⟩ := hpow a ha
    obtain ⟨kb, hkb⟩ := hpow b hb
    obtain ⟨j, rfl⟩ := hexp x hx
    have e1 : a * (g : G) ^ j * a⁻¹ = (g : G) ^ (ka * j) := by
      rw [← conj_zpow, hka, ← zpow_mul]
    have e2 : b * (g : G) ^ j * b⁻¹ = (g : G) ^ (kb * j) := by
      rw [← conj_zpow, hkb, ← zpow_mul]
    have e3 : a * (g : G) ^ (kb * j) * a⁻¹ = (g : G) ^ (ka * (kb * j)) := by
      rw [← conj_zpow, hka, ← zpow_mul]
    have e4 : b * (g : G) ^ (ka * j) * b⁻¹ = (g : G) ^ (kb * (ka * j)) := by
      rw [← conj_zpow, hkb, ← zpow_mul]
    rw [e2, e3, e1, e4]
    congr 1
    ring
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  apply commute_of_conj_eq
  have h := hcomm g₁⁻¹ (M.inv_mem hg₁) g₂⁻¹ (M.inv_mem hg₂) x hx
  simp only [inv_inv] at h
  rw [commutatorElement_def]
  calc (g₁ * g₂ * g₁⁻¹ * g₂⁻¹) * x * (g₁ * g₂ * g₁⁻¹ * g₂⁻¹)⁻¹
      = g₁ * g₂ * (g₁⁻¹ * (g₂⁻¹ * x * g₂) * g₁) * g₂⁻¹ * g₁⁻¹ := by group
    _ = g₁ * g₂ * (g₂⁻¹ * (g₁⁻¹ * x * g₁) * g₂) * g₂⁻¹ * g₁⁻¹ := by rw [h]
    _ = x := by group

end Abstract

section Stability

variable {G : Type*} [Group G]

theorem stab_chain_centralizes [Finite G] {p : ℕ} {M P Q U : Subgroup G} {t : G} (htM : t ∈ M) (ht2 : t ^ 2 = 1)
    (hPM : ∀ m ∈ M, ∀ x ∈ P, m * x * m⁻¹ ∈ P) (hPp : ∀ x ∈ P, ∃ e : ℕ, x ^ (p ^ e) = 1)
    (hQM : ∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q) (hQP : Q ≤ P) (hUP : U ≤ P)
    (hUn : ∀ x ∈ P, ∀ u ∈ U, x * u * x⁻¹ ∈ U) (hUc : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u)
    (hCQ : ∀ x ∈ P, (∀ u ∈ U, x * u = u * x) → x ∈ Q) (htQ : ∀ x ∈ Q, t * x * t⁻¹ = x⁻¹) :
    ∀ a ∈ ⁅M, Subgroup.zpowers t⁆, Nat.Coprime (orderOf a) p → ∀ x ∈ P, a * x = x * a := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact ht2)
  have hUQ : U ≤ Q := fun u hu => hCQ u (hUP hu) (fun v hv => hUc u hu v hv)
  have htU : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ := fun u hu => htQ u (hUQ hu)
  have hPt : ∀ x ∈ P, x⁻¹ * (t * x * t⁻¹) ∈ Q := by
    intro x hx
    have hxt : t * x * t⁻¹ ∈ P := hPM t htM x hx
    refine hCQ _ (P.mul_mem (P.inv_mem hx) hxt) fun u hu => ?_
    have hu' : t⁻¹ * u * t = u⁻¹ := by
      have := htU u hu
      rw [htinv] at this ⊢
      exact this
    have hxu : x * u * x⁻¹ ∈ U := hUn x hx u hu
    have h1 := htU _ (U.inv_mem hxu)
    have key : (t * x * t⁻¹) * u * (t * x * t⁻¹)⁻¹ = x * u * x⁻¹ := by
      calc (t * x * t⁻¹) * u * (t * x * t⁻¹)⁻¹ = t * x * (t⁻¹ * u * t) * x⁻¹ * t⁻¹ := by group
        _ = t * x * u⁻¹ * x⁻¹ * t⁻¹ := by rw [hu']
        _ = t * (x * u * x⁻¹)⁻¹ * t⁻¹ := by group
        _ = x * u * x⁻¹ := by rw [h1]; group
    have hc : (x⁻¹ * (t * x * t⁻¹)) * u * (x⁻¹ * (t * x * t⁻¹))⁻¹ = u := by
      calc (x⁻¹ * (t * x * t⁻¹)) * u * (x⁻¹ * (t * x * t⁻¹))⁻¹
          = x⁻¹ * ((t * x * t⁻¹) * u * (t * x * t⁻¹)⁻¹) * x := by group
        _ = x⁻¹ * (x * u * x⁻¹) * x := by rw [key]
        _ = u := by group
    exact (commute_of_conj_eq hc).symm
  have cg_trans : ∀ x y z : G, x⁻¹ * y ∈ Q → y⁻¹ * z ∈ Q → x⁻¹ * z ∈ Q := fun x y z h1 h2 => by
    have h3 := Q.mul_mem h1 h2
    have e : x⁻¹ * y * (y⁻¹ * z) = x⁻¹ * z := by group
    rwa [e] at h3
  have cg_symm : ∀ x y : G, x⁻¹ * y ∈ Q → y⁻¹ * x ∈ Q := fun x y h => by
    have h3 := Q.inv_mem h
    have e : (x⁻¹ * y)⁻¹ = y⁻¹ * x := by group
    rwa [e] at h3
  have cg_conj : ∀ m ∈ M, ∀ x y : G, x⁻¹ * y ∈ Q → (m * x * m⁻¹)⁻¹ * (m * y * m⁻¹) ∈ Q :=
    fun m hm x y h => by
      have h3 := hQM m hm _ h
      have e : m * (x⁻¹ * y) * m⁻¹ = (m * x * m⁻¹)⁻¹ * (m * y * m⁻¹) := by group
      rwa [e] at h3
  let Stab : Subgroup G :=
    { carrier := {a | a ∈ M ∧ (∀ q ∈ Q, a * q = q * a) ∧ ∀ x ∈ P, x⁻¹ * (a * x * a⁻¹) ∈ Q}
      one_mem' := ⟨M.one_mem, fun q _ => by simp, fun x _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haM, haQ, haP⟩ ⟨hbM, hbQ, hbP⟩
        refine ⟨M.mul_mem haM hbM, fun q hq => ?_, fun x hx => ?_⟩
        · calc a * b * q = a * (b * q) := by group
            _ = a * (q * b) := by rw [hbQ q hq]
            _ = (a * q) * b := by group
            _ = (q * a) * b := by rw [haQ q hq]
            _ = q * (a * b) := by group
        · have hx' : b * x * b⁻¹ ∈ P := hPM b hbM x hx
          have h3 := Q.mul_mem (hbP x hx) (haP _ hx')
          have e : x⁻¹ * (b * x * b⁻¹) * ((b * x * b⁻¹)⁻¹ * (a * (b * x * b⁻¹) * a⁻¹)) =
              x⁻¹ * (a * b * x * (a * b)⁻¹) := by group
          rwa [e] at h3
      inv_mem' := by
        rintro a ⟨haM, haQ, haP⟩
        refine ⟨M.inv_mem haM, fun q hq => ?_, fun x hx => ?_⟩
        · have h3 := haQ q hq
          calc a⁻¹ * q = a⁻¹ * (q * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * q) * a⁻¹ := by rw [h3]
            _ = q * a⁻¹ := by group
        · have hx' : a⁻¹ * x * a ∈ P := by simpa using hPM a⁻¹ (M.inv_mem haM) x hx
          have h3 := Q.inv_mem (haP _ hx')
          have e : ((a⁻¹ * x * a)⁻¹ * (a * (a⁻¹ * x * a) * a⁻¹))⁻¹ = x⁻¹ * (a⁻¹ * x * a⁻¹⁻¹) := by group
          rwa [e] at h3 }
  have hgen : ∀ g ∈ M, ⁅g, t⁆ ∈ Stab := by
    intro g hg
    have hc := commutator_zpowers_le_centralizer_of_inv htM ht2 hQM htQ
      (Subgroup.commutator_mem_commutator hg (Subgroup.mem_zpowers t))
    refine ⟨M.mul_mem (M.mul_mem (M.mul_mem hg htM) (M.inv_mem hg)) (M.inv_mem htM),
      fun q hq => (Subgroup.mem_centralizer_iff.mp hc q hq).symm, fun x hx => ?_⟩
    have hx₂ : g⁻¹ * x * g ∈ P := by simpa using hPM g⁻¹ (M.inv_mem hg) x hx
    have ht1 : ∀ y : G, t⁻¹ * y * t = t * y * t⁻¹ := fun y => by simp only [htinv]
    have s1 : x⁻¹ * (t⁻¹ * x * t) ∈ Q := by rw [ht1]; exact hPt x hx
    have s2 := cg_conj g⁻¹ (M.inv_mem hg) _ _ s1
    simp only [inv_inv] at s2
    have s3 := cg_conj t htM _ _ s2
    have s5 := cg_trans _ _ _ (hPt _ hx₂) s3
    have s6 := cg_conj g hg _ _ s5
    have e : (g * (g⁻¹ * x * g) * g⁻¹)⁻¹ * (g * (t * (g⁻¹ * (t⁻¹ * x * t) * g) * t⁻¹) * g⁻¹) =
        x⁻¹ * (⁅g, t⁆ * x * ⁅g, t⁆⁻¹) := by
      rw [commutatorElement_def]
      group
    rwa [e] at s6
  have hAle : ⁅M, Subgroup.zpowers t⁆ ≤ Stab := by
    rw [Subgroup.commutator_le]
    intro g hg τ hτ
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hτ
    rcases zpow_eq_one_or_self ht2 n with h1 | h1
    · rw [h1]
      simp
    · rw [h1]
      exact hgen g hg
  intro a haA hcop x hx
  obtain ⟨haM, haQ, haP⟩ := hAle haA
  have hqQ : x⁻¹ * (a * x * a⁻¹) ∈ Q := haP x hx
  set q := x⁻¹ * (a * x * a⁻¹) with hq
  have hax : a * x * a⁻¹ = x * q := by rw [hq]; group
  have hiter : ∀ j : ℕ, a ^ j * x * (a ^ j)⁻¹ = x * q ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hqj : q ^ j ∈ Q := Q.pow_mem hqQ j
      have hcomm : a * q ^ j = q ^ j * a := haQ _ hqj
      calc a ^ (j + 1) * x * (a ^ (j + 1))⁻¹ = a * (a ^ j * x * (a ^ j)⁻¹) * a⁻¹ := by group
        _ = a * (x * q ^ j) * a⁻¹ := by rw [ih]
        _ = (a * x * a⁻¹) * (a * q ^ j * a⁻¹) := by group
        _ = (x * q) * q ^ j := by rw [hax, hcomm]; group
        _ = x * q ^ (j + 1) := by rw [pow_succ']; group
  have hn : x * q ^ orderOf a = x := by
    have h3 := hiter (orderOf a)
    rw [pow_orderOf_eq_one] at h3
    simpa using h3.symm
  have hq1 : q ^ orderOf a = 1 := by simpa using hn
  obtain ⟨e, he⟩ := hPp q (hQP hqQ)
  have hdvd1 : orderOf q ∣ orderOf a := orderOf_dvd_of_pow_eq_one hq1
  have hdvd2 : orderOf q ∣ p ^ e := orderOf_dvd_of_pow_eq_one he
  have hord : orderOf q = 1 := Nat.eq_one_of_dvd_coprimes (hcop.pow_right e) hdvd1 hdvd2
  have hq1' : q = 1 := orderOf_eq_one_iff.mp hord
  rw [hq1', mul_one] at hax
  calc a * x = (a * x * a⁻¹) * a := by group
    _ = x * a := by rw [hax]

end Stability

end CFSG.GH74.GLS.Stage2.Final.Thm4
