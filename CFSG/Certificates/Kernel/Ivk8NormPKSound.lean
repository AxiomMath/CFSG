module

public import Certificates.Data.Kernel.Ivk8NormPK
public import CFSG.Certificates.Kernel.Ivk8CentSound
public import CFSG.Certificates.Kernel.Ivk8NormPSound
import CFSG.Certificates.Kernel.Spor.PcompFacts

public section

namespace CFSG.KS.Ivk8NormP

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Ivk8Cent Subgroup

variable {n w : ℕ}

theorem pr_cmpF {a b : ℕ} {σ τ : Equiv.Perm (Fin n)} (ha : PR n w a σ) (hb : PR n w b τ) :
    PR n w (cmpF n w a b) (σ * τ) :=
  ha.pc hb

theorem pr_powN {y : ℕ} {σ : Equiv.Perm (Fin n)} (hy : PR n w y σ) :
    ∀ (k : ℕ) {z : ℕ} {τ : Equiv.Perm (Fin n)}, PR n w z τ →
      PR n w (powN n w y k z) (σ ^ k * τ)
  | 0, _, _, hz => by simpa [powN] using hz
  | k + 1, _, _, hz => by
    have := pr_powN hy k (pr_cmpF hy hz)
    rw [powN]
    rwa [pow_succ, mul_assoc]

theorem powN_mem_powsN' (y : ℕ) :
    ∀ (k : ℕ) (z : ℕ), ∀ i < k, powN n w y i z ∈ powsN n w y k z
  | 0, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | k + 1, z, 0, _ => by
    rw [powsN]
    exact List.mem_cons_self ..
  | k + 1, z, i + 1, hi => by
    rw [powsN, powN]
    exact List.mem_cons_of_mem _ (powN_mem_powsN' y k _ i (by omega))

theorem okP_sound (hsz : szOK n w = true) {p : ℕ} (hp : p.Prime) {hs : List (ℕ × ℕ)}
    {G : Set (Equiv.Perm (Fin n))} (hhs : ∀ h ∈ hs, ∃ g ∈ G, PR n w h.1 g ∧ PR n w h.2 g⁻¹)
    {x : ℕ} {ξ : Equiv.Perm (Fin n)} (hx : PR n w x ξ) (hξ : orderOf ξ = p)
    (h : okP n w p hs x = true) :
    ∃ g ∈ G, g ∉ normalizer (zpowers ξ : Set (Equiv.Perm (Fin n))) := by
  unfold okP at h
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h
  have hI := PR.one hsz
  have hpow : PR n w (powN n w x p (pidn n w)) 1 := by
    have := pr_powN hx p hI
    rw [mul_one, ← hξ, pow_orderOf_eq_one] at this
    rwa [hξ] at this
  have hξ1 : ξ ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hξ
    exact hp.one_lt.ne hξ
  rcases h with (h1 | h2) | h3
  · rw [(PR.beq hpow hI).2 rfl] at h1
    exact absurd h1 (by decide)
  · exact absurd ((PR.beq hx hI).1 h2) hξ1
  · unfold movesN at h3
    obtain ⟨hh, hmem, hnot⟩ := List.any_eq_true.1 h3
    obtain ⟨g, hgG, hg1, hg2⟩ := hhs hh hmem
    refine ⟨g, hgG, fun hN => ?_⟩
    have hc : g * ξ * g⁻¹ ∈ zpowers ξ := (mem_normalizer_iff.1 hN _).1 (mem_zpowers _)
    have hc1 : g * ξ * g⁻¹ ≠ 1 := by
      intro h1
      apply hξ1
      calc ξ = g⁻¹ * (g * ξ * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    obtain ⟨j, hj1, hjp, hj⟩ := exists_pow_of_mem_zpowers hξ hp.pos hc hc1
    have hq := powN_mem_powsN' (n := n) (w := w) x (p - 1) (cmpF n w x (pidn n w)) (j - 1)
      (by omega)
    unfold notInN at hnot
    have hz := List.all_eq_true.1 hnot _ hq
    have hrep : PR n w (powN n w x (j - 1) (cmpF n w x (pidn n w))) (g * ξ * g⁻¹) := by
      have := pr_powN hx (j - 1) (pr_cmpF hx hI)
      rwa [mul_one, ← pow_succ, Nat.sub_add_cancel hj1, hj] at this
    have hcrep : PR n w (conjF n w hh x) (g * ξ * g⁻¹) := by
      have := pr_cmpF hg1 (pr_cmpF hx hg2)
      rwa [← mul_assoc] at this
    rw [(PR.beq hcrep hrep).2 rfl] at hz
    exact absurd hz (by decide)

theorem chkPK_sound (hsz : szOK n w = true) {p : ℕ} (hp : p.Prime) {c ci cnt : ℕ}
    {T : ℕ → ℕ} {hs : List (ℕ × ℕ)} {G : Set (Equiv.Perm (Fin n))}
    (hhs : ∀ h ∈ hs, ∃ g ∈ G, PR n w h.1 g ∧ PR n w h.2 g⁻¹) {γ : Equiv.Perm (Fin n)}
    (hc : PR n w c γ) (hci : PR n w ci γ⁻¹) (h : chkPK n w p c ci cnt T hs = true) {i : ℕ}
    (hi : i < cnt) {τ : Equiv.Perm (Fin n)} (hT : PR n w (T i) τ) (hτ : orderOf τ = p) :
    ∃ g ∈ G, g ∉ normalizer (zpowers (γ * τ * γ⁻¹) : Set (Equiv.Perm (Fin n))) := by
  have hi' := allN_spec h i hi
  rw [PF.strictB_eqP] at hi'
  refine okP_sound hsz hp hhs ?_ ?_ hi'
  · have := hc.pc (hT.pc hci)
    rwa [← mul_assoc] at this
  · rw [show γ * τ * γ⁻¹ = (MulAut.conj γ) τ by simp, MulEquiv.orderOf_eq, hτ]

end CFSG.KS.Ivk8NormP

end
