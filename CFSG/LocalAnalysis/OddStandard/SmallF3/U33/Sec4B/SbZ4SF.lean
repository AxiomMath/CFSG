module

public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SD

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Pre

variable (hp : Z4Pre t L S x₁ x₂ lam rho tau)
include hp

theorem comm_tau_eq_of_comm_t_eq {a b : G} (ha : a ∈ ctxYq t tau x₁ x₂ rho)
    (hb : b ∈ ctxYq t tau x₁ x₂ rho) (h : z4Comm t a = z4Comm t b) :
    z4Comm tau a = z4Comm tau b := by
  have hd : a * b⁻¹ ∈ ctxYq t tau x₁ x₂ rho := mul_mem ha (inv_mem hb)
  have h1 : z4Comm t (a * b⁻¹) = 1 := by
    rw [hp.comm_mul hp.t_mem_X (hp.Y_le_Q ha) (inv_mem (hp.Y_le_Q hb)),
      hp.comm_inv hp.t_mem_X (hp.Y_le_Q hb), h]
    group
  have hV : a * b⁻¹ ∈ fourGrp x₁ x₂ := (hp.comm_t_eq_one_iff hd).mp h1
  have h2 : z4Comm tau (a * b⁻¹) = 1 := hp.comm_V hp.tau_mem_O hV
  rw [hp.comm_mul hp.tau_mem_X (hp.Y_le_Q ha) (inv_mem (hp.Y_le_Q hb)),
    hp.comm_inv hp.tau_mem_X (hp.Y_le_Q hb)] at h2
  exact mul_inv_eq_one.mp h2

private theorem classify {ay aw cr a₀ b₀ c₀ : G}
    (hay : ay ∈ ctxYq t tau x₁ x₂ rho) (haw : aw ∈ ctxYq t tau x₁ x₂ rho)
    (hcr : cr ∈ ctxYq t tau x₁ x₂ rho)
    (hty : z4Comm t ay = x₁ ^ 2) (htw : z4Comm t aw = x₂ ^ 2)
    (htr : z4Comm t cr = (x₁ * x₂) ^ 2)
    (hta : z4Comm tau ay = a₀) (htb : z4Comm tau aw = b₀)
    (htc : z4Comm tau cr = c₀) :
    ∀ a ∈ ctxYq t tau x₁ x₂ rho,
      (z4Comm t a = 1 ∧ z4Comm tau a = 1) ∨
      (z4Comm t a = x₁ ^ 2 ∧ z4Comm tau a = a₀) ∨
      (z4Comm t a = x₂ ^ 2 ∧ z4Comm tau a = b₀) ∨
      (z4Comm t a = (x₁ * x₂) ^ 2 ∧ z4Comm tau a = c₀) := by
  intro a ha
  have hv : z4Comm t a ∈ fourGrp x₁ x₂ := hp.comm_mem hp.t_mem_X (hp.Y_le_O ha)
  rcases (hp.mem_V_iff (z4Comm t a)).mp hv with h | h | h | h
  · left
    exact ⟨h, hp.comm_V hp.tau_mem_O ((hp.comm_t_eq_one_iff ha).mp h)⟩
  · right; left
    exact ⟨h, by rw [← hta]; exact hp.comm_tau_eq_of_comm_t_eq ha hay (by rw [h, hty])⟩
  · right; right; right
    exact ⟨h, by rw [← htc]; exact hp.comm_tau_eq_of_comm_t_eq ha hcr (by rw [h, htr])⟩
  · right; right; left
    exact ⟨h, by rw [← htb]; exact hp.comm_tau_eq_of_comm_t_eq ha haw (by rw [h, htw])⟩

theorem comm_tau_trivial_or_eq :
    (∀ a ∈ ctxYq t tau x₁ x₂ rho, z4Comm tau a = 1) ∨
      ∀ a ∈ ctxYq t tau x₁ x₂ rho, z4Comm tau a = z4Comm t a := by
  obtain ⟨ay, hay, hty⟩ := hp.exists_comm_eq (x₁ ^ 2) hp.y_mem_V
  let a₀ : G := z4Comm tau ay
  have hta : z4Comm tau ay = a₀ := rfl
  have ha₀V : a₀ ∈ fourGrp x₁ x₂ := hp.comm_mem hp.tau_mem_X (hp.Y_le_O hay)
  let aw : G := (lam * t) * ay * (lam * t)⁻¹
  have haw : aw ∈ ctxYq t tau x₁ x₂ rho :=
    hp.normal_Y.2 (lam * t) hp.sigma_mem_M ay hay
  let b₀ : G := z4Comm tau aw
  have htb : z4Comm tau aw = b₀ := rfl
  have hb₀V : b₀ ∈ fourGrp x₁ x₂ := hp.comm_mem hp.tau_mem_X (hp.Y_le_O haw)
  have htw : z4Comm t aw = x₂ ^ 2 := by
    change z4Comm t ((lam * t) * ay * (lam * t)⁻¹) = x₂ ^ 2
    rw [hp.comm_conj hp.sigma_comm_t.symm ay, hty, hp.sigma_y]
  have hb₀def : b₀ = (lam * t) * a₀ * (lam * t)⁻¹ := by
    change z4Comm tau ((lam * t) * ay * (lam * t)⁻¹) = (lam * t) * a₀ * (lam * t)⁻¹
    rw [hp.comm_conj hp.sigma_comm_tau.symm ay]
  have hmem : a₀ = 1 ∨ a₀ = x₁ ^ 2 ∨ a₀ = (x₁ * x₂) ^ 2 ∨ a₀ = x₂ ^ 2 :=
    (hp.mem_V_iff a₀).mp ha₀V
  rcases hp.rho_V with hA | hB
  · obtain ⟨hAy, hAw, hAz⟩ := hA
    let cr : G := rho * aw * rho⁻¹
    have hcr : cr ∈ ctxYq t tau x₁ x₂ rho := hp.normal_Y.2 rho hp.rho_mem_M aw haw
    have htr : z4Comm t cr = (x₁ * x₂) ^ 2 := by
      change z4Comm t (rho * aw * rho⁻¹) = (x₁ * x₂) ^ 2
      rw [hp.comm_conj hp.rho_comm_t.symm aw, htw, hAw]
    let c₀ : G := rho * b₀ * rho⁻¹
    have htc : z4Comm tau cr = c₀ := by
      change z4Comm tau (rho * aw * rho⁻¹) = rho * b₀ * rho⁻¹
      rw [hp.comm_conj hp.rho_comm_tau.symm aw]
    have hbar : rho * a₀ * rho⁻¹ = b₀ := by
      have har : rho * ay * rho⁻¹ ∈ ctxYq t tau x₁ x₂ rho :=
        hp.normal_Y.2 rho hp.rho_mem_M ay hay
      have h1 : z4Comm t (rho * ay * rho⁻¹) = z4Comm t aw := by
        rw [hp.comm_conj hp.rho_comm_t.symm ay, hty, hAy, htw]
      have h2 := hp.comm_tau_eq_of_comm_t_eq har haw h1
      rw [show z4Comm tau (rho * ay * rho⁻¹) = rho * a₀ * rho⁻¹ from by
            rw [hp.comm_conj hp.rho_comm_tau.symm ay], htb] at h2
      exact h2
    have hschur : (a₀ = 1 ∧ b₀ = 1) ∨ (a₀ = x₁ ^ 2 ∧ b₀ = x₂ ^ 2) :=
      schur_V (y := x₁ ^ 2) (z := (x₁ * x₂) ^ 2) (w := x₂ ^ 2)
        (ρ := rho) (σ := lam * t) (a := a₀) (b := b₀)
        (by simpa [pow_two] using hp.y_sq) (by simpa [pow_two] using hp.z_sq)
        hp.x₂_sq.symm (by rw [← hp.y_comm_z]; exact hp.x₂_sq.symm)
        hp.x₂_sq_ne_one hp.y_ne_z hmem
        hp.sigma_y hp.sigma_z hp.sigma_w hb₀def (Or.inl ⟨hAy, hAw, hAz, hbar.symm⟩)
    rcases hschur with ⟨ha₀1, hb₀1⟩ | ⟨ha₀y, hb₀w⟩
    · left
      intro a ha
      rcases hp.classify hay haw hcr hty htw htr hta htb htc a ha with
        ⟨_, hτ⟩ | ⟨_, hτ⟩ | ⟨_, hτ⟩ | ⟨_, hτ⟩
      · exact hτ
      · rw [hτ, ha₀1]
      · rw [hτ, hb₀1]
      · rw [hτ]; dsimp only [c₀]; rw [hb₀1]; group
    · right
      intro a ha
      rcases hp.classify hay haw hcr hty htw htr hta htb htc a ha with
        ⟨h, hτ⟩ | ⟨h, hτ⟩ | ⟨h, hτ⟩ | ⟨h, hτ⟩
      · rw [hτ, h]
      · rw [hτ, h, ha₀y]
      · rw [hτ, h, hb₀w]
      · rw [hτ, h]; dsimp only [c₀]; rw [hb₀w, hAw]
  · obtain ⟨hBy, hBz, hBw⟩ := hB
    let cr : G := rho * ay * rho⁻¹
    have hcr : cr ∈ ctxYq t tau x₁ x₂ rho := hp.normal_Y.2 rho hp.rho_mem_M ay hay
    have htr : z4Comm t cr = (x₁ * x₂) ^ 2 := by
      change z4Comm t (rho * ay * rho⁻¹) = (x₁ * x₂) ^ 2
      rw [hp.comm_conj hp.rho_comm_t.symm ay, hty, hBy]
    let c₀ : G := rho * a₀ * rho⁻¹
    have htc : z4Comm tau cr = c₀ := by
      change z4Comm tau (rho * ay * rho⁻¹) = rho * a₀ * rho⁻¹
      rw [hp.comm_conj hp.rho_comm_tau.symm ay]
    have hrel : a₀ * b₀ = rho * a₀ * rho⁻¹ := by
      have h1 : z4Comm t (ay * aw) = z4Comm t cr := by
        rw [hp.comm_mul hp.t_mem_X (hp.Y_le_Q hay) (hp.Y_le_Q haw), hty, htw, htr,
          hp.x₂_sq, ← mul_assoc, ← pow_two, hp.y_sq, one_mul]
      have h2 := hp.comm_tau_eq_of_comm_t_eq (mul_mem hay haw) hcr h1
      rw [show z4Comm tau (ay * aw) = a₀ * b₀ from by
            rw [hp.comm_mul hp.tau_mem_X (hp.Y_le_Q hay) (hp.Y_le_Q haw), hta, htb],
          htc] at h2
      exact h2
    have hschur : (a₀ = 1 ∧ b₀ = 1) ∨ (a₀ = x₁ ^ 2 ∧ b₀ = x₂ ^ 2) :=
      schur_V (y := x₁ ^ 2) (z := (x₁ * x₂) ^ 2) (w := x₂ ^ 2)
        (ρ := rho) (σ := lam * t) (a := a₀) (b := b₀)
        (by simpa [pow_two] using hp.y_sq) (by simpa [pow_two] using hp.z_sq)
        hp.x₂_sq.symm (by rw [← hp.y_comm_z]; exact hp.x₂_sq.symm)
        hp.x₂_sq_ne_one hp.y_ne_z hmem
        hp.sigma_y hp.sigma_z hp.sigma_w hb₀def (Or.inr ⟨hBy, hBz, hBw, hrel⟩)
    rcases hschur with ⟨ha₀1, hb₀1⟩ | ⟨ha₀y, hb₀w⟩
    · left
      intro a ha
      rcases hp.classify hay haw hcr hty htw htr hta htb htc a ha with
        ⟨_, hτ⟩ | ⟨_, hτ⟩ | ⟨_, hτ⟩ | ⟨_, hτ⟩
      · exact hτ
      · rw [hτ, ha₀1]
      · rw [hτ, hb₀1]
      · rw [hτ]; dsimp only [c₀]; rw [ha₀1]; group
    · right
      intro a ha
      rcases hp.classify hay haw hcr hty htw htr hta htb htc a ha with
        ⟨h, hτ⟩ | ⟨h, hτ⟩ | ⟨h, hτ⟩ | ⟨h, hτ⟩
      · rw [hτ, h]
      · rw [hτ, h, ha₀y]
      · rw [hτ, h, hb₀w]
      · rw [hτ, h]; dsimp only [c₀]; rw [ha₀y, hBy]

theorem dichotomy :
    (∀ a ∈ ctxYq t tau x₁ x₂ rho, tau * a = a * tau) ∨
      ∀ a ∈ ctxYq t tau x₁ x₂ rho, (t * tau) * a = a * (t * tau) := by
  rcases hp.comm_tau_trivial_or_eq with h | h
  · left
    intro a ha
    exact hp.comm_eq_one_iff.mp (h a ha)
  · right
    intro a ha
    rw [← hp.comm_eq_one_iff, hp.comm_ttau (hp.Y_le_Q ha), h a ha]
    have hv : z4Comm t a ∈ fourGrp x₁ x₂ := hp.comm_mem hp.t_mem_X (hp.Y_le_O ha)
    have h2 := hp.Y_sq (hp.V_le_Y hv)
    rwa [pow_two] at h2

end Z4Pre

end CFSG.OddStandard.SmallF3.HarrisU33
