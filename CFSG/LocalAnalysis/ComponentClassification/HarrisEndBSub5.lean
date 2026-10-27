module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBNorm2
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBSub3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42 CFSG.ComponentClassification.J2Cover CFSG.Sporadic.Schreier
open CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace EndB.JLayer

variable {hs : Setting46e t L p f S w z V i j}
  {π : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →* P}

theorem exists_v0
    (hJ : JLayer hs π) (hπi : Function.Injective π)
    {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (htW : t ∈ W) {c : Equiv.Perm (Fin 315)} (hcR : c ∈ R)
    (hc : ∀ x : Equiv.Perm (Fin 315),
      x ∈ piSub π (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (W ⊓ oP W)) ⊔
        zpowers ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315)) ↔
      c⁻¹ * x * c ∈ vModel.sub ⊔ zpowers u0)
    {e' : ℕ → X} (h' : IdxModel 128 e' vT vI 0) (hsub : h'.sub = W ⊓ oP W)
    (hφ : ∀ k < 128, ∃ hk : e' k ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
      ∃ hkE : (QuotientGroup.mk ⟨e' k, hk⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c = vE k) :
    ∃ v₀ < 128, vT v₀ (vT (vCu v₀) vUsq) = 0 ∧ ∀ k < 128, t * e' k * t⁻¹ = e' (vAc v₀ k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hrtP, hrt2, hrtconj⟩ := hJ.rt_facts
  obtain ⟨-, hcu, husq⟩ := (u0_facts).2
  set rt := ((rAutEquiv.symm (hJ.theta (hs.setup.tBar i j)) : R) : Equiv.Perm (Fin 315))
    with hrt
  have hαS : c⁻¹ * rt * c ∈ vModel.sub ⊔ zpowers u0 := (hc rt).mp (mem_sup_right (mem_zpowers _))
  have hαP : c⁻¹ * rt * c ∉ P := by
    intro h
    apply hrtP
    have := (mem_normalizer_iff.mp (R_le_normalizer hcR) _).mp h
    rwa [show c * (c⁻¹ * rt * c) * c⁻¹ = rt by group] at this
  obtain ⟨v₀, hv₀, hv₀e⟩ := isSylowOf_SA0.2.1 _ hαS hαP
  have hα : c⁻¹ * rt * c = vE v₀ * u0 := by rw [hv₀e]; group
  have hcu₀ := vCu_facts
  have husq₀ := vUsq_lt
  refine ⟨v₀, hv₀, ?_, fun k hk => ?_⟩
  ·
    have hrt2' : rt * rt = 1 := by rw [← sq]; exact hrt2
    have h1 : (c⁻¹ * rt * c) * (c⁻¹ * rt * c) = 1 := by
      rw [show (c⁻¹ * rt * c) * (c⁻¹ * rt * c) = c⁻¹ * (rt * rt) * c by group, hrt2']
      group
    have hq : vE (vT v₀ (vT (vCu v₀) vUsq)) = vE 0 := by
      rw [vModel.e_T _ hv₀ _ (vModel.T_lt _ (hcu₀ v₀ hv₀).1 _ husq₀),
        vModel.e_T _ (hcu₀ v₀ hv₀).1 _ husq₀, ← hcu v₀ hv₀, ← husq, vModel.e_o, ← h1, hα]
      group
    exact vModel.inj _ (vModel.T_lt _ hv₀ _ (vModel.T_lt _ (hcu₀ v₀ hv₀).1 _ husq₀)) _
      (by norm_num) hq
  ·
    have hm : vAc v₀ k < 128 :=
      vModel.T_lt _ (vModel.T_lt _ hv₀ _ (hcu₀ k hk).1) _ (vModel.I_lt _ hv₀)
    obtain ⟨hk1, hkE, hk2⟩ := hφ k hk
    obtain ⟨hm1, hmE, hm2⟩ := hφ _ hm
    have hkV : e' k ∈ W ⊓ oP W := hsub ▸ h'.e_mem hk
    have hmV : e' (vAc v₀ k) ∈ W ⊓ oP W := hsub ▸ h'.e_mem hm
    have htk : t * e' k * t⁻¹ ∈ W ⊓ oP W :=
      conj_mem_inf' conj_mem_W conj_mem_oP t (le_normalizer_self htW) _ hkV
    have hWM := hW.le
    have hV₀M : W ⊓ oP W ≤ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) :=
      inf_le_left.trans hWM
    set l' : ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) :=
      ⟨hs.setup.tBar i j * QuotientGroup.mk ⟨e' k, hk1⟩ * (hs.setup.tBar i j)⁻¹,
        (inferInstance : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal).conj_mem _
          hkE _⟩ with hl'
    have hl'eq : (l' : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        QuotientGroup.mk ⟨t * e' k * t⁻¹, hV₀M htk⟩ := by
      rw [hl']
      change _ = QuotientGroup.mk ((⟨t, hs.setup.t_mem_centralizer_beta i j⟩ :
        ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) * ⟨e' k, hk1⟩ *
          (⟨t, hs.setup.t_mem_centralizer_beta i j⟩ :
            ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))⁻¹)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rfl
    have hπl' := hrtconj ⟨_, hkE⟩ l' rfl
    have himg : c⁻¹ * ((π l' : P) : Equiv.Perm (Fin 315)) * c = vE (vAc v₀ k) := by
      rw [← hπl']
      calc c⁻¹ * (rt * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * rt⁻¹) * c =
          (c⁻¹ * rt * c) * (c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c) *
            (c⁻¹ * rt * c)⁻¹ := by group
        _ = vE v₀ * (u0 * vE k * u0⁻¹) * (vE v₀)⁻¹ := by rw [hk2, hα]; group
        _ = vE (vAc v₀ k) := by
          rw [hcu k hk, ← vModel.e_I v₀ hv₀, ← vModel.e_T _ hv₀ _ (hcu₀ k hk).1,
            ← vModel.e_T _ (vModel.T_lt _ hv₀ _ (hcu₀ k hk).1) _ (vModel.I_lt _ hv₀)]
          rfl
    have hπeq : π l' = π ⟨_, hmE⟩ := by
      apply Subtype.ext
      have := himg.trans hm2.symm
      exact mul_left_cancel (mul_right_cancel this)
    have hleq := congrArg Subtype.val (hπi hπeq)
    rw [hl'eq] at hleq
    exact mk_injOn hV₀M (hW.isPGroup.to_le inf_le_left) htk hmV hleq

theorem eq_of_comm_basis
    (hJ : JLayer hs π)
    (hQ : pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
      zpowers (betaBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hβW : w ^ (orderOf w / 2) * t ^ i * z ^ j ∈ W) {c : Equiv.Perm (Fin 315)} (hcR : c ∈ R)
    {e' : ℕ → X} (h' : IdxModel 128 e' vT vI 0) (hsub : h'.sub = W ⊓ oP W)
    (hφ : ∀ k < 128, ∃ hk : e' k ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
      ∃ hkE : (QuotientGroup.mk ⟨e' k, hk⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)),
      c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c = vE k)
    {x : X} (hxW : x ∈ W) (hxc : ∀ k ∈ vBasis, x * e' k = e' k * x) :
    x = 1 ∨ x = w ^ (orderOf w / 2) * t ^ i * z ^ j ∨ x = e' 1 ∨
      x = w ^ (orderOf w / 2) * t ^ i * z ^ j * e' 1 := by
  have hWM := hW.le
  have hW2 := hW.isPGroup
  have hxM := hWM hxW
  have hβ2 := orderOf_eq_prime hs.betaBar_sq hs.betaBar_ne_one
  set rx := rAutEquiv.symm (hJ.theta (QuotientGroup.mk ⟨x, hxM⟩)) with hrx
  have hrxθ : rAutEquiv rx = hJ.theta (QuotientGroup.mk ⟨x, hxM⟩) := MulEquiv.apply_symm_apply _ _
  have hcomm : ∀ k ∈ vBasis, (c⁻¹ * (rx : Equiv.Perm (Fin 315)) * c) * vE k =
      vE k * (c⁻¹ * (rx : Equiv.Perm (Fin 315)) * c) := by
    intro k hkB
    have hk : k < 128 := by
      simp only [vBasis, List.mem_cons, List.not_mem_nil, or_false] at hkB
      omega
    obtain ⟨hk1, hkE, hk2⟩ := hφ k hk
    have hxe : (⟨x, hxM⟩ : ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) *
        ⟨e' k, hk1⟩ = ⟨e' k, hk1⟩ * ⟨x, hxM⟩ := Subtype.ext (hxc k hkB)
    have hfix := hJ.theta_apply (QuotientGroup.mk ⟨x, hxM⟩) ⟨_, hkE⟩ ⟨_, hkE⟩ (by
      change (QuotientGroup.mk ⟨e' k, hk1⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) =
        QuotientGroup.mk (⟨x, hxM⟩ * ⟨e' k, hk1⟩ * (⟨x, hxM⟩ :
          ↥(centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))⁻¹)
      rw [hxe]
      group)
    rw [← hrxθ, rAutEquiv_apply] at hfix
    have h1 : (rx : Equiv.Perm (Fin 315)) * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) *
        (rx : Equiv.Perm (Fin 315))⁻¹ = ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) := by
      rw [← rConj_apply, hfix]
    rw [← hk2]
    calc c⁻¹ * (rx : Equiv.Perm (Fin 315)) * c *
          (c⁻¹ * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) * c) =
        c⁻¹ * ((rx : Equiv.Perm (Fin 315)) * ((π ⟨_, hkE⟩ : P) : Equiv.Perm (Fin 315)) *
          (rx : Equiv.Perm (Fin 315))⁻¹) * (rx : Equiv.Perm (Fin 315)) * c := by group
      _ = _ := by rw [h1]; group
  have hcrc : c⁻¹ * (rx : Equiv.Perm (Fin 315)) * c ∈ R :=
    mul_mem (mul_mem (inv_mem hcR) rx.2) hcR
  have he1W : e' 1 ∈ W := (mem_inf.mp (hsub ▸ h'.e_mem (by norm_num) : e' 1 ∈ W ⊓ oP W)).1
  rcases eq_of_centralizes_basis hcrc hcomm with h | h
  ·
    have hrx1 : rx = 1 := Subtype.ext (by
      calc (rx : Equiv.Perm (Fin 315)) = c * (c⁻¹ * (rx : Equiv.Perm (Fin 315)) * c) * c⁻¹ := by
            group
        _ = 1 := by rw [h]; group)
    have hθ : hJ.theta (QuotientGroup.mk ⟨x, hxM⟩) = 1 := by rw [← hrxθ, hrx1, map_one]
    rw [hJ.theta_eq_one_iff, hQ] at hθ
    rcases eq_one_or_eq_of_mem_zpowers hβ2 hθ with h1 | h1
    · left
      exact mk_injOn hWM hW2 hxW (one_mem W) (by rw [h1]; rfl)
    · right
      left
      exact mk_injOn hWM hW2 hxW hβW (by rw [h1]; rfl)
  ·
    obtain ⟨h11, h1E, h12⟩ := hφ 1 (by norm_num)
    have hrxe : (rx : Equiv.Perm (Fin 315)) = ((π ⟨_, h1E⟩ : P) : Equiv.Perm (Fin 315)) := by
      calc (rx : Equiv.Perm (Fin 315)) = c * (c⁻¹ * (rx : Equiv.Perm (Fin 315)) * c) * c⁻¹ := by
            group
        _ = c * vE 1 * c⁻¹ := by rw [h, vE_one]
        _ = _ := by rw [← h12]; group
    have hrxeq : rx = ⟨((π ⟨_, h1E⟩ : P) : Equiv.Perm (Fin 315)), P_le_R (π ⟨_, h1E⟩).2⟩ :=
      Subtype.ext hrxe
    have hθ : hJ.theta (QuotientGroup.mk ⟨x, hxM⟩) = hJ.theta (QuotientGroup.mk ⟨e' 1, h11⟩) := by
      rw [← hrxθ, hrxeq, rAutEquiv_of_mem]
      exact (hJ.theta_conj ⟨_, h1E⟩).symm
    have hq : (QuotientGroup.mk ⟨x, hxM⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) *
        (QuotientGroup.mk ⟨e' 1, h11⟩)⁻¹ ∈
          pCore 2 (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← hJ.theta_eq_one_iff, map_mul, map_inv, hθ, mul_inv_cancel]
    rw [hQ] at hq
    rcases eq_one_or_eq_of_mem_zpowers hβ2 hq with h1 | h1
    · right
      right
      left
      refine mk_injOn hWM hW2 hxW he1W ?_
      rw [mul_inv_eq_one] at h1
      exact h1
    · right
      right
      right
      refine mk_injOn hWM hW2 hxW (mul_mem hβW he1W) ?_
      rw [mul_inv_eq_iff_eq_mul] at h1
      rw [h1]
      rfl

end EndB.JLayer

end CFSG.ComponentClassification.HarrisLit
