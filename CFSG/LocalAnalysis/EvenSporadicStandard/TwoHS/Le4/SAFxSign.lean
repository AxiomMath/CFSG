module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFxDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignE
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignF
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignG
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFyHInspect
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoHS.Le4.SAFySignD

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoHS

open Subgroup

section Lemmas

variable {G : Type} [Group G] [Finite G] {t r : G} {Θ : HModel →* G}

theorem FyConf.conj_of_redX (h : FyConf t r Θ) (m : HModel) (hm : m * m = 1)
    (hconj : ∃ x : RedX r, h.Phi m = x * h.tauX * x⁻¹) :
    ∃ g : G, g * r = r * g ∧ Θ m = g * t * g⁻¹ := by
  obtain ⟨x, hx⟩ := hconj
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  set T : RedC r := h.thetaC (DihedralGroup.r 2, 1, 1) with hT
  set W : RedC r := h.thetaC m with hW
  have hT_G : (T : G) = t := h.t_eq
  have hTT : T * T = 1 := by
    rw [hT, ← map_mul]
    have : ((DihedralGroup.r 2 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
        (DihedralGroup.r 2, 1, 1) = 1 := by decide
    rw [this, map_one]
  have hWW : W * W = 1 := by
    rw [hW, ← map_mul, hm, map_one]
  have haa : (y * T * y⁻¹) * (y * T * y⁻¹) = 1 := by
    calc (y * T * y⁻¹) * (y * T * y⁻¹) = y * (T * T) * y⁻¹ := by group
      _ = 1 := by rw [hTT]; group
  have hab : (y * T * y⁻¹)⁻¹ * W ∈ RedO r := by
    rw [← QuotientGroup.eq_one_iff]
    have h1 : (QuotientGroup.mk W : RedX r) = QuotientGroup.mk (y * T * y⁻¹) := by
      have e1 : (QuotientGroup.mk W : RedX r) = h.Phi m := rfl
      have e2 : (QuotientGroup.mk T : RedX r) = h.tauX := rfl
      rw [e1, hx]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [e2]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1 ⊢
    rw [h1]; group
  obtain ⟨n, hnO, hn⟩ := exists_conj_of_odd (O := RedO r) (redO_odd r) haa hWW hab
  refine ⟨((n * y : RedC r) : G), mem_centralizer_singleton_iff.1 (n * y).2, ?_⟩
  have h2 := congrArg Subtype.val hn
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [hT_G] at h2
  show (W : G) = ((n * y : RedC r) : G) * t * ((n * y : RedC r) : G)⁻¹
  simp only [Subgroup.coe_mul]
  calc (W : G) = (n : G) * ((y : G) * t * (y : G)⁻¹) * (n : G)⁻¹ := h2.symm
    _ = (n : G) * (y : G) * t * ((n : G) * (y : G))⁻¹ := by group

theorem FyConf.redX_conj_of_conj (h : FyConf t r Θ) (m : HModel) {g : G} (hg : g * r = r * g)
    (hm : Θ m = g * t * g⁻¹) : ∃ x : RedX r, h.Phi m = x * h.tauX * x⁻¹ := by
  set T : RedC r := h.thetaC (DihedralGroup.r 2, 1, 1) with hT
  have hT_G : (T : G) = t := h.t_eq
  set gC : RedC r := ⟨g, mem_centralizer_singleton_iff.2 hg⟩ with hgC
  have hWT : h.thetaC m = gC * T * gC⁻¹ := by
    apply Subtype.ext
    show Θ m = g * (T : G) * g⁻¹
    rw [hT_G]; exact hm
  refine ⟨redPi r gC, ?_⟩
  rw [h.Phi_eq_redPi, hWT, map_mul, map_mul, map_inv]
  rfl

theorem FyConf.chi_formula (h : FyConf t r Θ) (χ : RedX r →* ℤˣ)
    (hχD : ∀ d ∈ h.subD, orderOf d = 4 → χ d = -1)
    (hχS : ∀ s : h.subS, Equiv.Perm.sign (h.eS s) = -1 → χ s = -1)
    (d : DihedralGroup 4) (c : Z3) (σ : Equiv.Perm (Fin 5)) :
    χ (h.Phi (d, c, σ)) = dihChar (χ (h.Phi (DihedralGroup.sr 0, 1, 1))) d *
      Equiv.Perm.sign σ := by
  have hlamS : χ.comp (h.Phi.comp embS) = Equiv.Perm.sign := by
    apply eq_sign_of_odd
    intro σ hσ
    have := hχS ⟨h.Phi (1, 1, σ), h.mem_subS σ⟩ (by rw [h.eS_apply]; exact hσ)
    exact this
  have hlamD1 : (χ.comp (h.Phi.comp embD)) (DihedralGroup.r 1) = -1 := by
    have hord : orderOf (h.Phi (embD (DihedralGroup.r 1))) = 4 := by
      have := orderOf_injective (h.Phi.comp embD) h.injD (DihedralGroup.r 1)
      rw [DihedralGroup.orderOf_r_one] at this
      exact this
    exact hχD _ (h.mem_subD _) hord
  rw [h.Phi_split, map_mul]
  have hD := dihChar_of_hom hlamD1 d
  have hS := congrArg (fun f => f σ) hlamS
  exact congrArg₂ (· * ·) hD hS

theorem FyConf.false_of_pg (h : FyConf t r Θ) (χ : RedX r →* ℤˣ)
    (hχD : ∀ d ∈ h.subD, orderOf d = 4 → χ d = -1)
    (hχS : ∀ s : h.subS, Equiv.Perm.sign (h.eS s) = -1 → χ s = -1)
    (F1 : ∀ d ∈ h.subD, d ≠ 1 → d ≠ h.tauX → d * d = 1 →
      ¬ ∃ g : RedX r, d = g * h.tauX * g⁻¹)
    (F2 : ∀ d ∈ h.subD, d ≠ 1 → d ≠ h.tauX → d * d = 1 → χ d = -1 →
      ∀ s ∈ h.subS, s ≠ 1 → s * s = 1 → χ s = -1 → ∃ g : RedX r, d * s = g * h.tauX * g⁻¹)
    {k : ZMod 4} {σ : Equiv.Perm (Fin 5)}
    (hpar : dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1)
    (hw : ∃ g : G, g * r = r * g ∧ Θ (DihedralGroup.sr k, 1, σ) = g * t * g⁻¹) : False := by
  have hform := h.chi_formula χ hχD hχS
  set b : ℤˣ := χ (h.Phi (DihedralGroup.sr 0, 1, 1)) with hb
  have hχτ : χ h.tauX = 1 := by
    have := hform (DihedralGroup.r 2) 1 1
    rw [map_one, dihChar_r_two, mul_one] at this
    exact this
  have hb1 : b = 1 := by
    obtain ⟨g, hg, hu⟩ := hw
    obtain ⟨x, hx⟩ := h.redX_conj_of_conj (DihedralGroup.sr k, 1, σ) hg hu
    have h1 : χ (h.Phi (DihedralGroup.sr k, 1, σ)) = 1 := by
      rw [hx, map_mul, map_mul, map_inv, hχτ]
      simp
    rw [hform, dihChar_sr_eq, mul_assoc, hpar, mul_one] at h1
    exact h1
  have hd1 : h.Phi (DihedralGroup.sr 1, 1, 1) ≠ 1 := fun e =>
    absurd ((h.Phi_eq_one_iff _).1 e).1 (sr_ne_one 1)
  have hd1τ : h.Phi (DihedralGroup.sr 1, 1, 1) ≠ h.tauX := by
    intro e
    have := h.injD (a₁ := DihedralGroup.sr 1) (a₂ := DihedralGroup.r 2) e
    exact absurd this (sr_ne_r2 1)
  have hd1d1 : h.Phi (DihedralGroup.sr 1, 1, 1) * h.Phi (DihedralGroup.sr 1, 1, 1) = 1 := by
    rw [← map_mul]
    have : ((DihedralGroup.sr 1 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
        (DihedralGroup.sr 1, 1, 1) = 1 := by
      ext <;> simp [sr_sq 1]
    rw [this, map_one]
  have hχd1 : χ (h.Phi (DihedralGroup.sr 1, 1, 1)) = -1 := by
    have := hform (DihedralGroup.sr 1) 1 1
    rw [map_one, mul_one] at this
    rw [this, dihChar_sr, hb1]
    have h1 : (1 : ZMod 4).val = 1 := rfl
    simp [h1]
  have hs1 : h.Phi (1, 1, Equiv.swap 0 1) ≠ 1 := fun e => by
    have := ((h.Phi_eq_one_iff _).1 e).2
    exact absurd this (by decide)
  have hs1s1 : h.Phi (1, 1, Equiv.swap 0 1) * h.Phi (1, 1, Equiv.swap 0 1) = 1 := by
    rw [← map_mul]
    have : ((1 : DihedralGroup 4), (1 : Z3), Equiv.swap (0 : Fin 5) 1) *
        (1, 1, Equiv.swap 0 1) = 1 := by
      ext <;> simp
    rw [this, map_one]
  have hχs1 : χ (h.Phi (1, 1, Equiv.swap 0 1)) = -1 := by
    have := hform 1 1 (Equiv.swap 0 1)
    have h2 : dihChar (χ (h.Phi (DihedralGroup.sr 0, 1, 1))) 1 = 1 := dihChar_one _
    rw [this, h2, one_mul]
    exact Equiv.Perm.sign_swap (by decide)
  obtain ⟨x₁, hx₁⟩ := F2 _ (h.mem_subD _) hd1 hd1τ hd1d1 hχd1 _ (h.mem_subS _) hs1 hs1s1 hχs1
  have hc : h.Phi (DihedralGroup.sr 1, 1, Equiv.swap 0 1) =
      h.Phi (DihedralGroup.sr 1, 1, 1) * h.Phi (1, 1, Equiv.swap 0 1) :=
    h.Phi_split (DihedralGroup.sr 1) 1 (Equiv.swap 0 1)
  have hcc : ((DihedralGroup.sr 1 : DihedralGroup 4), (1 : Z3), Equiv.swap (0 : Fin 5) 1) *
      (DihedralGroup.sr 1, 1, Equiv.swap 0 1) = 1 := by
    ext <;> simp [sr_sq 1]
  obtain ⟨g₁, hg₁r, hg₁⟩ := h.conj_of_redX (DihedralGroup.sr 1, 1, Equiv.swap 0 1) hcc
    ⟨x₁, by rw [hc]; exact hx₁⟩
  obtain ⟨nf, hnf, hnf'⟩ := h.fusion
  have ha : Θ (DihedralGroup.sr 0, 1, 1) = (nf⁻¹ * g₁) * t * (nf⁻¹ * g₁)⁻¹ := by
    have e1 : Θ (DihedralGroup.sr 0, 1, 1) = nf⁻¹ * Θ (DihedralGroup.sr 1, 1, Equiv.swap 0 1) *
        nf := by
      rw [← hnf']; group
    rw [e1, hg₁]; group
  obtain ⟨g₃, hg₃r, hg₃⟩ := h.exists_conj_cent (h.comm_r (DihedralGroup.sr 0, 1, 1))
    ⟨nf⁻¹ * g₁, ha⟩
  obtain ⟨x₃, hx₃⟩ := h.redX_conj_of_conj (DihedralGroup.sr 0, 1, 1) hg₃r hg₃
  have hd0 : h.Phi (DihedralGroup.sr 0, 1, 1) ≠ 1 := fun e =>
    absurd ((h.Phi_eq_one_iff _).1 e).1 (sr_ne_one 0)
  have hd0τ : h.Phi (DihedralGroup.sr 0, 1, 1) ≠ h.tauX := by
    intro e
    have := h.injD (a₁ := DihedralGroup.sr 0) (a₂ := DihedralGroup.r 2) e
    exact absurd this (sr_ne_r2 0)
  have hd0d0 : h.Phi (DihedralGroup.sr 0, 1, 1) * h.Phi (DihedralGroup.sr 0, 1, 1) = 1 := by
    rw [← map_mul]
    have : ((DihedralGroup.sr 0 : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
        (DihedralGroup.sr 0, 1, 1) = 1 := by
      ext <;> simp [sr_sq 0]
    rw [this, map_one]
  exact F1 _ (h.mem_subD _) hd0 hd0τ hd0d0 ⟨x₃, hx₃⟩

end Lemmas

@[expose] def SignTheoremXW : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (t r : G) (Θ : HModel →* G), FyConf t r Θ →
    ∀ (k : ZMod 4) (σ : Equiv.Perm (Fin 5)),
      dihChar 1 (DihedralGroup.sr k) * Equiv.Perm.sign σ = 1 →
      (∃ g : G, g * r = r * g ∧ Θ (DihedralGroup.sr k, 1, σ) = g * t * g⁻¹) →
      ∃ (χ : ↥(centralizer ({r} : Set G)) →* ℤˣ) (b : ℤˣ),
        (∀ (d : DihedralGroup 4) (c : Z3) (σ : Equiv.Perm (Fin 5))
          (h : Θ (d, c, σ) ∈ centralizer ({r} : Set G)),
          χ ⟨Θ (d, c, σ), h⟩ = dihChar b d * Equiv.Perm.sign σ) ∧
        (∀ (k : ZMod 4) (σ : Equiv.Perm (Fin 5)), σ ≠ 1 → σ * σ = 1 → Equiv.Perm.sign σ = 1 →
          dihChar b (DihedralGroup.sr k) = 1 →
          ¬ ∃ g : G, g * r = r * g ∧ Θ (DihedralGroup.sr k, 1, σ) = g * t * g⁻¹)

variable {G : Type} [Group G] [Finite G] {t r : G} {Θ : HModel →* G}

theorem signTheoremXW (hGH : GH312WrFixed) (hS9 : SignDataS9X)
    (hWr : SignDataWrX) (hPG : SignDataPGSpXS) : SignTheoremXW := by
  intro G _ _ t r Θ h k₀ σ₀ hpar₀ hw₀
  obtain ⟨P, hP⟩ := h.exists_sylow
  have hu : ∃ u : RedX r, u * u = 1 ∧ u ≠ 1 ∧
      Nonempty (↥(centralizer ({u} : Set (RedX r))) ≃* DihedralGroup 4 × Equiv.Perm (Fin 5)) :=
    ⟨h.tauX, h.tauX_sq, h.tauX_ne_one, ⟨h.centEquiv⟩⟩
  have hX := hGH (RedX r) pPrimeCore_quotient_bot h.center_eq_bot ⟨P, hP⟩ hu
  obtain ⟨χ, hχD, hχS, hχI⟩ : ∃ χ : RedX r →* ℤˣ, (∀ d ∈ h.subD, orderOf d = 4 → χ d = -1) ∧
      (∀ s : h.subS, Equiv.Perm.sign (h.eS s) = -1 → χ s = -1) ∧
      (∀ d ∈ h.subD, d ≠ 1 → d ≠ h.tauX → d * d = 1 → χ d = 1 →
        ∀ s ∈ h.subS, s ≠ 1 → s * s = 1 → χ s = 1 → ¬ ∃ g : RedX r, d * s = g * h.tauX * g⁻¹) := by
    rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
    · exact hS9 (RedX r) φ h.tauX h.subD h.subS h.eD h.eS h.localPair
    · exact hWr (RedX r) φ h.tauX h.subD h.subS h.eD h.eS h.localPair
    · exfalso
      obtain ⟨χ, hχD, hχS, F1, F2⟩ :=
        hPG (RedX r) φ h.tauX h.subD h.subS h.eD h.eS ⟨P, hP⟩ h.localPair
      exact h.false_of_pg χ hχD hχS F1 F2 hpar₀ hw₀
  have hform := h.chi_formula χ hχD hχS
  refine ⟨χ.comp (redPi r), χ (h.Phi (DihedralGroup.sr 0, 1, 1)), ?_, ?_⟩
  · intro d c σ hmem
    have e0 : (⟨Θ (d, c, σ), hmem⟩ : RedC r) = h.thetaC (d, c, σ) := Subtype.ext rfl
    show χ (redPi r ⟨Θ (d, c, σ), hmem⟩) = _
    rw [e0]
    exact hform d c σ
  · intro k σ hσ1 hσ2 hσs hk
    rintro ⟨g, hgr, hg⟩
    have hdk : dihChar (χ (h.Phi (DihedralGroup.sr 0, 1, 1))) (DihedralGroup.sr k) = 1 := hk
    have hd1 : h.Phi (DihedralGroup.sr k, 1, 1) ≠ 1 := fun e =>
      absurd ((h.Phi_eq_one_iff _).1 e).1 (sr_ne_one k)
    have hdτ : h.Phi (DihedralGroup.sr k, 1, 1) ≠ h.tauX := by
      intro e
      have := h.injD (a₁ := DihedralGroup.sr k) (a₂ := DihedralGroup.r 2) e
      exact absurd this (sr_ne_r2 k)
    have hdd : h.Phi (DihedralGroup.sr k, 1, 1) * h.Phi (DihedralGroup.sr k, 1, 1) = 1 := by
      rw [← map_mul]
      have : ((DihedralGroup.sr k : DihedralGroup 4), (1 : Z3), (1 : Equiv.Perm (Fin 5))) *
          (DihedralGroup.sr k, 1, 1) = 1 := by
        ext <;> simp [sr_sq k]
      rw [this, map_one]
    have hχd : χ (h.Phi (DihedralGroup.sr k, 1, 1)) = 1 := by
      have := hform (DihedralGroup.sr k) 1 1
      rw [map_one] at this
      simpa [hdk] using this
    have hs1 : h.Phi (1, 1, σ) ≠ 1 := fun e => hσ1 ((h.Phi_eq_one_iff _).1 e).2
    have hss : h.Phi (1, 1, σ) * h.Phi (1, 1, σ) = 1 := by
      rw [← map_mul]
      have : ((1 : DihedralGroup 4), (1 : Z3), σ) * (1, 1, σ) = 1 := by
        ext <;> simp [hσ2]
      rw [this, map_one]
    have hχs : χ (h.Phi (1, 1, σ)) = 1 := by
      have := hform 1 1 σ
      rw [this, dihChar_one, one_mul]
      exact hσs
    refine hχI _ (h.mem_subD _) hd1 hdτ hdd hχd _ (h.mem_subS σ) hs1 hss hχs ?_
    have hgC : g ∈ centralizer ({r} : Set G) := mem_centralizer_singleton_iff.2 hgr
    set gC : RedC r := ⟨g, hgC⟩ with hgCdef
    have hTG : ((h.thetaC (DihedralGroup.r 2, 1, 1) : RedC r) : G) = t := h.t_eq
    have hWT : h.thetaC (DihedralGroup.sr k, 1, σ) =
        gC * h.thetaC (DihedralGroup.r 2, 1, 1) * gC⁻¹ := by
      apply Subtype.ext
      show Θ (DihedralGroup.sr k, 1, σ) = g * ((h.thetaC (DihedralGroup.r 2, 1, 1) : RedC r) : G) *
        g⁻¹
      rw [hTG]; exact hg
    refine ⟨redPi r gC, ?_⟩
    have e1 : h.Phi (DihedralGroup.sr k, 1, σ) =
        h.Phi (DihedralGroup.sr k, 1, 1) * h.Phi (1, 1, σ) := by
      have := h.Phi_split (DihedralGroup.sr k) 1 σ
      exact this
    rw [← e1, h.Phi_eq_redPi, hWT, map_mul, map_mul, map_inv]
    rfl

end CFSG.EvenSporadicStandard.TwoHS
