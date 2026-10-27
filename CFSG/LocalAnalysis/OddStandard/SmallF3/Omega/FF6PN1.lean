module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PN1Aux1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V}

theorem ff6p_omega_mono_eq_hat (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {σ : Equiv.Perm (Fin 5)} {K : Finset (Option (Fin 5))}
    (h : fr.pOrth σ * fr.signChange K ∈ omegaGroup hQ) :
    ∃ b ∈ ffB0p fr, fr.pOrth σ * fr.signChange K = ffHat fr σ * b := by
  have hcrit := (ff6p_mem_omega_iff hQ fr σ K).mp h
  refine ⟨fr.signChange (K.erase none), ?_, ?_⟩
  · exact (mem_ffB0p_iff fr).mpr ⟨K.erase none, Finset.notMem_erase none K, hcrit.2, rfl⟩
  · rw [ffHat, mul_assoc, fr.signChange_mul, ffOutFF6PN1_symmDiff_erase K σ hcrit.1]

@[expose] noncomputable def ffN0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Subgroup (OGroup Q) :=
  omegaGroup hQ ⊓ Subgroup.normalizer (ffB0p fr : Set (OGroup Q))

theorem mem_ffN0p_iff (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} :
    g ∈ ffN0p hQ fr ↔ ∃ σ : Equiv.Perm (Fin 5), ∃ b ∈ ffB0p fr, g = ffHat fr σ * b := by
  constructor
  · intro hg
    rw [ffN0p, Subgroup.mem_inf] at hg
    obtain ⟨hgω, hgN⟩ := hg
    have hinvN : g⁻¹ ∈ Subgroup.normalizer (ffB0p fr : Set (OGroup Q)) :=
      (Subgroup.normalizer (ffB0p fr : Set (OGroup Q))).inv_mem hgN
    have hnorm : ∀ b ∈ ffB0p fr, simAct Q (orthToSim Q g)⁻¹ b ∈ ffB0p fr ∨
        piOrth Q * simAct Q (orthToSim Q g)⁻¹ b ∈ ffB0p fr := by
      intro b hb
      left
      have h1 : g⁻¹ * b * (g⁻¹)⁻¹ ∈ ffB0p fr :=
        (Subgroup.mem_normalizer_iff.mp hinvN b).mp hb
      have h2 : simAct Q (orthToSim Q g)⁻¹ b = g⁻¹ * b * (g⁻¹)⁻¹ := by
        rw [← map_inv, simAct_orthToSim]
      rw [h2]; exact h1
    obtain ⟨σ, K, hσK⟩ := ff6p_mono_of_normalizes fr (orthToSim Q g) hnorm
    have hg_eq : g = fr.pOrth σ * fr.signChange K := orthToSim_injective hσK
    have hmem : fr.pOrth σ * fr.signChange K ∈ omegaGroup hQ := by rw [← hg_eq]; exact hgω
    obtain ⟨b, hb, hb_eq⟩ := ff6p_omega_mono_eq_hat hQ fr hmem
    exact ⟨σ, b, hb, by rw [hg_eq, hb_eq]⟩
  · rintro ⟨σ, b, hb, rfl⟩
    rw [ffN0p, Subgroup.mem_inf]
    refine ⟨Subgroup.mul_mem _ (ffHat_mem_omega hQ fr σ) (ffB0p_le_omega hQ fr hb), ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact ffOutFF6PN1_conj_mem_B0 fr σ hb hh
    · intro hh
      obtain ⟨J, hJe, hbJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hb
      have hinv : (ffHat fr σ * b)⁻¹ = ffHat fr σ⁻¹ * fr.signChange (ffOpt (ffAct σ J)) := by
        rw [hbJ]; exact ffOutFF6PN1_inv_hat_mul fr σ J
      have hb' : fr.signChange (ffOpt (ffAct σ J)) ∈ ffB0p fr :=
        (mem_ffB0p_iff_ffOpt fr).mpr ⟨ffAct σ J, by rw [ffAct_card]; exact hJe, rfl⟩
      have hthis := ffOutFF6PN1_conj_mem_B0 fr σ⁻¹ hb' hh
      rw [← hinv] at hthis
      have heq : (ffHat fr σ * b)⁻¹ * ((ffHat fr σ * b) * h * (ffHat fr σ * b)⁻¹) *
          ((ffHat fr σ * b)⁻¹)⁻¹ = h := by group
      rwa [heq] at hthis

theorem ffN0p_le_ffMonoP (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffN0p hQ fr ≤ ffMonoP fr := by
  intro g hg
  obtain ⟨σ, b, hb, rfl⟩ := (mem_ffN0p_iff hQ fr).mp hg
  obtain ⟨J, -, hbJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hb
  rw [hbJ, ffHat, mul_assoc, fr.signChange_mul]
  exact mono_mem_ffMonoP fr σ _

theorem ffP0p_le_ffN0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffP0p hQ fr ≤ ffN0p hQ fr := by
  intro g hg
  obtain ⟨σ, -, b, hb, rfl⟩ := (mem_ffP0p_iff_hat hQ fr).mp hg
  exact (mem_ffN0p_iff hQ fr).mpr ⟨σ, b, hb, rfl⟩

theorem ffB0p_le_ffN0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ffB0p fr ≤ ffN0p hQ fr := by
  intro b hb
  exact (mem_ffN0p_iff hQ fr).mpr ⟨1, b, hb, by rw [ffHat_one, one_mul]⟩

theorem ffHat_mem_ffN0p (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    (σ : Equiv.Perm (Fin 5)) : ffHat fr σ ∈ ffN0p hQ fr := by
  refine (mem_ffN0p_iff hQ fr).mpr ⟨σ, 1, Subgroup.one_mem _, ?_⟩
  rw [mul_one]

@[expose] noncomputable def ffN0Rho (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    ↥(ffN0p hQ fr) →* Equiv.Perm (Fin 5) :=
  (ffMonoPRho fr).comp (Subgroup.inclusion (ffN0p_le_ffMonoP hQ fr))

theorem ffN0Rho_hat (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {σ : Equiv.Perm (Fin 5)} {b : OGroup Q} (hb : b ∈ ffB0p fr)
    (h : ffHat fr σ * b ∈ ffN0p hQ fr) : ffN0Rho hQ fr ⟨ffHat fr σ * b, h⟩ = σ := by
  obtain ⟨J, -, hbJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hb
  refine ffMonoPRho_eq_of_hat fr (g := ⟨ffHat fr σ * b, ffN0p_le_ffMonoP hQ fr h⟩)
    (K := ffOpt J) ?_
  show ffHat fr σ * b = ffHat fr σ * fr.signChange (ffOpt J)
  rw [hbJ]

theorem ffN0Rho_surjective (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Function.Surjective (ffN0Rho hQ fr) := by
  intro σ
  have h1 : ffHat fr σ * 1 ∈ ffN0p hQ fr := by
    rw [mul_one]; exact ffHat_mem_ffN0p hQ fr σ
  exact ⟨⟨ffHat fr σ * 1, h1⟩,
    ffN0Rho_hat hQ fr (σ := σ) (b := 1) (Subgroup.one_mem _) h1⟩

theorem ffN0Rho_ker (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    (ffN0Rho hQ fr).ker = (ffB0p fr).subgroupOf (ffN0p hQ fr) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨σ, b, hb, hx_eq⟩ := (mem_ffN0p_iff hQ fr).mp x.2
    have hb' : ffHat fr σ * b ∈ ffN0p hQ fr := hx_eq ▸ x.2
    have hσ : ffN0Rho hQ fr x = σ := by
      rw [show x = ⟨ffHat fr σ * b, hb'⟩ from Subtype.ext hx_eq]
      exact ffN0Rho_hat hQ fr hb hb'
    have hs1 : σ = 1 := by rw [← hσ]; exact hx
    rw [hx_eq, hs1, ffHat_one, one_mul]
    exact hb
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [MonoidHom.mem_ker]
    obtain ⟨σ, b, hb, hx_eq⟩ := (mem_ffN0p_iff hQ fr).mp x.2
    have hb' : ffHat fr σ * b ∈ ffN0p hQ fr := hx_eq ▸ x.2
    have hσ : ffN0Rho hQ fr x = σ := by
      rw [show x = ⟨ffHat fr σ * b, hb'⟩ from Subtype.ext hx_eq]
      exact ffN0Rho_hat hQ fr hb hb'
    have hff : ffHat fr σ ∈ ffB0p fr := by
      have h1 : ffHat fr σ * b ∈ ffB0p fr := by rw [← hx_eq]; exact hx
      have h2 : (ffHat fr σ * b) * b⁻¹ ∈ ffB0p fr :=
        Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hb)
      rwa [mul_inv_cancel_right] at h2
    rw [hσ, ffOutFF6PN1_hat_mem_B0_eq_one fr hff]

theorem ff6p_N0_quotEquivTo (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    QuotEquivTo (ffN0p hQ fr) (ffB0p fr) (Equiv.Perm (Fin 5)) :=
  ⟨ffN0Rho hQ fr, ffN0Rho_surjective hQ fr, ffN0Rho_ker hQ fr⟩

theorem ffN0p_card (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    Nat.card ↥(ffN0p hQ fr) = 1920 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((ffB0p fr).subgroupOf (ffN0p hQ fr))]
  have h1 : Nat.card (↥(ffN0p hQ fr) ⧸ (ffB0p fr).subgroupOf (ffN0p hQ fr)) =
      Nat.card (Equiv.Perm (Fin 5)) := by
    rw [← ffN0Rho_ker hQ fr]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (ffN0Rho hQ fr)
      (ffN0Rho_surjective hQ fr)).toEquiv
  have h2 : Nat.card ((ffB0p fr).subgroupOf (ffN0p hQ fr)) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (ffB0p_le_ffN0p hQ fr)).toEquiv,
      ffB0p_card]
  have h3 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
    rw [Nat.card_perm, Nat.card_fin]; decide
  rw [h1, h2, h3]

theorem ffN0p_conj_signChange (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} (hg : g ∈ ffN0p hQ fr) (J : Finset (Fin 5)) :
    g * fr.signChange (ffOpt J) * g⁻¹ =
      fr.signChange (ffOpt (ffAct (ffN0Rho hQ fr ⟨g, hg⟩) J)) := by
  obtain ⟨σ, b, hb, hg_eq⟩ := (mem_ffN0p_iff hQ fr).mp hg
  obtain ⟨K, -, hbK⟩ := (mem_ffB0p_iff_ffOpt fr).mp hb
  have hσ : ffN0Rho hQ fr ⟨g, hg⟩ = σ := by
    have hb' : ffHat fr σ * b ∈ ffN0p hQ fr := hg_eq ▸ hg
    rw [show (⟨g, hg⟩ : ↥(ffN0p hQ fr)) = ⟨ffHat fr σ * b, hb'⟩ from Subtype.ext hg_eq]
    exact ffN0Rho_hat hQ fr hb hb'
  rw [hσ, hg_eq]
  have hb2 : b * b = 1 := by rw [hbK, fr.signChange_mul_self]
  have hinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
  have hcomm : b * fr.signChange (ffOpt J) = fr.signChange (ffOpt J) * b := by
    rw [hbK, fr.signChange_comm]
  have hbconj : b * fr.signChange (ffOpt J) * b⁻¹ = fr.signChange (ffOpt J) := by
    rw [hinv, hcomm, mul_assoc, hb2, mul_one]
  calc (ffHat fr σ * b) * fr.signChange (ffOpt J) * (ffHat fr σ * b)⁻¹
      = ffHat fr σ * (b * fr.signChange (ffOpt J) * b⁻¹) * (ffHat fr σ)⁻¹ := by group
    _ = ffHat fr σ * fr.signChange (ffOpt J) * (ffHat fr σ)⁻¹ := by rw [hbconj]
    _ = fr.signChange (ffOpt (ffAct σ J)) := ffHat_conj_signChange_ffOpt fr σ J

theorem ff6p_centralizer_B0 (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC)
    {g : OGroup Q} (hg : g ∈ omegaGroup hQ) (hc : ∀ b ∈ ffB0p fr, g * b = b * g) :
    g ∈ ffB0p fr := by
  have hnorm : g ∈ Subgroup.normalizer (ffB0p fr : Set (OGroup Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hc h hh, mul_assoc, mul_inv_cancel, mul_one]
      exact hh
    · intro hh
      have hy : g * h * g⁻¹ ∈ ffB0p fr := hh
      have hconj : g⁻¹ * (g * h * g⁻¹) * g = g * h * g⁻¹ := by
        have h' : g * (g * h * g⁻¹) = (g * h * g⁻¹) * g := hc _ hy
        calc g⁻¹ * (g * h * g⁻¹) * g = g⁻¹ * ((g * h * g⁻¹) * g) := by group
          _ = g⁻¹ * (g * (g * h * g⁻¹)) := by rw [h']
          _ = g * h * g⁻¹ := by group
      have hmem : g⁻¹ * (g * h * g⁻¹) * g ∈ ffB0p fr := hconj.symm ▸ hy
      rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at hmem
  have hσ1 : ffN0Rho hQ fr ⟨g, ⟨hg, hnorm⟩⟩ = 1 := by
    apply ff_perm_eq_one_of_fix_even
    intro J hJe
    have hcomm : g * fr.signChange (ffOpt J) = fr.signChange (ffOpt J) * g :=
      hc _ ((mem_ffB0p_iff_ffOpt fr).mpr ⟨J, hJe, rfl⟩)
    have h1 : g * fr.signChange (ffOpt J) * g⁻¹ = fr.signChange (ffOpt J) := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    have h2 := ffN0p_conj_signChange hQ fr (g := g) ⟨hg, hnorm⟩ J
    rw [h1] at h2
    exact ((ffOpt_signChange_eq_iff fr).mp h2).symm
  obtain ⟨σ', b, hb, hg_eq⟩ := (mem_ffN0p_iff hQ fr).mp ⟨hg, hnorm⟩
  have hb' : ffHat fr σ' * b ∈ ffN0p hQ fr := hg_eq ▸ ⟨hg, hnorm⟩
  have hσ' : ffN0Rho hQ fr ⟨g, ⟨hg, hnorm⟩⟩ = σ' := by
    rw [show (⟨g, ⟨hg, hnorm⟩⟩ : ↥(ffN0p hQ fr)) = ⟨ffHat fr σ' * b, hb'⟩ from
      Subtype.ext hg_eq]
    exact ffN0Rho_hat hQ fr hb hb'
  have hσ'1 : σ' = 1 := by rw [← hσ', hσ1]
  rw [hg_eq, hσ'1, ffHat_one, one_mul]
  exact hb

@[expose] noncomputable def ffVecT (fr : PFrame Q (Option (Fin 5)) ffC) (v : Fin 5 → ZMod 2) :
    OGroup Q :=
  fr.signChange (ffOpt (Finset.univ.filter fun i => v i ≠ 0))

private theorem ffOutFF6PN1_ffVecT (fr : PFrame Q (Option (Fin 5)) ffC)
    (v : Fin 5 → ZMod 2) :
    ffVecT fr v = fr.signChange (ffOpt (ffOutFF6PN1_supp v)) := rfl

theorem ff6p_N0_permModule (hQ : Q.Nondegenerate) (fr : PFrame Q (Option (Fin 5)) ffC) :
    IsPermModuleVia IsEvenVec (ffVecT fr) (ffB0p fr) (ffN0p hQ fr) ⊤ := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v w _ _
    simp only [ffOutFF6PN1_ffVecT]
    rw [ffOutFF6PN1_supp_add, ffOpt_symmDiff, fr.signChange_mul]
  · intro v w _ _ h
    rw [ffOutFF6PN1_ffVecT] at h
    exact ffOutFF6PN1_eq_of_supp_eq (ffOpt_injective (fr.signChange_injective h))
  · intro x
    constructor
    · intro hx
      obtain ⟨J, hJe, hxJ⟩ := (mem_ffB0p_iff_ffOpt fr).mp hx
      refine ⟨fun i => if i ∈ J then (1 : ZMod 2) else 0, ?_, ?_⟩
      · rw [ffOutFF6PN1_isEvenVec_iff_even_supp, ffOutFF6PN1_supp_indicator]
        exact hJe
      · rw [ffOutFF6PN1_ffVecT, ffOutFF6PN1_supp_indicator]
        exact hxJ.symm
    · rintro ⟨v, hv, hx⟩
      rw [← hx]
      exact (mem_ffB0p_iff_ffOpt fr).mpr ⟨ffOutFF6PN1_supp v,
        (ffOutFF6PN1_isEvenVec_iff_even_supp v).mp hv, rfl⟩
  · intro h hh
    exact ⟨ffN0Rho hQ fr ⟨h, hh⟩, Subgroup.mem_top _, fun v _ => by
      simp only [ffOutFF6PN1_ffVecT, ffOutFF6PN1_supp_permVec]
      exact ffN0p_conj_signChange hQ fr hh (ffOutFF6PN1_supp v)⟩
  · intro σ _
    exact ⟨ffHat fr σ, ffHat_mem_ffN0p hQ fr σ, fun v _ => by
      simp only [ffOutFF6PN1_ffVecT, ffOutFF6PN1_supp_permVec]
      exact ffHat_conj_signChange_ffOpt fr σ (ffOutFF6PN1_supp v)⟩

end CFSG.OddStandard.SmallF3.Omega
