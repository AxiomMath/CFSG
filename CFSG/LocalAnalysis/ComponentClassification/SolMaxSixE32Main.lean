module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Assem
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Final
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixE32Transport
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSixG

public section

namespace CFSG.ComponentClassification.SolMax.Sig36.E32

open CFSG Subgroup Equiv

variable {X : Type} [Group X] [Finite X] {M : Subgroup X}
  {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9)}
  {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)} {t s : X} {H Q : Subgroup X}

theorem core_six {g : X} {J : Subgroup X} (Z : Ctx M θ ρ t s H Q)
    (hJ : SolAltLit.IsAltTwoComponent t J 9)
    (hNoA9 : ∀ (x : X) (hx : x ∈ M), x * x = 1 → (ρ ⟨x, le_normalizer hx⟩).support.card = 4 →
      ∀ K : Subgroup X, K ≤ centralizer ({x} : Set X) →
        IsPComponent 2 (K.subgroupOf (centralizer ({x} : Set X))) →
        IsEmpty (↥K ⧸ pPrimeCore 2 ↥K ≃* alternatingGroup (Fin 9)))
    (hgs : g⁻¹ * t * g = s) (h6t : (rhoX ρ (g * t * g⁻¹)).support.card = 6) : False := by
  classical
  obtain ⟨w₀, w₁, x, F⟩ := Z.exists_frame
  have hts : s * t = t * s := Z.hst
  have hts' : t = g * s * g⁻¹ := by rw [← hgs]; group
  have ht₁C : g * t * g⁻¹ ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g * t * g⁻¹ * t = g * t * g⁻¹ * (g * s * g⁻¹) := by rw [← hts']
      _ = g * (t * s) * g⁻¹ := by group
      _ = g * (s * t) * g⁻¹ := by rw [hts]
      _ = (g * s * g⁻¹) * (g * t * g⁻¹) := by group
      _ = t * (g * t * g⁻¹) := by rw [← hts']
  have ht₁2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [Z.ht2]; group
  obtain ⟨c₁, hc₁C, hc₁⟩ := Z.fusion ht₁C ht₁2 h6t
  have hc₁t : c₁ * t = t * c₁ := mem_centralizer_singleton_iff.mp hc₁C
  have hstC : s * t ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc s * t * t = t * s * t := by rw [hts]
      _ = t * (s * t) := by group
  have hst2 : s * t * (s * t) = 1 := by
    calc s * t * (s * t) = s * (t * s) * t := by group
      _ = s * (s * t) * t := by rw [← hts]
      _ = (s * s) * (t * t) := by group
      _ = 1 := by rw [Z.hs2, Z.ht2, one_mul]
  have hst6 : (rhoX ρ (s * t)).support.card = 6 := by
    rw [rhoX_mul Z.s_mem_N Z.t_mem_N, Z.hρs, Z.rho_t, mul_one]
    exact card_support_σ₀
  obtain ⟨r, hrC, hr⟩ := Z.fusion hstC hst2 hst6
  have hrt : r * t * r⁻¹ = t := by
    have := mem_centralizer_singleton_iff.mp hrC
    rw [this]; group
  have hmt : g⁻¹ * c₁ * t * (g⁻¹ * c₁)⁻¹ = s := by
    calc g⁻¹ * c₁ * t * (g⁻¹ * c₁)⁻¹ = g⁻¹ * (c₁ * t * c₁⁻¹) * g := by group
      _ = g⁻¹ * t * g := by rw [hc₁t]; group
      _ = s := hgs
  have hms : g⁻¹ * c₁ * s * (g⁻¹ * c₁)⁻¹ = t := by
    calc g⁻¹ * c₁ * s * (g⁻¹ * c₁)⁻¹ = g⁻¹ * (c₁ * s * c₁⁻¹) * g := by group
      _ = g⁻¹ * (g * t * g⁻¹) * g := by rw [hc₁]
      _ = t := by group
  obtain ⟨ω, hωt, hωs, hω0, hω1, v, hv2, hv3, hv4, hωx⟩ := F.exists_omega hmt hms hrt hr
  obtain ⟨c, hcC, hct, hca⟩ := F.exists_symm (finRotate 4)
  have e0 : (finRotate 4) 0 = 1 := by decide
  have e1 : (finRotate 4) 1 = 2 := by decide
  have e2 : (finRotate 4) 2 = 3 := by decide
  have e3 : (finRotate 4) 3 = 0 := by decide
  have h0 := hca 0
  have h1 := hca 1
  have h2 := hca 2
  have h3 := hca 3
  rw [e0] at h0
  rw [e1] at h1
  rw [e2] at h2
  rw [e3] at h3
  have hts_conj : IsConj t s := isConj_iff.mpr ⟨g⁻¹, by rw [inv_inv]; exact hgs⟩
  obtain ⟨hbC, hb2, hb6, hbC', hb2', hb6'⟩ := F.sixpoint_C
  have hS₂ : IsConj t (s * w₀ * w₁ * x) := by
    obtain ⟨c₂, -, hc₂⟩ := Z.fusion hbC hb2 hb6
    exact hts_conj.trans (isConj_iff.mpr ⟨c₂, hc₂⟩)
  have hS₁ : IsConj t (s * w₀ * w₁ * x * t) := by
    obtain ⟨c₂, -, hc₂⟩ := Z.fusion hbC' hb2' hb6'
    exact hts_conj.trans (isConj_iff.mpr ⟨c₂, hc₂⟩)
  obtain ⟨hzM, hz2, hz4⟩ := F.fourpoint_M
  have hz4' : (ρ ⟨w₀ * w₁ * x, le_normalizer hzM⟩).support.card = 4 := by
    rw [← rhoX_of_mem (le_normalizer hzM)]; exact hz4
  have hP2 : ¬ IsConj t (w₀ * w₁ * x) := fun h => by
    obtain ⟨y, hy⟩ := isConj_iff.mp h
    exact not_isConj_of_isEmpty hJ (hNoA9 _ hzM hz2 hz4') y hy
  have hP1 : ∀ y : X, y * t * y⁻¹ = t → y * (s * w₁) * y⁻¹ ≠ s * w₀ * w₁ * x := fun y hy =>
    F.P1 (mem_centralizer_singleton_iff.mpr (by
      calc y * t = y * t * y⁻¹ * y := by group
        _ = t * y := by rw [hy]))
  refine final_false F.E5 ω c ⟨hωt, hωs, hω0, hω1⟩ hv2 hv3 hv4 hωx ⟨hct, ?_, ?_, ?_, ?_⟩ hS₁ hS₂
    hP2 hP1
  · simpa [aF] using h0
  · simpa [aF] using h1
  · simpa [aF] using h2
  · simpa [aF] using h3

theorem exists_normalize (hρ : IsPermAction θ ρ) (π : Perm (Fin 9)) :
    ∃ (θ₀ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin 9))
      (ρ₀ : ↥(normalizer (M : Set X)) →* Perm (Fin 9)), IsPermAction θ₀ ρ₀ ∧
        ∀ (x : X) (hx : x ∈ normalizer (M : Set X)), ρ₀ ⟨x, hx⟩ = π * ρ ⟨x, hx⟩ * π⁻¹ := by
  refine ⟨θ.trans (MulAut.conjNormal π), (MulAut.conj π).toMonoidHom.comp ρ, ?_,
    fun x hx => rfl⟩
  intro g m
  have h := hρ g m
  simp only [MulEquiv.trans_apply, MulAut.conjNormal_apply, MonoidHom.comp_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [h]
  group

end CFSG.ComponentClassification.SolMax.Sig36.E32

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem signalizerNineSixDihedralInput_holds : SignalizerNineSixDihedralInput := by
  intro X _ _ _ t J e E D S₀ hW M hMH hMpc hJM hHN hsup θ ρ hρ hNoA9 Q Sc hQK hQ2 hQcard htQ hQS
    hSH hS2 hScard htZ hCQ hd3 s hsS hsQ g hgs hgH hs2 hd4 hsN hρs2 h6 hy hR6 h6t
  classical
  set H := normalizer (Sol78.signalizerCompletion E E : Set X) with hHdef
  have hct : (ρ ⟨s, hsN⟩).cycleType = Sig36.E32.σ₀.cycleType := by
    rw [SixGen.cycleType_of_mul_self (k := 3) hρs2 (by norm_num) h6,
      SixGen.cycleType_of_mul_self (k := 3) Sig36.E32.σ₀_mul_self (by norm_num)
        Sig36.E32.card_support_σ₀]
  obtain ⟨π, hπ⟩ := isConj_iff.mp (Perm.isConj_iff_cycleType_eq.mpr hct)
  obtain ⟨θ₀, ρ₀, hρ₀, hρ₀def⟩ := Sig36.E32.exists_normalize hρ π
  have hsupp : ∀ (x : X) (hx : x ∈ normalizer (M : Set X)),
      (ρ₀ ⟨x, hx⟩).support.card = (ρ ⟨x, hx⟩).support.card := fun x hx => by
    rw [hρ₀def, Perm.card_support_conj]
  have hto : orderOf t = 2 := S₀.pair.1.1
  have ht2 : t * t = 1 := by rw [← sq, ← hto, pow_orderOf_eq_one]
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    exact absurd hto (by norm_num)
  have hsH : s ∈ H := hSH hsS
  have hsNQ : s ∈ normalizer (Q : Set X) :=
    le_normalizer_of_sylow_kernel hHN hQK hQcard hQS hSH hS2 hsS
  have Z : Sig36.E32.Ctx M θ₀ ρ₀ t s H Q :=
    { hρ := hρ₀
      hHN := hHN
      hCt := hCQ t htQ hto
      ht2 := ht2
      ht1 := ht1
      hsH := hsH
      hs2 := hs2
      hst := htZ s hsS
      hρs := by
        rw [Sig36.E32.rhoX_of_mem hsN, hρ₀def, hπ]
      hQK := hQK
      hQ2 := hQ2
      hQcard := hQcard
      htQ := htQ
      hQt := fun q hq => htZ q (hQS hq)
      hsQ := hsQ
      hsNQ := hsNQ
      hR := hR6
      hy := by
        obtain ⟨y, hyQ, hy2, hyt⟩ := hy
        refine ⟨y, hyQ, ?_, ?_, hyt⟩
        · rw [← sq, ← hy2, pow_orderOf_eq_one]
        · intro h1
          rw [h1, orderOf_one] at hy2
          exact absurd hy2 (by norm_num) }
  refine Sig36.E32.core_six (g := g) Z S₀.pair.1 ?_ hgs ?_
  · intro x hx hx2 hx4 K hKx hKc
    exact hNoA9 x hx hx2 (by rw [← hsupp]; exact hx4) K hKx hKc
  · have ht₁N : g * t * g⁻¹ ∈ normalizer (M : Set X) := by
      have : g * t * g⁻¹ ∈ centralizer ({t} : Set X) := by
        have hts' : t = g * s * g⁻¹ := by rw [← hgs]; group
        rw [mem_centralizer_singleton_iff]
        calc g * t * g⁻¹ * t = g * t * g⁻¹ * (g * s * g⁻¹) := by rw [← hts']
          _ = g * (t * s) * g⁻¹ := by group
          _ = g * (s * t) * g⁻¹ := by rw [← htZ s hsS]
          _ = (g * s * g⁻¹) * (g * t * g⁻¹) := by group
          _ = t * (g * t * g⁻¹) := by rw [← hts']
      exact Z.mem_normalizer_of_mem_C this
    rw [Sig36.E32.rhoX_of_mem ht₁N, hsupp]
    exact h6t ht₁N

theorem signalizerNineSixDihedralLocalInput_holds : SignalizerNineSixDihedralLocalInput :=
  signalizerNineSixDihedralLocalInput_of_dihedral signalizerNineSixDihedralInput_holds

end CFSG.ComponentClassification.SolMax
