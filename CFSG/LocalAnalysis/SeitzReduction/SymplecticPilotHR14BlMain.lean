module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHR14BlShape
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotHsyl

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG mem_modelToG)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

section Class

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2]

theorem exists_conj_eq_spARep_of_injective {n : ℕ} (hn : 3 ≤ n) (e : L ≃* StatedSp n K)
    (ψ : StatedSp n K →* G) (hψ : Function.Injective ψ) (hψL : ∀ y, ψ y ∈ L) (j : ℕ) :
    ∃ c ∈ L, c * ψ (spARep n j) * c⁻¹ = ((e.symm (spARep n j) : L) : G) := by
  let φ : StatedSp n K →* StatedSp n K :=
    { toFun := fun y => e ⟨ψ y, hψL y⟩
      map_one' := by
        show e ⟨ψ 1, hψL 1⟩ = 1
        rw [show (⟨ψ 1, hψL 1⟩ : L) = 1 from Subtype.ext (map_one ψ), map_one]
      map_mul' := fun y y' => by
        show e ⟨ψ (y * y'), hψL _⟩ = e ⟨ψ y, hψL y⟩ * e ⟨ψ y', hψL y'⟩
        rw [← map_mul e]
        congr 1
        exact Subtype.ext (map_mul ψ y y') }
  have hφ : Function.Injective φ := by
    intro y y' h
    have h1 := congrArg Subtype.val (e.injective h)
    exact hψ h1
  have hb : Function.Bijective φ := Finite.injective_iff_bijective.1 hφ
  obtain ⟨s, σ, hs⟩ := exists_eq_conj_mul_fieldSp hn (MulEquiv.ofBijective φ hb)
  have hφa : φ (spARep n j) = s * spARep n j * s⁻¹ := by
    have h1 := congrArg (fun β : MulAut (StatedSp n K) => β (spARep n j)) hs
    simp only [MulEquiv.ofBijective_apply, MulAut.mul_apply, MulAut.conj_apply,
      fieldSp_spARep] at h1
    exact h1
  have hψa : ψ (spARep n j) = ((e.symm (φ (spARep n j)) : L) : G) := by
    change ψ (spARep n j) = ((e.symm (e ⟨ψ (spARep n j), hψL _⟩) : L) : G)
    rw [MulEquiv.symm_apply_apply]
  refine ⟨((e.symm s⁻¹ : L) : G), (e.symm s⁻¹).2, ?_⟩
  rw [hψa, hφa, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_inv,
    ← map_mul, ← map_mul]
  congr 2
  group

end Class

section Torus

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem false_of_conj_spARep_of_toral {n : ℕ} (e : L ≃* StatedSp n K) {t g : G}
    (htC : t ∈ centralizer (L : Set G)) {G₀ : Subgroup G} (θs : MulAut G₀)
    (hact : ∀ y : G₀, ((θs y : G₀) : G) = (g⁻¹ * t * g) * y * (g⁻¹ * t * g)⁻¹)
    {x₀ : G₀} (hFle : fixedSubgroup θs ≤ centralizer ({x₀} : Set G₀))
    (hFtor : ∀ T : Subgroup G₀, T ≤ fixedSubgroup θs → Odd (Nat.card T) →
      ∃ P : Subgroup G₀, P ≤ centralizer (T : Set G₀) ∧ ⁅P, P⁆ = P ∧
        ¬ P ≤ centralizer ({x₀} : Set G₀))
    (hΛ : L ⊓ centralizer ({g * x₀ * g⁻¹} : Set G) ≤
      (fixedSubgroup θs).map ((MulAut.conj g).toMonoidHom.comp G₀.subtype))
    {a : StatedSp n K} {A : Subgroup (StatedSp n K)}
    (hA : A ≤ centralizer ({a} : Set (StatedSp n K))) (hAodd : Odd (Nat.card A)) {l : G}
    (hlL : l ∈ L) (hxl : g * x₀ * g⁻¹ = l * ((e.symm a : L) : G) * l⁻¹)
    (hTor : centralizerPerfectCore (modelToG e A) ≤ centralizer ({t} : Set G)) : False := by
  set x : G := g * x₀ * g⁻¹ with hx
  set φ : G₀ →* G := (MulAut.conj g).toMonoidHom.comp G₀.subtype with hφ
  have hinj : Function.Injective φ := (MulAut.conj g).injective.comp G₀.subtype_injective
  set T₀ : Subgroup G := modelToG e A with hT₀
  set T : Subgroup G := T₀.map (MulAut.conj l).toMonoidHom with hT
  have hTΛ : T ≤ (fixedSubgroup θs).map φ := by
    refine le_trans ?_ hΛ
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨d, hd, rfl⟩ := (mem_modelToG e).1 hy
    have hdz := mem_centralizer_singleton_iff.1 (hA hd)
    have hmemL : l * ((e.symm d : L) : G) * l⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem hlL (e.symm d).2) (L.inv_mem hlL)
    refine ⟨hmemL, ?_⟩
    show l * ((e.symm d : L) : G) * l⁻¹ ∈ centralizer ({x} : Set G)
    rw [mem_centralizer_singleton_iff, hxl]
    have h2 : ((e.symm d : L) : G) * ((e.symm a : L) : G) =
        ((e.symm a : L) : G) * ((e.symm d : L) : G) := by
      rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hdz]
    calc l * ((e.symm d : L) : G) * l⁻¹ * (l * ((e.symm a : L) : G) * l⁻¹) =
        l * (((e.symm d : L) : G) * ((e.symm a : L) : G)) * l⁻¹ := by group
      _ = l * (((e.symm a : L) : G) * ((e.symm d : L) : G)) * l⁻¹ := by rw [h2]
      _ = l * ((e.symm a : L) : G) * l⁻¹ * (l * ((e.symm d : L) : G) * l⁻¹) := by group
  have hT₀odd : Odd (Nat.card T₀) := by
    rw [hT₀, UnitaryPilot.modelToG_def, Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective]
    exact hAodd
  have hTodd : Odd (Nat.card T) := by
    rw [hT, Subgroup.card_map_of_injective (MulAut.conj l).injective]
    exact hT₀odd
  set Tu : Subgroup G₀ := T.comap φ with hTu
  have hTuF : Tu ≤ fixedSubgroup θs := by
    intro y hy
    obtain ⟨y', hy', hyy'⟩ := hTΛ hy
    have : y' = y := hinj hyy'
    rw [← this]
    exact hy'
  have hTuodd : Odd (Nat.card Tu) := by
    have h1 : Nat.card (Tu.map φ) = Nat.card Tu := Subgroup.card_map_of_injective hinj
    have h2 : Tu.map φ ≤ T := Subgroup.map_comap_le _ _
    rw [← h1]
    exact Odd.of_dvd_nat hTodd (Subgroup.card_dvd_of_le h2)
  obtain ⟨P, hPc, hPperf, hPx⟩ := hFtor Tu hTuF hTuodd
  set P' : Subgroup G := P.map φ with hP'
  have hP'perf : ⁅P', P'⁆ = P' := by rw [hP', ← Subgroup.map_commutator, hPperf]
  have hP'T : P' ≤ centralizer (T : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro τ hτ
    obtain ⟨τ', -, hττ'⟩ := hTΛ hτ
    have hτ'u : τ' ∈ Tu := by
      show φ τ' ∈ T
      rw [hττ']
      exact hτ
    have h1 : τ' * y = y * τ' := mem_centralizer_iff.1 (hPc hy) τ' hτ'u
    rw [← hττ']
    rw [← map_mul, ← map_mul, h1]
  set P'' : Subgroup G := P'.map (MulAut.conj l⁻¹).toMonoidHom with hP''
  have hP''perf : ⁅P'', P''⁆ = P'' := by rw [hP'', ← Subgroup.map_commutator, hP'perf]
  have hP''T₀ : P'' ≤ centralizer (T₀ : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_centralizer_iff]
    intro τ hτ
    have hτT : l * τ * l⁻¹ ∈ T := ⟨τ, hτ, rfl⟩
    have h1 : (l * τ * l⁻¹) * y = y * (l * τ * l⁻¹) := mem_centralizer_iff.1 (hP'T hy) _ hτT
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    calc τ * (l⁻¹ * y * l) = l⁻¹ * ((l * τ * l⁻¹) * y) * l := by group
      _ = l⁻¹ * (y * (l * τ * l⁻¹)) * l := by rw [h1]
      _ = l⁻¹ * y * l * τ := by group
  have hP''t : P'' ≤ centralizer ({t} : Set G) :=
    (F4Pilot.le_centralizerPerfectCore hP''perf hP''T₀).trans hTor
  have hlt : l * t = t * l := mem_centralizer_iff.1 htC l hlL
  have hPF : P ≤ fixedSubgroup θs := by
    intro y hy
    have h1 : l⁻¹ * φ y * l ∈ P'' := by
      refine ⟨φ y, ⟨y, hy, rfl⟩, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    have h2 : (l⁻¹ * φ y * l) * t = t * (l⁻¹ * φ y * l) :=
      mem_centralizer_singleton_iff.1 (hP''t h1)
    have h3 : φ y * t = t * φ y := by
      calc φ y * t = l * ((l⁻¹ * φ y * l) * t) * l⁻¹ := by
            rw [show l * ((l⁻¹ * φ y * l) * t) * l⁻¹ = φ y * (l * t * l⁻¹) by group, hlt]
            group
        _ = l * (t * (l⁻¹ * φ y * l)) * l⁻¹ := by rw [h2]
        _ = t * φ y := by
            rw [show l * (t * (l⁻¹ * φ y * l)) * l⁻¹ = (l * t * l⁻¹) * φ y by group, hlt]
            group
    show θs y = y
    apply Subtype.ext
    rw [hact]
    have h4 : (g * (y : G) * g⁻¹) * t = t * (g * y * g⁻¹) := h3
    calc (g⁻¹ * t * g) * (y : G) * (g⁻¹ * t * g)⁻¹ =
        g⁻¹ * (t * (g * y * g⁻¹)) * t⁻¹ * g := by group
      _ = g⁻¹ * ((g * (y : G) * g⁻¹) * t) * t⁻¹ * g := by rw [h4]
      _ = y := by group
  exact hPx (hPF.trans hFle)

end Torus

end CFSG.SeitzReduction.SymplecticPilot
