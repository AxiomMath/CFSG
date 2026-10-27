module

public import CFSG.HardMathSupport.Lang.D4Three.UnitLayers
public import CFSG.LieType.Chevalley.E7SupportedBruhatTorus

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie


variable {τ : Tag} {K : Type} [Field K] [Finite K]

@[expose] def BorelScalar (g : ModGL τ K) : Prop :=
  (∀ h : ℤ, g ∈ Subgroup.normalizer (heightSeries τ K h : Set (ModGL τ K))) ∧
  ∃ s : (Fin τ.rank → ℤ) → K, (∀ α, IsRoot τ α → 0 < height α → s α ≠ 0) ∧
    ∀ α (hα : IsRoot τ α ∧ 0 < height α) (x : ModGL τ K), x ∈ heightSeries τ K (height α) →
      rootCoord hα (g * x * g⁻¹) = s α * rootCoord hα x

theorem BorelScalar.one : BorelScalar (1 : ModGL τ K) := by
  refine ⟨fun h => one_mem _, fun _ => 1, fun _ _ _ => one_ne_zero, fun α hα x _ => ?_⟩
  simp

theorem BorelScalar.mul {g g' : ModGL τ K} (hg : BorelScalar g) (hg' : BorelScalar g') :
    BorelScalar (g * g') := by
  obtain ⟨hn, s, hs0, hs⟩ := hg
  obtain ⟨hn', s', hs0', hs'⟩ := hg'
  refine ⟨fun h => mul_mem (hn h) (hn' h), fun α => s α * s' α, fun α h1 h2 =>
    mul_ne_zero (hs0 α h1 h2) (hs0' α h1 h2), fun α hα x hx => ?_⟩
  have hy : g' * x * g'⁻¹ ∈ heightSeries τ K (height α) :=
    (Subgroup.mem_normalizer_iff.1 (hn' _) x).1 hx
  have : g * g' * x * (g * g')⁻¹ = g * (g' * x * g'⁻¹) * g⁻¹ := by group
  rw [this, hs α hα _ hy, hs' α hα x hx]
  ring

theorem BorelScalar.inv {g : ModGL τ K} (hg : BorelScalar g) : BorelScalar g⁻¹ := by
  obtain ⟨hn, s, hs0, hs⟩ := hg
  refine ⟨fun h => inv_mem (hn h), fun α => (s α)⁻¹, fun α h1 h2 =>
    inv_ne_zero (hs0 α h1 h2), fun α hα x hx => ?_⟩
  have hy : g⁻¹ * x * g ∈ heightSeries τ K (height α) := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hn (height α))) x).1 hx
    simpa using this
  have h1 := hs α hα _ hy
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [e] at h1
  have e2 : g⁻¹ * x * g⁻¹⁻¹ = g⁻¹ * x * g := by simp
  rw [e2, h1, ← mul_assoc, inv_mul_cancel₀ (hs0 α hα.1 hα.2), one_mul]

theorem borelScalar_of_mem_posUnipotent {u : ModGL τ K} (hu : u ∈ posUnipotent τ K) :
    BorelScalar u := by
  refine ⟨fun h => heightSeries_le_normalizer K h hu, fun _ => 1, fun _ _ _ => one_ne_zero,
    fun α hα x hx => ?_⟩
  rw [one_mul]
  exact rootCoord_conj hα hu hx

theorem borelScalar_of_mem_torusGroup {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    BorelScalar h := by
  have hF : ∀ γ, IsRoot τ γ → ∀ c : K,
      ∃ d : K, (MulAut.conj h).toMonoidHom (pinnedX τ K γ c) = pinnedX τ K (id γ) d :=
    fun γ hγ c => ⟨_, conj_pinnedX_of_mem_torusGroup hh hγ c⟩
  have hmem : ∀ (h' : ModGL τ K), h' ∈ torusGroup τ K → ∀ H : ℤ, ∀ {x : ModGL τ K},
      x ∈ heightSeries τ K H → h' * x * h'⁻¹ ∈ heightSeries τ K H := by
    intro h' hh' H x hx
    have hF' : ∀ γ, IsRoot τ γ → ∀ c : K,
        ∃ d : K, (MulAut.conj h').toMonoidHom (pinnedX τ K γ c) = pinnedX τ K (id γ) d :=
      fun γ hγ c => ⟨_, conj_pinnedX_of_mem_torusGroup hh' hγ c⟩
    exact map_heightSeries_le (MulAut.conj h').toMonoidHom id (fun γ hγ => hγ) (fun γ => rfl)
      hF' H hx
  refine ⟨fun H => ?_, fun α => torusRootChar h α, fun α hα _ =>
    torusRootChar_ne_zero (torusGroup_le_diagonalGroup hh) α, fun α hα x hx => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hmem h hh H hx
    · intro hx
      have := hmem h⁻¹ (inv_mem hh) H hx
      simpa [mul_assoc] using this
  · have key := rootCoord_map (MulAut.conj h).toMonoidHom id (fun γ hγ => hγ) (fun γ => rfl)
      (fun γ γ' _ _ hh' => hh') hF (AddMonoidHom.id K) hα hα (torusRootChar h α)
      (fun c => by
        change h * pinnedX τ K α c * h⁻¹ = _
        rw [conj_pinnedX_of_mem_torusGroup hh hα.1 c]
        rfl) hx
    simpa using key

theorem borelScalar_of_mem_borelGroup {g : ModGL τ K} (hg : g ∈ borelGroup τ K) :
    BorelScalar g := by
  rw [borelGroup, Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact borelScalar_of_mem_torusGroup hx
    · exact borelScalar_of_mem_posUnipotent hx
  | one => exact BorelScalar.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

def BorelScalar.s {g : ModGL τ K} (hg : BorelScalar g) : (Fin τ.rank → ℤ) → K :=
  Classical.choose (And.right hg)

theorem BorelScalar.spec {g : ModGL τ K} (hg : BorelScalar g) :
    (∀ α, IsRoot τ α → 0 < height α → hg.s α ≠ 0) ∧
    ∀ α (hα : IsRoot τ α ∧ 0 < height α) (x : ModGL τ K), x ∈ heightSeries τ K (height α) →
      rootCoord hα (g * x * g⁻¹) = hg.s α * rootCoord hα x :=
  Classical.choose_spec (And.right hg)

theorem rootCoord_congr' {x : ModGL τ K} {α α' : Fin τ.rank → ℤ} (h : α = α')
    (hα : IsRoot τ α ∧ 0 < height α) (hα' : IsRoot τ α' ∧ 0 < height α') :
    rootCoord hα x = rootCoord hα' x := by
  subst h
  rfl

@[expose] def layerAct_of_borel_monomial {β : MulAut ↥(adjointGroup τ K)} {g : ModGL τ K}
    (hg : BorelScalar g)
    (F : ModGL τ K →* ModGL τ K) (ρ : (Fin τ.rank → ℤ) → (Fin τ.rank → ℤ))
    (e : (Fin τ.rank → ℤ) → K) (σ : K ≃+* K)
    (hρR : ∀ γ, IsRoot τ γ → IsRoot τ (ρ γ)) (hρh : ∀ γ, height (ρ γ) = height γ)
    (hρinj : ∀ γ γ', IsRoot τ γ → IsRoot τ γ' → ρ γ = ρ γ' → γ = γ')
    (hF : ∀ γ, IsRoot τ γ → ∀ c : K, F (pinnedX τ K γ c) = pinnedX τ K (ρ γ) (e γ * σ c))
    (hβ : ∀ x : ↥(adjointGroup τ K),
      ((β x : ↥(adjointGroup τ K)) : ModGL τ K) = g * F (x : ModGL τ K) * g⁻¹)
    (r : ∀ k, UnitRoots τ k → UnitRoots τ k) (hr : ∀ k δ, ρ (r k δ).1 = δ.1) :
    LayerAct τ β σ :=
  have hF' : ∀ γ, IsRoot τ γ → ∀ c : K, ∃ d : K, F (pinnedX τ K γ c) = pinnedX τ K (ρ γ) d :=
    fun γ hγ c => ⟨_, hF γ hγ c⟩
  have hFU : ∀ (H : ℤ) {x : ModGL τ K}, x ∈ heightSeries τ K H → F x ∈ heightSeries τ K H :=
    fun H x hx => map_heightSeries_le F ρ hρR hρh hF' H hx
  { r := r
    f := fun k δ => hg.s δ.1 * e (r k δ).1
    stable := fun k x hx => by
      rw [mem_unitN] at hx ⊢
      rw [hβ]
      exact (Subgroup.mem_normalizer_iff.1 (hg.1 _) _).1 (hFU _ hx)
    coord := fun k δ x hx => by
      have hs := hg.spec.2
      have hxU : (x : ModGL τ K) ∈ heightSeries τ K (((k + 1 : ℕ) : ℤ)) := hx
      have hδh : height δ.1 = ((k + 1 : ℕ) : ℤ) := δ.2.2
      have hαh : height (r k δ).1 = ((k + 1 : ℕ) : ℤ) := (r k δ).2.2
      have hFx : F (x : ModGL τ K) ∈ heightSeries τ K (height δ.1) := by
        rw [hδh]; exact hFU _ hxU
      rw [hβ, hs δ.1 (UnitRoots.pos τ δ) _ hFx]
      have hαpos := UnitRoots.pos τ (r k δ)
      have hρα : IsRoot τ (ρ (r k δ).1) ∧ 0 < height (ρ (r k δ).1) :=
        ⟨hρR _ hαpos.1, by rw [hρh]; exact hαpos.2⟩
      have hxα : (x : ModGL τ K) ∈ heightSeries τ K (height (r k δ).1) := by
        rw [hαh]; exact hxU
      have key := rootCoord_map F ρ hρR hρh hρinj hF' σ.toAddMonoidHom hαpos hρα
        (e (r k δ).1) (fun c => hF _ hαpos.1 c) hxα
      rw [rootCoord_congr' (hr k δ).symm (UnitRoots.pos τ δ) hρα, key]
      change hg.s δ.1 * (e (r k δ).1 * σ _) = (hg.s δ.1 * e (r k δ).1) * σ _
      ring }

end CFSG.HardMathSupport.Lang.D4Three
