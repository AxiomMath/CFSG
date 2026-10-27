module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentInitial.OddOrthogonalFourGroupCommutant
public import CFSG.LocalAnalysis.ComponentInitial.CentralQuotientComponentLift
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal

open Module CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial.CentralQuotientLift
  CFSG.ComponentClassification.CatalogueBOrthogonalScalarSquare
open TauCeti.QuadraticMap (orthogonalGroup)
open scoped commutatorElement

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polarBilin_map_of_mem {g : V ≃ₗ[K] V} (hg : g ∈ orthogonalGroup Q) (x y : V) :
    Q.polarBilin (g x) (g y) = Q.polarBilin x y := by
  have hg' := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polar, QuadraticMap.polar, ← map_add, hg', hg', hg']

theorem centralizer_eq_orthogonalOperatorCentralizer (T : orthogonalGroup Q) :
    Subgroup.centralizer {T} =
      orthogonalOperatorCentralizer Q (T : V ≃ₗ[K] V).toLinearMap := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h x
    exact LinearEquiv.congr_fun (congrArg Subtype.val h) x
  · intro h
    exact Subtype.ext (LinearEquiv.ext fun x => h x)

section Fixed

variable (hQ : Q.polarBilin.Nondegenerate) {P N : Submodule K V} (hc : IsCompl P N)
  (horth : ∀ x ∈ P, ∀ y ∈ N, Q.polarBilin x y = 0)

include hQ hc horth in
theorem mem_of_forall_polarBilin_eq_zero {v : V} (hv : ∀ n ∈ N, Q.polarBilin v n = 0) : v ∈ P := by
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
    v ∈ P ⊔ N)
  have hy0 : y = 0 := by
    refine hQ.1 y fun z => ?_
    obtain ⟨p, hp, n, hn, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
      z ∈ P ⊔ N)
    have h1 : Q.polarBilin y n = 0 := by
      have h2 := hv n hn
      rw [map_add, LinearMap.add_apply, horth x hx n hn, zero_add] at h2
      exact h2
    have h3 : Q.polarBilin y p = 0 := by
      rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm,
        ← QuadraticMap.polarBilin_apply_apply]
      exact horth p hp y hy
    rw [map_add, h3, h1, add_zero]
  rw [hy0, add_zero]
  exact hx

include hQ hc horth in
theorem fixed_eq_and_fix_of_perfect {G : Subgroup (orthogonalGroup Q)}
    (hGN : ∀ g ∈ G, ∀ w ∈ N, (g : V ≃ₗ[K] V) w = w)
    (hfix0 : ∀ a ∈ P, (∀ g ∈ G, (g : V ≃ₗ[K] V) a = a) → a = 0)
    (hfun0 : ∀ φ : P →ₗ[K] K,
      (∀ g ∈ G, ∀ a c : P, (c : V) = (g : V ≃ₗ[K] V) a → φ c = φ a) → φ = 0)
    (hcent : ∀ r : P ≃ₗ[K] P,
      (∀ g ∈ G, ∀ a c : P, (c : V) = (g : V ≃ₗ[K] V) a → (r c : V) = (g : V ≃ₗ[K] V) (r a)) →
        ∃ s : K, ∀ a : P, (r a : V) = s • (a : V)) :
    {v : V | ∀ g ∈ G, (g : V ≃ₗ[K] V) v = v} = N ∧
      ∀ R : Subgroup (orthogonalGroup Q), R ≤ Subgroup.centralizer (G : Set (orthogonalGroup Q)) →
        ⁅R, R⁆ = R → ∀ r ∈ R, ∀ a ∈ P, (r : V ≃ₗ[K] V) a = a := by
  have hfixN : {v : V | ∀ g ∈ G, (g : V ≃ₗ[K] V) v = v} = N := by
    ext v
    constructor
    · intro hv
      obtain ⟨a, ha, w, hw, rfl⟩ := Submodule.mem_sup.mp (hc.sup_eq_top ▸ Submodule.mem_top :
        v ∈ P ⊔ N)
      have ha0 : a = 0 := hfix0 a ha fun g hg => by
        have h1 := hv g hg
        rw [map_add, hGN g hg w hw] at h1
        exact add_right_cancel h1
      rw [ha0, zero_add]
      exact hw
    · intro hv g hg
      exact hGN g hg v hv
  refine ⟨hfixN, fun R hR hRp => ?_⟩
  have hcomm : ∀ r ∈ R, ∀ g ∈ G, ∀ v : V,
      (g : V ≃ₗ[K] V) ((r : V ≃ₗ[K] V) v) = (r : V ≃ₗ[K] V) ((g : V ≃ₗ[K] V) v) := by
    intro r hr g hg v
    exact LinearEquiv.congr_fun (congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hR hr) g hg)) v
  have hRP : ∀ r ∈ R, ∀ a ∈ P, (r : V ≃ₗ[K] V) a ∈ P := by
    intro r hr a ha
    refine mem_of_forall_polarBilin_eq_zero hQ hc horth fun n hn => ?_
    let φ : P →ₗ[K] K :=
      (Q.polarBilin.flip n).comp ((r : V ≃ₗ[K] V).toLinearMap.comp P.subtype)
    have hφ : φ = 0 := hfun0 φ fun g hg a' c' hc' => by
      change Q.polarBilin ((r : V ≃ₗ[K] V) c') n = Q.polarBilin ((r : V ≃ₗ[K] V) a') n
      rw [hc', ← hcomm r hr g hg, ← hGN g hg n hn, polarBilin_map_of_mem (g : orthogonalGroup Q).2,
        hGN g hg n hn]
    exact LinearMap.congr_fun hφ ⟨a, ha⟩
  have hRs : ∀ r ∈ R, ∃ s : K, ∀ a ∈ P, (r : V ≃ₗ[K] V) a = s • a := by
    intro r hr
    have hmap : P.map (r : V ≃ₗ[K] V).toLinearMap = P := by
      refine le_antisymm ?_ fun a ha => ?_
      · rintro _ ⟨a, ha, rfl⟩
        exact hRP r hr a ha
      · refine ⟨((r⁻¹ : orthogonalGroup Q) : V ≃ₗ[K] V) a, hRP _ (inv_mem hr) a ha, ?_⟩
        change (r : V ≃ₗ[K] V) ((r : V ≃ₗ[K] V).symm a) = a
        exact LinearEquiv.apply_symm_apply _ a
    obtain ⟨s, hs⟩ := hcent (LinearEquiv.ofSubmodules (r : V ≃ₗ[K] V) P P hmap)
      fun g hg a' c' hc' => by
        change (r : V ≃ₗ[K] V) c' = (g : V ≃ₗ[K] V) ((r : V ≃ₗ[K] V) a')
        rw [hc', hcomm r hr g hg]
    exact ⟨s, fun a ha => hs ⟨a, ha⟩⟩
  let H : Subgroup (orthogonalGroup Q) :=
    { carrier := {x | ∀ a ∈ P, (x : V ≃ₗ[K] V) a = a}
      one_mem' := fun _ _ => rfl
      mul_mem' := fun {x y} hx hy a ha => by
        change (x : V ≃ₗ[K] V) ((y : V ≃ₗ[K] V) a) = a
        rw [hy a ha, hx a ha]
      inv_mem' := fun {x} hx a ha => by
        change (x : V ≃ₗ[K] V).symm a = a
        rw [LinearEquiv.symm_apply_eq, hx a ha] }
  have hRH : ⁅R, R⁆ ≤ H := by
    rw [Subgroup.commutator_le]
    intro r₁ h₁ r₂ h₂ a ha
    obtain ⟨s₁, hs₁⟩ := hRs r₁ h₁
    obtain ⟨s₂, hs₂⟩ := hRs r₂ h₂
    have hab : ∀ c ∈ P, ((r₁ * r₂ : orthogonalGroup Q) : V ≃ₗ[K] V) c =
        ((r₂ * r₁ : orthogonalGroup Q) : V ≃ₗ[K] V) c := fun c hc' => by
      change (r₁ : V ≃ₗ[K] V) ((r₂ : V ≃ₗ[K] V) c) = (r₂ : V ≃ₗ[K] V) ((r₁ : V ≃ₗ[K] V) c)
      rw [hs₂ c hc', hs₁ c hc', map_smul, map_smul, hs₁ c hc', hs₂ c hc', smul_smul, smul_smul,
        mul_comm]
    have he : ⁅r₁, r₂⁆ = (r₁ * r₂) * (r₂ * r₁)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [he]
    change ((r₁ * r₂ : orthogonalGroup Q) : V ≃ₗ[K] V)
      ((((r₂ * r₁)⁻¹ : orthogonalGroup Q) : V ≃ₗ[K] V) a) = a
    have hmem : (((r₂ * r₁)⁻¹ : orthogonalGroup Q) : V ≃ₗ[K] V) a ∈ P :=
      hRP _ (inv_mem (mul_mem h₂ h₁)) a ha
    rw [hab _ hmem]
    change ((r₂ * r₁ : orthogonalGroup Q) : V ≃ₗ[K] V)
      (((r₂ * r₁ : orthogonalGroup Q) : V ≃ₗ[K] V).symm a) = a
    exact LinearEquiv.apply_symm_apply _ a
  intro r hr a ha
  rw [← hRp] at hr
  exact hRH hr a ha

end Fixed

theorem split_case {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    [FiniteDimensional K V] (hn : 2 ≤ finrank K V) (hQ : Q.polarBilin.Nondegenerate)
    {T : orthogonalGroup Q} (hTns : ∀ c : K, (T : V ≃ₗ[K] V).toLinearMap ≠ c • 1)
    (hTT : ∀ x, (T : V ≃ₗ[K] V) ((T : V ≃ₗ[K] V) x) = x) (b : Kˣ) (hb : (b : K) ^ 2 = 1)
    {P N : Submodule K V} (hPdef : P = positiveSquareKernel (T : V ≃ₗ[K] V) b)
    (hNdef : N = negativeSquareKernel (T : V ≃ₗ[K] V) b)
    {L : Subgroup (Subgroup.centralizer {T})} (hL : CFSG.IsComponent L)
    (hfix : ∀ x ∈ L, ∀ w ∈ N, ((x : orthogonalGroup Q) : V ≃ₗ[K] V) w = w)
    (hE : ∃ E : Subgroup (Subgroup.centralizer {T}), E ≤ L ∧ CFSG.Assembly.IsElemAbelian 2 E ∧
      Nat.card E = 4) :
    P ≠ ⊥ ∧ N ≠ ⊥ ∧ IsCompl P N ∧ (∀ x ∈ P, ∀ y ∈ N, Q.polarBilin x y = 0) ∧
      (LinearMap.BilinForm.restrict Q.polarBilin P).Nondegenerate ∧
      (LinearMap.BilinForm.restrict Q.polarBilin N).Nondegenerate ∧
      (∃ C : Subgroup (orthogonalGroup (Q.comp P.subtype)), CFSG.IsComponent C ∧
        ∀ c, c ∈ C ↔ ∃ x ∈ L, ∀ a : P,
          (((c : P ≃ₗ[K] P) a : P) : V) = ((x : orthogonalGroup Q) : V ≃ₗ[K] V) a) ∧
      3 ≤ finrank K P ∧
      {v : V | ∀ x ∈ L, ((x : orthogonalGroup Q) : V ≃ₗ[K] V) v = v} = N ∧
      ∀ R : Subgroup (orthogonalGroup Q),
        R ≤ Subgroup.centralizer ((L.map (Subgroup.centralizer {T}).subtype :
          Subgroup (orthogonalGroup Q)) : Set (orthogonalGroup Q)) →
        ⁅R, R⁆ = R → ∀ r ∈ R, ∀ a ∈ P, (r : V ≃ₗ[K] V) a = a := by
  subst hPdef hNdef
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (pow_pos hℓ.pos f).ne')
  have hchar : CharP K ℓ := finite_field_prime_power_characteristic hℓ hf hK
  have hk : ringChar K ≠ 2 := by
    rw [ringChar.eq K ℓ]
    exact hℓ2
  obtain ⟨-, -, hsq, -⟩ :=
    CatalogueBOrthogonalScalarSquareStructure.scalar_square_centralizer_structure ℓ f hℓ hℓ2 hf
      hK hn Q hQ (T : V ≃ₗ[K] V) 1 1 (fun x => by rw [Units.val_one, one_smul]; exact hTT x)
      (fun x y => by rw [Units.val_one, one_mul]; exact polarBilin_map_of_mem T.2 x y) hTns
  obtain ⟨hc, hP, hN, hpos, -⟩ := hsq b (by rw [Units.val_one, hb])
  obtain ⟨horth, hndP, hndN, e, he1, he2, -⟩ := hpos (by rw [Units.val_one, div_one])
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup.centralizer {T} ≃*
      (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype) ×
        orthogonalGroup (Q.comp (negativeSquareKernel (T : V ≃ₗ[K] V) b).subtype)),
      E' = (MulEquiv.subgroupCongr (centralizer_eq_orthogonalOperatorCentralizer T)).trans e :=
    ⟨_, rfl⟩
  have heP : ∀ (x : Subgroup.centralizer {T}) (a : positiveSquareKernel (T : V ≃ₗ[K] V) b),
      ((((E' x).1 : positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
        positiveSquareKernel (T : V ≃ₗ[K] V) b) a : positiveSquareKernel (T : V ≃ₗ[K] V) b) :
          V) = ((x : orthogonalGroup Q) : V ≃ₗ[K] V) a := fun x a => by
    rw [hE']
    exact he1 _ a
  have heN : ∀ (x : Subgroup.centralizer {T}) (w : negativeSquareKernel (T : V ≃ₗ[K] V) b),
      ((((E' x).2 : negativeSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
        negativeSquareKernel (T : V ≃ₗ[K] V) b) w : negativeSquareKernel (T : V ≃ₗ[K] V) b) :
          V) = ((x : orthogonalGroup Q) : V ≃ₗ[K] V) w := fun x w => by
    rw [hE']
    exact he2 _ w
  have hsnd : ∀ x : Subgroup.centralizer {T}, (∀ w ∈ negativeSquareKernel (T : V ≃ₗ[K] V) b,
      ((x : orthogonalGroup Q) : V ≃ₗ[K] V) w = w) → (E' x).2 = 1 := fun x hx =>
    Subtype.ext (LinearEquiv.ext fun w => Subtype.ext (by
      rw [heN]
      exact hx w w.2))
  set ρ := (MonoidHom.fst _ _).comp E'.toMonoidHom with hρ
  have hρs : Function.Surjective ρ := fun y => ⟨E'.symm (y, 1), by simp [hρ]⟩
  have hρinj : ∀ x ∈ L, ∀ y ∈ L, ρ x = ρ y → x = y := fun x hx y hy hxy =>
    E'.injective (Prod.ext hxy (by rw [hsnd x (hfix x hx), hsnd y (hfix y hy)]))
  have hC : CFSG.IsComponent (L.map ρ) := by
    refine ⟨?_, hL.2.map hρs⟩
    have hbij : Function.Bijective (ρ.subgroupMap L) := by
      refine ⟨fun x y hxy => Subtype.ext (hρinj x x.2 y y.2 (congrArg Subtype.val hxy)), ?_⟩
      exact ρ.subgroupMap_surjective L
    exact (isQuasisimple_congr (MulEquiv.ofBijective (ρ.subgroupMap L) hbij)).1 hL.1
  have hρapp : ∀ (x : Subgroup.centralizer {T}) (a : positiveSquareKernel (T : V ≃ₗ[K] V) b),
      (((ρ x : orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)) :
        positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K] positiveSquareKernel (T : V ≃ₗ[K] V) b) a :
          V) = ((x : orthogonalGroup Q) : V ≃ₗ[K] V) a := heP
  have hC' : CFSG.Assembly.IsComponentOf ((L.map ρ).map
      (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype)
      (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)) := by
    refine (isComponentOf_iff_isComponent_subgroupOf (Subgroup.map_subtype_le _)).mpr ?_
    rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    exact hC
  obtain ⟨E, hEL, hEab, hEcard⟩ := hE
  have hφinj : Set.InjOn ((orthogonalGroup
      (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype.comp ρ)
      (E : Set (Subgroup.centralizer {T})) :=
    fun x hx y hy hxy => hρinj x (hEL hx) y (hEL hy) (Subtype.ext hxy)
  have hE₂ : ∃ E₂ : Subgroup (positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
      positiveSquareKernel (T : V ≃ₗ[K] V) b), E₂ ≤ (L.map ρ).map
        (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype ∧
      CFSG.Assembly.IsElemAbelian 2 E₂ ∧ Nat.card E₂ = 4 := by
    refine ⟨E.map ((orthogonalGroup
      (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype.comp ρ), ?_, ⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨ρ x, ⟨x, hEL hx, rfl⟩, rfl⟩
    · have : IsMulCommutative E := hEab.1
      exact Subgroup.map_isMulCommutative E _
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEab.2 x hx, map_one]
    · rw [← hEcard]
      change Nat.card ((orthogonalGroup
        (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype.comp ρ ''
          (E : Set (Subgroup.centralizer {T}))) = Nat.card (E : Set (Subgroup.centralizer {T}))
      exact Nat.card_image_of_injOn hφinj
  have hQP : (QuadraticMap.polarBilin
      (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).Nondegenerate := by
    rw [QuadraticMap.polarBilin_comp]
    exact hndP
  obtain ⟨h3, hcentC, hfixC, hfunC⟩ :=
    odd_orthogonal_component_with_four_group_natural_commutant hk _ hQP hC' hE₂
  have hmemC : ∀ g' ∈ (L.map ρ).map
      (orthogonalGroup (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype,
      ∃ x ∈ L, ∀ a : positiveSquareKernel (T : V ≃ₗ[K] V) b,
        ((g' a : positiveSquareKernel (T : V ≃ₗ[K] V) b) : V) =
          ((x : orthogonalGroup Q) : V ≃ₗ[K] V) a := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, hρapp x⟩
  obtain ⟨hfixN, hRfix⟩ := fixed_eq_and_fix_of_perfect hQ hc horth
    (G := L.map (Subgroup.centralizer {T}).subtype)
    (by
      rintro _ ⟨x, hx, rfl⟩ w hw
      exact hfix x hx w hw)
    (by
      intro a ha hag
      have hmem : (⟨a, ha⟩ : positiveSquareKernel (T : V ≃ₗ[K] V) b) ∈
          {v | ∀ g ∈ (L.map ρ).map (orthogonalGroup
            (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype, g v = v} := by
        intro g' hg'
        obtain ⟨x, hx, hxg⟩ := hmemC g' hg'
        exact Subtype.ext ((hxg _).trans (hag _ ⟨x, hx, rfl⟩))
      rw [hfixC] at hmem
      exact congrArg Subtype.val hmem)
    (by
      intro φ hφ
      refine hfunC φ fun g' hg' v => ?_
      obtain ⟨x, hx, hxg⟩ := hmemC g' hg'
      exact hφ _ ⟨x, hx, rfl⟩ v (g' v) (hxg v))
    (by
      intro r hr
      have hrc : r ∈ Subgroup.centralizer (((L.map ρ).map (orthogonalGroup
          (Q.comp (positiveSquareKernel (T : V ≃ₗ[K] V) b).subtype)).subtype : Subgroup _) :
            Set (positiveSquareKernel (T : V ≃ₗ[K] V) b ≃ₗ[K]
              positiveSquareKernel (T : V ≃ₗ[K] V) b)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g' hg'
        obtain ⟨x, hx, hxg⟩ := hmemC g' hg'
        refine LinearEquiv.ext fun v => Subtype.ext ?_
        change ((g' (r v) : positiveSquareKernel (T : V ≃ₗ[K] V) b) : V) =
          ((r (g' v) : positiveSquareKernel (T : V ≃ₗ[K] V) b) : V)
        rw [hxg, hr _ ⟨x, hx, rfl⟩ v (g' v) (hxg v)]
        rfl
      have hrs := (Set.ext_iff.mp hcentC r).mp hrc
      obtain ⟨s, hs⟩ := hrs
      exact ⟨s, fun a => congrArg Subtype.val (hs a)⟩)
  have hfixL : {v : V | ∀ x ∈ L, ((x : orthogonalGroup Q) : V ≃ₗ[K] V) v = v} =
      negativeSquareKernel (T : V ≃ₗ[K] V) b := by
    rw [← hfixN]
    ext v
    constructor
    · rintro hv _ ⟨x, hx, rfl⟩
      exact hv x hx
    · intro hv x hx
      exact hv _ ⟨x, hx, rfl⟩
  refine ⟨hP, hN, hc, horth, hndP, hndN, ⟨L.map ρ, hC, fun c => ⟨?_, ?_⟩⟩, h3, hfixL, hRfix⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, hρapp x⟩
  · rintro ⟨x, hx, hxc⟩
    refine ⟨x, hx, Subtype.ext (LinearEquiv.ext fun a => Subtype.ext ?_)⟩
    rw [hρapp, hxc]

end CFSG.LocalAnalysis.ComponentInitial.ProjectiveOrthogonal
