module

public import CFSG.ClassicalInvolution.Balance.BootstrapExoticD4
public import CFSG.ClassicalInvolution.Balance.LayerGenerationPairBridge

public section

namespace CFSG.ClassicalInvolution.Balance.Q27

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
open scoped MatrixGroups

section Surjection

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]

theorem exists_surjective_of_modOdd {a : G} {K : Subgroup G}
    (hKa : K ≤ Subgroup.centralizer ({a} : Set G))
    (hK : Nonempty (↥K ⧸ classicalInvolutionOddCore ↥K ≃* SL(2, GaloisField p f)))
    {B : Type} [Group B] (u : B →* OddQuot a) (hu : u.range = modOdd a K) :
    ∃ ψ : B →* SL(2, GaloisField p f), Function.Surjective ψ := by
  obtain ⟨e⟩ := hK
  let τ : ↥K →* OddQuot a := (oddQuotMk a).comp (Subgroup.inclusion hKa)
  have hτ : τ.range = modOdd a K := by
    ext y
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨Subgroup.inclusion hKa k, k.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c.1, hc⟩, rfl⟩
  have hker : τ.ker ≤ classicalInvolutionOddCore ↥K := by
    have h1 : τ.ker = (componentClassificationOddCore
        ↥(Subgroup.centralizer ({a} : Set G))).comap (Subgroup.inclusion hKa) := by
      ext k
      simp [τ, MonoidHom.mem_ker, oddQuotMk, QuotientGroup.eq_one_iff]
    rw [h1]
    refine CFSG.ComponentClassification.OddCore.maximal ↥K _
      (Subgroup.Normal.comap inferInstance _) ?_
    exact (CFSG.ComponentClassification.OddCore.odd_card
      ↥(Subgroup.centralizer ({a} : Set G))).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (Subgroup.inclusion_injective hKa))
  let φ : ↥K →* SL(2, GaloisField p f) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (classicalInvolutionOddCore ↥K))
  have hφker : τ.ker ≤ φ.ker := fun l hl => by
    have h1 : l ∈ classicalInvolutionOddCore ↥K := hker hl
    rw [MonoidHom.mem_ker]
    have h2 : QuotientGroup.mk' (classicalInvolutionOddCore ↥K) l = 1 :=
      (QuotientGroup.eq_one_iff l).2 h1
    show e (QuotientGroup.mk' (classicalInvolutionOddCore ↥K) l) = 1
    rw [h2, map_one]
  obtain ⟨ψ, hψ⟩ := exists_hom_of_range_eq u τ (hu.trans hτ.symm) φ hφker
  have hφs : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥K))
  exact ⟨ψ, MonoidHom.range_eq_top.1 (hψ.trans (MonoidHom.range_eq_top.2 hφs))⟩

end Surjection

section Pair

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {A : Subgroup G}

theorem exists_pair_frame_data_members (hΩ : InClass p f Ω) (hT : IndepTripleOn p f Ω A) {a : G}
    (ha : a ∈ A) (ha1 : a ≠ 1) (D : LocalLieSystemAt p f Ω a) (j : Fin D.card)
    {F₀ : Subgroup G} (hF₀A : F₀ ≤ A) (hF₀4 : Nat.card F₀ = 4)
    (hfaith : ∀ g ∈ modOdd a F₀, g ≠ 1 → ¬ ∀ y ∈ (componentHom hΩ D j).range, g * y = y * g) :
    ∃ R₁ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    ∃ R₂ ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
    ∃ z₁ ∈ R₁.map (componentHom hΩ D j), ∃ z₂ ∈ R₂.map (componentHom hΩ D j),
      (∀ y ∈ R₁.map (componentHom hΩ D j), z₁ * y = y * z₁) ∧
      (∀ y ∈ R₂.map (componentHom hΩ D j), z₂ * y = y * z₂) ∧
      (∀ y ∈ R₁.map (componentHom hΩ D j), z₂ * y = y * z₂) ∧
      (∀ y ∈ R₂.map (componentHom hΩ D j), z₁ * y = y * z₁) ∧
      (∃ K₂ : Subgroup G, K₂ ≤ Subgroup.centralizer ({a} : Set G) ∧
        Nonempty (↥K₂ ⧸ classicalInvolutionOddCore ↥K₂ ≃* SL(2, GaloisField p f)) ∧
        modOdd a K₂ = R₂.map (componentHom hΩ D j)) ∧
      ∃ f₁ ∈ modOdd a F₀, ∃ f₂ ∈ modOdd a F₀, f₁ ≠ 1 ∧ f₂ ≠ 1 ∧ f₁ ≠ f₂ ∧
        (∀ y ∈ (componentHom hΩ D j).range, f₁ * y * f₁⁻¹ = z₁ * y * z₁⁻¹) ∧
        (∀ y ∈ (componentHom hΩ D j).range, f₂ * y * f₂⁻¹ = z₂ * y * z₂⁻¹) := by
  classical
  obtain ⟨K, z, hK, hcomm, rfl, hel, hcard⟩ := hT
  have hKA := triple_centralizes (p := p) (f := f) hK hcomm
  have hA2 : ∀ x ∈ Subgroup.closure (Set.range z), x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hel.2 x hx
  have hAc : ∀ x ∈ Subgroup.closure (Set.range z), ∀ y ∈ Subgroup.closure (Set.range z),
      x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hel.1.is_comm.comm (⟨x, hx⟩ : Subgroup.closure (Set.range z)) ⟨y, hy⟩)
  have hAC : ∀ g ∈ Subgroup.closure (Set.range z), g ∈ Subgroup.centralizer ({a} : Set G) :=
    fun g hg => Subgroup.mem_centralizer_singleton_iff.mpr (hAc g hg a ha)
  have hzA : ∀ m, z m ∈ Subgroup.closure (Set.range z) := fun m => Subgroup.subset_closure ⟨m, rfl⟩
  have hz2 : ∀ m, z m * z m = 1 := fun m => by
    have := pow_orderOf_eq_one (z m)
    rwa [(hK m).2.orderOf_eq_two, pow_two] at this
  have hKm : ∀ m, K m ∈ centMembers Ω a := fun m =>
    ⟨(hK m).1, (hKA m).trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha))⟩
  set L : Subgroup (OddQuot a) := (componentHom hΩ D j).range with hL
  set B : Subgroup G := Subgroup.closure (Set.range z) ⊓
    ((Subgroup.centralizer (L : Set (OddQuot a))).comap (oddQuotMk a)).map
      (Subgroup.centralizer ({a} : Set G)).subtype with hB
  have hBmem : ∀ (g : G) (hg : g ∈ Subgroup.closure (Set.range z)), g ∈ B ↔
      ∀ y ∈ L, oddQuotMk a ⟨g, hAC g hg⟩ * y = y * oddQuotMk a ⟨g, hAC g hg⟩ := by
    intro g hg
    constructor
    · rintro ⟨-, ⟨c, hc, hcg⟩⟩ y hy
      have hcg' : c = ⟨g, hAC g hg⟩ := Subtype.ext hcg
      subst hcg'
      exact (Subgroup.mem_centralizer_iff.mp hc y hy).symm
    · intro h
      exact ⟨hg, ⟨⟨g, hAC g hg⟩, Subgroup.mem_centralizer_iff.mpr fun y hy => (h y hy).symm,
        rfl⟩⟩
  have haB : a ∈ B := (hBmem a ha).mpr fun y _ => oddQuotMk_central (hAC a ha) y
  have hne1 : ∀ (g : G) (hg : g ∈ Subgroup.closure (Set.range z)), g ≠ 1 →
      oddQuotMk a ⟨g, hAC g hg⟩ ≠ 1 := fun g hg hg1 h => by
    have hsq : (⟨g, hAC g hg⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hg⟩ = 1 :=
      Subtype.ext (hA2 g hg)
    exact hg1 (congrArg Subtype.val (eq_one_of_oddQuotMk_eq_one hsq h))
  have hFB : ∀ f₀ ∈ F₀, f₀ ∈ B → f₀ = 1 := by
    intro f₀ hf₀ hfB
    by_contra hne
    have hf₀A := hF₀A hf₀
    exact hfaith _ (oddQuotMk_mem_modOdd hf₀ (hAC f₀ hf₀A)) (hne1 f₀ hf₀A hne)
      ((hBmem f₀ hf₀A).mp hfB)
  obtain ⟨x, ⟨m, rfl⟩, y, ⟨m', rfl⟩, hxB, hyB, hxyB, hrep⟩ :=
    exists_pair_in_subgroup hA2 hAc hcard (S := Set.range z) (fun w ⟨m, hm⟩ => hm ▸ hzA m) rfl
      (B := B) ha haB ha1 hF₀A hF₀4 hFB
  have hmm : m ≠ m' := by
    rintro rfl
    exact hxyB (by rw [hz2 m]; exact B.one_mem)
  have hfund : ∀ n, z n ∉ B → ∃ R ∈ fundamentalSubgroups (D.tag j) (compModel D j).D,
      modOdd a (K n) = R.map (componentHom hΩ D j) := by
    intro n hn
    rcases member_image_dichotomy hΩ D j (hKm n) with h | h
    · exact h
    · exfalso
      apply hn
      rw [hBmem (z n) (hzA n)]
      exact fun y' hy' => h _ (oddQuotMk_mem_modOdd (hK n).2.mem (hAC _ (hzA n))) y' hy'
  obtain ⟨R₁, hR₁, hR₁K⟩ := hfund m hxB
  obtain ⟨R₂, hR₂, hR₂K⟩ := hfund m' hyB
  set z₁ : OddQuot a := oddQuotMk a ⟨z m, hAC _ (hzA m)⟩ with hz₁
  set z₂ : OddQuot a := oddQuotMk a ⟨z m', hAC _ (hzA m')⟩ with hz₂
  have hz₁sq : z₁ * z₁ = 1 := by
    rw [hz₁, ← map_mul]
    have : (⟨z m, hAC _ (hzA m)⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨z m, hAC _ (hzA m)⟩ =
        1 := Subtype.ext (hz2 m)
    rw [this, map_one]
  have hz₂sq : z₂ * z₂ = 1 := by
    rw [hz₂, ← map_mul]
    have : (⟨z m', hAC _ (hzA m')⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
        ⟨z m', hAC _ (hzA m')⟩ = 1 := Subtype.ext (hz2 m')
    rw [this, map_one]
  have hz₁mem : z₁ ∈ R₁.map (componentHom hΩ D j) := by
    rw [← hR₁K]
    exact oddQuotMk_mem_modOdd (hK m).2.mem _
  have hz₂mem : z₂ ∈ R₂.map (componentHom hΩ D j) := by
    rw [← hR₂K]
    exact oddQuotMk_mem_modOdd (hK m').2.mem _
  refine ⟨R₁, hR₁, R₂, hR₂, z₁, hz₁mem, z₂, hz₂mem, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hR₁K]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [hz₁, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext ((hK m).2.isCentralInvolution.central _ hk))
  · rw [← hR₂K]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [hz₂, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext ((hK m').2.isCentralInvolution.central _ hk))
  · rw [← hR₁K]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [hz₂, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext
      (hcomm m m' hmm _ hk _ (hK m').2.isCentralInvolution.mem).symm)
  · rw [← hR₂K]
    intro y' hy'
    obtain ⟨k, hk, rfl⟩ := mem_modOdd_iff.mp hy'
    rw [hz₁, ← map_mul, ← map_mul]
    exact congrArg (oddQuotMk a) (Subtype.ext
      (hcomm m' m hmm.symm _ hk _ (hK m).2.isCentralInvolution.mem).symm)
  · exact ⟨K m', (hKm m').2, (hK m').2.nonempty_equiv, hR₂K⟩
  ·
    have hact : ∀ (g : G) (hgA : g ∈ Subgroup.closure (Set.range z)) (zg : G)
        (hzgA : zg ∈ Subgroup.closure (Set.range z)), g ∈ F₀ → g * zg ∈ B → zg * zg = 1 →
        ∀ y' ∈ L, oddQuotMk a ⟨g, hAC g hgA⟩ * y' * (oddQuotMk a ⟨g, hAC g hgA⟩)⁻¹ =
          oddQuotMk a ⟨zg, hAC zg hzgA⟩ * y' * (oddQuotMk a ⟨zg, hAC zg hzgA⟩)⁻¹ := by
      intro g hgA zg hzgA hgF hgB hzg y' hy'
      have hgsq : oddQuotMk a ⟨g, hAC g hgA⟩ * oddQuotMk a ⟨g, hAC g hgA⟩ = 1 := by
        rw [← map_mul]
        have : (⟨g, hAC g hgA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) * ⟨g, hAC g hgA⟩ = 1 :=
          Subtype.ext (hA2 g hgA)
        rw [this, map_one]
      have hzsq : oddQuotMk a ⟨zg, hAC zg hzgA⟩ * oddQuotMk a ⟨zg, hAC zg hzgA⟩ = 1 := by
        rw [← map_mul]
        have : (⟨zg, hAC zg hzgA⟩ : ↥(Subgroup.centralizer ({a} : Set G))) *
            ⟨zg, hAC zg hzgA⟩ = 1 := Subtype.ext hzg
        rw [this, map_one]
      have hB' := (hBmem (g * zg) (Subgroup.mul_mem _ hgA hzgA)).mp hgB y' hy'
      have h3 : oddQuotMk a ⟨g * zg, hAC _ (Subgroup.mul_mem _ hgA hzgA)⟩ =
          oddQuotMk a ⟨g, hAC g hgA⟩ * oddQuotMk a ⟨zg, hAC zg hzgA⟩ := by
        rw [← map_mul]
        rfl
      rw [h3] at hB'
      set u := oddQuotMk a ⟨g, hAC g hgA⟩ with hu
      set w := oddQuotMk a ⟨zg, hAC zg hzgA⟩ with hw
      have hu' : u * w * y' * (u * w)⁻¹ = y' := by
        rw [hB']
        group
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hgsq
      calc u * y' * u⁻¹ = u * (u * w * y' * (u * w)⁻¹) * u⁻¹ := by rw [hu']
        _ = (u * u) * w * y' * w⁻¹ * (u⁻¹ * u⁻¹) := by group
        _ = w * y' * w⁻¹ := by
          rw [hgsq, hui, hgsq]
          group
    obtain ⟨f₁, hf₁F, hf₁1, hf₁B⟩ := hrep (z m) (Or.inl rfl)
    obtain ⟨f₂, hf₂F, hf₂1, hf₂B⟩ := hrep (z m') (Or.inr (Or.inl rfl))
    have hf₁A := hF₀A hf₁F
    have hf₂A := hF₀A hf₂F
    have hact₁ := hact f₁ hf₁A (z m) (hzA m) hf₁F hf₁B (hz2 m)
    have hact₂ := hact f₂ hf₂A (z m') (hzA m') hf₂F hf₂B (hz2 m')
    refine ⟨oddQuotMk a ⟨f₁, hAC f₁ hf₁A⟩, oddQuotMk_mem_modOdd hf₁F _,
      oddQuotMk a ⟨f₂, hAC f₂ hf₂A⟩, oddQuotMk_mem_modOdd hf₂F _, hne1 f₁ hf₁A hf₁1,
      hne1 f₂ hf₂A hf₂1, ?_, hact₁, hact₂⟩
    intro heq
    apply hxyB
    rw [hBmem _ (Subgroup.mul_mem _ (hzA m) (hzA m'))]
    intro y' hy'
    have e1 := hact₁ y' hy'
    have e2 := hact₂ y' hy'
    rw [heq] at e1
    have e3 : z₁ * y' * z₁⁻¹ = z₂ * y' * z₂⁻¹ := e1.symm.trans e2
    have hc12 : z₁ * z₂ = z₂ * z₁ := by
      rw [hz₁, hz₂, ← map_mul, ← map_mul]
      exact congrArg (oddQuotMk a) (Subtype.ext (hAc _ (hzA m) _ (hzA m')))
    have hz₂i : z₂⁻¹ = z₂ := inv_eq_of_mul_eq_one_right hz₂sq
    have hz₁i : z₁⁻¹ = z₁ := inv_eq_of_mul_eq_one_right hz₁sq
    have h3 : oddQuotMk a ⟨z m * z m', hAC _ (Subgroup.mul_mem _ (hzA m) (hzA m'))⟩ = z₁ * z₂ := by
      rw [hz₁, hz₂, ← map_mul]
      rfl
    rw [h3]
    have e4 : z₂ * (z₁ * y' * z₁) * z₂ = y' := by
      have e3' : z₁ * y' * z₁ = z₂ * y' * z₂ := by
        simpa only [hz₁i, hz₂i] using e3
      rw [e3']
      calc z₂ * (z₂ * y' * z₂) * z₂ = (z₂ * z₂) * y' * (z₂ * z₂) := by group
        _ = y' := by rw [hz₂sq]; group
    have e5 : (z₂ * z₁) * y' * (z₁ * z₂) = y' := by
      calc (z₂ * z₁) * y' * (z₁ * z₂) = z₂ * (z₁ * y' * z₁) * z₂ := by group
        _ = y' := e4
    have e6 : (z₂ * z₁) * y' = y' * (z₂ * z₁) := by
      calc (z₂ * z₁) * y' = (z₂ * z₁) * y' * (z₁ * z₂) * (z₁ * z₂)⁻¹ := by group
        _ = y' * (z₁ * z₂)⁻¹ := by rw [e5]
        _ = y' * (z₂ * z₁) := by rw [mul_inv_rev, hz₁i, hz₂i]
    rw [hc12]
    exact e6

end Pair

end CFSG.ClassicalInvolution.Balance.Q27
