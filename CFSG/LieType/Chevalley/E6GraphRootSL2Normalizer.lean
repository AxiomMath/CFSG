module

public import CFSG.LieType.Chevalley.E6GraphRootSL2Basic
public import CFSG.LieType.Chevalley.E6GraphRadicalCocycle
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer

public noncomputable section

namespace CFSG.LieType.Chevalley.E6GraphRootSL2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.E6GraphHighestRoot
  CFSG.LieType.Chevalley.E6GraphLevi

variable {E : Type} [Field E] {F₀ : Type} [Field F₀]

theorem normalizer_eq_sup
    [Finite F₀] (h2 : (2 : E) = 0) (ι : F₀ →+* E)
    {G L : Subgroup (ModGL TwistTag.E6.tag E)} (hXG : thetaRankOneGroup ι ≤ G) (hLG : L ≤ G)
    (hLC : L ≤ Subgroup.centralizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)))
    (hNR : ∀ g ∈ Subgroup.normalizer (thetaRootGroup ι : Set (ModGL TwistTag.E6.tag E)) ⊓ G,
      ∃ q ∈ parabolicRadical TwistTag.E6.tag E setA, ∃ l ∈ L, ∃ h ∈ thetaTorus ι,
        g = q * (l * h)) :
    Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) ⊓ G =
        thetaRankOneGroup ι ⊔ L ∧
      thetaRankOneGroup ι ⊓ L = ⊥ ∧
      (∀ x ∈ thetaRankOneGroup ι, ∀ l ∈ L, x * l = l * x) ∧
      ∀ g ∈ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) ⊓ G,
        ∃! p : ModGL TwistTag.E6.tag E × ModGL TwistTag.E6.tag E,
          p.1 ∈ thetaRankOneGroup ι ∧ p.2 ∈ L ∧ g = p.1 * p.2 := by
  have hcomm : ∀ x ∈ thetaRankOneGroup ι, ∀ l ∈ L, x * l = l * x := fun x hx l hl =>
    Subgroup.mem_centralizer_iff.1 (hLC hl) x hx
  have hbot := thetaRankOneGroup_inf_eq_bot h2 ι hLC
  have hXN : thetaRankOneGroup ι ≤
      Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) :=
    Subgroup.le_normalizer
  have hLN : L ≤ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) :=
    hLC.trans (Subgroup.centralizer_le_normalizer _)
  have hfac : ∀ g ∈ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) ⊓ G,
      ∃ x ∈ thetaRankOneGroup ι, ∃ l ∈ L, g = x * l := by
    intro g hg
    obtain ⟨hgN, hgG⟩ := Subgroup.mem_inf.1 hg
    obtain ⟨x, hx, hxg⟩ := exists_mul_mem_normalizer h2 ι hgN
    obtain ⟨q, hq, l, hl, h, hh, he⟩ := hNR _ (Subgroup.mem_inf.2 ⟨hxg, mul_mem (hXG hx) hgG⟩)
    have hhX : h ∈ thetaRankOneGroup ι := thetaTorus_le_thetaRankOneGroup h2 ι hh
    have hqe : q = x * g * (l * h)⁻¹ := by rw [he]; group
    have hqN : q ∈ Subgroup.normalizer (thetaRankOneGroup ι : Set (ModGL TwistTag.E6.tag E)) := by
      rw [hqe]
      exact mul_mem (mul_mem (hXN hx) hgN) (inv_mem (mul_mem (hLN hl) (hXN hhX)))
    have hqR := mem_thetaRootGroup_of_mem_normalizer h2 ι hq hqN
    have hRX : thetaRootGroup ι ≤ thetaRankOneGroup ι := le_sup_left
    refine ⟨x⁻¹ * q * h, mul_mem (mul_mem (inv_mem hx) (hRX hqR)) hhX, l, hl, ?_⟩
    calc g = x⁻¹ * (x * g) := by group
      _ = x⁻¹ * q * (l * h) := by rw [he]; group
      _ = x⁻¹ * q * (h * l) := by rw [hcomm h hhX l hl]
      _ = x⁻¹ * q * h * l := by group
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (le_inf hXN hXG) (le_inf hLN hLG)), hbot, hcomm,
    fun g hg => ?_⟩
  · obtain ⟨x, hx, l, hl, rfl⟩ := hfac g hg
    exact mul_mem (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right hl)
  · obtain ⟨x, hx, l, hl, rfl⟩ := hfac g hg
    refine ⟨(x, l), ⟨hx, hl, rfl⟩, ?_⟩
    rintro ⟨x', l'⟩ ⟨hx', hl', he⟩
    have h1 : x'⁻¹ * x = l' * l⁻¹ := by
      calc x'⁻¹ * x = x'⁻¹ * (x * l) * l⁻¹ := by group
        _ = l' * l⁻¹ := by rw [he]; group
    have h2' : x'⁻¹ * x ∈ thetaRankOneGroup ι ⊓ L :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx') hx, by rw [h1]; exact mul_mem hl' (inv_mem hl)⟩
    rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at h2'
    subst h2'
    have : l' = l := by
      have := congrArg (fun g => x'⁻¹ * g) he
      simpa using this.symm
    rw [this]

theorem _root_.CFSG.LieType.Chevalley.even_E6_graph_root_SL2_normalizer
    (f : ℕ) (hf : 1 ≤ f)
    (k K : Type) [Field k] [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    (thetaRankOneGroup (RingHom.id k) ≤ adjointGroup TwistTag.E6.tag k ∧
      subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ≤
        adjointGroup TwistTag.E6.tag k ∧
      Subgroup.normalizer (thetaRankOneGroup (RingHom.id k) : Set (ModGL TwistTag.E6.tag k)) ⊓
          adjointGroup TwistTag.E6.tag k =
        thetaRankOneGroup (RingHom.id k) ⊔
          (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) ∧
      thetaRankOneGroup (RingHom.id k) ⊓
          (subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k) = ⊥ ∧
      (∀ x ∈ thetaRankOneGroup (RingHom.id k),
        ∀ l ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k,
          x * l = l * x) ∧
      (∀ g ∈ Subgroup.normalizer (thetaRankOneGroup (RingHom.id k) :
          Set (ModGL TwistTag.E6.tag k)) ⊓ adjointGroup TwistTag.E6.tag k,
        ∃! p : ModGL TwistTag.E6.tag k × ModGL TwistTag.E6.tag k,
          p.1 ∈ thetaRankOneGroup (RingHom.id k) ∧
          p.2 ∈ subsystemGroup TwistTag.E6.tag k setA ⊓ adjointGroup TwistTag.E6.tag k ∧
          g = p.1 * p.2) ∧
      ∀ x ∈ thetaRankOneGroup (RingHom.id k),
        diagramMap TwistTag.E6 k * x * (diagramMap TwistTag.E6 k)⁻¹ = x) ∧
    (thetaRankOneGroup (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ ∧
      subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ≤
        graphFixedRootGroup TwistTag.E6 K σ ∧
      Subgroup.normalizer (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ =
        thetaRankOneGroup (algebraMap k K) ⊔
          (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) ∧
      thetaRankOneGroup (algebraMap k K) ⊓
          (subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ) = ⊥ ∧
      (∀ x ∈ thetaRankOneGroup (algebraMap k K),
        ∀ l ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ,
          x * l = l * x) ∧
      (∀ g ∈ Subgroup.normalizer (thetaRankOneGroup (algebraMap k K) :
          Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ,
        ∃! p : ModGL TwistTag.E6.tag K × ModGL TwistTag.E6.tag K,
          p.1 ∈ thetaRankOneGroup (algebraMap k K) ∧
          p.2 ∈ subsystemGroup TwistTag.E6.tag K setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
          g = p.1 * p.2) ∧
      ∀ x ∈ thetaRankOneGroup (algebraMap k K),
        diagramMap TwistTag.E6 K * x * (diagramMap TwistTag.E6 K)⁻¹ = x) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have hσk : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c
  obtain ⟨hO, hT⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  obtain ⟨hNO, hNT⟩ := even_E6_graph_highest_root_normalizer f hf k K hk hK σ hσ
  refine ⟨?_, ?_⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hLX, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hXfix,
      -, -⟩ := hO
    obtain ⟨-, -, -, hfac, -⟩ := hNO
    have hXG := E6GraphRadical.thetaRankOneGroup_le_adjointGroup (E := k) (RingHom.id k)
    obtain ⟨h1, h2, h3, h4⟩ := normalizer_eq_sup hk2 (RingHom.id k) hXG inf_le_right hLX
      fun g hg => by
        obtain ⟨⟨q, l, h⟩, ⟨hq, hl, hh, he⟩, -⟩ := hfac g hg
        exact ⟨q, (Subgroup.mem_inf.1 hq).1, l, hl, h, hh, he⟩
    exact ⟨hXG, inf_le_right, h1, h2, h3, h4, hXfix⟩
  · obtain ⟨-, -, -, -, -, -, -, -, hLX, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, hXfix, -, -⟩ := hT
    obtain ⟨-, -, -, hfac, -⟩ := hNT
    have hXG := thetaRankOneGroup_le_graphFixedRootGroup (k := k) hK2 hσk
    obtain ⟨h1, h2, h3, h4⟩ := normalizer_eq_sup hK2 (algebraMap k K) hXG inf_le_right hLX
      fun g hg => by
        obtain ⟨⟨q, l, h⟩, ⟨hq, hl, hh, he⟩, -⟩ := hfac g hg
        exact ⟨q, (Subgroup.mem_inf.1 hq).1, l, hl, h, hh, he⟩
    exact ⟨hXG, inf_le_right, h1, h2, h3, h4, hXfix⟩

end CFSG.LieType.Chevalley.E6GraphRootSL2
