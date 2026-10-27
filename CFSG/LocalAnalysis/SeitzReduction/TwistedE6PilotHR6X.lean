module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotModel
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.LieType.Chevalley.E7SupportedBruhat
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSL2

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.E6GraphLevi CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Assembly.LowTwoRank
  CFSG.LieType.Chevalley.E6GraphHighestRoot

section Defs

variable {K : Type} [Field K]

@[expose] noncomputable def su6Levi (σ : K →+* K) : Subgroup (ModGL TwistTag.E6.tag K) :=
  subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓ graphFixedRootGroup TwistTag.E6 K σ

theorem su6Levi_le_graphFixedRootGroup (σ : K →+* K) :
    su6Levi σ ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  inf_le_right

theorem su6Levi_le_subsystemGroup (σ : K →+* K) :
    su6Levi σ ≤ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
  inf_le_left

theorem sigma_eq_pow_card {f : ℕ} {k : Type} [Field k] (hk : Nat.card k = 2 ^ f) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) : ∀ c, σ c = c ^ Nat.card k := fun c => by rw [hk]; exact hσ c

end Defs


section Facts

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem su6Levi_facts (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    su6Levi σ ≤ centralizer (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ∧
      su6Levi σ ⊔ thetaTorus (algebraMap k K) =
        parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA ⊓ graphFixedRootGroup TwistTag.E6 K σ ∧
      su6Levi σ ⊓ thetaTorus (algebraMap k K) = ⊥ ∧
      (∀ l ∈ su6Levi σ, ∀ h ∈ thetaTorus (algebraMap k K), l * h = h * l) ∧
      su6Levi σ = subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA ⊓
        twistedFixedGroup TwistTag.E6 K σ ∧
      StatedClassicalModel (su6Levi σ) .PSU 6 2 f ∧
      ∀ (a : kˣ) (c : k),
        rootTorusSL2 TwistTag.E6.tag K e6HighestRoot (Units.map (algebraMap k K).toMonoidHom a) *
            pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K c) *
            (rootTorusSL2 TwistTag.E6.tag K e6HighestRoot
              (Units.map (algebraMap k K).toMonoidHom a))⁻¹ =
          pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K ((a : k) ^ 2 * c)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, h9, h10, h11, h12, -, -, -, -, -, -, -, -, h21, -, -, -, -,
    -, h27, -, -, -, -, -, h33⟩ := even_E6_graph_finite_Levi_intersections f hf k K hk hK σ hσ
  exact ⟨h9, h10, h11, h12, h21, h27, h33⟩

theorem lieModel_su6Levi (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    LieModel (su6Levi σ) .PSU 6 2 f :=
  Or.inl ⟨by decide, (su6Levi_facts hf hk hK hσ).2.2.2.2.2.1⟩

theorem thetaRankOneGroup_le_C0 [Finite k] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    thetaRankOneGroup (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  thetaRankOneGroup_le_graphFixedRootGroup (two_eq_zero_of_card_sq hf hK)
    (sigma_eq_pow_card hk hσ)

theorem thetaTorus_le_thetaRankOneGroup' (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    thetaTorus (algebraMap k K) ≤ thetaRankOneGroup (algebraMap k K) :=
  thetaTorus_le_thetaRankOneGroup (two_eq_zero_of_card_sq hf hK) _

theorem thetaTorus_le_C0 [Finite k] (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    thetaTorus (algebraMap k K) ≤ graphFixedRootGroup TwistTag.E6 K σ :=
  (thetaTorus_le_thetaRankOneGroup' hf hK).trans (thetaRankOneGroup_le_C0 hf hk hK hσ)

omit
  [Algebra k K] in
theorem thetaTorus_le_centralizer_self (ι : k →+* K) :
    thetaTorus ι ≤ centralizer (thetaTorus ι : Set (ModGL TwistTag.E6.tag K)) := by
  rintro _ ⟨a, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, rfl⟩
  rw [← map_mul, mul_comm, map_mul]

end Facts

section Split

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem rootSpan_perpRoots_le_subsystemGroup :
    rootSpan .E6 K (EPilot.perpRoots .E6) ≤
      subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  rw [subsystemGroup_eq_rootSpan]
  refine rootSpan_mono fun γ hγ => ⟨hγ.1, fun i hi => ?_⟩
  have hi1 : i = e6Idx 1 := by
    by_contra h
    exact hi h
  subst hi1
  exact hγ.2

theorem highTorusLine_sup_le_parabolicLevi :
    EPilot.highTorusLine .E6 K ⊔ rootSpan .E6 K (EPilot.perpRoots .E6) ≤
      parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA :=
  sup_le ((EPilot.highTorusLine_le_torusGroup (Or.inl rfl)).trans le_sup_left)
    (rootSpan_perpRoots_le_subsystemGroup.trans subsystemGroup_le_parabolicLevi')

omit
  [Algebra k K] in
theorem rootDiagUnit_highDiag_mem_thetaTorus (ι : k →+* K) (c : kˣ) :
    rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 (Units.map ι.toMonoidHom c)) ∈
      thetaTorus ι :=
  ⟨c, rfl⟩

theorem centralizer_highDiag_inf_le (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) {c : kˣ}
    (hc : 3 ≤ orderOf c) {g : ModGL TwistTag.E6.tag K}
    (hgc : g * rootDiagUnit TwistTag.E6.tag
        (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c)) =
      rootDiagUnit TwistTag.E6.tag
        (EPilot.highDiag .E6 (Units.map (algebraMap k K).toMonoidHom c)) * g)
    (hgC : g ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    g ∈ su6Levi σ ⊔ thetaTorus (algebraMap k K) := by
  have := finite_of_card hK
  have := charP_two_of_card hf hK
  set c' := Units.map (algebraMap k K).toMonoidHom c with hc'
  have hc3 : 3 ≤ orderOf c' := by
    rw [hc', orderOf_injective _ (Units.map_injective (algebraMap k K).injective) c]
    exact hc
  have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgC).1
  have hgT : g ∈ toralCentralizer .E6 K (EPilot.highDiag .E6 c') := by
    refine mem_toralCentralizer.2 ⟨hgA, ?_⟩
    change rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 c') * g *
      (rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 c'))⁻¹ = g
    rw [← hgc, mul_inv_cancel_right]
  rw [(EPilot.toralCentralizer_highDiag_eq_sup (Or.inl rfl) (ringChar.eq K 2) hc3).1] at hgT
  have hgM : g ∈ parabolicLevi TwistTag.E6.tag K E6GraphLevi.setA ⊓
      graphFixedRootGroup TwistTag.E6 K σ :=
    ⟨highTorusLine_sup_le_parabolicLevi hgT, hgC⟩
  rw [← (su6Levi_facts hf hk hK hσ).2.1] at hgM
  exact hgM

theorem centralizer_thetaTorus_inf_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (thetaTorus (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
          graphFixedRootGroup TwistTag.E6 K σ =
        thetaTorus (algebraMap k K) ⊔ su6Levi σ ∧
      Disjoint (thetaTorus (algebraMap k K)) (su6Levi σ) ∧
      thetaTorus (algebraMap k K) ≤ centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) := by
  have hf : 1 ≤ f := by omega
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  obtain ⟨-, -, hinf, hcomm, -, -, -⟩ := su6Levi_facts hf hk hK hσ
  have hq : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨c, hc⟩ := F4Pilot.exists_three_le_orderOf hq
  have hHc : thetaTorus (algebraMap k K) ≤
      centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) :=
    fun h hh => mem_centralizer_iff.2 fun l hl => hcomm l hl h hh
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (le_inf (thetaTorus_le_centralizer_self _)
      (thetaTorus_le_C0 hf hk hK hσ)) (le_inf (fun l hl => mem_centralizer_iff.2 fun h hh =>
        (hcomm l hl h hh).symm) (su6Levi_le_graphFixedRootGroup σ))), ?_, hHc⟩
  · obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
    have h := centralizer_highDiag_inf_le hf hk hK hσ hc
      ((mem_centralizer_iff.1 hgc _ (rootDiagUnit_highDiag_mem_thetaTorus _ c)).symm) hgC
    rwa [sup_comm] at h
  · rw [disjoint_iff, inf_comm]
    exact hinf

theorem centralizer_thetaRankOneGroup_inf_eq (hf2 : 2 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f) :
    centralizer (thetaRankOneGroup (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
        graphFixedRootGroup TwistTag.E6 K σ = su6Levi σ := by
  have hf : 1 ≤ f := by omega
  have hK2 := two_eq_zero_of_card_sq hf hK
  obtain ⟨hLX, -, hinf, hcomm, -, -, hconj⟩ := su6Levi_facts hf hk hK hσ
  refine le_antisymm (fun g hg => ?_) (le_inf hLX (su6Levi_le_graphFixedRootGroup σ))
  obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
  have hgW : g ∈ centralizer (thetaTorus (algebraMap k K) : Set (ModGL TwistTag.E6.tag K)) ⊓
      graphFixedRootGroup TwistTag.E6 K σ :=
    ⟨centralizer_le (thetaTorus_le_thetaRankOneGroup' hf hK) hgc, hgC⟩
  rw [(centralizer_thetaTorus_inf_eq hf2 hk hK hσ).1, sup_comm] at hgW
  obtain ⟨⟨l, h⟩, ⟨hl, hh, rfl⟩, -⟩ := existsUnique_mul_of_commute hinf hcomm g hgW
  have hX1 : pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) ∈
      thetaRankOneGroup (algebraMap k K) :=
    mem_sup_left ((mem_thetaRootGroup _).2 ⟨1, rfl⟩)
  have hlX := mem_centralizer_iff.1 (hLX hl) _ hX1
  have hgX := mem_centralizer_iff.1 hgc _ hX1
  have hhX : h * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) =
      pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) * h := by
    have e1 : l * (h * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1)) =
        l * (pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) * h) := by
      calc l * (h * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1)) =
            l * h * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) := by group
        _ = pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) * (l * h) := hgX.symm
        _ = l * pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) * h := by
          rw [← mul_assoc, ← hlX]
        _ = l * (pinnedX TwistTag.E6.tag K e6HighestRoot (algebraMap k K 1) * h) := by group
    exact mul_left_cancel e1
  obtain ⟨a, rfl⟩ := (mem_thetaTorus _).1 hh
  have h1 := hconj a 1
  rw [hhX, mul_inv_cancel_right, mul_one] at h1
  have h2 := pinnedX_injective (τ := TwistTag.E6.tag) (R := K) e6HighestRoot h1
  have ha2 : (a : k) ^ 2 = 1 := (algebraMap k K).injective (by rw [h2])
  have ha : a = 1 := Units.ext (eq_one_of_mul_self_eq_one_of_two_eq_zero
    (two_eq_zero_of_card hf hk) (by rw [← sq]; exact ha2))
  subst ha
  rw [map_one, ← thetaTorusHom_apply, map_one, mul_one]
  exact hl

end Split

section Field

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem finrank_eq_two (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2) :
    Module.finrank k K = 2 := by
  have : Finite K := finite_of_card hK
  have h := Module.natCard_eq_pow_finrank (K := k) (V := K)
  rw [hK, hk] at h
  have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
  exact (Nat.pow_right_injective h2 h).symm

theorem sigma_eq_self_iff [Finite k] (hk : Nat.card k = 2 ^ f) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) (z : K) : σ z = z ↔ z ∈ Set.range (algebraMap k K) := by
  refine ⟨fun h => mem_range_algebraMap_of_pow_card_eq (by rw [← sigma_eq_pow_card hk hσ, h]),
    ?_⟩
  rintro ⟨a, rfl⟩
  exact fixed_algebraMap (sigma_eq_pow_card hk hσ) a

theorem exists_inv_mul_map_mul_eq_HSL_of_finrank [Finite k] [CharP k 2]
    (hfin : Module.finrank k K = 2) {A : SL2 k} (hA : orderOf A = Nat.card k + 1) :
    ∃ l : Kˣ, ∃ P : SL2 K, l ≠ 1 ∧ l ^ (Nat.card k + 1) = 1 ∧
      P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A * P = HSL l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, P, -, hl1, hlq, hP⟩ := F4Pilot.exists_inv_mul_map_mul_eq_HSL hA
  set e : K ≃ₐ[k] FiniteField.Extension k 2 2 := FiniteField.algEquivExtension k 2 2 K hfin
  set φ : FiniteField.Extension k 2 2 →+* K := e.symm.toRingEquiv.toRingHom
  have hφι : φ.comp (algebraMap k (FiniteField.Extension k 2 2)) = algebraMap k K :=
    RingHom.ext fun a => e.symm.commutes a
  refine ⟨Units.map φ.toMonoidHom l, Matrix.SpecialLinearGroup.map φ P, fun h => hl1 ?_, ?_, ?_⟩
  · exact Units.map_injective φ.injective (by rw [h, map_one])
  · rw [← map_pow, hlq, map_one]
  · have h := congrArg (Matrix.SpecialLinearGroup.map φ) hP
    rw [map_mul, map_mul, map_inv, E6GraphLevi.map_HSL] at h
    rw [← h]
    congr 2
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
    exact (congrArg (fun ψ : k →+* K => ψ ((A : Matrix (Fin 2) (Fin 2) k) i j)) hφι).symm

theorem exists_inv_mul_map_mul_eq_HSL_of_orderOf_eq_three [Finite K]
    (h3K : 3 ∣ Nat.card K - 1) {A : SL2 k} (hA : orderOf A = 3) :
    ∃ l : Kˣ, ∃ P : SL2 K, orderOf l = 3 ∧
      P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap k K) A * P = HSL l := by
  set B : SL2 K := Matrix.SpecialLinearGroup.map (algebraMap k K) A with hBdef
  have hA3 : A ^ 3 = 1 := by rw [← hA]; exact pow_orderOf_eq_one A
  have hA1 : A ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hA
    omega
  have hB3 : B ^ 3 = 1 := by
    rw [hBdef, ← map_pow, hA3, map_one]
  have hB1 : B ≠ 1 := by
    intro h
    exact hA1 (F4Pilot.SL2_map_injective (algebraMap k K) (by simpa [hBdef] using h))
  have hBord : orderOf B = 3 := by
    rw [hBdef, orderOf_injective _ (F4Pilot.SL2_map_injective (algebraMap k K)) A, hA]
  obtain ⟨P, l, hP⟩ := CFSG.RankThree.PartTwo.Sec11.KS11Lie4Proof.exists_conj_HSL_of_three
    (K := K) h3K B ⟨1, by simpa using hB3⟩
  have hl3 : orderOf l = 3 := by
    have hsem : SemiconjBy P B (HSL l) := by
      rw [SemiconjBy, ← hP]
      group
    have hord : orderOf (HSL l) = orderOf B := (SemiconjBy.orderOf_eq P hsem).symm
    rw [F4Pilot.orderOf_HSL] at hord
    simpa [hBord] using hord
  exact ⟨l, P⁻¹, hl3, by simpa using hP⟩

end Field

theorem exists_eq_zpowers_of_isCyclic {G : Type*} [Group G] {X : Subgroup G} (hX : IsCyclic X) :
    ∃ x ∈ X, X = zpowers x := by
  obtain ⟨⟨x, hxX⟩, hgen⟩ := IsCyclic.exists_generator (α := X)
  refine ⟨x, hxX, le_antisymm (fun y hy => ?_) (zpowers_le.2 hxX)⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.1 (hgen ⟨y, hy⟩)
  exact mem_zpowers_iff.2 ⟨n, by simpa using congrArg Subtype.val hn⟩

theorem zpowers_le_centralizer_zpowers {G : Type*} [Group G] (x : G) :
    zpowers x ≤ centralizer (zpowers x : Set G) := by
  intro y hy
  rw [mem_centralizer_iff]
  intro z hz
  obtain ⟨a, rfl⟩ := mem_zpowers_iff.1 hy
  obtain ⟨b, rfl⟩ := mem_zpowers_iff.1 hz
  exact (Commute.zpow_zpow_self x b a).eq

section Nonsplit

variable {f : ℕ} {k K : Type} [Field k] [Field K] [Algebra k K]

theorem twistHom_mem_subsystemGroup_setA (σ : K →+* K) {g : ModGL TwistTag.E6.tag K}
    (hg : g ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) :
    twistHom TwistTag.E6 K σ g ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
  have hρ : ∀ i : Fin TwistTag.E6.tag.rank, i ≠ e6Idx 1 → TwistTag.E6.perm i ≠ e6Idx 1 := by
    decide
  refine ((Subgroup.closure_le
    ((subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA).comap (twistHom TwistTag.E6 K σ))).2
      ?_) hg
  rintro _ ⟨i, hi, c, rfl | rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_xUnit]
    exact Subgroup.subset_closure ⟨_, hρ i hi, σ c, Or.inl rfl⟩
  · rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_yUnit]
    exact Subgroup.subset_closure ⟨_, hρ i hi, σ c, Or.inr rfl⟩

theorem disjoint_range_thetaSL2_subsystemGroup (h2 : (2 : K) = 0) :
    Disjoint (thetaSL2 K).range (subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA) := by
  have : CharP K 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero h2
  rw [Subgroup.disjoint_def]
  rintro _ ⟨B, rfl⟩ hBL
  have hB : B ∈ center (SL2 K) := by
    rw [mem_center_iff]
    intro A
    apply thetaSL2_injective h2
    rw [map_mul, map_mul]
    exact (mem_centralizer_iff.1 (subsystemGroup_le_centralizer_thetaSL2 h2 hBL) _
      ⟨A, rfl⟩)
  rw [E6Pilot.eq_one_of_mem_center_SL2 hB, map_one]

theorem highTorusLine_le_range_thetaSL2 :
    EPilot.highTorusLine .E6 K ≤ (thetaSL2 K).range := by
  rintro _ ⟨c, rfl⟩
  exact ⟨HSL c, (thetaTorusHom_eq_thetaSL2 c).symm⟩

theorem thetaSL2_HSL (l : Kˣ) :
    thetaSL2 K (HSL l) = rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 l) :=
  (thetaTorusHom_eq_thetaSL2 l).symm

theorem exists_mul_su6Levi_of_conj_highDiag
    (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {x g : ModGL TwistTag.E6.tag K} {P : SL2 K} {l : Kˣ}
    (hl3 : 3 ≤ orderOf l)
    (hconj : (thetaSL2 K P)⁻¹ * x * thetaSL2 K P =
      rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 l))
    (hgx : g * x = x * g)
    (hgC : g ∈ graphFixedRootGroup TwistTag.E6 K σ) :
    ∃ j d : ModGL TwistTag.E6.tag K, j ∈ (thetaSL2 K).range ∧ d ∈ su6Levi σ ∧
      g = j * d ∧ twistHom TwistTag.E6 K σ j = j ∧
      twistHom TwistTag.E6 K σ d = d ∧ ∀ y ∈ su6Levi σ, j * y = y * j := by
  have : Finite K := finite_of_card hK
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP K 2 := charP_two_of_card hf hK
  obtain ⟨-, -, -, -, hLΓ, -, -⟩ := su6Levi_facts hf hk hK hσ
  have hgA : g ∈ adjointGroup TwistTag.E6.tag K := (graphFixedRootGroup_le _ _ _ hgC).1
  set n := thetaSL2 K P with hn
  have hnR : n ∈ (thetaSL2 K).range := ⟨P, rfl⟩
  have hnA : n ∈ adjointGroup TwistTag.E6.tag K :=
    E6Pilot.rootSL2_highRoot_mem_adjointGroup (τ := .E6) P
  have hm : n⁻¹ * g * n ∈ toralCentralizer .E6 K (EPilot.highDiag .E6 l) := by
    refine mem_toralCentralizer.2 ⟨mul_mem (mul_mem (inv_mem hnA) hgA) hnA, ?_⟩
    change rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 l) * (n⁻¹ * g * n) *
      (rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 l))⁻¹ = n⁻¹ * g * n
    rw [← hconj]
    calc n⁻¹ * x * n * (n⁻¹ * g * n) * (n⁻¹ * x * n)⁻¹ =
          n⁻¹ * (x * g) * x⁻¹ * n := by group
      _ = n⁻¹ * g * n := by rw [← hgx]; group
  obtain ⟨hTD, hdisjT, hcommT⟩ := EPilot.toralCentralizer_highDiag_eq_sup (K := K) (τ := .E6)
    (Or.inl rfl) (ringChar.eq K 2) hl3
  have hm' : (n⁻¹ * g * n : ModGL Tag.E6 K) ∈
      EPilot.highTorusLine .E6 K ⊔ rootSpan .E6 K (EPilot.perpRoots .E6) := by
    rw [← hTD]
    exact hm
  have hkey : ∃ t : ModGL TwistTag.E6.tag K, t ∈ EPilot.highTorusLine .E6 K ∧
      ∃ d : ModGL TwistTag.E6.tag K, d ∈ rootSpan .E6 K (EPilot.perpRoots .E6) ∧
        n⁻¹ * g * n = t * d := by
    obtain ⟨⟨t, d⟩, ⟨ht, hd, htd⟩, -⟩ := existsUnique_mul_of_commute (disjoint_iff.1 hdisjT)
      (fun a ha b hb => (hcommT a ha b hb).eq) _ hm'
    exact ⟨t, ht, d, hd, htd⟩
  obtain ⟨t, ht, d, hd, htd'⟩ := hkey
  have hdL : d ∈ subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA :=
    rootSpan_perpRoots_le_subsystemGroup hd
  set j := n * t * n⁻¹ with hjdef
  have hjJ : j ∈ (thetaSL2 K).range :=
    mul_mem (mul_mem hnR (highTorusLine_le_range_thetaSL2 ht)) (inv_mem hnR)
  have hnd : n * d = d * n :=
    mem_centralizer_iff.1 (subsystemGroup_le_centralizer_thetaSL2 hK2 hdL) n hnR
  have hg2 : g = j * d := by
    calc g = n * (n⁻¹ * g * n) * n⁻¹ := by group
      _ = n * (t * d) * n⁻¹ := by rw [htd']
      _ = n * t * n⁻¹ * (n * d * n⁻¹) := by group
      _ = j * d := by rw [hnd, mul_inv_cancel_right]
  have hFg : twistHom TwistTag.E6 K σ g = g :=
    ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 (graphFixedRootGroup_le _ _ _ hgC)).2
  have hFj : twistHom TwistTag.E6 K σ j ∈ (thetaSL2 K).range := by
    obtain ⟨B, hB⟩ := hjJ
    rw [← hB, twistHom_thetaSL2 hK2]
    exact ⟨_, rfl⟩
  have hFd := twistHom_mem_subsystemGroup_setA σ hdL
  have hjd : twistHom TwistTag.E6 K σ j = j ∧ twistHom TwistTag.E6 K σ d = d := by
    have h1 : (twistHom TwistTag.E6 K σ j)⁻¹ * j = twistHom TwistTag.E6 K σ d * d⁻¹ := by
      have h2 : twistHom TwistTag.E6 K σ j * twistHom TwistTag.E6 K σ d = j * d := by
        rw [← map_mul, ← hg2, hFg]
      calc (twistHom TwistTag.E6 K σ j)⁻¹ * j =
            (twistHom TwistTag.E6 K σ j)⁻¹ * (j * d) * d⁻¹ := by group
        _ = (twistHom TwistTag.E6 K σ j)⁻¹ *
            (twistHom TwistTag.E6 K σ j * twistHom TwistTag.E6 K σ d) * d⁻¹ := by rw [h2]
        _ = twistHom TwistTag.E6 K σ d * d⁻¹ := by group
    have hJ : (twistHom TwistTag.E6 K σ j)⁻¹ * j ∈ (thetaSL2 K).range :=
      mul_mem (inv_mem hFj) hjJ
    have hD : (twistHom TwistTag.E6 K σ j)⁻¹ * j ∈
        subsystemGroup TwistTag.E6.tag K E6GraphLevi.setA := by
      rw [h1]
      exact mul_mem hFd (inv_mem hdL)
    have h0 := (Subgroup.disjoint_def.1 (disjoint_range_thetaSL2_subsystemGroup hK2)) hJ hD
    rw [h0] at h1
    exact ⟨inv_mul_eq_one.1 h0, mul_inv_eq_one.1 h1.symm⟩
  have hdD : d ∈ su6Levi σ := by
    rw [hLΓ]
    exact ⟨hdL, (mem_twistedFixedGroup_iff_twistHom _ _ _).2
      ⟨subsystemGroup_le_adjointGroup hdL, hjd.2⟩⟩
  refine ⟨j, d, hjJ, hdD, hg2, hjd.1, hjd.2, ?_⟩
  intro y hy
  exact mem_centralizer_iff.1
    (subsystemGroup_le_centralizer_thetaSL2 hK2 (su6Levi_le_subsystemGroup σ hy)) j hjJ

theorem centralizer_nonsplit_twistedE6 (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    {X : Subgroup (ModGL TwistTag.E6.tag K)} (hXJ : X ≤ thetaRankOneGroup (algebraMap k K))
    (hX : Nat.card X = 2 ^ f + 1) (hcyc : IsCyclic X) :
    centralizer (X : Set (ModGL TwistTag.E6.tag K)) ⊓ graphFixedRootGroup TwistTag.E6 K σ =
        X ⊔ su6Levi σ ∧
      Disjoint X (su6Levi σ) ∧ X ≤ centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) ∧
      X ≤ graphFixedRootGroup TwistTag.E6 K σ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Finite K := finite_of_card hK
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨hLX, -, -, -, -, -, -⟩ := su6Levi_facts hf hk hK hσ
  have hXC : X ≤ graphFixedRootGroup TwistTag.E6 K σ :=
    hXJ.trans (thetaRankOneGroup_le_C0 hf hk hK hσ)
  have hXL : X ≤ centralizer (su6Levi σ : Set (ModGL TwistTag.E6.tag K)) := fun y hy =>
    mem_centralizer_iff.2 fun l hl => (mem_centralizer_iff.1 (hLX hl) y (hXJ hy)).symm
  have hdisj : Disjoint X (su6Levi σ) :=
    (disjoint_range_thetaSL2_subsystemGroup hK2).mono
      (hXJ.trans (thetaRankOneGroup_le_range hK2 _)) (su6Levi_le_subsystemGroup σ)
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (le_inf ?_ hXC)
    (le_inf (fun l hl => mem_centralizer_iff.2 fun y hy =>
      (mem_centralizer_iff.1 (hXL hy) l hl).symm) (su6Levi_le_graphFixedRootGroup σ))),
    hdisj, hXL, hXC⟩
  swap
  · obtain ⟨x, -, rfl⟩ := exists_eq_zpowers_of_isCyclic hcyc
    exact zpowers_le_centralizer_zpowers x
  obtain ⟨hgc, hgC⟩ := mem_inf.1 hg
  obtain ⟨x, hxX, rfl⟩ := exists_eq_zpowers_of_isCyclic hcyc
  have hgx : g * x = x * g := (mem_centralizer_iff.1 hgc x (mem_zpowers x)).symm
  have hxJ := hXJ (mem_zpowers x)
  rw [thetaRankOneGroup_eq_range hK2] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρdef
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  have hA : orderOf A = Nat.card k + 1 := by
    rw [← orderOf_injective _ hρinj A, ← Nat.card_zpowers, hX, hk]
  obtain ⟨l, P, hl1, hlq, hP⟩ :=
    exists_inv_mul_map_mul_eq_HSL_of_finrank (finrank_eq_two hf hk hK) hA
  have hl3 : 3 ≤ orderOf l := by
    have hdvd : orderOf l ∣ 2 ^ f + 1 := orderOf_dvd_of_pow_eq_one (by rw [← hk]; exact hlq)
    have hpos : 0 < orderOf l := Nat.pos_of_dvd_of_pos hdvd (by positivity)
    have hne1 : orderOf l ≠ 1 := fun h => hl1 (orderOf_eq_one_iff.1 h)
    have hne2 : orderOf l ≠ 2 := fun h => by
      rw [h] at hdvd
      have h2f : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      have := (Nat.dvd_add_right h2f).1 hdvd
      omega
    omega
  have hconj : (thetaSL2 K P)⁻¹ * ρ A * thetaSL2 K P =
      rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 l) := by
    rw [hρdef, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, hP, thetaSL2_HSL]
  obtain ⟨j, d, hjJ, hdD, hg2, hFj, -, -⟩ :=
    exists_mul_su6Levi_of_conj_highDiag hf hk hK hσ hl3 hconj hgx hgC
  obtain ⟨B, hB⟩ := hjJ
  have hσB : Matrix.SpecialLinearGroup.map σ B = B :=
    thetaSL2_injective hK2 (by rw [← twistHom_thetaSL2 hK2, hB, hFj])
  obtain ⟨B₀, rfl⟩ :=
    F4Pilot.exists_map_eq_of_map_eq (algebraMap k K) σ (sigma_eq_self_iff hk hσ) B hσB
  have hdx : Commute d (ρ A) :=
    (mem_centralizer_iff.1 (hLX hdD) (ρ A) (hXJ (mem_zpowers _))).symm
  have hjx : Commute (ρ B₀) (ρ A) := by
    have e : ρ B₀ = g * d⁻¹ := by
      rw [hρdef, MonoidHom.comp_apply, hB, hg2, mul_inv_cancel_right]
    rw [e]
    exact Commute.mul_left hgx hdx.inv_left
  have hBA : B₀ ∈ centralizer {A} := by
    rw [mem_centralizer_singleton_iff]
    apply hρinj
    rw [map_mul, map_mul]
    exact hjx.eq
  rw [F4Pilot.centralizer_eq_zpowers_of_orderOf_eq hA] at hBA
  obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hBA
  rw [hg2]
  refine mul_mem_sup ?_ hdD
  rw [← hB]
  exact mem_zpowers_iff.2 ⟨m, (map_zpow ρ A m).symm⟩

theorem inner_on_su6Levi_of_commute_order_three (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (h3dvd : 3 ∣ 2 ^ f + 1) {x : ModGL TwistTag.E6.tag K}
    (hxJ : x ∈ thetaRankOneGroup (algebraMap k K)) (hx3 : orderOf x = 3)
    {g : ModGL TwistTag.E6.tag K} (hgC : g ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (hgx : g * x = x * g) :
    ∃ d ∈ su6Levi σ, ∀ y ∈ su6Levi σ,
      g * y * g⁻¹ = d * y * d⁻¹ := by
  have : Finite K := finite_of_card hK
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have h3K : 3 ∣ Nat.card K - 1 := by
    rw [hK]
    have hq1 : 2 ^ f + 1 ≡ 0 [MOD 3] := Nat.modEq_zero_iff_dvd.mpr h3dvd
    have hq2 : 2 ^ f ≡ 2 [MOD 3] := by
      have h3' : 2 + 1 ≡ 0 [MOD 3] := by norm_num [Nat.ModEq]
      exact Nat.ModEq.add_right_cancel' 1 (hq1.trans h3'.symm)
    have hq2sq : (2 ^ f) ^ 2 ≡ 1 [MOD 3] := by
      have h := Nat.ModEq.pow 2 hq2
      have h4 : (2 ^ 2 : ℕ) ≡ 1 [MOD 3] := by norm_num [Nat.ModEq]
      exact h.trans h4
    exact hq2sq.symm.dvd'
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K)) with hρdef
  have hρinj : Function.Injective ρ := injective_thetaSL2_comp_map hK2 (algebraMap k K)
  rw [thetaRankOneGroup_eq_range hK2] at hxJ
  obtain ⟨A, rfl⟩ := hxJ
  have hA : orderOf A = 3 := by
    rw [← orderOf_injective _ hρinj A]
    exact hx3
  obtain ⟨l, P, hl3, hP⟩ :=
    exists_inv_mul_map_mul_eq_HSL_of_orderOf_eq_three (K := K) h3K hA
  have hconj : (thetaSL2 K P)⁻¹ * ρ A * thetaSL2 K P =
      rootDiagUnit TwistTag.E6.tag (EPilot.highDiag .E6 l) := by
    rw [hρdef, MonoidHom.comp_apply, ← map_inv, ← map_mul, ← map_mul, hP, thetaSL2_HSL]
  obtain ⟨j, d, -, hdD, hg2, -, -, hjcomm⟩ :=
    exists_mul_su6Levi_of_conj_highDiag hf hk hK hσ hl3.symm.le hconj hgx hgC
  refine ⟨d, hdD, fun y hy => ?_⟩
  have hcomm : j * (d * y * d⁻¹) = (d * y * d⁻¹) * j :=
    hjcomm _ (mul_mem (mul_mem hdD hy) (inv_mem hdD))
  calc g * y * g⁻¹ = (j * d) * y * (j * d)⁻¹ := by rw [hg2]
    _ = j * (d * y * d⁻¹) * j⁻¹ := by group
    _ = (d * y * d⁻¹) * j * j⁻¹ := by rw [hcomm]
    _ = d * y * d⁻¹ := by group

theorem exists_nonsplit_le_thetaRankOneGroup (hf : 1 ≤ f) (hk : Nat.card k = 2 ^ f)
    (hK : Nat.card K = (2 ^ f) ^ 2) :
    ∃ X : Subgroup (ModGL TwistTag.E6.tag K), X ≤ thetaRankOneGroup (algebraMap k K) ∧
      IsCyclic X ∧ Nat.card X = 2 ^ f + 1 := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have hk2 : (2 : k) = 0 := two_eq_zero_of_card hf hk
  have hK2 : (2 : K) = 0 := two_eq_zero_of_card_sq hf hK
  have : CharP k 2 := CharTwo.of_one_ne_zero_of_two_eq_zero one_ne_zero hk2
  obtain ⟨A, hA⟩ := F4Pilot.exists_orderOf_eq_natCard_add_one (K := k)
  set ρ := (thetaSL2 K).comp (Matrix.SpecialLinearGroup.map (algebraMap k K))
  refine ⟨zpowers (ρ A), ?_, isCyclic_zpowers _, ?_⟩
  · rw [zpowers_le, thetaRankOneGroup_eq_range hK2]
    exact ⟨A, rfl⟩
  · rw [Nat.card_zpowers, orderOf_injective _ (injective_thetaSL2_comp_map hK2 _), hA, hk]

end Nonsplit

end CFSG.SeitzReduction.TwistedE6Pilot
