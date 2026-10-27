module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf43HsStab

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

theorem not_mem_oddCoreOf_of_sq {T : Type} [Group T] [Finite T] (X : Subgroup T) {x : T}
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x ∉ oddCoreOf X := by
  intro hx
  refine hx1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard X) hx ?_)
  exact IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1, pow_one])

section RestrictAux

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

private theorem subgroupOf_mem_aStar_restrict_aux (hΩ : HypOmegaGen Ω) {K Y : Subgroup G}
    (hY : ∀ M ∈ aStar Ω K, M ≤ Y) {L : Subgroup G} (hL : L ∈ aStar Ω K) :
    L.subgroupOf Y ∈ aStar (restrictFamily Ω Y) (K.subgroupOf Y) := by
  induction hL with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    rename_i b c
    have hbY : b ≤ Y := hY b hab
    have hcY : c ≤ Y := hY c (hab.tail hbc)
    refine ih.tail ?_
    obtain ⟨hcΩ, hA | hA | ⟨htw, hne⟩⟩ := hbc
    · obtain ⟨zb, zc, hv⟩ := hA
      exact ⟨subgroupOf_mem_restrictFamily hcΩ hcY,
        Or.inl ⟨_, _, aViol_restrict_gen hΩ hbY hcY hv⟩⟩
    · obtain ⟨zc, zb, hv⟩ := hA
      exact ⟨subgroupOf_mem_restrictFamily hcΩ hcY,
        Or.inr (Or.inl ⟨_, _, aViol_restrict_gen hΩ hcY hbY hv⟩)⟩
    · exact ⟨subgroupOf_mem_restrictFamily hcΩ hcY,
        Or.inr (Or.inr ⟨twinSet_subgroupOf hbY hcY htw, subgroupOf_ne_of_ne hbY hcY hne⟩)⟩

omit [Finite G] in
private theorem commutator_le_sup_inf_of_subgroupOf_aux {Y A B : Subgroup G} (hA : A ≤ Y)
    (hB : B ≤ Y)
    (h : ⁅A.subgroupOf Y, B.subgroupOf Y⁆ ≤
      (oddCoreOf (A.subgroupOf Y) ⊔ classicalInvolutionOddCore ↥Y) ⊓
        (oddCoreOf (B.subgroupOf Y) ⊔ classicalInvolutionOddCore ↥Y)) :
    ⁅A, B⁆ ≤ (oddCoreOf A ⊔ oddCoreOf Y) ⊓ (oddCoreOf B ⊔ oddCoreOf Y) := by
  have h1 := Subgroup.map_mono (f := Y.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB] at h1
  refine h1.trans ((Subgroup.map_inf_le _ _ _).trans ?_)
  rw [Subgroup.map_sup, Subgroup.map_sup, oddCoreOf_subgroupOf hA, oddCoreOf_subgroupOf hB,
    Subgroup.map_subgroupOf_eq_of_le ((oddCoreOf_le_self A).trans hA),
    Subgroup.map_subgroupOf_eq_of_le ((oddCoreOf_le_self B).trans hB)]
  exact le_rfl

end RestrictAux

namespace FrameCfg

variable {T : Type} [Group T] [Finite T] {K : Subgroup T} {z : T} {J : Subgroup T} {zJ : T}
  {S : Subgroup T}

private theorem thm3Quot_sigmaGen_aux (cfg : FrameCfg K z J zJ S) :
    Thm3A.Thm3RGroupQuotG ↥(sigmaGen K) ∧
      TypeRHyp (restrictFamily (CoreAssembly.conjClass K) (sigmaGen K)) ∧
      K.subgroupOf (sigmaGen K) ∈ restrictFamily (CoreAssembly.conjClass K) (sigmaGen K) ∧
      ¬ AEmpty (restrictFamily (CoreAssembly.conjClass K) (sigmaGen K))
        (K.subgroupOf (sigmaGen K)) := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKH : K ≤ sigmaGen K := le_omegaGen (Relation.ReflTransGen.refl : K ∈ sigmaOf K)
  have hJA : J ∈ aStar (CoreAssembly.conjClass K) K :=
    Relation.ReflTransGen.single ⟨cfg.viol.mem, Or.inl ⟨z, zJ, cfg.viol⟩⟩
  have hJH : J ≤ sigmaGen K := le_omegaGen (aStar_subset_dstarComp_gen hΩg hK hJA).2
  have hHtop : sigmaGen K ≠ ⊤ := sigmaGen_ne_top hΩg.conjInvariant cfg.sigma_ne
  have hlt : Nat.card ↥(sigmaGen K) < Nat.card T :=
    lt_of_le_of_ne (Subgroup.card_le_card_group _)
      (fun h => hHtop ((Subgroup.card_eq_iff_eq_top _).mp h))
  exact ⟨Thm3A.thm3RGroupQuotG_of_belowG cfg.below hlt,
    (typeRHyp_of_datum cfg.datum).restrict (sigmaGen K), subgroupOf_mem_restrictFamily hK hKH,
    not_aEmpty_iff.mpr ⟨J.subgroupOf (sigmaGen K), _, _, aViol_restrict_gen hΩg hKH hJH cfg.viol⟩⟩

theorem mem_sigmaOf_of_le (cfg : FrameCfg K z J zJ S) {L : Subgroup T}
    (hL : L ∈ CoreAssembly.conjClass K) (hLH : L ≤ sigmaGen K) : L ∈ sigmaOf K := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKH : K ≤ sigmaGen K := le_omegaGen (Relation.ReflTransGen.refl : K ∈ sigmaOf K)
  obtain ⟨hQ, hΦ, hKΦ, hnA⟩ := cfg.thm3Quot_sigmaGen_aux
  by_cases hLA : L.subgroupOf (sigmaGen K) ∈
      aStar (restrictFamily (CoreAssembly.conjClass K) (sigmaGen K)) (K.subgroupOf (sigmaGen K))
  · have h1 := mem_aStar_of_restrict_gen hΩg hKH hLA
    rw [Subgroup.map_subgroupOf_eq_of_le hLH] at h1
    exact (aStar_subset_dstarComp_gen hΩg hK h1).2
  ·
    obtain ⟨R, hR, hRL, -⟩ := exists_mem_RSet_ge hL (isPGroup_two_bot' (G := T)) bot_le
    obtain ⟨n, -, hRn, hKn⟩ := (Thm3A.thm3R_lift_stab hQ hΦ hKΦ hnA
      (subgroupOf_mem_restrictFamily hL hLH) hLA Relation.ReflTransGen.refl).2 _
      (hRL.subgroupOf hLH)
    rw [conjSub_subgroupOf] at hRn hKn
    have hKnH : conjSub (n : T) K ≤ sigmaGen K := by
      intro y hy
      rw [mem_conjSub_iff] at hy
      have h := (sigmaGen K).mul_mem ((sigmaGen K).mul_mem n.2 (hKH hy)) ((sigmaGen K).inv_mem n.2)
      simpa [mul_assoc] using h
    have hKnS : conjSub (n : T) K ∈ dstarComp (CoreAssembly.conjClass K) K := by
      have h1 := mem_aStar_of_restrict_gen hΩg hKH hKn
      rw [Subgroup.map_subgroupOf_eq_of_le hKnH] at h1
      exact (aStar_subset_dstarComp_gen hΩg hK h1).2
    have hRN : R ≤ Subgroup.normalizer (conjSub (n : T) K : Set T) := fun r hr =>
      (mem_normalizer_subgroupOf_iff (y := ⟨r, hLH (hRL.1 hr)⟩) hKnH).mpr
        (hRn (Subgroup.mem_subgroupOf.mpr hr))
    by_cases hLK : L = conjSub (n : T) K
    · rw [hLK]
      exact hKnS
    · exact hKnS.tail ⟨hL, Or.inl (omegaNbr_subset_omegaStarNbr_gen hΩg _
        ⟨hL, hLK, R, hR, hRL.1, hRN⟩)⟩

theorem sigmaNorm_le_sigmaStarNorm (cfg : FrameCfg K z J zJ S) :
    sigmaNorm K ≤ sigmaStarNorm (CoreAssembly.conjClass K) K := by
  have hΩ := cfg.datum.hyp.conjInvariant
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have key : ∀ n ∈ sigmaNorm K, ∀ M' ∈ sigmaOf K, conjSub n M' ∈ sigmaOf K := by
    intro n hn M' hM'
    have hM'Ω : M' ∈ CoreAssembly.conjClass K := (mem_dstarComp_symm hK hM').1
    refine cfg.mem_sigmaOf_of_le (hΩ n M' hM'Ω) ?_
    calc conjSub n M' ≤ conjSub n (sigmaGen K) := conjSub_mono (le_omegaGen hM')
      _ = sigmaGen K := mem_normalizer_iff_conjSub_eq.mp hn
  intro m hm
  rw [mem_sigmaStarNorm_iff]
  intro M'
  refine ⟨key m hm M', fun h => ?_⟩
  have := key m⁻¹ ((sigmaNorm K).inv_mem hm) _ h
  rw [conjSub_inv_conjSub] at this
  exact this

theorem conjSub_firstFactor_le (cfg : FrameCfg K z J zJ S) {m : T} (hm : m ∈ sigmaNorm K) :
    conjSub m (firstFactor K) ≤ sigmaGen K :=
  calc conjSub m (firstFactor K) ≤ conjSub m (sigmaGen K) := conjSub_mono cfg.ht_le
    _ = sigmaGen K := mem_normalizer_iff_conjSub_eq.mp hm

theorem sigmaGen_le_normalizer_conjSub_firstFactor (cfg : FrameCfg K z J zJ S) {m : T}
    (hm : m ∈ sigmaNorm K) :
    sigmaGen K ≤ Subgroup.normalizer (conjSub m (firstFactor K) : Set T) := by
  intro x hx
  have hx' : m⁻¹ * x * m ∈ sigmaGen K := by
    have h0 := mem_normalizer_iff_conjSub_eq.mp ((sigmaNorm K).inv_mem hm)
    have h1 : m⁻¹ * x * m⁻¹⁻¹ ∈ conjSub m⁻¹ (sigmaGen K) := conj_mem_conjSub hx
    rw [h0, inv_inv] at h1
    exact h1
  have h2 := mem_normalizer_iff_conjSub_eq.mp (cfg.hs_le_normalizer_ht hx')
  rw [mem_normalizer_iff_conjSub_eq, ← conjSub_mul]
  calc conjSub (x * m) (firstFactor K) = conjSub m (conjSub (m⁻¹ * x * m) (firstFactor K)) := by
        rw [← conjSub_mul]
        congr 1
        group
    _ = conjSub m (firstFactor K) := by rw [h2]

theorem oddCoreOf_firstFactor (cfg : FrameCfg K z J zJ S) :
    oddCoreOf (firstFactor K) = oddCoreOf (sigmaGen K) := by
  refine le_antisymm (Hall196.oddCoreOf_le_of_le_normalizer cfg.ht_le cfg.hs_le_normalizer_ht) ?_
  refine Sec6Gen.le_oddCoreOf_of_normal (le_sup_right : oddCoreOf (sigmaGen K) ≤ firstFactor K)
    (fun x hx => ?_) (oddCoreOf_odd_natCard _)
  exact mem_normalizer_iff_conjSub_eq.mpr
    (Asc77.T7V.conjSub_oddCoreOf_eq_of_mem_normalizer (Subgroup.le_normalizer (cfg.ht_le hx)))

theorem commutator_le_of_not_mem_aStar (cfg : FrameCfg K z J zJ S) {L L' : Subgroup T}
    (hL : L ∈ sigmaOf K) (hLA : L ∉ aStar (CoreAssembly.conjClass K) K)
    (hL' : L' ∈ aStar (CoreAssembly.conjClass K) K) :
    ⁅L, L'⁆ ≤ (oddCoreOf L ⊔ oddCoreOf (sigmaGen K)) ⊓ (oddCoreOf L' ⊔ oddCoreOf (sigmaGen K)) := by
  have hΩg : HypOmegaGen (CoreAssembly.conjClass K) := cfg.datum.hyp
  have hK : K ∈ CoreAssembly.conjClass K := CoreAssembly.mem_conjClass_self K
  have hKH : K ≤ sigmaGen K := le_omegaGen (Relation.ReflTransGen.refl : K ∈ sigmaOf K)
  have hLΩ : L ∈ CoreAssembly.conjClass K := (mem_dstarComp_symm hK hL).1
  have hLH : L ≤ sigmaGen K := le_omegaGen hL
  have hAH : ∀ M ∈ aStar (CoreAssembly.conjClass K) K, M ≤ sigmaGen K :=
    fun M hM => le_omegaGen (aStar_subset_dstarComp_gen hΩg hK hM).2
  have hL'H : L' ≤ sigmaGen K := hAH L' hL'
  obtain ⟨hQ, hΦ, hKΦ, hnA⟩ := cfg.thm3Quot_sigmaGen_aux
  have hLA' : L.subgroupOf (sigmaGen K) ∉
      aStar (restrictFamily (CoreAssembly.conjClass K) (sigmaGen K))
        (K.subgroupOf (sigmaGen K)) := by
    intro h
    have h1 := mem_aStar_of_restrict_gen hΩg hKH h
    rw [Subgroup.map_subgroupOf_eq_of_le hLH] at h1
    exact hLA h1
  exact commutator_le_sup_inf_of_subgroupOf_aux hLH hL'H
    (Thm3A.thm3R_comm_mod hQ hΦ hKΦ hnA (subgroupOf_mem_restrictFamily hLΩ hLH) hLA'
      (subgroupOf_mem_aStar_restrict_aux hΩg hAH hL'))

end FrameCfg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
