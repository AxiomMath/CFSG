module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange

public section

namespace CFSG.ComponentClassification.UnbalancedCorr

open Subgroup

theorem map_conjugate {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (K : Subgroup X) (g : X) :
    (conjugate K g).map f = conjugate (K.map f) (f g) := by
  ext y
  rw [UnbalancedLayer.mem_conjugate_iff, mem_map, mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [UnbalancedLayer.mem_conjugate_iff] at hx
    exact ⟨g * x * g⁻¹, hx, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨k, hk, hky⟩
    refine ⟨g⁻¹ * k * g, ?_, ?_⟩
    · rw [UnbalancedLayer.mem_conjugate_iff]
      rwa [show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
    · rw [map_mul, map_mul, map_inv, hky]
      group

theorem card_center_quotient_le {Q : Type*} [Group Q] [Finite Q] {T U : Subgroup Q}
    (hTU : T ≤ U) (hU : Group.IsPerfect U) :
    Nat.card (T ⧸ center T) ≤ Nat.card (U ⧸ center U) ∧
      (Nat.card (T ⧸ center T) = Nat.card (U ⧸ center U) → T = U) := by
  let f : T →* U ⧸ center U := (QuotientGroup.mk' (center U)).comp (inclusion hTU)
  have hker : f.ker ≤ center T := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx' : inclusion hTU x ∈ center U := (QuotientGroup.eq_one_iff _).mp hx
    rw [mem_center_iff] at hx' ⊢
    intro y
    have h := congrArg Subtype.val (hx' (inclusion hTU y))
    exact Subtype.ext h
  have h1 : Nat.card (T ⧸ center T) ≤ Nat.card f.range := by
    rw [← index_eq_card, ← index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero (index_ne_zero_of_finite)) (index_dvd_of_le hker)
  have h2 : Nat.card f.range ≤ Nat.card (U ⧸ center U) := card_le_card_group f.range
  refine ⟨h1.trans h2, fun heq => ?_⟩
  have hrange : f.range = ⊤ := by
    apply eq_top_of_card_eq
    exact le_antisymm h2 (heq ▸ h1)
  have hsup : T.subgroupOf U ⊔ center U = ⊤ := by
    rw [eq_top_iff]
    intro u _
    obtain ⟨t, ht⟩ : ∃ t, f t = (u : U ⧸ center U) := by
      rw [← MonoidHom.mem_range, hrange]
      exact mem_top _
    have hz : (inclusion hTU t)⁻¹ * u ∈ center U := QuotientGroup.eq.mp ht
    have : u = inclusion hTU t * ((inclusion hTU t)⁻¹ * u) := by group
    rw [this]
    exact mul_mem (mem_sup_left (show inclusion hTU t ∈ T.subgroupOf U from t.2))
      (mem_sup_right hz)
  have hZc : ⁅(⊤ : Subgroup U), center U⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_center_left _
  have hTn : (T.subgroupOf U).Normal := by
    rw [← normalizer_eq_top_iff, eq_top_iff, ← hsup]
    exact sup_le le_normalizer (center_le_normalizer _)
  have hcomm : commutator U ≤ T.subgroupOf U := by
    rw [_root_.commutator_def]
    calc ⁅(⊤ : Subgroup U), ⊤⁆ = ⁅⊤, T.subgroupOf U ⊔ center U⁆ := by rw [hsup]
      _ = ⁅⊤, T.subgroupOf U⁆ ⊔ ⁅⊤, center U⁆ := commutator_sup_left _ _ _
      _ = ⁅⊤, T.subgroupOf U⁆ := by rw [hZc, sup_bot_eq]
      _ ≤ T.subgroupOf U := commutator_le_right _ _
  rw [hU.commutator_eq_top] at hcomm
  apply le_antisymm hTU
  intro u hu
  exact hcomm (mem_top (⟨u, hu⟩ : U))

theorem commutator_zpowers_eq_of_not_centralizes {Q : Type*} [Group Q] {A : Subgroup Q} {t : Q}
    (hA : IsQuasisimple A) (hAU : A ⊔ conjugate A t ≤ normalizer (A : Set Q))
    (ht : t ∈ normalizer ((A ⊔ conjugate A t : Subgroup Q) : Set Q))
    (hU : ⁅A ⊔ conjugate A t, A ⊔ conjugate A t⁆ = A ⊔ conjugate A t)
    (hnc : ¬ ∀ u ∈ A ⊔ conjugate A t, u * t = t * u) :
    ⁅A ⊔ conjugate A t, zpowers t⁆ = A ⊔ conjugate A t := by
  set U := A ⊔ conjugate A t with hUdef
  set W := ⁅U, zpowers t⁆ with hWdef
  have htU : zpowers t ≤ normalizer (U : Set Q) := zpowers_le.mpr ht
  have hWU : W ≤ U := UnbalancedLayer.commutator_le_left_of_le_normalizer htU
  have hUW : U ≤ normalizer (W : Set Q) := normalizer_commutator_ge_left U (zpowers t)
  have htW : t ∈ normalizer (W : Set Q) :=
    normalizer_commutator_ge_right U (zpowers t) (mem_zpowers t)
  have hAU' : A ≤ U := le_sup_left
  have hWA : W ≤ normalizer (A : Set Q) := hWU.trans hAU
  have hD : ⁅A, W⁆ ≤ A := UnbalancedLayer.commutator_le_left_of_le_normalizer hWA
  have hDn : ((⁅A, W⁆ : Subgroup Q).subgroupOf A).Normal :=
    (normal_subgroupOf_iff_le_normalizer hD).mpr (normalizer_commutator_ge_left A W)
  rcases LocalCores.quasisimple_normal_subgroups hA hDn with htop | hcen
  ·
    have hDA : ⁅A, W⁆ = A := le_antisymm hD (subgroupOf_eq_top.mp htop)
    have hAW : A ≤ W := by
      rw [← hDA, commutator_comm]
      exact UnbalancedLayer.commutator_le_left_of_le_normalizer (hAU'.trans hUW)
    have hAtW : conjugate A t ≤ W := by
      rw [← UnbalancedLayer.conjugate_eq_of_mem_normalizer htW]
      exact map_mono hAW
    exact le_antisymm hWU (sup_le hAW hAtW)
  · exfalso
    have hD1 : ⁅A, W⁆ = ⊥ := by
      apply LocalCores.perfect_double_commutator hA.1
      rw [commutator_eq_bot_iff_le_centralizer]
      intro x hx
      rw [mem_centralizer_iff]
      intro y hy
      have hxc := hcen (show (⟨x, hD hx⟩ : A) ∈ (⁅A, W⁆ : Subgroup Q).subgroupOf A from hx)
      exact congrArg Subtype.val (mem_center_iff.mp hxc ⟨y, hy⟩)
    have hWcA : ∀ w ∈ W, ∀ u ∈ A, u * w = w * u := by
      intro w hw u hu
      have h1 := commutator_mem_commutator hu hw
      rw [hD1, mem_bot] at h1
      exact commutatorElement_eq_one_iff_mul_comm.mp h1
    have hWcAt : ∀ w ∈ W, ∀ u ∈ conjugate A t, u * w = w * u := by
      intro w hw u hu
      rw [UnbalancedLayer.mem_conjugate_iff] at hu
      have hw' : t * w * t⁻¹ ∈ W := (mem_normalizer_iff.mp htW w).mp hw
      have h1 := hWcA _ hw' _ hu
      calc u * w = t⁻¹ * ((t * u * t⁻¹) * (t * w * t⁻¹)) * t := by group
        _ = t⁻¹ * ((t * w * t⁻¹) * (t * u * t⁻¹)) * t := by rw [h1]
        _ = w * u := by group
    have hWcU : U ≤ centralizer (W : Set Q) := by
      refine sup_le (fun u hu => ?_) (fun u hu => ?_)
      · rw [mem_centralizer_iff]
        intro w hw
        exact (hWcA w hw u hu).symm
      · rw [mem_centralizer_iff]
        intro w hw
        exact (hWcAt w hw u hu).symm
    have hcW : ∀ u ∈ U, u * t * u⁻¹ * t⁻¹ ∈ W := fun u hu =>
      commutator_mem_commutator hu (mem_zpowers t)
    have hcZ : ∀ u : U, (⟨u * t * u⁻¹ * t⁻¹, hWU (hcW u u.2)⟩ : U) ∈ center U := by
      intro u
      rw [mem_center_iff]
      intro v
      have h := (mem_centralizer_iff.mp (hWcU v.2) _ (hcW u u.2)).symm
      exact Subtype.ext h
    let c : U →* center U :=
      { toFun := fun u => ⟨⟨u * t * u⁻¹ * t⁻¹, hWU (hcW u u.2)⟩, hcZ u⟩
        map_one' := by
          apply Subtype.ext
          apply Subtype.ext
          show (1 : Q) * t * (1 : Q)⁻¹ * t⁻¹ = 1
          group
        map_mul' := by
          intro u v
          apply Subtype.ext
          apply Subtype.ext
          show (u : Q) * v * t * ((u : Q) * v)⁻¹ * t⁻¹ =
            ((u : Q) * t * (u : Q)⁻¹ * t⁻¹) * ((v : Q) * t * (v : Q)⁻¹ * t⁻¹)
          have hv : (v : Q) * t * (v : Q)⁻¹ * t⁻¹ * u = u * ((v : Q) * t * (v : Q)⁻¹ * t⁻¹) :=
            mem_centralizer_iff.mp (hWcU u.2) _ (hcW v v.2)
          calc (u : Q) * v * t * ((u : Q) * v)⁻¹ * t⁻¹
              = u * ((v : Q) * t * (v : Q)⁻¹ * t⁻¹) * t * (u : Q)⁻¹ * t⁻¹ := by group
            _ = (v : Q) * t * (v : Q)⁻¹ * t⁻¹ * u * t * (u : Q)⁻¹ * t⁻¹ := by rw [← hv]
            _ = ((v : Q) * t * (v : Q)⁻¹ * t⁻¹) * ((u : Q) * t * (u : Q)⁻¹ * t⁻¹) := by group
            _ = ((u : Q) * t * (u : Q)⁻¹ * t⁻¹) * ((v : Q) * t * (v : Q)⁻¹ * t⁻¹) :=
              mem_centralizer_iff.mp (hWcU (hWU (hcW u u.2))) _ (hcW v v.2) }
    have hker : commutator U ≤ c.ker := Abelianization.commutator_subset_ker c
    have hperf : commutator U = ⊤ := by
      apply map_injective U.subtype_injective
      rw [map_subtype_commutator, hU, ← MonoidHom.range_eq_map, range_subtype]
    apply hnc
    intro u hu
    have h1 : c ⟨u, hu⟩ = 1 := by
      rw [← MonoidHom.mem_ker]
      apply hker
      rw [hperf]
      exact mem_top _
    have h3 : u * t * u⁻¹ * t⁻¹ = 1 := congrArg (fun z : center U => ((z : U) : Q)) h1
    calc u * t = (u * t * u⁻¹ * t⁻¹) * t * u := by group
      _ = t * u := by rw [h3, one_mul]

theorem card_centerQuotient_pPrimeCore_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card ((X ⧸ pPrimeCore 2 X) ⧸ center (X ⧸ pPrimeCore 2 X)) =
      Nat.card ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) := by
  obtain ⟨f, -⟩ := exists_centerQuotient_congr
    (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 e)
  exact Nat.card_congr f.toEquiv

variable {G : Type*} [Group G] [Finite G]

theorem card_centerQuotient_eq_of_subnormal {X H : Subgroup G} (hXH : X ≤ H)
    (hX : (X.subgroupOf H).IsSubnormal) :
    Nat.card ((↥X ⧸ pPrimeCore 2 ↥X) ⧸ center (↥X ⧸ pPrimeCore 2 ↥X)) =
      Nat.card (↥((X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H))) ⧸
        center ↥((X.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore 2 ↥H)))) := by
  obtain ⟨e, -⟩ := exists_restriction_quotient_equiv_of_subnormal hXH hX
  obtain ⟨f, -⟩ := exists_centerQuotient_congr e
  exact Nat.card_congr f.toEquiv

end CFSG.ComponentClassification.UnbalancedCorr
