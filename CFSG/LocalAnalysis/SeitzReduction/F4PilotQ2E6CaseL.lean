module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6CaseNotDvd
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6CaseRoot
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotQ2E6XiExclusion
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLRows
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLProof

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.F4Pilot

open Subgroup CFSG.EvenSmallLie CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
open CFSG.LieType.Ree (ReeTag)
open CFSG.LieType.Chevalley.E6SecondGraphFixed (SecondGraphFixedSubgroup)
open CFSG.SeitzReduction.EPilot (normalizerQuotMulAut normalizerQuotMulAut_apply)
open CFSG.Quasithin (perfectCore)

section Generic

variable {G : Type*} [Group G]

theorem zpowers_eq_of_mem_of_card_prime [Finite G] {H : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hH : Nat.card H = p) {y : G} (hy : y ∈ H) (hy1 : y ≠ 1) : zpowers y = H := by
  have hle : zpowers y ≤ H := (zpowers_le).2 hy
  have h1 : orderOf y ∣ p := hH ▸ Subgroup.orderOf_dvd_natCard H hy
  have h2 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
  have h3 : orderOf y = p := ((Nat.dvd_prime hp).1 h1).resolve_left h2
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hH, Nat.card_zpowers, h3])

theorem centralizer_zpowers_coe_eq (y : G) :
    centralizer ((zpowers y : Subgroup G) : Set G) = centralizer ({y} : Set G) := by
  rw [zpowers_eq_closure, centralizer_closure]

theorem exists_perfect_pullback {M N : Subgroup G} (β : M ≃* N) {A : Subgroup G} (hAN : A ≤ N)
    (hA : ⁅A, A⁆ = A) (z : N) (hAz : A ≤ centralizer ({(z : G)} : Set G)) :
    ∃ P : Subgroup G, P ≤ M ∧ ⁅P, P⁆ = P ∧ Nat.card P = Nat.card A ∧
      P ≤ centralizer ({((β.symm z : M) : G)} : Set G) := by
  have : Group.IsPerfect A := Subgroup.isPerfect_iff.2 hA
  set γ : A →* G := M.subtype.comp (β.symm.toMonoidHom.comp (Subgroup.inclusion hAN)) with hγ
  have hγa : ∀ a : A, γ a = ((β.symm ⟨a, hAN a.2⟩ : M) : G) := fun a => rfl
  have hγinj : Function.Injective γ := by
    intro a b hab
    rw [hγa, hγa] at hab
    have h1 := β.symm.injective (Subtype.ext hab)
    have h2 := congrArg (fun y : N => (y : G)) h1
    exact Subtype.ext h2
  refine ⟨γ.range, ?_, commutator_monoidHom_range_eq_of_isPerfect γ,
    (Nat.card_congr (MonoidHom.ofInjective hγinj).toEquiv).symm, ?_⟩
  · rintro _ ⟨a, rfl⟩
    rw [hγa]
    exact (β.symm _).2
  · rintro _ ⟨a, rfl⟩
    rw [hγa, mem_centralizer_singleton_iff]
    have hc : (a : G) * z = z * a := mem_centralizer_singleton_iff.1 (hAz a.2)
    have hN : (⟨a, hAN a.2⟩ : N) * z = z * ⟨a, hAN a.2⟩ := Subtype.ext hc
    have h1 := congrArg (fun y : N => ((β.symm y : M) : G)) hN
    simp only [map_mul, Subgroup.coe_mul] at h1
    exact h1

end Generic

section Conj

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

theorem subgroupToG_map_mulAut_conj (e : L ≃* adjointGroup .F4 K)
    (H : Subgroup (adjointGroup .F4 K)) (d : adjointGroup .F4 K) :
    subgroupToG e (H.map (MulAut.conj d).toMonoidHom) =
      (subgroupToG e H).map (MulAut.conj ((e.symm d : L) : G)).toMonoidHom := by
  rw [subgroupToG, subgroupToG, Subgroup.map_map, Subgroup.map_map, Subgroup.map_map,
    Subgroup.map_map]
  congr 1
  ext h
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
    Subgroup.coe_subtype]

theorem centralizerPerfectCore_subgroupToG_map_conj [Finite G] (e : L ≃* adjointGroup .F4 K)
    (H : Subgroup (adjointGroup .F4 K)) (d : adjointGroup .F4 K) :
    centralizerPerfectCore (subgroupToG e (H.map (MulAut.conj d).toMonoidHom)) =
      (centralizerPerfectCore (subgroupToG e H)).map
        (MulAut.conj ((e.symm d : L) : G)).toMonoidHom := by
  rw [subgroupToG_map_mulAut_conj, map_centralizerPerfectCore]

theorem natCard_centralizerPerfectCore_subgroupToG_map_conj [Finite G]
    (e : L ≃* adjointGroup .F4 K) (H : Subgroup (adjointGroup .F4 K)) (d : adjointGroup .F4 K) :
    Nat.card (centralizerPerfectCore (subgroupToG e (H.map (MulAut.conj d).toMonoidHom))) =
      Nat.card (centralizerPerfectCore (subgroupToG e H)) := by
  rw [centralizerPerfectCore_subgroupToG_map_conj, card_map_of_injective (MulAut.conj _).injective]

theorem mem_subgroupToG_iff (e : L ≃* adjointGroup .F4 K) {H : Subgroup (adjointGroup .F4 K)}
    {x : G} (hx : x ∈ L) : x ∈ subgroupToG e H ↔ e ⟨x, hx⟩ ∈ H := by
  constructor
  · rintro ⟨l, ⟨h, hh, rfl⟩, rfl⟩
    change e ⟨((e.symm h : L) : G), hx⟩ ∈ H
    have e1 : (⟨((e.symm h : L) : G), hx⟩ : L) = e.symm h := Subtype.ext rfl
    rw [e1, MulEquiv.apply_symm_apply]
    exact hh
  · intro h
    refine ⟨⟨x, hx⟩, ⟨e ⟨x, hx⟩, h, ?_⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]

theorem natCard_subgroupToG (e : L ≃* adjointGroup .F4 K) (H : Subgroup (adjointGroup .F4 K)) :
    Nat.card (subgroupToG e H) = Nat.card H := by
  rw [subgroupToG, card_map_of_injective L.subtype_injective,
    card_map_of_injective e.symm.injective]

theorem subgroupToG_trans_symm_eq_map (e : L ≃* adjointGroup .F4 K)
    (φ : MulAut (adjointGroup .F4 K)) (H : Subgroup (adjointGroup .F4 K)) :
    subgroupToG (e.trans φ.symm) H = subgroupToG e (H.map φ.toMonoidHom) := by
  unfold subgroupToG
  congr 1
  rw [Subgroup.map_map]
  rfl

end Conj

section Lambda

theorem natCard_fixSubgroup_xi_E6_two {K' : Type} [Field K'] [Finite K'] (hK' : Nat.card K' = 2)
    {η : MulAut (adjointGroup TwistTag.E6.tag K')}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K', (η h : ModGL TwistTag.E6.tag K') =
      diagramMap TwistTag.E6 K' * h * (diagramMap TwistTag.E6 K')⁻¹)
    (hx : pinnedX TwistTag.E6.tag K' e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K') :
    Nat.card (E6Pilot.fixSubgroup (MulAut.conj (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K') * η)) =
      Nat.card (centralizer ({yRep K' .t} : Set (adjointGroup .F4 K'))) := by
  have hK1 : Nat.card K' = 2 ^ 1 := by rw [hK', pow_one]
  have := charP_two_of_natCard_eq_two_pow hK1
  have hM' : Nat.card (GaloisField 2 (2 * 1)) = (2 ^ 1) ^ 2 := by
    rw [GaloisField.card 2 (2 * 1) (by omega)]
    norm_num
  obtain ⟨ι⟩ := E6GraphFullCoset.nonempty_ringHom_of_card le_rfl hK1 hM'
  let _ : Algebra K' (GaloisField 2 (2 * 1)) := ι.toAlgebra
  have hσM : ∀ c : GaloisField 2 (2 * 1), iterateFrobenius (GaloisField 2 (2 * 1)) 2 1 c =
      c ^ 2 ^ 1 := fun c => iterateFrobenius_def (p := 2) 1 c
  obtain ⟨ht, -, -, -, ⟨eJ, -, heJ2, hsec⟩, -⟩ :=
    even_E6_twisted_E6_second_graph_fixed_subgroup 1 le_rfl K' (GaloisField 2 (2 * 1)) hK1 hM' _
      hσM
  obtain ⟨htJ, hcard⟩ := natCard_fixSubgroup_of_secondGraph hsec hη hx
  rw [hcard]
  obtain ⟨c, hcC, hc⟩ := exists_conj_e6FixedToF4_highRoot_eq_yRep_t ht
  have h1 : (⟨c, hcC⟩ : adjointGroup .F4 K') * eJ ⟨_, htJ⟩ * (⟨c, hcC⟩ : adjointGroup .F4 K')⁻¹ =
      yRep K' .t := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [heJ2 htJ]
    exact hc
  rw [← h1, natCard_centralizer_conj]

theorem natCard_centralizer_yRep_dvd_of_xi {G : Type} [Group G] [Finite G] {K : Type} [Field K]
    [Finite K] (hK : Nat.card K = 2) {M : Subgroup G} (hZM : Odd (Nat.card (center M)))
    (eM : M ⧸ center M ≃* adjointGroup TwistTag.E6.tag K) {t : G} (ht : orderOf t = 2)
    (htM : t ∈ normalizer (M : Set G)) {η : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hη : ∀ h : adjointGroup TwistTag.E6.tag K, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹)
    (hx : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag K)
    {φ : MulAut (adjointGroup TwistTag.E6.tag K)}
    (hφ : φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹ = MulAut.conj ⟨_, hx⟩ * η) :
    Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) ∣
      Nat.card (perfectCore (M ⊓ centralizer ({t} : Set G))) := by
  have hperfA := fixSubgroup_perfect_of_conj hφ (commutator_fixSubgroup_xi_E6_two hK hη hx)
  have hmapΛ := map_perfectCore_subgroupOf_centralizer_eq hZM eM ht htM hperfA
  have hfixmap := map_eqLocus_eq_of_conj hφ
  have hfixA : Nat.card (E6Pilot.fixSubgroup (normalizerQuotMulAut eM ⟨t, htM⟩)) =
      Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) := by
    rw [← card_map_of_injective (f := φ.toMonoidHom) φ.injective]
    change Nat.card (((normalizerQuotMulAut eM ⟨t, htM⟩).toMonoidHom.eqLocus
      (MonoidHom.id _)).map φ.toMonoidHom) = _
    rw [hfixmap]
    exact natCard_fixSubgroup_xi_E6_two hK hη hx
  rw [← map_subtype_perfectCore_subgroupOf M t, card_map_of_injective M.subtype_injective,
    ← hfixA, ← hmapΛ]
  exact natCard_map_dvd _ _

theorem exists_yRep_of_le_of_dvd {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type}
    [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {w : G} (hwL : w ∈ L) (hw1 : w ≠ 1) {Λ : Subgroup G}
    (hΛL : Λ ≤ L) (hΛw : Λ ≤ centralizer ({w} : Set G))
    (hdvd : Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) ∣ Nat.card Λ) :
    ∃ (κ : TwoCentral) (c₁ : adjointGroup .F4 K), κ ≠ .tu ∧ c₁ * e ⟨w, hwL⟩ * c₁⁻¹ = yRep K κ ∧
      Λ = L ⊓ centralizer ({w} : Set G) ∧
      Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) =
        Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) := by
  have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  have hK1 : Nat.card K = 2 ^ 1 := by rw [hK, pow_one]
  set P3 := ((2 ^ 1) ^ 2 - 1) * ((2 ^ 1) ^ 4 - 1) * ((2 ^ 1) ^ 6 - 1) with hP3
  have hCt : Nat.card (centralizer ({yRep K .t} : Set (adjointGroup .F4 K))) =
      (2 ^ 1) ^ 24 * P3 := natCard_centralizer_yRep_of_ne_tu le_rfl hK1 (by decide)
  have hdvd' : (2 ^ 1) ^ 24 * P3 ∣ Nat.card Λ := by rw [← hCt]; exact hdvd
  have hLcard : Nat.card L = 2 ^ (24 * 1) *
      (((2 ^ 1) ^ 12 - 1) * ((2 ^ 1) ^ 8 - 1) * ((2 ^ 1) ^ 6 - 1) * ((2 ^ 1) ^ 2 - 1)) := by
    rw [Nat.card_congr e.toEquiv, natCard_adjointGroup_F4_eq hK1]
  have h2dvd : 2 ^ (24 * 1) ∣ Nat.card Λ := (Dvd.intro P3 rfl).trans hdvd'
  obtain ⟨U, hUΛ, hUcard⟩ :=
    exists_le_natCard_eq_two_pow hΛL (odd_ordF4_oddPart le_rfl) hLcard h2dvd
  set wL : L := ⟨w, hwL⟩ with hwLdef
  have hwL1 : wL ≠ 1 := fun h => hw1 (congrArg Subtype.val h)
  set UL : Subgroup L := U.subgroupOf L with hULdef
  have hUL : Nat.card UL = 2 ^ (24 * 1) := by
    rw [hULdef, card_subgroupOf_of_le (hUΛ.trans hΛL), hUcard]
  have hwUL : wL ∈ centralizer (UL : Set L) := by
    rw [mem_centralizer_iff]
    intro u hu
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hΛw (hUΛ (mem_subgroupOf.1 hu))))
  have hcardCL : Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) =
      Nat.card (centralizer ({e wL} : Set (adjointGroup .F4 K))) := by
    have h1 : (L ⊓ centralizer ({w} : Set G) : Subgroup G) =
        ((centralizer ({wL} : Set L)).map e.toMonoidHom).map (L.subtype.comp
          e.symm.toMonoidHom) := by
      rw [map_map]
      ext g
      simp only [mem_inf, mem_map, mem_centralizer_singleton_iff, MonoidHom.comp_apply,
        MulEquiv.coe_toMonoidHom, coe_subtype]
      constructor
      · rintro ⟨hgL, hgw⟩
        refine ⟨⟨g, hgL⟩, Subtype.ext hgw, ?_⟩
        rw [MulEquiv.symm_apply_apply]
      · rintro ⟨y, hy, rfl⟩
        rw [MulEquiv.symm_apply_apply]
        exact ⟨y.2, congrArg Subtype.val hy⟩
    have h2 : (centralizer ({wL} : Set L)).map e.toMonoidHom =
        centralizer ({e wL} : Set (adjointGroup .F4 K)) := by
      ext y
      simp only [mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom]
      constructor
      · rintro ⟨z, hz, rfl⟩
        rw [← map_mul, ← map_mul, hz]
      · intro hy
        exact ⟨e.symm y, e.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy]),
          MulEquiv.apply_symm_apply e y⟩
    have hinj : Function.Injective (L.subtype.comp e.symm.toMonoidHom) := fun a b hab =>
      e.symm.injective (L.subtype_injective hab)
    rw [h1, card_map_of_injective hinj, h2]
  have hUe : Nat.card (UL.map e.toMonoidHom) = 2 ^ (24 * 1) := by
    rw [card_map_of_injective e.injective, hUL]
  have hxP : e wL ∈ centralizer (((sylowOfCardF4 le_rfl hK1 (UL.map e.toMonoidHom) hUe :
      Sylow 2 (adjointGroup .F4 K)) : Subgroup (adjointGroup .F4 K)) :
        Set (adjointGroup .F4 K)) := by
    rw [coe_sylowOfCardF4, mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_mul, ← map_mul, mem_centralizer_iff.1 hwUL u hu]
  obtain ⟨κ, c₁, hc₁⟩ :=
    factF2 _ (e wL) hxP (fun h => hwL1 (e.injective (h.trans (map_one e).symm)))
  have hdivCL : (2 ^ 1) ^ 24 * P3 ∣ Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) :=
    hdvd'.trans (Subgroup.card_dvd_of_le (le_inf hΛL hΛw))
  have hκ : κ ≠ .tu := by
    rintro rfl
    apply not_dvd_natCard_centralizer_yRep_tu le_rfl hK1 hK1 (κ := .t) (by decide)
    rw [natCard_centralizer_yRep_of_ne_tu le_rfl hK1 (by decide), ← hc₁, natCard_centralizer_conj,
      ← hcardCL]
    exact hdivCL
  have hCκ : Nat.card (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) = (2 ^ 1) ^ 24 * P3 :=
    natCard_centralizer_yRep_of_ne_tu le_rfl hK1 hκ
  have hCL : Nat.card (L ⊓ centralizer ({w} : Set G) : Subgroup G) = (2 ^ 1) ^ 24 * P3 := by
    rw [hcardCL, ← natCard_centralizer_conj c₁, hc₁, hCκ]
  refine ⟨κ, c₁, hκ, hc₁, Subgroup.eq_of_le_of_card_ge (le_inf hΛL hΛw) ?_, by rw [hCL, hCκ]⟩
  rw [hCL]
  exact Nat.le_of_dvd Nat.card_pos hdvd'

end Lambda

section Endgame

theorem eq_one_of_le_map_conj_of_commute {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2)
    (e : L ≃* adjointGroup .F4 K) {t : G} (htC : t ∈ centralizer (L : Set G))
    {X₀ : Subgroup (adjointGroup .F4 K)}
    (hXJ : X₀ ≤ (highestRootRankOne K).subgroupOf (adjointGroup .F4 K)) (hcyc : IsCyclic X₀)
    (hX₀ : Nat.card X₀ = 3) {M : Subgroup G} (d : adjointGroup .F4 K)
    (hEM : (centralizerPerfectCore (subgroupToG e X₀)).map
      (MulAut.conj ((e.symm d : L) : G)).toMonoidHom ≤ M)
    {w : G} (hwL : w ∈ L) (hww : w * w = 1)
    (hwc : ∀ c ∈ M ⊓ centralizer ({t} : Set G), c * w = w * c)
    (hwX : ∀ x ∈ X₀, e ⟨w, hwL⟩ * (d * x * d⁻¹) = d * x * d⁻¹ * e ⟨w, hwL⟩) : w = 1 := by
  have hX₀D : X₀ ≤ centralizer (C3Levi K : Set (adjointGroup .F4 K)) := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact (centralizer_nonsplit hXJ hcyc (by rw [hX₀, hK])).2.2
  have hDq : CFSG.IsQuasisimple (subgroupToG e (C3Levi K)) := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact isQuasisimple_map_C3Levi e
  have hDperf : ⁅subgroupToG e (C3Levi K), subgroupToG e (C3Levi K)⁆ = subgroupToG e (C3Levi K) :=
    Subgroup.isPerfect_iff.1 hDq.1
  have hDX : subgroupToG e (C3Levi K) ≤ centralizer (subgroupToG e X₀ : Set G) :=
    map_map_symm_le_centralizer e hX₀D
  have hDE : subgroupToG e (C3Levi K) ≤ centralizerPerfectCore (subgroupToG e X₀) :=
    le_centralizerPerfectCore hDperf hDX
  have hsD : ∀ δ ∈ C3Levi K, e ⟨w, hwL⟩ * (d * δ * d⁻¹) = d * δ * d⁻¹ * e ⟨w, hwL⟩ := by
    intro δ hδ
    have hgE : ((e.symm (d * δ * d⁻¹) : L) : G) ∈ (centralizerPerfectCore (subgroupToG e X₀)).map
        (MulAut.conj ((e.symm d : L) : G)).toMonoidHom := by
      refine ⟨((e.symm δ : L) : G), hDE (coe_symm_mem_subgroupToG e hδ), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv,
        Subgroup.coe_mul, Subgroup.coe_inv]
    have hgt : ((e.symm (d * δ * d⁻¹) : L) : G) ∈ centralizer ({t} : Set G) :=
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 htC _ (e.symm _).2)
    have h1 := hwc _ ⟨hEM hgE, hgt⟩
    have h2 : e.symm (d * δ * d⁻¹) * ⟨w, hwL⟩ = ⟨w, hwL⟩ * e.symm (d * δ * d⁻¹) := Subtype.ext h1
    have h3 : e (e.symm (d * δ * d⁻¹) * ⟨w, hwL⟩) = e (⟨w, hwL⟩ * e.symm (d * δ * d⁻¹)) :=
      congrArg e h2
    rw [e.map_mul, e.map_mul, e.apply_symm_apply] at h3
    exact h3.symm
  have hyX : d⁻¹ * e ⟨w, hwL⟩ * d ∈ centralizer (X₀ : Set (adjointGroup .F4 K)) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h := hwX x hx
    calc x * (d⁻¹ * e ⟨w, hwL⟩ * d) = d⁻¹ * ((d * x * d⁻¹) * e ⟨w, hwL⟩) * d := by group
      _ = d⁻¹ * (e ⟨w, hwL⟩ * (d * x * d⁻¹)) * d := by rw [h]
      _ = d⁻¹ * e ⟨w, hwL⟩ * d * x := by group
  have hs2 : e ⟨w, hwL⟩ * e ⟨w, hwL⟩ = 1 := by
    rw [← map_mul]
    have h1 : (⟨w, hwL⟩ : L) * ⟨w, hwL⟩ = 1 := Subtype.ext hww
    rw [h1, map_one]
  have hy2 : (d⁻¹ * e ⟨w, hwL⟩ * d) * (d⁻¹ * e ⟨w, hwL⟩ * d) = 1 := by
    calc (d⁻¹ * e ⟨w, hwL⟩ * d) * (d⁻¹ * e ⟨w, hwL⟩ * d) =
        d⁻¹ * (e ⟨w, hwL⟩ * e ⟨w, hwL⟩) * d := by group
      _ = 1 := by rw [hs2]; group
  have hyD : ∀ δ ∈ C3Levi K, (d⁻¹ * e ⟨w, hwL⟩ * d) * δ = δ * (d⁻¹ * e ⟨w, hwL⟩ * d) := by
    intro δ hδ
    have h := hsD δ hδ
    calc (d⁻¹ * e ⟨w, hwL⟩ * d) * δ = d⁻¹ * (e ⟨w, hwL⟩ * (d * δ * d⁻¹)) * d := by group
      _ = d⁻¹ * (d * δ * d⁻¹ * e ⟨w, hwL⟩) * d := by rw [h]
      _ = δ * (d⁻¹ * e ⟨w, hwL⟩ * d) := by group
  have hy1 := eq_one_of_mem_centralizer_of_commute_C3Levi hK hXJ hcyc hX₀ hyX hy2 hyD
  have hs1 : e ⟨w, hwL⟩ = 1 := by
    have h1 : e ⟨w, hwL⟩ = d * (d⁻¹ * e ⟨w, hwL⟩ * d) * d⁻¹ := by group
    rw [h1, hy1]
    group
  have h2 : (⟨w, hwL⟩ : L) = 1 := e.injective (hs1.trans (map_one e).symm)
  exact congrArg Subtype.val h2

end Endgame

section CaseL

theorem twoE6XiCaseLInput_holds : TwoE6XiCaseLInput := by
  intro G _ _ L K _ _ _ e t hw X₀ hXJ hcyc hX₀ hκ6 hκ8 φF hφF e₀ M hM htM eM η hη hx φ hφ w hwM
    hwL hww htw hwq hwΛ hwc htwM _ htN htwN hC₀ _ hφ'
  obtain ⟨φ', hφ'⟩ := hφ'
  have hK : Nat.card K = 2 := by rw [hw.card_eq, pow_one]
  have hK1 : Nat.card K = 2 ^ 1 := hw.card_eq
  have htC := hw.mem_centralizer
  have := finite_adjointGroup_F4 (K := K)
  obtain ⟨hZ0, -, -⟩ := exists_mulEquiv_twoE6Span_of_family hK e X₀ htC hφF
  obtain ⟨g, hMg⟩ := hM
  have hZMc : Nat.card (center M) = 1 := by
    rw [hMg, E6Pilot.card_center_conjugate, hZ0, Subgroup.card_bot]
  have hZM : center M = ⊥ := Subgroup.eq_bot_of_card_eq _ hZMc
  have hZModd : Odd (Nat.card (center M)) := by
    rw [hZMc]
    exact odd_one
  have hw1 : w ≠ 1 := by
    intro h1
    subst h1
    apply not_conj_eta_xi_E6 le_rfl hK1 hη hx 1
    have h2 : (⟨_, hx⟩ : adjointGroup TwistTag.E6.tag K) = 1 := by
      have h3 : eM (QuotientGroup.mk' (center M) (⟨1, hwM⟩ : M)) = 1 := by
        have h4 : (⟨1, hwM⟩ : M) = 1 := rfl
        rw [h4, map_one, map_one]
      rw [hwq] at h3
      have h4 := congrArg φ h3
      rwa [MulAut.inv_apply, MulEquiv.apply_symm_apply, map_one] at h4
    rw [h2, map_one]
    group
  have hχ : (φ'⁻¹ * φ) * normalizerQuotMulAut eM ⟨t, htM⟩ * (φ'⁻¹ * φ)⁻¹ =
      normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ := by
    calc (φ'⁻¹ * φ) * normalizerQuotMulAut eM ⟨t, htM⟩ * (φ'⁻¹ * φ)⁻¹ =
        φ'⁻¹ * (φ * normalizerQuotMulAut eM ⟨t, htM⟩ * φ⁻¹) * φ' := by group
      _ = φ'⁻¹ * (φ' * normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ * φ'⁻¹) * φ' := by rw [hφ, hφ']
      _ = normalizerQuotMulAut e₀ ⟨t * w, htwN⟩ := by group
  set β := quotTransport hZM hZ0 eM e₀ (φ'⁻¹ * φ) with hβdef
  have hβt : ∀ m : M, (m : G) ∈ centralizer ({t} : Set G) ↔
      (β m : G) ∈ centralizer ({t * w} : Set G) :=
    quotTransport_mem_centralizer_iff hZM hZ0 eM e₀ htM htwN hχ
  have hOut := isSolvable_outer_of_mulEquiv_F4 e
  have hΛcL := perfectCore_inf_centralizer_le hw.standard hOut htC hw.orderOf_eq M
  have hΛcw : perfectCore (M ⊓ centralizer ({t} : Set G)) ≤ centralizer ({w} : Set G) :=
    fun c hc => mem_centralizer_singleton_iff.2 (hwc c (CFSG.Quasithin.perfectCore_le _ hc))
  obtain ⟨κ, c₁, hκtu, hc₁, hΛeq, hΛcard⟩ := exists_yRep_of_le_of_dvd hK e hwL hw1 hΛcL hΛcw
    (natCard_centralizer_yRep_dvd_of_xi hK hZModd eM hw.orderOf_eq htM hη hx hφ)
  have hΛperf : ⁅L ⊓ centralizer ({w} : Set G), L ⊓ centralizer ({w} : Set G)⁆ =
      L ⊓ centralizer ({w} : Set G) := by
    rw [← hΛeq]
    exact CFSG.Quasithin.perfectCore_perfect _
  have hLG₀ := le_twoE6Span e X₀
  have hΛG₀ : L ⊓ centralizer ({w} : Set G) ≤ twoE6Span e X₀ := inf_le_left.trans hLG₀
  have hΛtw : L ⊓ centralizer ({w} : Set G) ≤ centralizer ({t * w} : Set G) := by
    intro l hl
    have hlL : l ∈ L := (mem_inf.1 hl).1
    have hlw : l * w = w * l := mem_centralizer_singleton_iff.1 (mem_inf.1 hl).2
    rw [mem_centralizer_singleton_iff]
    have h1 : l * t = t * l := mem_centralizer_iff.1 htC l hlL
    calc l * (t * w) = (l * t) * w := by group
      _ = t * (l * w) := by rw [h1]; group
      _ = t * (w * l) := by rw [hlw]
      _ = t * w * l := by group
  have hβΛ : ∀ l : twoE6Span e X₀, (l : G) ∈ L ⊓ centralizer ({w} : Set G) →
      ((β.symm l : M) : G) ∈ L ⊓ centralizer ({w} : Set G) := by
    intro l hl
    have hP : (((L ⊓ centralizer ({w} : Set G)).subgroupOf (twoE6Span e X₀)).map
        β.symm.toMonoidHom).map M.subtype ≤ L ⊓ centralizer ({w} : Set G) := by
      refine le_trans (CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_) hΛeq.le
      · rintro _ ⟨_, ⟨l', hl', rfl⟩, rfl⟩
        refine ⟨(β.symm l').2, (hβt (β.symm l')).2 ?_⟩
        rw [MulEquiv.apply_symm_apply]
        exact hΛtw (mem_subgroupOf.1 hl')
      · exact commutator_map_eq _ (commutator_map_eq _ (commutator_subgroupOf_eq hΛG₀ hΛperf))
    exact hP ⟨β.symm l, ⟨l, mem_subgroupOf.2 hl, rfl⟩, rfl⟩
  set Λ : Subgroup G := L ⊓ centralizer ({w} : Set G) with hΛdef
  have hΛL : Λ ≤ L := inf_le_left
  set f : Λ →* Λ := (M.subtype.comp (β.symm.toMonoidHom.comp
    (Subgroup.inclusion hΛG₀))).codRestrict Λ (fun l => hβΛ (Subgroup.inclusion hΛG₀ l) l.2)
    with hfdef
  have hf : ∀ l : Λ, ((f l : Λ) : G) = ((β.symm ⟨l, hΛG₀ l.2⟩ : M) : G) := fun l => rfl
  have hfinj : Function.Injective f := by
    intro a b hab
    have h1 : ((β.symm ⟨a, hΛG₀ a.2⟩ : M) : G) = ((β.symm ⟨b, hΛG₀ b.2⟩ : M) : G) := by
      rw [← hf, ← hf, hab]
    have h2 := β.symm.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (fun y : twoE6Span e X₀ => (y : G)) h2)
  set θΛ : Λ ≃* Λ := MulEquiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.1 hfinj⟩
    with hθΛdef
  have hΨmem : ∀ l : Λ, (MulAut.conj c₁).toMonoidHom (e.toMonoidHom (Subgroup.inclusion hΛL l)) ∈
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) := by
    intro l
    change c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹ ∈ centralizer ({yRep K κ} : Set (adjointGroup .F4 K))
    rw [mem_centralizer_singleton_iff, ← hc₁]
    have h1 : (⟨l, hΛL l.2⟩ : L) * ⟨w, hwL⟩ = ⟨w, hwL⟩ * ⟨l, hΛL l.2⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 l.2).2)
    have h2 : e (⟨l, hΛL l.2⟩ * ⟨w, hwL⟩) = e (⟨w, hwL⟩ * ⟨l, hΛL l.2⟩) := congrArg e h1
    rw [e.map_mul, e.map_mul] at h2
    calc c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹ * (c₁ * e ⟨w, hwL⟩ * c₁⁻¹) =
        c₁ * (e ⟨l, hΛL l.2⟩ * e ⟨w, hwL⟩) * c₁⁻¹ := by group
      _ = c₁ * (e ⟨w, hwL⟩ * e ⟨l, hΛL l.2⟩) * c₁⁻¹ := by rw [h2]
      _ = c₁ * e ⟨w, hwL⟩ * c₁⁻¹ * (c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹) := by group
  set Ψ₀ : Λ →* centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) :=
    ((MulAut.conj c₁).toMonoidHom.comp (e.toMonoidHom.comp (Subgroup.inclusion hΛL))).codRestrict
      _ hΨmem with hΨ₀def
  have hΨ₀ : ∀ l : Λ, ((Ψ₀ l : centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) :
      adjointGroup .F4 K) = c₁ * e ⟨l, hΛL l.2⟩ * c₁⁻¹ := fun l => rfl
  have hΨinj : Function.Injective Ψ₀ := by
    intro a b hab
    have h1 : c₁ * e ⟨a, hΛL a.2⟩ * c₁⁻¹ = c₁ * e ⟨b, hΛL b.2⟩ * c₁⁻¹ := by
      rw [← hΨ₀, ← hΨ₀, hab]
    have h2 : e ⟨a, hΛL a.2⟩ = e ⟨b, hΛL b.2⟩ := mul_left_cancel (mul_right_cancel h1)
    have h3 := e.injective h2
    exact Subtype.ext (congrArg (fun y : L => (y : G)) h3)
  have hΨbij : Function.Bijective Ψ₀ :=
    (Nat.bijective_iff_injective_and_card Ψ₀).2 ⟨hΨinj, hΛcard⟩
  set ΨE : Λ ≃* centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) :=
    MulEquiv.ofBijective Ψ₀ hΨbij with hΨEdef
  have hXJ' : X₀ ≤ rootSL2 K rootR := by
    rw [rootSL2_rootR, ← highestRootRankOne_eq_rootSL2R]
    exact hXJ
  obtain ⟨c, hc⟩ := exists_conj_of_mulEquiv_centralizer_yRep hK hκtu hXJ' hX₀
    (ΨE.symm.trans (θΛ.trans ΨE))
  have hX₀ne : X₀ ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hX₀
    norm_num at hX₀
  obtain ⟨⟨x₀, hx₀X⟩, hx₀1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hX₀ne
  have hx₀1' : x₀ ≠ 1 := fun h => hx₀1 (Subtype.ext h)
  have hF3 : FactF3 K := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact factF3
  have hx₀C : x₀ ∈ centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) := by
    obtain ⟨Q, -, hQM, -, -⟩ := hF3 κ
    rw [← hQM]
    exact mem_sup_right (rootSL2_rootR_le_levi κ (hXJ' hx₀X))
  set x₀' : centralizer ({yRep K κ} : Set (adjointGroup .F4 K)) := ⟨x₀, hx₀C⟩ with hx₀'def
  set z : Λ := ΨE.symm x₀' with hzdef
  have hz : c₁ * e ⟨z, hΛL z.2⟩ * c₁⁻¹ = x₀ := congrArg Subtype.val (ΨE.apply_symm_apply x₀')
  set z' : Λ := θΛ z with hz'def
  have hz'G : (z' : G) = ((β.symm ⟨z, hΛG₀ z.2⟩ : M) : G) := rfl
  have hθx : (((ΨE.symm.trans (θΛ.trans ΨE)) x₀' :
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) : adjointGroup .F4 K) =
        c₁ * e ⟨z', hΛL z'.2⟩ * c₁⁻¹ := rfl
  have hmem : (((ΨE.symm.trans (θΛ.trans ΨE)) x₀' :
      centralizer ({yRep K κ} : Set (adjointGroup .F4 K))) : adjointGroup .F4 K) ∈
      ((X₀.subgroupOf (centralizer ({yRep K κ} : Set (adjointGroup .F4 K)))).map
        (ΨE.symm.trans (θΛ.trans ΨE)).toMonoidHom).map
          (centralizer ({yRep K κ} : Set (adjointGroup .F4 K))).subtype :=
    ⟨_, ⟨x₀', hx₀X, rfl⟩, rfl⟩
  rw [hθx] at hmem
  have hzX : (z : G) ∈ subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom) := by
    rw [mem_subgroupToG_iff e (hΛL z.2)]
    refine ⟨x₀, hx₀X, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [← hz]
    group
  have hz1 : (z : G) ≠ 1 := by
    intro h
    apply hx₀1'
    rw [← hz]
    have h1 : (⟨(z : G), hΛL z.2⟩ : L) = 1 := Subtype.ext h
    rw [h1, map_one]
    group
  have hA : centralizerPerfectCore (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)) =
      (centralizerPerfectCore (subgroupToG e X₀)).map
        (MulAut.conj ((e.symm c₁⁻¹ : L) : G)).toMonoidHom :=
    centralizerPerfectCore_subgroupToG_map_conj e X₀ c₁⁻¹
  have hAG₀ : centralizerPerfectCore (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)) ≤
      twoE6Span e X₀ := by
    rw [hA]
    rintro _ ⟨a, ha, rfl⟩
    have hn : ((e.symm c₁⁻¹ : L) : G) ∈ twoE6Span e X₀ := hLG₀ (e.symm c₁⁻¹).2
    have ha' : a ∈ twoE6Span e X₀ := centralizerPerfectCore_le_twoE6Span e X₀ ha
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact mul_mem (mul_mem hn ha') (inv_mem hn)
  have hAz : centralizerPerfectCore (subgroupToG e (X₀.map (MulAut.conj c₁⁻¹).toMonoidHom)) ≤
      centralizer ({(z : G)} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2
      ((mem_centralizer_iff.1 (centralizerPerfectCore_le_centralizer _ ha) _ hzX).symm)
  obtain ⟨P, hPM, hPperf, hPcard, hPz'⟩ := exists_perfect_pullback β hAG₀
    (commutator_centralizerPerfectCore _) ⟨z, hΛG₀ z.2⟩ hAz
  rw [← hz'G] at hPz'
  have hPcard' : Nat.card P = Nat.card (centralizerPerfectCore (subgroupToG e X₀)) := by
    rw [hPcard, natCard_centralizerPerfectCore_subgroupToG_map_conj]
  have hz'1 : (z' : G) ≠ 1 := by
    intro h
    apply hz1
    have h1 : z' = 1 := Subtype.ext h
    have h2 : z = 1 := θΛ.injective (h1.trans (map_one θΛ).symm)
    rw [h2]
    rfl
  have hwz' : e ⟨w, hwL⟩ * e ⟨z', hΛL z'.2⟩ = e ⟨z', hΛL z'.2⟩ * e ⟨w, hwL⟩ := by
    have h1 : (⟨z', hΛL z'.2⟩ : L) * ⟨w, hwL⟩ = ⟨w, hwL⟩ * ⟨z', hΛL z'.2⟩ :=
      Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 z'.2).2)
    have h2 : e (⟨z', hΛL z'.2⟩ * ⟨w, hwL⟩) = e (⟨w, hwL⟩ * ⟨z', hΛL z'.2⟩) := congrArg e h1
    rw [e.map_mul, e.map_mul] at h2
    exact h2.symm
  have key : ∀ H : Subgroup (adjointGroup .F4 K), Nat.card H = 3 →
      c₁ * e ⟨z', hΛL z'.2⟩ * c₁⁻¹ ∈ H.map (MulAut.conj c).toMonoidHom →
      P ≤ centralizerPerfectCore (subgroupToG e (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom)) ∧
      ∀ x ∈ H, e ⟨w, hwL⟩ * ((c₁⁻¹ * c) * x * (c₁⁻¹ * c)⁻¹) =
        ((c₁⁻¹ * c) * x * (c₁⁻¹ * c)⁻¹) * e ⟨w, hwL⟩ := by
    intro H hH3 hzH
    have hzH' : e ⟨z', hΛL z'.2⟩ ∈ H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom := by
      obtain ⟨y, hy, hyeq⟩ := hzH
      refine ⟨y, hy, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyeq ⊢
      calc (c₁⁻¹ * c) * y * (c₁⁻¹ * c)⁻¹ = c₁⁻¹ * (c * y * c⁻¹) * c₁ := by group
        _ = c₁⁻¹ * (c₁ * e ⟨z', hΛL z'.2⟩ * c₁⁻¹) * c₁ := by rw [hyeq]
        _ = e ⟨z', hΛL z'.2⟩ := by group
    have hcardH : Nat.card (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom) = 3 := by
      rw [card_map_of_injective (MulAut.conj _).injective, hH3]
    have hez'1 : e ⟨z', hΛL z'.2⟩ ≠ 1 := fun h => hz'1 (by
      have h1 := e.injective (h.trans (map_one e).symm)
      exact congrArg Subtype.val h1)
    have hzpF : zpowers (e ⟨z', hΛL z'.2⟩) = H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom :=
      zpowers_eq_of_mem_of_card_prime Nat.prime_three hcardH hzH' hez'1
    have hzG : (z' : G) ∈ subgroupToG e (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom) :=
      (mem_subgroupToG_iff e (hΛL z'.2)).2 hzH'
    have hzpG : zpowers (z' : G) = subgroupToG e (H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom) :=
      zpowers_eq_of_mem_of_card_prime Nat.prime_three (by rw [natCard_subgroupToG, hcardH]) hzG
        hz'1
    refine ⟨le_centralizerPerfectCore hPperf ?_, ?_⟩
    · rw [← hzpG, centralizer_zpowers_coe_eq]
      exact hPz'
    · intro x hx
      have hwC : e ⟨w, hwL⟩ ∈ centralizer ((H.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom :
          Subgroup (adjointGroup .F4 K)) : Set (adjointGroup .F4 K)) := by
        rw [← hzpF, centralizer_zpowers_coe_eq, mem_centralizer_singleton_iff]
        exact hwz'
      exact (mem_centralizer_iff.1 hwC _ ⟨x, hx, rfl⟩).symm
  rcases hc with hc | hc
  ·
    rw [hc] at hmem
    obtain ⟨hPE, hwX⟩ := key X₀ hX₀ hmem
    have hEcard : Nat.card (centralizerPerfectCore (subgroupToG e
        (X₀.map (MulAut.conj (c₁⁻¹ * c)).toMonoidHom))) = Nat.card P := by
      rw [natCard_centralizerPerfectCore_subgroupToG_map_conj, hPcard']
    have hPeq := Subgroup.eq_of_le_of_card_ge hPE hEcard.le
    have hEM : (centralizerPerfectCore (subgroupToG e X₀)).map
        (MulAut.conj ((e.symm (c₁⁻¹ * c) : L) : G)).toMonoidHom ≤ M := by
      rw [← centralizerPerfectCore_subgroupToG_map_conj, ← hPeq]
      exact hPM
    exact hw1 (eq_one_of_le_map_conj_of_commute hK e htC hXJ hcyc hX₀ (c₁⁻¹ * c) hEM hwL hww
      hwc hwX)
  ·
    rw [hc] at hmem
    have hφX₀ : Nat.card (X₀.map (graphAutF4 K).toMonoidHom) = 3 := by
      rw [card_map_of_injective (f := (graphAutF4 K).toMonoidHom) (graphAutF4 K).injective, hX₀]
    obtain ⟨hPE, -⟩ := key _ hφX₀ hmem
    apply twoE6CoreNotDvdInput_holds G L K e t hw X₀ hXJ hcyc hX₀ hκ6 hκ8
    rw [← hPcard', subgroupToG_trans_symm_eq_map,
      ← natCard_centralizerPerfectCore_subgroupToG_map_conj e _ (c₁⁻¹ * c)]
    exact Subgroup.card_dvd_of_le hPE

theorem twoE6UniqueInput_holds : TwoE6UniqueInput :=
  twoE6UniqueInput_of_notDvd_caseL twoE6CoreNotDvdInput_holds twoE6XiCaseLInput_holds

end CaseL

end CFSG.SeitzReduction.F4Pilot
