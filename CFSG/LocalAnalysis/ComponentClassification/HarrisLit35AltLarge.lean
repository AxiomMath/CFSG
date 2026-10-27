module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltPermIm
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltConf

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup Equiv Equiv.Perm GrSLit.L34Facts CFSG.ComponentClassification.GSThmB.Catalog82A10

theorem eq_altOn_of_isTwoComponentIn {m : ℕ} {π : Perm (Fin m)}
    (hππ : π * π = 1) {J : Subgroup (Perm (Fin m))}
    (hJ : IsTwoComponentIn J (centralizer {π} ⊓ alternatingGroup (Fin m))) :
    J = altOn π.supportᶜ ∧ 5 ≤ π.supportᶜ.card := by
  classical
  have hLP := hJ
  have hLPle := le_altOn_of_isTwoComponentIn hππ hJ
  set LP := J with hLPdef
  set T := π.supportᶜ with hTdef
  have hLPperf : ⁅LP, LP⁆ = LP := commutator_self_of_isPerfect hLP.2.2.1
  have hLPne : LP ≠ ⊥ := by
    intro hb
    apply not_odd_card_of_isTwoQuasisimple hLP.2.2
    have : Nat.card ↥LP = 1 := by rw [hb, card_bot]
    rw [this]
    exact odd_one
  have hpres : ∀ g ∈ LP, ∀ x, g x ∈ T ↔ x ∈ T := by
    intro g hg x
    have hgT := (mem_altOn.mp (hLPle hg)).2
    constructor
    · intro hgx
      by_contra hx
      have hfix : g x = x := by
        by_contra hne
        exact hx (hgT (Perm.mem_support.mpr hne))
      exact hx (hfix ▸ hgx)
    · intro hx
      by_contra hgx
      have hfix : g (g x) = g x := by
        by_contra hne
        exact hgx (hgT (Perm.mem_support.mpr hne))
      exact hgx (by rw [g.injective hfix]; exact hx)
  have hT5 : 5 ≤ T.card := by
    by_contra hlt
    push Not at hlt
    have hfixT := perfect_fix_small LP hLPperf T (by omega) hpres
    apply hLPne
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    refine Equiv.ext fun x => ?_
    change g x = x
    by_cases hx : x ∈ T
    · exact hfixT g hg x hx
    · have hgT := (mem_altOn.mp (hLPle hg)).2
      by_contra hne
      exact hx (hgT (Perm.mem_support.mpr hne))
  refine ⟨?_, hT5⟩
  have hAC : altOn T ≤ centralizer {π} ⊓ alternatingGroup (Fin m) := fun g hg => by
    obtain ⟨hgA, hgT⟩ := mem_altOn.mp hg
    exact ⟨mem_centralizer_singleton_iff.mpr (commute_of_support_subset_compl hgT), hgA⟩
  have hsub : (LP.subgroupOf (altOn T)).IsSubnormal := by
    have h1 := hLP.2.1.comap (Subgroup.inclusion hAC)
    have h2 : (LP.subgroupOf (centralizer {π} ⊓ alternatingGroup (Fin m))).comap
        (Subgroup.inclusion hAC) = LP.subgroupOf (altOn T) := by
      ext y
      rfl
    rwa [h2] at h1
  have hs : IsSimpleGroup ↥(altOn T) := isSimpleGroup_altOn T hT5
  rcases hsub.eq_bot_or_top_of_isSimpleGroup hs with hb | ht
  · exfalso
    apply hLPne
    rw [eq_bot_iff]
    intro g hg
    have h1 : (⟨g, hLPle hg⟩ : ↥(altOn T)) ∈ LP.subgroupOf (altOn T) := hg
    rw [hb, mem_bot] at h1
    exact (mem_bot).mpr (congrArg Subtype.val h1)
  · refine le_antisymm hLPle fun g hg => ?_
    have h1 : (⟨g, hg⟩ : ↥(altOn T)) ∈ LP.subgroupOf (altOn T) := ht ▸ mem_top _
    exact h1


theorem seven_fixed_of_full_a7_quotient {m : ℕ} {π : Perm (Fin m)}
    (hππ : π * π = 1) {J : Subgroup (Perm (Fin m))}
    (hJ : IsTwoComponentIn J (centralizer {π} ⊓ alternatingGroup (Fin m)))
    (e : (↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) :
    J = altOn π.supportᶜ ∧ π.supportᶜ.card = 7 ∧ pPrimeCore 2 ↥J = ⊥ := by
  obtain ⟨hEq, h5⟩ := eq_altOn_of_isTwoComponentIn hππ hJ
  have hs : IsSimpleGroup ↥J := by
    rw [hEq]
    exact isSimpleGroup_altOn _ h5
  let := hs
  have hO : pPrimeCore 2 ↥J = ⊥ := by
    rcases (inferInstance : (pPrimeCore 2 ↥J).Normal).eq_bot_or_eq_top with hb | ht
    · exact hb
    · exfalso
      apply not_odd_card_of_isTwoQuasisimple hJ.2.2
      have ho := (pPrimeCore_coprime_card (p := 2) (G := ↥J))
      rw [ht, card_top] at ho
      exact Nat.coprime_two_left.mp ho
  have hcardQ : Nat.card (↥J ⧸ pPrimeCore 2 ↥J) = 2520 := by
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num [Nat.factorial]
  have hcardJ : Nat.card ↥J = 2520 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥J), hcardQ,
      hO, card_bot, mul_one]
  have hfac : (π.supportᶜ.card).factorial / 2 = 2520 := by
    rw [hEq, card_altOn _ (by omega)] at hcardJ
    exact hcardJ
  have h7 : π.supportᶜ.card = 7 := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hl | hg
    · have hf := Nat.factorial_le (show π.supportᶜ.card ≤ 6 by omega)
      norm_num [Nat.factorial] at hf
      omega
    · have hf := Nat.factorial_le (show 8 ≤ π.supportᶜ.card by omega)
      norm_num [Nat.factorial] at hf
      omega
  exact ⟨hEq, h7, hO⟩

theorem odd_degree_ge_nine_of_full_a7_quotient {m : ℕ} {π : Perm (Fin m)}
    (hππ : π * π = 1) (hπne : π ≠ 1) {J : Subgroup (Perm (Fin m))}
    (hJ : IsTwoComponentIn J (centralizer {π} ⊓ alternatingGroup (Fin m)))
    (e : (↥J ⧸ pPrimeCore 2 ↥J) ≃* alternatingGroup (Fin 7)) :
    Odd m ∧ 9 ≤ m := by
  have h7 := (seven_fixed_of_full_a7_quotient hππ hJ e).2.1
  obtain ⟨k, hk⟩ := two_dvd_card_support (by rw [pow_two]; exact hππ)
  have hsum := Finset.card_add_card_compl π.support
  rw [Fintype.card_fin] at hsum
  have hkpos : 0 < k := by
    by_contra hn
    have hempty : π.support = ∅ := Finset.card_eq_zero.mp (by omega)
    exact hπne (support_eq_empty_iff.mp hempty)
  constructor
  · exact ⟨k + 3, by omega⟩
  · omega

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem tau_tau (h : Config G p w v L K) (y : ↥K ⧸ pPrimeCore 2 ↥K) : h.tau (h.tau y) = y := by
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  change oddAut h.beta (oddAut h.beta (QuotientGroup.mk k)) = QuotientGroup.mk k
  rw [oddAut_mk, oddAut_mk, h.beta_beta]

theorem quotAut_tau_sq (h : Config G p w v L K)
    (y : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K)) :
    quotAut h.tau (quotAut h.tau y) = y := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
  rw [quotAut_mk, quotAut_mk, h.tau_tau]

theorem exists_perm (h : Config G p w v L K) {m : ℕ} (hm7 : 7 ≤ m)
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m)) :
    ∃ π : Perm (Fin m), π * π = 1 ∧ ∀ y, y ∈ fixedPoints (quotAut h.tau) ↔
      (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m)) := by
  set σ := quotAut h.tau with hσdef
  have hbij := GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m (by omega)
    (by omega)
  set κ : Perm (Fin m) →* MulAut (alternatingGroup (Fin m)) := MulAut.conjNormal with hκ
  obtain ⟨π, hπ⟩ := hbij.2 (MulAut.congr e' σ)
  have hsq : σ * σ = 1 := by
    ext y
    exact h.quotAut_tau_sq y
  have hππ : π * π = 1 := by
    apply hbij.1
    rw [map_mul, hπ, map_one, ← map_mul, hsq, map_one]
  refine ⟨π, hππ, fun y => ?_⟩
  have h1 : e' (σ y) = κ π (e' y) := by
    rw [hπ]
    change e' (σ y) = e' (σ (e'.symm (e' y)))
    rw [MulEquiv.symm_apply_apply]
  have h2 : ((κ π (e' y) : alternatingGroup (Fin m)) : Perm (Fin m)) =
      π * (e' y : Perm (Fin m)) * π⁻¹ := MulAut.conjNormal_apply π (e' y)
  change σ y = y ↔ _
  constructor
  · intro hy
    have h3 : π * (e' y : Perm (Fin m)) * π⁻¹ = (e' y : Perm (Fin m)) := by
      rw [← h2, ← h1, hy]
    calc (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m)) * π⁻¹ * π := by rw [h3]
      _ = π * (e' y : Perm (Fin m)) := by group
  · intro hy
    apply e'.injective
    apply Subtype.ext
    rw [h1, h2, ← hy, mul_inv_cancel_right]

@[expose] noncomputable def iota {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m)) :
    (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) →* Perm (Fin m) :=
  (alternatingGroup (Fin m)).subtype.comp e'.toMonoidHom

omit [Finite G] in
theorem iota_injective {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m)) :
    Function.Injective (iota e') :=
  (alternatingGroup (Fin m)).subtype_injective.comp e'.injective

theorem map_fixedPoints_eq (h : Config G p w v L K) {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)} (hmemC : ∀ y, y ∈ fixedPoints (quotAut h.tau) ↔
      (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m))) :
    (fixedPoints (quotAut h.tau)).map (iota e') = centralizer {π} ⊓ alternatingGroup (Fin m) := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    exact ⟨mem_centralizer_singleton_iff.mpr ((hmemC y).mp hy), (e' y).2⟩
  · rintro g ⟨hgπ, hgA⟩
    refine ⟨e'.symm ⟨g, hgA⟩, (hmemC _).mpr ?_, ?_⟩
    · rw [MulEquiv.apply_symm_apply]
      exact mem_centralizer_singleton_iff.mp hgπ
    · change ((e' (e'.symm ⟨g, hgA⟩) : alternatingGroup (Fin m)) : Perm (Fin m)) = g
      rw [MulEquiv.apply_symm_apply]

theorem map_hat_le_altOn (h : Config G p w v L K) {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)} (hππ : π * π = 1) (hmemC : ∀ y, y ∈ fixedPoints (quotAut h.tau) ↔
      (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m))) {J : Subgroup G}
    (hJ : IsTwoComponentIn J (K ⊓ centralizer {v})) :
    IsTwoComponentIn ((hatOf K J).map (iota e')) (centralizer {π} ⊓ alternatingGroup (Fin m)) ∧
      (hatOf K J).map (iota e') ≤ altOn π.supportᶜ := by
  have h1 := isTwoComponentIn_map_of_injective (iota e') (iota_injective e')
    (h.isTwoComponentIn_hat hJ)
  rw [h.map_fixedPoints_eq e' hmemC] at h1
  exact ⟨h1, le_altOn_of_isTwoComponentIn hππ h1⟩

theorem compLK (h : Config G p w v L K) : IsTwoComponentIn L (K ⊓ centralizer {v}) := by
  have hle : L ≤ K ⊓ centralizer {v} := le_inf h.L_le (h.compL.1.trans inf_le_right)
  rw [isTwoComponentIn_iff hle]
  exact UnbalancedCorr.isPComponent_subgroupOf_of_le hle
    (inf_le_inf_right _ h.compK.1) ((isTwoComponentIn_iff h.compL.1).mp h.compL)

theorem map_hat_eq_altOn (h : Config G p w v L K) {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)} (hππ : π * π = 1) (hmemC : ∀ y, y ∈ fixedPoints (quotAut h.tau) ↔
      (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m))) :
    (hatOf K L).map (iota e') = altOn π.supportᶜ ∧ 5 ≤ (π.supportᶜ).card := by
  obtain ⟨hLP, -⟩ := h.map_hat_le_altOn e' hππ hmemC h.compLK
  exact eq_altOn_of_isTwoComponentIn hππ hLP

end Config

end CFSG.ComponentClassification.HarrisLit.L35
