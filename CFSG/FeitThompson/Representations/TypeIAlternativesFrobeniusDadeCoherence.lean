module

public import CFSG.FeitThompson.Representations.OrientedSeparationFullCoreDadeSupports
public import CFSG.FeitThompson.Representations.DadeInverseConstantOffExceptionalFamily
public import CFSG.FeitThompson.Representations.ExponentDivisibilityFrobeniusCoherence
public import CFSG.FeitThompson.Representations.SibleyNilpotentFrobeniusCoherence
import CFSG.FeitThompson.Local.SupportingFrobeniusComplementShape
import CFSG.FeitThompson.Representations.SolvableGroupNonprincipalLinearCharacter
import CFSG.FeitThompson.Representations.LargeAbelianizationDescendingCoherence
import CFSG.FeitThompson.Representations.DadeMapPreservesInnerProduct
import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
import CFSG.FeitThompson.Representations.PGroupFrobeniusTISibleyCoherence
import CFSG.FeitThompson.Representations.DadeMapPreservesGenChars
import CFSG.FeitThompson.Representations.OddNormalInducedBlocksConjPairs
import CFSG.FeitThompson.Representations.DadeMapRestrictsInductionTI

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace FrobeniusDade

open Subgroup NormalInducedFamily
open scoped Pointwise

section Aux

variable {G : Type*} [Group G]

theorem isCoherent_of_set_eq {X : Type*} [Group X] [Fintype X] [Fintype G]
    {S S' : Set (X → ℂ)} (hSS' : S = S')
    (τ : charSpanZero S →+ virtualChars G) (τ' : charSpanZero S' →+ virtualChars G)
    (hcoe : ∀ (f : charSpanZero S) (f' : charSpanZero S'),
      (f : X → ℂ) = (f' : X → ℂ) → (τ f : G → ℂ) = (τ' f' : G → ℂ))
    (h : IsCoherent S' τ') : IsCoherent S τ := by
  subst hSS'
  have he : τ = τ' := AddMonoidHom.ext fun f => Subtype.ext (hcoe f f rfl)
  rwa [he]

variable {L H : Subgroup G}

theorem sdiff_eq_image_subgroupOf (hHL : H ≤ L) :
    (H : Set G) \ {1}
      = (fun x : ↥L => (x : G)) '' (((H.subgroupOf L : Subgroup ↥L) : Set ↥L) \ {1}) :=
  (SibleyPGroupCoherence.sdiff_eq_sdiff_map_subgroupOf hHL).trans sdiff_map_eq_image

theorem sdiff_nonempty (hH : H ≠ ⊥) : ((H : Set G) \ {1}).Nonempty := by
  have : Nontrivial ↥H := H.nontrivial_iff_ne_bot.2 hH
  obtain ⟨x, hx⟩ := exists_ne (1 : ↥H)
  exact ⟨(x : G), x.2, by simpa using hx⟩

end Aux

section Pair

variable {L G : Type*} [Group L] [Group G] [Fintype L] [Fintype G]
  {S : Set (L → ℂ)} {tau : (L → ℂ) → G → ℂ}
  {τ : charSpanZero S →+ virtualChars G} {ν : Submodule.span ℤ S →+ virtualChars G}

theorem coe_nu_mem_signedIrr (hν : IsCoherentWith S τ ν) {ζ : L → ℂ} (hζS : ζ ∈ S)
    (hζIrr : ζ ∈ Irr L) :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) ∈ signedIrr G := by
  refine mem_signedIrr.2 (mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one
    (mem_span_Irr_of_mem_virtualChars (ν _).2) ?_)
  rw [hν.inner_eq]
  exact cfInner_self_of_mem_Irr hζIrr

theorem cfInner_tau_sub_star_nu (hτ : IsAntirealIsometry S tau)
    (hτcoe : ∀ f : charSpanZero S, (τ f : G → ℂ) = tau (f : L → ℂ))
    (hν : IsCoherentWith S τ ν) {ζ : L → ℂ} (hζS : ζ ∈ S) :
    cfInner (tau (ζ - star ζ)) (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) = 1 := by
  have hζIrr : ζ ∈ Irr L := hτ.subset_Irr hζS
  have hstarS : star ζ ∈ S := hτ.star_mem ζ hζS
  set f₀ : charSpanZero S := ⟨ζ - star ζ, hτ.sub_star_mem hζS⟩ with hf₀
  have hg : (ζ - star ζ) ∈ Submodule.span ℤ S :=
    sub_mem (Submodule.subset_span hζS) (Submodule.subset_span hstarS)
  have hincl : Submodule.inclusion (charSpanZero_le S) f₀ = ⟨ζ - star ζ, hg⟩ := Subtype.ext rfl
  have hkey : tau (ζ - star ζ) = (ν ⟨ζ - star ζ, hg⟩ : G → ℂ) := by
    rw [← hincl, hν.eq_on_zero f₀, hτcoe f₀]
  rw [hkey, hν.inner_eq]
  change cfInner (ζ - star ζ) ζ = 1
  rw [cfInner_sub_left, cfInner_self_of_mem_Irr hζIrr,
    cfInner_eq_ite_of_mem_Irr (star_mem_Irr hζIrr) hζIrr, if_neg (hτ.star_ne ζ hζS), sub_zero]

theorem coe_nu_eq_or_eq_neg_star (hτ : IsAntirealIsometry S tau)
    (hτcoe : ∀ f : charSpanZero S, (τ f : G → ℂ) = tau (f : L → ℂ))
    (hν : IsCoherentWith S τ ν) {ζ : L → ℂ} (hζS : ζ ∈ S) :
    (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) = antirealRoot (tau (ζ - star ζ)) ∨
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ)
        = -star (antirealRoot (tau (ζ - star ζ))) := by
  have hηIrr := hτ.root_mem_Irr hζS
  have hηne := hτ.star_root_ne hζS
  have hstarIrr := star_mem_Irr hηIrr
  have horth : cfInner (antirealRoot (tau (ζ - star ζ)))
      (star (antirealRoot (tau (ζ - star ζ)))) = 0 := by
    rw [cfInner_eq_ite_of_mem_Irr hηIrr hstarIrr, if_neg fun hcon => hηne hcon.symm]
  have hsub : cfInner (antirealRoot (tau (ζ - star ζ)) - star (antirealRoot (tau (ζ - star ζ))))
      (ν ⟨ζ, Submodule.subset_span hζS⟩ : G → ℂ) = 1 := by
    rw [← hτ.map_sub_star_eq hζS]
    exact cfInner_tau_sub_star_nu hτ hτcoe hν hζS
  exact eq_or_eq_neg_of_cfInner_sub_eq_one (Irr_subset_signedIrr hηIrr)
    (Irr_subset_signedIrr hstarIrr)
    (coe_nu_mem_signedIrr hν hζS (hτ.subset_Irr hζS)) horth hsub

end Pair

variable {G : Type*} [Group G] [Fintype G] {L H E : Subgroup G} {J : G → Subgroup G}

structure IsSetup (L H E : Subgroup G) (J : G → Subgroup G) : Prop where
  odd_card : Odd (Nat.card ↥L)
  le_left : H ≤ L
  le_right : E ≤ L
  le_normalizer : L ≤ normalizer (H : Set G)
  sup_eq : H ⊔ E = L
  inf_eq_bot : H ⊓ E = ⊥
  ne_bot_left : H ≠ ⊥
  ne_bot_right : E ≠ ⊥
  free : ∀ u ∈ E, u ≠ 1 → H ⊓ centralizer ({u} : Set G) = ⊥
  isNilpotent : Group.IsNilpotent ↥H
  isDadeData : IsDadeData L ((H : Set G) \ {1}) J

namespace IsSetup

abbrev core (_hc : IsSetup L H E J) : Subgroup ↥L := H.subgroupOf L

abbrev compl (_hc : IsSetup L H E J) : Subgroup ↥L := E.subgroupOf L

variable (hc : IsSetup L H E J)

theorem normal_core : (hc.core).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hc.le_left).2 hc.le_normalizer

theorem isComplement'_core : (hc.core).IsComplement' hc.compl :=
  SibleyPGroupCoherence.isComplement'_subgroupOf hc.le_left hc.le_right hc.le_normalizer
    hc.sup_eq hc.inf_eq_bot

theorem core_ne_bot : hc.core ≠ ⊥ :=
  SibleyNilpotentCoherence.subgroupOf_ne_bot hc.le_left hc.ne_bot_left

theorem compl_ne_bot : hc.compl ≠ ⊥ := by
  intro h
  rw [Subgroup.subgroupOf_eq_bot, disjoint_iff, inf_eq_left.2 hc.le_right] at h
  exact hc.ne_bot_right h

theorem free_core : ∀ u ∈ hc.compl, u ≠ 1 → hc.core ⊓ centralizer ({u} : Set ↥L) = ⊥ :=
  CFSG.FeitThompson.free_subgroupOf hc.le_left hc.free

theorem isNilpotent_core : Group.IsNilpotent ↥hc.core :=
  (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hc.le_left)).2 hc.isNilpotent

theorem sdiff_eq_image :
    (H : Set G) \ {1} = (fun x : ↥L => (x : G)) '' ((hc.core : Set ↥L) \ {1}) :=
  sdiff_eq_image_subgroupOf hc.le_left

theorem card_core : Nat.card ↥hc.core = Nat.card ↥H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe hc.le_left).toEquiv

theorem exponent_compl : Monoid.exponent ↥hc.compl = Monoid.exponent ↥E :=
  Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hc.le_right)

theorem mul_core_compl :
    ((hc.core : Subgroup ↥L) : Set ↥L) * ((hc.compl : Subgroup ↥L) : Set ↥L) = Set.univ :=
  hc.isComplement'_core.mul_eq

theorem inf_core_compl : hc.core ⊓ hc.compl = ⊥ := disjoint_iff.1 hc.isComplement'_core.disjoint

section Fam

variable [Fintype ↥L]

abbrev family (hc : IsSetup L H E J) : Set (↥L → ℂ) :=
  indFam hc.core (nonprincipalIrr ↥hc.core)

theorem family_subset_indFam_Irr : hc.family ⊆ indFam hc.core (Irr ↥hc.core) :=
  indFam_mono _ nonprincipalIrr_subset_Irr

theorem family_subset_Irr : hc.family ⊆ Irr ↥L :=
  SibleyNilpotentCoherence.indFam_subgroupOf_subset_Irr hc.le_left hc.le_right hc.le_normalizer
    hc.sup_eq hc.inf_eq_bot hc.ne_bot_left hc.free

theorem star_mem_family {ζ : ↥L → ℂ} (hζ : ζ ∈ hc.family) : star ζ ∈ hc.family :=
  conj_mem_indFam_nonprincipalIrr _ hζ

theorem star_ne_of_mem_family {ζ : ↥L → ℂ} (hζ : ζ ∈ hc.family) : star ζ ≠ ζ :=
  have := hc.normal_core
  fun h => ne_conj_of_mem_indFam_nonprincipalIrr hc.odd_card _ hζ h.symm

theorem family_nonempty : hc.family.Nonempty := by
  have := hc.normal_core
  have : Nontrivial ↥hc.core := (Subgroup.nontrivial_iff_ne_bot _).2 hc.core_ne_bot
  have : Group.IsNilpotent ↥hc.core := hc.isNilpotent_core
  have : Group.IsSolvable ↥hc.core := inferInstance
  obtain ⟨θ, hθ, -, hθ1⟩ := exists_mem_Irr_apply_one_eq_one_and_ne_one ↥hc.core
  exact ⟨indClassFun hc.core θ, (mem_indFam _).2 ⟨θ, mem_nonprincipalIrr.2 ⟨hθ, hθ1⟩, rfl⟩⟩

theorem family_nontrivial : hc.family.Nontrivial := by
  obtain ⟨ζ, hζ⟩ := hc.family_nonempty
  exact ⟨star ζ, hc.star_mem_family hζ, ζ, hζ, hc.star_ne_of_mem_family hζ⟩

theorem family_finite : hc.family.Finite := indFam_finite _ finite_nonprincipalIrr

theorem mem_dadeDomain_of_mem_charSpanZero {S : Set (↥L → ℂ)}
    (hS : S ⊆ indFam hc.core (Irr ↥hc.core)) {f : ↥L → ℂ} (hf : f ∈ charSpanZero S) :
    f ∈ dadeDomain L ((H : Set G) \ {1}) :=
  have := hc.normal_core
  mem_dadeDomain_of_mem_dadeZDomain
    (NormalInducedFamily.charSpanZero_le_dadeZDomain hc.sdiff_eq_image hS hf)

noncomputable def tauHom {S : Set (↥L → ℂ)} (hS : S ⊆ indFam hc.core (Irr ↥hc.core)) :
    charSpanZero S →+ virtualChars G :=
  have := hc.normal_core
  NormalInducedFamily.dadeBaselineHom hc.isDadeData hc.sdiff_eq_image hS

theorem coe_tauHom {S : Set (↥L → ℂ)} (hS : S ⊆ indFam hc.core (Irr ↥hc.core))
    (f : charSpanZero S) :
    ((hc.tauHom hS f : virtualChars G) : G → ℂ)
      = dadeMapFun L ((H : Set G) \ {1}) J (f : ↥L → ℂ) := by
  have := hc.normal_core
  rw [tauHom, NormalInducedFamily.coe_dadeBaselineHom hc.isDadeData hc.sdiff_eq_image hS f
    ⟨(f : ↥L → ℂ), hc.mem_dadeDomain_of_mem_charSpanZero hS f.2⟩ rfl, coe_dadeMap]

theorem cfInner_tauHom {S : Set (↥L → ℂ)} (hS : S ⊆ indFam hc.core (Irr ↥hc.core))
    (f g : charSpanZero S) :
    cfInner ((hc.tauHom hS f : virtualChars G) : G → ℂ)
        ((hc.tauHom hS g : virtualChars G) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) := by
  have hf := hc.mem_dadeDomain_of_mem_charSpanZero hS f.2
  have hg := hc.mem_dadeDomain_of_mem_charSpanZero hS g.2
  rw [hc.coe_tauHom hS f, hc.coe_tauHom hS g, ← coe_dadeMap hc.isDadeData ⟨(f : ↥L → ℂ), hf⟩,
    ← coe_dadeMap hc.isDadeData ⟨(g : ↥L → ℂ), hg⟩]
  exact cfInner_dadeMap hc.isDadeData _ _

theorem tauHom_apply_one {S : Set (↥L → ℂ)} (hS : S ⊆ indFam hc.core (Irr ↥hc.core))
    (f : charSpanZero S) : ((hc.tauHom hS f : virtualChars G) : G → ℂ) 1 = 0 := by
  have hf := hc.mem_dadeDomain_of_mem_charSpanZero hS f.2
  rw [hc.coe_tauHom hS f, ← coe_dadeMap hc.isDadeData ⟨(f : ↥L → ℂ), hf⟩]
  exact dadeMap_one_eq_zero hc.isDadeData _

noncomputable abbrev tau (hc : IsSetup L H E J) : charSpanZero hc.family →+ virtualChars G :=
  hc.tauHom hc.family_subset_indFam_Irr

theorem coe_tau (f : charSpanZero hc.family) :
    ((hc.tau f : virtualChars G) : G → ℂ)
      = dadeMapFun L ((H : Set G) \ {1}) J (f : ↥L → ℂ) :=
  hc.coe_tauHom _ f

theorem cfInner_tau (f g : charSpanZero hc.family) :
    cfInner ((hc.tau f : virtualChars G) : G → ℂ) ((hc.tau g : virtualChars G) : G → ℂ)
      = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ) :=
  hc.cfInner_tauHom _ f g

theorem tau_apply_one (f : charSpanZero hc.family) :
    ((hc.tau f : virtualChars G) : G → ℂ) 1 = 0 :=
  hc.tauHom_apply_one _ f

theorem isCoherent_tau_of_ti
    (hstab : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ↔ g ∈ L)
    (hdisj : ∀ g ∉ L, ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅) :
    IsCoherent hc.family hc.tau := by
  have hTIor : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) ∩ ((H : Set G) \ {1}) = ∅ := by
    intro g
    by_cases hg : g ∈ L
    · exact Or.inl ((hstab g).2 hg)
    · exact Or.inr (by rw [Set.inter_comm]; exact hdisj g hg)
  have _ : Group.IsNilpotent ↥H := hc.isNilpotent
  refine SibleyNilpotentCoherence.isCoherent_indFam_nonprincipalIrr (E := E) hc.odd_card
    hc.le_left hc.le_right hc.le_normalizer hc.sup_eq hc.inf_eq_bot hc.ne_bot_left
    hc.ne_bot_right hc.free hstab hTIor hc.tau (fun f => ?_)
  have hf := hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr f.2
  rw [hc.coe_tau f, ← coe_dadeMap hc.isDadeData ⟨(f : ↥L → ℂ), hf⟩]
  exact dadeMap_eq_indClassFun_of_stabilizer_eq hc.isDadeData subset_rfl
    (sdiff_nonempty hc.ne_bot_left) hstab hdisj _ hf

theorem isCoherent_tau_of_isMulCommutative [IsMulCommutative ↥H] :
    IsCoherent hc.family hc.tau := by
  have _ : IsMulCommutative ↥hc.core := Subgroup.subgroupOf_isMulCommutative L H
  exact isCoherent_of_forall_apply_one_eq hc.family_finite hc.family_subset_Irr
    (d := (Nat.card ↥hc.compl : ℂ))
    (fun _ hχ => apply_one_eq_card_of_mem_indFam_nonprincipalIrr hc.isComplement'_core hχ)
    hc.tau hc.cfInner_tau hc.tau_apply_one

theorem isCoherent_tau_of_exponent_dvd
    (hexp : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥H → Monoid.exponent ↥E ∣ p - 1) :
    IsCoherent hc.family hc.tau := by
  have hnorm := hc.normal_core
  have hnil := hc.isNilpotent_core
  refine isCoherent_of_set_eq (kerLayerIndFam_bot_eq_indFam_nonprincipalIrr hc.core).symm
    hc.tau (hc.tauHom NormalInducedFamily.kerLayerIndFam_subset_indFam)
    (fun f f' hff' => by rw [hc.coe_tauHom, hc.coe_tauHom, hff']) ?_
  refine isCoherent_kerLayerIndFam_bot_of_exponent_dvd_sub_one (E := hc.compl) hc.odd_card
    hc.core_ne_bot hc.compl_ne_bot hc.mul_core_compl hc.inf_core_compl hc.free_core _
    (hc.cfInner_tauHom _) (hc.tauHom_apply_one _) (fun p hp hpd => ?_)
  rw [hc.exponent_compl]
  exact hexp p hp (hc.card_core ▸ hpd)

theorem isCoherent_tau
    (halt :
      ((∀ g : G, (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = (H : Set G) \ {1} ↔ g ∈ L) ∧
          ∀ g ∉ L, ((H : Set G) \ {1}) ∩ (fun x => g⁻¹ * x * g) '' ((H : Set G) \ {1}) = ∅) ∨
        IsMulCommutative ↥H ∨
        ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥H → Monoid.exponent ↥E ∣ p - 1) :
    IsCoherent hc.family hc.tau := by
  rcases halt with ⟨hstab, hdisj⟩ | habel | hexp
  · exact hc.isCoherent_tau_of_ti hstab hdisj
  · have := habel
    exact hc.isCoherent_tau_of_isMulCommutative
  · exact hc.isCoherent_tau_of_exponent_dvd hexp

theorem isAntirealIsometry :
    IsAntirealIsometry hc.family (dadeMapFun L ((H : Set G) \ {1}) J) where
  subset_Irr := hc.family_subset_Irr
  star_mem := fun _ hχ => hc.star_mem_family hχ
  star_ne := fun _ hχ => hc.star_ne_of_mem_family hχ
  map_add := fun f _ g _ => dadeMapFun_add L _ J f g
  map_mem := fun f hf => by
    rw [← coe_dadeMap hc.isDadeData
      ⟨f, hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr hf⟩]
    exact hc.isDadeData.dadeMap_mem_span_Irr _ (Submodule.span_le.2
      (fun χ hχ => Submodule.subset_span (hc.family_subset_Irr hχ)) (charSpanZero_le _ hf))
  inner_eq := fun f hf g hg => by
    rw [← coe_dadeMap hc.isDadeData
        ⟨f, hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr hf⟩,
      ← coe_dadeMap hc.isDadeData
        ⟨g, hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr hg⟩]
    exact cfInner_dadeMap hc.isDadeData _ _
  apply_one := fun f hf => by
    rw [← coe_dadeMap hc.isDadeData
      ⟨f, hc.mem_dadeDomain_of_mem_charSpanZero hc.family_subset_indFam_Irr hf⟩]
    exact dadeMap_one_eq_zero hc.isDadeData _
  map_star := fun f _ => dadeMapFun_star L _ J f

theorem existsUnique_root {ζ : ↥L → ℂ} (hζ : ζ ∈ hc.family) :
    ∃! η : G → ℂ, η ∈ Irr G ∧ star η ≠ η ∧
      dadeMapFun L ((H : Set G) \ {1}) J (ζ - star ζ) = η - star η :=
  hc.isAntirealIsometry.existsUnique_root hζ

theorem root_mem_Irr {ζ : ↥L → ℂ} (hζ : ζ ∈ hc.family) :
    antirealRoot (dadeMapFun L ((H : Set G) \ {1}) J (ζ - star ζ)) ∈ Irr G :=
  hc.isAntirealIsometry.root_mem_Irr hζ

theorem star_root_ne {ζ : ↥L → ℂ} (hζ : ζ ∈ hc.family) :
    star (antirealRoot (dadeMapFun L ((H : Set G) \ {1}) J (ζ - star ζ)))
      ≠ antirealRoot (dadeMapFun L ((H : Set G) \ {1}) J (ζ - star ζ)) :=
  hc.isAntirealIsometry.star_root_ne hζ

theorem coe_nu_eq_or_eq_neg_star
    {ν : Submodule.span ℤ hc.family →+ virtualChars G}
    (hν : IsCoherentWith hc.family hc.tau ν) {ζ : ↥L → ℂ} (hζ : ζ ∈ hc.family) :
    (ν ⟨ζ, Submodule.subset_span hζ⟩ : G → ℂ)
        = antirealRoot (dadeMapFun L ((H : Set G) \ {1}) J (ζ - star ζ)) ∨
      (ν ⟨ζ, Submodule.subset_span hζ⟩ : G → ℂ)
        = -star (antirealRoot (dadeMapFun L ((H : Set G) \ {1}) J (ζ - star ζ))) :=
  FrobeniusDade.coe_nu_eq_or_eq_neg_star hc.isAntirealIsometry hc.coe_tau hν hζ

end Fam

end IsSetup

end FrobeniusDade

end CFSG.FeitThompson

end
