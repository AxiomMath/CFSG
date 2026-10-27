module

public import CFSG.FeitThompson.Representations.TISetDadeData
public import CFSG.FeitThompson.Representations.CentralPrimeOrientedProjectionSupport
public import CFSG.FeitThompson.Representations.LinearFrobeniusLayerCoherence
public import CFSG.FeitThompson.Representations.ConstantCharacterCentralSectionCongruence
public import CFSG.FeitThompson.Representations.CoherentQuotientLinearImageConstant
public import CFSG.FeitThompson.Representations.NormOneVirtualCharacters
public import CFSG.FeitThompson.Representations.AbelianNormalDetectingRestrictionSplit
public import CFSG.FeitThompson.Representations.FreeActionAbelianizedCoreInducedIrreducible
public import CFSG.FeitThompson.Representations.FixedPointFreeComplementOrderBounds
public import CFSG.FeitThompson.Local.PSubgroupNormalizingFullPSubgroup
public import CFSG.FeitThompson.Local.NormalComplementDerivedIntersection
public import CFSG.FeitThompson.Local.SmallAbelianizationChiefFactor
public import CFSG.FeitThompson.Foundations.PGroupNilpotent
public import CFSG.FeitThompson.Foundations.AbelianSolvable
import Mathlib.GroupTheory.Abelianization.Finite
public import CFSG.FeitThompson.Representations.VirtualCharacterIntegerCoefficients

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace CentralPrimeInduction

open Subgroup
open NormalLinearInduced (indFamLinear apply_one_of_mem_indFamLinear)

variable {G : Type*} [Group G] {p a : ℕ} {L P E Z : Subgroup G}

structure IsCentralPrimeInduction (p a : ℕ) (L P E Z : Subgroup G) : Prop where
  prime : p.Prime
  odd_prime : Odd p
  one_le_exponent : 1 ≤ a
  natCard_P : Nat.card P = p ^ a
  odd_natCard_G : Odd (Nat.card G)
  P_le : P ≤ L
  le_normalizer_P : L ≤ normalizer (P : Set G)
  E_le : E ≤ L
  sup_eq : P ⊔ E = L
  inf_eq_bot : P ⊓ E = ⊥
  E_ne_bot : E ≠ ⊥
  isCyclic_E : IsCyclic E
  coprime_natCard : (Nat.card P).Coprime (Nat.card E)
  not_isMulCommutative_P : ¬ IsMulCommutative P
  Z_le_commutator : Z ≤ ⁅P, P⁆
  natCard_Z : Nat.card Z = p
  Z_le_center : Z ≤ L ⊓ centralizer (L : Set G)
  inf_centralizer_eq : ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) = Z
  fixes_only_commutator_coset : ∀ u ∈ E, u ≠ 1 → ∀ k ∈ P,
    k⁻¹ * (u⁻¹ * k * u) ∈ (⁅P, P⁆ : Subgroup G) → k ∈ (⁅P, P⁆ : Subgroup G)
  sylow_natCard_P : Nat.card P = p ^ ((Nat.card G).factorization p)
  stabilizer_punctured_eq : {g : G | (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1})
    = (P : Set G) \ {1}} = (L : Set G)
  inter_conj_eq_empty : ∀ g ∉ L, ((P : Set G) \ {1})
    ∩ ((fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1})) = ∅

theorem puncturedAmbient_subgroupOf_eq (hPL : P ≤ L) :
    (NormalLinearInduced.puncturedAmbient (P.subgroupOf L) : Set G) = (P : Set G) \ {1} := by
  ext g
  constructor
  · intro hg
    have hgL : g ∈ (L : Set G) := NormalLinearInduced.puncturedAmbient_subset hg
    have hg' : (⟨g, hgL⟩ : ↥L) ∈ P.subgroupOf L ∧ (⟨g, hgL⟩ : ↥L) ≠ 1 :=
      NormalLinearInduced.mem_puncturedAmbient_iff.1 hg
    exact ⟨Subgroup.mem_subgroupOf.1 hg'.1, fun hc => hg'.2 (Subtype.ext hc)⟩
  · rintro ⟨hgP, hg1⟩
    have hne : (⟨g, hPL hgP⟩ : ↥L) ≠ 1 := fun hc => hg1 (congrArg (fun w : ↥L => (w : G)) hc)
    have hx : ((⟨g, hPL hgP⟩ : ↥L) : G)
        ∈ NormalLinearInduced.puncturedAmbient (P.subgroupOf L) :=
      NormalLinearInduced.mem_puncturedAmbient_iff.2 ⟨Subgroup.mem_subgroupOf.2 hgP, hne⟩
    exact hx

namespace IsCentralPrimeInduction

variable (h : IsCentralPrimeInduction p a L P E Z)

include h

theorem Z_le_P : Z ≤ P := h.Z_le_commutator.trans (commutator_le_self P)

theorem Z_le : Z ≤ L := h.Z_le_center.trans inf_le_left

theorem Z_ne_bot : Z ≠ ⊥ := by
  have hZ := h.natCard_Z
  intro hbot
  rw [hbot, Subgroup.card_bot] at hZ
  exact h.prime.one_lt.ne' hZ.symm

theorem P_ne_bot : P ≠ ⊥ := fun hbot => h.Z_ne_bot (le_bot_iff.1 (hbot ▸ h.Z_le_P))

theorem Z_le_centralizer_P : Z ≤ centralizer (P : Set G) :=
  (h.Z_le_center.trans inf_le_right).trans
    (Subgroup.centralizer_le (by exact_mod_cast h.P_le))

theorem normal_subgroupOf : (P.subgroupOf L).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.P_le).2 h.le_normalizer_P

theorem isTI : IsTIWithNormalizer ((P : Set G) \ {1}) L := by
  have hne : ((P : Set G) \ {1}).Nonempty := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.P_ne_bot
    exact ⟨x, x.2, by simpa using hx⟩
  have h1 : (1 : G) ∉ (P : Set G) \ {1} := by simp
  have hTI : ∀ g : G, (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) = (P : Set G) \ {1} ∨
      (fun x => g⁻¹ * x * g) '' ((P : Set G) \ {1}) ∩ ((P : Set G) \ {1}) = ∅ := by
    intro g
    by_cases hg : g ∈ L
    · refine Or.inl ?_
      have hg' : g ∈ (L : Set G) := hg
      rw [← h.stabilizer_punctured_eq] at hg'
      exact hg'
    · exact Or.inr (by rw [Set.inter_comm]; exact h.inter_conj_eq_empty g hg)
  have key := isTIWithNormalizer_normalizer hne h1 hTI
  have hLeq : Subgroup.normalizer ((P : Set G) \ {1}) = L := by
    refine SetLike.ext' ?_
    rw [← h.stabilizer_punctured_eq]
    exact Set.ext fun g => mem_normalizer_iff_conjInv_image_eq
  rwa [hLeq] at key

theorem normalizer_punctured_eq : Subgroup.normalizer ((P : Set G) \ {1}) = L := by
  refine SetLike.ext' ?_
  rw [← h.stabilizer_punctured_eq]
  exact Set.ext fun g => mem_normalizer_iff_conjInv_image_eq

theorem normalizer_coe_eq : Subgroup.normalizer ((P : Set G)) = L := by
  rw [← normalizer_sdiff_singleton_one P]; exact h.normalizer_punctured_eq

theorem odd_natCard_L : Odd (Nat.card L) :=
  h.odd_natCard_G.of_dvd_nat (Subgroup.card_subgroup_dvd_card L)

theorem E_le_normalizer_P : E ≤ normalizer (P : Set G) := h.E_le.trans h.le_normalizer_P

theorem natCard_mul_natCard : Nat.card P * Nat.card E = Nat.card L := by
  have key := natCard_sup_mul_natCard_inf_of_le_normalizer (S := P) (T := E) h.E_le_normalizer_P
  rw [h.sup_eq, h.inf_eq_bot] at key
  simpa using key.symm

theorem index_subgroupOf_eq [Finite G] : (P.subgroupOf L).index = Nat.card E := by
  have h1 : Nat.card (P.subgroupOf L) = Nat.card P :=
    Nat.card_congr (subgroupOfEquivOfLe h.P_le).toEquiv
  have h2 := Subgroup.index_mul_card (P.subgroupOf L)
  rw [h1] at h2
  refine Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := P)) ?_
  rw [h2, ← h.natCard_mul_natCard, Nat.mul_comm]

theorem relIndex_mul_natCard_Z : Z.relIndex P * p = Nat.card P := by
  have h1 := Subgroup.index_mul_card ((Z.subgroupOf P))
  rw [Nat.card_congr (subgroupOfEquivOfLe h.Z_le_P).toEquiv, h.natCard_Z] at h1
  exact h1

theorem P_subgroupOf_ne_bot : P.subgroupOf L ≠ ⊥ := by
  intro hbot
  obtain ⟨x, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.P_ne_bot
  have hxm : (⟨(x : G), h.P_le x.2⟩ : ↥L) ∈ P.subgroupOf L := Subgroup.mem_subgroupOf.2 x.2
  rw [hbot, Subgroup.mem_bot] at hxm
  exact hx1 (Subtype.ext (congrArg (fun w : ↥L => (w : G)) hxm))

theorem normalizer_puncturedAmbient_eq :
    Subgroup.normalizer (NormalLinearInduced.puncturedAmbient (P.subgroupOf L) : Set G) = L := by
  rw [puncturedAmbient_subgroupOf_eq h.P_le]; exact h.normalizer_punctured_eq

theorem disjoint_puncturedAmbient :
    ∀ g ∉ L, (NormalLinearInduced.puncturedAmbient (P.subgroupOf L) : Set G)
      ∩ (fun x => g⁻¹ * x * g) ''
        (NormalLinearInduced.puncturedAmbient (P.subgroupOf L) : Set G) = ∅ := by
  intro g hg
  rw [puncturedAmbient_subgroupOf_eq h.P_le]
  exact h.inter_conj_eq_empty g hg

theorem Z_le_centralizer_L : Z ≤ centralizer (L : Set G) := h.Z_le_center.trans inf_le_right

theorem conj_eq_self_of_mem_Z {g : G} (hg : g ∈ L) {w : G} (hw : w ∈ Z) : g * w * g⁻¹ = w := by
  have hc := Subgroup.mem_centralizer_iff.1 (h.Z_le_centralizer_L hw) g hg
  calc g * w * g⁻¹ = (w * g) * g⁻¹ := by rw [← hc]
    _ = w := by group

theorem le_normalizer_Z : L ≤ Subgroup.normalizer (Z : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · have hz' : z ∈ Z := hz
    rw [h.conj_eq_self_of_mem_Z hg hz']
    exact hz'
  · have hz' : g * z * g⁻¹ ∈ Z := hz
    have hkey : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = g * z * g⁻¹ :=
      h.conj_eq_self_of_mem_Z (L.inv_mem hg) hz'
    have heq : z = g * z * g⁻¹ := by
      calc z = g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ := by group
        _ = g * z * g⁻¹ := hkey
    rw [heq]; exact hz'

theorem inf_centralizer_L_eq (z : G) (hz : z ∈ Z) :
    L ⊓ Subgroup.centralizer ({z} : Set G) = L := by
  refine le_antisymm inf_le_left (le_inf le_rfl fun x hx => ?_)
  refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
  have hy' : y = z := by simpa using hy
  subst hy'
  have hc := h.conj_eq_self_of_mem_Z hx hz
  calc y * x = (x * y * x⁻¹) * x := by rw [hc]
    _ = x * y := by group

theorem Z_subgroupOf_le_center : Z.subgroupOf L ≤ Subgroup.center ↥L := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.1
    (h.Z_le_centralizer_L (mem_subgroupOf.1 hz)) (g : G) g.2)

theorem normal_Z_subgroupOf : (Z.subgroupOf L).Normal where
  conj_mem z hz g := by
    have hc := (Subgroup.mem_center_iff.1 (h.Z_subgroupOf_le_center hz)) g
    have hg : g * z * g⁻¹ = z := by rw [hc]; group
    rwa [hg]

theorem Z_subgroupOf_le_commutator_subgroupOf :
    Z.subgroupOf L ≤ ⁅P.subgroupOf L, P.subgroupOf L⁆ := by
  rw [commutator_subgroupOf_eq h.P_le]
  exact Subgroup.subgroupOf_mono L h.Z_le_commutator

theorem Z_subgroupOf_P_le_center :
    ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ≤ Subgroup.center ↥(P.subgroupOf L) := by
  intro z hz
  have hzZ : ((z : ↥L) : G) ∈ Z := Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hz)
  rw [Subgroup.mem_center_iff]
  intro g
  refine Subtype.ext (Subtype.ext ?_)
  have hgP : ((g : ↥L) : G) ∈ P := Subgroup.mem_subgroupOf.1 g.2
  have hc := Subgroup.mem_centralizer_iff.1 (h.Z_le_centralizer_P hzZ) _ hgP
  push_cast
  exact hc

theorem natCard_Z_subgroupOf : Nat.card ↥(Z.subgroupOf L) = p := by
  rw [Nat.card_congr (subgroupOfEquivOfLe h.Z_le).toEquiv]; exact h.natCard_Z

theorem finite_Z_subgroupOf : Finite ↥(Z.subgroupOf L) :=
  Nat.finite_of_card_ne_zero (by rw [h.natCard_Z_subgroupOf]; exact h.prime.pos.ne')

theorem isMulCommutative_Z_subgroupOf : IsMulCommutative ↥(Z.subgroupOf L) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite_Z_subgroupOf
  have := isCyclic_of_prime_card (α := ↥(Z.subgroupOf L)) h.natCard_Z_subgroupOf
  infer_instance

theorem apply_one_eq_one_of_mem_Irr_Z {lam : ↥(Z.subgroupOf L) → ℂ}
    (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) : lam 1 = 1 := by
  have := h.isMulCommutative_Z_subgroupOf
  exact Irr.apply_one_eq_one_of_isMulCommutative hlam

theorem isPGroup_subgroupOf_P : IsPGroup p ↥(P.subgroupOf L) :=
  (IsPGroup.of_card h.natCard_P).comap_of_injective L.subtype L.subtype_injective

theorem isSolvable_subgroupOf_P [Finite G] : Group.IsSolvable ↥(P.subgroupOf L) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite ↥(P.subgroupOf L) := Subtype.finite
  have := h.isPGroup_subgroupOf_P.isNilpotent
  infer_instance

theorem nontrivial_subgroupOf_P : Nontrivial ↥(P.subgroupOf L) :=
  (subgroupOfEquivOfLe h.P_le).toEquiv.nontrivial_congr.2
    ((Subgroup.nontrivial_iff_ne_bot P).2 h.P_ne_bot)

theorem coprime_natCard_subgroupOf :
    (Nat.card ↥(P.subgroupOf L)).Coprime (Nat.card ↥(E.subgroupOf L)) := by
  rw [Nat.card_congr (subgroupOfEquivOfLe h.P_le).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe h.E_le).toEquiv]
  exact h.coprime_natCard

theorem inf_centralizer_le_commutator :
    ∀ u ∈ E, u ≠ 1 → P ⊓ centralizer ({u} : Set G) ≤ (⁅P, P⁆ : Subgroup G) := by
  intro u hu hu1
  rw [h.inf_centralizer_eq u hu hu1]
  exact h.Z_le_commutator

theorem inf_centralizer_subgroupOf_le (u : ↥L) (hu : u ∈ E.subgroupOf L) (hu1 : u ≠ 1) :
    P.subgroupOf L ⊓ centralizer ({u} : Set ↥L) ≤ ⁅P.subgroupOf L, P.subgroupOf L⁆ := by
  intro k hk
  obtain ⟨hkP, hkc⟩ := Subgroup.mem_inf.1 hk
  have hcomm : ((k : G)) * ((u : G)) = ((u : G)) * ((k : G)) := by
    have := congrArg (fun w : ↥L => (w : G)) (Subgroup.mem_centralizer_singleton_iff.1 hkc)
    simpa using this
  rw [commutator_subgroupOf_eq h.P_le]
  refine Subgroup.mem_subgroupOf.2 (h.inf_centralizer_le_commutator (u : G) hu
    (fun hc => hu1 (Subtype.ext hc)) ?_)
  exact Subgroup.mem_inf.2
    ⟨Subgroup.mem_subgroupOf.1 hkP, Subgroup.mem_centralizer_singleton_iff.2 hcomm⟩

theorem isComplement'_subgroupOf : (P.subgroupOf L).IsComplement' (E.subgroupOf L) := by
  have := h.normal_subgroupOf
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ (disjoint_iff.2 ?_) ?_
  · rw [Subgroup.subgroupOf, Subgroup.subgroupOf, ← Subgroup.comap_inf, h.inf_eq_bot]
    simp [Subgroup.ker_subtype]
  · rw [← Subgroup.normal_mul, ← Subgroup.subgroupOf_sup h.P_le h.E_le, h.sup_eq,
      Subgroup.subgroupOf_self]
    simp

theorem indFamLinear_subset_Irr [Fintype ↥L] [Finite G] :
    NormalLinearInduced.indFamLinear (P.subgroupOf L) ⊆ Irr ↥L := by
  have := h.normal_subgroupOf
  have := h.isSolvable_subgroupOf_P
  have := h.nontrivial_subgroupOf_P
  exact indFamLinear_subset_Irr_of_centralizer_le h.isComplement'_subgroupOf
    h.coprime_natCard_subgroupOf (fun u hu hu1 => h.inf_centralizer_subgroupOf_le u hu hu1)

theorem indFamLinear_nonempty [Fintype ↥L] [Finite G] :
    (NormalLinearInduced.indFamLinear (P.subgroupOf L)).Nonempty := by
  have := h.isSolvable_subgroupOf_P
  have := h.nontrivial_subgroupOf_P
  exact _root_.CFSG.FeitThompson.indFamLinear_nonempty

omit h in
theorem star_mem_indFamLinear [Fintype ↥L] {η : ↥L → ℂ}
    (hη : η ∈ NormalLinearInduced.indFamLinear (P.subgroupOf L)) :
    star η ∈ NormalLinearInduced.indFamLinear (P.subgroupOf L) :=
  NormalLinearInduced.conj_mem_indFamLinear _ hη

theorem star_ne_self_of_mem_indFamLinear [Fintype ↥L] [Finite G] {η : ↥L → ℂ}
    (hη : η ∈ NormalLinearInduced.indFamLinear (P.subgroupOf L)) : star η ≠ η :=
  fun he => not_conj_eq_self_of_mem_indFamLinear h.odd_natCard_L h.indFamLinear_subset_Irr hη
    he.symm

omit h in
@[expose] noncomputable def sylowP [Finite G] (hp : Fact p.Prime)
    (h : IsCentralPrimeInduction p a L P E Z) : Sylow p G :=
  Sylow.ofCard P h.sylow_natCard_P

@[simp] theorem coe_sylowP [Finite G] (hp : Fact p.Prime) :
    ((sylowP hp h : Sylow p G) : Subgroup G) = P := rfl

theorem isTINormalCentralSection [Finite G] (hp : Fact p.Prime) :
    IsTINormalCentralSection p (sylowP hp h) L Z (Nat.card L) where
  prime := h.prime
  sylow_ne_bot := by rw [coe_sylowP]; exact h.P_ne_bot
  normalizer_eq := by rw [coe_sylowP]; exact h.normalizer_coe_eq
  odd_natCard := h.odd_natCard_L
  ti := by rw [coe_sylowP]; exact h.inter_conj_eq_empty
  Z_ne_bot := h.Z_ne_bot
  Z_le_center := by rw [coe_sylowP]; exact le_inf h.Z_le_P h.Z_le_centralizer_P
  le_normalizer_Z := h.le_normalizer_Z
  natCard_centralizer_inf_eq := fun z hz _ => by rw [h.inf_centralizer_L_eq z hz]

theorem exists_int_natCard_P_dvd_sub [Fintype G] {ψ : G → ℂ}
    (hψ : ψ ∈ Submodule.span ℤ (Irr G)) (hnorm : cfInner ψ ψ = 1) {b : ℂ}
    (hb : ∀ z ∈ Z, z ≠ 1 → ψ z = b) :
    ∃ A B : ℤ, b = A ∧ ψ 1 = B ∧ (Nat.card P : ℤ) ∣ B - A := by
  have hp : Fact p.Prime := ⟨h.prime⟩
  have hs := h.isTINormalCentralSection hp
  rcases mem_Irr_or_neg_mem_Irr_of_mem_span_Irr_of_cfInner_self_eq_one hψ hnorm with hirr | hneg
  · have := hs.exists_int_dvd_sub hirr hb
    rwa [coe_sylowP] at this
  · have hn' : ∀ z ∈ Z, z ≠ 1 → -(-ψ) z = b := fun z hz hz1 => by
      simp only [Pi.neg_apply, neg_neg]; exact hb z hz hz1
    obtain ⟨A, B, hA, hB, hdvd⟩ := hs.exists_int_dvd_sub_neg hneg hn'
    simp only [Pi.neg_apply, neg_neg] at hB
    rw [coe_sylowP] at hdvd
    exact ⟨A, B, hA, hB, hdvd⟩

theorem natCard_E_dvd_relIndex_commutator_sub_one [Finite G] :
    Nat.card ↥E ∣ (⁅P, P⁆ : Subgroup G).relIndex P - 1 := by
  have hnP := h.normal_subgroupOf
  have hfL : Finite ↥L := Subtype.finite
  have hfK : Finite ↥(P.subgroupOf L) := Subtype.finite
  have hsolv := h.isSolvable_subgroupOf_P
  have hfree : ∀ u : ↥(E.subgroupOf L), u ≠ 1 → MonoidHom.FixedPointFree
      (((abelConjHom (P.subgroupOf L)).comp (E.subgroupOf L).subtype) u) := fun u hu =>
    fixedPointFree_abelConjHom (E := E.subgroupOf L) h.coprime_natCard_subgroupOf u.2
      (h.inf_centralizer_subgroupOf_le (u : ↥L) u.2 (fun hc => hu (Subtype.ext hc)))
  have key := card_dvd_card_sub_one_of_fixedPointFree
    (φ := (abelConjHom (P.subgroupOf L)).comp (E.subgroupOf L).subtype) hfree
  have hAcard : Nat.card ↥(E.subgroupOf L) = Nat.card ↥E :=
    Nat.card_congr (subgroupOfEquivOfLe h.E_le).toEquiv
  have habel : Nat.card (Abelianization ↥(P.subgroupOf L))
      = (⁅P, P⁆ : Subgroup G).relIndex P := by
    have he : ↥(P.subgroupOf L) ≃* ↥P := subgroupOfEquivOfLe h.P_le
    rw [Nat.card_congr (MulEquiv.abelianizationCongr he).toEquiv,
      show ((⁅P, P⁆ : Subgroup G).relIndex P)
        = ((⁅P, P⁆ : Subgroup G).subgroupOf P).index from rfl,
      ← commutator_eq_subgroupOf_commutator, Subgroup.index_eq_card]
    exact Nat.card_congr (Equiv.refl _)
  rwa [hAcard, habel] at key

theorem commutator_lt [Finite G] : (⁅P, P⁆ : Subgroup G) < P := by
  have : Group.IsNilpotent ↥P := isNilpotent_of_natCard_eq_prime_pow h.prime h.natCard_P
  exact commutator_self_lt_self_of_isNilpotent h.P_ne_bot

theorem two_le_relIndex_commutator [Finite G] : 2 ≤ (⁅P, P⁆ : Subgroup G).relIndex P := by
  have hne0 : ((⁅P, P⁆ : Subgroup G).subgroupOf P).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hne1 : ((⁅P, P⁆ : Subgroup G).subgroupOf P).index ≠ 1 := by
    intro h1
    have h3 : P ≤ (⁅P, P⁆ : Subgroup G) :=
      Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 h1)
    exact absurd (le_antisymm h.commutator_lt.le h3) h.commutator_lt.ne
  have hr : (⁅P, P⁆ : Subgroup G).relIndex P = ((⁅P, P⁆ : Subgroup G).subgroupOf P).index := rfl
  omega

theorem natCard_E_lt_relIndex [Finite G] : Nat.card ↥E < Z.relIndex P := by
  have h2 := h.two_le_relIndex_commutator
  have hle : Nat.card ↥E ≤ (⁅P, P⁆ : Subgroup G).relIndex P - 1 :=
    Nat.le_of_dvd (by omega) h.natCard_E_dvd_relIndex_commutator_sub_one
  have hmul : Z.relIndex (⁅P, P⁆ : Subgroup G) * (⁅P, P⁆ : Subgroup G).relIndex P
      = Z.relIndex P :=
    Subgroup.relIndex_mul_relIndex (H := Z) (K := ⁅P, P⁆) (L := P) h.Z_le_commutator
      (Subgroup.commutator_le_self P)
  have hpos : 0 < Z.relIndex (⁅P, P⁆ : Subgroup G) := by
    rcases Nat.eq_zero_or_pos (Z.relIndex (⁅P, P⁆ : Subgroup G)) with hz | hz
    · exact absurd (show Z.relIndex P = 0 from by rw [← hmul, hz, zero_mul])
        Subgroup.index_ne_zero_of_finite
    · exact hz
  calc Nat.card ↥E ≤ (⁅P, P⁆ : Subgroup G).relIndex P - 1 := hle
    _ < (⁅P, P⁆ : Subgroup G).relIndex P := by omega
    _ ≤ Z.relIndex (⁅P, P⁆ : Subgroup G) * (⁅P, P⁆ : Subgroup G).relIndex P :=
        Nat.le_mul_of_pos_left _ hpos
    _ = Z.relIndex P := hmul

end IsCentralPrimeInduction

noncomputable def centralFam (L P : Subgroup G) [Fintype ↥L] : Set (↥L → ℂ) :=
  indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L))

theorem centralFam_eq_indFam (L P : Subgroup G) [Fintype ↥L] :
    centralFam L P = indFam (P.subgroupOf L) (nonprincipalIrr ↥(P.subgroupOf L)) := (rfl)

theorem mem_centralFam [Fintype ↥L] {f : ↥L → ℂ} :
    f ∈ centralFam L P ↔ ∃ θ ∈ nonprincipalIrr ↥(P.subgroupOf L),
      indClassFun (P.subgroupOf L) θ = f := mem_indFam _

theorem indFamLinear_subset_centralFam [Fintype ↥L] :
    indFamLinear (P.subgroupOf L) ⊆ centralFam L P := by
  intro f hf
  obtain ⟨θ, hθ, rfl⟩ := NormalLinearInduced.mem_indFamLinear _ |>.1 hf
  obtain ⟨hθIrr, -, hθne⟩ := NormalLinearInduced.mem_nonprincipalLinearIrr.1 hθ
  exact mem_centralFam.2 ⟨θ, mem_nonprincipalIrr.2 ⟨hθIrr, hθne⟩, rfl⟩

noncomputable def gammaChar (P Z : Subgroup G) {L : Subgroup G} [Fintype ↥L]
    (lam : ↥(Z.subgroupOf L) → ℂ) (η : ↥L → ℂ) : ↥L → ℂ :=
  indClassFun (Z.subgroupOf L) lam - (Z.relIndex P : ℂ) • η

theorem gammaChar_def (P Z : Subgroup G) {L : Subgroup G} [Fintype ↥L]
    (lam : ↥(Z.subgroupOf L) → ℂ) (η : ↥L → ℂ) :
    gammaChar P Z lam η = indClassFun (Z.subgroupOf L) lam - (Z.relIndex P : ℂ) • η := (rfl)

theorem gammaChar_apply_one [Fintype ↥L] (hZP : Z ≤ P) (hPL : P ≤ L)
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam 1 = 1)
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L)) :
    gammaChar P Z lam η 1 = 0 := by
  have hcard : (Nat.card ↥L : ℂ) / (Nat.card ↥(Z.subgroupOf L) : ℂ)
      = ((Z.subgroupOf L).index : ℂ) := by
    rw [eq_comm, eq_div_iff (by
      exact_mod_cast (Nat.card_pos (α := ↥(Z.subgroupOf L))).ne')]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℂ) (Subgroup.index_mul_card (Z.subgroupOf L))
  have hindex : (Z.subgroupOf L).index = Z.relIndex P * (P.subgroupOf L).index := by
    rw [← Subgroup.relIndex_subgroupOf hPL,
      Subgroup.relIndex_mul_index (Subgroup.subgroupOf_mono L hZP)]
  simp only [gammaChar, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, indClassFun_one, hlam, mul_one,
    hcard, apply_one_of_mem_indFamLinear _ hη, hindex]
  push_cast
  ring

section Pairings

variable [Fintype G] [Fintype ↥L] [Fintype ↥(Z.subgroupOf L)]

omit [Fintype G] [Fintype ↥(Z.subgroupOf L)] in
theorem gammaChar_mem_charSpanZero [(P.subgroupOf L).Normal] (hZP : Z ≤ P) (hPL : P ≤ L)
    (hZPc : ((Z.subgroupOf L).subgroupOf (P.subgroupOf L)) ≤ Subgroup.center ↥(P.subgroupOf L))
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) (hlam1 : lam ≠ 1)
    (hlamdeg : lam 1 = 1)
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L)) :
    gammaChar P Z lam η ∈ charSpanZero (centralFam L P) := by
  refine mem_charSpanZero.2 ⟨?_, gammaChar_apply_one hZP hPL hlamdeg hη⟩
  rw [gammaChar_def, centralFam_eq_indFam]
  refine Submodule.sub_mem _
    (indClassFun_mem_span_indFam_nonprincipalIrr (Subgroup.subgroupOf_mono L hZP) hZPc hlam hlam1)
    ?_
  rw [show ((Z.relIndex P : ℂ) • η) = (Z.relIndex P : ℤ) • η from by
    rw [← Int.cast_natCast (R := ℂ) (Z.relIndex P), Int.cast_smul_eq_zsmul]]
  exact Submodule.smul_mem _ _ (Submodule.subset_span
    (by rw [← centralFam_eq_indFam]; exact indFamLinear_subset_centralFam hη))

omit [Fintype G] [Fintype ↥(Z.subgroupOf L)] in
theorem cfInner_indClassFun_indFamLinear_eq_zero [(P.subgroupOf L).Normal]
    (hZP' : Z.subgroupOf L ≤ ⁅P.subgroupOf L, P.subgroupOf L⁆)
    (hYIrr : indFamLinear (P.subgroupOf L) ⊆ Irr ↥L)
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) (hlam1 : lam ≠ 1)
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L)) :
    cfInner (indClassFun (Z.subgroupOf L) lam) η = 0 := by
  have : Fintype ↥(Z.subgroupOf L) := Fintype.ofFinite _
  rw [cfInner_indClassFun _ _ (Irr_subset_classFun (hYIrr hη))]
  have hres : resClassFun (Z.subgroupOf L) η = (η 1) • (1 : ↥(Z.subgroupOf L) → ℂ) := by
    funext z
    rw [resClassFun_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    exact NormalLinearInduced.apply_eq_apply_one_of_mem_commutator _ hη (hZP' z.2)
  rw [hres, cfInner_smul_right, cfInner_eq_zero_of_mem_Irr hlam one_mem_Irr hlam1, mul_zero]

omit [Fintype G] [Fintype ↥(Z.subgroupOf L)] in
theorem cfInner_gammaChar_self [(P.subgroupOf L).Normal] [(Z.subgroupOf L).Normal]
    (hZP : Z ≤ P) (hPL : P ≤ L)
    (hZcL : Z.subgroupOf L ≤ Subgroup.center ↥L)
    (hZP' : Z.subgroupOf L ≤ ⁅P.subgroupOf L, P.subgroupOf L⁆)
    (hYIrr : indFamLinear (P.subgroupOf L) ⊆ Irr ↥L)
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) (hlam1 : lam ≠ 1)
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L)) :
    cfInner (gammaChar P Z lam η) (gammaChar P Z lam η)
      = ((P.subgroupOf L).index : ℂ) * (Z.relIndex P : ℂ) + (Z.relIndex P : ℂ) ^ 2 := by
  have : Fintype ↥(Z.subgroupOf L) := Fintype.ofFinite _
  have hnorm : cfInner (indClassFun (Z.subgroupOf L) lam) (indClassFun (Z.subgroupOf L) lam)
      = ((Z.subgroupOf L).index : ℂ) := by
    rw [cfInner_self_indClassFun _ hlam, inertiaGroup_eq_top_of_le_center _ hZcL lam,
      Subgroup.relIndex_top_right]
  have hcross : cfInner (indClassFun (Z.subgroupOf L) lam) η = 0 :=
    cfInner_indClassFun_indFamLinear_eq_zero hZP' hYIrr hlam hlam1 hη
  have hcross' : cfInner η (indClassFun (Z.subgroupOf L) lam) = 0 := by
    rw [← conj_cfInner, hcross, map_zero]
  have hηη : cfInner η η = 1 := cfInner_self_of_mem_Irr (hYIrr hη)
  have hindex : (Z.subgroupOf L).index = Z.relIndex P * (P.subgroupOf L).index := by
    rw [← Subgroup.relIndex_subgroupOf hPL, Subgroup.relIndex_mul_index
      (Subgroup.subgroupOf_mono L hZP)]
  rw [gammaChar_def, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
    cfInner_smul_left, cfInner_smul_right, cfInner_smul_right, hnorm, hcross, hcross', hηη,
    hindex]
  simp only [map_natCast]
  push_cast
  ring

omit [Fintype G] [Fintype ↥(Z.subgroupOf L)] in
theorem cfInner_gammaChar_sub [(P.subgroupOf L).Normal]
    (hZP' : Z.subgroupOf L ≤ ⁅P.subgroupOf L, P.subgroupOf L⁆)
    (hYIrr : indFamLinear (P.subgroupOf L) ⊆ Irr ↥L)
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) (hlam1 : lam ≠ 1)
    {η ψ : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L))
    (hψ : ψ ∈ indFamLinear (P.subgroupOf L)) (hne : ψ ≠ η) :
    cfInner (gammaChar P Z lam η) (ψ - η) = (Z.relIndex P : ℂ) := by
  have h1 : cfInner (indClassFun (Z.subgroupOf L) lam) ψ = 0 :=
    cfInner_indClassFun_indFamLinear_eq_zero hZP' hYIrr hlam hlam1 hψ
  have h2 : cfInner (indClassFun (Z.subgroupOf L) lam) η = 0 :=
    cfInner_indClassFun_indFamLinear_eq_zero hZP' hYIrr hlam hlam1 hη
  have h3 : cfInner η ψ = 0 := cfInner_eq_zero_of_mem_Irr (hYIrr hη) (hYIrr hψ) (Ne.symm hne)
  have h4 : cfInner η η = 1 := cfInner_self_of_mem_Irr (hYIrr hη)
  rw [gammaChar_def, cfInner_sub_left, cfInner_sub_right, cfInner_sub_right, cfInner_smul_left,
    cfInner_smul_left, h1, h2, h3, h4]
  ring

theorem cfInner_indClassFun_coherentVal_sub
    (hTI : IsTIWithNormalizer ((P : Set G) \ {1}) L) (hPL : P ≤ L)
    [(P.subgroupOf L).Normal]
    (ν : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G)
    (hν0 : ∀ f : charSpanZero (indFamLinear (P.subgroupOf L)),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ))
    {f : ↥L → ℂ} (hf : f ∈ dadeZDomain L ((P : Set G) \ {1}))
    {η ψ : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L))
    (hψ : ψ ∈ indFamLinear (P.subgroupOf L)) :
    cfInner (indClassFun L f) (coherentVal ν ⟨ψ, hψ⟩)
        - cfInner (indClassFun L f) (coherentVal ν ⟨η, hη⟩)
      = cfInner f (ψ - η) := by
  have hmem : ψ - η ∈ charSpanZero (indFamLinear (P.subgroupOf L)) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hψ)
      (Submodule.subset_span hη), ?_⟩
    rw [Pi.sub_apply, NormalLinearInduced.apply_one_of_mem_indFamLinear _ hψ,
      NormalLinearInduced.apply_one_of_mem_indFamLinear _ hη, sub_self]
  have hincl : Submodule.inclusion (charSpanZero_le (indFamLinear (P.subgroupOf L))) ⟨_, hmem⟩
      = (⟨ψ, Submodule.subset_span hψ⟩ :
          Submodule.span ℤ (indFamLinear (P.subgroupOf L)))
        - ⟨η, Submodule.subset_span hη⟩ := Subtype.ext rfl
  have hνsub := hν0 ⟨_, hmem⟩
  rw [hincl, map_sub] at hνsub
  have hcoe : ((ν ⟨ψ, Submodule.subset_span hψ⟩ : virtualChars G) : G → ℂ)
      - ((ν ⟨η, Submodule.subset_span hη⟩ : virtualChars G) : G → ℂ)
      = indClassFun L (ψ - η) := by
    rw [← hνsub]; rfl
  rw [← cfInner_sub_right]
  simp only [coherentVal_apply]
  rw [hcoe]
  exact hTI.cfInner_indClassFun (mem_dadeDomain_of_mem_dadeZDomain hf)
    (mem_dadeDomain_of_mem_dadeZDomain (mem_dadeZDomain_of_mem_charSpanZero_of_subset_indFam hPL
      (NormalLinearInduced.indFamLinear_subset_indFam_Irr _) hmem))

set_option linter.unusedFintypeInType false in
theorem cfInner_indClassFun_gammaChar_coherentVal (hZL : Z ≤ L)
    {lam : ↥(Z.subgroupOf L) → ℂ} (hlam : lam ∈ Irr ↥(Z.subgroupOf L)) (hlam1 : lam ≠ 1)
    (hlamdeg : lam 1 = 1)
    {ν : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G}
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L))
    {b : ℂ} (hb : ∀ z ∈ Z, z ≠ 1 → coherentVal ν ⟨η, hη⟩ z = b) :
    cfInner (indClassFun L (gammaChar P Z lam η)) (coherentVal ν ⟨η, hη⟩)
      = (Nat.card ↥Z : ℂ)⁻¹ * (starRingEnd ℂ) (coherentVal ν ⟨η, hη⟩ 1 - b)
        - (Z.relIndex P : ℂ) * cfInner η (resClassFun L (coherentVal ν ⟨η, hη⟩)) := by
  have hψcf : coherentVal ν ⟨η, hη⟩ ∈ classFun G :=
    virtualChars_le_classFun (coherentVal_mem_virtualChars ν ⟨η, hη⟩)
  rw [cfInner_indClassFun _ _ hψcf, gammaChar_def, cfInner_sub_left, cfInner_smul_left,
    cfInner_indClassFun_resClassFun_eq hZL hlam hlam1 hlamdeg hψcf hb]

omit [Fintype ↥(Z.subgroupOf L)] in
theorem isOrthogonal_add_smul_coherentVal
    (hYIrr : indFamLinear (P.subgroupOf L) ⊆ Irr ↥L)
    {τ : charSpanZero (indFamLinear (P.subgroupOf L)) →+ virtualChars G}
    {μ : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G}
    (hμ : IsCoherentWith (indFamLinear (P.subgroupOf L)) τ μ)
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L)) {r : ℂ} {d : G → ℂ}
    (hd : ∀ ξ : indFamLinear (P.subgroupOf L), cfInner d (coherentVal μ ξ)
      = -r * (if ξ = (⟨η, hη⟩ : indFamLinear (P.subgroupOf L)) then 1 else 0))
    {ψ : ↥L → ℂ} (hψ : ψ ∈ indFamLinear (P.subgroupOf L)) :
    IsOrthogonal (d + r • coherentVal μ ⟨η, hη⟩) (coherentVal μ ⟨ψ, hψ⟩) := by
  classical
  rw [isOrthogonal_iff, cfInner_add_left, cfInner_smul_left, hd ⟨ψ, hψ⟩,
    cfInner_coherentVal_coherentVal hYIrr hμ]
  by_cases hc : (⟨ψ, hψ⟩ : indFamLinear (P.subgroupOf L)) = ⟨η, hη⟩
  · rw [if_pos hc, if_pos (show (⟨η, hη⟩ : indFamLinear (P.subgroupOf L)) = ⟨ψ, hψ⟩ from hc.symm)]
    ring
  · rw [if_neg hc, if_neg (Ne.symm hc)]
    ring

end Pairings

theorem exists_oriented_projection [Fintype G] [Fintype ↥L]
    (h : IsCentralPrimeInduction p a L P E Z)
    (ν : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G)
    (hνinner : ∀ f g : Submodule.span ℤ (indFamLinear (P.subgroupOf L)),
      cfInner ((ν f : virtualChars G) : G → ℂ) ((ν g : virtualChars G) : G → ℂ)
        = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ))
    (hν0 : ∀ f : charSpanZero (indFamLinear (P.subgroupOf L)),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ))
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear (P.subgroupOf L)) :
    ∃ μ : Submodule.span ℤ (indFamLinear (P.subgroupOf L)) →+ virtualChars G,
      (∀ f g : Submodule.span ℤ (indFamLinear (P.subgroupOf L)),
        cfInner ((μ f : virtualChars G) : G → ℂ) ((μ g : virtualChars G) : G → ℂ)
          = cfInner (f : ↥L → ℂ) (g : ↥L → ℂ)) ∧
      (∀ f : charSpanZero (indFamLinear (P.subgroupOf L)),
        ((μ (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
          = indClassFun L (f : ↥L → ℂ)) ∧
      Submodule.span ℂ (Set.range (coherentVal μ))
          = Submodule.span ℂ (Set.range (coherentVal ν)) ∧
      (μ = ν ∨ ∃ hbar : star η ∈ indFamLinear (P.subgroupOf L),
        indFamLinear (P.subgroupOf L) = {η, star η} ∧
        coherentVal μ ⟨η, hη⟩ = -coherentVal ν ⟨star η, hbar⟩ ∧
        coherentVal μ ⟨star η, hbar⟩ = -coherentVal ν ⟨η, hη⟩) ∧
      ∀ lam ∈ Irr ↥(Z.subgroupOf L), lam ≠ 1 →
        gammaChar P Z lam η ∈ charSpanZero (centralFam L P) ∧
        cfInner (indClassFun L (gammaChar P Z lam η))
            (indClassFun L (gammaChar P Z lam η))
          = ((Nat.card E : ℂ) * (Z.relIndex P : ℂ) + (Z.relIndex P : ℂ) ^ 2) ∧
        ∀ ψ : ↥L → ℂ, ∀ hψ : ψ ∈ indFamLinear (P.subgroupOf L),
          IsOrthogonal (indClassFun L (gammaChar P Z lam η)
              + (Z.relIndex P : ℂ) • coherentVal μ ⟨η, hη⟩)
            (coherentVal μ ⟨ψ, hψ⟩) := by
  classical
  have hp : Fact p.Prime := ⟨h.prime⟩
  have hPn := h.normal_subgroupOf
  have hZn := IsCentralPrimeInduction.normal_Z_subgroupOf h
  have hZfin := IsCentralPrimeInduction.finite_Z_subgroupOf h
  have hZfint : Fintype ↥(Z.subgroupOf L) := Fintype.ofFinite _
  have hYIrr := IsCentralPrimeInduction.indFamLinear_subset_Irr h
  have hYind := NormalLinearInduced.indFamLinear_subset_indFam_Irr (P.subgroupOf L)
  have hν : IsCoherentWith (indFamLinear (P.subgroupOf L))
      (tiIndCharSpanZeroHom h.isTI hYind hYIrr) ν :=
    ⟨hνinner, fun f => Subtype.ext (by rw [coe_tiIndCharSpanZeroHom]; exact hν0 f)⟩
  have hηbar : star η ∈ indFamLinear (P.subgroupOf L) :=
    IsCentralPrimeInduction.star_mem_indFamLinear hη
  have hηbarne : star η ≠ η := IsCentralPrimeInduction.star_ne_self_of_mem_indFamLinear h hη
  have hdeg : ∀ ξ ∈ indFamLinear (P.subgroupOf L), ξ 1 = η 1 := fun ξ hξ => by
    rw [apply_one_of_mem_indFamLinear _ hξ, apply_one_of_mem_indFamLinear _ hη]
  set ψ₀ := coherentVal ν ⟨η, hη⟩ with hψ₀def
  have hψ₀norm : cfInner ψ₀ ψ₀ = 1 := by
    simp only [hψ₀def, coherentVal_apply]
    rw [hνinner]
    exact cfInner_self_of_mem_Irr (hYIrr hη)
  have hψ₀span : ψ₀ ∈ Submodule.span ℤ (Irr G) :=
    mem_span_Irr_of_mem_virtualChars (coherentVal_mem_virtualChars ν ⟨η, hη⟩)
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Z, z ≠ 1 := by
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 h.Z_ne_bot
    exact ⟨x, x.2, fun hc => hx (Subtype.ext hc)⟩
  have hb : ∀ z ∈ Z, z ≠ 1 → ψ₀ z = ψ₀ z₀ := by
    intro z hz hz1
    exact NormalLinearInduced.coherentVal_apply_eq_of_mem_prime_subgroup_commutator
      (ν := ν) (Z := Z.subgroupOf L) h.odd_natCard_G
      (IsCentralPrimeInduction.P_subgroupOf_ne_bot h)
      (IsCentralPrimeInduction.normalizer_puncturedAmbient_eq h)
      (IsCentralPrimeInduction.disjoint_puncturedAmbient h) h.prime
      (IsCentralPrimeInduction.natCard_Z_subgroupOf h)
      (IsCentralPrimeInduction.Z_subgroupOf_le_commutator_subgroupOf h)
      (IsCentralPrimeInduction.indFamLinear_nonempty h) hYIrr hνinner hν0 hη
      (z := ⟨z, h.Z_le hz⟩) (z₀ := ⟨z₀, h.Z_le hz₀⟩) (mem_subgroupOf.2 hz)
      (fun hc => hz1 (congrArg (fun w : ↥L => (w : G)) hc))
      (mem_subgroupOf.2 hz₀) (fun hc => hz₀1 (congrArg (fun w : ↥L => (w : G)) hc))
  obtain ⟨A, B, hA, hB, hdvd⟩ :=
    IsCentralPrimeInduction.exists_int_natCard_P_dvd_sub h hψ₀span hψ₀norm hb
  obtain ⟨c, hc⟩ : ∃ c : ℤ, cfInner η (resClassFun L ψ₀) = (c : ℂ) :=
    exists_int_cfInner_of_mem_span_Irr (Submodule.subset_span (hYIrr hη))
      (resClassFun_mem_span_Irr L hψ₀span)
  obtain ⟨t, ht⟩ := hdvd
  have hpne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 h.prime.pos.ne'
  have hPcard : Z.relIndex P * p = Nat.card P := IsCentralPrimeInduction.relIndex_mul_natCard_Z h
  have hγmem : ∀ lam ∈ Irr ↥(Z.subgroupOf L), lam ≠ 1 →
      gammaChar P Z lam η ∈ charSpanZero (centralFam L P) := fun lam hlam hlam1 =>
    gammaChar_mem_charSpanZero h.Z_le_P h.P_le
      (IsCentralPrimeInduction.Z_subgroupOf_P_le_center h) hlam hlam1
      (IsCentralPrimeInduction.apply_one_eq_one_of_mem_Irr_Z h hlam) hη
  have hSind : centralFam L P ⊆ indFam (P.subgroupOf L) (Irr ↥(P.subgroupOf L)) := by
    rw [centralFam_eq_indFam]; exact indFam_mono _ nonprincipalIrr_subset_Irr
  have hγZ : ∀ lam ∈ Irr ↥(Z.subgroupOf L), lam ≠ 1 →
      gammaChar P Z lam η ∈ dadeZDomain L ((P : Set G) \ {1}) := fun lam hlam hlam1 =>
    mem_dadeZDomain_of_mem_charSpanZero_of_subset_indFam h.P_le hSind (hγmem lam hlam hlam1)
  have hγnorm : ∀ lam ∈ Irr ↥(Z.subgroupOf L), lam ≠ 1 →
      cfInner (indClassFun L (gammaChar P Z lam η)) (indClassFun L (gammaChar P Z lam η))
        = ((Nat.card E : ℂ) * (Z.relIndex P : ℂ) + (Z.relIndex P : ℂ) ^ 2) := by
    intro lam hlam hlam1
    rw [h.isTI.cfInner_indClassFun
      (mem_dadeDomain_of_mem_dadeZDomain (hγZ lam hlam hlam1))
      (mem_dadeDomain_of_mem_dadeZDomain (hγZ lam hlam hlam1)),
      cfInner_gammaChar_self h.Z_le_P h.P_le (IsCentralPrimeInduction.Z_subgroupOf_le_center h)
        (IsCentralPrimeInduction.Z_subgroupOf_le_commutator_subgroupOf h) hYIrr hlam hlam1 hη,
      IsCentralPrimeInduction.index_subgroupOf_eq h]
  have hcoeff : ∀ lam ∈ Irr ↥(Z.subgroupOf L), lam ≠ 1 →
      ∀ ξ : indFamLinear (P.subgroupOf L),
        cfInner (indClassFun L (gammaChar P Z lam η)) (coherentVal ν ξ)
          = (Z.relIndex P : ℂ) * (((t - c + 1 : ℤ) : ℂ)
              - if ξ = (⟨η, hη⟩ : indFamLinear (P.subgroupOf L)) then 1 else 0) := by
    intro lam hlam hlam1 ξ
    have hlamdeg := IsCentralPrimeInduction.apply_one_eq_one_of_mem_Irr_Z h hlam
    have hval : cfInner (indClassFun L (gammaChar P Z lam η)) ψ₀
        = (Z.relIndex P : ℂ) * (((t - c + 1 : ℤ) : ℂ) - 1) := by
      rw [cfInner_indClassFun_gammaChar_coherentVal h.Z_le hlam hlam1 hlamdeg hη
        (b := ψ₀ z₀) hb, hc, show coherentVal ν ⟨η, hη⟩ 1 = ψ₀ 1 from rfl, hB, hA]
      have hZcard : (Nat.card ↥Z : ℂ) = (p : ℂ) := by rw [h.natCard_Z]
      have hBA : (B : ℂ) - (A : ℂ) = (Z.relIndex P : ℂ) * (p : ℂ) * (t : ℂ) := by
        have h2 : ((B - A : ℤ) : ℂ) = (((Nat.card P : ℕ) : ℤ) * t : ℤ) := by rw [ht]
        push_cast at h2
        rw [← hPcard] at h2
        push_cast at h2
        linear_combination h2
      rw [hZcard, show (starRingEnd ℂ) ((B : ℂ) - (A : ℂ)) = (B : ℂ) - (A : ℂ) from by
        rw [map_sub]; norm_num, hBA]
      push_cast
      field_simp
      ring
    by_cases hcase : ξ = (⟨η, hη⟩ : indFamLinear (P.subgroupOf L))
    · rw [if_pos hcase, hcase, hψ₀def] at *
      exact hval
    · rw [if_neg hcase]
      have hne : (ξ : ↥L → ℂ) ≠ η := fun he => hcase (Subtype.ext he)
      have hdiff := cfInner_indClassFun_coherentVal_sub h.isTI h.P_le ν hν0
        (hγZ lam hlam hlam1) hη ξ.2
      rw [cfInner_gammaChar_sub (IsCentralPrimeInduction.Z_subgroupOf_le_commutator_subgroupOf h)
        hYIrr hlam hlam1 hη ξ.2 hne] at hdiff
      rw [show (⟨(ξ : ↥L → ℂ), ξ.2⟩ : indFamLinear (P.subgroupOf L)) = ξ from rfl,
        show coherentVal ν ⟨η, hη⟩ = ψ₀ from rfl, hval] at hdiff
      rw [show cfInner (indClassFun L (gammaChar P Z lam η)) (coherentVal ν ξ)
          = (Z.relIndex P : ℂ) * (((t - c + 1 : ℤ) : ℂ) - 1) + (Z.relIndex P : ℂ) from by
        linear_combination hdiff]
      ring
  obtain ⟨lam₀, hlam₀, hlam₀1⟩ : ∃ lam ∈ Irr ↥(Z.subgroupOf L), lam ≠ 1 := by
    have hnt : Nontrivial ↥(Z.subgroupOf L) :=
      (Subgroup.nontrivial_iff_ne_bot _).2 fun hbot => by
        have hcard : Nat.card ↥(Z.subgroupOf L) = 1 := by rw [hbot]; exact Subgroup.card_bot
        rw [IsCentralPrimeInduction.natCard_Z_subgroupOf h] at hcard
        exact h.prime.one_lt.ne' hcard
    have hsolv : Group.IsSolvable ↥(Z.subgroupOf L) := by
      have := IsCentralPrimeInduction.isMulCommutative_Z_subgroupOf h
      exact isSolvable_of_isMulCommutative
    obtain ⟨lam, hlam, -, hlamne⟩ :=
      exists_mem_Irr_apply_one_eq_one_and_ne_one ↥(Z.subgroupOf L)
    exact ⟨lam, hlam, hlamne⟩
  have hrpos : (0 : ℤ) < (Z.relIndex P : ℤ) :=
    Int.natCast_pos.2 (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
  have hNlt : ((Nat.card E * Z.relIndex P + Z.relIndex P ^ 2 : ℕ) : ℤ)
      < 2 * (Z.relIndex P : ℤ) ^ 2 := by
    have := IsCentralPrimeInduction.natCard_E_lt_relIndex h
    push_cast
    nlinarith [hrpos]
  obtain ⟨μ, hμ, hspan, halt, hor⟩ :=
    SibleyLinearOrientation.exists_isCoherentWith_forall_cfInner_eq_neg_ite hYIrr
      (NormalLinearInduced.finite_indFamLinear _) hν hη hηbar hηbarne hdeg
      (δ := indClassFun L (gammaChar P Z lam₀ η)) (c := (Z.relIndex P : ℤ))
      (k := t - c + 1) (N := ((Nat.card E * Z.relIndex P + Z.relIndex P ^ 2 : ℕ) : ℤ))
      hrpos hNlt
      (by rw [hγnorm lam₀ hlam₀ hlam₀1]; push_cast; ring)
      (by
        intro ξ
        rw [hcoeff lam₀ hlam₀ hlam₀1 ξ]
        push_cast
        ring)
  refine ⟨μ, hμ.inner_eq, fun f => by rw [hμ.eq_on_zero f, coe_tiIndCharSpanZeroHom], hspan, ?_,
    fun lam hlam hlam1 => ⟨hγmem lam hlam hlam1, hγnorm lam hlam hlam1, fun ψ hψ => ?_⟩⟩
  · rcases halt with hμν | ⟨hYeq, h1, h2⟩
    · exact Or.inl hμν
    · exact Or.inr ⟨hηbar, by rw [hYeq, Set.pair_comm], h1, h2⟩
  · refine isOrthogonal_add_smul_coherentVal hYIrr hμ hη (fun ξ => ?_) hψ
    have := hor (indClassFun L (gammaChar P Z lam η))
      (fun ξ' => by rw [hcoeff lam hlam hlam1 ξ']; push_cast; ring) ξ
    rw [this]
    push_cast
    ring

end CentralPrimeInduction

end CFSG.FeitThompson
