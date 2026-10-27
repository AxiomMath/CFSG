module

public import CFSG.FeitThompson.Representations.CentralSectionClassProductDivisibility
public import CFSG.FeitThompson.Representations.CommonClassScaledQuadraticCongruence
import CFSG.FeitThompson.Representations.CommonClassLinearCharacterCongruence
import CFSG.FeitThompson.Representations.ConstantValuePuncturedSubgroupInteger

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

variable {G : Type*} [Group G]

noncomputable def classesMeetingFinset [Finite G] (s : Set G) : Finset (ConjClasses G) :=
  (Set.toFinite (classesMeeting s)).toFinset

@[simp]
theorem mem_classesMeetingFinset [Finite G] {s : Set G} {K : ConjClasses G} :
    K ∈ classesMeetingFinset s ↔ K ∈ classesMeeting s := Set.Finite.mem_toFinset _

@[simp]
theorem coe_classesMeetingFinset [Finite G] (s : Set G) :
    (classesMeetingFinset s : Set (ConjClasses G)) = classesMeeting s :=
  Set.Finite.coe_toFinset _

theorem carrier_mk_eq_setOf_isConj (z : G) :
    (ConjClasses.mk z).carrier = {g : G | IsConj g z} := by
  ext g
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

theorem one_notMem_classesMeeting_sdiff_one (s : Set G) :
    (1 : ConjClasses G) ∉ classesMeeting (s \ {1}) := by
  intro hmem
  obtain ⟨g, ⟨-, hg1⟩, hgK⟩ := mem_classesMeeting.1 hmem
  exact hg1 (isConj_one_right.1 (ConjClasses.mk_eq_mk_iff_isConj.1 hgK).symm)

theorem notMem_classesMeeting_of_notMem_sdiff_one {s : Set G} {K : ConjClasses G}
    (hK : K ∉ classesMeeting (s \ {1})) (hK1 : K ≠ 1) : K ∉ classesMeeting s := by
  intro hmem
  obtain ⟨g, hg, hgK⟩ := mem_classesMeeting.1 hmem
  rcases eq_or_ne g 1 with rfl | hg1
  · exact hK1 hgK.symm
  · exact hK (mem_classesMeeting.2 ⟨g, ⟨hg, hg1⟩, hgK⟩)

namespace IsTINormalCentralSection

variable {p : ℕ} {P : Sylow p G} {L Z : Subgroup G} {h : ℕ}
  (hs : IsTINormalCentralSection p P L Z h)
include hs

section Finite

variable [Finite G]

theorem natCard_carrier_eq_of_mem_classesMeeting {M : ConjClasses G}
    (hM : M ∈ classesMeeting ((Z : Set G) \ {1})) : Nat.card M.carrier = Nat.card G / h := by
  obtain ⟨z, ⟨hz, hz1⟩, rfl⟩ := mem_classesMeeting.1 hM
  rw [carrier_mk_eq_setOf_isConj]
  exact hs.natCard_setOf_isConj_eq hz (by simpa using hz1)

theorem sub_mem_algIntegerMultiples {φ : G → ℂ} (hφ : φ ∈ Irr G) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → φ z = c) :
    c - φ 1 ∈ algIntegerMultiples ((Nat.card (P : Subgroup G) : ℕ) : ℂ) := by
  classical
  have _ : Fintype G := Fintype.ofFinite G
  set t : ℕ := Nat.card (P : Subgroup G)
  set I : Finset (ConjClasses G) := classesMeetingFinset ((Z : Set G) \ {1})
  have hmemI : ∀ M : ConjClasses G, M ∈ I ↔ M ∈ classesMeeting ((Z : Set G) \ {1}) := fun _ =>
    mem_classesMeetingFinset
  have hI1 : (1 : ConjClasses G) ∉ I := fun hm =>
    one_notMem_classesMeeting_sdiff_one (Z : Set G) ((hmemI _).1 hm)
  have hcard : ∀ M ∈ I, Nat.card M.carrier = Nat.card G / h := fun M hM =>
    hs.natCard_carrier_eq_of_mem_classesMeeting ((hmemI M).1 hM)
  have hdvd : ∀ K ∈ I, ∀ L' ∈ I, ∀ M : ConjClasses G, M ∉ I → M ≠ 1 →
      t ∣ classStructureConstant K L' M * Nat.card M.carrier := fun K hK L' hL' M hM hM1 =>
    hs.natCard_sylow_dvd_classStructureConstant_mul ((hmemI K).1 hK) ((hmemI L').1 hL')
      (notMem_classesMeeting_of_notMem_sdiff_one (fun hcon => hM ((hmemI M).2 hcon)) hM1)
  obtain ⟨z, hz, hz1⟩ := hs.exists_mem_Z_ne_one
  have hK : ConjClasses.mk z ∈ I :=
    (hmemI _).2 (mem_classesMeeting_mk ⟨hz, by simpa using hz1⟩)
  have hL : ConjClasses.mk z⁻¹ ∈ I :=
    (hmemI _).2 (mem_classesMeeting_mk ⟨Z.inv_mem hz, by simpa using hz1⟩)
  have hKL : ConjClasses.mk z ≠ ConjClasses.mk z⁻¹ := fun hcon =>
    hs.not_isConj_inv hz hz1 (ConjClasses.mk_eq_mk_iff_isConj.1 hcon)
  have hcI : ∀ x : G, ConjClasses.mk x ∈ I → φ x = c := by
    intro x hx
    obtain ⟨w, ⟨hw, hw1⟩, hwx⟩ := mem_classesMeeting.1 ((hmemI _).1 hx)
    rw [← classFun.apply_eq_of_isConj (Irr_subset_classFun hφ)
      (ConjClasses.mk_eq_mk_iff_isConj.1 hwx)]
    exact hc w hw (by simpa using hw1)
  have hcong := Irr.classStructureConstantDiffSum_mul_smodEq hφ hs.coprime_n_t hI1 hcard hdvd hcI
    hK hL (carrier_mk_inv z) hKL
  obtain ⟨k, hk⟩ := dvd_classStructureConstantDiffSum_sub_one (t := t) hs.coprime_n_t hI1 hcard
    hdvd hK hL (carrier_mk_inv z) hKL
  set B : ℤ := classStructureConstantDiffSum I (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
  have hcint : IsIntegral ℤ c :=
    hcI z hK ▸ isIntegral_apply_of_mem_span_Irr (Submodule.subset_span hφ) z
  have h1 : (B : ℂ) * c - φ 1 ∈ algIntegerMultiples ((t : ℕ) : ℂ) := SModEq.sub_mem.1 hcong
  have h2 : (B : ℂ) * c - c ∈ algIntegerMultiples ((t : ℕ) : ℂ) := by
    have hBc : (B : ℂ) * c - c = (t : ℂ) * ((k : ℂ) * c) := by
      have hh : ((B - 1 : ℤ) : ℂ) = ((t * k : ℤ) : ℂ) := by rw [hk]
      push_cast at hh
      linear_combination c * hh
    rw [hBc]
    exact mul_mem_algIntegerMultiples _ ((isIntegral_intCast k).mul hcint)
  simpa using Submodule.sub_mem _ h1 h2

theorem exists_int_of_eq_on_punctured {φ : G → ℂ} (hφ : φ ∈ Irr G) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → φ z = c) : ∃ a : ℤ, c = a :=
  exists_int_of_eq_on_punctured_subgroup hs.Z_ne_bot (Submodule.subset_span hφ) hc

theorem natCard_sylow_dvd_sub {φ : G → ℂ} (hφ : φ ∈ Irr G) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → φ z = c) {a b : ℤ} (ha : c = a) (hb : φ 1 = b) :
    (Nat.card (P : Subgroup G) : ℤ) ∣ b - a := by
  have hmem := hs.sub_mem_algIntegerMultiples hφ hc
  rw [ha, hb] at hmem
  have hmem' : ((a - b : ℤ) : ℂ) ∈ algIntegerMultiples ((Nat.card (P : Subgroup G) : ℕ) : ℂ) := by
    push_cast
    exact hmem
  simpa using (intCast_dvd_of_mem_algIntegerMultiples hmem').neg_right

theorem exists_int_dvd_sub {φ : G → ℂ} (hφ : φ ∈ Irr G) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → φ z = c) :
    ∃ a b : ℤ, c = a ∧ φ 1 = b ∧ (Nat.card (P : Subgroup G) : ℤ) ∣ b - a := by
  obtain ⟨a, ha⟩ := hs.exists_int_of_eq_on_punctured hφ hc
  obtain ⟨b, hb⟩ := exists_int_apply_one_of_mem_span_Irr (Submodule.subset_span hφ)
  exact ⟨a, b, ha, hb, hs.natCard_sylow_dvd_sub hφ hc ha hb⟩

theorem exists_int_dvd_sub_neg {φ : G → ℂ} (hφ : φ ∈ Irr G) {c : ℂ}
    (hc : ∀ z ∈ Z, z ≠ 1 → -φ z = c) :
    ∃ a b : ℤ, c = a ∧ -φ 1 = b ∧ (Nat.card (P : Subgroup G) : ℤ) ∣ b - a := by
  obtain ⟨a, b, ha, hb, hdvd⟩ :=
    hs.exists_int_dvd_sub hφ (c := -c) fun z hz hz1 => by rw [← hc z hz hz1]; ring
  refine ⟨-a, -b, by push_cast; linear_combination -ha, by push_cast; linear_combination -hb, ?_⟩
  have hneg := hdvd.neg_right
  rwa [show -(b - a) = -b - -a by ring] at hneg

end Finite

end IsTINormalCentralSection

end CFSG.FeitThompson
