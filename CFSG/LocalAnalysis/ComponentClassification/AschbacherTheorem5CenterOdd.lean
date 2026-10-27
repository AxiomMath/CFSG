module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5CenterQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitCentralExtension
public import CFSG.CharacterTheory.TwoRankLowerBound.RankOneClassification
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Hyp
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5Semisimple
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public noncomputable section

open CFSG.Open

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace CenterQuotient

variable {G : Type*} [Group G] [Finite G]

theorem two_element_mem_commutator (D : Subgroup G)
    (Abar : Subgroup (D ⧸ aschbacherThm5OddCore D)) [Group.IsPerfect Abar]
    (w : aschbacherThm5Preimage D Abar) {k : ℕ} (hw : w ^ (2 ^ k) = 1) :
    w ∈ commutator (aschbacherThm5Preimage D Abar) := by
  let μ : aschbacherThm5Preimage D Abar →* Abar :=
    ((QuotientGroup.mk' (aschbacherThm5OddCore D)).comp
      (Subgroup.inclusion (preimage_le D Abar))).codRestrict Abar
      (fun a => (mem_preimage_iff D Abar _).mp a.2)
  have hμ : Function.Surjective μ := by
    rintro ⟨x, hx⟩
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨⟨d.val, (mem_preimage_iff D Abar d).mpr hx⟩, rfl⟩
  have hmap : (commutator (aschbacherThm5Preimage D Abar)).map μ = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hμ, ← _root_.commutator_def,
      Group.IsPerfect.commutator_eq_top]
  obtain ⟨c, hc, hcw⟩ := Subgroup.mem_map.mp (hmap ▸ Subgroup.mem_top (μ w))
  have hcore : ((c⁻¹ * w : aschbacherThm5Preimage D Abar) : G) ∈ aschbacherThm5Core D := by
    have hone : μ (c⁻¹ * w) = 1 := by rw [map_mul, map_inv, hcw, inv_mul_cancel]
    have hval : QuotientGroup.mk' (aschbacherThm5OddCore D)
        (Subgroup.inclusion (preimage_le D Abar) (c⁻¹ * w)) = 1 := congrArg Subtype.val hone
    exact (mem_core_iff D _).mpr ((QuotientGroup.eq_one_iff _).mp hval)
  have hodd : (c⁻¹ * w) ^ Nat.card (aschbacherThm5Core D) = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hcore)
  have hmk : QuotientGroup.mk' (commutator (aschbacherThm5Preimage D Abar)) w =
      QuotientGroup.mk' (commutator (aschbacherThm5Preimage D Abar)) (c⁻¹ * w) := by
    have hcone : QuotientGroup.mk' (commutator (aschbacherThm5Preimage D Abar)) c = 1 :=
      (QuotientGroup.eq_one_iff c).mpr hc
    rw [map_mul, map_inv, hcone, inv_one, one_mul]
  have hone : QuotientGroup.mk' (commutator (aschbacherThm5Preimage D Abar)) w = 1 := by
    apply eq_one_of_two_pow_of_odd (k := k) (n := Nat.card (aschbacherThm5Core D))
    · rw [← map_pow, hw, map_one]
    · exact core_odd D
    · rw [hmk, ← map_pow, hodd, map_one]
  exact (QuotientGroup.eq_one_iff w).mp hone

theorem center_inf_odd (A : Subgroup G)
    (hcomm : ∀ w : A, (w : G) ∈ Subgroup.center G → (∃ k : ℕ, w ^ (2 ^ k) = 1) →
      w ∈ commutator A)
    (hrank : Open.pRank 2 (A.map (QuotientGroup.mk' (Subgroup.center G))) ≤ 1) :
    Odd (Nat.card (Subgroup.center G ⊓ A : Subgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra heven
  rw [Nat.not_odd_iff_even] at heven
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
  have hwZ : (w : G) ∈ Subgroup.center G := (Subgroup.mem_inf.mp w.2).1
  have hwA : (w : G) ∈ A := (Subgroup.mem_inf.mp w.2).2
  have hwAorder : orderOf (⟨w, hwA⟩ : A) = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hw]
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (p := 2)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hwAorder, pow_one]) :
      IsPGroup 2 (Subgroup.zpowers (⟨w, hwA⟩ : A)))
  have hwP : (⟨w, hwA⟩ : A) ∈ (P : Subgroup A) := hP (Subgroup.mem_zpowers _)
  let f : (P : Subgroup A) →* G ⧸ Subgroup.center G :=
    (QuotientGroup.mk' (Subgroup.center G)).comp (A.subtype.comp (P : Subgroup A).subtype)
  have hmemK : ∀ x : (P : Subgroup A), x ∈ f.ker ↔ ((x : A) : G) ∈ Subgroup.center G := by
    intro x
    rw [MonoidHom.mem_ker]
    exact QuotientGroup.eq_one_iff _
  have hKcenter : f.ker ≤ Subgroup.center (P : Subgroup A) := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp ((hmemK x).mp hx) _))
  have hKcomm : f.ker ≤ commutator (P : Subgroup A) := by
    set Z := f.ker.map (P : Subgroup A).subtype
    have hZcenter : Z ≤ Subgroup.center A := by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp ((hmemK x).mp hx) _)
    have hZtwo : IsPGroup 2 Z := P.isPGroup'.to_le (Subgroup.map_subtype_le _)
    have hZcomm : Z ≤ commutator A := by
      rintro _ ⟨x, hx, rfl⟩
      apply hcomm _ ((hmemK x).mp hx)
      obtain ⟨k, hk⟩ := P.isPGroup' x
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have heq := AschbacherToolkit.central_sylow_commutator P hZcenter hZtwo
    intro x hx
    have hxZ : (x : A) ∈ Z := Subgroup.mem_map_of_mem _ hx
    have hxboth : (x : A) ∈ Z ⊓ commutator A := Subgroup.mem_inf.mpr ⟨hxZ, hZcomm hxZ⟩
    rw [heq] at hxboth
    exact (Subgroup.mem_map_iff_mem (P : Subgroup A).subtype_injective).mp
      (Subgroup.mem_inf.mp hxboth).2
  have hrankP : twoRank ((P : Subgroup A) ⧸ f.ker) ≤ 1 := by
    calc twoRank ((P : Subgroup A) ⧸ f.ker)
        = Open.pRank 2 (⊤ : Subgroup ((P : Subgroup A) ⧸ f.ker)) := rfl
      _ ≤ Open.pRank 2 ((⊤ : Subgroup ((P : Subgroup A) ⧸ f.ker)).map (QuotientGroup.kerLift f)) :=
          SectionRank.pRank_le_map (by norm_num) _ (QuotientGroup.kerLift_injective f) _
      _ ≤ Open.pRank 2 (A.map (QuotientGroup.mk' (Subgroup.center G))) := by
          apply SectionRank.pRank_mono (by norm_num)
          rintro _ ⟨q, -, rfl⟩
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
          rw [QuotientGroup.kerLift_mk]
          exact Subgroup.mem_map_of_mem _ (x : A).2
      _ ≤ 1 := hrank
  have hbot : f.ker = ⊥ := by
    rcases TwoRankLowerBound.Helpers.rank_one_two_group_cyclic_or_quaternion _
        (P.isPGroup'.to_quotient f.ker) hrankP with hcyclic | ⟨e, -, ⟨iso⟩⟩
    · have := hcyclic
      have hderived := AschbacherToolkit.cyclic_central_extension (QuotientGroup.mk' f.ker)
        (by rw [QuotientGroup.ker_mk']; exact hKcenter)
      rw [hderived] at hKcomm
      exact le_bot_iff.mp hKcomm
    · have : NeZero (2 ^ (e - 2)) := ⟨by positivity⟩
      have hinf := AschbacherToolkit.quaternion_central_extension f.ker hKcenter iso
      rwa [inf_eq_left.mpr hKcomm] at hinf
  have hwK : (⟨⟨w, hwA⟩, hwP⟩ : (P : Subgroup A)) ∈ f.ker := (hmemK _).mpr hwZ
  rw [hbot, Subgroup.mem_bot] at hwK
  have hwone : (⟨w, hwA⟩ : A) = 1 := congrArg Subtype.val hwK
  rw [hwone, orderOf_one] at hwAorder
  exact absurd hwAorder (by norm_num)

theorem pRank_eq_of_center_inf_odd (A : Subgroup G)
    (hodd : Odd (Nat.card (Subgroup.center G ⊓ A : Subgroup G))) :
    Open.pRank 2 A = Open.pRank 2 (A.map (QuotientGroup.mk' (Subgroup.center G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ 2 ∣ Nat.card ((Subgroup.center G).subgroupOf A) := by
    rw [← Subgroup.card_subtype A, Subgroup.subgroupOf_map_subtype]
    exact hodd.not_two_dvd_nat
  have hker : ((QuotientGroup.mk' (Subgroup.center G)).subgroupMap A).ker =
      (Subgroup.center G).subgroupOf A := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  let e : A ⧸ (Subgroup.center G).subgroupOf A ≃* A.map (QuotientGroup.mk' (Subgroup.center G)) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ (MonoidHom.subgroupMap_surjective _ A))
  rw [SectionRank.pRank_eq_pRank_top_subgroup A,
    SectionRank.pRank_eq_pRank_top_subgroup (A.map (QuotientGroup.mk' (Subgroup.center G))),
    ← SectionRank.pRank_quotient_eq _ hN, SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]

end CenterQuotient

open CenterQuotient

theorem center_inf_factor_odd {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
    {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)} (hyp : Hyp61 G D r Abar) (i : Fin r)
    (hrank : Open.pRank 2
      (aschbacherThm5Preimage (quotientSubgroup D) (quotientFactors D Abar i)) ≤ 1) :
    Odd (Nat.card (Subgroup.center G ⊓ aschbacherThm5Preimage D (Abar i) : Subgroup G)) := by
  have : Group.IsPerfect (Abar i) := semisimple_perfect (Abar i) (hyp.hsemisimple i)
  apply center_inf_odd
  · rintro w - ⟨k, hk⟩
    exact two_element_mem_commutator D (Abar i) w hk
  · rwa [quotientFactors_apply, preimage_center_quotient] at hrank

end CFSG.ComponentClassification.AschbacherTheorem5
