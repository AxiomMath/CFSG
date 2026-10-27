module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuasi
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5SixInputs
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Transfer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorNontrivial
public import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3WeakClosure
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveOrbit
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5TransitiveQuotient
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace SectionSix

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

namespace Strong

omit [Finite G] in
theorem conj_of_odd_product {z z' : G} (hz : z ^ 2 = 1) (hz' : z' ^ 2 = 1)
    (hodd : Odd (orderOf (z * z'))) :
    ∃ w ∈ Subgroup.zpowers (z * z'), z' = w⁻¹ * z * w := by
  set o := z * z' with ho
  obtain ⟨a, ha⟩ := hodd
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hz)
  have hzi' : z'⁻¹ = z' := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hz')
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz
  have hinv : z * o * z⁻¹ = o⁻¹ := by
    calc z * o * z⁻¹ = (z * z) * z' * z⁻¹ := by rw [ho]; group
      _ = o⁻¹ := by rw [hzz, one_mul, ho, mul_inv_rev, hzi', hzi]
  refine ⟨o ^ (a + 1), Subgroup.npow_mem_zpowers o _, ?_⟩
  have hzw : z * o ^ (a + 1) * z⁻¹ = (o ^ (a + 1))⁻¹ := by
    rw [← conj_pow, hinv, inv_pow]
  have hsq : o ^ (a + 1) * o ^ (a + 1) = o := by
    rw [← pow_add, show a + 1 + (a + 1) = orderOf o + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  calc z' = o⁻¹ * z := by
        rw [ho, mul_inv_rev, hzi', hzi, mul_assoc, hzz, mul_one]
    _ = (o ^ (a + 1) * o ^ (a + 1))⁻¹ * z := by rw [hsq]
    _ = (o ^ (a + 1))⁻¹ * (z * o ^ (a + 1) * z⁻¹) * z := by rw [hzw]; group
    _ = (o ^ (a + 1))⁻¹ * z * o ^ (a + 1) := by group

omit [Finite G] in
theorem le_core_of_odd {N : Subgroup G} (hND : N ≤ D) (hDN : D ≤ Subgroup.normalizer (N : Set G))
    (hodd : Odd (Nat.card N)) : N ≤ aschbacherThm5Core D :=
  AschbacherTheorem3.le_map_oddCore hND hDN hodd

theorem factor_not_solvable (hyp : Hyp61 G D r Abar) (k : Fin r) {Q : Subgroup G}
    (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q) : ¬ Group.IsSolvable Q := by
  intro hQ
  have := hQ
  set A := aschbacherThm5Preimage D (Abar k)
  have hAH : A ≤ Subgroup.normalizer (D : Set G) := (preimage_le D _).trans Subgroup.le_normalizer
  have hA : Group.IsSolvable A :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hkQ)
      (Subgroup.inclusion_injective hkQ)
  have hA' : Group.IsSolvable (A.subgroupOf (Subgroup.normalizer (D : Set G))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hAH).toMonoidHom) (MulEquiv.injective _)
  have hbar : Group.IsSolvable (bar D A) :=
    Group.isSolvable_of_surjective (f := (toBar D).subgroupMap (A.subgroupOf _))
      ((toBar D).subgroupMap_surjective _)
  have : Group.IsPerfect (bar D A) := bar_factor_perfect hyp k
  have : Nontrivial (bar D A) := (bar D A).nontrivial_iff_ne_bot.mpr (bar_factor_ne_bot hyp k)
  exact Group.IsPerfect.not_isSolvable _ hbar

theorem pRank_le_of_isSylowOf {P K : Subgroup G} (hP : IsSylowOf 2 P K) :
    CFSG.Open.pRank 2 K ≤ CFSG.Open.pRank 2 P := by
  obtain ⟨E, hEK, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 2) K
  have hE2 : IsPGroup 2 E := IsPGroup.of_card hcard
  obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hP hE2 hEK
  refine CFSG.SectionRank.le_pRank (by norm_num) hc ?_ (by rw [rightConjugate_card, hcard])
  exact CFSG.SectionRank.isElemAbelian_map hE _

theorem factor_sylow_not_cyclic (hyp : Hyp61 G D r Abar) (k : Fin r) {P : Subgroup G}
    (hP : IsSylowOf 2 P (aschbacherThm5Preimage D (Abar k))) : ¬ IsCyclic P := by
  intro hcyc
  have hAH : aschbacherThm5Preimage D (Abar k) ≤ Subgroup.normalizer (D : Set G) :=
    (preimage_le D _).trans Subgroup.le_normalizer
  have hbar := isSylowOf_bar (D := D) hP hAH
  apply sylow_not_cyclic_of_perfect (bar_factor_perfect hyp k) (bar_factor_ne_bot hyp k) hbar
  have : IsCyclic P := hcyc
  have : IsCyclic (P.subgroupOf (Subgroup.normalizer (D : Set G))) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (hP.le.trans hAH)).symm.toMonoidHom
      (MulEquiv.surjective _)
  exact isCyclic_of_surjective ((toBar D).subgroupMap (P.subgroupOf _))
    ((toBar D).subgroupMap_surjective _)

omit [Finite G] in
theorem isCyclic_of_le {P R : Subgroup G} (hPR : P ≤ R) (hR : IsCyclic R) : IsCyclic P := by
  have : IsCyclic (P.subgroupOf R) := Subgroup.isCyclic _
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hPR).toMonoidHom
    (MulEquiv.surjective _)

theorem conj_of_pRank_le_one {K : Subgroup G} (hK : CFSG.Open.pRank 2 K ≤ 1) {z a : G}
    (hzK : z ∈ K) (hz : orderOf z = 2) (haK : a ∈ K) (ha : orderOf a = 2) :
    ∃ c ∈ K, c * a * c⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have ha2 : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha, pow_one])
  obtain ⟨P, hP, hzP⟩ := AschbacherTheorem3.exists_isSylowOf_le hz2
    (Subgroup.zpowers_le.mpr hzK)
  obtain ⟨c, hcK, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hP ha2
    (Subgroup.zpowers_le.mpr haK)
  have hca : c⁻¹ * a * c ∈ P := hc ((mem_rightConjugate_iff _ c _).mpr (by
    simp [mul_assoc]))
  have hcaord : orderOf (c⁻¹ * a * c) = 2 := by
    rw [show c⁻¹ * a * c = MulAut.conj c⁻¹ a by simp, MulEquiv.orderOf_eq, ha]
  have hPr : CFSG.Open.pRank 2 P ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hP.le).trans hK
  have heq := eq_of_pRank_le_one hP.isPGroup hPr hca (hzP (Subgroup.mem_zpowers z)) hcaord hz
  refine ⟨c⁻¹, K.inv_mem hcK, ?_⟩
  rw [inv_inv, ← heq]

theorem eq_one_of_mem_core_of_sq {x : G} (hx : x ∈ aschbacherThm5Core D) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  have hodd : Odd (orderOf x) :=
    (core_odd D).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hx)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at hodd
    exact absurd hodd (by decide)

end Strong

open Strong in
theorem conclusion_of_shared_involution {Abar : Fin 2 → Subgroup (D ⧸ aschbacherThm5OddCore D)}
    (hyp : Hyp61 G D 2 Abar)
    (hrank : ∀ i, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar i)) ≤ 1)
    {z : G} (hz : orderOf z = 2) (hzA : ∀ i, z ∈ aschbacherThm5Preimage D (Abar i)) :
    Conclusion G D 2 Abar := by
  have hzO : ∀ (i : Fin 2) (a : G), a ∈ aschbacherThm5Preimage D (Abar i) → orderOf a = 2 →
      aschbacherThm5Centralizes (aschbacherThm5Core D) (aschbacherThm5Preimage D (Abar i)) a →
      z⁻¹ * a ∈ aschbacherThm5Core D := by
    intro i a ha hao hac
    obtain ⟨c, hcA, hca⟩ := conj_of_pRank_le_one (hrank i) (hzA i) hz ha hao
    have hw := hac c⁻¹ ((aschbacherThm5Preimage D (Abar i)).inv_mem hcA)
    rw [show z⁻¹ * a = (a⁻¹ * c⁻¹⁻¹ * a * c⁻¹)⁻¹ by rw [← hca]; group]
    exact (aschbacherThm5Core D).inv_mem hw
  right
  refine ⟨rfl, fun i j hij => ⟨canonical_two_factor_product D Abar hyp.hcomm hyp.hgen i j hij,
    le_antisymm (hrank i) ?_, ?_⟩⟩
  · have hz2 : IsElemAbelian 2 (Subgroup.zpowers z) := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
      · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
        obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
        change (a : G) * b = b * a
        rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
      · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          ← hz, pow_orderOf_eq_one, one_zpow]
    exact CFSG.SectionRank.le_pRank (by norm_num) (Subgroup.zpowers_le.mpr (hzA i)) hz2
      (by rw [Nat.card_zpowers, hz, pow_one])
  · intro a₁ ha₁ a₂ ha₂ ho₁ ho₂ hcomm hc₁ hc₂
    left
    have h₁ := hzO i a₁ ha₁ ho₁ hc₁
    have h₂ := hzO j a₂ ha₂ ho₂ hc₂
    have hmem : a₁⁻¹ * a₂ ∈ aschbacherThm5Core D := by
      have := (aschbacherThm5Core D).mul_mem ((aschbacherThm5Core D).inv_mem h₁) h₂
      simpa [mul_assoc] using this
    have hsq : (a₁⁻¹ * a₂) ^ 2 = 1 := by
      have ha₁sq : a₁ * a₁ = 1 := by rw [← pow_two, ← ho₁, pow_orderOf_eq_one]
      have ha₂sq : a₂ * a₂ = 1 := by rw [← pow_two, ← ho₂, pow_orderOf_eq_one]
      have ha₁i : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_left ha₁sq
      rw [pow_two, ha₁i]
      calc a₁ * a₂ * (a₁ * a₂) = a₁ * (a₂ * a₁) * a₂ := by group
        _ = a₁ * (a₁ * a₂) * a₂ := by rw [hcomm]
        _ = (a₁ * a₁) * (a₂ * a₂) := by group
        _ = 1 := by rw [ha₁sq, ha₂sq, one_mul]
    have h1 := eq_one_of_mem_core_of_sq hmem hsq
    rw [inv_mul_eq_one] at h1
    exact h1

namespace Strong

omit [Finite G] in
theorem oddCore_map_normal {K : Subgroup G} [hK : K.Normal] :
    ((CFSG.oddCore K).map K.subtype).Normal := by
  refine ⟨fun n hn x => ?_⟩
  have hxK : x ∈ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hK]
    exact Subgroup.mem_top x
  have hφ := Subgroup.characteristic_iff_map_eq.mp (oddCore_characteristic K) (onD K ⟨x, hxK⟩)
  have hmem : x * n * x⁻¹ ∈ ((CFSG.oddCore K).map K.subtype).map (MulAut.conj x).toMonoidHom :=
    ⟨n, hn, rfl⟩
  have heq : ((CFSG.oddCore K).map K.subtype).map (MulAut.conj x).toMonoidHom =
      (CFSG.oddCore K).map K.subtype := by
    rw [Subgroup.map_map, show (MulAut.conj x).toMonoidHom.comp K.subtype =
      K.subtype.comp (onD K ⟨x, hxK⟩).toMonoidHom from (onD_equivariant K ⟨x, hxK⟩).symm,
      ← Subgroup.map_map]
    exact congrArg (Subgroup.map K.subtype) hφ
  rwa [heq] at hmem

theorem conj_mem_oddCore_mul {K : Subgroup G} [hK : K.Normal]
    (hrank : CFSG.Open.pRank 2 K ≤ 1) {z : G} (hzK : z ∈ K) (hz : orderOf z = 2)
    (hcent : ∀ c ∈ K, z⁻¹ * (c * z * c⁻¹) ∈ (CFSG.oddCore K).map K.subtype) (g : G) :
    z⁻¹ * (g⁻¹ * z * g) ∈ (CFSG.oddCore K).map K.subtype := by
  have hz'K : g⁻¹ * z * g ∈ K := by
    have := hK.conj_mem z hzK g⁻¹
    simpa using this
  have hz' : orderOf (g⁻¹ * z * g) = 2 := by
    rw [show g⁻¹ * z * g = MulAut.conj g⁻¹ z by simp, MulEquiv.orderOf_eq, hz]
  obtain ⟨c, hcK, hc⟩ := conj_of_pRank_le_one hrank hzK hz hz'K hz'
  have hz'eq : g⁻¹ * z * g = c⁻¹ * z * c⁻¹⁻¹ := by
    have h : g⁻¹ * z * g = c⁻¹ * (c * (g⁻¹ * z * g) * c⁻¹) * c := by group
    rw [hc] at h
    rw [h, inv_inv]
  rw [hz'eq]
  exact hcent c⁻¹ (K.inv_mem hcK)

theorem bar_factor_le_centralizer (hyp : Hyp61 G D r Abar) {a b : Fin r} (hab : a ≠ b) :
    bar D (aschbacherThm5Preimage D (Abar b)) ≤
      Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar a)) : Set (Bar D)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := (mem_bar_iff D _ x).mp hx
  exact (centralizes_iff_mem_centralizer D _ (preimage_le D _) y).mp
    (cross_factor_centralizes D Abar hyp.hcomm a b hab y hy)

theorem sylow_not_le_factor (hyp : Hyp61 G D r Abar) {a b : Fin r} (hab : a ≠ b)
    {P : Subgroup G} (hP : IsSylowOf 2 P (aschbacherThm5Preimage D (Abar a))) :
    ¬ P ≤ aschbacherThm5Preimage D (Abar b) := by
  intro hPb
  have hAH : aschbacherThm5Preimage D (Abar a) ≤ Subgroup.normalizer (D : Set G) :=
    (preimage_le D _).trans Subgroup.le_normalizer
  exact sylow_not_le_centralizer_of_perfect (bar_factor_perfect hyp a) (bar_factor_ne_bot hyp a)
    (isSylowOf_bar (D := D) hP hAH)
    ((bar_mono D hPb).trans (bar_factor_le_centralizer hyp hab))

theorem exists_ne_index (hr : 2 ≤ r) (l : Fin r) : ∃ l' : Fin r, l' ≠ l := by
  by_cases hl : l.val = 0
  · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at hl; exact absurd hl (by norm_num)⟩
  · exact ⟨⟨0, by omega⟩, fun h => hl (by rw [← h])⟩

end Strong

open Strong in
theorem not_stronglyEmbedded (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {Q : Subgroup G} {k j : Fin r} (hkQ : aschbacherThm5Preimage D (Abar k) ≤ Q)
    (hQj : Q ≤ centralizing D (Abar j)) :
    ¬ CFSG.Open.fusionStronglyEmbedded
      ((Subgroup.normalizer (Q : Set G)).subgroupOf (Subgroup.normalClosure (Q : Set G))) := by
  intro hSE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := Subgroup.normalClosure (Q : Set G) with hKdef
  have hKn : K.Normal := Subgroup.normalClosure_normal
  have hQK : Q ≤ K := Subgroup.le_normalClosure
  by_cases hrank : 2 ≤ CFSG.Open.twoRank K
  ·
    have hsolv := hin.strongly_embedded_solvable K _ hSE hrank
    apply factor_not_solvable hC.hyp k hkQ
    have hQN : Q.subgroupOf K ≤ (Subgroup.normalizer (Q : Set G)).subgroupOf K :=
      Subgroup.subgroupOf_mono K Subgroup.le_normalizer
    have h1 : Group.IsSolvable (Q.subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hQN)
        (Subgroup.inclusion_injective hQN)
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hQK).symm.toMonoidHom) (MulEquiv.injective _)
  have hrank1 : CFSG.Open.pRank 2 K ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    unfold CFSG.Open.twoRank at hrank
    omega
  obtain ⟨z0, hz0⟩ := exists_prime_orderOf_dvd_card' 2
    (even_iff_two_dvd.mp (factor_even hC.hyp k))
  set z : G := (z0 : G) with hzdef
  have hz : orderOf z = 2 := by rw [hzdef, Subgroup.orderOf_coe, hz0]
  have hzsq : z ^ 2 = 1 := by rw [← hz, pow_orderOf_eq_one]
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_left (by rw [← pow_two, hzsq])
  have hz1 : z ≠ 1 := by
    rintro h
    rw [h, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzA : z ∈ aschbacherThm5Preimage D (Abar k) := z0.2
  have hzQ := hkQ hzA
  have hzK := hQK hzQ
  have hzD : z ∈ D := preimage_le D _ hzA
  have hz2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  obtain ⟨PK, hPK, hzPK⟩ := AschbacherTheorem3.exists_isSylowOf_le hz2
    (Subgroup.zpowers_le.mpr hzK)
  have hPKr : CFSG.Open.pRank 2 PK ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) hPK.le).trans hrank1
  have hPKnc : ¬ IsCyclic PK := by
    intro hcyc
    obtain ⟨PA, hPA⟩ := exists_isSylowOf 2 (aschbacherThm5Preimage D (Abar k))
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hPK
      hPA.isPGroup (hPA.le.trans (hkQ.trans hQK))
    exact not_isCyclic_rightConjugate (factor_sylow_not_cyclic hC.hyp k hPA) c
      (isCyclic_of_le hc hcyc)
  obtain ⟨n, hn, ⟨e⟩⟩ :=
    (cyclic_or_quaternion_of_pRank_le_one hPK.isPGroup hPKr).resolve_left hPKnc
  have hPK0 := hPK
  obtain ⟨PK', hPK'⟩ := hPK0
  have hquat : Nonempty ((PK' : Subgroup K) ≃* QuaternionGroup (2 ^ (n - 2))) :=
    ⟨(((PK' : Subgroup K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hPK')).trans e⟩
  have hzmem : (⟨z, hzK⟩ : K) ∈ (PK' : Subgroup K) := by
    have h1 : z ∈ PK := hzPK (Subgroup.mem_zpowers z)
    rw [← hPK'] at h1
    obtain ⟨w, hw, hwz⟩ := h1
    have hweq : w = ⟨z, hzK⟩ := Subtype.ext hwz
    rwa [← hweq]
  have hzord : orderOf (⟨z, hzK⟩ : K) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz
  have hBS := CFSG.BrauerSuzuki.brauer_suzuki n hn PK' hquat ⟨z, hzK⟩ hzmem hzord
  set OK := (CFSG.oddCore K).map K.subtype with hOKdef
  have hcent : ∀ c ∈ K, z⁻¹ * (c * z * c⁻¹) ∈ OK := by
    intro c hc
    have hcomm := Subgroup.mem_center_iff.mp hBS (QuotientGroup.mk ⟨c, hc⟩)
    have heq : (QuotientGroup.mk ⟨z, hzK⟩ : K ⧸ CFSG.oddCore K) =
        QuotientGroup.mk (⟨c, hc⟩ * ⟨z, hzK⟩ * (⟨c, hc⟩ : K)⁻¹) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hcomm]
      group
    exact ⟨_, QuotientGroup.eq.mp heq, rfl⟩
  have hOKn : OK.Normal := oddCore_map_normal
  have hOKodd : Odd (Nat.card OK) := by
    rw [hOKdef, Subgroup.card_map_of_injective K.subtype_injective]
    exact OddCore.odd_card K
  have hconj := conj_mem_oddCore_mul hrank1 hzK hz hcent
  have hzCH := centralizer_le hC j ⟨1, by rw [pow_one, hzsq]⟩ hz1
    (centralizes_of_mem_centralizing (hQj hzQ))
  have hGHO : ∀ g : G, ∃ h ∈ Subgroup.normalizer (D : Set G), ∃ w ∈ OK, g = h * w := by
    intro g
    have hzz : z * (g⁻¹ * z * g) ∈ OK := by
      have h1 := hconj g
      rwa [hzi] at h1
    have hz'sq : (g⁻¹ * z * g) ^ 2 = 1 := by
      rw [pow_two, show g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g by group,
        ← pow_two, hzsq]
      group
    have hodd : Odd (orderOf (z * (g⁻¹ * z * g))) :=
      hOKodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hzz)
    obtain ⟨w, hw, hweq⟩ := conj_of_odd_product hzsq hz'sq hodd
    have hwOK : w ∈ OK := (Subgroup.zpowers_le.mpr hzz) hw
    refine ⟨g * w⁻¹, hzCH ?_, w, hwOK, by group⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc g * w⁻¹ * z = g * (w⁻¹ * z * w) * w⁻¹ := by group
      _ = g * (g⁻¹ * z * g) * w⁻¹ := by rw [← hweq]
      _ = z * (g * w⁻¹) := by group
  have hGH : OK ≤ Subgroup.normalizer (D : Set G) → False := by
    intro hOKH
    apply hC.proper
    rw [eq_top_iff]
    intro g _
    obtain ⟨h, hh, w, hw, rfl⟩ := hGHO g
    exact Subgroup.mul_mem _ hh (hOKH hw)
  have hOKD : OK ⊓ D ≤ aschbacherThm5Core D := by
    refine le_core_of_odd inf_le_right (fun x hx => ?_)
      (hOKodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
    have hxOK : x ∈ Subgroup.normalizer (OK : Set G) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hOKn]
      exact Subgroup.mem_top x
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxOK, Subgroup.le_normalizer hx⟩
  have hzk : aschbacherThm5Centralizes (aschbacherThm5Core D)
      (aschbacherThm5Preimage D (Abar k)) z := by
    intro a ha
    have haD : a ∈ D := preimage_le D _ ha
    have h1 := hconj a
    have hmemD : z⁻¹ * (a⁻¹ * z * a) ∈ D :=
      D.mul_mem (D.inv_mem hzD) (D.mul_mem (D.mul_mem (D.inv_mem haD) hzD) haD)
    have h2 := hOKD ⟨h1, hmemD⟩
    simpa [mul_assoc] using h2
  obtain ⟨SD, hSD, hzSD⟩ := AschbacherTheorem3.exists_isSylowOf_le hz2
    (Subgroup.zpowers_le.mpr hzD)
  have hzC : ∀ l, z ∈ SD ⊓ centralizing D (Abar l) := by
    intro l
    refine ⟨hzSD (Subgroup.mem_zpowers z), ?_⟩
    by_cases hlk : l = k
    · subst hlk
      exact (mem_centralizing_iff _ z).mpr ⟨hzD, hzk⟩
    · exact factor_le_centralizing hC.hyp.hcomm hlk hzA
  have hfactorSyl : ∀ l, IsSylowOf 2 (SD ⊓ aschbacherThm5Preimage D (Abar l))
      (aschbacherThm5Preimage D (Abar l)) := by
    intro l
    have hn := canonical_preimage_normal D Abar hC.hyp.hcomm hC.hyp.hgen l
    exact hSD.inf_of_le_normalizer (preimage_le D _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (preimage_le D _)).mp hn)
  by_cases hbig : ∃ l, 2 ≤ CFSG.Open.pRank 2 (SD ⊓ centralizing D (Abar l))
  ·
    obtain ⟨l, hl⟩ := hbig
    obtain ⟨E, hEC, hE, hE4⟩ :=
      CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := 2) hl
    obtain ⟨u, huE, t, htE, hu1, ht1, htu⟩ := AschbacherTheorem3.exists_two_ne_one
      (show 4 ≤ Nat.card E by rw [hE4]; norm_num)
    have hord : ∀ v ∈ E, v ≠ 1 → orderOf v = 2 := fun v hv hv1 =>
      orderOf_eq_prime (hE.2 v hv) hv1
    have hCH : ∀ v ∈ E, v ≠ 1 →
        Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
      intro v hv hv1
      exact centralizer_le hC l ⟨1, by rw [pow_one]; exact hE.2 v hv⟩ hv1
        (centralizes_of_mem_centralizing (hEC hv).2)
    have hut : Commute u t := congrArg Subtype.val (hE.1.is_comm.comm ⟨u, huE⟩ ⟨t, htE⟩)
    have hut1 : u * t ≠ 1 := by
      intro h
      apply htu
      have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_left (by rw [← pow_two]; exact hE.2 t htE)
      rw [eq_inv_of_mul_eq_one_left h, hti]
    have hgen :=
      CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.four_group_odd_centralizer_generation
      OK u t (hord u huE hu1) (hord t htE ht1) hut (Ne.symm htu) hOKodd (by
        rw [Subgroup.normalizer_eq_top_iff.mpr hOKn]
        exact le_top)
    apply hGH
    rw [hgen]
    exact sup_le (sup_le (inf_le_right.trans (hCH u huE hu1))
      (inf_le_right.trans (hCH t htE ht1)))
      (inf_le_right.trans (hCH (u * t) (E.mul_mem huE htE) hut1))
  push Not at hbig
  have hsmall : ∀ l, CFSG.Open.pRank 2 (SD ⊓ centralizing D (Abar l)) ≤ 1 :=
    fun l => Nat.lt_succ_iff.mp (hbig l)
  have hzAll : ∀ l, z ∈ aschbacherThm5Preimage D (Abar l) := by
    intro l
    obtain ⟨l', hl'⟩ := exists_ne_index (two_le hC) l
    have hPl := hfactorSyl l
    have heven : Even (Nat.card (SD ⊓ aschbacherThm5Preimage D (Abar l) : Subgroup G)) := by
      rw [hPl.card_eq]
      have hf : (Nat.card (aschbacherThm5Preimage D (Abar l))).factorization 2 ≠ 0 :=
        (Nat.Prime.factorization_pos_of_dvd Nat.prime_two Nat.card_pos.ne'
          (even_iff_two_dvd.mp (factor_even hC.hyp l))).ne'
      exact (Nat.even_pow' hf).mpr even_two
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp heven)
    have htC : (t : G) ∈ SD ⊓ centralizing D (Abar l') :=
      ⟨t.2.1, factor_le_centralizing hC.hyp.hcomm hl' t.2.2⟩
    have heq := eq_of_pRank_le_one hSD.isPGroup.to_inf_left (hsmall l') htC (hzC l')
      ((Subgroup.orderOf_coe t).trans ht) hz
    rw [← heq]
    exact t.2.2
  have hfactorRank : ∀ l, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar l)) ≤ 1 := by
    intro l
    obtain ⟨l', hl'⟩ := exists_ne_index (two_le hC) l
    refine (pRank_le_of_isSylowOf (hfactorSyl l)).trans
      ((CFSG.SectionRank.pRank_mono (by norm_num) ?_).trans (hsmall l'))
    exact le_inf inf_le_left (inf_le_right.trans (factor_le_centralizing hC.hyp.hcomm hl'))
  rcases Nat.lt_or_ge r 3 with hr3 | hr3
  ·
    have hr2 : r = 2 := by have := two_le hC; omega
    subst hr2
    exact hC.fails (conclusion_of_shared_involution hC.hyp hfactorRank hz hzAll)
  ·
    set a : Fin r := ⟨0, by omega⟩
    set b : Fin r := ⟨1, by omega⟩
    set c : Fin r := ⟨2, by omega⟩
    have hab : a ≠ b := fun h => absurd (congrArg Fin.val h) (by norm_num)
    have hac : a ≠ c := fun h => absurd (congrArg Fin.val h) (by norm_num)
    have hbc : b ≠ c := fun h => absurd (congrArg Fin.val h) (by norm_num)
    have hPa : SD ⊓ aschbacherThm5Preimage D (Abar a) ≤ SD ⊓ centralizing D (Abar c) :=
      le_inf inf_le_left (inf_le_right.trans (factor_le_centralizing hC.hyp.hcomm hac.symm))
    have hPb : SD ⊓ aschbacherThm5Preimage D (Abar b) ≤ SD ⊓ centralizing D (Abar c) :=
      le_inf inf_le_left (inf_le_right.trans (factor_le_centralizing hC.hyp.hcomm hbc.symm))
    have hCc := cyclic_or_quaternion_of_pRank_le_one hSD.isPGroup.to_inf_left (hsmall c)
    have hRtype : IsCyclic (SD ⊓ centralizing D (Abar c) : Subgroup G) ∨
        AschbacherTheorem3.IsDihedralTwoGroup (SD ⊓ centralizing D (Abar c)) ∨
        AschbacherTheorem3.IsQuaternionTwoGroup (SD ⊓ centralizing D (Abar c)) :=
      hCc.elim Or.inl (fun h => Or.inr (Or.inr h))
    have hcommab : ∀ x ∈ SD ⊓ aschbacherThm5Preimage D (Abar a),
        ∀ y ∈ SD ⊓ aschbacherThm5Preimage D (Abar b), x * y = y * x := by
      intro x hx y hy
      have h1 := cross_factor_centralizes D Abar hC.hyp.hcomm b a hab.symm x hx.2 y hy.2
      have h2 : x⁻¹ * y⁻¹ * x * y ∈ SD :=
        SD.mul_mem (SD.mul_mem (SD.mul_mem (SD.inv_mem hx.1) (SD.inv_mem hy.1)) hx.1) hy.1
      have h3 : x⁻¹ * y⁻¹ * x * y = 1 := by
        have hinf : SD ⊓ aschbacherThm5Core D = ⊥ :=
          CFSG.ComponentClassification.AschbacherToolkit.inf_eq_bot_of_isPGroup_of_coprime
            hSD.isPGroup (fun h => (Nat.not_even_iff_odd.mpr (core_odd D)) (even_iff_two_dvd.mpr h))
        have hmem : x⁻¹ * y⁻¹ * x * y ∈ SD ⊓ aschbacherThm5Core D := ⟨h2, h1⟩
        rwa [hinf, Subgroup.mem_bot] at hmem
      calc x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
        _ = y * x := by rw [h3, mul_one]
    have heq := commuting_noncyclic_eq hRtype hPa hPb
      (factor_sylow_not_cyclic hC.hyp a (hfactorSyl a))
      (factor_sylow_not_cyclic hC.hyp b (hfactorSyl b)) hcommab
    exact sylow_not_le_factor hC.hyp hab (hfactorSyl a) (heq ▸ inf_le_right)

end SectionSix

end CFSG.ComponentClassification.AschbacherTheorem5
