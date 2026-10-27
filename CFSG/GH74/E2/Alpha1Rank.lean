module

public import CFSG.GH74.E2.SD16Cert
public import CFSG.GH74.E2.Cl2Quot
public import CFSG.GH74.E2.FrattiniRank
public import CFSG.GH74.E2.DirectProd
public import CFSG.CharacterTheory.Semidihedral.Presentation
public import CFSG.CharacterTheory.Semidihedral.NormalForm
public meta import Mathlib
public meta import CFSG.CharacterTheory.Semidihedral.Model
public import CFSG.GH74.E2.Cl2Rank
public import CFSG.GH74.Uniqueness.SU.SU1BgMaxClass
public import CFSG.GH74.Uniqueness.SU.SU1BgTwoMaxClass
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Defs
public import CFSG.GH74.GLS.Statements
public import CFSG.GH74.SectionalRank
public import CFSG.GroupTheory.FrattiniQuotient
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Critical

public section

namespace CFSG.GH74.E2

open Subgroup

section Centralizer

variable {G : Type*} [Group G]

theorem klein_eq {W : Subgroup G} {t t' : G} (hW4 : Nat.card W = 4)
    (hW2 : ∀ w ∈ W, w * w = 1) (htW : t ∈ W) (ht'W : t' ∈ W) (ht1 : t ≠ 1) (ht'1 : t' ≠ 1)
    (hne : t ≠ t') : (W : Set G) = {1, t, t', t * t'} := by
  have hsub : ({1, t, t', t * t'} : Set G) ⊆ (W : Set G) := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl
    · exact W.one_mem
    · exact htW
    · exact ht'W
    · exact W.mul_mem htW ht'W
  have ht2 : t * t = 1 := hW2 t htW
  have hT4 : ({1, t, t', t * t'} : Set G).ncard = 4 := by
    have h1 : (1 : G) ≠ t := fun h => ht1 h.symm
    have h2 : (1 : G) ≠ t' := fun h => ht'1 h.symm
    have h3 : (1 : G) ≠ t * t' := by
      intro h
      apply hne
      calc t = t⁻¹ := (inv_eq_of_mul_eq_one_right ht2).symm
        _ = t' := by
          calc t⁻¹ = t⁻¹ * (t * t') := by rw [← h]; group
            _ = t' := by group
    have h4 : t ≠ t' := hne
    have h5 : t ≠ t * t' := by
      intro h
      apply ht'1
      calc t' = t⁻¹ * (t * t') := by group
        _ = t⁻¹ * t := by rw [← h]
        _ = 1 := by group
    have h6 : t' ≠ t * t' := by
      intro h
      apply ht1
      calc t = t * t' * t'⁻¹ := by group
        _ = t' * t'⁻¹ := by rw [← h]
        _ = 1 := by group
    rw [Set.ncard_insert_of_notMem (by simp [h1, h2, h3]),
      Set.ncard_insert_of_notMem (by simp [h4, h5]), Set.ncard_pair h6]
  have hW4' : (W : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hW4
  have hfin : (W : Set G).Finite := by
    apply Set.finite_of_ncard_ne_zero
    rw [hW4']; norm_num
  exact (Set.eq_of_subset_of_ncard_le hsub (by rw [hT4, hW4']) hfin).symm

theorem exists_second_involution {W : Subgroup G} {t' : G} (hW4 : Nat.card W = 4)
    (ht'1 : t' ≠ 1) : ∃ s ∈ W, s ≠ 1 ∧ s ≠ t' := by
  by_contra hcon
  have hsub : (W : Set G) ⊆ {1, t'} := by
    intro s hs
    by_contra hn
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hn
    exact hcon ⟨s, hs, hn.1, hn.2⟩
  have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_pair (Ne.symm ht'1)] at h1
  have hW4' : (W : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]; exact hW4
  omega

end Centralizer

section MaximalClass

theorem quaternionGroup_involution_eq_a (n : ℕ) [NeZero n] {q : QuaternionGroup n}
    (hq2 : q * q = 1) (hq1 : q ≠ 1) : q = QuaternionGroup.a (n : ZMod (2 * n)) := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  cases q with
  | a i =>
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at hq2
    have h2 : ((2 * i.val : ℕ) : ZMod (2 * n)) = 0 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      push_cast
      rw [two_mul i, hq2]
    rw [ZMod.natCast_eq_zero_iff] at h2
    have h3 : n ∣ i.val := Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 2) h2
    obtain ⟨c, hc⟩ := h3
    have hlt : i.val < 2 * n := ZMod.val_lt i
    have hc2 : c < 2 := by
      by_contra hcon
      have : 2 * n ≤ n * c := by nlinarith
      omega
    interval_cases c
    · exfalso
      apply hq1
      have : i = 0 := by
        rw [← ZMod.natCast_zmod_val i, hc]; simp
      rw [this, QuaternionGroup.one_def]
    · congr 1
      rw [← ZMod.natCast_zmod_val i, hc]; simp
  | xa i =>
    rw [QuaternionGroup.xa_mul_xa, QuaternionGroup.one_def, QuaternionGroup.a.injEq] at hq2
    have h2 : (n : ZMod (2 * n)) = 0 := by
      have : (n : ZMod (2 * n)) + i - i = 0 := hq2
      simpa using this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd hn h2
    omega

variable {G : Type} [Group G]

theorem not_klein_quaternion {R W : Subgroup G} {t' : G} {n : ℕ} [NeZero n]
    (e : ↥R ≃* QuaternionGroup n) (hWR : W ≤ R) (hW4 : Nat.card W = 4)
    (ht'W : t' ∈ W) (ht'1 : t' ≠ 1) (hW2 : ∀ w ∈ W, w * w = 1) : False := by
  obtain ⟨s, hsW, hs1, hst'⟩ := exists_second_involution hW4 ht'1
  have key : ∀ (w : G) (hw : w ∈ W), w ≠ 1 →
      e ⟨w, hWR hw⟩ = QuaternionGroup.a (n : ZMod (2 * n)) := by
    intro w hw hw1
    apply quaternionGroup_involution_eq_a n
    · rw [← map_mul]
      have : (⟨w, hWR hw⟩ : ↥R) * ⟨w, hWR hw⟩ = 1 := Subtype.ext (hW2 w hw)
      rw [this, map_one]
    · intro h
      apply hw1
      have : (⟨w, hWR hw⟩ : ↥R) = 1 := e.injective (by rw [h, map_one])
      exact congrArg Subtype.val this
  have h1 := key t' ht'W ht'1
  have h2 := key s hsW hs1
  have : (⟨t', hWR ht'W⟩ : ↥R) = ⟨s, hWR hsW⟩ := e.injective (h1.trans h2.symm)
  exact hst' (congrArg Subtype.val this).symm

theorem dihedral_of_order_eight [Finite G] {R W : Subgroup G} {t' : G}
    (hR8 : Nat.card R = 8) (hWR : W ≤ R) (hW4 : Nat.card W = 4) (hW2 : ∀ w ∈ W, w * w = 1)
    (ht'W : t' ∈ W) (ht'1 : t' ≠ 1) (hcent : ∀ r ∈ R, r * t' = t' * r → r ∈ W) :
    Nonempty (↥R ≃* DihedralGroup (2 ^ 2)) := by
  classical
  have hidx : (W.subgroupOf R).index = 2 := by
    have h1 := Subgroup.card_mul_index (W.subgroupOf R)
    have h2 : Nat.card (W.subgroupOf R) = Nat.card W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv
    rw [h2, hW4, hR8] at h1
    omega
  have hS : ∀ g ∈ R, g * g ∈ W := by
    intro g hg
    have := Subgroup.mul_self_mem_of_index_two hidx ⟨g, hg⟩
    exact this
  have hN : ∀ g ∈ R, ∀ w ∈ W, g * w * g⁻¹ ∈ W := by
    intro g hg w hw
    have hNorm : (W.subgroupOf R).Normal := Subgroup.normal_of_index_eq_two hidx
    have := hNorm.conj_mem ⟨w, hWR hw⟩ hw ⟨g, hg⟩
    exact this
  have hWcomm : ∀ w ∈ W, ∀ w' ∈ W, w * w' = w' * w := by
    intro w hw w' hw'
    have h1 : w * w' * (w * w') = 1 := hW2 _ (W.mul_mem hw hw')
    have h2 : w⁻¹ = w := inv_eq_of_mul_eq_one_right (hW2 w hw)
    have h3 : w'⁻¹ = w' := inv_eq_of_mul_eq_one_right (hW2 w' hw')
    have h4 : w * w' = (w * w')⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [h4, mul_inv_rev, h2, h3]
  obtain ⟨g, hgR, hgW⟩ : ∃ g ∈ R, g ∉ W := by
    by_contra hcon
    have hle : R ≤ W := fun g hg => by
      by_contra h
      exact hcon ⟨g, hg, h⟩
    have := Subgroup.card_le_of_le hle
    omega
  have hgt' : g * t' ≠ t' * g := fun h => hgW (hcent g hgR h)
  obtain ⟨t'', ht''⟩ : ∃ t'' : G, t'' = g * t' * g⁻¹ := ⟨_, rfl⟩
  have ht''W : t'' ∈ W := ht'' ▸ hN g hgR t' ht'W
  have ht''1 : t'' ≠ 1 := by
    intro h
    apply ht'1
    calc t' = g⁻¹ * (g * t' * g⁻¹) * g := by group
      _ = 1 := by rw [← ht'', h]; group
  have ht't'' : t' ≠ t'' := by
    intro h
    apply hgt'
    calc g * t' = (g * t' * g⁻¹) * g := by group
      _ = t' * g := by rw [← ht'', ← h]
  have ht2 : t' * t' = 1 := hW2 t' ht'W
  have hWk := klein_eq hW4 hW2 ht'W ht''W ht'1 ht''1 ht't''
  obtain ⟨z, hz⟩ : ∃ z : G, z = t' * t'' := ⟨_, rfl⟩
  have hzW : z ∈ W := hz ▸ W.mul_mem ht'W ht''W
  have hz1 : z ≠ 1 := by
    intro h
    apply ht't''
    calc t' = t'⁻¹ := (inv_eq_of_mul_eq_one_right ht2).symm
      _ = t'' := by
        calc t'⁻¹ = t'⁻¹ * (t' * t'') := by rw [← hz, h, mul_one]
          _ = t'' := by group
  have hz2 : z * z = 1 := hW2 z hzW
  have hg2W : g * g ∈ W := hS g hgR
  have hgt'' : g * t'' * g⁻¹ = t' := by
    have hc : t' * (g * g) = (g * g) * t' := hWcomm t' ht'W _ hg2W
    calc g * t'' * g⁻¹ = g * (g * t' * g⁻¹) * g⁻¹ := by rw [← ht'']
      _ = (g * g) * t' * (g * g)⁻¹ := by group
      _ = t' * (g * g) * (g * g)⁻¹ := by rw [hc]
      _ = t' := by group
  obtain ⟨ρ, hρR, hρW, hρ2, hρt'⟩ : ∃ ρ ∈ R, ρ ∉ W ∧ ρ * ρ = z ∧ ρ * t' * ρ⁻¹ = t'' := by
    by_cases hg2 : g * g = 1
    · refine ⟨t' * g, R.mul_mem (hWR ht'W) hgR, ?_, ?_, ?_⟩
      · intro h
        apply hgW
        have : g = t'⁻¹ * (t' * g) := by group
        rw [this]
        exact W.mul_mem (W.inv_mem ht'W) h
      · calc t' * g * (t' * g) = t' * (g * t' * g⁻¹) * (g * g) := by group
          _ = t' * t'' * 1 := by rw [← ht'', hg2]
          _ = z := by rw [hz, mul_one]
      · calc t' * g * t' * (t' * g)⁻¹ = t' * (g * t' * g⁻¹) * t'⁻¹ := by group
          _ = t' * t'' * t'⁻¹ := by rw [← ht'']
          _ = t'' * t' * t'⁻¹ := by rw [hWcomm t' ht'W t'' ht''W]
          _ = t'' := by group
    · refine ⟨g, hgR, hgW, ?_, by rw [← ht'']⟩
      have hfix : g * (g * g) * g⁻¹ = g * g := by group
      have hmem : g * g ∈ ({1, t', t'', t' * t''} : Set G) := by rw [← hWk]; exact hg2W
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h | h
      · exact absurd h hg2
      · exfalso
        rw [h, ← ht''] at hfix
        exact ht't'' hfix.symm
      · exfalso
        rw [h, hgt''] at hfix
        exact ht't'' hfix
      · rw [h, hz]
  have hρ4' : ρ ^ 4 = 1 := by
    calc ρ ^ 4 = ρ * ρ * ρ * ρ := by simp only [pow_succ, pow_zero, one_mul]
      _ = (ρ * ρ) * (ρ * ρ) := by group
      _ = 1 := by rw [hρ2, hz2]
  have hρ4 : orderOf ρ = 2 ^ 2 := by
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · simpa [pow_two, hρ2] using hz1
    · simpa using hρ4'
  have hρ3 : ρ⁻¹ = z * ρ := by
    have h4 : ρ * ρ * (ρ * ρ) = 1 := by rw [hρ2, hz2]
    calc ρ⁻¹ = ρ⁻¹ * (ρ * ρ * (ρ * ρ)) := by rw [h4, mul_one]
      _ = (ρ * ρ) * ρ := by group
      _ = z * ρ := by rw [hρ2]
  have hrelG : t' * ρ * t'⁻¹ = ρ⁻¹ := by
    have ht'inv : t'⁻¹ = t' := inv_eq_of_mul_eq_one_right ht2
    calc t' * ρ * t'⁻¹ = t' * ρ * t' := by rw [ht'inv]
      _ = t' * (ρ * t' * ρ⁻¹) * ρ := by group
      _ = t' * t'' * ρ := by rw [hρt']
      _ = z * ρ := by rw [hz]
      _ = ρ⁻¹ := hρ3.symm
  let ρ' : ↥R := ⟨ρ, hρR⟩
  let σ' : ↥R := ⟨t', hWR ht'W⟩
  have hσ2 : σ' ^ 2 = 1 := Subtype.ext (by simpa [σ', pow_two] using ht2)
  have hrel : σ' * ρ' * σ'⁻¹ = ρ'⁻¹ := Subtype.ext (by simpa [σ', ρ'] using hrelG)
  have hσρ : σ' ∉ zpowers ρ' := by
    intro h
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 h
    have hj' : ρ ^ j = t' := by
      have := congrArg Subtype.val hj
      simpa [σ', ρ'] using this
    apply ht't''
    calc t' = ρ ^ j := hj'.symm
      _ = ρ * ρ ^ j * ρ⁻¹ := by group
      _ = ρ * t' * ρ⁻¹ := by rw [hj']
      _ = t'' := hρt'
  have hord' : orderOf ρ' = 4 := by
    have := Subgroup.orderOf_coe ρ'
    rw [show ((ρ' : ↥R) : G) = ρ from rfl, hρ4] at this
    simpa using this.symm
  have hgen : ⊤ = zpowers ρ' ⊔ zpowers σ' := by
    have hle : zpowers ρ' ≤ zpowers ρ' ⊔ zpowers σ' := le_sup_left
    have hcard4 : Nat.card (zpowers ρ') = 4 := by rw [Nat.card_zpowers, hord']
    obtain ⟨N, hN⟩ : ∃ N, N = Nat.card (zpowers ρ' ⊔ zpowers σ' : Subgroup ↥R) := ⟨_, rfl⟩
    have hdvd1 : 4 ∣ N := by
      rw [hN, ← hcard4]; exact Subgroup.card_dvd_of_le hle
    have hdvd2 : N ∣ 8 := by
      rw [hN, ← hR8]; exact Subgroup.card_subgroup_dvd_card _
    have hne4 : N ≠ 4 := by
      intro h
      have heq : zpowers ρ' = zpowers ρ' ⊔ zpowers σ' :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [← hN, h, hcard4])
      apply hσρ
      rw [heq]
      exact (le_sup_right : zpowers σ' ≤ zpowers ρ' ⊔ zpowers σ') (Subgroup.mem_zpowers σ')
    have h8 : N = 8 := by
      have hle8 := Nat.le_of_dvd (by norm_num) hdvd2
      have hpos : 0 < N := Nat.pos_of_dvd_of_pos hdvd2 (by norm_num)
      obtain ⟨c, hc⟩ := hdvd1
      omega
    exact (Subgroup.eq_top_of_card_eq _ (by rw [← hN, h8, hR8])).symm
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ' σ' hgen hσ2 hrel hσρ
  rw [hord'] at e
  exact ⟨e⟩

theorem dihedral_or_semidihedral_of_selfcentralizing [Finite G] {R W : Subgroup G} {t' : G}
    (hR : IsPGroup 2 R) (hWR : W ≤ R) (hW4 : Nat.card W = 4) (hW2 : ∀ w ∈ W, w * w = 1)
    (ht'W : t' ∈ W) (ht'1 : t' ≠ 1) (hWne : W ≠ R)
    (hcent : ∀ r ∈ R, r * t' = t' * r → r ∈ W) :
    (∃ a : ℕ, 2 ≤ a ∧ Nonempty (↥R ≃* DihedralGroup (2 ^ a))) ∨
      ∃ m : ℕ, 4 ≤ m ∧ Nonempty (↥R ≃* CFSG.Open.SemidihedralGroup m) := by
  classical
  have hdvd : 4 ∣ Nat.card R := by
    rw [← hW4]; exact Subgroup.card_dvd_of_le hWR
  have hpos : 0 < Nat.card R := Nat.card_pos
  have hne4 : Nat.card R ≠ 4 := by
    intro h
    apply hWne
    exact Subgroup.eq_of_le_of_card_ge hWR (by rw [h, hW4])
  have h8 : 8 ≤ Nat.card R := by
    obtain ⟨c, hc⟩ := hdvd
    omega
  have hcard : Nat.card (centralizer ({(⟨t', hWR ht'W⟩ : ↥R)} : Set ↥R)) ≤ 2 ^ 2 := by
    have hinj : Function.Injective (fun g : centralizer ({(⟨t', hWR ht'W⟩ : ↥R)} : Set ↥R) =>
        (⟨(g : ↥R).1, hcent (g : ↥R).1 (g : ↥R).2 (by
          have := Subgroup.mem_centralizer_singleton_iff.1 g.2
          exact congrArg Subtype.val this)⟩ : ↥W)) := by
      intro a b h
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun w : ↥W => (w : G)) h
      simpa using this
    have := Nat.card_le_card_of_injective _ hinj
    rw [hW4] at this
    simpa using this
  obtain ⟨m, hm, hγ⟩ := CFSG.GH74.Uniqueness.SU.SU1.b_maximalClass_of_small_centralizer 2
    Nat.prime_two ↥R hR (by norm_num; omega) _ hcard
  rcases Nat.lt_or_ge 8 (Nat.card R) with hlt | hge
  · rcases CFSG.GH74.Uniqueness.SU.SU1.b_two_maximalClass_shape ↥R hR hlt m hm hγ with
      ⟨k, hk1, ⟨e⟩⟩ | ⟨k, hk1, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · left
      refine ⟨k, ?_, ⟨e⟩⟩
      have : NeZero (2 ^ k) := ⟨by positivity⟩
      have hc := Nat.card_congr e.toEquiv
      rw [DihedralGroup.nat_card] at hc
      by_contra hk
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exfalso
      have : NeZero (2 ^ k) := ⟨by positivity⟩
      exact not_klein_quaternion e hWR hW4 ht'W ht'1 hW2
    · exact Or.inr ⟨n, hn, ⟨e⟩⟩
  · left
    have hR8 : Nat.card R = 8 := le_antisymm hge h8
    exact ⟨2, le_refl _, dihedral_of_order_eight hR8 hWR hW4 hW2 ht'W ht'1 hcent⟩

end MaximalClass

end CFSG.GH74.E2
