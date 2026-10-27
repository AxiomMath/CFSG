module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Basic
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2OuterInvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2TorusCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.GorensteinWalter
open scoped Pointwise

universe u

abbrev pslRange (K : Type u) [Field K] : Subgroup (PGL2 K) :=
  (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range

@[expose] def outerTorusOrder (q : ℕ) : ℕ := if q % 4 = 1 then q + 1 else q - 1

theorem outerTorusOrder_mod_four {q : ℕ} (hq : Odd q) : outerTorusOrder q % 4 = 2 := by
  obtain ⟨k, rfl⟩ := hq
  unfold outerTorusOrder
  split_ifs with h <;> omega

theorem six_le_outerTorusOrder {q : ℕ} (hq : Odd q) (h5 : 5 ≤ q) : 6 ≤ outerTorusOrder q := by
  obtain ⟨k, rfl⟩ := hq
  unfold outerTorusOrder
  split_ifs with h <;> omega

theorem outerTorusOrder_eq {q : ℕ} : outerTorusOrder q = q + 1 ∨ outerTorusOrder q = q - 1 := by
  unfold outerTorusOrder
  split_ifs <;> simp

theorem pslRange_index_eq_two {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : (pslRange K).index = 2 :=
  pgl2_psl2Range_index_eq_two K hK

theorem pslRange_normal {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) : (pslRange K).Normal := by
  rw [pslRange, ← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
  infer_instance

theorem odd_card_of_isOddPrimePower {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) : Odd (Nat.card K) := by
  obtain ⟨p, n, _, hp, _, hn⟩ := hK
  rw [hn]
  exact hp.pow

theorem centralizer_conj {G : Type*} [Group G] (h s : G) :
    Subgroup.centralizer ({h * s * h⁻¹} : Set G) =
      (Subgroup.centralizer ({s} : Set G)).map (MulAut.conj h).toMonoidHom := by
  ext x
  simp only [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · intro hx
    refine ⟨h⁻¹ * x * h, ?_, by group⟩
    calc h⁻¹ * x * h * s = h⁻¹ * (x * (h * s * h⁻¹)) * h := by group
      _ = h⁻¹ * ((h * s * h⁻¹) * x) * h := by rw [hx]
      _ = s * (h⁻¹ * x * h) := by group
  · rintro ⟨y, hy, rfl⟩
    calc h * y * h⁻¹ * (h * s * h⁻¹) = h * (y * s) * h⁻¹ := by group
      _ = h * (s * y) * h⁻¹ := by rw [hy]
      _ = h * s * h⁻¹ * (h * y * h⁻¹) := by group

theorem zpowers_le_normalizer_of_inverting {G : Type*} [Group G] {U : Subgroup G} {w : G}
    (hww : w * w = 1) (hwinv : ∀ x ∈ U, w * x * w⁻¹ = x⁻¹) :
    Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [hwinv x hx]
    exact U.inv_mem hx
  · intro hx
    have h1 := hwinv _ hx
    have h2 : w * (w * x * w⁻¹) * w⁻¹ = x := by
      calc w * (w * x * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
        _ = x := by rw [hww]; group
    rw [h2] at h1
    rw [h1]
    exact U.inv_mem hx

theorem outer_involution_centralizer {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {g : PGL2 K}
    (hg : g ^ 2 = 1) (hgJ : g ∉ pslRange K) :
    ∃ (U : Subgroup (PGL2 K)) (w : PGL2 K), IsCyclic U ∧
      Nat.card U = outerTorusOrder (Nat.card K) ∧ g ∈ U ∧ w ∉ U ∧ w * w = 1 ∧
      (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({g} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hqodd := odd_card_of_isOddPrimePower hK
  have hJ2 := pslRange_index_eq_two hK
  have : (pslRange K).Normal := pslRange_normal hK hcard
  obtain ⟨U, s, w, hUc, hUcard, hsU, hss, hs1, hwU, hww, hwinv, hC, hUJ⟩ :
      ∃ (U : Subgroup (PGL2 K)) (s w : PGL2 K), IsCyclic U ∧
        Nat.card U = outerTorusOrder (Nat.card K) ∧ s ∈ U ∧ s * s = 1 ∧ s ≠ 1 ∧ w ∉ U ∧
        w * w = 1 ∧ (∀ x ∈ U, w * x * w⁻¹ = x⁻¹) ∧
        Subgroup.centralizer ({s} : Set (PGL2 K)) = U ⊔ Subgroup.zpowers w ∧
        ¬ U ≤ pslRange K := by
    by_cases h : Nat.card K % 4 = 1
    · obtain ⟨U, s, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        pgl2_nonsplit_torus_centralizer_data K hqodd
      exact ⟨U, s, w, h1, by rw [h2]; simp [outerTorusOrder, h], h3, h4, h5, h6, h7, h8, h9,
        h10 hqodd⟩
    · obtain ⟨U, s, w, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ :=
        pgl2_split_torus_centralizer_data K hqodd
      exact ⟨U, s, w, h1, by rw [h2]; simp [outerTorusOrder, h], h3, h4, h5, h6, h7, h8, h9,
        h10 hqodd⟩
  have hsJ : s ∉ pslRange K := by
    intro hsJ
    have hdvd : (pslRange K).relIndex U ∣ 2 := by
      have := Subgroup.relIndex_dvd_index_of_normal (pslRange K) U
      rwa [hJ2] at this
    have hrel : (pslRange K).relIndex U = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (Subgroup.relIndex_eq_one.mp h1) hUJ
      · exact h2
    have hcardUJ : Nat.card ((pslRange K).subgroupOf U) * 2 = Nat.card U := by
      have h := ((pslRange K).subgroupOf U).card_mul_index
      have hrel' : ((pslRange K).subgroupOf U).index = 2 := hrel
      rw [hrel'] at h
      exact h
    have hmod := outerTorusOrder_mod_four hqodd
    have hodd : ¬ 2 ∣ Nat.card ((pslRange K).subgroupOf U) := by
      intro h2
      obtain ⟨c, hc⟩ := h2
      rw [hUcard] at hcardUJ
      omega
    let s' : (pslRange K).subgroupOf U := ⟨⟨s, hsU⟩, hsJ⟩
    have hs' : orderOf s' = 2 := by
      apply orderOf_eq_prime
      · exact Subtype.ext (Subtype.ext (by rw [pow_two]; exact hss))
      · intro h
        exact hs1 (congrArg Subtype.val (congrArg Subtype.val h))
    have h := orderOf_dvd_natCard s'
    rw [hs'] at h
    exact hodd h
  have hcomm : commutator (PGL2 K) = pslRange K :=
    pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard
  have hg1 : g ≠ 1 := fun h => hgJ (h ▸ (pslRange K).one_mem)
  have hconj : IsConj s g :=
    pgl2_outer_involutions_conjugate K hK hcard ⟨hs1, by rw [pow_two]; exact hss⟩ ⟨hg1, hg⟩
      (by rw [hcomm]; exact hsJ) (by rw [hcomm]; exact hgJ)
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  let φ : PGL2 K →* PGL2 K := (MulAut.conj c).toMonoidHom
  have hφinj : Function.Injective φ := (MulAut.conj c).injective
  have hφ : ∀ x, φ x = c * x * c⁻¹ := fun x => rfl
  refine ⟨U.map φ, c * w * c⁻¹, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (MulEquiv.isCyclic (U.equivMapOfInjective φ hφinj)).mp hUc
  · rw [← hUcard]
    exact (Nat.card_congr (U.equivMapOfInjective φ hφinj).toEquiv).symm
  · exact ⟨s, hsU, by rw [hφ, hc]⟩
  · rintro ⟨x, hx, hxw⟩
    rw [hφ] at hxw
    have : x = w := by
      have := congrArg (fun y => c⁻¹ * y * c) hxw
      simpa [mul_assoc] using this
    exact hwU (this ▸ hx)
  · calc c * w * c⁻¹ * (c * w * c⁻¹) = c * (w * w) * c⁻¹ := by group
      _ = 1 := by rw [hww]; group
  · rintro x ⟨y, hy, rfl⟩
    rw [hφ]
    calc c * w * c⁻¹ * (c * y * c⁻¹) * (c * w * c⁻¹)⁻¹ = c * (w * y * w⁻¹) * c⁻¹ := by group
      _ = c * y⁻¹ * c⁻¹ := by rw [hwinv y hy]
      _ = (c * y * c⁻¹)⁻¹ := by group
  · rw [← hc, centralizer_conj, hC, Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl

theorem card_outer_involution_centralizer {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {g : PGL2 K}
    (hg : g ^ 2 = 1) (hgJ : g ∉ pslRange K) :
    Nat.card (Subgroup.centralizer ({g} : Set (PGL2 K))) =
      2 * outerTorusOrder (Nat.card K) := by
  obtain ⟨U, w, -, hUcard, -, hwU, hww, hwinv, hC⟩ := outer_involution_centralizer hK hcard hg hgJ
  rw [hC, card_sup_eq_mul_of_disjoint_of_le_normalizer, hUcard, Nat.card_zpowers, mul_comm]
  · congr 1
    apply orderOf_eq_prime
    · rw [pow_two]; exact hww
    · rintro rfl
      exact hwU U.one_mem
  · exact zpowers_le_normalizer_of_inverting hww hwinv
  · rw [Subgroup.disjoint_def]
    intro x hxU hxw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxw
    have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hww
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, hw2, one_zpow]
    · exfalso
      apply hwU
      rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, hw2, one_zpow, one_mul,
        zpow_one] at hxU
      exact hxU

theorem outer_involution_centralizer_center {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) {g : PGL2 K}
    (hg : g ^ 2 = 1) (hgJ : g ∉ pslRange K) :
    ∀ y ∈ Subgroup.centralizer ({g} : Set (PGL2 K)),
      (∀ m ∈ Subgroup.centralizer ({g} : Set (PGL2 K)), y * m = m * y) →
        y ∈ Subgroup.zpowers g := by
  classical
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨U, w, hUc, hUcard, hgU, hwU, hww, hwinv, hC⟩ :=
    outer_involution_centralizer hK hcard hg hgJ
  have hqodd := odd_card_of_isOddPrimePower hK
  have h6 : 6 ≤ Nat.card U := hUcard ▸ six_le_outerTorusOrder hqodd (by
    obtain ⟨p, n, hp, hpodd, hn, hq⟩ := hK
    rcases hqodd with ⟨k, hk⟩
    omega)
  have hg1 : g ≠ 1 := fun h => hgJ (h ▸ (pslRange K).one_mem)
  have hw' : w⁻¹ = w := by
    rw [inv_eq_iff_mul_eq_one]
    exact hww
  have hnorm : Subgroup.zpowers w ≤ Subgroup.normalizer (U : Set (PGL2 K)) :=
    zpowers_le_normalizer_of_inverting hww hwinv
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    have := hUc.commGroup.mul_comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  intro y hy hcent
  rw [hC] at hy
  have hy' : y ∈ (U : Set (PGL2 K)) * (Subgroup.zpowers w : Set (PGL2 K)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left U _ hnorm]
    exact hy
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hw2 : w ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hww
  have hwC : w ∈ Subgroup.centralizer ({g} : Set (PGL2 K)) := by
    rw [hC]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  have hUC : U ≤ Subgroup.centralizer ({g} : Set (PGL2 K)) := by
    rw [hC]
    exact le_sup_left
  rcases Int.emod_two_eq_zero_or_one k with hk | hk
  · rw [← Int.mul_ediv_add_emod k 2, hk, add_zero, zpow_mul, hw2, one_zpow, mul_one] at hcent ⊢
    have h1 : w * u * w⁻¹ = u := by
      rw [← hcent w hwC]
      group
    rw [hwinv u hu] at h1
    have hu2 : u ^ 2 = 1 := by
      rw [pow_two]
      calc u * u = u * u⁻¹ := by rw [h1]
        _ = 1 := by group
    by_cases hu1 : u = 1
    · rw [hu1]
      exact Subgroup.one_mem _
    · have : (⟨u, hu⟩ : U) = ⟨g, hgU⟩ :=
        eq_of_sq_eq_one_of_isCyclic (Subtype.ext hu2) (Subtype.ext hg)
          (fun h => hu1 (congrArg Subtype.val h)) (fun h => hg1 (congrArg Subtype.val h))
      rw [show u = g from congrArg Subtype.val this]
      exact Subgroup.mem_zpowers g
  · exfalso
    rw [← Int.mul_ediv_add_emod k 2, hk, zpow_add, zpow_mul, hw2, one_zpow, one_mul,
      zpow_one] at hcent
    have hsq : ∀ x : U, x ^ 2 = 1 := by
      intro x
      have h1 := hcent x (hUC x.2)
      have h2 : u * w * x * (u * w)⁻¹ = x := by rw [h1]; group
      have h3 : u * w * x * (u * w)⁻¹ = (x : PGL2 K)⁻¹ := by
        calc u * w * x * (u * w)⁻¹ = u * (w * x * w⁻¹) * u⁻¹ := by group
          _ = u * (x : PGL2 K)⁻¹ * u⁻¹ := by rw [hwinv x x.2]
          _ = (x : PGL2 K)⁻¹ := by
            rw [hUcomm u hu _ (U.inv_mem x.2)]
            group
      apply Subtype.ext
      rw [Subgroup.coe_pow, OneMemClass.coe_one, pow_two]
      calc (x : PGL2 K) * x = x * (x : PGL2 K)⁻¹ := by rw [← h3, h2]
        _ = 1 := by group
    let _ : Fintype U := Fintype.ofFinite U
    have hle := IsCyclic.card_pow_eq_one_le (α := U) (n := 2) two_pos
    have hall : (Finset.univ.filter (fun a : U => a ^ 2 = 1)) = Finset.univ := by
      ext x
      simp [hsq x]
    rw [hall, Finset.card_univ, ← Nat.card_eq_fintype_card] at hle
    omega

theorem pgl2_dihedral_sylow {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    ∃ (S : Sylow 2 (PGL2 K)) (m : ℕ), Nonempty ((S : Subgroup (PGL2 K)) ≃*
      DihedralGroup (2 ^ m)) := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let S : Sylow 2 (PGL2 K) := Classical.choice Sylow.nonempty
  obtain ⟨m, -, he⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK S
  exact ⟨S, m, he⟩

theorem pgl2_eq_of_commute_orderOf_four {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {c v : PGL2 K} (hc : orderOf c = 4) (hv : v ^ 2 = 1)
    (hcv : c * v = v * c) : v = 1 ∨ v = c ^ 2 := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨S, m, ⟨e⟩⟩ := pgl2_dihedral_sylow hK
  exact eq_of_commute_orderOf_four_of_dihedral S e hc hv hcv

theorem pgl2_not_quaternion_pair {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {c d : PGL2 K} (hc : orderOf c = 4)
    (hd : d ^ 2 = c ^ 2) (hdc : d * c * d⁻¹ = c⁻¹) : False := by
  let : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨S, m, ⟨e⟩⟩ := pgl2_dihedral_sylow hK
  exact not_quaternion_pair_of_dihedral S e hc hd hdc

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
