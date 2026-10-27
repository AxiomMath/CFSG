module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Bypass

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer Assembly.LowTwoRank

theorem isCoverOf_congr {τ : StatedLieTag} {n p f c : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : IsCoverOf τ n p f c A) : IsCoverOf τ n p f c B := by
  obtain ⟨hq, hc, hm⟩ := h
  refine ⟨LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hm⟩
  rw [← Subgroup.map_center_eq e, Subgroup.card_map_of_injective e.injective, hc]

section Image

variable {H : Type} [Group H] [Finite H] (A : Subgroup H)

abbrev imageHom : ↥A →* H ⧸ pPrimeCore 2 H :=
  (QuotientGroup.mk' (pPrimeCore 2 H)).comp A.subtype

theorem ker_eq_pPrimeCore (hn : A.Normal) : (imageHom A).ker = pPrimeCore 2 ↥A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  ·
    refine le_pPrimeCore_of_normal_of_odd (MonoidHom.normal_ker _) ?_
    have hle : (imageHom A).ker.map A.subtype ≤ pPrimeCore 2 H := by
      rintro _ ⟨x, hx, rfl⟩
      exact (QuotientGroup.eq_one_iff _).mp hx
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective A.subtype_injective] at hdvd
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) hdvd
  ·
    intro x hx
    have h := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hn.isSubnormal ⟨x, hx, rfl⟩
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr h

omit [Finite H] in
theorem normal_range (hn : A.Normal) : (imageHom A).range.Normal := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact hn.map _ (QuotientGroup.mk'_surjective _)

omit [Finite H] in
theorem index_range_dvd : (imageHom A).range.index ∣ A.index := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)

end Image

section Reduce

variable {G : Type} [Group G] [Finite G]

theorem isCoverOf_range {H L : Subgroup G} (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal)
    {τ : StatedLieTag} {n p f c : ℕ} (h : IsCoverOf τ n p f c (↥L ⧸ pPrimeCore 2 ↥L)) :
    IsCoverOf τ n p f c ↥(imageHom (L.subgroupOf H)).range := by
  let e := subgroupOfEquivOfLe hLH
  have hO : (pPrimeCore 2 ↥(L.subgroupOf H)).map (e : ↥(L.subgroupOf H) →* ↥L) =
      pPrimeCore 2 ↥L := pPrimeCore_map_iso 2 e
  refine isCoverOf_congr ?_ h
  exact (QuotientGroup.congr _ _ e hO).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq (ker_eq_pPrimeCore _ hn).symm).trans
      (QuotientGroup.quotientKerEquivRange _))

theorem not_two_dvd_index_range {H L : Subgroup G} (hLH : L ≤ H) (S : Sylow 2 G)
    (hSL : (S : Subgroup G) ≤ L) : ¬ 2 ∣ (imageHom (L.subgroupOf H)).range.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  apply S.not_dvd_index
  refine h2.trans ((index_range_dvd _).trans ?_)
  change L.relIndex H ∣ (S : Subgroup G).index
  rw [← relIndex_mul_index hSL, ← relIndex_mul_index hLH]
  exact (dvd_mul_right _ _).mul_left _

theorem mem_pPrimeCore_of_mem {H L : Subgroup G} (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal)
    {c : G} (hcL : c ∈ L) (hc : (⟨c, hLH hcL⟩ : ↥H) ∈ pPrimeCore 2 ↥H) :
    (⟨c, hcL⟩ : ↥L) ∈ pPrimeCore 2 ↥L := by
  let a : ↥(L.subgroupOf H) := ⟨⟨c, hLH hcL⟩, mem_subgroupOf.mpr hcL⟩
  have ha : a ∈ pPrimeCore 2 ↥(L.subgroupOf H) := by
    rw [← ker_eq_pPrimeCore _ hn, MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  rw [← pPrimeCore_map_iso 2 (subgroupOfEquivOfLe hLH)]
  exact ⟨a, ha, rfl⟩

theorem centralizer_range_le {H L : Subgroup G} (hLH : L ≤ H) (hn : (L.subgroupOf H).Normal)
    (hQ : H ⊓ coreActionKernel L ≤ (pPrimeCore 2 ↥H).map H.subtype ⊔ L) :
    centralizer ((imageHom (L.subgroupOf H)).range : Set (↥H ⧸ pPrimeCore 2 ↥H)) ≤
      (imageHom (L.subgroupOf H)).range := by
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H)
  have hHN : H ≤ normalizer (L : Set G) := le_normalizer_of_normal_subgroupOf hLH
  intro xb hxb
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) xb
  have hxQ : (x : G) ∈ coreActionKernel L := by
    refine ⟨hHN x.2, fun l hl => ?_⟩
    have hc : l⁻¹ * (x : G)⁻¹ * l * x ∈ L := by
      have h := (mem_normalizer_iff.mp (inv_mem (hHN x.2)) l).mp hl
      rw [inv_inv] at h
      rw [mul_assoc, mul_assoc, ← mul_assoc (x : G)⁻¹]
      exact mul_mem (inv_mem hl) h
    let l' : ↥H := ⟨l, hLH hl⟩
    have hcomm : π l' * π x = π x * π l' :=
      (mem_centralizer_iff.mp hxb) (π l') ⟨⟨l', mem_subgroupOf.mpr hl⟩, rfl⟩
    have h1 : π (l'⁻¹ * x⁻¹ * l' * x) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_assoc _ (π l') (π x), hcomm]
      group
    have hmem := mem_pPrimeCore_of_mem hLH hn hc ((QuotientGroup.eq_one_iff _).mp h1)
    exact ⟨_, hmem, rfl⟩
  have hx := hQ ⟨x.2, hxQ⟩
  have hU : (pPrimeCore 2 ↥H).map H.subtype ⊔ L ≤
      ((imageHom (L.subgroupOf H)).range.comap π).map H.subtype := by
    refine sup_le (map_mono fun o ho => ?_) fun l hl => ?_
    · have hπo : π o = 1 := (QuotientGroup.eq_one_iff o).mpr ho
      rw [mem_comap, hπo]
      exact one_mem _
    · exact ⟨⟨l, hLH hl⟩, ⟨⟨⟨l, hLH hl⟩, mem_subgroupOf.mpr hl⟩, rfl⟩, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hU hx
  rw [Subtype.ext hyx] at hy
  exact hy

theorem hyp31i_of_le [hsimple : IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hKP : Assembly.KProper Blueprint.Catalog G) (hcat : ¬ Blueprint.Catalog G) {z : G}
    (hz : orderOf z = 2) {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {z}))
    (hzL : z ∈ L) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hcov : IsCoverOf .POmegaOdd 3 p f 2 (↥L ⧸ pPrimeCore 2 ↥L)) (h5 : 5 ≤ p ^ f)
    (hchar : (L.subgroupOf (centralizer {z})).Characteristic)
    (hQ : centralizer {z} ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({z} : Set G))).map (centralizer {z}).subtype ⊔ zpowers z)
    (hconj : ∀ x ∈ centralizer ({z} : Set G), (∃ g : G, g * z * g⁻¹ = x) ↔
      (x ∈ L ∧ orderOf x = 2))
    (S : Sylow 2 G) (hSL : (S : Subgroup G) ≤ L) : Hyp31i G z p f := by
  have hLH : L ≤ centralizer ({z} : Set G) := hL.1
  have hn : (L.subgroupOf (centralizer ({z} : Set G))).Normal := by
    have := hchar
    infer_instance
  refine ⟨hsimple, hnonab, hKP, hcat, hz, fun x hx => exists_conj_of_sylow_le hLH hconj S hSL hx,
    hp, hp2, h5, (imageHom (L.subgroupOf (centralizer ({z} : Set G)))).range, normal_range _ hn,
    not_two_dvd_index_range hLH S hSL, isCoverOf_range hLH hn hcov,
    centralizer_range_le hLH hn ?_⟩
  rw [hQ]
  exact sup_le_sup_left ((zpowers_le).mpr hzL) _

end Reduce

end CFSG.ComponentClassification.HarrisLit.T1.S74
