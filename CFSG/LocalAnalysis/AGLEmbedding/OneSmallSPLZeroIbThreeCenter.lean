module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSPLZeroIbThreeDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.GaschutzTransfer

public section

namespace CFSG.AGLEmbedding

section Transfer

variable {Y : Type*} [Group Y]

theorem le_normalizer_centralizer_ib3 (L : Subgroup Y) :
    L ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set Y) : Set Y) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc h hh
    have := hc (l⁻¹ * h * l) (L.mul_mem (L.mul_mem (L.inv_mem hl) hh) hl)
    calc h * (l * c * l⁻¹) = l * ((l⁻¹ * h * l) * c) * l⁻¹ := by group
      _ = l * (c * (l⁻¹ * h * l)) * l⁻¹ := by rw [this]
      _ = l * c * l⁻¹ * h := by group
  · intro hc h hh
    have := hc (l * h * l⁻¹) (L.mul_mem (L.mul_mem hl hh) (L.inv_mem hl))
    calc h * c = l⁻¹ * ((l * h * l⁻¹) * (l * c * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * c * l⁻¹) * (l * h * l⁻¹)) * l := by rw [this]
      _ = c * h := by group

variable [Finite Y]

open scoped Pointwise in
theorem mem_of_mem_sup_of_perfect {D C : Subgroup Y} (hDp : ⁅D, D⁆ = D)
    (hDc : ∀ A : Subgroup Y, A ≤ D → IsPGroup 3 A → IsCyclic A)
    (hDN : D ≤ Subgroup.normalizer (C : Set Y)) {y : Y} (hy3 : y ^ 3 = 1)
    (hyD : y ∈ Subgroup.centralizer (D : Set Y)) (hyDC : y ∈ D ⊔ C) : y ∈ C := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hyDC' : y ∈ (D : Set Y) * (C : Set Y) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right D C hDN]
    exact hyDC
  obtain ⟨d, hd, c, hc, rfl⟩ := Set.mem_mul.mp hyDC'
  have hcomm : ∀ e ∈ D, d⁻¹ * e⁻¹ * d * e ∈ C := by
    intro e he
    have hey : e * (d * c) = d * c * e := Subgroup.mem_centralizer_iff.mp hyD e he
    have h1 : (d * c)⁻¹ * e⁻¹ * (d * c) = e⁻¹ := by
      calc (d * c)⁻¹ * e⁻¹ * (d * c) = (d * c)⁻¹ * e⁻¹ * (d * c * e) * e⁻¹ := by group
        _ = (d * c)⁻¹ * e⁻¹ * (e * (d * c)) * e⁻¹ := by rw [hey]
        _ = e⁻¹ := by group
    have h2 : d⁻¹ * e⁻¹ * d * e = c * (e⁻¹ * c⁻¹ * e⁻¹⁻¹) := by
      calc d⁻¹ * e⁻¹ * d * e = c * ((d * c)⁻¹ * e⁻¹ * (d * c)) * c⁻¹ * e := by group
        _ = c * (e⁻¹ * c⁻¹ * e⁻¹⁻¹) := by rw [h1]; group
    rw [h2]
    refine C.mul_mem hc ?_
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hDN he)) c⁻¹).mp (C.inv_mem hc)
  have hd3 : d ^ 3 ∈ C := by
    have hdy : Commute d⁻¹ (d * c) :=
      (show Commute d (d * c) from Subgroup.mem_centralizer_iff.mp hyD d hd).inv_left
    have hc3 : c ^ 3 = d⁻¹ ^ 3 := by
      calc c ^ 3 = (d⁻¹ * (d * c)) ^ 3 := by rw [inv_mul_cancel_left]
        _ = d⁻¹ ^ 3 * (d * c) ^ 3 := hdy.mul_pow 3
        _ = d⁻¹ ^ 3 := by rw [hy3, mul_one]
    have : d ^ 3 = (c ^ 3)⁻¹ := by rw [hc3, inv_pow, inv_inv]
    rw [this]
    exact C.inv_mem (C.pow_mem hc 3)
  let N : Subgroup D := C.subgroupOf D
  have hN : N.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hDN
  have hDperf : Group.IsPerfect D := Subgroup.isPerfect_iff.mpr hDp
  have hQ : Group.IsPerfect (D ⧸ N) := inferInstance
  let u : D ⧸ N := ((⟨d, hd⟩ : D) : D ⧸ N)
  have hu : u ∈ Subgroup.center (D ⧸ N) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    induction g using QuotientGroup.induction_on with
    | H e =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have he := hcomm e e.2
      have : (((e * ⟨d, hd⟩)⁻¹ * (⟨d, hd⟩ * e) : D) : Y) = d⁻¹ * (e : Y)⁻¹ * d * e := by
        push_cast
        group
      rw [this]
      exact he
  have hu3 : u ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
      Subgroup.coe_pow]
    exact hd3
  obtain ⟨P⟩ : Nonempty (Sylow 3 D) := inferInstance
  let T : Sylow 3 (D ⧸ N) := P.mapSurjective (QuotientGroup.mk'_surjective N)
  have hPc : IsCyclic (P : Subgroup D) := by
    have h := hDc ((P : Subgroup D).map D.subtype) (Subgroup.map_subtype_le _)
      (P.isPGroup'.map _)
    let e := Subgroup.equivMapOfInjective (P : Subgroup D) D.subtype D.subtype_injective
    exact isCyclic_of_injective e.toMonoidHom e.injective
  have hTc : IsCyclic (T : Subgroup (D ⧸ N)) :=
    isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap (P : Subgroup D))
      ((QuotientGroup.mk' N).subgroupMap_surjective (P : Subgroup D))
  have hu1 : u = 1 := by
    by_contra hu1
    exact CFSG.LocalAnalysis.RankThreeTheoremC.not_isCyclic_sylow_of_isPerfect hQ T hu hu1 hu3
      hTc
  have hdC : d ∈ C := by
    have := (QuotientGroup.eq_one_iff _).mp hu1
    exact Subgroup.mem_subgroupOf.mp this
  exact C.mul_mem hdC hc

end Transfer

theorem kFactBlockCenterThreeIb_holds : KFactBlockCenterThreeIb := by
  intro G _ _ M S L D x hyp y _ hy3 hyD hyDC
  obtain ⟨-, -, -, -, -, -, -, -, hDp, hDPC, hDc, -⟩ := hyp
  refine mem_of_mem_sup_of_perfect hDp hDc (hDPC.trans (sup_le ?_ Subgroup.le_normalizer)) hy3
    hyD hyDC
  refine le_trans ?_ (le_normalizer_centralizer_ib3 (barM M L))
  rintro _ ⟨m, hm, rfl⟩
  exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hm).2)

end CFSG.AGLEmbedding
