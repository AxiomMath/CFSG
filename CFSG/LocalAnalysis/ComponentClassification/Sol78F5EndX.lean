module

public import CFSG.LocalAnalysis.ComponentClassification.Sol78F5EndOne

public noncomputable section

namespace CFSG.ComponentClassification.Sol78.F514

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools CFSG.ComponentClassification.Foote5
  CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.Open

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isDihedralTwoGroup_of_mulEquiv {Y : Type} [Group Y] {P : Subgroup G} {Q : Subgroup Y}
    (e : P ≃* Q) (h : AschbacherTheorem3.IsDihedralTwoGroup P) :
    AschbacherTheorem3.IsDihedralTwoGroup Q := by
  obtain ⟨n, hn, ⟨f⟩⟩ := h
  exact ⟨n, hn, ⟨e.symm.trans f⟩⟩

omit [Finite G] in
theorem card_conjugate (K : Subgroup G) (g : G) : Nat.card ↥(conjugate K g) = Nat.card ↥K :=
  (Nat.card_congr (K.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
    (MulAut.conj g⁻¹).injective).toEquiv).symm

theorem orderOf_mk_eq_two {Y : Type*} [Group Y] [Finite Y] {y : Y} (hy : orderOf y = 2) :
    orderOf (QuotientGroup.mk' (pPrimeCore 2 Y) y) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (zpowers y) := isPGroup_zpowers_of_orderOf hy
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy; omega
  refine orderOf_eq_prime ?_ fun h => hy1 ?_
  · rw [← map_pow, ← hy, pow_orderOf_eq_one, map_one]
  · refine GSThmB.OddQuot.injOn_of_isPGroup hP (mem_zpowers y) (one_mem _) ?_
    rw [h, map_one]

@[expose] noncomputable def oddQuotImage (B M : Subgroup G) : Subgroup (↥B ⧸ pPrimeCore 2 ↥B) :=
  (M.subgroupOf B).map (QuotientGroup.mk' (pPrimeCore 2 ↥B))

theorem factorization_card_eq_of_quotient_equiv {A C : Type} [Group A] [Group C] [Finite A]
    [Finite C] (e : A ⧸ pPrimeCore 2 A ≃* C ⧸ pPrimeCore 2 C) :
    (Nat.card A).factorization 2 = (Nat.card C).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ∀ (X : Type) [Group X] [Finite X],
      (Nat.card (pPrimeCore 2 X)).factorization 2 = 0 := fun X _ _ =>
    Nat.factorization_eq_zero_of_not_dvd fun h =>
      Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl h (pPrimeCore_coprime_card (p := 2))
  have hne : ∀ (X : Type) [Group X] [Finite X], Nat.card (pPrimeCore 2 X) ≠ 0 :=
    fun X _ _ => Nat.card_pos.ne'
  have hne' : ∀ (X : Type) [Group X] [Finite X], Nat.card (X ⧸ pPrimeCore 2 X) ≠ 0 :=
    fun X _ _ => Nat.card_pos.ne'
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 A),
    Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 C),
    Nat.factorization_mul (hne' A) (hne A), Nat.factorization_mul (hne' C) (hne C),
    Finsupp.add_apply, Finsupp.add_apply, hodd A, hodd C, Nat.card_congr e.toEquiv]

theorem isTwoComponentAt_oddQuotImage {B M : Subgroup G} {b : G} (hbB : b ∈ B) (hMB : M ≤ B)
    (hM : IsTwoComponentAt b M) :
    IsTwoComponentAt (QuotientGroup.mk' (pPrimeCore 2 ↥B) ⟨b, hbB⟩) (oddQuotImage B M) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hb2, hMC, hMpc⟩ := hM
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥B) with hπ
  set bB : ↥B := ⟨b, hbB⟩ with hbBdef
  have hbB2 : bB * bB = 1 := Subtype.ext (by
    change b * b = 1
    rw [← sq, ← hb2, pow_orderOf_eq_one])
  have hker := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥B)
  have hMBC : M.subgroupOf B ≤ centralizer ({bB} : Set ↥B) := fun x hx =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext
      (mem_centralizer_singleton_iff.mp (hMC (mem_subgroupOf.mp hx))))
  have hMBpc : IsPComponent 2 ((M.subgroupOf B).subgroupOf (centralizer ({bB} : Set ↥B))) := by
    rw [centralizer_mk_eq hbB, isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact isPComponent_subgroupOf_of_le (le_inf hMC hMB) inf_le_left hMpc
  have hK := GSThmB.OddQuot.isPComponent_map π hker hMBC hMBpc
  rw [← GSThmB.OddQuot.centralizer_singleton_map_eq hbB2] at hK
  refine ⟨orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact hb2), ?_, hK⟩
  change (M.subgroupOf B).map π ≤ _
  rw [GSThmB.OddQuot.centralizer_singleton_map_eq hbB2]
  exact map_mono hMBC

theorem nonempty_quotient_equiv_oddQuotImage {B M : Subgroup G} (hMB : M ≤ B) :
    Nonempty (M ⧸ pPrimeCore 2 M ≃* oddQuotImage B M ⧸ pPrimeCore 2 (oddQuotImage B M)) := by
  have hker := GSThmB.OddQuot.not_two_dvd_card_ker (H := ↥B)
  obtain ⟨e₁⟩ := GSThmB.OddQuot.nonempty_quotient_pPrimeCore_equiv
    (QuotientGroup.mk' (pPrimeCore 2 ↥B)) hker (M.subgroupOf B)
  exact ⟨(UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2
    (subgroupOfEquivOfLe hMB)).symm.trans e₁⟩

namespace Hyp

variable {L₀ L Q S T : Subgroup G} {z t s : G} {𝕊 : Type} [Group 𝕊] [Finite 𝕊]
  {ε : L ⧸ pPrimeCore 2 L ≃* 𝕊} {Lin : Subgroup (MulAut 𝕊)} (H : Hyp L₀ L Q S T z t s ε Lin)
include H

theorem isDihedralTwoGroup_Rs : AschbacherTheorem3.IsDihedralTwoGroup (conjugate (S ⊓ L) s) :=
  isDihedralTwoGroup_of_mulEquiv ((S ⊓ L).equivMapOfInjective (MulAut.conj s⁻¹).toMonoidHom
    (MulAut.conj s⁻¹).injective) H.isDihedralTwoGroup_R

theorem exists_quotient_data (h3 : Asc76.Asc76Theorem3Large) {B : Subgroup G} (hLB : L ≤ B)
    (hRsB : conjugate (S ⊓ L) s ≤ B) :
    ∃ (z' t' : ↥B ⧸ pPrimeCore 2 ↥B) (K P D : Subgroup (↥B ⧸ pPrimeCore 2 ↥B)),
      K = oddQuotImage B L ∧ P = oddQuotImage B (S ⊓ L) ∧
      D = oddQuotImage B (conjugate (S ⊓ L) s) ∧
      IsTwoComponentAt z' K ∧ Nonempty (L ⧸ pPrimeCore 2 L ≃* K ⧸ pPrimeCore 2 K) ∧
      IsSylowOf 2 P K ∧ t' ∈ P ∧ orderOf t' = 2 ∧ z' * t' = t' * z' ∧ z' ∈ D ∧
      D ≤ centralizer ({z'} : Set _) ⊓ coreActionKernel K ∧ P ≤ centralizer (D : Set _) ∧
      IsPGroup 2 D ∧ Nat.card D = Nat.card ↥(S ⊓ L) ∧ AschbacherTheorem3.IsDihedralTwoGroup D ∧
      Group.IsSolvable ↥(centralizer ({z' * t'} : Set (↥B ⧸ pPrimeCore 2 ↥B))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥B) with hπ
  have hzB : z ∈ B := hRsB H.z_mem_Rs
  have htB : t ∈ B := hLB H.sec5.tL
  set zB : ↥B := ⟨z, hzB⟩ with hzBdef
  set tB : ↥B := ⟨t, htB⟩ with htBdef
  have hzt : z * t = t * z := H.z_mul_t
  have hztB2 : zB * tB * (zB * tB) = 1 := Subtype.ext (by
    change z * t * (z * t) = 1
    calc z * t * (z * t) = z * (t * z) * t := by group
      _ = z * (z * t) * t := by rw [← hzt]
      _ = (z * z) * (t * t) := by group
      _ = 1 := by rw [H.mul_self_z, H.mul_self_t, one_mul])
  set LB := L.subgroupOf B with hLBdef
  set Rs := conjugate (S ⊓ L) s with hRsdef
  set RsB := Rs.subgroupOf B with hRsBdef
  set RB := (S ⊓ L).subgroupOf B with hRBdef
  have hRs2 : IsPGroup 2 ↥Rs := H.sec5.R_sylow.isPGroup.map _
  have hRsB2 : IsPGroup 2 ↥RsB := hRs2.comap_subtype
  have hRB2 : IsPGroup 2 ↥RB := H.sec5.R_sylow.isPGroup.comap_subtype
  have hK := isTwoComponentAt_oddQuotImage hzB hLB H.sec5.zL
  obtain ⟨eK⟩ := nonempty_quotient_equiv_oddQuotImage (B := B) hLB
  have hRL : S ⊓ L ≤ L := inf_le_right
  have hPK : RB.map π ≤ LB.map π := map_mono fun x hx => mem_subgroupOf.mpr (hRL hx)
  have hPcard : Nat.card (RB.map π) = Nat.card ↥(S ⊓ L) := by
    rw [GSThmB.OddQuot.card_map_of_isPGroup hRB2]
    exact Nat.card_congr (subgroupOfEquivOfLe (hRL.trans hLB)).toEquiv
  have hPsyl : IsSylowOf 2 (RB.map π) (LB.map π) := by
    refine isSylowOf_of_card hPK ?_
    rw [hPcard, H.sec5.R_sylow.card_eq]
    exact congrArg (2 ^ ·) (factorization_card_eq_of_quotient_equiv eK)
  have hRsK : RsB ≤ coreActionKernel LB := fun x hx =>
    (mem_coreActionKernel_subgroupOf_iff hLB x).mpr (H.sec5.Q_le (H.l511 (mem_subgroupOf.mp hx)))
  have hRsN : RsB ≤ normalizer (LB : Set ↥B) := fun x hx => (mem_coreActionKernel.mp (hRsK hx)).1
  have hDK : RsB.map π ≤ coreActionKernel (LB.map π) := by
    have h1 := GSThmB.OddQuot.map_inf_coreActionKernel (X := LB) (Y := RsB) hRsN
    rw [inf_eq_left.mpr hRsK] at h1
    rw [h1]
    exact inf_le_right
  have hDC : RsB.map π ≤ centralizer ({π zB} : Set _) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (H.sec5.zS _ (H.Rs_le_S (mem_subgroupOf.mp hx)))
  have hPD : RB.map π ≤ centralizer ((RsB.map π : Subgroup _) : Set _) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (H.commute_R_Rs (mem_subgroupOf.mp ha) (mem_subgroupOf.mp hb)).symm
  have hinj : Function.Injective (π.subgroupMap RsB) := fun x y hxy =>
    Subtype.ext (GSThmB.OddQuot.injOn_of_isPGroup hRsB2 x.2 y.2 (congrArg Subtype.val hxy))
  let eD : ↥RsB ≃* ↥(RsB.map π) :=
    MulEquiv.ofBijective (π.subgroupMap RsB) ⟨hinj, π.subgroupMap_surjective RsB⟩
  let eRs : ↥Rs ≃* ↥RsB := (subgroupOfEquivOfLe hRsB).symm
  have hsolv : Group.IsSolvable ↥(centralizer ({π zB * π tB} : Set (↥B ⧸ pPrimeCore 2 ↥B))) := by
    rw [← map_mul, GSThmB.OddQuot.centralizer_singleton_map_eq hztB2]
    have hsG := H.isSolvable_centralizer h3
    have hle : (centralizer ({zB * tB} : Set ↥B)).map B.subtype ≤
        centralizer ({z * t} : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
      rw [mem_centralizer_singleton_iff]
      exact congrArg Subtype.val hx
    have h1 : Group.IsSolvable ↥((centralizer ({zB * tB} : Set ↥B)).map B.subtype) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have h2 : Group.IsSolvable ↥(centralizer ({zB * tB} : Set ↥B)) := by
      let e := (centralizer ({zB * tB} : Set ↥B)).equivMapOfInjective B.subtype
        B.subtype_injective
      exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_surjective (π.subgroupMap_surjective _)
  refine ⟨π zB, π tB, LB.map π, RB.map π, RsB.map π, rfl, rfl, rfl, hK, ⟨eK⟩, hPsyl,
    mem_map_of_mem π (show tB ∈ RB from H.sec5.tR),
    orderOf_mk_eq_two (by rw [Subgroup.orderOf_mk]; exact H.sec5.t2),
    by rw [← map_mul, ← map_mul, show zB * tB = tB * zB from Subtype.ext hzt],
    mem_map_of_mem π (show zB ∈ RsB from H.z_mem_Rs), le_inf hDC hDK, hPD, hRsB2.map π, ?_, ?_,
    hsolv⟩
  · rw [← Nat.card_congr eD.toEquiv, ← Nat.card_congr eRs.toEquiv, card_conjugate]
  · exact isDihedralTwoGroup_of_mulEquiv (eRs.trans eD) H.isDihedralTwoGroup_Rs

end Hyp

end CFSG.ComponentClassification.Sol78.F514
