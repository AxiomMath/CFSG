module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Layer
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Mult
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Aut
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.GomiU42Transport

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo

open Subgroup
open scoped commutatorElement

variable {B : Type} [Group B] [Finite B] {e t : B} {J₀ E₂ : Subgroup B} [(zpowers e).Normal]

abbrev Kt (J₀ : Subgroup B) : Subgroup B := normalClosure (J₀ : Set B)

abbrev Qq (e : B) [(zpowers e).Normal] (J₀ : Subgroup B) : Subgroup (B ⧸ zpowers e) :=
  normalClosure ((J₀.map (π₁q e) : Subgroup (B ⧸ zpowers e)) : Set (B ⧸ zpowers e))

abbrev Dq (e : B) [(zpowers e).Normal] (J₀ : Subgroup B) : Subgroup (Xq e) :=
  normalClosure (((J₀.map (π₁q e)).map (θq e) : Subgroup (Xq e)) : Set (Xq e))

section Part1

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

include h hL in
theorem π₂_injOn_two {P : Subgroup B} (hP : IsPGroup 2 P) : Set.InjOn (π₂q e) P := by
  intro x hx y hy hxy
  have hPm : IsPGroup 2 ↥(P.map (π₁q e)) :=
    hP.of_surjective ((π₁q e).subgroupMap P) ((π₁q e).subgroupMap_surjective P)
  have h1 : π₁q e x = π₁q e y := hL.injOn_two _ hPm ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩ hxy
  exact h.injOn_of_isPGroup hP hx hy h1

theorem map_Kt_π₁ : (Kt J₀).map (π₁q e) = Qq e J₀ := by
  rw [Kt, Qq, map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
  congr 1

include hL in
theorem map_Kt_π₂ : (Kt J₀).map (π₂q e) = Dq e J₀ := by
  rw [π₂q, ← Subgroup.map_map, map_Kt_π₁]
  exact hL.map_Q

include h in
theorem GomiU42Setup.perfect_J₀ : ⁅J₀, J₀⁆ = J₀ := by
  haveI := h.isSimpleGroup_J₀
  exact Subgroup.isPerfect_iff.1 (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian_J₀).1.1

include h in
theorem GomiU42Setup.perfect_Kt : ⁅Kt J₀, Kt J₀⁆ = Kt J₀ :=
  isPerfect_normalClosure_of_perfect h.perfect_J₀

end Part1

section Part2

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

theorem mem_Qq_of_mem_Kt {x : B} (hx : x ∈ Kt J₀) : π₁q e x ∈ Qq e J₀ := by
  rw [← map_Kt_π₁]
  exact ⟨x, hx, rfl⟩

@[expose] noncomputable def fKt (e : B) (J₀ : Subgroup B) [(zpowers e).Normal] : ↥(Kt J₀) →* ↥(Qq e J₀) :=
  ((π₁q e).comp (Kt J₀).subtype).codRestrict (Qq e J₀) (fun x => mem_Qq_of_mem_Kt x.2)

theorem fKt_surjective : Function.Surjective (fKt e J₀) := by
  intro q
  have hq : (q : B ⧸ zpowers e) ∈ (Kt J₀).map (π₁q e) := by rw [map_Kt_π₁]; exact q.2
  obtain ⟨x, hx, hxq⟩ := hq
  exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩

include h in
theorem fKt_ker_le_center : (fKt e J₀).ker ≤ center ↥(Kt J₀) := by
  intro x hx
  have h1 : π₁q e x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
  have h2 : (x : B) ∈ zpowers e := (QuotientGroup.eq_one_iff _).1 h1
  rw [mem_center_iff]
  intro y
  exact Subtype.ext ((mem_center_iff.1 (h.zpowers_e_le_center h2) (y : B)))

include h hL in
theorem center_Kt_eq :
    (center ↥(Kt J₀)).map (Kt J₀).subtype = Kt J₀ ⊓ (π₂q e).ker := by
  have hperf : Group.IsPerfect ↥(Kt J₀) := Subgroup.isPerfect_iff.2 h.perfect_Kt
  have key := CFSG.LocalCores.comap_center_eq_of_perfect hperf (fKt e J₀) fKt_surjective
    (fKt_ker_le_center h)
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, ?_⟩
    have hy' : y ∈ (center ↥(Qq e J₀)).comap (fKt e J₀) := by rw [key]; exact hy
    have hfy : fKt e J₀ y ∈ center ↥(Qq e J₀) := hy'
    have hmem : ((fKt e J₀ y : ↥(Qq e J₀)) : B ⧸ zpowers e) ∈
        (center ↥(Qq e J₀)).map (Qq e J₀).subtype := ⟨_, hfy, rfl⟩
    rw [hL.center_Q] at hmem
    have hR : π₁q e y ∈ Rq e := (mem_inf.1 hmem).2
    exact (QuotientGroup.eq_one_iff _).2 hR
  · intro hx
    obtain ⟨hxK, hx1⟩ := mem_inf.1 hx
    have hR : π₁q e x ∈ Rq e := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx1)
    have hmem : π₁q e x ∈ Qq e J₀ ⊓ Rq e := mem_inf.2 ⟨mem_Qq_of_mem_Kt hxK, hR⟩
    rw [← hL.center_Q] at hmem
    obtain ⟨q, hq, hqx⟩ := hmem
    refine ⟨⟨x, hxK⟩, ?_, rfl⟩
    rw [← key]
    have : fKt e J₀ ⟨x, hxK⟩ = q := Subtype.ext hqx.symm
    show fKt e J₀ ⟨x, hxK⟩ ∈ center ↥(Qq e J₀)
    rw [this]
    exact hq

end Part2

section Part3

theorem eq_one_of_sq_eq_one_of_odd {H : Type*} [Group H] [Finite H]
    (hodd : Odd (Nat.card H)) {x : H} (hx : x * x = 1) : x = 1 := by
  have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hx)
  have hc : orderOf x ∣ Nat.card H := orderOf_dvd_natCard x
  have hcop : Nat.Coprime 2 (Nat.card H) := Nat.coprime_two_left.2 hodd
  have : orderOf x ∣ Nat.gcd 2 (Nat.card H) := Nat.dvd_gcd h2 hc
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at this
  exact this

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

include h in
theorem GomiU42Setup.eq_one_of_mem_zpowers_e_of_sq {x : B} (hx : x ∈ zpowers e) (hsq : x * x = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hx
  have h3 : x ^ 3 = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← h.orderOf_e,
      pow_orderOf_eq_one, one_zpow]
  have h2 : x ^ 2 = 1 := by rw [pow_two]; exact hsq
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2]; group

include h hL in
theorem odd_card_center_Kt : Odd (Nat.card (center ↥(Kt J₀))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have hev : 2 ∣ Nat.card (center ↥(Kt J₀)) := by
    rcases Nat.even_or_odd (Nat.card (center ↥(Kt J₀))) with h' | h'
    · exact even_iff_two_dvd.1 h'
    · exact absurd h' hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := center ↥(Kt J₀)) 2 hev
  set x : B := (((z : ↥(center ↥(Kt J₀))) : ↥(Kt J₀)) : B) with hx
  have hxo : orderOf x = 2 := by
    rw [hx, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  have hxsq : x * x = 1 := by
    rw [← pow_two, ← hxo]
    exact pow_orderOf_eq_one x
  have hzK : x ∈ (center ↥(Kt J₀)).map (Kt J₀).subtype := ⟨z, z.2, rfl⟩
  rw [center_Kt_eq h hL] at hzK
  obtain ⟨hzK1, hzK2⟩ := mem_inf.1 hzK
  have hR : π₁q e x ∈ Rq e := (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hzK2)
  have hmem : π₁q e x ∈ Qq e J₀ ⊓ Rq e := mem_inf.2 ⟨mem_Qq_of_mem_Kt hzK1, hR⟩
  have hsq' : (⟨π₁q e x, hmem⟩ : ↥(Qq e J₀ ⊓ Rq e)) * ⟨π₁q e x, hmem⟩ = 1 :=
    Subtype.ext (by
      change π₁q e x * π₁q e x = 1
      rw [← map_mul, hxsq, map_one])
  have h1 := eq_one_of_sq_eq_one_of_odd hL.odd_Q_inf_R hsq'
  have h1' : π₁q e x = 1 := congrArg Subtype.val h1
  have hxe : x ∈ zpowers e := (QuotientGroup.eq_one_iff _).1 h1'
  have hx1 := h.eq_one_of_mem_zpowers_e_of_sq hxe hxsq
  rw [hx1, orderOf_one] at hxo
  exact absurd hxo (by norm_num)

end Part3

section Part4

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

@[expose] noncomputable def gKt (hL : LayerOut e t J₀) : ↥(Kt J₀) →* ↥(Dq e J₀) :=
  ((π₂q e).comp (Kt J₀).subtype).codRestrict (Dq e J₀) (fun x => by
    rw [← map_Kt_π₂ hL]
    exact ⟨x, x.2, rfl⟩)

theorem gKt_surjective : Function.Surjective (gKt hL) := by
  intro q
  have hq : (q : Xq e) ∈ (Kt J₀).map (π₂q e) := by rw [map_Kt_π₂ hL]; exact q.2
  obtain ⟨x, hx, hxq⟩ := hq
  exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩

include h in
theorem ker_gKt : (gKt hL).ker = center ↥(Kt J₀) := by
  ext x
  have hc := center_Kt_eq h hL
  constructor
  · intro hx
    have h1 : π₂q e x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
    have hmem : (x : B) ∈ (center ↥(Kt J₀)).map (Kt J₀).subtype := by
      rw [hc]; exact mem_inf.2 ⟨x.2, h1⟩
    exact (Subgroup.mem_map_iff_mem (Kt J₀).subtype_injective).1 hmem
  · intro hx
    have hmem : (x : B) ∈ (center ↥(Kt J₀)).map (Kt J₀).subtype := ⟨x, hx, rfl⟩
    rw [hc] at hmem
    exact Subtype.ext (MonoidHom.mem_ker.1 (mem_inf.1 hmem).2)

noncomputable def GomiU42Setup.equivKtD (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀) :
    ↥(Kt J₀) ⧸ center ↥(Kt J₀) ≃* ↥(Dq e J₀) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_gKt h hL).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (gKt hL) (gKt_surjective hL))

include h in
theorem gKt_injective_of_center_bot (hz : center ↥(Kt J₀) = ⊥) :
    Function.Injective (gKt hL) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have : x ∈ (gKt hL).ker := hx
  rw [ker_gKt h hL, hz, mem_bot] at this
  exact this

end Part4

section PartE

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

include h in
theorem isElementaryAbelian_Ex : CFSG.IsElementaryAbelian 2 ↥(E₂.map (π₂q e)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.elementary
  exact IsElementaryAbelian.map (π₂q e)

include h hL in
theorem card_Ex : Nat.card ↥(E₂.map (π₂q e)) = 2 ^ 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.elementary
  rw [GomiU42Setup.card_map_of_injOn _ E₂ (π₂_injOn_two h hL (IsElementaryAbelian.isPGroup 2 E₂)), h.card_E₂]

include h in
theorem mem_normalizer_Ex :
    π₂q e t ∈ normalizer ((E₂.map (π₂q e) : Subgroup (Xq e)) : Set (Xq e)) := by
  rw [mem_normalizer_iff]
  intro y
  have ht : ∀ x : B, x ∈ E₂ ↔ t * x * t⁻¹ ∈ E₂ := fun x => mem_normalizer_iff.1 h.mem_normalizer x
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨t * x * t⁻¹, (ht x).1 hx, by simp⟩
  · rintro ⟨x', hx', hxy⟩
    refine ⟨t⁻¹ * x' * t, (ht _).2 ?_, ?_⟩
    · rw [show t * (t⁻¹ * x' * t) * t⁻¹ = x' by group]
      exact hx'
    · rw [map_mul, map_mul, map_inv, hxy]
      group

include h hL in
theorem inf_centralizer_Ex :
    (E₂.map (π₂q e)) ⊓ centralizer ({π₂q e t} : Set (Xq e)) =
      (E₂ ⊓ centralizer ({t} : Set B)).map (π₂q e) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyE, hyC⟩ := mem_inf.1 hy
    obtain ⟨x, hx, rfl⟩ := hyE
    have hcomm : π₂q e x * π₂q e t = π₂q e t * π₂q e x := mem_centralizer_singleton_iff.1 hyC
    have hP := h.isPGroup_sup
    have hxP : x ∈ E₂ ⊔ zpowers t := mem_sup_left hx
    have htP : t ∈ E₂ ⊔ zpowers t := mem_sup_right (mem_zpowers t)
    have hxt : x * t = t * x := by
      apply π₂_injOn_two h hL hP (mul_mem hxP htP) (mul_mem htP hxP)
      rw [map_mul, map_mul]
      exact hcomm
    exact ⟨x, mem_inf.2 ⟨hx, mem_centralizer_singleton_iff.2 hxt⟩, rfl⟩
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨hxE, hxC⟩ := mem_inf.1 hx
    refine mem_inf.2 ⟨⟨x, hxE, rfl⟩, mem_centralizer_singleton_iff.2 ?_⟩
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hxC]

include h hL in
theorem card_inf_Ex :
    Nat.card ↥((E₂.map (π₂q e)) ⊓ centralizer ({π₂q e t} : Set (Xq e)) : Subgroup (Xq e)) =
      2 ^ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := h.elementary
  rw [inf_centralizer_Ex h hL, GomiU42Setup.card_map_of_injOn _ _
    (π₂_injOn_two h hL ((IsElementaryAbelian.isPGroup 2 E₂).to_le (inf_le_left : E₂ ⊓
      centralizer ({t} : Set B) ≤ E₂))), h.card_inf]

include h hL in
theorem inf_le_Jx :
    (E₂.map (π₂q e)) ⊓ centralizer ({π₂q e t} : Set (Xq e)) ≤
      (J₀.map (π₁q e)).map (θq e) := by
  rw [inf_centralizer_Ex h hL, Subgroup.map_map]
  exact Subgroup.map_mono h.inf_le

end PartE

section PartData

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

include h hL in
theorem orderOf_π₂_t : orderOf (π₂q e t) = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : orderOf (π₁q e t) = 2 := h.orderOf_mk_t
  have hpg : IsPGroup 2 ↥(zpowers (π₁q e t)) :=
    IsPGroup.of_card (by rw [Nat.card_zpowers, hF]; exact (pow_one 2).symm)
  have hsq : π₂q e t ^ 2 = 1 := by
    rw [← map_pow, pow_two, h.t_sq, map_one]
  have hne : π₂q e t ≠ 1 := by
    intro h1
    have h1' : θq e (π₁q e t) = θq e 1 := by rw [map_one]; exact h1
    have := hL.injOn_two _ hpg (mem_zpowers _) (one_mem _) h1'
    rw [this, orderOf_one] at hF
    exact absurd hF (by norm_num)
  exact orderOf_eq_prime hsq hne

include h hL in
theorem lieModel_Jx :
    CFSG.Blueprint.LieModel ↥((J₀.map (π₁q e)).map (θq e)) .PSU 4 2 1 := by
  let e₁ : J₀ ≃* J₀.map (π₁q e) := h.equivJb
  let e₂ : ↥(J₀.map (π₁q e)) ≃* ↥((J₀.map (π₁q e)).map (θq e)) :=
    GomiU42Setup.equivMapOfInjOn (θq e) _ hL.injOn_J
  exact lieModel_of_mulEquiv_classical (e₁.trans e₂).symm (by decide) h.lieModel

include h hL in
theorem GomiU42Setup.data_of_simple
    (hsimple : IsSimpleGroup ↥(Dq e J₀)) (hnab : ∃ x y : ↥(Dq e J₀), x * y ≠ y * x)
    (hlt : (J₀.map (π₁q e)).map (θq e) < Dq e J₀)
    (hcent : centralizer ((Dq e J₀ : Subgroup (Xq e)) : Set (Xq e)) = ⊥) :
    GomiU42Data (Xq e) ((J₀.map (π₁q e)).map (θq e)) (Dq e J₀) (E₂.map (π₂q e)) (π₂q e t) := by
  haveI := hsimple
  exact
    { kGroup := hL.kGroup
      oddCore := hL.oddCore
      lieModel := lieModel_Jx h hL
      standard := hL.standard
      orderOf_a := orderOf_π₂_t h hL
      inf_eq_bot := hL.inf_eq
      sup_eq := hL.sup_eq
      not_central := hL.sylow
      normalClosure_eq := rfl
      simple := hsimple
      nonabelian := hnab
      lt := hlt
      centralizer_eq := hcent
      catalog := CFSG.SectionRank.catalog_of_isKGroupCat_of_surjective hL.kGroup (Dq e J₀)
        (MonoidHom.id _) Function.surjective_id
      elementary := isElementaryAbelian_Ex h
      card_E := card_Ex h hL
      mem_normalizer := mem_normalizer_Ex h
      card_centralizer_E := card_inf_Ex h hL
      centralizer_E_le := inf_le_Jx h hL }

end PartData

section PartLayer

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

include h hL in
theorem layer_le_Kt : CFSG.layer B ≤ Kt J₀ := by
  rw [CFSG.layer.eq_sSup B]
  refine sSup_le fun C hC => ?_
  rcases CFSG.LocalCores.component_normal_subgroup hC
    (normalClosure_normal : (Kt J₀).Normal) with hle | hcomm
  · exact hle
  · exfalso
    have hCc : C ≤ centralizer (Kt J₀ : Set B) := commutator_eq_bot_iff_le_centralizer.1 hcomm
    have hCR : ∀ c ∈ C, π₁q e c ∈ Rq e := by
      intro c hc
      rw [← hL.centralizer_Q, mem_centralizer_iff]
      intro q hq
      have hq' : q ∈ (Kt J₀).map (π₁q e) := by rw [map_Kt_π₁]; exact hq
      obtain ⟨k, hk, rfl⟩ := hq'
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 (hCc hc) k hk]
    haveI := hL.R_abelian
    have hcomm1 : ∀ g ∈ C, ∀ g' ∈ C, ⁅g, g'⁆ ∈ zpowers e := by
      intro g hg g' hg'
      have h1 : π₁q e g * π₁q e g' = π₁q e g' * π₁q e g :=
        congrArg Subtype.val ((IsMulCommutative.is_comm (M := ↥(Rq e))).comm
          ⟨π₁q e g, hCR g hg⟩ ⟨π₁q e g', hCR g' hg'⟩)
      have h2 : π₁q e ⁅g, g'⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 h1
      exact (QuotientGroup.eq_one_iff _).1 h2
    have hCcomm : ⁅C, C⁆ ≤ zpowers e := commutator_le.2 hcomm1
    have hCperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hC.1.1
    have hCcenter : ∀ c ∈ C, c ∈ center B := fun c hc =>
      h.zpowers_e_le_center (hCcomm (by rw [hCperf]; exact hc))
    obtain ⟨a, b, hab⟩ := hC.1.2.2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hxy : x * y = y * x := Subtype.ext ((mem_center_iff.1 (hCcenter x x.2) y).symm)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hxy]

include hL in
theorem Kt_le_layer (hq : CFSG.IsQuasisimple ↥(Kt J₀)) : Kt J₀ ≤ CFSG.layer B := by
  rw [CFSG.layer.eq_sSup B]
  exact le_sSup ⟨hq, (inferInstance : (Kt J₀).Normal).isSubnormal⟩

end PartLayer

section PartSimple

variable (h : GomiU42Setup B e t J₀ E₂) (hL : LayerOut e t J₀)

include h hL in
theorem Kt_inf_centralizer (hz : center ↥(Kt J₀) = ⊥)
    (hDJ : Dq e J₀ ⊓ centralizer ({π₂q e t} : Set (Xq e)) = (J₀.map (π₁q e)).map (θq e)) :
    Kt J₀ ⊓ centralizer ({t} : Set B) = J₀ := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxK, hxC⟩ := mem_inf.1 hx
    have hxD : π₂q e x ∈ Dq e J₀ := by
      rw [← map_Kt_π₂ hL]
      exact ⟨x, hxK, rfl⟩
    have hxC' : π₂q e x ∈ centralizer ({π₂q e t} : Set (Xq e)) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.1 hxC]
    have hxJ : π₂q e x ∈ (J₀.map (π₁q e)).map (θq e) := by
      rw [← hDJ]
      exact mem_inf.2 ⟨hxD, hxC'⟩
    rw [Subgroup.map_map] at hxJ
    obtain ⟨j, hj, hjx⟩ := hxJ
    have hjK : j ∈ Kt J₀ := subset_normalClosure hj
    have hinj := gKt_injective_of_center_bot h hL hz
    have : (⟨x, hxK⟩ : ↥(Kt J₀)) = ⟨j, hjK⟩ := hinj (Subtype.ext hjx.symm)
    have hxj : x = j := congrArg Subtype.val this
    rw [hxj]
    exact hj
  · exact le_inf (subset_normalClosure) h.le_centralizer

noncomputable def GomiU42Setup.equivKtD' (hz : center ↥(Kt J₀) = ⊥) :
    ↥(Kt J₀) ≃* ↥(Dq e J₀) :=
  MulEquiv.ofBijective (gKt hL) ⟨gKt_injective_of_center_bot h hL hz, gKt_surjective hL⟩

include h hL in
theorem GomiU42Setup.simple_branch (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : GomiU42Selector fun _ _ => True)
    (hsimple : IsSimpleGroup ↥(Dq e J₀)) (hnab : ∃ x y : ↥(Dq e J₀), x * y ≠ y * x)
    (hlt : (J₀.map (π₁q e)).map (θq e) < Dq e J₀)
    (hcent : centralizer ((Dq e J₀ : Subgroup (Xq e)) : Set (Xq e)) = ⊥) :
    CFSG.layer B ⊓ centralizer ({t} : Set B) = J₀ ∧
      CFSG.Blueprint.LieModel ↥(CFSG.layer B) .PSL 4 2 2 := by
  have hdata := h.data_of_simple hL hsimple hnab hlt hcent
  obtain ⟨hnot, hlie⟩ := hS (Xq e) _ (Dq e J₀) _ (π₂q e t) hdata trivial
  have hperf : Group.IsPerfect ↥(Kt J₀) := Subgroup.isPerfect_iff.2 h.perfect_Kt
  have hz : center ↥(Kt J₀) = ⊥ :=
    center_eq_bot_of_psl_four_four hGA hperf (h.equivKtD hL) hlie (odd_card_center_Kt h hL)
  have hDJ := hdata.inf_centralizer_eq hnot
  have hinf := Kt_inf_centralizer h hL hz hDJ
  let eKD := h.equivKtD' hL hz
  haveI := hsimple
  have hsimpleK : IsSimpleGroup ↥(Kt J₀) := eKD.isSimpleGroup
  have hnabK : ∃ x y : ↥(Kt J₀), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnab
    refine ⟨eKD.symm x, eKD.symm y, fun h' => hxy ?_⟩
    have h'' := congrArg eKD h'
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h''
  have hq : CFSG.IsQuasisimple ↥(Kt J₀) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnabK).1
  have hlayer : CFSG.layer B = Kt J₀ := le_antisymm (layer_le_Kt h hL) (Kt_le_layer hL hq)
  refine ⟨by rw [hlayer]; exact hinf, ?_⟩
  rw [hlayer]
  exact lieModel_of_mulEquiv_classical eKD (by decide) hlie

end PartSimple

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
