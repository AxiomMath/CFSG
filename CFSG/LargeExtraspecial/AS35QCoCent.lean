module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35QCoSeven
public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixCoverModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.AS35QCo

open Module Subgroup CFSG.RankThree.OrthogonalInvolutions CFSG.Sporadic.Co2Smith

section TypeA

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {q : QuadraticForm (ZMod 2) V}

theorem eq_of_isTypeA {d : V ≃ₗ[ZMod 2] V} (hd : IsTypeA q d 2) {U : Submodule (ZMod 2) V}
    (hU2 : finrank (ZMod 2) U = 2)
    (hnd : U ⊓ LinearMap.BilinForm.orthogonal q.polarBilin U = ⊥)
    (hdU : ∀ u ∈ U, d u ∈ U) {u : V} (hu : u ∈ U) : d u = u := by
  by_contra hne
  set w := d u - u with hw
  have hwU : w ∈ U := U.sub_mem (hdU u hu) hu
  have hqw : q w = 0 := hd.2.2.2.2 w (mem_commSpace.mpr ⟨u, rfl⟩)
  have hw0 : w ≠ 0 := fun h => hne (sub_eq_zero.mp h)
  have hdu : d u = u + w := by rw [hw]; abel
  have hu0 : u ≠ 0 := by
    rintro rfl
    exact hne (map_zero d)
  have huw : u ≠ w := by
    intro h
    apply hu0
    have h2 : d u = 0 := by rw [hdu, ← h, ← two_nsmul, two_nsmul_eq_zero]
    exact d.injective (h2.trans (map_zero d).symm)
  have hpol : QuadraticMap.polar q u w = 0 := by
    have e := hd.1 u
    rw [hdu, map_add_eq] at e
    linear_combination e - hqw
  have hww : QuadraticMap.polar q w w = 0 := by
    rw [QuadraticMap.polar_self, hqw, smul_zero]
  set U₀ := U ⊓ LinearMap.ker (q.polarBilin w) with hU₀
  have huU₀ : u ∈ U₀ := Submodule.mem_inf.mpr ⟨hu, by
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_comm]
    exact hpol⟩
  have hwU₀ : w ∈ U₀ := Submodule.mem_inf.mpr ⟨hwU, by
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact hww⟩
  have hU₀U : U₀ = U := by
    by_contra hne'
    have h1 : finrank (ZMod 2) U₀ < finrank (ZMod 2) U :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne')
    have h2 : finrank (ZMod 2) U₀ ≠ 0 := by
      intro h
      rw [Submodule.finrank_eq_zero] at h
      rw [h] at huU₀
      exact hu0 ((Submodule.mem_bot _).mp huU₀)
    exact huw (Frame.eq_of_finrank_eq_one (by omega) huU₀ hwU₀ hu0 hw0)
  have hperp : w ∈ LinearMap.BilinForm.orthogonal q.polarBilin U := by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    have h := (Submodule.mem_inf.mp (hU₀U ▸ hv : v ∈ U₀)).2
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply] at h
    change QuadraticMap.polar q v w = 0
    rw [QuadraticMap.polar_comm]
    exact h
  have hmem := Submodule.mem_inf.mpr ⟨hwU, hperp⟩
  rw [hnd] at hmem
  exact hw0 ((Submodule.mem_bot _).mp hmem)

omit [FiniteDimensional (ZMod 2) V] in
theorem commSpace_ne_bot [FiniteDimensional (ZMod 2) V] {g : V ≃ₗ[ZMod 2] V} (hg : g ≠ 1) :
    finrank (ZMod 2) (commSpace g) ≠ 0 := by
  intro h
  apply hg
  apply Frame.fixSpace_eq_top_iff.mp
  apply Submodule.eq_top_of_finrank_eq
  have := finrank_commSpace_add_finrank_fixSpace g
  omega

end TypeA

variable {G : Type} [Group G] [Finite G] (S : Setting G)

theorem finite_Qt : Module.Finite (ZMod 2) S.Qt := Module.Finite.of_finite

theorem finite_lin : Finite (S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  Finite.of_injective (fun e : S.Qt ≃ₗ[ZMod 2] S.Qt => (e : S.Qt → S.Qt))
    (fun _ _ h => LinearEquiv.ext (congrFun h))

theorem isom (g : S.O) : ∀ v, S.q ((g : S.Qt ≃ₗ[ZMod 2] S.Qt) v) = S.q v :=
  TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp g.2

theorem finrank_eq_eight (hw : S.width = 4) : finrank (ZMod 2) S.Qt = 8 := by
  rw [S.finrank_Qt_eq_two_mul_width, hw]

theorem isTypeA_of_mem_dbar (hS : S.SixHyp) {a : S.O} (ha : a ∈ S.DbarAsc) :
    IsTypeA S.q (a : S.Qt ≃ₗ[ZMod 2] S.Qt) 2 := by
  obtain ⟨t, ht, htM, rfl⟩ := ha
  exact (S.fiveOne_two hS.sixFour hS.weak ht htM).1

theorem dbar_subset_mbar : S.DbarAsc ⊆ S.Mbar := by
  rintro _ ⟨t, -, htM, rfl⟩
  exact ⟨⟨t, htM⟩, rfl⟩

theorem lbar_le_mbar : S.LbarAsc ≤ S.Mbar :=
  (closure_le _).mpr (dbar_subset_mbar S)

theorem even_of_mem_lbar (hS : S.SixHyp) {g : S.O} (hg : g ∈ S.LbarAsc) :
    Even (finrank (ZMod 2) (commSpace (g : S.Qt ≃ₗ[ZMod 2] S.Qt))) := by
  have := finite_Qt S
  have hle : S.LbarAsc ≤ (omegaGroup S.q S.q_nondegenerate).comap S.O.subtype := by
    rw [closure_le]
    intro a ha
    have hA := isTypeA_of_mem_dbar S hS ha
    refine ⟨a.2, ?_⟩
    change Even (finrank (ZMod 2) ↥(commSpace (a : S.Qt ≃ₗ[ZMod 2] S.Qt)))
    rw [hA.2.2.2.1]
    exact even_two
  exact (hle hg).2

theorem commute_of_mem_centralizer {c : S.O} (hc : c ∈ centralizer S.DbarAsc) {g : S.O}
    (hg : g ∈ S.LbarAsc) : g * c = c * g := by
  have hc' : c ∈ centralizer (closure S.DbarAsc : Set S.O) := by
    rw [centralizer_closure]
    exact hc
  exact mem_centralizer_iff.mp hc' g hg

theorem fixed_of_mem_lbar {U : Submodule (ZMod 2) S.Qt}
    (h : ∀ a ∈ S.DbarAsc, ∀ u ∈ U, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u) {g : S.O}
    (hg : g ∈ S.LbarAsc) : ∀ u ∈ U, (g : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
  induction hg using closure_induction with
  | mem a ha => exact h a ha
  | one => exact fun u _ => rfl
  | mul a b _ _ iha ihb =>
    intro u hu
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ihb u hu, iha u hu]
  | inv a _ iha =>
    intro u hu
    rw [Subgroup.coe_inv]
    nth_rewrite 1 [← iha u hu]
    exact inv_mul_apply _ u

theorem exists_seven (hsp : S.Asc512SpSix) :
    ∃ x : S.O, x ∈ S.LbarAsc ∧ x ^ 7 = 1 ∧ x ≠ 1 := by
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.nonempty_mulEquiv_statedSp_of_lieModel
      hsp.2
  have := finite_lin S
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have : Fintype Sp62 := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card (G := Sp62) 7
    (by rw [← Nat.card_eq_fintype_card, natCard_sp62]; norm_num)
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm g)
  have hl7 : orderOf (QuotientGroup.mk l : S.LbarAsc ⧸ center S.LbarAsc) = 7 := by
    rw [hl, MulEquiv.orderOf_eq, hg]
  have hdvd : 7 ∣ orderOf l := by
    rw [← hl7]
    exact orderOf_map_dvd (QuotientGroup.mk' (center S.LbarAsc)) l
  have hpos : orderOf l ≠ 0 := (orderOf_pos l).ne'
  have ho := orderOf_pow_orderOf_div hpos hdvd
  refine ⟨((l ^ (orderOf l / 7) : S.LbarAsc) : S.O), (l ^ (orderOf l / 7)).2, ?_, ?_⟩
  · have h7 := pow_orderOf_eq_one (l ^ (orderOf l / 7))
    rw [ho] at h7
    rw [← Subgroup.coe_pow, h7, Subgroup.coe_one]
  · intro h
    have h1 : l ^ (orderOf l / 7) = 1 := Subtype.ext h
    rw [h1, orderOf_one] at ho
    exact absurd ho (by norm_num)

theorem seven_hyp (hw : S.width = 4) {x : S.O} (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) :
    Seven.Hyp S.q (x : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  ⟨S.q_nondegenerate, finrank_eq_eight S hw, isom S x, by rw [← Subgroup.coe_pow, hx7]; rfl,
    fun h => hx1 (Subtype.ext h)⟩

theorem orderOf_le_three (hst : S.Asc512Standing) {z : S.O} (hzL : z ∈ S.LbarAsc)
    (hz : ∀ g ∈ S.LbarAsc, g * z = z * g) : orderOf z ≤ 3 := by
  set Cg : Subgroup S.O := S.Mbar ⊓ centralizer S.DbarAsc with hCg
  have hzC : z ∈ Cg := ⟨lbar_le_mbar S hzL, mem_centralizer_iff.mpr fun a ha =>
    hz a (subset_closure ha)⟩
  set z' : Cg := ⟨z, hzC⟩
  have hcen : z' ∈ center Cg := by
    rw [mem_center_iff]
    intro g
    apply Subtype.ext
    exact (commute_of_mem_centralizer S (mem_inf.mp g.2).2 hzL).symm
  have hF : z' ∈ CFSG.generalizedFitting Cg := by
    apply le_sup_left (a := CFSG.fittingSubgroup Cg)
    exact le_sSup (show center Cg ∈ {N : Subgroup Cg | N.Normal ∧ Group.IsNilpotent N} from
      ⟨inferInstance, inferInstance⟩) hcen
  have hd := orderOf_dvd_natCard (⟨z', hF⟩ : CFSG.generalizedFitting Cg)
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hd
  have : Finite Cg := inferInstance
  exact (Nat.le_of_dvd Nat.card_pos hd).trans hst.fstar_card

theorem center_lbar_eq_bot (hS : S.SixHyp) (hst : S.Asc512Standing) (hsp : S.Asc512SpSix) :
    center S.LbarAsc = ⊥ := by
  have := finite_Qt S
  have hq := S.q_nondegenerate
  have hV := finrank_eq_eight S hsp.1
  obtain ⟨x, hxL, hx7, hx1⟩ := exists_seven S hsp
  have hx := seven_hyp S hsp.1 hx7 hx1
  obtain ⟨hF2, -, -⟩ := hx.finrank_fixSpace
  set X : S.Qt ≃ₗ[ZMod 2] S.Qt := (x : S.Qt ≃ₗ[ZMod 2] S.Qt) with hXdef
  rw [eq_bot_iff]
  intro zz hzz
  rw [mem_bot]
  set z : S.O := zz.1 with hzdef
  have hzL : z ∈ S.LbarAsc := zz.2
  have hcomm : ∀ g ∈ S.LbarAsc, g * z = z * g := fun g hg =>
    congrArg Subtype.val (mem_center_iff.mp hzz ⟨g, hg⟩)
  set c : S.Qt ≃ₗ[ZMod 2] S.Qt := (z : S.Qt ≃ₗ[ZMod 2] S.Qt) with hcdef
  have hcx : c * X = X * c := by
    have := hcomm x hxL
    rw [hcdef, hXdef, ← Subgroup.coe_mul, ← Subgroup.coe_mul, this]
  have hpowc : ∀ n : ℕ, z ^ n = 1 → c ^ n = 1 := fun n h => by
    rw [hcdef, ← Subgroup.coe_pow, h]
    rfl
  have hc1 : z ≠ 1 → c ≠ 1 := fun h h' => h (Subtype.ext h')
  have hle3 := orderOf_le_three S hst hzL hcomm
  have hpos := orderOf_pos z
  by_contra hz1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hne1 : orderOf z ≠ 1 := fun h => hz1' (orderOf_eq_one_iff.mp h)
  have hFinf : fixSpace X ⊓ commSpace X = ⊥ := fixSpace_inf_commSpace ⟨3, rfl⟩ hx.pow
  have hcne := commSpace_ne_bot (hc1 hz1')
  have h123 : orderOf z = 2 ∨ orderOf z = 3 := by omega
  rcases h123 with h | h
  ·
    have hcc : c * c = 1 := by
      rw [← pow_two]
      have h' := pow_orderOf_eq_one z
      rw [h] at h'
      exact hpowc 2 h'
    have hle := hx.commSpace_le_fixSpace hcx (Or.inl hcc)
    have hev : Even (finrank (ZMod 2) ↥(commSpace c)) := even_of_mem_lbar S hS hzL
    have hle' := Submodule.finrank_mono hle
    have hc2 : finrank (ZMod 2) (commSpace c) = 2 := by
      obtain ⟨k, hk⟩ := hev
      rw [hF2] at hle'
      omega
    have heq : commSpace c = fixSpace X :=
      Submodule.eq_of_le_of_finrank_eq hle (by rw [hc2, hF2])
    have h1 : fixSpace X ≤ commSpace X := by
      rw [← heq, commSpace_eq_orthogonal hq hx.isom, ← heq,
        ← fixSpace_eq_orthogonal hq (isom S z)]
      exact commSpace_le_fixSpace hcc
    have h2 : fixSpace X = ⊥ := by
      rw [← hFinf]
      exact le_antisymm (le_inf le_rfl h1) inf_le_left
    rw [h2, finrank_bot] at hF2
    exact absurd hF2 (by norm_num)
  ·
    have hc3 : c ^ 3 = 1 := by
      have h' := pow_orderOf_eq_one z
      rw [h] at h'
      exact hpowc 3 h'
    have hle := hx.commSpace_le_fixSpace hcx (Or.inr hc3)
    have hle' := Submodule.finrank_mono hle
    rw [hF2] at hle'
    have hev : finrank (ZMod 2) (commSpace c) % 2 = 0 := by
      have h1 := mod_two_of_pow_three hc3 (W := ⊤) (fun _ _ => Submodule.mem_top)
      rw [top_inf_eq, finrank_top, hV] at h1
      have h2 := finrank_commSpace_add_finrank_fixSpace c
      rw [hV] at h2
      omega
    have hU2 : finrank (ZMod 2) (commSpace c) = 2 := by omega
    have hcinf : commSpace c ⊓ fixSpace c = ⊥ := by
      rw [inf_comm]
      exact fixSpace_inf_commSpace ⟨1, rfl⟩ hc3
    have hnd : commSpace c ⊓ LinearMap.BilinForm.orthogonal S.q.polarBilin (commSpace c) = ⊥ := by
      rw [← fixSpace_eq_orthogonal hq (isom S z)]
      exact hcinf
    have hD : ∀ a ∈ S.DbarAsc, ∀ u ∈ commSpace c, (a : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
      intro a ha u hu
      have hac : (a : S.Qt ≃ₗ[ZMod 2] S.Qt) * c = c * a := by
        rw [hcdef, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hcomm a (subset_closure ha)]
      exact eq_of_isTypeA (isTypeA_of_mem_dbar S hS ha) hU2 hnd
        (fun v hv => apply_mem_commSpace hac hv) hu
    have hfix := fixed_of_mem_lbar S hD hzL
    have hbot : commSpace c = ⊥ := by
      rw [← hcinf]
      exact le_antisymm (le_inf le_rfl fun u hu => mem_fixSpace.mpr (hfix u hu)) inf_le_left
    rw [hbot, finrank_bot] at hU2
    exact absurd hU2 (by norm_num)

theorem exists_lbar_equiv (hS : S.SixHyp) (hst : S.Asc512Standing) (hsp : S.Asc512SpSix) :
    Nonempty (S.LbarAsc ≃* Sp62) := by
  obtain ⟨e⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix.nonempty_mulEquiv_statedSp_of_lieModel
      hsp.2
  exact ⟨(QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
    (center_lbar_eq_bot S hS hst hsp).symm)).trans e⟩

end CFSG.LargeExtraspecial.AS35QCo
