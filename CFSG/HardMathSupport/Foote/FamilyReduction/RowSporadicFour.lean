module

public import CFSG.LocalAnalysis.OddStandard.AltStdSecLookupFix
public import CFSG.Walter.J1Props.Hyp
public import CFSG.Walter.Models
public import CFSG.Quasithin.H13.NQCatC2JH
public import CFSG.Sporadic.SmallOddCore.J2Local
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitSL25
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitKGJ3
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxH35M12
public import CFSG.GH74.GLS.LU.Local.FiveSL2
public import CFSG.HardMathSupport.Foote.FamilyReduction.Abstract
public import CFSG.Walter.J1.Local

public section

namespace CFSG.HardMathSupport.Foote.FamilyReduction

open CFSG Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

theorem compIn5_inner {S : Type} [Group S] [IsSimpleGroup S] (hna : ∃ x y : S, x * y ≠ y * x)
    (h : CompIn5 S) :
    ∃ t : S, orderOf t = 2 ∧ ∃ B : Subgroup (centralizer ({t} : Set S)), IsComponent B ∧
      Nonempty (B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) := by
  obtain ⟨α, w, hαw, hα, K, hK, ⟨eK⟩, -⟩ := h
  have hα2 : α * α = 1 := by
    have h2 : α ^ 2 = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
    rwa [sq] at h2
  have hα1 : α ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hα
    exact absurd hα (by norm_num)
  refine ⟨w, CFSG.OddStandard.AltStdSec.lookup_orderOf_eq_two_of_conj hna hα2 hα1 hαw, ?_⟩
  obtain ⟨B', hB', ⟨φ⟩⟩ := CFSG.OddStandard.AltStdSec.isComponent_map_fixedSubgroup_conj hαw hK
  exact ⟨B', hB', ⟨φ.trans eK⟩⟩

theorem isComponentOf_map_subtype {X : Type} [Group X] {C : Subgroup X} {B : Subgroup C}
    (hB : IsComponent B) : CFSG.Assembly.IsComponentOf (B.map C.subtype) C := by
  have hle : B.map C.subtype ≤ C := Subgroup.map_subtype_le B
  rw [CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hle]
  have : (B.map C.subtype).subgroupOf C = B :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective B
  rwa [this]

theorem card_sl5 {K : Type} [Group K] (e : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K) :
    Nat.card K = 120 :=
  CFSG.GH74.GLS.LU.Local.Five.sl2_five_card e

theorem card_map_subtype_sl5 {X : Type} [Group X] {C : Subgroup X} {B : Subgroup C}
    (eB : B ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) : Nat.card (B.map C.subtype) = 120 := by
  rw [Subgroup.card_map_of_injective C.subtype_injective, card_sl5 eB.symm]

theorem exists_order_four_sl5 :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5), ¬ g ^ 2 = 1 ∧ g ^ 4 = 1 := by
  refine ⟨⟨!![2, 0; 0, 3], by rw [Matrix.det_fin_two_of]; decide⟩, ?_, ?_⟩
  · decide
  · decide

theorem not_comp5_J1 {Q : Type} [Group Q] [Finite Q]
    (e : Q ≃* NativeSporadic.Carrier .J1) : ¬ CompIn5 Q := by
  rintro ⟨α, w, -, -, K, -, ⟨eK⟩, -⟩
  have hJ : CFSG.Walter.J1.JankoHyp Q := CFSG.Quasithin.H13.NQCat.C2.jankoHypOfMulEquiv
    CFSG.Walter.J1Props.jankoHyp (e.trans CFSG.Walter.walterJ1EquivNative.symm)
  obtain ⟨g, hg2, hg4⟩ := exists_order_four_sl5
  let ι : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) →* Q :=
    (((fixedSubgroup α).subtype.comp K.subtype).comp eK.symm.toMonoidHom)
  have hι : Function.Injective ι :=
    ((fixedSubgroup α).subtype_injective.comp K.subtype_injective).comp eK.symm.injective
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf g = 2 ^ (1 + 1) :=
    orderOf_eq_prime_pow (by simpa using hg2) (by simpa using hg4)
  have hord' : orderOf (ι g) = 2 ^ (1 + 1) := by rw [orderOf_injective ι hι g, hord]
  have hPg : IsPGroup 2 (Subgroup.zpowers (ι g)) :=
    IsPGroup.of_card (n := 1 + 1) (by rw [Nat.card_zpowers, hord'])
  obtain ⟨S, hS⟩ := hPg.exists_le_sylow
  have hmem : ι g ∈ (S : Subgroup Q) := hS (Subgroup.mem_zpowers _)
  have h1 : ι g * ι g = 1 := (hJ.sylow_structure S).2.1 _ hmem
  apply hg2
  apply hι
  rw [map_one, pow_two, map_mul]
  exact h1

theorem no_sl5_component_of_perfect {C : Type} [Group C] [Finite C] [Group.IsPerfect C]
    {K : Subgroup C} (hK : IsComponent K)
    (eK : Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) ≃* K)
    (hcard : Nat.card C * 2 < Nat.card K * Nat.card K) {j : ℕ} (hj : 1 ≤ j)
    (hdiv : Nat.card C = Nat.card K * 2 ^ j) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ2 : Nat.card (center K) = 2 := CFSG.GH74.GLS.LU.Local.Five.sl2_five_center_card eK
  have hKn : K.Normal := ⟨fun n hn c => by
    set K' := K.map (MulAut.conj c).toMonoidHom with hK'def
    have hK' : IsComponent K' := CFSG.LocalCores.isComponent_map_mulEquiv _ hK
    have hmem : c * n * c⁻¹ ∈ K' := ⟨n, hn, by simp⟩
    rcases CFSG.LocalCores.distinct_components_commute hK hK' with h | h
    · rwa [← h] at hmem
    · exfalso
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      have hcomm : ∀ (a : K) (b : K'), Commute (K.subtype a) (K'.subtype b) := fun a b =>
        ((mem_centralizer_iff.mp (hle a.2)) b b.2).symm
      let f := MonoidHom.noncommCoprod K.subtype K'.subtype hcomm
      have hf : ∀ p : K × K', f p = (p.1 : C) * (p.2 : C) := fun p =>
        MonoidHom.noncommCoprod_apply _ _ hcomm p
      have hker : ∀ p : f.ker, (p.1.1 : K) ∈ center K := by
        intro p
        have h1 : (p.1.1 : C) * (p.1.2 : C) = 1 := by rw [← hf]; exact p.2
        have h2 : (p.1.1 : C) = ((p.1.2 : K') : C)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [mem_center_iff]
        intro y
        have h3 : (p.1.1 : C) ∈ K' := by rw [h2]; exact K'.inv_mem p.1.2.2
        exact Subtype.ext (mem_centralizer_iff.mp (hle y.2) _ h3).symm
      have hkerle : Nat.card f.ker ≤ 2 := by
        rw [← hZ2]
        refine Nat.card_le_card_of_injective (fun p => ⟨p.1.1, hker p⟩) ?_
        intro p q hpq
        have h1 : (p.1.1 : K) = q.1.1 := congrArg Subtype.val hpq
        have h2 : (p.1.2 : C) = ((p.1.1 : K) : C)⁻¹ := by
          have : (p.1.1 : C) * (p.1.2 : C) = 1 := by rw [← hf]; exact p.2
          exact eq_inv_of_mul_eq_one_right this
        have h3 : (q.1.2 : C) = ((q.1.1 : K) : C)⁻¹ := by
          have : (q.1.1 : C) * (q.1.2 : C) = 1 := by rw [← hf]; exact q.2
          exact eq_inv_of_mul_eq_one_right this
        refine Subtype.ext (Prod.ext h1 (Subtype.ext ?_))
        rw [h2, h3, h1]
      have hrange : Nat.card f.range ≤ Nat.card C := Subgroup.card_le_card_group _
      have hkr := Subgroup.card_ker_mul_card_range f
      have hK'card : Nat.card K' = Nat.card K :=
        Subgroup.card_map_of_injective (MulAut.conj c).injective
      rw [Nat.card_prod, hK'card] at hkr
      have := Nat.mul_le_mul hkerle hrange
      nlinarith⟩
  have hq : Nat.card (C ⧸ K) = 2 ^ j := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
    rw [hdiv] at h
    have hKpos : 0 < Nat.card ↥K := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hKpos (by rw [mul_comm]; exact h.symm)
  have hnil : Group.IsNilpotent (C ⧸ K) := (IsPGroup.of_card hq).isNilpotent
  have : Nontrivial (C ⧸ K) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hq]
    exact Nat.one_lt_two_pow (by omega)
  exact Group.IsPerfect.not_isNilpotent (G := C ⧸ K) hnil

section J3


theorem not_comp5_J3 {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ∃ x y : Q, x * y ≠ y * x) (e : Q ≃* NativeSporadic.Carrier .J3) : ¬ CompIn5 Q := by
  intro h
  obtain ⟨t, ht, B, hB, ⟨eB⟩⟩ := compIn5_inner hna h
  obtain ⟨hperf, hcard⟩ := CFSG.ComponentClassification.FooteLit.KG.centralizer_perfect_card_of_J3
    (G := Q) ⟨e⟩ t ht
  have : Group.IsPerfect (centralizer ({t} : Set Q)) := hperf
  have hB120 : Nat.card B = 120 := card_sl5 eB.symm
  exact no_sl5_component_of_perfect hB eB.symm (by rw [hcard, hB120]; norm_num) (j := 4)
    (by norm_num) (by rw [hcard, hB120]; norm_num)

end J3

section J2

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.LocalAnalysis.ComponentInitial


theorem j2P_no_comp_card_120 {τ : Equiv.Perm (Fin 315)} (hτP : τ ∈ j2P) (hτ : orderOf τ = 2)
    {B : Subgroup (Equiv.Perm (Fin 315))}
    (hB : CFSG.Assembly.IsComponentOf B (j2P ⊓ centralizer ({τ} : Set _)))
    (h120 : Nat.card B = 120) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, rfl⟩ := hcover τ (j2P_le_j2R hτP) hτ
  set f := (MulAut.conj g⁻¹).toMonoidHom
  have hfinj : Function.Injective f := (MulAut.conj g⁻¹).injective
  have hBr : CFSG.Assembly.IsComponentOf (B.map f)
      (j2P ⊓ centralizer ({tp 315 r.rep} : Set _)) := by
    have h := (isComponentOf_map_iff hfinj).2 hB
    rwa [map_conj_inf_centralizer j2P (j2P.inv_mem hg), Set.image_singleton,
      show f (g * tp 315 r.rep * g⁻¹) = tp 315 r.rep by simp only [f]; simp; group] at h
  have hcardB : Nat.card (B.map f) = 120 := by
    rw [Subgroup.card_map_of_injective hfinj, h120]
  set B' := B.map f
  have htrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) hτP) hg
    rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · have := (hrows _ List.mem_cons_self).2.2.1
    exact absurd htrP (this.1 rfl)
  · obtain ⟨hDcard, hDC1, hC1D, hDsimple, hC1cent⟩ := j2_D_facts
    have hC1 : genOf 315 j2C1Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _) := by
      have h := (hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)).2.2.2.1
      dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
      rw [genOf, j2C1Gens]
      exact h
    dsimp only at hBr
    rw [← hC1] at hBr
    rcases isComponentOf_le_or_commute hBr hDC1 hC1D with hle | hcomm
    · have := Subgroup.card_le_of_le hle
      rw [hcardB, hDcard] at this
      omega
    · have hle : B' ≤ genOf 315 j2C1Gens ⊓
          centralizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315))) := by
        intro x hx
        refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
        rw [mem_centralizer_iff] at this
        exact this y hy
      have := Subgroup.card_le_of_le hle
      rw [hcardB, hC1cent] at this
      omega
  · obtain ⟨hQcard, hQC2, hC2Q, hC2cent⟩ := j2_Q_facts
    have hC2 : genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
      have h := (hrows _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self))).2.2.2.1
      dsimp only [CFSG.Sporadic.SmallOddCore.j2C] at h
      rw [genOf, j2C2Gens]
      exact h
    dsimp only at hBr
    rw [← hC2] at hBr
    rcases isComponentOf_le_or_commute hBr hQC2 hC2Q with hle | hcomm
    · have := Subgroup.card_le_of_le hle
      rw [hcardB, hQcard] at this
      omega
    · have hle : B' ≤ genOf 315 j2C2Gens ⊓
          centralizer (genOf 315 j2QGens : Set (Equiv.Perm (Fin 315))) := by
        intro x hx
        refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
        rw [mem_centralizer_iff] at this
        exact this y hy
      have := Subgroup.card_le_of_le hle
      rw [hcardB, hC2cent] at this
      omega

theorem not_comp5_J2 {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ∃ x y : Q, x * y ≠ y * x) (e : Q ≃* NativeSporadic.Carrier .J2) : ¬ CompIn5 Q := by
  intro h
  obtain ⟨t, ht, B₀, hB₀, ⟨eB⟩⟩ := compIn5_inner hna h
  have hB := isComponentOf_map_subtype hB₀
  set B := B₀.map (centralizer ({t} : Set Q)).subtype
  set ι : Q →* Equiv.Perm (Fin 315) :=
    j2P.subtype.comp ((e : Q ≃* NativeSporadic.J2).trans j2PermEquiv).toMonoidHom
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp ((e : Q ≃* NativeSporadic.J2).trans j2PermEquiv).injective
  have hrange : ι.range = j2P := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr
      ((e : Q ≃* NativeSporadic.J2).trans j2PermEquiv).surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hτP : ι t ∈ j2P := hrange ▸ ⟨t, rfl⟩
  have hτ : orderOf (ι t) = 2 := by rw [orderOf_injective ι hι, ht]
  have hB' : CFSG.Assembly.IsComponentOf (B.map ι)
      (j2P ⊓ centralizer ({ι t} : Set (Equiv.Perm (Fin 315)))) := by
    have := (isComponentOf_map_iff hι).2 hB
    rwa [map_centralizer_eq_inf hι, hrange, Set.image_singleton] at this
  refine j2P_no_comp_card_120 hτP hτ hB' ?_
  rw [Subgroup.card_map_of_injective hι, card_map_subtype_sl5 eB]

end J2

theorem false_of_comm_five {G : Type} [Group G] {M : Subgroup G}
    (eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (ha5 : a ^ 5 = 1) (hb5 : b ^ 5 = 1) (hD2 : a * b * (a * b) = 1) (hD1 : a * b ≠ 1) :
    False := by
  have hab : a * b ∈ M := M.mul_mem ha hb
  have hD : eM ⟨a * b, hab⟩ * eM ⟨a * b, hab⟩ = 1 := by
    rw [← map_mul]
    have : (⟨a * b, hab⟩ : M) * ⟨a * b, hab⟩ = 1 := Subtype.ext hD2
    rw [this, map_one]
  rcases CFSG.ComponentClassification.FooteLit.sl25_eq_one_or_eq_negOne hD with h1 | h1
  · apply hD1
    have : (⟨a * b, hab⟩ : M) = 1 := eM.injective (by rw [h1, map_one])
    exact congrArg Subtype.val this
  · have hcomm : a * b * a = a * (a * b) := by
      have h2 : eM ⟨a, ha⟩ * eM ⟨a * b, hab⟩ = eM ⟨a * b, hab⟩ * eM ⟨a, ha⟩ := by
        rw [h1]
        exact CFSG.ComponentClassification.FooteLit.sl25NegOne_mul_comm _
      rw [← map_mul, ← map_mul] at h2
      exact (congrArg Subtype.val (eM.injective h2)).symm
    have hba : b * a = a * b := by
      have : a * (b * a) = a * (a * b) := by rw [← mul_assoc]; exact hcomm
      exact mul_left_cancel this
    have hc : Commute a b := hba.symm
    have h5 : (a * b) ^ 5 = 1 := by rw [hc.mul_pow, ha5, hb5, mul_one]
    have h2 : (a * b) ^ 2 = 1 := by rw [sq]; exact hD2
    have h6 : (a * b) ^ 5 = a * b := by
      rw [show (5 : ℕ) = 2 * 2 + 1 by norm_num, pow_succ, pow_mul, h2, one_pow, one_mul]
    exact hD1 (h6.symm.trans h5)

@[expose] def centralizerEquivOf {S T : Type*} [Group S] [Group T] (e : S ≃* T) (s : S) :
    ↥(centralizer ({s} : Set S)) ≃* ↥(centralizer ({e s} : Set T)) where
  toFun x := ⟨e x.1, mem_centralizer_singleton_iff.mpr (by
    rw [← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp x.2])⟩
  invFun y := ⟨e.symm y, mem_centralizer_singleton_iff.mpr (by
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply, mem_centralizer_singleton_iff.mp y.2])⟩
  left_inv x := Subtype.ext (e.symm_apply_apply x.1)
  right_inv y := Subtype.ext (e.apply_symm_apply y.1)
  map_mul' x y := Subtype.ext (map_mul e x.1 y.1)

section M12

open CFSG.ComponentClassification.M12Cover CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier


theorem not_comp5_M12_inner {Q : Type} [Group Q] (e : Q ≃* NativeSporadic.M12) (t : Q)
    (ht : orderOf t = 2) (B₀ : Subgroup (centralizer ({t} : Set Q))) (hB₀ : IsComponent B₀)
    (eB : B₀ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) : False := by
  set x₀ : NativeSporadic.M12 := e t with hx₀def
  have hxo : orderOf x₀ = 2 := by rw [hx₀def, MulEquiv.orderOf_eq]; exact ht
  let φ := centralizerEquivOf e t
  have hB := CFSG.LocalCores.isComponent_map_mulEquiv φ hB₀
  set M := (B₀.map φ.toMonoidHom).map (centralizer ({x₀} : Set NativeSporadic.M12)).subtype
    with hMdef
  have hM : CFSG.Assembly.IsComponentOf M (centralizer ({x₀} : Set NativeSporadic.M12)) :=
    isComponentOf_map_subtype hB
  have hM120 : Nat.card M = 120 := by
    rw [hMdef, Subgroup.card_map_of_injective (centralizer ({x₀} : Set _)).subtype_injective,
      Subgroup.card_map_of_injective φ.injective, card_sl5 eB.symm]
  have eM : M ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5) :=
    ((B₀.map φ.toMonoidHom).equivMapOfInjective _
      (centralizer ({x₀} : Set NativeSporadic.M12)).subtype_injective).symm.trans
      ((B₀.equivMapOfInjective φ.toMonoidHom φ.injective).symm.trans eB)
  rcases CFSG.GH74.Generic.S45.LAlt.m12_involution_data x₀ hxo with h192 | ⟨h240, hfix0, -⟩
  · have := Subgroup.card_dvd_of_le hM.1
    rw [h192, hM120] at this
    exact absurd this (by norm_num)
  · obtain ⟨y₀, hy₀⟩ := conj_elemZ_of_fixedCount_zero x₀ hxo hfix0
    have hcop : Nat.Coprime 5 (M.relIndex (centralizer ({x₀} : Set NativeSporadic.M12))) := by
      have hcard : Nat.card (centralizer ({x₀} : Set NativeSporadic.M12)) =
          Nat.card M * M.relIndex (centralizer ({x₀} : Set NativeSporadic.M12)) := by
        rw [← Subgroup.card_mul_index (M.subgroupOf (centralizer ({x₀} : Set _))),
          Subgroup.relIndex, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM.1).toEquiv]
      rw [h240, hM120] at hcard
      have : M.relIndex (centralizer ({x₀} : Set NativeSporadic.M12)) = 2 := by omega
      rw [this]
      norm_num
    obtain ⟨g₀, h₀, hgM, hhM, hgz, hhz, hg5, hh5, hd2, hd1, -⟩ :=
      CFSG.ComponentClassification.SolMax.H35.M12.exists_gh
    set g : NativeSporadic.M12 := ⟨g₀, hgM⟩
    set h : NativeSporadic.M12 := ⟨h₀, hhM⟩
    have hx₀ : x₀ = y₀ * elemZ * y₀⁻¹ := hy₀.symm
    have hg5' : g ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hg5)
    have hh5' : h ^ 5 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hh5)
    have hG : y₀ * g * y₀⁻¹ ∈ M := by
      refine CFSG.ComponentClassification.SolMax.H35.mem_of_isSubnormal_of_coprime hM.2.1 hcop
        (CFSG.ComponentClassification.SolMax.H35.M12.conj_mem_centralizer hgz y₀ hx₀) ?_
      rw [conj_pow, hg5', mul_one, mul_inv_cancel]
    have hH : y₀ * h * y₀⁻¹ ∈ M := by
      refine CFSG.ComponentClassification.SolMax.H35.mem_of_isSubnormal_of_coprime hM.2.1 hcop
        (CFSG.ComponentClassification.SolMax.H35.M12.conj_mem_centralizer hhz y₀ hx₀) ?_
      rw [conj_pow, hh5', mul_one, mul_inv_cancel]
    have hgh2 : g * h * (g * h) = 1 := Subtype.ext hd2
    have hgh1 : g * h ≠ 1 := fun h1 => hd1 (congrArg Subtype.val h1)
    refine false_of_comm_five eM hG hH ?_ ?_ ?_ ?_
    · rw [conj_pow, hg5', mul_one, mul_inv_cancel]
    · rw [conj_pow, hh5', mul_one, mul_inv_cancel]
    · calc y₀ * g * y₀⁻¹ * (y₀ * h * y₀⁻¹) * (y₀ * g * y₀⁻¹ * (y₀ * h * y₀⁻¹)) =
          y₀ * (g * h * (g * h)) * y₀⁻¹ := by group
        _ = 1 := by rw [hgh2]; group
    · intro h1
      apply hgh1
      calc g * h = y₀⁻¹ * (y₀ * g * y₀⁻¹ * (y₀ * h * y₀⁻¹)) * y₀ := by group
        _ = 1 := by rw [h1]; group

theorem not_comp5_M12 {Q : Type} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hna : ∃ x y : Q, x * y ≠ y * x) (e : Q ≃* NativeSporadic.Carrier .M12) : ¬ CompIn5 Q := by
  intro h
  obtain ⟨t, ht, B₀, hB₀, ⟨eB⟩⟩ := compIn5_inner hna h
  exact not_comp5_M12_inner (e : Q ≃* NativeSporadic.M12) t ht B₀ hB₀ eB

end M12

end CFSG.HardMathSupport.Foote.FamilyReduction
