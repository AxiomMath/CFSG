module

public import CFSG.LocalAnalysis.GLTheoremA.S10.InputsAlpha
public import CFSG.LocalAnalysis.GLTheoremA.S10.Inputs105
public import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDChev
public import CFSG.LocalAnalysis.GLTheoremA.S3.KDAmbSolv
public import CFSG.LocalAnalysis.GLTheoremA.CatC.LieQHolds
public import CFSG.LocalAnalysis.GLTheoremA.PartI.U42
public import CFSG.GH74.KGroups.U33
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.Narrow
public import CFSG.Adapters.TauCetiLieModels

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

private theorem autL3_index_A2 (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (h : S9.isL3char2 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    ∃ q : TauCeti.PrimePower, d = TauCeti.LieTypeIndex.A 2 q ∧ q.p = 2 ∧ q.card % 3 = 1 := by
  match d, hv, h with
  | .A r q, hv, h =>
    rcases r with _ | _ | _ | r
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | .twistedA _ _, _, h => exact (show False from h).elim
  | .B _ _, _, h => exact (show False from h).elim
  | .C _ _, _, h => exact (show False from h).elim
  | .D _ _, _, h => exact (show False from h).elim
  | .twistedD _ _, _, h => exact (show False from h).elim
  | .E6 _, _, h => exact (show False from h).elim
  | .E7 _, _, h => exact (show False from h).elim
  | .E8 _, _, h => exact (show False from h).elim
  | .F4 _, _, h => exact (show False from h).elim
  | .G2 _, _, h => exact (show False from h).elim
  | .twistedE6 _, _, h => exact (show False from h).elim
  | .trialityD4 _, _, h => exact (show False from h).elim
  | .suzuki _, _, h => exact (show False from h).elim
  | .reeG2 _, _, h => exact (show False from h).elim
  | .reeF4 _, _, h => exact (show False from h).elim
  | .tits, _, h => exact (show False from h).elim

theorem autL3At_holds (G : Type) [Group G] [Finite G] : AutL3At G := by
  intro X L A hL hcat hAN hA
  have hp : Nat.Prime 3 := Nat.prime_three
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    obtain ⟨q, rfl, -, hq3⟩ := autL3_index_A2 d hv hi
    have hm := CFSG.Models.lieModel_A 2 q hv e
    rcases hm.2 with hcl | ⟨h0, -⟩
    swap
    · exact absurd h0 (by norm_num)
    obtain ⟨-, K, hKf, hKfin, hKcard, ⟨eK⟩⟩ := hcl
    have hK3 : 3 ∣ Nat.card K - 1 := by
      rw [hKcard, ← TauCeti.PrimePower.card_def]
      omega
    have eK' : CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L ≃*
        CFSG.Open.StatedProj (CFSG.Open.StatedSL 3 K) := eK
    have hPQ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hL
    have hQ : CFSG.Open.IsQuasisimple (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) :=
      CFSG.ComponentClassification.Quasisimple.central_quotient hPQ (Subgroup.center _) le_rfl
    have hsimp : IsSimpleGroup (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) := hPQ.2
    have hZ : Subgroup.center (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) = ⊥ := by
      rcases hsimp.eq_bot_or_eq_top_of_normal (Subgroup.center _) with h | h
      · exact h
      · exfalso
        have hc : commutator (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) = ⊥ :=
          (commutator_eq_bot_iff_center_eq_top _).mpr h
        have ht := hQ.1
        rw [hc] at ht
        exact bot_ne_top ht
    have ε : (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L ⧸
        Subgroup.center (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L)) ≃*
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 K :=
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).trans
        (eK'.trans (CFSG.HardMathSupport.Solomon.Coordinator.psiO K))
    let N : Subgroup G := Subgroup.normalizer (L : Set G)
    let H : Subgroup N := A.subgroupOf N
    let ψ : H →* MulAut (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 L) :=
      (CFSG.LocalAnalysis.GLTheoremA.chevAut 3 L).comp H.subtype
    have hcardH : Nat.card H = Nat.card A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    have hsplit : Nat.card H = Nat.card ψ.range * Nat.card ψ.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
    have hf : Function.Injective (N.subtype.comp H.subtype) :=
      Subtype.val_injective.comp Subtype.val_injective
    have hmap : ψ.ker.map (N.subtype.comp H.subtype) =
        A ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup 3 L := by
      ext g
      simp only [Subgroup.mem_map, MonoidHom.mem_ker, Subgroup.mem_inf]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : CFSG.LocalAnalysis.GLTheoremA.chevAut 3 L x.1 = 1 := hx
        have hcent : CFSG.Yardstones.Md0ec50421ce4.CentMod 3 L (x.1 : G) :=
          (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff hp hL x.1.2).1 hx'
        exact ⟨Subgroup.mem_subgroupOf.1 x.2,
          CFSG.LocalAnalysis.GLTheoremA.centMod_iff.1 hcent⟩
      · rintro ⟨hgA, hgC⟩
        have hgN : g ∈ N := (CFSG.LocalAnalysis.GLTheoremA.mem_centModSubgroup.1 hgC).1
        refine ⟨⟨⟨g, hgN⟩, Subgroup.mem_subgroupOf.2 hgA⟩, ?_, rfl⟩
        show CFSG.LocalAnalysis.GLTheoremA.chevAut 3 L ⟨g, hgN⟩ = 1
        exact (CFSG.LocalAnalysis.GLTheoremA.chevAut_eq_one_iff hp hL hgN).2
          (CFSG.LocalAnalysis.GLTheoremA.centMod_iff.2 hgC)
    have hkerCard : Nat.card ψ.ker =
        Nat.card ↥(A ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup 3 L) := by
      rw [← hmap, Subgroup.card_map_of_injective hf]
    have hHcomm : ∀ x y : H, x * y = y * x := by
      intro x y
      have hxA : (x.1 : G) ∈ A := Subgroup.mem_subgroupOf.1 x.2
      have hyA : (y.1 : G) ∈ A := Subgroup.mem_subgroupOf.1 y.2
      have h1 := congrArg Subtype.val
        ((isMulCommutative_iff.mp hA.1) ⟨(x.1 : G), hxA⟩ ⟨(y.1 : G), hyA⟩)
      apply Subtype.ext
      apply Subtype.ext
      simpa using h1
    have hE0 : CFSG.Open.IsElemAbelian 3 ψ.range := by
      refine ⟨isMulCommutative_iff.mpr ?_, ?_⟩
      · rintro ⟨a, ha⟩ ⟨b, hb⟩
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
        obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 hb
        apply Subtype.ext
        show ψ x * ψ y = ψ y * ψ x
        rw [← map_mul, ← map_mul, hHcomm x y]
      · intro a ha
        obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 ha
        have hxA : (x.1 : G) ∈ A := Subgroup.mem_subgroupOf.1 x.2
        have hx3 : x ^ 3 = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa using hA.2 _ hxA
        rw [← map_pow, hx3, map_one]
    have hE0card : Nat.card ψ.range ≤ 3 ^ 3 :=
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.GenL3.card_elemAbelian_le_27
        hQ hK3 ε ψ.range hE0).trans (by norm_num)
    calc Nat.card A = Nat.card H := hcardH.symm
      _ = Nat.card ψ.range * Nat.card ψ.ker := hsplit
      _ ≤ 3 ^ 3 * Nat.card ψ.ker := Nat.mul_le_mul_right _ hE0card
      _ = 3 ^ 3 * Nat.card ↥(A ⊓ CFSG.LocalAnalysis.GLTheoremA.centModSubgroup 3 L) := by
        rw [hkerCard]

private theorem u33_index_twistedA (d : TauCeti.LieTypeIndex) (hv : d.Valid)
    (h : S10.isU33 (TauCeti.CFSGIndex.lie ⟨d, hv⟩)) :
    ∃ q : TauCeti.PrimePower, d = TauCeti.LieTypeIndex.twistedA 2 q ∧ q.card = 3 := by
  match d, hv, h with
  | .twistedA r q, hv, h =>
    rcases r with _ | _ | _ | r
    · exact (show False from h).elim
    · exact (show False from h).elim
    · exact ⟨q, rfl, h⟩
    · exact (show False from h).elim
  | .A _ _, _, h => exact (show False from h).elim
  | .B _ _, _, h => exact (show False from h).elim
  | .C _ _, _, h => exact (show False from h).elim
  | .D _ _, _, h => exact (show False from h).elim
  | .twistedD _ _, _, h => exact (show False from h).elim
  | .E6 _, _, h => exact (show False from h).elim
  | .E7 _, _, h => exact (show False from h).elim
  | .E8 _, _, h => exact (show False from h).elim
  | .F4 _, _, h => exact (show False from h).elim
  | .G2 _, _, h => exact (show False from h).elim
  | .twistedE6 _, _, h => exact (show False from h).elim
  | .trialityD4 _, _, h => exact (show False from h).elim
  | .suzuki _, _, h => exact (show False from h).elim
  | .reeG2 _, _, h => exact (show False from h).elim
  | .reeF4 _, _, h => exact (show False from h).elim
  | .tits, _, h => exact (show False from h).elim

private theorem u33_pq {q : TauCeti.PrimePower} (hq : q.card = 3) :
    q.p = 3 ∧ q.exponent = 1 := by
  have hcard3 : q.p ^ q.exponent = 3 := by
    rw [← TauCeti.PrimePower.card_def]
    exact hq
  have hpq : q.p = 3 := by
    have hdvd : q.p ∣ 3 := by
      rw [← hcard3]
      exact dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1 hdvd
  refine ⟨hpq, ?_⟩
  rw [hpq] at hcard3
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3)
    (show 3 ^ q.exponent = 3 ^ 1 by simpa using hcard3)

private theorem u33_lieModel
    {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA 2 q).Valid) (hq : q.card = 3) :
    Nonempty ((TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group ≃*
      CFSG.GH74.KGroups.U33.QP.originalSubgroup) := by
  obtain ⟨hpq, hfq⟩ := u33_pq hq
  have hmodel' := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv
    (MulEquiv.refl (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group)
  rw [hpq, hfq] at hmodel'
  have hmodel : CFSG.Blueprint.LieModel (TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩).Group
      .PSU 3 3 1 := Or.inl ⟨by decide, hmodel'⟩
  obtain ⟨e⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel hmodel
  exact ⟨e⟩

private theorem u33_card {K : Type} [Group K]
    (E : K ≃* CFSG.GH74.KGroups.U33.QP.originalSubgroup) :
    Nat.card K = 6048 ∧ Nat.card (MulAut K) = 12096 := by
  refine ⟨?_, CFSG.GH74.KGroups.U33.card_mulAut E⟩
  rw [Nat.card_congr E.toEquiv, CFSG.GH74.KGroups.card_group _ CFSG.GH74.KGroups.U33.QP_ok,
    CFSG.GH74.KGroups.U33.QP_valid.2]

private theorem u33_mem_inner {S : Type} [Group S] (hz : Subgroup.center S = ⊥)
    (hS : Nat.card S = 6048) (hA : Nat.card (MulAut S) = 12096) (α : MulAut S) (hα : α ^ 3 = 1) :
    α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner S := by
  have hinj : Function.Injective (MulAut.conj : S →* MulAut S) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hc : g ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h3 := congrArg (fun φ : MulAut S => φ h) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      exact (mul_inv_eq_iff_eq_mul.1 h3).symm
    rw [hz, Subgroup.mem_bot] at hc
    exact hc
  have hinner : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner S) = Nat.card S :=
    Nat.card_range_of_injective hinj
  have hidx := (CFSG.ComponentClassification.OuterAutomorphisms.inner S).card_mul_index
  rw [hinner, hS, hA] at hidx
  have hO : (CFSG.ComponentClassification.OuterAutomorphisms.inner S).index = 2 := by
    omega
  haveI : Finite (MulAut S) := Nat.finite_of_card_ne_zero (by rw [hA]; norm_num)
  let π : MulAut S →* CFSG.ComponentClassification.OuterAutomorphisms.Outer S :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner S)
  have hp' : π α ^ 3 = 1 := by
    rw [← map_pow, hα, map_one]
  have hord : orderOf (π α) ∣ 3 := orderOf_dvd_of_pow_eq_one hp'
  have hdvd : orderOf (π α) ∣ 2 := by
    have h2 : orderOf (π α) ∣ (CFSG.ComponentClassification.OuterAutomorphisms.inner S).index :=
      orderOf_dvd_natCard (π α)
    rw [hO] at h2
    exact h2
  have hg1 : orderOf (π α) ∣ 1 := by
    have h3 := Nat.dvd_gcd hord hdvd
    rwa [show Nat.gcd 3 2 = 1 by norm_num] at h3
  have h1 : orderOf (π α) = 1 := Nat.dvd_one.1 hg1
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 h1)

theorem u33SolvCentAt_holds (G : Type) [Group G] [Finite G] :
    U33SolvCentAt G := by
  intro X I y hI hcat hyN hy3 hnc
  have hp : Nat.Prime 3 := Nat.prime_three
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  obtain ⟨i, hi, ⟨f⟩⟩ := hcat
  cases i with
  | cyclic _ _ => exact (show False from hi).elim
  | alternating _ _ => exact (show False from hi).elim
  | sporadic _ => exact (show False from hi).elim
  | lie j =>
    obtain ⟨d, hv⟩ := j
    obtain ⟨q, rfl, hq⟩ := u33_index_twistedA d hv hi
    obtain ⟨e⟩ := u33_lieModel hv hq
    obtain ⟨hS, hA⟩ := u33_card (f.trans e)
    obtain ⟨hsimple, hnonab⟩ := CFSG.LocalAnalysis.GLTheoremA.chev_pSimple_simple_nonabelian hp hI
    have hz : Subgroup.center (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 I) = ⊥ := by
      haveI := hsimple
      exact CFSG.LocalAnalysis.GLTheoremA.chev_center_eq_bot_of_simple_nonabelian hnonab
    have hmem := u33_mem_inner hz hS hA
      (CFSG.LocalAnalysis.GLTheoremA.chevAut 3 I ⟨y, hyN⟩)
      (CFSG.LocalAnalysis.GLTheoremA.chevAut_pow_eq_one 3 I hyN hy3)
    have hin : CFSG.Yardstones.Md0ec50421ce4.InducesInnerMod 3 I y :=
      (CFSG.LocalAnalysis.GLTheoremA.chevAut_mem_inner_iff hp hI hyN).1 hmem
    obtain ⟨hpq, -⟩ := u33_pq hq
    have hchev : CFSG.Yardstones.Md0ec50421ce4.IsChevSimple 3
        (CFSG.Yardstones.Md0ec50421ce4.PSimple 3 I) := by
      refine Or.inl ⟨TauCeti.CFSGIndex.lie ⟨.twistedA 2 q, hv⟩, ?_, ⟨f⟩⟩
      show TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.twistedA 2 q) = 3
      rw [TauCeti.LieTypeIndex.characteristic_twistedA]
      exact hpq
    have hKI : CFSG.LocalAnalysis.GLTheoremA.KDChevInner 3 :=
      CFSG.LocalAnalysis.GLTheoremA.kdChevInner_of hp hp2
        (CFSG.LocalAnalysis.GLTheoremA.kdCharP_holds hp hp2)
        (CFSG.LocalAnalysis.GLTheoremA.kdAmbSolv_holds hp hp2
          CFSG.LocalAnalysis.GLTheoremA.u42_fixSubgroup_solvable)
    have hempty : {L : Subgroup G |
        GLAPComponent 3 (I ⊓ Subgroup.centralizer ({y} : Set G)) L} = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun L hL =>
        CFSG.LocalAnalysis.GLTheoremA.chev_one_element_inner hp hKI hI hchev hyN hy3 hnc hin L hL
    show sSup {L : Subgroup G | GLAPComponent 3 (I ⊓ Subgroup.centralizer ({y} : Set G)) L} = ⊥
    rw [hempty, sSup_empty]

end CFSG.LocalAnalysis.GLTheoremA
