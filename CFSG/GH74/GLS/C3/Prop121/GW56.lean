module

public import CFSG.Adapters.QiuzhenLegacy.Compat.G7.ASeven
public import CFSG.Quasithin.Background.I4Dihedral
public import CFSG.GH74.KGroups.A6
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix
public import CFSG.Dihedral.GorensteinWalter
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedSupport
public import CFSG.CharacterTheory.Wreathed.WreathCentralSquare
public import CFSG.CharacterTheory.Wreathed.BrauerWongSylowCentralizer
public import CFSG.GroupTheory.QuasiDihedralFusion.Basic
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotients
public import CFSG.LocalAnalysis.ComponentInitial.OddLinearTwoAliases
public import CFSG.Dihedral.DihedralFusionPrefixes
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.Walter.Defs
public import Certificates.Certificate10
public import Certificates.Certificate8
public import Certificates.Certificate9
public import CFSG.Assembly.OrderReductions.OddInversion
public import Certificates.Certificate7
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate1
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Mathlib.Algebra.AffineMonoid.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Even
public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Vector.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.GroupExtension.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.GroupTheory.Perm.Closure
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.GroupTheory.RegularWreathProduct
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Logic.Equiv.Option
public import Mathlib.NumberTheory.Fermat
public import Mathlib.RingTheory.TensorProduct.Finite
public import TauCeti.Algebra.Group.Subgroup.Map

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup CFSG.GorensteinWalter

theorem gw56_index_ne_two {X : Type*} [Group X] [Finite X]
    (hSyl : ∀ S : Sylow 2 X, Nonempty ((S : Subgroup X) ≃* DihedralGroup 4))
    (hone : ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    (M : Subgroup X) (hM : M.index = 2) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMn : M.Normal := Subgroup.normal_of_index_eq_two hM
  obtain ⟨T⟩ : Nonempty (Sylow 2 X) := inferInstance
  obtain ⟨e⟩ := hSyl T
  have hsq : ∀ g : X, g ^ 2 ∈ M := by
    intro g
    have h1 : (QuotientGroup.mk g : X ⧸ M) ^ Nat.card (X ⧸ M) = 1 := pow_card_eq_one'
    rw [← Subgroup.index_eq_card, hM, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h1
    exact h1
  have hTM : ¬ (T : Subgroup X) ≤ M := by
    intro h
    have h1 : M.index ∣ (T : Subgroup X).index := Subgroup.index_dvd_of_le h
    rw [hM] at h1
    exact T.not_dvd_index h1
  obtain ⟨t, htT, htM⟩ : ∃ t ∈ (T : Subgroup X), t ∉ M := by
    by_contra hcon
    push Not at hcon
    exact hTM hcon
  have hinv : ∀ i : ZMod 4, orderOf ((e.symm (DihedralGroup.sr i) : T) : X) = 2 := by
    intro i
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  obtain ⟨s, hs2, hsM⟩ : ∃ s : X, orderOf s = 2 ∧ s ∉ M := by
    set u : DihedralGroup 4 := e ⟨t, htT⟩ with hu
    have htu : t = ((e.symm u : T) : X) := by simp [hu]
    cases hc : u with
    | sr i =>
      refine ⟨t, ?_, htM⟩
      rw [htu, hc]
      exact hinv i
    | r i =>
      by_cases h0 : ((e.symm (DihedralGroup.sr 0) : T) : X) ∈ M
      · refine ⟨((e.symm (DihedralGroup.sr 0) : T) : X) * t, ?_, ?_⟩
        · have : (e.symm (DihedralGroup.sr 0) : T) * ⟨t, htT⟩ = e.symm (DihedralGroup.sr i) := by
            have h2 : e (e.symm (DihedralGroup.sr 0) * ⟨t, htT⟩) = DihedralGroup.sr i := by
              rw [map_mul, MulEquiv.apply_symm_apply, ← hu, hc, DihedralGroup.sr_mul_r]
              simp
            rw [← h2, MulEquiv.symm_apply_apply]
          have h3 := hinv i
          rw [← this] at h3
          simpa using h3
        · intro hmem
          exact htM ((M.mul_mem_cancel_left h0).mp hmem)
      · exact ⟨_, hinv 0, h0⟩
  have hz0 : ((e.symm (DihedralGroup.r 2) : T) : X) ∈ M := by
    have : ((e.symm (DihedralGroup.r 2) : T) : X) =
        ((e.symm (DihedralGroup.r 1) : T) : X) ^ 2 := by
      rw [← Subgroup.coe_pow, ← map_pow]
      congr 2
    rw [this]
    exact hsq _
  have hz02 : orderOf ((e.symm (DihedralGroup.r 2) : T) : X) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    apply orderOf_eq_prime
    · rw [pow_two, DihedralGroup.r_mul_r, DihedralGroup.one_def]
      exact congrArg DihedralGroup.r (by decide)
    · rw [DihedralGroup.one_def]
      intro h
      have := DihedralGroup.r.inj h
      exact absurd this (by decide)
  obtain ⟨g, hg⟩ := isConj_iff.mp (hone _ _ hz02 hs2)
  apply hsM
  have : s = g * ((e.symm (DihedralGroup.r 2) : T) : X) * g⁻¹ := hg.symm
  rw [this]
  exact hMn.conj_mem _ hz0 g

theorem gw56_card_centralizer_eq_index_mul {G : Type*} [Group G] [Finite G] {L : Subgroup G}
    [L.Normal] (hL : Odd L.index) {z : G} (hz : orderOf z = 2) (hzL : z ∈ L)
    (hinvG : ∀ u : G, orderOf u = 2 → IsConj z u)
    (hinvL : ∀ u : L, orderOf u = 2 → IsConj (⟨z, hzL⟩ : L) u) :
    Nat.card (Subgroup.centralizer ({z} : Set G)) =
      L.index * Nat.card (Subgroup.centralizer ({(⟨z, hzL⟩ : L)} : Set L)) := by
  set z' : L := ⟨z, hzL⟩ with hz'def
  have hz' : orderOf z' = 2 := by rw [hz'def, Subgroup.orderOf_mk, hz]
  have hG := CFSG.Quasithin.I4.index_centralizer_eq_ncard hz hinvG
  have hL' := CFSG.Quasithin.I4.index_centralizer_eq_ncard hz' hinvL
  have hset : {u : G | orderOf u = 2} = Subtype.val '' {u : L | orderOf u = 2} := by
    ext u
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hu
      have huL : u ∈ L := CFSG.Quasithin.I4.mem_of_odd_index hL (k := 1) (by rw [hu, pow_one])
      exact ⟨⟨u, huL⟩, by rw [Subgroup.orderOf_mk, hu], rfl⟩
    · rintro ⟨v, hv, rfl⟩
      rwa [Subgroup.orderOf_coe]
  have hncard : {u : G | orderOf u = 2}.ncard = {u : L | orderOf u = 2}.ncard := by
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective]
  have h1 := (Subgroup.centralizer ({z} : Set G)).card_mul_index
  have h2 := (Subgroup.centralizer ({z'} : Set L)).card_mul_index
  have h3 := L.card_mul_index
  rw [hG] at h1
  rw [hL', ← hncard] at h2
  have hI : 0 < {u : G | orderOf u = 2}.ncard := by
    rw [← hG]
    exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have : Nat.card (Subgroup.centralizer ({z} : Set G)) * {u : G | orderOf u = 2}.ncard =
      (L.index * Nat.card (Subgroup.centralizer ({z'} : Set L))) *
        {u : G | orderOf u = 2}.ncard := by
    rw [h1, ← h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hI this

theorem gw56_trichotomy
    {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥)
    (hSyl : ∀ S : Sylow 2 X, Nonempty ((S : Subgroup X) ≃* DihedralGroup 4))
    (hone : ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {z : X} (hz : orderOf z = 2) (hnot2 : ¬ IsPGroup 2 X) :
    (Nonempty (X ≃* alternatingGroup (Fin 7)) ∧
        Nat.card (Subgroup.centralizer ({z} : Set X)) = 24) ∨
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (L : Subgroup X),
        L.Normal ∧ IsOddPrimePower (Nat.card F) ∧ Odd L.index ∧ Nonempty (L ≃* PSL2 F) ∧
        (Nat.card F % 4 = 1 →
          Nat.card (Subgroup.centralizer ({z} : Set X)) = L.index * (Nat.card F - 1)) ∧
        (Nat.card F % 4 = 3 →
          Nat.card (Subgroup.centralizer ({z} : Set X)) = L.index * (Nat.card F + 1)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdih : HasDihedralSylowTwo X := fun S => by
    obtain ⟨e⟩ := hSyl S
    exact ⟨2, by norm_num, ⟨e⟩⟩
  have hinv : ∀ u : X, orderOf u = 2 → IsConj z u := fun u hu => hone z u hz hu
  let eQ : X ⧸ pPrimeCore 2 X ≃* X :=
    (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  rcases gorensteinWalter X hdih with ⟨-, hTwo⟩ | ⟨-, ⟨h7⟩⟩ | ⟨-, F, hF, L, hLn, hLodd, hLmodel⟩
  · exact absurd (hTwo.of_equiv eQ) hnot2
  · left
    let f : X ≃* alternatingGroup (Fin 7) := eQ.symm.trans h7
    refine ⟨⟨f⟩, ?_⟩
    have hfz : orderOf (f z) = 2 := by rw [MulEquiv.orderOf_eq, hz]
    obtain ⟨g, hg⟩ := aSeven_involutions_conjugate (f z) a7t
      (CFSG.Quasithin.I4.isInvolution_of_orderOf_eq_two hfz) a7t_involution
    symm
    rw [← a7t_centralizer_card, ← hg]
    change Nat.card (Subgroup.centralizer {(MulAut.conj g) (f z)}) = _
    rw [CFSG.Quasithin.I4.card_centralizer_map, CFSG.Quasithin.I4.card_centralizer_map]
  · right
    obtain ⟨p, f, hp, hpodd, hf, hFcard⟩ := hF
    have : Fact p.Prime := ⟨hp⟩
    have : L.Normal := hLn
    set L' : Subgroup X := L.map eQ.toMonoidHom with hL'def
    have hL'n : L'.Normal := hLn.map eQ.toMonoidHom eQ.surjective
    have hL'odd : Odd L'.index := by
      rw [hL'def, Subgroup.index_map_of_injective _ eQ.injective,
        MonoidHom.range_eq_top.mpr eQ.surjective, Subgroup.index_top, mul_one]
      exact hLodd
    let eL : L' ≃* L := (L.equivMapOfInjective eQ.toMonoidHom eQ.injective).symm
    have hzL : z ∈ L' :=
      CFSG.Quasithin.I4.mem_of_odd_index hL'odd (k := 1) (by rw [pow_one, hz])
    rcases hLmodel with hPSL | hPGL
    ·
      obtain ⟨ePSL⟩ := hPSL
      let eL' : L' ≃* PSL2 F := eL.trans ePSL
      have hz' : orderOf (eL' ⟨z, hzL⟩) = 2 := by
        rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hz]
      have hinvL : ∀ u : L', orderOf u = 2 → IsConj (⟨z, hzL⟩ : L') u := by
        intro u hu
        have hu' : orderOf (eL' u) = 2 := by rw [MulEquiv.orderOf_eq, hu]
        have hc := eL'.symm.toMonoidHom.map_isConj
          (CFSG.Walter.psl2_isConj_of_orderOf_eq_two F hFcard hpodd hf hz' hu')
        simpa using hc
      have hcount := gw56_card_centralizer_eq_index_mul hL'odd hz hzL hinv hinvL
      have hCt : Nat.card (Subgroup.centralizer ({(⟨z, hzL⟩ : L')} : Set L')) =
          Nat.card (Subgroup.centralizer ({eL' ⟨z, hzL⟩} : Set (PSL2 F))) :=
        (CFSG.Quasithin.I4.card_centralizer_map eL' ⟨z, hzL⟩).symm
      obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution F hFcard hpodd hf hz'
      refine ⟨F, inferInstance, inferInstance, L', hL'n, ⟨p, f, hp, hpodd, hf, hFcard⟩, hL'odd,
        ⟨eL'⟩, ?_, ?_⟩
      · intro h4
        rw [hFcard] at h4 ⊢
        rw [hcount, hCt, (h1 h4).1]
      · intro h4
        rw [hFcard] at h4 ⊢
        rw [hcount, hCt, (h3 h4).1]
    ·
      exfalso
      obtain ⟨ePGL⟩ := hPGL
      let eP : L' ≃* PGL2 F := eL.trans ePGL
      have hqodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
      have hK' : IsOddPrimePower (Nat.card F) := ⟨p, f, hp, hpodd, hf, hFcard⟩
      obtain ⟨L'', hL''n, -, ⟨eL''⟩⟩ :
          ∃ L'' : Subgroup X, L''.Normal ∧ L'' ≤ L' ∧ Nonempty (L'' ≃* PSL2 F) := by
        by_cases h3 : 3 < Nat.card F
        · exact exists_normal_psl2_core_of_normal_mulEquiv_pgl2_card_gt_three L' hL'n F hK' h3 eP
        · have hK3 : Nat.card F = 3 := by
            have hp3 : 3 ≤ p := by
              have := hp.two_le
              rcases hpodd with ⟨k, hk⟩
              omega
            have : p ≤ p ^ f := Nat.le_self_pow (by omega) p
            omega
          let : Fintype F := Fintype.ofFinite F
          let eK : ZMod 3 ≃+* F :=
            ZMod.ringEquivOfPrime F Nat.prime_three (by rw [← Nat.card_eq_fintype_card, hK3])
          obtain ⟨L'', h1, h2, ⟨e3⟩⟩ := exists_normal_psl2_three_core_of_normal_mulEquiv_pgl2_three
            L' hL'n (eP.trans (pgl2RingEquiv eK).symm)
          exact ⟨L'', h1, h2, ⟨e3.trans (psl2RingEquiv eK)⟩⟩
      have : L''.Normal := hL''n
      have hcard1 : Nat.card L' = Nat.card F * (Nat.card F ^ 2 - 1) :=
        (Nat.card_congr eP.toEquiv).trans (pgl2_card_formula F)
      have hcard2 : Nat.card L'' = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
        (Nat.card_congr eL''.toEquiv).trans (psl2_card_formula F hK')
      have heven : 2 ∣ Nat.card F * (Nat.card F ^ 2 - 1) :=
        (Nat.Odd.sub_odd hqodd.pow odd_one).two_dvd.mul_left _
      have hcard : Nat.card L' = 2 * Nat.card L'' := by
        rw [hcard1, hcard2, Nat.mul_div_cancel' heven]
      have hidx : L''.index = 2 * L'.index := by
        have h1 := L'.card_mul_index
        have h2 := L''.card_mul_index
        rw [hcard] at h1
        have hpos : 0 < Nat.card L'' := Nat.card_pos
        have : Nat.card L'' * L''.index = Nat.card L'' * (2 * L'.index) := by
          rw [h2, ← h1]
          ring
        exact Nat.eq_of_mul_eq_mul_left hpos this
      obtain ⟨M, hM⟩ := CFSG.Quasithin.I4.exists_index_two_of_index_eq_two_mul_odd hL'odd hidx
      exact gw56_index_ne_two hSyl hone M hM

theorem gw56_card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem gw56_card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem gw56_not_isPGroup_two {X : Type*} [Group X] [Finite X] {K : Subgroup X}
    (h : 3 ∣ Nat.card K) : ¬ IsPGroup 2 X := by
  intro hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have h3 : 3 ∣ 2 ^ k := by
    rw [← hk]
    exact h.trans (Subgroup.card_subgroup_dvd_card K)
  exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)

theorem gw56_arith_five {q idx : ℕ} (hq : Odd q) (hidx : Odd idx)
    (h1 : q % 4 = 1 → 8 = idx * (q - 1)) (h3 : q % 4 = 3 → 8 = idx * (q + 1))
    (hK : 60 ∣ idx * (q * (q ^ 2 - 1) / 2)) : idx = 1 ∧ q = 9 := by
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    have := Nat.odd_iff.mp hq
    omega
  have hdvd : idx ∣ 8 := by
    rcases hq4 with h | h
    · exact ⟨q - 1, h1 h⟩
    · exact ⟨q + 1, h3 h⟩
  have hle : idx ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  have hidx1 : idx = 1 := by
    interval_cases idx <;> first | rfl | (exfalso; revert hdvd hidx; decide)
  subst hidx1
  refine ⟨rfl, ?_⟩
  rcases hq4 with h | h
  · have := h1 h
    omega
  · have := h3 h
    have hq7 : q = 7 := by omega
    subst hq7
    exfalso
    revert hK
    norm_num

theorem gw56_arith_six {q idx : ℕ} (hq : Odd q) (hidx : Odd idx)
    (h1 : q % 4 = 1 → 24 = idx * (q - 1)) (h3 : q % 4 = 3 → 24 = idx * (q + 1))
    (hK : 360 ∣ idx * (q * (q ^ 2 - 1) / 2)) : idx = 3 ∧ q = 9 := by
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by
    have := Nat.odd_iff.mp hq
    omega
  have hdvd : idx ∣ 24 := by
    rcases hq4 with h | h
    · exact ⟨q - 1, h1 h⟩
    · exact ⟨q + 1, h3 h⟩
  have hle : idx ≤ 24 := Nat.le_of_dvd (by norm_num) hdvd
  have hidx' : idx = 1 ∨ idx = 3 := by
    interval_cases idx <;> first | omega | (exfalso; revert hdvd hidx; decide)
  rcases hidx' with rfl | rfl
  · exfalso
    rcases hq4 with h | h
    · have := h1 h
      have hq25 : q = 25 := by omega
      subst hq25
      revert hK
      norm_num
    · have := h3 h
      have hq23 : q = 23 := by omega
      subst hq23
      revert hK
      norm_num
  · refine ⟨rfl, ?_⟩
    rcases hq4 with h | h
    · have := h1 h
      omega
    · have := h3 h
      have hq7 : q = 7 := by omega
      subst hq7
      exfalso
      revert hK
      norm_num

theorem gw56_no_normal_simple_index_three {X : Type*} [Group X] [Finite X]
    (hO : ∀ N : Subgroup X, N.Normal → Nat.Coprime 2 (Nat.card N) → N = ⊥)
    (L : Subgroup X) [L.Normal] [IsSimpleGroup L]
    (hcard : Nat.card L = 360) (hidx : L.index = 3) (hAut : Nat.card (MulAut L) = 1440) :
    False := by
  classical
  have hcenter : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      let _ : CommGroup L := Group.commGroupOfCenterEqTop h
      have hp := IsSimpleGroup.prime_card (α := L)
      rw [hcard] at hp
      exact absurd hp (by norm_num)
  let φ : X →* MulAut L := MulAut.conjNormal
  have hker : φ.ker ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
    rw [Subgroup.mem_bot]
    have hgc : (⟨g, hg2⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro h
      have := congrArg (fun a : MulAut L => ((a h : L) : X)) (MonoidHom.mem_ker.mp hg1)
      simp only [MulAut.one_apply] at this
      apply Subtype.ext
      have h2 : g * (h : X) * g⁻¹ = h := this
      calc (h : X) * g = g * h * g⁻¹ * g := by rw [h2]
        _ = g * h := by group
    rw [hcenter, Subgroup.mem_bot] at hgc
    exact congrArg Subtype.val hgc
  have hkerdvd : Nat.card φ.ker ∣ 3 := by
    have : Nat.card (X ⧸ L) = 3 := by rw [← Subgroup.index_eq_card, hidx]
    rw [← this]
    refine Subgroup.card_dvd_of_injective ((QuotientGroup.mk' L).comp φ.ker.subtype) ?_
    intro a b hab
    have h1 : ((a : X)⁻¹ * (b : X)) ∈ L := by
      have := QuotientGroup.eq.mp hab
      simpa using this
    have h2 : ((a : X)⁻¹ * (b : X)) ∈ φ.ker := φ.ker.mul_mem (φ.ker.inv_mem a.2) b.2
    have h3 : ((a : X)⁻¹ * (b : X)) ∈ φ.ker ⊓ L := Subgroup.mem_inf.mpr ⟨h2, h1⟩
    rw [hker, Subgroup.mem_bot] at h3
    apply Subtype.ext
    exact (inv_mul_eq_one.mp h3)
  have hkerbot : φ.ker = ⊥ := by
    refine hO _ inferInstance ?_
    have h3 : Nat.Coprime 2 3 := by norm_num
    exact Nat.Coprime.coprime_dvd_right hkerdvd h3
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hkerbot
  have hdvd : Nat.card X ∣ 1440 := by
    rw [← hAut]
    exact Subgroup.card_dvd_of_injective φ hinj
  have hX : Nat.card X = 1080 := by
    rw [← L.card_mul_index, hcard, hidx]
  rw [hX] at hdvd
  exact absurd hdvd (by norm_num)

theorem gw56_five
    {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥)
    (hSyl : ∀ S : Sylow 2 X, Nonempty ((S : Subgroup X) ≃* DihedralGroup 4))
    (hone : ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {z : X} (hz : orderOf z = 2) (hC : Nat.card (Subgroup.centralizer ({z} : Set X)) = 8)
    {K : Subgroup X} (hK : Nonempty (K ≃* alternatingGroup (Fin 5))) :
    Nonempty (X ≃* alternatingGroup (Fin 6)) := by
  classical
  obtain ⟨eK⟩ := hK
  have hKcard : Nat.card K = 60 := (Nat.card_congr eK.toEquiv).trans gw56_card_alt_five
  have hnot2 : ¬ IsPGroup 2 X :=
    gw56_not_isPGroup_two (K := K) (by rw [hKcard]; norm_num)
  rcases gw56_trichotomy hO hSyl hone hz hnot2 with ⟨-, h24⟩ | ⟨F, hFfield, hFfin, L, hLn,
    hFodd, hLodd, ⟨eL⟩, h1, h3⟩
  · rw [hC] at h24
    exact absurd h24 (by norm_num)
  · have : L.Normal := hLn
    obtain ⟨p, f, hp, hpodd, hf, hFcard⟩ := hFodd
    have hqodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
    have hLcard : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
      (Nat.card_congr eL.toEquiv).trans (psl2_card_formula F ⟨p, f, hp, hpodd, hf, hFcard⟩)
    have hKX : 60 ∣ L.index * (Nat.card F * (Nat.card F ^ 2 - 1) / 2) := by
      rw [← hLcard, mul_comm, L.card_mul_index, ← hKcard]
      exact Subgroup.card_subgroup_dvd_card K
    obtain ⟨hidx, hq⟩ := gw56_arith_five hqodd hLodd (fun h => hC.symm.trans (h1 h))
      (fun h => hC.symm.trans (h3 h)) hKX
    have htop : L = ⊤ := Subgroup.index_eq_one.mp hidx
    let eX : X ≃* PSL2 F :=
      Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans eL)
    let _ : Fintype F := Fintype.ofFinite F
    have hF9 : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hq]
    obtain ⟨e6⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        F hF9
    exact ⟨eX.trans e6⟩

theorem gw56_six
    {X : Type} [Group X] [Finite X]
    (hO : pPrimeCore 2 X = ⊥)
    (hSyl : ∀ S : Sylow 2 X, Nonempty ((S : Subgroup X) ≃* DihedralGroup 4))
    (hone : ∀ a b : X, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {z : X} (hz : orderOf z = 2) (hC : Nat.card (Subgroup.centralizer ({z} : Set X)) = 24)
    {K : Subgroup X} (hK : Nonempty (K ≃* alternatingGroup (Fin 6))) :
    Nonempty (X ≃* alternatingGroup (Fin 7)) := by
  classical
  obtain ⟨eK⟩ := hK
  have hKcard : Nat.card K = 360 := (Nat.card_congr eK.toEquiv).trans gw56_card_alt_six
  have hnot2 : ¬ IsPGroup 2 X :=
    gw56_not_isPGroup_two (K := K) (by rw [hKcard]; norm_num)
  rcases gw56_trichotomy hO hSyl hone hz hnot2 with ⟨h7, -⟩ | ⟨F, hFfield, hFfin, L, hLn,
    hFodd, hLodd, ⟨eL⟩, h1, h3⟩
  · exact h7
  · exfalso
    have : L.Normal := hLn
    obtain ⟨p, f, hp, hpodd, hf, hFcard⟩ := hFodd
    have hqodd : Odd (Nat.card F) := hFcard ▸ hpodd.pow
    have hLcard : Nat.card L = Nat.card F * (Nat.card F ^ 2 - 1) / 2 :=
      (Nat.card_congr eL.toEquiv).trans (psl2_card_formula F ⟨p, f, hp, hpodd, hf, hFcard⟩)
    have hKX : 360 ∣ L.index * (Nat.card F * (Nat.card F ^ 2 - 1) / 2) := by
      rw [← hLcard, mul_comm, L.card_mul_index, ← hKcard]
      exact Subgroup.card_subgroup_dvd_card K
    obtain ⟨hidx, hq⟩ := gw56_arith_six hqodd hLodd (fun h => hC.symm.trans (h1 h))
      (fun h => hC.symm.trans (h3 h)) hKX
    let _ : Fintype F := Fintype.ofFinite F
    have hF9 : Fintype.card F = 9 := by rw [← Nat.card_eq_fintype_card, hq]
    obtain ⟨e6⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.unique_field_nine_projective_linear_alternating_six_isomorphism
        F hF9
    let eL6 : L ≃* alternatingGroup (Fin 6) := eL.trans e6
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have : IsSimpleGroup L := eL6.isSimpleGroup
    have hLc : Nat.card L = 360 := (Nat.card_congr eL6.toEquiv).trans gw56_card_alt_six
    obtain ⟨eP⟩ := CFSG.GH74.KGroups.A6.equiv_of_alt6 ⟨eL6⟩
    exact gw56_no_normal_simple_index_three (CFSG.pPrimeCore_eq_bot_iff.mp hO) L hLc hidx
      (CFSG.GH74.KGroups.A6.card_mulAut eP)

end CFSG.GH74.GLS.C3.Prop121
