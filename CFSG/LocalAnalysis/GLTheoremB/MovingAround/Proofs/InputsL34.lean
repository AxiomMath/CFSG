module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims11x
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1245
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L34Idx
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts3
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs2
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims126
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input236gt

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem card_mulAut_of_isLThreeFour {X : Type} [Group X] (hX : IsLThreeFour X) :
    Nat.card (MulAut X) = 241920 := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  rw [Nat.card_congr (MulAut.congr φ).toEquiv]
  exact CFSG.RankThree.PartTwo.KFacts.L34.card_mulAut hk

theorem inputAutL34Order27_holds : Claims11x.InputAutL34Order27 := by
  intro X _ hX P hP
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := card_mulAut_of_isLThreeFour hX
  haveI : Finite (MulAut X) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : Nat.card P ∣ 241920 := hcard ▸ Subgroup.card_subgroup_dvd_card P
  rw [hn] at hdvd ⊢
  have hn3 : n ≤ 3 := by
    by_contra h
    have h4 : 3 ^ 4 ∣ 3 ^ n := Nat.pow_dvd_pow 3 (by omega)
    have := h4.trans hdvd
    norm_num at this
  calc 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) hn3
    _ = 27 := by norm_num

section AbelianSylow

open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

theorem sylow_inf_center_eq_bot {p : ℕ} [hp : Fact p.Prime] (S : Sylow p G)
    (hSab : ∀ x y : (S : Subgroup G), x * y = y * x) (hperf : commutator G = ⊤) :
    (S : Subgroup G) ⊓ Subgroup.center G = ⊥ := by
  set N := Subgroup.normalizer ((S : Subgroup G) : Set G) with hNdef
  have hSN : (S : Subgroup G) ≤ N := Subgroup.le_normalizer
  set S' : Subgroup N := (S : Subgroup G).subgroupOf N with hS'def
  have hS'n : S'.Normal := Subgroup.normal_in_normalizer
  have hS'card : Nat.card S' = Nat.card (S : Subgroup G) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSN).toEquiv
  have hS'idx : ¬ p ∣ S'.index := fun h =>
    S.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le hSN))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp S.isPGroup'
  have hcop : (Nat.card S').Coprime S'.index := by
    rw [hS'card, hk]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hS'idx)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set H : Subgroup G := K.map N.subtype with hHdef
  have hHN : H ≤ N := Subgroup.map_subtype_le K
  have hHcard : Nat.card H = S'.index := by
    rw [hHdef, Subgroup.card_map_of_injective N.subtype_injective]
    exact hK.symm.index_eq_card.symm
  have hHp : ¬ p ∣ Nat.card H := by
    rw [hHcard]
    exact hS'idx
  have hdecomp : ∀ n ∈ N, ∃ s ∈ (S : Subgroup G), ∃ h ∈ H, s * h = n := by
    intro n hn
    obtain ⟨⟨s, h⟩, hsh⟩ := (hK.existsUnique ⟨n, hn⟩).exists
    exact ⟨s, Subgroup.mem_subgroupOf.mp s.2, h, ⟨h, h.2, rfl⟩, congrArg Subtype.val hsh⟩
  have hfus : ∀ x ∈ (S : Subgroup G), ∀ g : G, g⁻¹ * x * g ∈ (S : Subgroup G) →
      ∃ h ∈ H, g⁻¹ * x * g = h⁻¹ * x * h := by
    intro x hx g hg
    haveI : IsMulCommutative (S : Subgroup G) := ⟨⟨hSab⟩⟩
    obtain ⟨n, hn, hgn⟩ := Sylow.conj_eq_normalizer_conj_of_mem S x g hx hg
    obtain ⟨s, hs, h, hh, rfl⟩ := hdecomp n hn
    refine ⟨h, hh, ?_⟩
    have hxs : x * s = s * x := congrArg Subtype.val (hSab ⟨x, hx⟩ ⟨s, hs⟩)
    rw [hgn]
    calc (s * h)⁻¹ * x * (s * h) = h⁻¹ * (s⁻¹ * (x * s)) * h := by group
      _ = h⁻¹ * x * h := by rw [hxs, inv_mul_cancel_left]
  have hfocal : (S : Subgroup G) ⊓ commutator G ≤ ⁅(S : Subgroup G), H⁆ := by
    have h := CFSG.sylow_inf_derivedSubgroup_eq_focalSubgroup p S
    rw [CFSG.derivedSubgroup, derivedSeries_one] at h
    rw [h, Subgroup.closure_le]
    rintro z ⟨x, hx, y, hy, hxy, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    have hy' : c⁻¹⁻¹ * x * c⁻¹ = y := by rw [inv_inv]; exact hc
    obtain ⟨h, hh, hxh⟩ := hfus x hx c⁻¹ (by rw [hy']; exact hy)
    rw [← hy', hxh]
    have he : x⁻¹ * (h⁻¹ * x * h) = ⁅x⁻¹, h⁻¹⁆ := by
      rw [commutatorElement_def, inv_inv, inv_inv]
      group
    rw [he]
    exact Subgroup.commutator_mem_commutator ((S : Subgroup G).inv_mem hx) (H.inv_mem hh)
  have hcopHS : Nat.Coprime (Nat.card H) (Nat.card (S : Subgroup G)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hHp).symm
  obtain ⟨-, hddisj⟩ :=
    CFSG.QuasithinUnique.Setup.Layer.coprime_abelian_decomp (S : Subgroup G) H hHN hSab hcopHS
  rw [eq_bot_iff]
  intro z hz
  have hzS : z ∈ (S : Subgroup G) := hz.1
  have hzc : z ∈ ⁅(S : Subgroup G), H⁆ := hfocal ⟨hzS, by rw [hperf]; exact Subgroup.mem_top z⟩
  have hzC : z ∈ (S : Subgroup G) ⊓ Subgroup.centralizer (H : Set G) :=
    ⟨hzS, Subgroup.mem_centralizer_iff.2 fun h _ => Subgroup.mem_center_iff.1 hz.2 h⟩
  exact Subgroup.mem_bot.2 (Subgroup.disjoint_def.1 hddisj hzC hzc)

end AbelianSylow

section L34Facts

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

theorem card_of_isLThreeFour {X : Type} [Group X] (hX : IsLThreeFour X) : Nat.card X = 20160 :=
  CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hX

theorem finite_of_isLThreeFour {X : Type} [Group X] (hX : IsLThreeFour X) : Finite X :=
  Nat.finite_of_card_ne_zero (by rw [card_of_isLThreeFour hX]; norm_num)

theorem card_sylow_of_isLThreeFour {X : Type} [Group X] [Finite X] (hX : IsLThreeFour X)
    (S : Sylow 3 X) : Nat.card S = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [Sylow.card_eq_multiplicity, card_of_isLThreeFour hX,
    CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 20160 = 3 ^ 2 * 2240 by norm_num) (by norm_num)]
  norm_num

theorem commute_of_card_nine {X : Type} [Group X] {E : Subgroup X} (hE : Nat.card E = 9) {x y : X}
    (hx : x ∈ E) (hy : y ∈ E) : x * y = y * x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h := (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥E)
    (by rw [hE]; norm_num)).is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val h

theorem pow_three_of_card_nine {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {x : X} (hx : x ∈ E) : x ^ 3 = 1 := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have hE' : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE]
  obtain ⟨g, hg⟩ := exists_eq_map_conj_eZero hk hE'
  have hφx : φ x ∈ (eZero k).map (MulAut.conj g).toMonoidHom := hg ▸ ⟨x, hx, rfl⟩
  obtain ⟨e, he, hex⟩ := hφx
  have h3 : (φ x) ^ 3 = 1 := by
    rw [← hex, MulEquiv.coe_toMonoidHom, ← map_pow, pow_three_of_mem_eZero hk he, map_one]
  apply φ.injective
  rw [map_pow, h3, map_one]

theorem pow_three_of_isPGroup {X : Type} [Group X] (hX : IsLThreeFour X) {x : X}
    (hx : IsPGroup 3 (Subgroup.zpowers x)) : x ^ 3 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  obtain ⟨S, hS⟩ := hx.exists_le_sylow
  exact pow_three_of_card_nine hX (card_sylow_of_isLThreeFour hX S) (hS (Subgroup.mem_zpowers x))

theorem exists_eq_conj_of_fixes_proj {k : Type} [Field k] (hk : Nat.card k = 4)
    {E : Subgroup (projectiveSL 3 k)} (hE : Nat.card E = 9) {α : MulAut (projectiveSL 3 k)}
    (hα : α ^ 3 = 1) (hfix : ∀ x ∈ E, α x = x) : ∃ e ∈ E, α = MulAut.conj e := by
  have := LinearFieldFour.finite_of_card_eq_four hk
  have := LinearFieldFour.charP_two_of_card_eq_four hk
  have hσ : ∀ a, frobeniusEquiv k 2 a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨g, rfl⟩ := exists_eq_map_conj_eZero hk hE
  set c : MulAut (projectiveSL 3 k) := MulAut.conj g with hc
  set α' : MulAut (projectiveSL 3 k) := c⁻¹ * α * c with hα'
  have hfix' : ∀ x ∈ eZero k, α' x = x := by
    intro x hx
    have h1 := hfix (c x) ⟨x, hx, rfl⟩
    rw [hα', MulAut.mul_apply, MulAut.mul_apply, h1, MulAut.inv_apply, c.symm_apply_apply]
  have hα'3 : α' ^ 3 = 1 := by
    rw [hα', show (c⁻¹ * α * c) ^ 3 = c⁻¹ * α ^ 3 * c by rw [pow_three, pow_three]; group, hα]
    group
  have hαeq : α = c * α' * c⁻¹ := by rw [hα']; group
  obtain ⟨e, he, h | h⟩ := (forall_fixes_eZero_iff hk hσ α').1 hfix'
  · refine ⟨c e, ⟨e, he, rfl⟩, ?_⟩
    rw [hαeq, h, hc, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · exfalso
    have hcomm : Commute (MulAut.conj e) (betaAut (frobeniusEquiv k 2)) := by
      have hb := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv
        (betaAut (frobeniusEquiv k 2)) e
      rw [betaAut_fixed hk hσ he] at hb
      calc MulAut.conj e * betaAut (frobeniusEquiv k 2) =
            betaAut (frobeniusEquiv k 2) * MulAut.conj e * (betaAut (frobeniusEquiv k 2))⁻¹ *
              betaAut (frobeniusEquiv k 2) := by rw [hb]
        _ = betaAut (frobeniusEquiv k 2) * MulAut.conj e := by group
    have h3 := hα'3
    rw [h, hcomm.mul_pow, ← map_pow, pow_three_of_mem_eZero hk he, map_one, one_mul, pow_three,
      betaAut_mul_self hk hσ, mul_one] at h3
    exact betaAut_ne_one hk h3

theorem exists_eq_conj_of_fixes {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {α : MulAut X} (hα : α ^ 3 = 1) (hfix : ∀ x ∈ E, α x = x) :
    ∃ e ∈ E, α = MulAut.conj e := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  set α' := MulAut.congr φ α with hα'
  have hα'3 : α' ^ 3 = 1 := by rw [hα', ← map_pow, hα, map_one]
  have hE' : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE]
  have hfix' : ∀ x ∈ E.map φ.toMonoidHom, α' x = x := by
    rintro _ ⟨x, hx, rfl⟩
    change φ (α (φ.symm (φ x))) = φ x
    rw [φ.symm_apply_apply, hfix x hx]
  obtain ⟨_, ⟨x, hx, rfl⟩, he⟩ := exists_eq_conj_of_fixes_proj hk hE' hα'3 hfix'
  refine ⟨x, hx, ?_⟩
  ext y
  have h1 := congrArg (fun β : MulAut (projectiveSL 3 k) => β (φ y)) he
  change φ (α (φ.symm (φ y))) = MulAut.conj (φ x) (φ y) at h1
  rw [φ.symm_apply_apply, MulAut.conj_apply] at h1
  apply φ.injective
  rw [h1, MulAut.conj_apply, map_mul, map_mul, map_inv]

end L34Facts

section SylowCent

open CFSG.LocalAnalysis.GLTheoremB (quotientCenterAut' quotientCenterAut'_injective)

theorem quotientCenterAut'_mk {Y : Type*} [Group Y] (φ : MulAut Y) (y : Y) :
    quotientCenterAut' Y φ (QuotientGroup.mk y) = QuotientGroup.mk (φ y) := rfl

theorem quotientCenterAut'_conj {Y : Type*} [Group Y] (y : Y) :
    quotientCenterAut' Y (MulAut.conj y) = MulAut.conj (QuotientGroup.mk y) := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H x =>
    rw [quotientCenterAut'_mk, MulAut.conj_apply, MulAut.conj_apply]
    rfl

theorem inputSL34SylowCent_holds : Claims1245.InputSL34SylowCent := by
  intro Y _ _ hq hO hL hZ φ hφ P hfix
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hperf : commutator Y = ⊤ := hq.1
  set π : Y →* Y ⧸ Subgroup.center Y := QuotientGroup.mk' (Subgroup.center Y) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set Pbar : Sylow 3 (Y ⧸ Subgroup.center Y) := P.mapSurjective hπsurj with hPbar
  have hPbar9 : Nat.card (Pbar : Subgroup (Y ⧸ Subgroup.center Y)) = 9 :=
    card_sylow_of_isLThreeFour hL Pbar
  have hφbar3 : quotientCenterAut' Y φ ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
  have hfixbar : ∀ x ∈ (Pbar : Subgroup (Y ⧸ Subgroup.center Y)), quotientCenterAut' Y φ x = x := by
    intro x hx
    rw [hPbar, Sylow.coe_mapSurjective] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [hπ, QuotientGroup.mk'_apply, quotientCenterAut'_mk, hfix y hy]
  obtain ⟨_, hebar, hφe⟩ := exists_eq_conj_of_fixes hL hPbar9 hφbar3 hfixbar
  have hebar' := hebar
  rw [hPbar, Sylow.coe_mapSurjective] at hebar'
  obtain ⟨y, hyP, rfl⟩ := hebar'
  have hφy : φ = MulAut.conj y := by
    apply quotientCenterAut'_injective hperf
    rw [hφe, quotientCenterAut'_conj, hπ, QuotientGroup.mk'_apply]
  have hyc : ∀ x ∈ (P : Subgroup Y), y * x = x * y := by
    intro x hx
    have h1 := hfix x hx
    rw [hφy, MulAut.conj_apply] at h1
    calc y * x = y * x * y⁻¹ * y := by group
      _ = x * y := by rw [h1]
  by_cases hyZ : y ∈ Subgroup.center Y
  · rw [hφy]
    ext x
    rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.1 hyZ x).symm,
      mul_inv_cancel_right]
  · exfalso
    set yb : ↥(Pbar : Subgroup (Y ⧸ Subgroup.center Y)) := ⟨π y, hebar⟩ with hyb
    have hyb1 : yb ≠ 1 := by
      intro h
      apply hyZ
      have h1 : π y = 1 := congrArg Subtype.val h
      rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hyb3 : yb ^ 3 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact pow_three_of_card_nine hL hPbar9 hebar)
    have hPbarab : ∀ a b : ↥(Pbar : Subgroup (Y ⧸ Subgroup.center Y)), a * b = b * a := fun a b =>
      Subtype.ext (commute_of_card_nine hPbar9 a.2 b.2)
    haveI : (Subgroup.zpowers yb).Normal :=
      ⟨fun n hn g => by rw [hPbarab g n, mul_inv_cancel_right]; exact hn⟩
    have hcardz : Nat.card (Subgroup.zpowers yb) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hyb3 hyb1]
    have hcardq : Nat.card (↥(Pbar : Subgroup (Y ⧸ Subgroup.center Y)) ⧸ Subgroup.zpowers yb) ∣ 3 := by
      have h1 := Subgroup.card_mul_index (Subgroup.zpowers yb)
      rw [hcardz, hPbar9] at h1
      rw [← Subgroup.index_eq_card]
      exact ⟨1, by omega⟩
    haveI : IsCyclic (↥(Pbar : Subgroup (Y ⧸ Subgroup.center Y)) ⧸ Subgroup.zpowers yb) :=
      isCyclic_of_card_dvd_prime (p := 3) hcardq
    let f₀ : ↥(P : Subgroup Y) →* ↥(Pbar : Subgroup (Y ⧸ Subgroup.center Y)) :=
      π.subgroupMap (P : Subgroup Y)
    let f := (QuotientGroup.mk' (Subgroup.zpowers yb)).comp f₀
    have hker : f.ker ≤ Subgroup.center ↥(P : Subgroup Y) := by
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hx
      have hi' : π (y ^ i) = π (x : Y) := by
        rw [map_zpow]
        exact congrArg Subtype.val hi
      have hz : (y ^ i)⁻¹ * (x : Y) ∈ Subgroup.center Y := by
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hi'
        exact hi'
      have hxe : (x : Y) = y ^ i * ((y ^ i)⁻¹ * (x : Y)) := by group
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hxe]
      have hwy : (w : Y) * y ^ i = y ^ i * (w : Y) :=
        ((show Commute y (w : Y) from hyc w w.2).zpow_left i).eq.symm
      calc (w : Y) * (y ^ i * ((y ^ i)⁻¹ * (x : Y))) = y ^ i * ((w : Y) * ((y ^ i)⁻¹ * (x : Y))) := by
            rw [← mul_assoc, hwy, mul_assoc]
        _ = y ^ i * ((y ^ i)⁻¹ * (x : Y)) * (w : Y) := by
            rw [Subgroup.mem_center_iff.1 hz (w : Y)]
            group
    have hPab : ∀ a b : ↥(P : Subgroup Y), a * b = b * a :=
      (f.isMulCommutative_of_isCyclic_of_ker_le_center hker).is_comm.comm
    have hZ3 : IsPGroup 3 ↥(Subgroup.center Y) :=
      AltFacts2.isPGroup_center_of_core_eq_bot Nat.prime_three hO
    have hZP : Subgroup.center Y ≤ (P : Subgroup Y) := hZ3.le_sylow_of_normal P
    have hbot := sylow_inf_center_eq_bot P hPab hperf
    rw [inf_eq_right.2 hZP] at hbot
    exact hZ hbot

end SylowCent

section Fix3

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34 CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedScalars)

theorem twoFixed_of_card_nine {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {φ : MulAut X} (hfix : ∀ x ∈ E, φ x = x) :
    ∃ w₁ w₂ : X, orderOf w₁ = 3 ∧ orderOf w₂ = 3 ∧ φ w₁ = w₁ ∧ φ w₂ = w₂ ∧
      w₂ ∉ Subgroup.zpowers w₁ := by
  haveI := finite_of_isLThreeFour hX
  have hEne : E ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hE
    norm_num at hE
  obtain ⟨w₁, hw₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEne
  have hw₁ : orderOf (w₁ : X) = 3 :=
    orderOf_eq_prime (pow_three_of_card_nine hX hE w₁.2) (fun h => hw₁1 (Subtype.ext h))
  have hex : ∃ w₂ ∈ E, w₂ ∉ Subgroup.zpowers (w₁ : X) := by
    by_contra h
    push Not at h
    have hle : E ≤ Subgroup.zpowers (w₁ : X) := h
    have := Subgroup.card_le_of_le hle
    rw [hE, Nat.card_zpowers, hw₁] at this
    norm_num at this
  obtain ⟨w₂, hw₂E, hw₂⟩ := hex
  have hw₂1 : w₂ ≠ 1 := fun h => hw₂ (h ▸ Subgroup.one_mem _)
  exact ⟨(w₁ : X), w₂, hw₁, orderOf_eq_prime (pow_three_of_card_nine hX hE hw₂E) hw₂1,
    hfix _ w₁.2, hfix _ hw₂E, hw₂⟩

theorem twoFixed_of_inner {X : Type} [Group X] (hX : IsLThreeFour X) {t : X} (ht : t ^ 3 = 1) :
    ∃ w₁ w₂ : X, orderOf w₁ = 3 ∧ orderOf w₂ = 3 ∧ MulAut.conj t w₁ = w₁ ∧
      MulAut.conj t w₂ = w₂ ∧ w₂ ∉ Subgroup.zpowers w₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  have ht3 : IsPGroup 3 (Subgroup.zpowers t) := by
    rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one ht) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  obtain ⟨S, hS⟩ := ht3.exists_le_sylow
  have hS9 := card_sylow_of_isLThreeFour hX S
  have htS : t ∈ (S : Subgroup X) := hS (Subgroup.mem_zpowers t)
  refine twoFixed_of_card_nine hX hS9 (fun x hx => ?_)
  rw [MulAut.conj_apply, commute_of_card_nine hS9 htS hx, mul_inv_cancel_right]

theorem twoFixed_of_conj {X : Type} [Group X] (hX : IsLThreeFour X) {φ : MulAut X} {w c : X}
    (hw : orderOf w = 3) (hwφ : φ w = w) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3)
    (hc : orderOf c = r) (hcφ : φ c = c) :
    ∃ w₁ w₂ : X, orderOf w₁ = 3 ∧ orderOf w₂ = 3 ∧ φ w₁ = w₁ ∧ φ w₂ = w₂ ∧
      w₂ ∉ Subgroup.zpowers w₁ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  refine ⟨w, c * w * c⁻¹, hw, ?_, hwφ, ?_, ?_⟩
  · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hw]
  · rw [map_mul, map_mul, map_inv, hwφ, hcφ]
  · intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hw1 : w ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hw
      norm_num at hw
    have h3i : ¬ (3 : ℤ) ∣ i := by
      rintro ⟨j, rfl⟩
      apply hw1
      have hw3 : w ^ 3 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
      have hw3' : w ^ (3 : ℤ) = 1 := by exact_mod_cast hw3
      have h1 : c * w * c⁻¹ = 1 := by
        rw [← hi, zpow_mul, hw3', one_zpow]
      calc w = c⁻¹ * (c * w * c⁻¹) * c := by group
        _ = 1 := by rw [h1]; group
    have hii : w ^ (i * i) = w := by
      rw [← zpow_mod_orderOf, hw]
      have h1 : i % 3 = 1 ∨ i % 3 = 2 := by omega
      have h2 : (i * i) % ((3 : ℕ) : ℤ) = 1 := by
        rw [show ((3 : ℕ) : ℤ) = 3 by norm_num, Int.mul_emod]
        rcases h1 with h1 | h1 <;> rw [h1] <;> norm_num
      rw [h2, zpow_one]
    have h2 : c ^ 2 * w * (c ^ 2)⁻¹ = w := by
      calc c ^ 2 * w * (c ^ 2)⁻¹ = (MulAut.conj c) ((MulAut.conj c) w) := by
            rw [MulAut.conj_apply, MulAut.conj_apply, sq]; group
        _ = w ^ (i * i) := by
            rw [MulAut.conj_apply c w, ← hi, map_zpow, MulAut.conj_apply, ← hi, ← zpow_mul]
        _ = w := hii
    have hcw : c ^ 2 * w = w * c ^ 2 := by
      calc c ^ 2 * w = c ^ 2 * w * (c ^ 2)⁻¹ * c ^ 2 := by group
        _ = w * c ^ 2 := by rw [h2]
    have hw3 : IsPGroup 3 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw, pow_one])
    obtain ⟨S, hS⟩ := hw3.exists_le_sylow
    have hS9 := card_sylow_of_isLThreeFour hX S
    have hc2 : c ^ 2 ∈ (S : Subgroup X) :=
      Inputs1114.l34_mem_of_commute hX hS9 (hS (Subgroup.mem_zpowers w)) hw1 hcw
    have h6 : c ^ 6 = 1 := by
      rw [show 6 = 2 * 3 by norm_num, pow_mul, pow_three_of_card_nine hX hS9 hc2]
    have hr6 : r ∣ 2 * 3 := hc ▸ orderOf_dvd_of_pow_eq_one h6
    rcases (Nat.Prime.dvd_mul hr).1 hr6 with h | h
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h)
    · exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h)

theorem isLThreeFour_projectiveSL {k : Type} [Field k] (hk : Nat.card k = 4) :
    IsLThreeFour (projectiveSL 3 k) := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  exact ⟨k, inferInstance, inferInstance, hk,
    ⟨(CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 k).symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 k)⟩⟩

theorem conjAut_fix_of_mem_centMod {k : Type} [Field k] (hk : Nat.card k = 4) {A z l : GL (Fin 3) k}
    (hz : z ∈ StatedScalars (Fin 3) k) (hl : l ∈ centMod (slPi true 3 (2 ^ 2) k) (A * z))
    {s : Matrix.SpecialLinearGroup (Fin 3) k} (hsl : Matrix.SpecialLinearGroup.toGL s = l) :
    conjAut 3 k A (proj 3 k s) = proj 3 k s := by
  obtain ⟨-, z', ⟨c', rfl⟩, hz'⟩ := mem_centMod_iff_scalar.1 hl
  obtain ⟨c, rfl⟩ := hz
  set Zc := Matrix.GeneralLinearGroup.scalar (Fin 3) c with hZc
  set Zc' := Matrix.GeneralLinearGroup.scalar (Fin 3) c' with hZc'
  have hlc : l * Zc⁻¹ * l⁻¹ = Zc⁻¹ := by
    rw [((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c l).inv_right).eq, mul_inv_cancel_right]
  have key0 : l * A * l⁻¹ = Zc' * A := by
    calc l * A * l⁻¹ = l * (A * Zc) * l⁻¹ * (l * Zc⁻¹ * l⁻¹) := by group
      _ = Zc' * (A * Zc) * (l * Zc⁻¹ * l⁻¹) := by rw [hz']
      _ = Zc' * A := by rw [hlc]; group
  have key : A * l * A⁻¹ = l * Zc'⁻¹ := by
    calc A * l * A⁻¹ = Zc'⁻¹ * (Zc' * A) * l * A⁻¹ := by group
      _ = Zc'⁻¹ * (l * A * l⁻¹) * l * A⁻¹ := by rw [key0]
      _ = Zc'⁻¹ * l := by group
      _ = l * Zc'⁻¹ := ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar c' l).inv_right).eq.symm
  have hc3 : (c'⁻¹) ^ 3 = 1 := Inputs1114.units_pow_three_of_card_four hk _
  have ha : CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 k A s =
      s * scalarElement c'⁻¹ hc3 := by
    apply Subtype.ext
    rw [coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul, coe_scalarElement]
    have h1 := congrArg (fun g : GL (Fin 3) k => (g : Matrix (Fin 3) (Fin 3) k)) key
    simp only [Units.val_mul] at h1
    have hsv : ((Matrix.SpecialLinearGroup.toGL s : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        (s : Matrix (Fin 3) (Fin 3) k) := rfl
    rw [← hsl, hsv] at h1
    rw [h1, hZc', ← map_inv, Matrix.GeneralLinearGroup.coe_scalar]
  rw [conjAut_proj, ha, map_mul, proj_eq_one_iff.2 (scalarElement_mem_scalars _ hc3), mul_one]

theorem scalar_of_proj_eq_one {k : Type} [Field k] {s : Matrix.SpecialLinearGroup (Fin 3) k}
    (hs : proj 3 k s = 1) :
    Matrix.SpecialLinearGroup.toGL s ∈ StatedScalars (Fin 3) k ∧ s ^ 3 = 1 := by
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hs)
  refine ⟨⟨c, Units.ext ?_⟩, ?_⟩
  · rw [Matrix.GeneralLinearGroup.coe_scalar]
    exact hc.symm
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow, ← Units.val_pow_eq_pow_val, hc3,
      Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem fixed_of_prime {k : Type} [Field k] (hk : Nat.card k = 4) {A z l : GL (Fin 3) k}
    (hz : z ∈ StatedScalars (Fin 3) k) (hl : l ∈ centMod (slPi true 3 (2 ^ 2) k) (A * z)) {r : ℕ}
    (hr : r.Prime) (hr3 : r ≠ 3) (hlr : orderOf l = r) :
    ∃ c : projectiveSL 3 k, orderOf c = r ∧ conjAut 3 k A c = c := by
  have hlL : l ∈ slPi true 3 (2 ^ 2) k := (Subgroup.mem_inf.1 hl).1
  set s : Matrix.SpecialLinearGroup (Fin 3) k := ⟨l, (mem_slPi_true _).1 hlL⟩ with hsdef
  have hsl : Matrix.SpecialLinearGroup.toGL s = l := Units.ext rfl
  refine ⟨proj 3 k s, ?_, conjAut_fix_of_mem_centMod hk hz hl hsl⟩
  have hsr : s ^ r = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, hsl, map_one, ← hlr, pow_orderOf_eq_one]
  haveI : Fact r.Prime := ⟨hr⟩
  refine orderOf_eq_prime (by rw [← map_pow, hsr, map_one]) (fun h1 => ?_)
  obtain ⟨-, hs3⟩ := scalar_of_proj_eq_one h1
  have hs1 : s = 1 := by
    have h := orderOf_dvd_of_pow_eq_one hs3
    have h' := orderOf_dvd_of_pow_eq_one hsr
    have : orderOf s ∣ Nat.gcd 3 r := Nat.dvd_gcd h h'
    rw [(Nat.coprime_primes Nat.prime_three hr).2 (Ne.symm hr3)] at this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this)
  have hl1 : l = 1 := by rw [← hsl, hs1, map_one]
  rw [hl1, orderOf_one] at hlr
  exact hr.one_lt.ne hlr

theorem fixed_of_three {k : Type} [Field k] (hk : Nat.card k = 4) {A z l : GL (Fin 3) k}
    (hz : z ∈ StatedScalars (Fin 3) k) (hl : l ∈ centMod (slPi true 3 (2 ^ 2) k) (A * z))
    (hl3 : l ^ 3 = 1) (hls : l ∉ StatedScalars (Fin 3) k) :
    ∃ w : projectiveSL 3 k, orderOf w = 3 ∧ conjAut 3 k A w = w := by
  have hlL : l ∈ slPi true 3 (2 ^ 2) k := (Subgroup.mem_inf.1 hl).1
  set s : Matrix.SpecialLinearGroup (Fin 3) k := ⟨l, (mem_slPi_true _).1 hlL⟩ with hsdef
  have hsl : Matrix.SpecialLinearGroup.toGL s = l := Units.ext rfl
  refine ⟨proj 3 k s, ?_, conjAut_fix_of_mem_centMod hk hz hl hsl⟩
  have hs3 : s ^ 3 = 1 := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    rw [map_pow, hsl, map_one, hl3]
  refine orderOf_eq_prime (by rw [← map_pow, hs3, map_one]) (fun h1 => hls ?_)
  rw [← hsl]
  exact (scalar_of_proj_eq_one h1).1

theorem fixed_of_nine {k : Type} [Field k] (hk : Nat.card k = 4) {A z : GL (Fin 3) k}
    (hz : z ∈ StatedScalars (Fin 3) k) {M : Subgroup (GL (Fin 3) k)}
    (hM : M ≤ centMod (slPi true 3 (2 ^ 2) k) (A * z)) (hM9 : Nat.card M = 9) :
    ∃ w : projectiveSL 3 k, orderOf w = 3 ∧ conjAut 3 k A w = w := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := isLThreeFour_projectiveSL hk
  have hsc : Nat.card (StatedScalars (Fin 3) k) ≤ 3 := by
    have h1 : Nat.card ((Matrix.GeneralLinearGroup.scalar (Fin 3) : kˣ →* GL (Fin 3) k).range) ≤
        Nat.card kˣ :=
      Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    rw [Nat.card_units, hk] at h1
    exact h1
  have hex : ∃ l ∈ M, l ∉ StatedScalars (Fin 3) k := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (show M ≤ StatedScalars (Fin 3) k from h)
    omega
  obtain ⟨l, hlM, hls⟩ := hex
  have hl9 : l ^ 9 = 1 := by
    have := pow_card_eq_one' (G := ↥M) (x := ⟨l, hlM⟩)
    rw [hM9] at this
    exact congrArg Subtype.val this
  have hlL : l ∈ slPi true 3 (2 ^ 2) k := (Subgroup.mem_inf.1 (hM hlM)).1
  set s : Matrix.SpecialLinearGroup (Fin 3) k := ⟨l, (mem_slPi_true _).1 hlL⟩ with hsdef
  have hsl : Matrix.SpecialLinearGroup.toGL s = l := Units.ext rfl
  refine ⟨proj 3 k s, ?_, conjAut_fix_of_mem_centMod hk hz (hM hlM) hsl⟩
  have hs9 : (proj 3 k s) ^ (3 ^ 2) = 1 := by
    rw [← map_pow]
    have : s ^ (3 ^ 2) = 1 := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [map_pow, hsl, map_one]
      exact hl9
    rw [this, map_one]
  have hp : IsPGroup 3 (Subgroup.zpowers (proj 3 k s)) := by
    intro g
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 g.2
    refine ⟨2, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hs9,
      one_zpow, Subgroup.coe_one]
  refine orderOf_eq_prime (pow_three_of_isPGroup hX hp) (fun h1 => hls ?_)
  rw [← hsl]
  exact (scalar_of_proj_eq_one h1).1

theorem twoFixed_proj {k : Type} [Field k] (hk : Nat.card k = 4) {φ : MulAut (projectiveSL 3 k)}
    (hφ : φ ^ 3 = 1) :
    ∃ w₁ w₂ : projectiveSL 3 k, orderOf w₁ = 3 ∧ orderOf w₂ = 3 ∧ φ w₁ = w₁ ∧ φ w₂ = w₂ ∧
      w₂ ∉ Subgroup.zpowers w₁ := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hX := isLThreeFour_projectiveSL hk
  have hlin : φ ∈ linearAutGroup 3 k := by
    by_contra hD
    obtain ⟨σ, hσ, -⟩ := CFSG.RankThree.PartTwo.KFacts.linear_order_three_field_descent
      (n := 3) le_rfl φ hφ hD
    have := (CFSG.RankThree.PartTwo.KFacts.eq_frobenius_pow_of_orderOf_eq_three
      (p := 2) (f := 2) Nat.prime_two (by norm_num) (by rw [hk]; norm_num) hσ).1
    omega
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.1 hlin
  by_cases hAs : A ∈ StatedScalars (Fin 3) k
  · obtain ⟨c, rfl⟩ := hAs
    exact twoFixed_of_card_nine hX (card_eZero hk) (fun x _ => by
      rw [conjAut_scalar c, MulAut.one_apply])
  have hA3 : A ^ 3 ∈ StatedScalars (Fin 3) k := by
    have h : conjAut 3 k (A ^ 3) = 1 := by rw [map_pow, hφ]
    obtain ⟨-, c, hc⟩ := eq_one_of_conjAut_mul_fieldAut_eq_one (n := 3) le_rfl (A ^ 3) 1
      (by rw [map_one, mul_one, h])
    exact ⟨c, hc⟩
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  have hu3 : (u : k) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, Inputs1114.units_pow_three_of_card_four hk u, Units.val_one]
  have hτ1 : (u : k) ≠ 1 := val_ne_one hu
  have hK : PiField true 2 2 k := ⟨Nat.prime_two, by norm_num, by rw [hk]; rfl⟩
  have hq : ModThree true (2 ^ 2) := by change 2 ^ 2 % 3 = 1; norm_num
  have hπ : true = false → UnitaryFieldData 2 2 k := fun h => absurd h (by decide)
  have hπ' : true = false → ModThree false (2 ^ 2) := fun h => absurd h (by decide)
  have hzPi : zPi true 3 (2 ^ 2) k = glPi true 3 (2 ^ 2) k ⊓ StatedScalars (Fin 3) k :=
    zPi_eq hπ hπ' hu3 hτ1
  have hxZ : A ∉ zPi true 3 (2 ^ 2) k := by rw [hzPi]; exact fun h => hAs h.2
  have hx3 : A ^ 3 ∈ zPi true 3 (2 ^ 2) k := by rw [hzPi]; exact ⟨mem_glPi_true _ _, hA3⟩
  obtain ⟨y, ⟨z, hz, rfl⟩, hcase⟩ := rank3II_4_10_one hK hq hu3 hτ1 (mem_glPi_true _ A) hxZ hx3
  have hzs : z ∈ StatedScalars (Fin 3) k := by rw [hzPi] at hz; exact hz.2
  have hAz : conjAut 3 k (A * z) = conjAut 3 k A := by
    obtain ⟨c, rfl⟩ := hzs
    rw [map_mul, conjAut_scalar, mul_one]
  rcases hcase with ⟨⟨g, hg, hgy⟩, -, -⟩ | ⟨-, ⟨e⟩, -⟩ | ⟨-, -, -, -, hcard, w, hwL, hw3, hwC, hcm, -⟩
  ·
    have hyL : A * z ∈ slPi true 3 (2 ^ 2) k := by
      rw [eq_conj_of_inv_conj hgy]
      exact conj_mem_slPi hπ hg (diagTau_mem_slPi hπ hπ' hu3)
    set s : Matrix.SpecialLinearGroup (Fin 3) k := ⟨A * z, (mem_slPi_true _).1 hyL⟩ with hsdef
    have hsl : Matrix.SpecialLinearGroup.toGL s = A * z := Units.ext rfl
    have hφt : conjAut 3 k A = MulAut.conj (proj 3 k s) := by
      rw [← hAz, ← hsl, conjAut_toGL]
    have ht3 : proj 3 k s ^ 3 = 1 := by
      apply conj_injective hk
      rw [map_pow, ← hφt, hφ, map_one]
    rw [hφt]
    exact twoFixed_of_inner hX ht3
  ·
    set C := slPi true 3 (2 ^ 2) k ⊓ Subgroup.centralizer {A * z} with hC
    have hCc : C ≤ centMod (slPi true 3 (2 ^ 2) k) (A * z) := centralizer_le_centMod _ _
    haveI : Fintype k := Fintype.ofFinite k
    have hk' : Fintype.card k = 4 := by rw [← Nat.card_eq_fintype_card, hk]
    have h180 : Nat.card C = 180 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (⊤ : Subgroup (GL (Fin 2) k)) = 180
      rw [Subgroup.card_top, Matrix.card_GL_field, hk', Fin.prod_univ_two]
      norm_num
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 5 (by rw [h180]; norm_num)
    obtain ⟨c, hc, hcφ⟩ := fixed_of_prime hk hzs (hCc c₀.2) (r := 5) (by norm_num) (by norm_num)
      (by rw [Subgroup.orderOf_coe, hc₀])
    obtain ⟨S, hS⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥C) 3 (n := 2)
      (by rw [h180]; norm_num)
    obtain ⟨w', hw', hwφ⟩ := fixed_of_nine hk hzs (M := S.map C.subtype)
      ((Subgroup.map_subtype_le S).trans hCc)
      (by rw [Subgroup.card_map_of_injective C.subtype_injective, hS]; norm_num)
    exact twoFixed_of_conj hX hw' hwφ (by norm_num) (by norm_num) (by norm_num) hc hcφ
  ·
    set C := slPi true 3 (2 ^ 2) k ⊓ Subgroup.centralizer {A * z} with hC
    have hCc : C ≤ centMod (slPi true 3 (2 ^ 2) k) (A * z) := centralizer_le_centMod _ _
    have h21 : Nat.card C = 21 := by rw [hcard]; rfl
    haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨c₀, hc₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 7 (by rw [h21]; norm_num)
    obtain ⟨c, hc, hcφ⟩ := fixed_of_prime hk hzs (hCc c₀.2) (r := 7) (by norm_num) (by norm_num)
      (by rw [Subgroup.orderOf_coe, hc₀])
    have hwM : w ∈ centMod (slPi true 3 (2 ^ 2) k) (A * z) := by
      rw [hcm]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
    have hws : w ∉ StatedScalars (Fin 3) k := by
      rintro ⟨d, rfl⟩
      apply hwC
      refine Subgroup.mem_inf.2 ⟨hwL, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
      exact ((CFSG.ClassicalGroups.UnitaryFlag.commute_scalar d (A * z)).eq).symm
    have hw3' : w ^ 3 = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hw3] at this
    obtain ⟨w', hw', hwφ⟩ := fixed_of_three hk hzs hwM hw3' hws
    exact twoFixed_of_conj hX hw' hwφ (by norm_num) (by norm_num) (by norm_num) hc hcφ

theorem inputL34Fix3_holds : Claims1245.InputL34Fix3 := by
  intro Y _ _ hY φ hφ Z hZ
  obtain ⟨k, _, hk, ⟨e⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hY
  have hφ' : MulAut.congr e φ ^ 3 = 1 := by rw [← map_pow, hφ, map_one]
  obtain ⟨w₁, w₂, h₁, h₂, hf₁, hf₂, hne⟩ := twoFixed_proj hk hφ'
  have hfix : ∀ w : projectiveSL 3 k, MulAut.congr e φ w = w → φ (e.symm w) = e.symm w := by
    intro w hw
    have h1 : e (φ (e.symm w)) = w := hw
    have h2 := congrArg e.symm h1
    rwa [e.symm_apply_apply] at h2
  have hord : ∀ w : projectiveSL 3 k, orderOf (e.symm w) = orderOf w := fun w =>
    MulEquiv.orderOf_eq e.symm w
  by_cases h₁Z : e.symm w₁ ∈ Z
  · refine ⟨e.symm w₂, by rw [hord, h₂], hfix w₂ hf₂, fun h₂Z => hne ?_⟩
    have hZ1 : Subgroup.zpowers (e.symm w₁) = Z := by
      haveI : Finite (Subgroup.zpowers (e.symm w₁)) :=
        Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hord, h₁]; norm_num)
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 h₁Z) ?_
      rw [Nat.card_zpowers, hord, h₁]
      exact hZ
    rw [← hZ1] at h₂Z
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 h₂Z
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    apply e.symm.injective
    rw [map_zpow, hi]
  · exact ⟨e.symm w₁, by rw [hord, h₁], hfix w₁ hf₁, h₁Z⟩

end Fix3

section Max

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

theorem card_le_nine_of_isPGroup {X : Type} [Group X] (hX : IsLThreeFour X) {H : Subgroup X}
    (hH : IsPGroup 3 H) : Nat.card H ≤ 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  obtain ⟨S, hS⟩ := hH.exists_le_sylow
  exact (Subgroup.card_le_of_le hS).trans (card_sylow_of_isLThreeFour hX S).le

theorem card_normalizer_nine {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) : Nat.card (Subgroup.normalizer (E : Set X)) = 72 := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have hE' : Nat.card (E.map φ.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective φ.injective, hE]
  have h := card_normalizer_of_card_eq_nine hk hE'
  rw [← Subgroup.map_equiv_normalizer_eq, Subgroup.card_map_of_injective φ.injective] at h
  exact h

theorem mem_of_mem_normalizer {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {y : X} (hy : y ∈ Subgroup.normalizer (E : Set X))
    (hy3 : IsPGroup 3 (Subgroup.zpowers y)) : y ∈ E := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 2) (by rw [hE]; norm_num)
  have hsup : IsPGroup 3 ↥(Subgroup.zpowers y ⊔ E) :=
    IsPGroup.to_sup_of_normal_right' hy3 hE3 (Subgroup.zpowers_le.2 hy)
  have heq : E = Subgroup.zpowers y ⊔ E :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hE]; exact card_le_nine_of_isPGroup hX hsup)
  rw [heq]
  exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)

theorem pow_three_eq_zero_of_isNilpotent' {K : Type} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (hN : IsNilpotent N) : N ^ 3 = 0 := by
  have hcp := Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN
  have hcp' : N.charpoly = Polynomial.X ^ 3 := by
    have := hcp.eq_zero
    rwa [sub_eq_zero, Fintype.card_fin] at this
  have h := Matrix.aeval_self_charpoly N
  rw [hcp'] at h
  simpa using h

theorem pow_four_of_pow_eight_proj {k : Type} [Field k] (hk : Nat.card k = 4)
    {x : projectiveSL 3 k} (hx : x ^ 8 = 1) : x ^ 4 = 1 := by
  haveI := LinearFieldFour.finite_of_card_eq_four hk
  haveI := LinearFieldFour.charP_two_of_card_eq_four hk
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := proj_surjective 3 k x
  have hg8 : proj 3 k (g ^ 8) = 1 := by rw [map_pow, hx]
  obtain ⟨c, hc3, hc⟩ := mem_scalars.1 (proj_eq_one_iff.1 hg8)
  have hg24 : g ^ 24 = 1 := by
    apply Subtype.ext
    rw [show 24 = 8 * 3 by norm_num, pow_mul, Matrix.SpecialLinearGroup.coe_pow, hc,
      ← map_pow, ← Units.val_pow_eq_pow_val, hc3, Units.val_one, map_one,
      Matrix.SpecialLinearGroup.coe_one]
  set h := g ^ 3 with hh
  set H : Matrix (Fin 3) (Fin 3) k := (h : Matrix (Fin 3) (Fin 3) k) with hH
  have hH8 : H ^ 8 = 1 := by
    have : h ^ 8 = 1 := by rw [hh, ← pow_mul, hg24]
    have h1 := congrArg (fun s : Matrix.SpecialLinearGroup (Fin 3) k =>
      (s : Matrix (Fin 3) (Fin 3) k)) this
    simpa [Matrix.SpecialLinearGroup.coe_pow] using h1
  have hnil : IsNilpotent (H - 1) := by
    refine ⟨8, ?_⟩
    have := sub_pow_char_pow_of_commute (p := 2) (n := 3) (Commute.one_right H)
    rw [show (2 : ℕ) ^ 3 = 8 by norm_num, one_pow, hH8, sub_self] at this
    exact this
  have h3 := pow_three_eq_zero_of_isNilpotent' hnil
  have hH4 : H ^ 4 = 1 := by
    have := add_pow_char_pow_of_commute (p := 2) (n := 2) (Commute.one_right (H - 1))
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, sub_add_cancel, one_pow,
      show (H - 1) ^ 4 = (H - 1) ^ 3 * (H - 1) by rw [pow_succ], h3, zero_mul, zero_add] at this
    exact this
  have hh4 : h ^ 4 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hH, hH4, Matrix.SpecialLinearGroup.coe_one]
  have h12 : proj 3 k g ^ 12 = 1 := by
    rw [← map_pow, show 12 = 3 * 4 by norm_num, pow_mul, ← hh, hh4, map_one]
  calc proj 3 k g ^ 4 = proj 3 k g ^ 12 * (proj 3 k g ^ 8)⁻¹ := by group
    _ = 1 := by rw [h12, hx, inv_one, mul_one]

theorem pow_four_of_pow_eight {X : Type} [Group X] (hX : IsLThreeFour X) {x : X} (hx : x ^ 8 = 1) :
    x ^ 4 = 1 := by
  obtain ⟨k, _, hk, ⟨φ⟩⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_equiv_projectiveSL hX
  have h := pow_four_of_pow_eight_proj hk (x := φ x) (by rw [← map_pow, hx, map_one])
  apply φ.injective
  rw [map_pow, h, map_one]

end Max

section Ten

theorem card_dvd_of_free' {K Y : Type*} [Group K] [Finite K] [MulAction K Y] [Finite Y]
    (hfree : ∀ (k : K) (y : Y), k • y = y → k = 1) : Nat.card K ∣ Nat.card Y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fintype Y := Fintype.ofFinite Y
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    MulAction.card_eq_sum_card_group_div_card_stabilizer K Y]
  refine Finset.dvd_sum fun ω _ => ?_
  have hstab : Fintype.card (MulAction.stabilizer K ω.out) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨1, fun k => Subtype.ext ?_⟩
    exact hfree k ω.out (MulAction.mem_stabilizer_iff.mp k.2)
  rw [hstab, Nat.div_one]

theorem card_ne_point {Ω : Type*} [Finite Ω] (ω₀ : Ω) :
    Nat.card {ω : Ω // ω ≠ ω₀} = Nat.card Ω - 1 := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    Fintype.card_subtype_eq]

theorem card_ne_two_points {Ω : Type*} [Finite Ω] {ω₁ ω₂ : Ω} (h : ω₂ ≠ ω₁) :
    Nat.card {ω : Ω // ω ≠ ω₁ ∧ ω ≠ ω₂} = Nat.card Ω - 2 := by
  classical
  have : Fintype Ω := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : (Finset.univ.filter fun ω : Ω => ω ≠ ω₁ ∧ ω ≠ ω₂) = Finset.univ \ {ω₁, ω₂} := by
    ext ω
    simp
  rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
    Finset.card_pair h.symm]

theorem card_dvd_card_sub_one {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (ω₀ : Ω) (hfix : ∀ g : G, g • ω₀ = ω₀)
    (hfree : ∀ (g : G) (ω : Ω), ω ≠ ω₀ → g • ω = ω → g = 1) : Nat.card G ∣ Nat.card Ω - 1 := by
  letI : MulAction G {ω : Ω // ω ≠ ω₀} :=
    { smul := fun g ω => ⟨g • ω.1, fun h => ω.2 (by
          have h2 : ω.1 = g⁻¹ • ω₀ := eq_inv_smul_iff.2 h
          rw [h2, hfix])⟩
      one_smul := fun ω => Subtype.ext (one_smul G ω.1)
      mul_smul := fun g h ω => Subtype.ext (mul_smul g h ω.1) }
  rw [← card_ne_point ω₀]
  exact card_dvd_of_free' fun g ω h => hfree g ω.1 ω.2 (congrArg Subtype.val h)

theorem false_of_ten {M Ω : Type*} [Group M] [Finite M] [MulAction M Ω] [Finite Ω]
    (hΩ : Nat.card Ω = 10) (ω₁ : Ω) (E : Subgroup M) (hE9 : Nat.card E = 9)
    (htrans : ∀ ω, ∃ g : M, g • ω₁ = ω)
    (hEfix : ∀ e ∈ E, e • ω₁ = ω₁)
    (hEfree : ∀ e ∈ E, ∀ ω, ω ≠ ω₁ → e • ω = ω → e = 1)
    (hEnorm : ∀ q : M, q • ω₁ = ω₁ → ∀ e ∈ E, q * e * q⁻¹ ∈ E)
    (hEcent : ∀ e ∈ E, e ≠ 1 → ∀ y : M, y * e = e * y → y ∈ E)
    (hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hS72 : Nat.card (MulAction.stabilizer M ω₁) = 72)
    (h8 : ∀ x : M, x ^ 8 = 1 → x ^ 4 = 1) : False := by
  classical
  have hEreg : ∀ ω ω', ω ≠ ω₁ → ω' ≠ ω₁ → ∃ e ∈ E, e • ω = ω' := by
    intro ω ω' hω hω'
    let F : E → {x : Ω // x ≠ ω₁} := fun e => ⟨(e : M) • ω, fun h => hω (by
      have h2 : ω = (e : M)⁻¹ • ω₁ := eq_inv_smul_iff.2 h
      rw [h2, hEfix _ (E.inv_mem e.2)])⟩
    have hFinj : Function.Injective F := by
      intro a b hab
      have h1 : (a : M) • ω = (b : M) • ω := congrArg Subtype.val hab
      have h2 : ((b : M)⁻¹ * a) • ω = ω := by rw [mul_smul, h1, inv_smul_smul]
      have h3 := hEfree _ (E.mul_mem (E.inv_mem b.2) a.2) ω hω h2
      exact Subtype.ext (inv_mul_eq_one.1 h3).symm
    have hcard : Nat.card {x : Ω // x ≠ ω₁} ≤ Nat.card E := by rw [card_ne_point, hΩ, hE9]
    obtain ⟨e, he⟩ := (hFinj.bijective_of_nat_card_le hcard).2 ⟨ω', hω'⟩
    exact ⟨e, e.2, congrArg Subtype.val he⟩
  obtain ⟨ω₂, hω₂⟩ : ∃ ω₂ : Ω, ω₂ ≠ ω₁ := by
    by_contra h
    push Not at h
    have hle : Nat.card Ω ≤ 1 := by
      haveI : Subsingleton Ω := ⟨fun a b => (h a).trans (h b).symm⟩
      exact Finite.card_le_one_iff_subsingleton.2 inferInstance
    omega
  have h2trans : ∀ α β : Ω, α ≠ β → ∃ g : M, g • ω₁ = α ∧ g • ω₂ = β := by
    intro α β hαβ
    obtain ⟨g₁, hg₁⟩ := htrans α
    have hne : g₁⁻¹ • β ≠ ω₁ := fun h => hαβ (by rw [← hg₁, ← h, smul_inv_smul])
    obtain ⟨e, he, he'⟩ := hEreg ω₂ (g₁⁻¹ • β) hω₂ hne
    exact ⟨g₁ * e, by rw [mul_smul, hEfix e he, hg₁], by rw [mul_smul, he', smul_inv_smul]⟩
  set Q : Subgroup M := MulAction.stabilizer M ω₁ ⊓ MulAction.stabilizer M ω₂ with hQ
  have hmemQ : ∀ q, q ∈ Q ↔ q • ω₁ = ω₁ ∧ q • ω₂ = ω₂ := fun q => by
    rw [hQ, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
  have hQE : ∀ q ∈ Q, q ∈ E → q = 1 := fun q hq hqE => hEfree q hqE ω₂ hω₂ ((hmemQ q).1 hq).2
  have hQfree : ∀ q ∈ Q, ∀ ω, ω ≠ ω₁ → ω ≠ ω₂ → q • ω = ω → q = 1 := by
    intro q hq ω hω1 hω2 hqω
    obtain ⟨hq1, hq2⟩ := (hmemQ q).1 hq
    obtain ⟨e, he, rfl⟩ := hEreg ω₂ ω hω₂ hω1
    have he1 : e ≠ 1 := by
      rintro rfl
      rw [one_smul] at hω2
      exact hω2 rfl
    have hc : e⁻¹ * (q * e * q⁻¹) ∈ E := E.mul_mem (E.inv_mem he) (hEnorm q hq1 e he)
    have hfix : (e⁻¹ * (q * e * q⁻¹)) • ω₂ = ω₂ := by
      have hq2' : q⁻¹ • ω₂ = ω₂ := by rw [inv_smul_eq_iff, hq2]
      rw [mul_smul, mul_smul, mul_smul, hq2', hqω, inv_smul_smul]
    have h1 := hEfree _ hc ω₂ hω₂ hfix
    have hqe : q * e = e * q := by
      have h2 : q * e * q⁻¹ = e := (inv_mul_eq_one.1 h1).symm
      calc q * e = q * e * q⁻¹ * q := by group
        _ = e * q := by rw [h2]
    exact hQE q hq (hEcent e he he1 q hqe)
  have hΔ : Nat.card {ω : Ω // ω ≠ ω₁ ∧ ω ≠ ω₂} = 8 := by rw [card_ne_two_points hω₂, hΩ]
  obtain ⟨δ₀, hδ1, hδ2⟩ : ∃ δ : Ω, δ ≠ ω₁ ∧ δ ≠ ω₂ := by
    by_contra h
    push Not at h
    have : IsEmpty {ω : Ω // ω ≠ ω₁ ∧ ω ≠ ω₂} := ⟨fun ω => ω.2.2 (h ω.1 ω.2.1)⟩
    rw [Nat.card_of_isEmpty] at hΔ
    omega
  let Fq : Q → {ω : Ω // ω ≠ ω₁ ∧ ω ≠ ω₂} := fun q => ⟨(q : M) • δ₀,
    fun h => hδ1 (by
      have h2 : δ₀ = (q : M)⁻¹ • ω₁ := eq_inv_smul_iff.2 h
      rw [h2, inv_smul_eq_iff, ((hmemQ q).1 q.2).1]),
    fun h => hδ2 (by
      have h2 : δ₀ = (q : M)⁻¹ • ω₂ := eq_inv_smul_iff.2 h
      rw [h2, inv_smul_eq_iff, ((hmemQ q).1 q.2).2])⟩
  have hFqinj : Function.Injective Fq := by
    intro a b hab
    have h1 : (a : M) • δ₀ = (b : M) • δ₀ := congrArg Subtype.val hab
    have h2 : ((b : M)⁻¹ * a) • δ₀ = δ₀ := by rw [mul_smul, h1, inv_smul_smul]
    have h3 := hQfree _ (Q.mul_mem (Q.inv_mem b.2) a.2) δ₀ hδ1 hδ2 h2
    exact Subtype.ext (inv_mul_eq_one.1 h3).symm
  have hQle : Nat.card Q ≤ 8 := hΔ ▸ Nat.card_le_card_of_injective Fq hFqinj
  have hQge : 72 ≤ 9 * Nat.card Q := by
    let F : E × Q → MulAction.stabilizer M ω₁ := fun p => ⟨(p.1 : M) * p.2, by
      rw [MulAction.mem_stabilizer_iff, mul_smul, ((hmemQ p.2).1 p.2.2).1, hEfix _ p.1.2]⟩
    have hF : Function.Surjective F := by
      intro s
      have hs1 : (s : M) • ω₁ = ω₁ := MulAction.mem_stabilizer_iff.1 s.2
      have hsω : (s : M) • ω₂ ≠ ω₁ := fun h => hω₂ (by
        have h2 : ω₂ = (s : M)⁻¹ • ω₁ := eq_inv_smul_iff.2 h
        rw [h2, inv_smul_eq_iff, hs1])
      obtain ⟨e, he, he'⟩ := hEreg ω₂ ((s : M) • ω₂) hω₂ hsω
      have hq : e⁻¹ * (s : M) ∈ Q := by
        rw [hmemQ, mul_smul, mul_smul, hs1, hEfix _ (E.inv_mem he), ← he', inv_smul_smul]
        exact ⟨rfl, rfl⟩
      exact ⟨(⟨e, he⟩, ⟨_, hq⟩), Subtype.ext (by simp [F])⟩
    have h1 := Nat.card_le_card_of_surjective F hF
    rw [Nat.card_prod, hE9, hS72] at h1
    exact h1
  have hQcard : Nat.card Q = 8 := by omega
  have hQreg : ∀ δ : Ω, δ ≠ ω₁ → δ ≠ ω₂ → ∃ q ∈ Q, q • δ₀ = δ := by
    intro δ h1 h2
    obtain ⟨q, hq⟩ := (hFqinj.bijective_of_nat_card_le (by rw [hΔ, hQcard])).2 ⟨δ, h1, h2⟩
    exact ⟨q, q.2, congrArg Subtype.val hq⟩
  have h3pt : ∀ x : M, ∀ α β γ : Ω, α ≠ β → γ ≠ α → γ ≠ β → x • α = α → x • β = β →
      x • γ = γ → x = 1 := by
    intro x α β γ hαβ hγα hγβ hxα hxβ hxγ
    obtain ⟨g, hg1, hg2⟩ := h2trans α β hαβ
    have hy : g⁻¹ * x * g ∈ Q := by
      rw [hmemQ]
      constructor
      · rw [mul_smul, mul_smul, hg1, hxα, ← hg1, inv_smul_smul]
      · rw [mul_smul, mul_smul, hg2, hxβ, ← hg2, inv_smul_smul]
    have hγ1 : g⁻¹ • γ ≠ ω₁ := fun h => hγα (by rw [← hg1, ← h, smul_inv_smul])
    have hγ2 : g⁻¹ • γ ≠ ω₂ := fun h => hγβ (by rw [← hg2, ← h, smul_inv_smul])
    have h1 := hQfree _ hy (g⁻¹ • γ) hγ1 hγ2 (by rw [mul_smul, mul_smul, smul_inv_smul, hxγ])
    calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hQ8 : ∀ x ∈ Q, x ^ 4 = 1 := fun x hx => h8 x (by
    have := pow_card_eq_one' (G := ↥Q) (x := ⟨x, hx⟩)
    rw [hQcard] at this
    exact congrArg Subtype.val this)
  have hQfpf : ∀ q ∈ Q, ∀ e ∈ E, q * e * q⁻¹ = e → q = 1 ∨ e = 1 := by
    intro q hq e he hqe
    by_cases he1 : e = 1
    · exact Or.inr he1
    · left
      refine hQE q hq (hEcent e he he1 q ?_)
      calc q * e = q * e * q⁻¹ * q := by group
        _ = e * q := by rw [hqe]
  have hinv : ∀ u ∈ Q, u ≠ 1 → u ^ 2 = 1 → ∀ e ∈ E, u * e * u⁻¹ = e⁻¹ := by
    intro u hu hu1 hu2 e he
    have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← sq, hu2])
    have hue : u * e * u⁻¹ ∈ E := hEnorm u ((hmemQ u).1 hu).1 e he
    have hfE : e * (u * e * u⁻¹) ∈ E := E.mul_mem he hue
    have hfu : u * (e * (u * e * u⁻¹)) * u⁻¹ = e * (u * e * u⁻¹) := by
      calc u * (e * (u * e * u⁻¹)) * u⁻¹ = (u * e * u⁻¹) * (u * u * e * (u⁻¹ * u⁻¹)) := by group
        _ = (u * e * u⁻¹) * e := by rw [hu', ← sq, hu2]; group
        _ = e * (u * e * u⁻¹) := hEab _ hue _ he
    rcases hQfpf u hu _ hfE hfu with h | h
    · exact absurd h hu1
    · exact eq_inv_of_mul_eq_one_right h
  obtain ⟨e₀, he₀, he₀1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    have : E = ⊥ := eq_bot_iff.2 fun e he => Subgroup.mem_bot.2 (h e he)
    rw [this, Subgroup.card_bot] at hE9
    omega
  have huniq : ∀ u ∈ Q, ∀ v ∈ Q, u ≠ 1 → v ≠ 1 → u ^ 2 = 1 → v ^ 2 = 1 → u = v := by
    intro u hu v hv hu1 hv1 hu2 hv2
    have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← sq, hv2])
    have h1 : (u * v⁻¹) * e₀ * (u * v⁻¹)⁻¹ = e₀ := by
      have h2 := hinv v hv hv1 hv2 e₀ he₀
      have h3 := hinv u hu hu1 hu2 e₀⁻¹ (E.inv_mem he₀)
      calc (u * v⁻¹) * e₀ * (u * v⁻¹)⁻¹ = u * (v⁻¹ * e₀ * v) * u⁻¹ := by group
        _ = u * (v * e₀ * v⁻¹) * u⁻¹ := by rw [show v⁻¹ * e₀ * v = v * e₀ * v⁻¹ by rw [hv']]
        _ = e₀ := by rw [h2, h3, inv_inv]
    rcases hQfpf (u * v⁻¹) (Q.mul_mem hu (Q.inv_mem hv)) e₀ he₀ h1 with h | h
    · exact mul_inv_eq_one.1 h
    · exact absurd h he₀1
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨z', hz'⟩ := exists_prime_orderOf_dvd_card' (G := ↥Q) 2 (by rw [hQcard]; norm_num)
  have hzQ : (z' : M) ∈ Q := z'.2
  have hz2 : (z' : M) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ← hz', pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z' : M) ≠ 1 := by
    intro h
    have : z' = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz'
    norm_num at hz'
  set z : M := (z' : M) with hzdef
  have hsq : ∀ x ∈ Q, x ≠ 1 → x ≠ z → x ^ 2 = z := by
    intro x hx hx1 hxz
    have hx2 : x ^ 2 ≠ 1 := fun h => hxz (huniq x hx z hzQ hx1 hz1 h hz2)
    exact huniq _ (Q.pow_mem hx 2) z hzQ hx2 hz1 (by rw [← pow_mul]; exact hQ8 x hx) hz2
  obtain ⟨g, hg⟩ := htrans ω₂
  have hne : g⁻¹ • ω₁ ≠ ω₁ := fun h => hω₂ (by
    have h2 := congrArg (g • ·) h
    simp only [smul_inv_smul] at h2
    rw [← hg, ← h2])
  obtain ⟨e, he, he'⟩ := hEreg ω₂ (g⁻¹ • ω₁) hω₂ hne
  have ht1 : (g * e) • ω₁ = ω₂ := by rw [mul_smul, hEfix e he, hg]
  have ht2 : (g * e) • ω₂ = ω₁ := by rw [mul_smul, he', smul_inv_smul]
  have htδ1 : (g * e) • δ₀ ≠ ω₁ := fun h => hδ2 (by rw [← ht2] at h; exact smul_left_cancel _ h)
  have htδ2 : (g * e) • δ₀ ≠ ω₂ := fun h => hδ1 (by rw [← ht1] at h; exact smul_left_cancel _ h)
  obtain ⟨q₀, hq₀, hq₀δ⟩ := hQreg _ htδ1 htδ2
  set t₁ := q₀⁻¹ * (g * e) with ht₁
  obtain ⟨hq₀1, hq₀2⟩ := (hmemQ q₀).1 hq₀
  have ht₁δ : t₁ • δ₀ = δ₀ := by rw [ht₁, mul_smul, ← hq₀δ, inv_smul_smul]
  have ht₁1 : t₁ • ω₁ = ω₂ := by rw [ht₁, mul_smul, ht1, inv_smul_eq_iff, hq₀2]
  have ht₁2 : t₁ • ω₂ = ω₁ := by rw [ht₁, mul_smul, ht2, inv_smul_eq_iff, hq₀1]
  have ht₁sq : t₁ * t₁ = 1 := h3pt _ ω₁ ω₂ δ₀ hω₂.symm hδ1 hδ2 (by rw [mul_smul, ht₁1, ht₁2])
    (by rw [mul_smul, ht₁2, ht₁1]) (by rw [mul_smul, ht₁δ, ht₁δ])
  have ht₁inv : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right ht₁sq
  have hnorm : ∀ x ∈ Q, t₁ * x * t₁⁻¹ ∈ Q := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := (hmemQ x).1 hx
    rw [hmemQ, ht₁inv]
    exact ⟨by rw [mul_smul, mul_smul, ht₁1, hx2, ht₁2], by rw [mul_smul, mul_smul, ht₁2, hx1, ht₁1]⟩
  have hcent : ∀ x ∈ Q, t₁ * x * t₁⁻¹ = x → x = 1 ∨ x = z := by
    intro x hx hxt
    by_contra hxne
    push Not at hxne
    obtain ⟨hx1, hxz⟩ := hxne
    have htx : t₁ * x = x * t₁ := by
      calc t₁ * x = t₁ * x * t₁⁻¹ * t₁ := by group
        _ = x * t₁ := by rw [hxt]
    have hfix1 : t₁ • (x • δ₀) = x • δ₀ := by rw [← mul_smul, htx, mul_smul, ht₁δ]
    have hfix2 : t₁ • ((x ^ 2) • δ₀) = (x ^ 2) • δ₀ := by
      rw [← mul_smul, show t₁ * x ^ 2 = x ^ 2 * t₁ by rw [sq, ← mul_assoc, htx, mul_assoc, htx,
        mul_assoc], mul_smul, ht₁δ]
    have hxδ : x • δ₀ ≠ δ₀ := fun h => hx1 (hQfree x hx δ₀ hδ1 hδ2 h)
    have hx2δ : (x ^ 2) • δ₀ ≠ δ₀ := fun h => by
      rw [hsq x hx hx1 hxz] at h
      exact hz1 (hQfree z hzQ δ₀ hδ1 hδ2 h)
    have hx2δ' : (x ^ 2) • δ₀ ≠ x • δ₀ := fun h => by
      rw [sq, mul_smul] at h
      exact hxδ (smul_left_cancel x h)
    have h1 := h3pt t₁ δ₀ (x • δ₀) ((x ^ 2) • δ₀) hxδ.symm hx2δ hx2δ' ht₁δ hfix1 hfix2
    rw [h1, one_smul] at ht₁1
    exact hω₂ ht₁1.symm
  have hsqform : ∀ x, (t₁ * x) ^ 2 = (t₁ * x * t₁⁻¹) * x := fun x => by
    rw [sq, ht₁inv]
    group
  by_cases hall : ∀ x ∈ Q, x ≠ 1 → x ≠ z → (t₁ * x) ^ 2 = 1 ∨ (t₁ * x) ^ 2 = z
  ·
    have hα : ∀ x ∈ Q, t₁ * x * t₁⁻¹ = x⁻¹ := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1, mul_one, mul_inv_cancel, inv_one]
      by_cases hxz : x = z
      · have h1 : t₁ * x * t₁⁻¹ ≠ 1 := fun h => hx1 (by
          calc x = t₁⁻¹ * (t₁ * x * t₁⁻¹) * t₁ := by group
            _ = 1 := by rw [h]; group)
        have h2 : (t₁ * x * t₁⁻¹) ^ 2 = 1 := by
          rw [show (t₁ * x * t₁⁻¹) ^ 2 = t₁ * x ^ 2 * t₁⁻¹ by rw [sq, sq]; group, hxz, hz2]
          group
        rw [huniq _ (hnorm x hx) z hzQ h1 hz1 h2 hz2, hxz]
        exact (inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])).symm
      · rcases hall x hx hx1 hxz with h | h
        · rw [hsqform] at h
          exact eq_inv_of_mul_eq_one_left h
        · exfalso
          rw [hsqform] at h
          have h2 : t₁ * x * t₁⁻¹ = x := by
            rw [eq_mul_inv_of_mul_eq h, ← hsq x hx hx1 hxz]
            group
          rcases hcent x hx h2 with h' | h'
          · exact hx1 h'
          · exact hxz h'
    have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
      intro x hx y hy
      have h1 := hα (x * y) (Q.mul_mem hx hy)
      rw [show t₁ * (x * y) * t₁⁻¹ = (t₁ * x * t₁⁻¹) * (t₁ * y * t₁⁻¹) by group, hα x hx,
        hα y hy, mul_inv_rev] at h1
      have h2 := congrArg (fun w => w⁻¹) h1
      simp only [mul_inv_rev, inv_inv] at h2
      exact h2.symm
    obtain ⟨x, hxQ, hx1, hxz⟩ : ∃ x ∈ Q, x ≠ 1 ∧ x ≠ z := by
      by_contra h
      push Not at h
      have hle : Nat.card Q ≤ 2 := by
        have hsub : (Set.univ : Set ↥Q) ⊆ {⟨1, Q.one_mem⟩, ⟨z, hzQ⟩} := by
          rintro ⟨w, hw⟩ -
          by_cases hw1 : w = 1
          · left
            exact Subtype.ext hw1
          · right
            exact Subtype.ext (h w hw hw1)
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [Set.ncard_univ] at this
        exact this.trans ((Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton]))
      omega
    obtain ⟨y, hyQ, hyx⟩ : ∃ y ∈ Q, y ∉ Subgroup.zpowers x := by
      by_contra h
      push Not at h
      have hle : Q ≤ Subgroup.zpowers x := fun y hy => h y hy
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers] at h1
      have h2 : orderOf x ∣ 4 := orderOf_dvd_of_pow_eq_one (hQ8 x hxQ)
      have h3 := Nat.le_of_dvd (by norm_num) h2
      omega
    have hy1 : y ≠ 1 := fun h => hyx (h ▸ Subgroup.one_mem _)
    have hyz : y ≠ z := fun h => hyx (by
      rw [h, ← hsq x hxQ hx1 hxz]
      exact Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2)
    have hxy : (x * y⁻¹) ^ 2 = 1 := by
      have hc : y⁻¹ * x = x * y⁻¹ := hQab _ (Q.inv_mem hyQ) _ hxQ
      calc (x * y⁻¹) ^ 2 = x ^ 2 * (y ^ 2)⁻¹ := by
            rw [sq, sq, sq, mul_assoc, ← mul_assoc y⁻¹, hc, mul_inv_rev]; group
        _ = 1 := by rw [hsq x hxQ hx1 hxz, hsq y hyQ hy1 hyz, mul_inv_cancel]
    by_cases h1 : x * y⁻¹ = 1
    · exact hyx (by rw [← mul_inv_eq_one.1 h1]; exact Subgroup.mem_zpowers x)
    · have h2 := huniq _ (Q.mul_mem hxQ (Q.inv_mem hyQ)) z hzQ h1 hz1 hxy hz2
      apply hyx
      have h3 : y = z⁻¹ * x := by rw [← h2]; group
      rw [h3, ← hsq x hxQ hx1 hxz]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) 2))
        (Subgroup.mem_zpowers x)
  ·
    push Not at hall
    obtain ⟨x, hx, hx1, hxz, h1, h2⟩ := hall
    have hsqQ : (t₁ * x) ^ 2 ∈ Q := by rw [hsqform]; exact Q.mul_mem (hnorm x hx) hx
    have h4 : ((t₁ * x) ^ 2) ^ 2 = z := hsq _ hsqQ h1 h2
    have h8' : (t₁ * x) ^ 8 = 1 := by
      rw [show 8 = 2 * 4 by norm_num, pow_mul, hQ8 _ hsqQ]
    have h4' := h8 _ h8'
    rw [show 4 = 2 * 2 by norm_num, pow_mul, h4] at h4'
    exact hz1 h4'

end Ten

section Maximal

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

theorem not_mulEquiv_alt {X : Type} [Group X] (hX : IsLThreeFour X) (Ω : Type) [Fintype Ω]
    [DecidableEq Ω] (h5 : 5 ≤ Fintype.card Ω) : IsEmpty (X ≃* alternatingGroup Ω) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  refine ⟨fun e => ?_⟩
  have hcard : Nat.card (alternatingGroup Ω) = 20160 := by
    rw [← Nat.card_congr e.toEquiv, card_of_isLThreeFour hX]
  haveI : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
  have h8 : Fintype.card Ω = 8 := by
    have h2 := two_mul_nat_card_alternatingGroup (α := Ω)
    rw [hcard, Nat.card_perm, Nat.card_eq_fintype_card] at h2
    exact CFSG.ComponentClassification.PSL3Four.eq_eight_of_factorial h5 (by omega)
  let f : Fin 8 ≃ Ω := (Fintype.equivFinOfCardEq h8).symm
  let e' : X ≃* alternatingGroup (Fin 8) := e.trans (Equiv.altCongrHom f).symm
  have hcmem : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  have hdmem : (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 5 6) ∈ alternatingGroup (Fin 8) := by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap (by decide),
      Equiv.Perm.sign_swap (by decide)]
    decide
  have hcd' : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) * (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 5 6) =
      (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 5 6) * (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) := by
    decide
  have hc3' : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ^ 3 = 1 := by decide
  have hc1' : (Equiv.swap (0 : Fin 8) 1 * Equiv.swap 1 2) ≠ 1 := by decide
  have hd2' : (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 5 6) ^ 2 = 1 := by decide
  have hd1' : (Equiv.swap (3 : Fin 8) 4 * Equiv.swap 5 6) ≠ 1 := by decide
  set c : alternatingGroup (Fin 8) := ⟨_, hcmem⟩ with hc
  set d : alternatingGroup (Fin 8) := ⟨_, hdmem⟩ with hd
  have hcd : c * d = d * c := Subtype.ext hcd'
  have hc3 : c ^ 3 = 1 := Subtype.ext hc3'
  have hc1 : c ≠ 1 := fun h => hc1' (congrArg Subtype.val h)
  have hd2 : d ^ 2 = 1 := Subtype.ext hd2'
  have hd1 : d ≠ 1 := fun h => hd1' (congrArg Subtype.val h)
  set x := e'.symm c with hx
  set t := e'.symm d with ht
  have hx3 : x ^ 3 = 1 := by rw [hx, ← map_pow, hc3, map_one]
  have hx1 : x ≠ 1 := fun h => hc1 (by rw [← e'.apply_symm_apply c, ← hx, h, map_one])
  have ht2 : t ^ 2 = 1 := by rw [ht, ← map_pow, hd2, map_one]
  have ht1 : t ≠ 1 := fun h => hd1 (by rw [← e'.apply_symm_apply d, ← ht, h, map_one])
  have htx : t * x = x * t := by rw [hx, ht, ← map_mul, ← map_mul, hcd]
  have hx3' : IsPGroup 3 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one])
  obtain ⟨S, hS⟩ := hx3'.exists_le_sylow
  have hS9 := card_sylow_of_isLThreeFour hX S
  have htS : t ∈ (S : Subgroup X) :=
    Inputs1114.l34_mem_of_commute hX hS9 (hS (Subgroup.mem_zpowers x)) hx1 htx
  have ht3 : t ^ 3 = 1 := pow_three_of_card_nine hX hS9 htS
  apply ht1
  calc t = t ^ 3 * (t ^ 2)⁻¹ := by group
    _ = 1 := by rw [ht3, ht2]; group

theorem index_gt_eleven {X : Type} [Group X] (hX : IsLThreeFour X) {M : Subgroup X} (hM : M ≠ ⊤) :
    11 < M.index := by
  haveI := finite_of_isLThreeFour hX
  haveI := (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hX).1
  exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.no_small_index_of_card_20160 (card_of_isLThreeFour hX)
    (fun Ω _ _ h5 => not_mulEquiv_alt hX Ω h5) M hM

theorem normalizer_maximal {X : Type} [Group X] (hX : IsLThreeFour X) {E : Subgroup X}
    (hE : Nat.card E = 9) {M : Subgroup X} (hNM : Subgroup.normalizer (E : Set X) ≤ M) :
    M = Subgroup.normalizer (E : Set X) ∨ M = ⊤ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := finite_of_isLThreeFour hX
  set N := Subgroup.normalizer (E : Set X) with hN
  have hN72 : Nat.card N = 72 := card_normalizer_nine hX hE
  have hEN : E ≤ N := Subgroup.le_normalizer
  have hEM : E ≤ M := hEN.trans hNM
  set N' : Subgroup M := N.subgroupOf M with hN'
  set E' : Subgroup M := E.subgroupOf M with hE'
  have hN'card : Nat.card N' = 72 := by
    rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNM).toEquiv, hN72]
  have hE'card : Nat.card E' = 9 := by
    rw [hE', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv, hE]
  have hmemN' : ∀ g : M, g ∈ N' ↔ (g : X) ∈ N := fun g => Subgroup.mem_subgroupOf
  have hmemE' : ∀ g : M, g ∈ E' ↔ (g : X) ∈ E := fun g => Subgroup.mem_subgroupOf
  set ω₁ : M ⧸ N' := ((1 : M) : M ⧸ N') with hω₁
  have hmk : ∀ g h : M, g • ((h : M) : M ⧸ N') = ((g * h : M) : M ⧸ N') := fun g h => rfl
  have hstab : ∀ q : M, q • ω₁ = ω₁ ↔ q ∈ N' := by
    intro q
    rw [hω₁, hmk, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]
  have hEfix : ∀ e ∈ E', e • ω₁ = ω₁ := fun e he => (hstab e).2 ((hmemN' e).2 (hEN ((hmemE' e).1 he)))
  have hEfree : ∀ e ∈ E', ∀ ω : M ⧸ N', ω ≠ ω₁ → e • ω = ω → e = 1 := by
    intro e he ω hω heω
    induction ω using QuotientGroup.induction_on with
    | H g =>
      by_contra he1
      apply hω
      rw [hmk, QuotientGroup.eq] at heω
      have hy : ((g : X)⁻¹ * (e : X)⁻¹ * (g : X)) ∈ N := by
        have := (hmemN' _).1 heω
        simpa [mul_assoc] using this
      have he3 : (e : X) ^ 3 = 1 := pow_three_of_card_nine hX hE ((hmemE' e).1 he)
      have hy3 : IsPGroup 3 (Subgroup.zpowers ((g : X)⁻¹ * (e : X)⁻¹ * (g : X))) := by
        refine IsPGroup.of_card (n := 1) ?_
        have h1 : ((g : X)⁻¹ * (e : X)⁻¹ * (g : X)) ^ 3 = 1 := by
          have h0 : (g : X)⁻¹ * (e : X)⁻¹ * (g : X) = (g : X)⁻¹ * (e : X)⁻¹ * ((g : X)⁻¹)⁻¹ := by
            rw [inv_inv]
          rw [h0, conj_pow, inv_pow, he3, inv_one, mul_one, mul_inv_cancel]
        have h2 : ((g : X)⁻¹ * (e : X)⁻¹ * (g : X)) ≠ 1 := fun h => he1 (Subtype.ext (by
          have h3 : (e : X)⁻¹ = 1 := by
            calc (e : X)⁻¹ = (g : X) * ((g : X)⁻¹ * (e : X)⁻¹ * (g : X)) * (g : X)⁻¹ := by group
              _ = 1 := by rw [h]; group
          rw [Subgroup.coe_one, ← inv_inj, h3, inv_one]))
        rw [Nat.card_zpowers, orderOf_eq_prime h1 h2, pow_one]
      have hyE := mem_of_mem_normalizer hX hE hy hy3
      have he1' : (e : X)⁻¹ ≠ 1 := fun h => he1 (Subtype.ext (by
        rw [Subgroup.coe_one, ← inv_inj, h, inv_one]))
      have hgN : (g : X) ∈ N := by
        refine Subgroup.mem_normalizer_fintype fun a ha => ?_
        refine Inputs1114.l34_mem_of_commute hX hE (E.inv_mem ((hmemE' e).1 he)) he1' ?_
        have hc := commute_of_card_nine hE ha hyE
        calc (g : X) * a * (g : X)⁻¹ * (e : X)⁻¹ =
              (g : X) * (a * ((g : X)⁻¹ * (e : X)⁻¹ * (g : X))) * (g : X)⁻¹ := by group
          _ = (g : X) * (((g : X)⁻¹ * (e : X)⁻¹ * (g : X)) * a) * (g : X)⁻¹ := by rw [hc]
          _ = (e : X)⁻¹ * ((g : X) * a * (g : X)⁻¹) := by group
      rw [hω₁, QuotientGroup.eq, mul_one]
      exact N'.inv_mem ((hmemN' _).2 hgN)
  have hm9 : 9 ∣ N'.index - 1 := by
    have h := card_dvd_card_sub_one (G := ↥E') ω₁ (fun e => hEfix e e.2)
      (fun e ω hω h => Subtype.ext (by
        have := hEfree e e.2 ω hω h
        rw [this]; rfl))
    rwa [hE'card] at h
  have hcardM : Nat.card M = 72 * N'.index := by rw [← hN'card]; exact (Subgroup.card_mul_index N').symm
  have hm280 : N'.index ∣ 280 := by
    have h := Subgroup.card_subgroup_dvd_card M
    rw [hcardM, card_of_isLThreeFour hX, show 20160 = 72 * 280 by norm_num] at h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
  have hdiv : N'.index ∈ Nat.divisors 280 := Nat.mem_divisors.2 ⟨hm280, by norm_num⟩
  have hdivs : Nat.divisors 280 = {1, 2, 4, 5, 7, 8, 10, 14, 20, 28, 35, 40, 56, 70, 140, 280} := by
    decide
  rw [hdivs] at hdiv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
  have hcases : N'.index = 1 ∨ N'.index = 10 ∨ N'.index = 28 ∨ N'.index = 280 := by omega
  rcases hcases with h1 | h10 | h28 | h280
  · left
    have htop : N' = ⊤ := Subgroup.index_eq_one.1 h1
    exact le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hNM
  · exfalso
    refine false_of_ten (M := ↥M) (Ω := ↥M ⧸ N') h10 ω₁ E' hE'card ?_ hEfix hEfree ?_ ?_ ?_ ?_ ?_
    · intro ω
      induction ω using QuotientGroup.induction_on with
      | H g => exact ⟨g, by rw [hω₁, hmk, mul_one]⟩
    · intro q hq e he
      have hqN : (q : X) ∈ N := (hmemN' q).1 ((hstab q).1 hq)
      rw [hmemE']
      exact (Subgroup.mem_normalizer_iff.1 hqN (e : X)).1 ((hmemE' e).1 he)
    · intro e he he1 y hy
      rw [hmemE']
      refine Inputs1114.l34_mem_of_commute hX hE ((hmemE' e).1 he) (fun h => he1 (Subtype.ext h)) ?_
      exact congrArg Subtype.val hy
    · intro a ha b hb
      exact Subtype.ext (commute_of_card_nine hE ((hmemE' a).1 ha) ((hmemE' b).1 hb))
    · have : MulAction.stabilizer M ω₁ = N' := by
        rw [hω₁]
        exact MulAction.stabilizer_quotient N'
      rw [this, hN'card]
    · intro x hx
      apply Subtype.ext
      have := pow_four_of_pow_eight hX (x := (x : X)) (by rw [← Subgroup.coe_pow, hx, Subgroup.coe_one])
      rw [Subgroup.coe_pow, this, Subgroup.coe_one]
  · exfalso
    have hMtop : M ≠ ⊤ := by
      rintro rfl
      rw [Subgroup.card_top, card_of_isLThreeFour hX, h28] at hcardM
      norm_num at hcardM
    have hidx : M.index = 10 := by
      have h := Subgroup.card_mul_index M
      rw [hcardM, h28, card_of_isLThreeFour hX] at h
      omega
    have := index_gt_eleven hX hMtop
    omega
  · right
    apply Subgroup.eq_top_of_card_eq
    rw [hcardM, h280, card_of_isLThreeFour hX]

end Maximal

section SylowNormalizer

open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.HallHigman (IsPSolvable)
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.PSolvableClosure (isPSolvable_of_normal)

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_of_mem_normalizer_bar {K S : Subgroup G} (hL : IsLThreeFour (barOf 3 K)) (hSK : S ≤ K)
    (hS3 : IsPGroup 3 S) (hS9 : Nat.card S = 9) {n₁ : ↥K}
    (hn : QuotientGroup.mk' (GLAPPrimeCore 3 ↥K) n₁ ∈ Subgroup.normalizer
      (((S.subgroupOf K).map (QuotientGroup.mk' (GLAPPrimeCore 3 ↥K)) : Subgroup (barOf 3 K)) :
        Set (barOf 3 K))) :
    (n₁ : G) ∈ GLAPPrimeCoreOf 3 K ⊔ (Subgroup.normalizer (S : Set G) ⊓ K) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 ↥K with hNdef
  set π := QuotientGroup.mk' N with hπ
  set P : Subgroup ↥K := S.subgroupOf K with hP
  have hP3 : IsPGroup 3 P := hS3.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hP9 : Nat.card P = 9 := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hS9]
  have hcomap : (P.map π).comap π = P ⊔ N := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hn₁ : GLBConj n₁ P ≤ P ⊔ N := by
    intro w hw
    rw [mem_gLBConj] at hw
    rw [← hcomap, Subgroup.mem_comap]
    have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) (π (n₁ * w * n₁⁻¹))).1
      ⟨_, hw, rfl⟩
    simpa [π, mul_assoc] using h1
  have hPmax : ∀ R : Subgroup ↥K, IsPGroup 3 R → Nat.card R ≤ Nat.card P := by
    intro R hR
    rw [hP9]
    exact Inputs1114.card_le_nine_of_isPGroup hL hR
  obtain ⟨w, hw, hnN⟩ := Inputs1114.exists_mul_mem_normalizer hP3 hPmax hn₁
  have h1 : ((n₁ * w : ↥K) : G) ∈ Subgroup.normalizer (S : Set G) ⊓ K :=
    ⟨Inputs1114.mem_normalizer_of_subgroupOf hSK hnN, (n₁ * w).2⟩
  have h2 : ((w⁻¹ : ↥K) : G) ∈ GLAPPrimeCoreOf 3 K ⊔ (Subgroup.normalizer (S : Set G) ⊓ K) := by
    have hw' : (w : G) ∈ (P ⊔ N).map K.subtype := ⟨w, hw, rfl⟩
    rw [Subgroup.map_sup, hP, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSK] at hw'
    have hle : S ⊔ N.map K.subtype ≤ GLAPPrimeCoreOf 3 K ⊔ (Subgroup.normalizer (S : Set G) ⊓ K) :=
      sup_le (le_sup_of_le_right (le_inf Subgroup.le_normalizer hSK)) le_sup_left
    exact Subgroup.inv_mem _ (hle hw')
  have h3 : (n₁ : G) = ((n₁ * w : ↥K) : G) * ((w⁻¹ : ↥K) : G) := by
    simp
  rw [h3]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) h2

theorem inputL34SylowNormalizer_holds : Claims11x.InputL34SylowNormalizer := by
  intro G _ _ K S hL hSK hS3 hS9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := GLAPPrimeCore 3 ↥K with hNdef
  set π := QuotientGroup.mk' N with hπ
  have hN : ¬ 3 ∣ Nat.card N := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
    (CFSG.HardMathSupport.Solomon.LocalBalance.coprime_card_gLAPPrimeCore_aux 3 ↥K)
  set P : Subgroup ↥K := S.subgroupOf K with hP
  have hP3 : IsPGroup 3 P := hS3.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hP9 : Nat.card P = 9 := by
    rw [hP, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hS9]
  have hPbar9 : Nat.card (P.map π) = 9 := by
    rw [Inputs1114.card_map_mk_of_isPGroup hN hP3, hP9]
  refine ⟨fun H hH hHK => ?_, ?_⟩
  · set H' : Subgroup ↥K := H.subgroupOf K with hH'
    have hle : Subgroup.normalizer ((P.map π : Subgroup (barOf 3 K)) : Set (barOf 3 K)) ≤ H'.map π := by
      intro xb hxb
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N xb
      exact ⟨x, Subgroup.mem_subgroupOf.2 (hH (mem_sup_of_mem_normalizer_bar hL hSK hS3 hS9 hxb)),
        rfl⟩
    rcases normalizer_maximal hL hPbar9 hle with h | h
    · right
      refine le_antisymm (fun g hg => ?_) hH
      have hgK : g ∈ K := hHK hg
      have hgb : π ⟨g, hgK⟩ ∈ H'.map π := ⟨⟨g, hgK⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
      rw [h] at hgb
      exact mem_sup_of_mem_normalizer_bar hL hSK hS3 hS9 hgb
    · left
      refine le_antisymm hHK (fun g hgK => ?_)
      have hgb : π ⟨g, hgK⟩ ∈ H'.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨h₀, hh₀, hh₀g⟩ := hgb
      have hO : h₀⁻¹ * ⟨g, hgK⟩ ∈ N := QuotientGroup.eq.1 hh₀g
      have hOH : ((h₀⁻¹ * ⟨g, hgK⟩ : ↥K) : G) ∈ H := hH (Subgroup.mem_sup_left ⟨_, hO, rfl⟩)
      have := H.mul_mem (Subgroup.mem_subgroupOf.1 hh₀) hOH
      simpa using this
  ·
    set NS := Subgroup.normalizer (S : Set G) ⊓ K with hNS
    have hSNS : S ≤ NS := le_inf Subgroup.le_normalizer hSK
    set S' : Subgroup ↥NS := S.subgroupOf NS with hS'
    haveI hS'n : S'.Normal := ⟨fun n hn g => by
      rw [hS', Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 (Subgroup.mem_inf.1 g.2).1 _).1 hn⟩
    have hS'3 : IsPGroup 3 S' := hS3.of_equiv (Subgroup.subgroupOfEquivOfLe hSNS).symm
    have hS'9 : Nat.card S' = 9 := by
      rw [hS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSNS).toEquiv, hS9]
    have hKcard : Nat.card K = Nat.card N * 20160 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, mul_comm,
        CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hL]
    have hNScard : Nat.card NS = 9 * Nat.card (↥NS ⧸ S') := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup S', hS'9, mul_comm]
    have hdvd : Nat.card NS ∣ Nat.card K := Subgroup.card_dvd_of_le inf_le_right
    rw [hNScard, hKcard, show Nat.card N * 20160 = 9 * (Nat.card N * 2240) by ring] at hdvd
    have hq : Nat.card (↥NS ⧸ S') ∣ Nat.card N * 2240 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
    have hcop : Nat.Coprime 3 (Nat.card (↥NS ⧸ S')) := by
      refine Nat.Coprime.coprime_dvd_right hq (Nat.Coprime.mul_right ?_ (by norm_num))
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN
    exact isPSolvable_of_normal S' (Claims11x.isPSolvable_of_isPGroup_three' hS'3)
      (Claims11x.isPSolvable_of_coprime_three' hcop)

end SylowNormalizer

section Lift23

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf coprime_card_gLAPPrimeCore_aux)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

variable {G : Type} [Group G] [Finite G]

theorem lift_alt' {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (K : Set G)) (hep : e ^ p = 1)
    {A₀ : Subgroup (barOf p K)}
    (hA₀F : A₀ ≤ fixedSub (barAut p K ⟨e, heN⟩))
    (hA₀N : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), y ∈ Subgroup.normalizer (A₀ : Set (barOf p K)))
    {m : ℕ} (h5 : 5 ≤ m) (hpm : p ≤ m) (g : ↥A₀ ≃* alternatingGroup (Fin m)) :
    A₀ ≤ barX p K (Lemma123.Ke' p K e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hsimpAlt := AltFacts3.isSimple_alt h5
  haveI hsimpA : IsSimpleGroup ↥A₀ := g.isSimpleGroup
  haveI hntA : Nontrivial ↥A₀ := hsimpA.toNontrivial
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({e} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixedSub (barAut p K ⟨e, heN⟩) = barX p K C := AltFacts3.fixedSub_barAut_eq_p hp hep heN
  let ρ : ↥C →* barOf p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)
  have hρF : ∀ c : ↥C, ρ c ∈ fixedSub (barAut p K ⟨e, heN⟩) := by
    intro c
    rw [hF]
    exact ⟨⟨c, hCK c.2⟩, Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  have hρsurj : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∃ c : ↥C, ρ c = y := by
    intro y hy
    rw [hF] at hy
    obtain ⟨⟨c, hcK⟩, hc, rfl⟩ := hy
    exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, rfl⟩
  have hkerC : ∀ x : ↥C, ρ x = 1 → x ∈ GLAPPrimeCore p ↥C := fun x hx =>
    AltFacts3.ker_inclusion_le_core p hCK (MonoidHom.mem_ker.2 hx)
  set NC : Subgroup ↥C := GLAPPrimeCore p ↥C with hNC
  set R : Subgroup (barOf p K) := NC.map ρ with hR
  have hRcop : Nat.Coprime p (Nat.card R) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd _ ρ) (coprime_card_gLAPPrimeCore_aux p ↥C)
  have hRnorm : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∀ r ∈ R, y * r * y⁻¹ ∈ R := by
    intro y hy r hr
    obtain ⟨c, rfl⟩ := hρsurj y hy
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hr
    refine Subgroup.mem_map.2 ⟨c * n * c⁻¹, ?_, by simp [map_mul, map_inv]⟩
    exact (GLAPPrimeCore.normal p ↥C).conj_mem n hn c
  have hpdvd : p ∣ Nat.card ↥A₀ := by
    rw [Nat.card_congr g.toEquiv]
    exact AltFacts3.p_dvd_card_alt hp hp2 hpm
  have hRA : ∀ a ∈ A₀, a ∈ R → a = 1 := by
    have hnormS : (R.subgroupOf A₀).Normal := ⟨fun r hr a => by
      have hr' : (r : barOf p K) ∈ R := hr
      show ((a * r * a⁻¹ : ↥A₀) : barOf p K) ∈ R
      simpa using hRnorm (a : barOf p K) (hA₀F a.2) _ hr'⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (R.subgroupOf A₀) with h | h
    · intro a ha haR
      have h1 : (⟨a, ha⟩ : ↥A₀) ∈ R.subgroupOf A₀ := haR
      rw [h, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have hle : A₀ ≤ R := fun a ha => by
        have h1 : (⟨a, ha⟩ : ↥A₀) ∈ R.subgroupOf A₀ := by rw [h]; exact Subgroup.mem_top _
        exact h1
      have hd : Nat.card ↥A₀ ∣ Nat.card ↥R := Subgroup.card_dvd_of_le hle
      exact hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes hRcop (dvd_refl p) (hpdvd.trans hd))
  set P : Subgroup ↥C := A₀.comap ρ with hP
  have hPnorm : P.Normal := ⟨fun x hx c => by
    have hx' : ρ x ∈ A₀ := hx
    show ρ (c * x * c⁻¹) ∈ A₀
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hA₀N _ (hρF c)) (ρ x)).1 hx'⟩
  set K' : Subgroup (↥C ⧸ NC) := P.map (QuotientGroup.mk' NC) with hK'
  let π₁ : ↥P →* ↥A₀ := (ρ.comp P.subtype).codRestrict A₀ (fun x => x.2)
  have hπ₁ : Function.Surjective π₁ := by
    intro a
    obtain ⟨c, hc⟩ := hρsurj (a : barOf p K) (hA₀F a.2)
    have hcP : c ∈ P := by
      show ρ c ∈ A₀
      rw [hc]; exact a.2
    exact ⟨⟨c, hcP⟩, Subtype.ext hc⟩
  let π₂ : ↥P →* ↥K' := ((QuotientGroup.mk' NC).comp P.subtype).codRestrict K' (fun x => ⟨x, x.2, rfl⟩)
  have hπ₂ : Function.Surjective π₂ := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have hker12 : π₁.ker ≤ π₂.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    have h1 : ρ (x : ↥C) = 1 := congrArg Subtype.val hx
    have h2 : (x : ↥C) ∈ NC := hkerC _ h1
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).2 h2)
  let f1 : ↥A₀ →* ↥K' :=
    (QuotientGroup.lift π₁.ker π₂ hker12).comp
      (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm.toMonoidHom
  have hf1 : ∀ x : ↥P, f1 (π₁ x) = π₂ x := by
    intro x
    show (QuotientGroup.lift π₁.ker π₂ hker12)
      ((QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm (π₁ x)) = _
    have : (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).symm (π₁ x) =
        (QuotientGroup.mk x : ↥P ⧸ π₁.ker) := by
      rw [MulEquiv.symm_apply_eq]; rfl
    rw [this, QuotientGroup.lift_mk]
  have hf1s : Function.Surjective f1 := by
    intro y
    obtain ⟨x, rfl⟩ := hπ₂ y
    exact ⟨π₁ x, hf1 x⟩
  have hKnt : Nontrivial ↥K' := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have hPN : ∀ x : ↥C, x ∈ P → x ∈ NC := by
      intro x hx
      have h1 : π₂ ⟨x, hx⟩ = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).1 (congrArg Subtype.val h1)
    have hA₀1 : ∀ a ∈ A₀, a = 1 := by
      intro a ha
      obtain ⟨c, hc⟩ := hρsurj a (hA₀F ha)
      have hcP : c ∈ P := by
        show ρ c ∈ A₀
        rw [hc]; exact ha
      exact hRA a ha ⟨c, hPN c hcP, hc⟩
    obtain ⟨a, ha⟩ := (nontrivial_iff_exists_ne (1 : ↥A₀)).1 hntA
    exact ha (Subtype.ext (hA₀1 a a.2))
  have hf1i : Function.Injective f1 := by
    rw [← MonoidHom.ker_eq_bot_iff]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f1.ker with h | h
    · exact h
    · exfalso
      have h1 : ∀ x : ↥A₀, f1 x = 1 := fun x => by
        rw [← MonoidHom.mem_ker, h]; exact Subgroup.mem_top x
      obtain ⟨y, hy⟩ := (nontrivial_iff_exists_ne (1 : ↥K')).1 hKnt
      obtain ⟨x, rfl⟩ := hf1s y
      exact hy (h1 x)
  let e₂ : ↥A₀ ≃* ↥K' := MulEquiv.ofBijective f1 ⟨hf1i, hf1s⟩
  have hKq : CFSG.Open.IsQuasisimple ↥K' :=
    CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv (g.symm.trans e₂)
      (AltFacts3.isQuasisimple_alt h5)
  have hcomp : IsComponentOf K' (⊤ : Subgroup (↥C ⧸ NC)) := by
    refine ⟨le_top, ?_, hKq⟩
    haveI : K'.Normal := hPnorm.map _ (QuotientGroup.mk'_surjective NC)
    exact IsSubnormal.step le_top (Subgroup.Normal.subgroupOf inferInstance _) (IsSubnormal.refl _)
  obtain ⟨J, hJ, hJK⟩ := exists_glaPComponent_barX_eq (p := p) C hcomp
  have hJKe : J ≤ Lemma123.Ke' p K e := le_sup_of_le_right (le_sSup hJ)
  intro a ha
  obtain ⟨c, hc⟩ := hρsurj a (hA₀F ha)
  have hcP : c ∈ P := by
    show ρ c ∈ A₀
    rw [hc]; exact ha
  have hmem : QuotientGroup.mk' NC c ∈ barX p C J := by
    rw [hJK]; exact ⟨c, hcP, rfl⟩
  obtain ⟨j', hj', hjc⟩ := hmem
  have hn : j'⁻¹ * c ∈ NC := QuotientGroup.eq.1 hjc
  have hcKe : (c : G) ∈ Lemma123.Ke' p K e := by
    have h1 : (j' : G) ∈ Lemma123.Ke' p K e := hJKe (Subgroup.mem_subgroupOf.1 hj')
    have h2 : ((j'⁻¹ * c : ↥C) : G) ∈ GLAPPrimeCoreOf p C :=
      (mem_gLAPPrimeCoreOf_iff p C _).2 ⟨(j'⁻¹ * c).2, hn⟩
    have h3 : ((j'⁻¹ * c : ↥C) : G) ∈ Lemma123.Ke' p K e := le_sup_left (a := GLAPPrimeCoreOf p C) h2
    have h4 := (Lemma123.Ke' p K e).mul_mem h1 h3
    simpa using h4
  exact ⟨⟨(c : G), hCK c.2⟩, Subgroup.mem_subgroupOf.2 hcKe, hc⟩

theorem lift_core' {p : ℕ} (hp : p.Prime) {K : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (K : Set G)) (hep : e ^ p = 1) {V : Subgroup (barOf p K)}
    (hVF : V ≤ fixedSub (barAut p K ⟨e, heN⟩))
    (hVN : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), y ∈ Subgroup.normalizer (V : Set (barOf p K)))
    (hVp : Nat.Coprime p (Nat.card V)) :
    V ≤ barX p K (Lemma123.Ke' p K e) := by
  set C : Subgroup G := K ⊓ Subgroup.centralizer ({e} : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hF : fixedSub (barAut p K ⟨e, heN⟩) = barX p K C := AltFacts3.fixedSub_barAut_eq_p hp hep heN
  let ρ : ↥C →* barOf p K :=
    (QuotientGroup.mk' (GLAPPrimeCore p ↥K)).comp (Subgroup.inclusion hCK)
  have hρF : ∀ c : ↥C, ρ c ∈ fixedSub (barAut p K ⟨e, heN⟩) := by
    intro c
    rw [hF]
    exact ⟨⟨c, hCK c.2⟩, Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  have hρsurj : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), ∃ c : ↥C, ρ c = y := by
    intro y hy
    rw [hF] at hy
    obtain ⟨⟨c, hcK⟩, hc, rfl⟩ := hy
    exact ⟨⟨c, Subgroup.mem_subgroupOf.1 hc⟩, rfl⟩
  set P : Subgroup ↥C := V.comap ρ with hP
  have hPnorm : P.Normal := ⟨fun x hx c => by
    have hx' : ρ x ∈ V := hx
    show ρ (c * x * c⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hVN _ (hρF c)) (ρ x)).1 hx'⟩
  let π₁ : ↥P →* ↥V := (ρ.comp P.subtype).codRestrict V (fun x => x.2)
  have hπ₁ : Function.Surjective π₁ := by
    intro v
    obtain ⟨c, hc⟩ := hρsurj (v : barOf p K) (hVF v.2)
    have hcP : c ∈ P := by
      show ρ c ∈ V
      rw [hc]; exact v.2
    exact ⟨⟨c, hcP⟩, Subtype.ext hc⟩
  have hkercop : Nat.Coprime p (Nat.card π₁.ker) := by
    have hle : π₁.ker.map (C.subtype.comp P.subtype) ≤ GLAPPrimeCoreOf p C := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : ρ (x : ↥C) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
      exact (mem_gLAPPrimeCoreOf_iff p C _).2 ⟨(x : ↥C).2,
        AltFacts3.ker_inclusion_le_core p hCK (MonoidHom.mem_ker.2 h1)⟩
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (f := C.subtype.comp P.subtype)
      (fun a b h => Subtype.ext (Subtype.ext h))] at h1
    exact Nat.Coprime.coprime_dvd_right h1 (card_gLAPPrimeCoreOf_coprime p C)
  have hPcop : Nat.Coprime p (Nat.card P) := by
    have h1 : Nat.card P = Nat.card V * Nat.card π₁.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup π₁.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π₁ hπ₁).toEquiv]
    rw [h1]
    exact Nat.Coprime.mul_right hVp hkercop
  have hPO : P ≤ GLAPPrimeCore p ↥C := CFSG.le_pPrimeCore_of_normal_coprime hPnorm hPcop
  intro v hv
  obtain ⟨c, hc⟩ := hρsurj v (hVF hv)
  have hcP : c ∈ P := by
    show ρ c ∈ V
    rw [hc]; exact hv
  have hcKe : (c : G) ∈ Lemma123.Ke' p K e :=
    le_sup_left (a := GLAPPrimeCoreOf p C) ((mem_gLAPPrimeCoreOf_iff p C _).2 ⟨c.2, hPO hcP⟩)
  exact ⟨⟨(c : G), hCK c.2⟩, Subgroup.mem_subgroupOf.2 hcKe, hc⟩

theorem altOn_le_of_fix {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (K : Set G)) (hep : e ^ p = 1) {n : ℕ}
    (f : barOf p K ≃* alternatingGroup (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ x, AltFacts3.permHom f (barAut p K ⟨e, heN⟩ x) =
      τ * AltFacts3.permHom f x * τ⁻¹)
    (h5 : 5 ≤ Fintype.card {i // τ i = i}) :
    AltFacts3.altOn (fun i => τ i = i) ≤
      (barX p K (Lemma123.Ke' p K e)).map (AltFacts3.permHom f) := by
  obtain ⟨hF, hN⟩ := AltFacts3.A0_props f (barAut p K ⟨e, heN⟩) τ hτ
  have hle : AltFacts3.A0 f (fun i => τ i = i) ≤ barX p K (Lemma123.Ke' p K e) := by
    by_cases hpm : p ≤ Fintype.card {i // τ i = i}
    · exact lift_alt' hp hp2 heN hep hF hN h5 hpm (AltFacts3.A0EquivFin f _ rfl)
    · refine lift_core' hp heN hep hF hN ?_
      rw [Nat.card_congr (AltFacts3.A0EquivFin f _ rfl).toEquiv]
      haveI : Nontrivial (Fin (Fintype.card {i // τ i = i})) :=
        Fin.nontrivial_iff_two_le.mpr (by omega)
      have h2 := two_mul_nat_card_alternatingGroup (α := Fin (Fintype.card {i // τ i = i}))
      rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin] at h2
      refine (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_
      have h3 : p ∣ (Fintype.card {i // τ i = i}).factorial := h2 ▸ Dvd.dvd.mul_left hd 2
      exact hpm ((Nat.Prime.dvd_factorial hp).1 h3)
  intro τ' hτ'
  obtain ⟨x, hx⟩ := AltFacts3.exists_permHom_eq f (AltFacts3.altOn_le _ hτ')
  refine ⟨x, hle ?_, hx⟩
  rw [AltFacts3.mem_A0, hx]
  exact hτ'

theorem kleinOn_le_of_fix {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K : Subgroup G} {e : G}
    (heN : e ∈ Subgroup.normalizer (K : Set G)) (hep : e ^ p = 1) {n : ℕ}
    (f : barOf p K ≃* alternatingGroup (Fin n)) (τ : Equiv.Perm (Fin n))
    (hτ : ∀ x, AltFacts3.permHom f (barAut p K ⟨e, heN⟩ x) =
      τ * AltFacts3.permHom f x * τ⁻¹)
    (h4 : (Finset.univ.filter fun i => τ i = i).card = 4) :
    Claims126.kleinOn (Finset.univ.filter fun i => τ i = i) ≤
      (barX p K (Lemma123.Ke' p K e)).map (AltFacts3.permHom f) := by
  set s := Finset.univ.filter fun i => τ i = i with hs
  set V : Subgroup (barOf p K) := (Claims126.kleinOn s).comap (AltFacts3.permHom f) with hV
  have hsupp : ∀ g ∈ Claims126.kleinOn s, ∀ i, ¬ τ i = i → g i = i := by
    intro g hg i hi
    by_contra hgi
    have h1 := (Claims126.mem_altOn.1 ((Claims126.mem_kleinOn h4).1 hg).1).2
      (Equiv.Perm.mem_support.2 hgi)
    rw [hs, Finset.mem_filter] at h1
    exact hi h1.2
  have hcomm : ∀ g ∈ Claims126.kleinOn s, g * τ = τ * g := fun g hg =>
    AltFacts3.comm_of_mem_altOn (AltFacts3.mem_altOn_of _
      (Claims126.mem_altOn.1 ((Claims126.mem_kleinOn h4).1 hg).1).1 (hsupp g hg))
  have hVF : V ≤ fixedSub (barAut p K ⟨e, heN⟩) := by
    intro x hx
    show barAut p K ⟨e, heN⟩ x = x
    apply AltFacts3.permHom_injective f
    rw [hτ x, ← hcomm _ hx, mul_inv_cancel_right]
  have hconj : ∀ c : Equiv.Perm (Fin n), c * τ = τ * c → ∀ g ∈ Claims126.kleinOn s,
      c * g * c⁻¹ ∈ Claims126.kleinOn s := by
    intro c hc g hg
    obtain ⟨hga, hg1⟩ := (Claims126.mem_kleinOn h4).1 hg
    obtain ⟨hgA, hgs⟩ := Claims126.mem_altOn.1 hga
    rw [Claims126.mem_kleinOn h4]
    refine ⟨Claims126.mem_altOn.2 ⟨alternatingGroup.normal.conj_mem g hgA c, ?_⟩, ?_⟩
    · rw [Equiv.Perm.support_conj]
      intro i hi
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hi
      have hjs := hgs hj
      rw [hs, Finset.mem_filter] at hjs ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      show τ (c j) = c j
      have := congrArg (fun π : Equiv.Perm (Fin n) => π j) hc
      simp only [Equiv.Perm.coe_mul, Function.comp_apply] at this
      rw [← this, hjs.2]
    · rcases hg1 with h | h
      · left
        rw [h, mul_one, mul_inv_cancel]
      · right
        rw [Equiv.Perm.cycleType_conj]
        exact h
  have hVN : ∀ y ∈ fixedSub (barAut p K ⟨e, heN⟩), y ∈ Subgroup.normalizer (V : Set (barOf p K)) := by
    intro y hy
    have hy' : barAut p K ⟨e, heN⟩ y = y := hy
    have hyτ : AltFacts3.permHom f y * τ = τ * AltFacts3.permHom f y := by
      have h1 := hτ y
      rw [hy'] at h1
      calc AltFacts3.permHom f y * τ = (τ * AltFacts3.permHom f y * τ⁻¹) * τ := by rw [← h1]
        _ = τ * AltFacts3.permHom f y := by group
    have hyτ' : (AltFacts3.permHom f y)⁻¹ * τ = τ * (AltFacts3.permHom f y)⁻¹ := by
      calc (AltFacts3.permHom f y)⁻¹ * τ =
            (AltFacts3.permHom f y)⁻¹ * (τ * AltFacts3.permHom f y) * (AltFacts3.permHom f y)⁻¹ := by
            group
        _ = τ * (AltFacts3.permHom f y)⁻¹ := by rw [← hyτ]; group
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      show AltFacts3.permHom f (y * x * y⁻¹) ∈ Claims126.kleinOn s
      rw [map_mul, map_mul, map_inv]
      exact hconj _ hyτ _ hx
    · intro hx
      show AltFacts3.permHom f x ∈ Claims126.kleinOn s
      have h1 := hconj _ hyτ' _ hx
      have : AltFacts3.permHom f x = (AltFacts3.permHom f y)⁻¹ * AltFacts3.permHom f (y * x * y⁻¹) *
          (AltFacts3.permHom f y)⁻¹⁻¹ := by
        rw [map_mul, map_mul, map_inv]; group
      rw [this]
      exact h1
  have hV4 : Nat.card V = 4 := by
    have hle : Claims126.kleinOn s ≤ (AltFacts3.permHom f).range := by
      intro g hg
      obtain ⟨x, hx⟩ := AltFacts3.exists_permHom_eq f
        (Claims126.mem_altOn.1 ((Claims126.mem_kleinOn h4).1 hg).1).1
      exact ⟨x, hx⟩
    have h1 := Subgroup.card_map_of_injective (K := V) (AltFacts3.permHom_injective f)
    rw [hV, Subgroup.map_comap_eq, inf_eq_right.2 hle, Claims126.card_kleinOn h4] at h1
    exact h1.symm
  have hle := lift_core' hp heN hep hVF hVN (by
    rw [hV4]
    exact Nat.Coprime.pow_right 2 ((Nat.coprime_primes hp Nat.prime_two).2 hp2))
  intro g hg
  obtain ⟨x, hx⟩ := AltFacts3.exists_permHom_eq f
    (Claims126.mem_altOn.1 ((Claims126.mem_kleinOn h4).1 hg).1).1
  refine ⟨x, hle ?_, hx⟩
  show AltFacts3.permHom f x ∈ Claims126.kleinOn s
  rw [hx]
  exact hg

end Lift23

section PermId

open Equiv

variable {α : Type*} [DecidableEq α]

theorem sq_swaps {a s s₁ s₂ t t₁ t₂ : α} (h1 : a ≠ s) (h2 : a ≠ s₁) (h3 : a ≠ s₂) (h4 : a ≠ t)
    (h5 : a ≠ t₁) (h6 : a ≠ t₂) (h7 : s ≠ s₁) (h8 : s ≠ s₂) (h9 : s ≠ t) (h10 : s ≠ t₁) (h11 : s ≠ t₂)
    (h12 : s₁ ≠ s₂) (h13 : s₁ ≠ t) (h14 : s₁ ≠ t₁) (h15 : s₁ ≠ t₂) (h16 : s₂ ≠ t) (h17 : s₂ ≠ t₁)
    (h18 : s₂ ≠ t₂) (h19 : t ≠ t₁) (h20 : t ≠ t₂) (h21 : t₁ ≠ t₂) :
    ((swap a s * swap s₁ s₂) * (swap a t * swap t₁ t₂)) ^ 2 = swap a t * swap a s := by
  have h1' := h1.symm; have h2' := h2.symm; have h3' := h3.symm; have h4' := h4.symm
  have h5' := h5.symm; have h6' := h6.symm; have h7' := h7.symm; have h8' := h8.symm
  have h9' := h9.symm; have h10' := h10.symm; have h11' := h11.symm; have h12' := h12.symm
  have h13' := h13.symm; have h14' := h14.symm; have h15' := h15.symm; have h16' := h16.symm
  have h17' := h17.symm; have h18' := h18.symm; have h19' := h19.symm; have h20' := h20.symm
  have h21' := h21.symm
  ext z
  simp only [sq, Perm.coe_mul, Function.comp_apply]
  by_cases za : z = a
  · rw [za]; simp [swap_apply_def, *]
  by_cases zs : z = s
  · rw [zs]; simp [swap_apply_def, *]
  by_cases zs₁ : z = s₁
  · rw [zs₁]; simp [swap_apply_def, *]
  by_cases zs₂ : z = s₂
  · rw [zs₂]; simp [swap_apply_def, *]
  by_cases zt : z = t
  · rw [zt]; simp [swap_apply_def, *]
  by_cases zt₁ : z = t₁
  · rw [zt₁]; simp [swap_apply_def, *]
  by_cases zt₂ : z = t₂
  · rw [zt₂]; simp [swap_apply_def, *]
  simp [swap_apply_of_ne_of_ne, za, zs, zs₁, zs₂, zt, zt₁, zt₂]

theorem inv_swaps {a s t : α} (h1 : a ≠ s) (h2 : a ≠ t) (h3 : s ≠ t) :
    (swap t s * swap t a)⁻¹ = swap a s * swap a t := by
  rw [mul_inv_rev, swap_inv, swap_inv]
  have h1' := h1.symm; have h2' := h2.symm; have h3' := h3.symm
  ext z
  simp only [Perm.coe_mul, Function.comp_apply]
  by_cases za : z = a
  · rw [za]; simp [swap_apply_def, *]
  by_cases zs : z = s
  · rw [zs]; simp [swap_apply_def, *]
  by_cases zt : z = t
  · rw [zt]; simp [swap_apply_def, *]
  simp [swap_apply_of_ne_of_ne, za, zs, zt]

theorem conj_swaps (g : Perm α) {a s c t : α} (ha : g a = t) (hs : g s = s) (hc : g c = a) :
    g * (swap a s * swap a c) * g⁻¹ = swap t s * swap t a := by
  rw [show g * (swap a s * swap a c) * g⁻¹ = (g * swap a s * g⁻¹) * (g * swap a c * g⁻¹) by group,
    ← swap_apply_apply, ← swap_apply_apply, ha, hs, hc]

end PermId

section Gen23

open Equiv Equiv.Perm

theorem alt_le_of_blocks {p n : ℕ} [hp : Fact p.Prime] (hp3 : 3 ≤ p) (hpn : p < n)
    (hpdvd : ¬ p ∣ n) (h5 : 5 ≤ n) {Γ Ab Bb : Subgroup (Perm (Fin n))} (hAb : IsElemAbelian p Ab)
    (hAbcard : Nat.card Ab = p ^ (n / p)) (hBbAb : Bb ≤ Ab) (hBbcard : p < Nat.card Bb)
    (hΓalt : ∀ β ∈ Bb, β ≠ 1 → 5 ≤ Fintype.card {i // β i = i} →
      AltFacts3.altOn (fun i => β i = i) ≤ Γ)
    (hΓkl : ∀ β ∈ Bb, β ≠ 1 → (Finset.univ.filter fun i => β i = i).card = 4 →
      Claims126.kleinOn (Finset.univ.filter fun i => β i = i) ≤ Γ) :
    alternatingGroup (Fin n) ≤ Γ := by
  classical
  obtain ⟨k, x, hk, hxA, hxc, hxd⟩ := AltInputs2.exists_pcyc hp3 hAb (by rw [Fintype.card_fin]; exact hAbcard)
  have hle : Subgroup.closure (Set.range x) ≤ Ab :=
    (Subgroup.closure_le Ab).2 (by rintro _ ⟨i, rfl⟩; exact hxA i)
  have hclcard := (AltInputs2.closure_pcyc (p := p) hxc hxd).1
  have hcl : Ab = Subgroup.closure (Set.range x) :=
    (Subgroup.eq_of_le_of_card_ge hle (by rw [hclcard, hAbcard, hk, Fintype.card_fin])).symm
  have hcomm : ∀ a ∈ Ab, ∀ b ∈ Ab, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAb.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hdisj : ∀ i j, i ≠ j → ∀ t, t ∈ (x i).support → t ∉ (x j).support := fun i j hij t hi hj =>
    Finset.disjoint_left.1 (hxd i j hij).disjoint_support hi hj
  have hinv : ∀ g ∈ Ab, ∀ j t, t ∈ (x j).support ↔ g t ∈ (x j).support := by
    intro g hg j
    rw [hcl] at hg
    refine Subgroup.closure_induction (p := fun g _ => ∀ t, t ∈ (x j).support ↔ g t ∈ (x j).support)
      ?_ (fun t => by simp) (fun a b _ _ ha hb t => by rw [Perm.mul_apply, hb t, ha (b t)])
      (fun a _ ha t => by
        have h1 := ha (a⁻¹ t)
        rw [show a (a⁻¹ t) = t by simp [Perm.inv_def]] at h1
        exact h1.symm) hg
    rintro _ ⟨i, rfl⟩ t
    by_cases hij : i = j
    · subst hij
      exact Perm.apply_mem_support.symm
    · constructor
      · intro ht
        have h1 : x i t = t := ((hxd i j hij) t).resolve_right (Perm.mem_support.1 ht)
        rw [h1]
        exact ht
      · intro ht
        by_contra hnt
        have h1 : x i t ≠ t := fun h => hnt (h ▸ ht)
        exact hdisj i j hij _ (Perm.apply_mem_support.2 (Perm.mem_support.2 h1)) ht
  have hfixall : ∀ g ∈ Ab, ∀ t, (∀ j, x j t = t) → g t = t := by
    intro g hg t ht
    rw [hcl] at hg
    refine Subgroup.closure_induction (p := fun g _ => g t = t) ?_ rfl
      (fun a b _ _ ha hb => by rw [Perm.mul_apply, hb, ha])
      (fun a _ ha => by rw [Perm.inv_eq_iff_eq, ha]) hg
    rintro _ ⟨i, rfl⟩
    exact ht i
  have hAbp : IsPGroup p ↥Ab := fun g => ⟨1, Subtype.ext (by simpa using hAb.2 g g.2)⟩
  have hmod := AltFacts3.card_fixedPoints_modEq hAbp Ab.subtype
  obtain ⟨⟨x₀, hx₀⟩⟩ : Nonempty {i : Fin n // ∀ q : ↥Ab, Ab.subtype q i = i} := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [Nat.card_of_isEmpty] at hmod
    exact hpdvd (Nat.modEq_zero_iff_dvd.1 hmod.symm)
  have hx₀' : ∀ g ∈ Ab, g x₀ = x₀ := fun g hg => hx₀ ⟨g, hg⟩
  have hx₀j : ∀ j, x₀ ∉ (x j).support := fun j h => (Perm.mem_support.1 h) (hx₀' _ (hxA j))
  have hblock : ∀ j, ∃ β ∈ Bb, β ≠ 1 ∧ ∀ t ∈ (x j).support, β t = t := by
    intro j
    obtain ⟨s, hs⟩ : (x j).support.Nonempty :=
      Finset.card_pos.1 (by rw [(hxc j).2]; exact hp.out.pos)
    let φ : ↥Bb → ↥(x j).support := fun b => ⟨(b : Perm (Fin n)) s, (hinv b (hBbAb b.2) j s).1 hs⟩
    obtain ⟨b₁, b₂, hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt φ (by
      rw [Fintype.card_coe, (hxc j).2, ← Nat.card_eq_fintype_card]
      exact hBbcard)
    have hβB : (b₂ : Perm (Fin n))⁻¹ * b₁ ∈ Bb := Bb.mul_mem (Bb.inv_mem b₂.2) b₁.2
    have hβ1 : (b₂ : Perm (Fin n))⁻¹ * b₁ ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.1 h).symm)
    have hβs : ((b₂ : Perm (Fin n))⁻¹ * b₁) s = s := by
      have h1 : (b₁ : Perm (Fin n)) s = (b₂ : Perm (Fin n)) s := congrArg Subtype.val heq
      rw [Perm.mul_apply, h1]
      simp [Perm.inv_def]
    refine ⟨_, hβB, hβ1, fun t ht => ?_⟩
    obtain ⟨m, hm⟩ := (hxc j).1.exists_pow_eq (Perm.mem_support.1 hs) (Perm.mem_support.1 ht)
    have hcβ : Commute ((b₂ : Perm (Fin n))⁻¹ * b₁) (x j) := hcomm _ (hBbAb hβB) _ (hxA j)
    rw [← hm, ← Perm.mul_apply, (hcβ.pow_right m).eq, Perm.mul_apply, hβs]
  have hfix5 : ∀ β ∈ Bb, β ≠ 1 → ∀ F : Finset (Fin n), (∀ i ∈ F, β i = i) → 5 ≤ F.card →
      ∀ τ ∈ alternatingGroup (Fin n), (∀ i, i ∉ F → τ i = i) → τ ∈ Γ := by
    intro β hβ hβ1 F hF hF5 τ hτA hτF
    have h5' : 5 ≤ Fintype.card {i // β i = i} := by
      rw [Fintype.card_subtype]
      exact hF5.trans (Finset.card_le_card fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hF i hi⟩)
    exact hΓalt β hβ hβ1 h5'
      (AltFacts3.mem_altOn_of _ hτA fun i hi => hτF i fun hiF => hi (hF i hiF))
  have hdt : ∀ β ∈ Bb, β ≠ 1 → ∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      β a = a → β b = b → β c = c → β d = d → swap a b * swap c d ∈ Γ := by
    intro β hβ hβ1 a b c d hab hac had hbc hbd hcd ha hb hc hd
    set F := Finset.univ.filter fun i => β i = i with hF
    have hmem : ∀ i, β i = i → i ∈ F := fun i hi => Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩
    have hsub : ({a, b, c, d} : Finset (Fin n)) ⊆ F := by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact hmem _ ha
      · exact hmem _ hb
      · exact hmem _ hc
      · exact hmem _ hd
    have h4 : ({a, b, c, d} : Finset (Fin n)).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
        Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
    have hcard := Finset.card_le_card hsub
    rw [h4] at hcard
    rcases (show F.card = 4 ∨ 5 ≤ F.card by omega) with hF4 | hF5
    · exact hΓkl β hβ hβ1 hF4 (Claims126.swap_mul_swap_mem_kleinOn hF4
        (by simp [hab, hac, had, hbc, hbd, hcd]) (hmem _ ha) (hmem _ hb) (hmem _ hc) (hmem _ hd))
    · refine hfix5 β hβ hβ1 F (fun i hi => (Finset.mem_filter.1 hi).2) hF5 _ ?_ ?_
      · rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
        decide
      · intro i hi
        have hi' : i ∉ ({a, b, c, d} : Finset (Fin n)) := fun h => hi (hsub h)
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi'
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi'.2.2.1 hi'.2.2.2,
          swap_apply_of_ne_of_ne hi'.1 hi'.2.1]
  by_cases hI : ∃ y₀, y₀ ≠ x₀ ∧ ∀ g ∈ Ab, g y₀ = y₀
  ·
    obtain ⟨y₀, hy₀x, hy₀⟩ := hI
    have hy₀j : ∀ j, y₀ ∉ (x j).support := fun j h => (Perm.mem_support.1 h) (hy₀ _ (hxA j))
    have hk1 : 0 < k := by
      rw [hk, Fintype.card_fin]
      exact Nat.div_pos hpn.le hp.out.pos
    refine AltFacts3.alternatingGroup_le_of_swap_mul_swap (x := x₀) (y := y₀) hy₀x.symm
      fun i hix hiy => ?_
    obtain ⟨j, hij⟩ : ∃ j : Fin k, (∀ g ∈ Ab, g i = i) ∨ i ∈ (x j).support := by
      by_cases hig : ∀ g ∈ Ab, g i = i
      · exact ⟨⟨0, hk1⟩, Or.inl hig⟩
      · push Not at hig
        obtain ⟨g, hg, hgi⟩ := hig
        by_contra hcon
        push Not at hcon
        exact hgi (hfixall g hg i fun j => by
          by_contra h
          exact (hcon j).2 (Perm.mem_support.2 h))
    obtain ⟨β, hβ, hβ1, hβj⟩ := hblock j
    set F : Finset (Fin n) := insert x₀ (insert y₀ (insert i (x j).support)) with hFdef
    refine hfix5 β hβ hβ1 F ?_ ?_ _ (isThreeCycle_swap_mul_swap_same hy₀x.symm hix.symm hiy.symm).mem_alternatingGroup
      ?_
    · intro t ht
      simp only [hFdef, Finset.mem_insert] at ht
      rcases ht with rfl | rfl | rfl | ht
      · exact hx₀' β (hBbAb hβ)
      · exact hy₀ β (hBbAb hβ)
      · rcases hij with h | h
        · exact h β (hBbAb hβ)
        · exact hβj _ h
      · exact hβj t ht
    · have h1 : (insert x₀ (insert y₀ (x j).support)).card = p + 2 := by
        rw [Finset.card_insert_of_notMem (by simp [hy₀x.symm, hx₀j j]),
          Finset.card_insert_of_notMem (hy₀j j), (hxc j).2]
      have h2 : insert x₀ (insert y₀ (x j).support) ⊆ F := by
        intro t ht
        simp only [hFdef, Finset.mem_insert] at ht ⊢
        tauto
      have := Finset.card_le_card h2
      omega
    · intro t ht
      simp only [hFdef, Finset.mem_insert, not_or] at ht
      rw [Perm.mul_apply, swap_apply_of_ne_of_ne ht.1 ht.2.2.1, swap_apply_of_ne_of_ne ht.1 ht.2.1]
  ·
    push Not at hI
    have hblk : ∀ y, y ≠ x₀ → ∃ j, y ∈ (x j).support := by
      intro y hy
      obtain ⟨g, hg, hgy⟩ := hI y hy
      by_contra hcon
      push Not at hcon
      exact hgy (hfixall g hg y fun j => by
        by_contra h
        exact hcon j (Perm.mem_support.2 h))
    have hthree : ∀ j, ∀ s ∈ (x j).support, ∃ s₁ s₂, s₁ ∈ (x j).support ∧ s₂ ∈ (x j).support ∧
        s₁ ≠ s ∧ s₂ ≠ s ∧ s₁ ≠ s₂ := by
      intro j s hs
      have h1 : 2 ≤ ((x j).support.erase s).card := by
        rw [Finset.card_erase_of_mem hs, (hxc j).2]
        omega
      obtain ⟨s₁, hs₁, s₂, hs₂, h12⟩ := (Finset.one_lt_card (s := (x j).support.erase s)).1 (by omega)
      exact ⟨s₁, s₂, Finset.mem_of_mem_erase hs₁, Finset.mem_of_mem_erase hs₂,
        Finset.ne_of_mem_erase hs₁, Finset.ne_of_mem_erase hs₂, h12⟩
    have hβfix : ∀ β ∈ Bb, β x₀ = x₀ := fun β hβ => hx₀' β (hBbAb hβ)
    have hcross : ∀ i j, i ≠ j → ∀ s ∈ (x i).support, ∀ t ∈ (x j).support,
        swap x₀ t * swap x₀ s ∈ Γ := by
      intro i j hij s hs t ht
      obtain ⟨s₁, s₂, hs₁, hs₂, h1s, h2s, h12⟩ := hthree i s hs
      obtain ⟨t₁, t₂, ht₁, ht₂, h1t, h2t, h12t⟩ := hthree j t ht
      obtain ⟨βi, hβi, hβi1, hβiF⟩ := hblock i
      obtain ⟨βj, hβj, hβj1, hβjF⟩ := hblock j
      have hxs : ∀ u ∈ (x i).support, x₀ ≠ u := fun u hu h => hx₀j i (h ▸ hu)
      have hxt : ∀ u ∈ (x j).support, x₀ ≠ u := fun u hu h => hx₀j j (h ▸ hu)
      have hst : ∀ u ∈ (x i).support, ∀ v ∈ (x j).support, u ≠ v := fun u hu v hv h =>
        hdisj i j hij u hu (h ▸ hv)
      have hu := hdt βi hβi hβi1 x₀ s s₁ s₂ (hxs s hs) (hxs s₁ hs₁) (hxs s₂ hs₂) h1s.symm h2s.symm h12
        (hβfix βi hβi) (hβiF s hs) (hβiF s₁ hs₁) (hβiF s₂ hs₂)
      have hv := hdt βj hβj hβj1 x₀ t t₁ t₂ (hxt t ht) (hxt t₁ ht₁) (hxt t₂ ht₂) h1t.symm h2t.symm
        h12t (hβfix βj hβj) (hβjF t ht) (hβjF t₁ ht₁) (hβjF t₂ ht₂)
      have h := Γ.pow_mem (Γ.mul_mem hu hv) 2
      rwa [sq_swaps (hxs s hs) (hxs s₁ hs₁) (hxs s₂ hs₂) (hxt t ht) (hxt t₁ ht₁) (hxt t₂ ht₂)
        h1s.symm h2s.symm (hst s hs t ht) (hst s hs t₁ ht₁) (hst s hs t₂ ht₂) h12
        (hst s₁ hs₁ t ht) (hst s₁ hs₁ t₁ ht₁) (hst s₁ hs₁ t₂ ht₂) (hst s₂ hs₂ t ht)
        (hst s₂ hs₂ t₁ ht₁) (hst s₂ hs₂ t₂ ht₂) h1t.symm h2t.symm h12t] at h
    have hall : ∀ s t, s ≠ x₀ → t ≠ x₀ → s ≠ t → swap x₀ s * swap x₀ t ∈ Γ := by
      intro s t hs ht hst
      obtain ⟨i, hsi⟩ := hblk s hs
      obtain ⟨j, htj⟩ := hblk t ht
      by_cases hij : i = j
      · subst hij
        obtain ⟨β, hβ, hβ1, hβF⟩ := hblock i
        obtain ⟨c, hc⟩ : ∃ c, β c ≠ c := by
          by_contra h
          push Not at h
          exact hβ1 (Perm.ext h)
        have hcx₀ : c ≠ x₀ := fun h => hc (h ▸ hβfix β hβ)
        obtain ⟨j', hcj'⟩ := hblk c hcx₀
        have hj' : j' ≠ i := fun h => hc (hβF c (h ▸ hcj'))
        have hκ : swap x₀ s * swap x₀ c ∈ Γ := hcross j' i hj' c hcj' s hsi
        have hg : swap x₀ c * swap x₀ t ∈ Γ := hcross i j' (Ne.symm hj') t htj c hcj'
        have hsc : s ≠ c := fun h => hdisj j' i hj' c hcj' (h ▸ hsi)
        have htc : t ≠ c := fun h => hdisj j' i hj' c hcj' (h ▸ htj)
        have h1 := Γ.mul_mem (Γ.mul_mem hg hκ) (Γ.inv_mem hg)
        rw [conj_swaps (swap x₀ c * swap x₀ t) (a := x₀) (s := s) (c := c) (t := t)
          (by rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne ht htc])
          (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne hs hst, swap_apply_of_ne_of_ne hs hsc])
          (by rw [Perm.mul_apply, swap_apply_of_ne_of_ne hcx₀ htc.symm, swap_apply_right])] at h1
        have h2 := Γ.inv_mem h1
        rwa [inv_swaps (Ne.symm hs) (Ne.symm ht) hst] at h2
      · exact hcross j i (Ne.symm hij) t htj s hsi
    obtain ⟨y, hy⟩ : ∃ y : Fin n, y ≠ x₀ := by
      by_contra h
      push Not at h
      have : Fintype.card (Fin n) ≤ 1 := Fintype.card_le_one_iff.2 fun a b => (h a).trans (h b).symm
      rw [Fintype.card_fin] at this
      omega
    exact AltFacts3.alternatingGroup_le_of_swap_mul_swap (x := x₀) (y := y) hy.symm
      fun i hix hiy => hall y i hy hix (Ne.symm hiy)

end Gen23

section Main23

open Equiv Equiv.Perm
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barAut_mk barOf)
open CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns

theorem input23_3_1_holds : Claims11x.Input23_3_1 := by
  intro G _ _ p hp hp2 X K A B hK hAX hAN hAel n hpn hpdvd hAlt hcard hBA hBrk
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨B₀, hB₀B, hB₀el, hB₀card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (le_refl (CFSG.Open.pRank p B))
  rw [hBrk] at hB₀card
  set H : Subgroup G := ⨆ (e : G) (_ : e ∈ B) (_ : e ≠ 1), Lemma123.Ke' p K e with hH
  have hHK : H ≤ K := iSup_le fun e => iSup_le fun _ => iSup_le fun _ =>
    sup_le ((gLAPPrimeCoreOf_le p _).trans inf_le_left) ((Sec12b.layer_le p _).trans inf_le_left)
  have hKe_le : ∀ e ∈ B₀, e ≠ 1 → barX p K (Lemma123.Ke' p K e) ≤ barX p K H := fun e he he1 =>
    barX_mono_of_le p (le_iSup_of_le e (le_iSup_of_le (hB₀B he) (le_iSup_of_le he1 le_rfl)))
  suffices htop : barX p K H = ⊤ by
    have hcov := (barX_eq_top_iff p hHK).1 htop
    exact ((barX_eq_iff_cov hp hK.2.1 hHK).2 hcov).ge
  have hq : CFSG.Open.IsQuasisimple (barOf p K) :=
    (isQuasisimple_barX_iff hp hK.2.1).1 hK.2.2.1.2.2
  obtain ⟨f⟩ := hAlt
  haveI hnt : Nontrivial (barOf p K) := by
    haveI := hq.2.toNontrivial
    exact (QuotientGroup.mk_surjective (s := Subgroup.center (barOf p K))).nontrivial
  have h5 : 5 ≤ n := by
    by_contra h
    have h4 : n ≤ 4 := by omega
    haveI : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by simpa using h4)
    haveI : Group.IsSolvable (barOf p K) := solvable_of_solvable_injective (f := f.toMonoidHom) f.injective
    exact absurd hq.1 (Group.IsSolvable.commutator_lt_top_of_nontrivial (barOf p K)).ne
  have hB₀N : ∀ e ∈ B₀, e ∈ Subgroup.normalizer (K : Set G) := fun e he => hAN (hBA (hB₀B he))
  have hB₀p : ∀ e ∈ B₀, e ^ p = 1 := fun e he => hB₀el.2 e he
  by_cases hker : ∃ (e : G) (he : e ∈ B₀), e ≠ 1 ∧ barAut p K ⟨e, hB₀N e he⟩ = 1
  · obtain ⟨e, he, he1, hbar⟩ := hker
    have hF : (⊤ : Subgroup (barOf p K)) ≤ fixedSub (barAut p K ⟨e, hB₀N e he⟩) := fun y _ => by
      show barAut p K ⟨e, hB₀N e he⟩ y = y
      rw [hbar]
      rfl
    have hle := lift_alt' hp hp2 (hB₀N e he) (hB₀p e he) hF
      (fun y _ => Subgroup.mem_normalizer_iff.2 fun x => by simp) h5 hpn.le
      (Subgroup.topEquiv.trans f)
    exact eq_top_iff.2 (hle.trans (hKe_le e he he1))
  push Not at hker
  have h6 : n ≠ 6 := by
    rintro rfl
    have hp5 : p = 5 := by
      have hp6 : p < 6 := hpn
      interval_cases p
      · exact absurd (by decide : 3 ∣ 6) hpdvd
      · exact absurd hp (by decide)
      · rfl
    subst hp5
    let τ : ↥B₀ →* MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.congr f).toMonoidHom.comp ((barAut 5 K).comp (Subgroup.inclusion hB₀N))
    have hτinj : Function.Injective τ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      apply hker (y : G) y.2 (fun h => hy1 (Subtype.ext h))
      exact (MulEquiv.map_eq_one_iff (MulAut.congr f)).1 hy
    haveI := Input236gt.finite_mulAut (alternatingGroup (Fin 6))
    have hdvd : 5 ^ 2 ∣ Nat.card (MulAut (alternatingGroup (Fin 6))) := by
      rw [← hB₀card, Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, hk⟩ := Input236gt.dvd_card_mulAut_six
    have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.automorphism_card_le
    have hpos : 0 < Nat.card (MulAut (alternatingGroup (Fin 6))) := Nat.card_pos
    rw [hk] at hdvd hle hpos
    have hk2 : k ≤ 2 := by omega
    interval_cases k <;> omega
  set ψ := AltFacts3.permHom f with hψ
  let f' : barOf p K ≃* alternatingGroup (Fin n) :=
    MulEquiv.ofBijective (ψ.codRestrict _ (AltFacts3.permHom_mem f))
      ⟨fun a b h => AltFacts3.permHom_injective f (congrArg Subtype.val h), fun z => by
        obtain ⟨x, hx⟩ := AltFacts3.exists_permHom_eq f z.2
        exact ⟨x, Subtype.ext hx⟩⟩
  have hf' : ∀ x, ((f' x : alternatingGroup (Fin n)) : Perm (Fin n)) = ψ x := fun x => rfl
  let Φ : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin n)))
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n h5 h6)
  let σ : ↥A →* Perm (Fin n) :=
    Φ.symm.toMonoidHom.comp ((MulAut.congr f').toMonoidHom.comp
      ((barAut p K).comp (Subgroup.inclusion hAN)))
  have hσ : ∀ (a : ↥A) (x : barOf p K),
      ψ (barAut p K ⟨(a : G), hAN a.2⟩ x) = σ a * ψ x * (σ a)⁻¹ := by
    intro a x
    have h : Φ (σ a) = MulAut.congr f' (barAut p K ⟨(a : G), hAN a.2⟩) := Φ.apply_symm_apply _
    have h2 := congrArg (fun φ : MulAut ↥(alternatingGroup (Fin n)) =>
      ((φ (f' x) : ↥(alternatingGroup (Fin n))) : Perm (Fin n))) h
    simp only [Φ, MulEquiv.ofBijective_apply, MulAut.conjNormal_apply] at h2
    rw [← hf', ← hf']
    rw [h2]
    simp [MulAut.congr_apply]
  have hσ1 : ∀ a : ↥A, σ a = 1 ↔ barAut p K ⟨(a : G), hAN a.2⟩ = 1 := fun a => by
    show Φ.symm (MulAut.congr f' (barAut p K ⟨(a : G), hAN a.2⟩)) = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  have hkermap : σ.ker.map A.subtype = A ⊓ centBar p ⊤ K := by
    ext g
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨a.2, ?_⟩
      unfold centBar
      exact ⟨Subgroup.mem_map.2 ⟨⟨(a : G), hAN a.2⟩, (hσ1 a).1 ha, rfl⟩, Subgroup.mem_top _⟩
    · rintro ⟨hgA, hgc⟩
      unfold centBar at hgc
      obtain ⟨y, hyk, hyg⟩ := Subgroup.mem_map.1 (Subgroup.mem_inf.1 hgc).1
      refine ⟨⟨g, hgA⟩, (hσ1 _).2 ?_, rfl⟩
      have : (⟨g, hAN hgA⟩ : ↥(Subgroup.normalizer (K : Set G))) = y := Subtype.ext hyg.symm
      rw [this]
      exact hyk
  have hcardker : Nat.card σ.ker = Nat.card ↥(A ⊓ centBar p ⊤ K) := by
    rw [← hkermap, Subgroup.card_map_of_injective A.subtype_injective]
  have hcardA : Nat.card A = Nat.card σ.ker * Nat.card σ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange σ).toEquiv]
  have hge : p ^ (n / p) ≤ Nat.card σ.range := by
    have hpos : 0 < Nat.card σ.ker := Nat.card_pos
    rw [hcardA, ← hcardker, mul_comm (Nat.card σ.ker)] at hcard
    exact Nat.le_of_mul_le_mul_right hcard hpos
  have hrangeel : IsElemAbelian p σ.range := by
    refine ⟨⟨⟨fun u v => ?_⟩⟩, fun y hy => ?_⟩
    · rcases u with ⟨_, a, rfl⟩
      rcases v with ⟨_, b, rfl⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul, show a * b = b * a from Subtype.ext
        (congrArg Subtype.val (hAel.1.is_comm.comm ⟨a, a.2⟩ ⟨b, b.2⟩))]
    · obtain ⟨a, rfl⟩ := hy
      rw [← map_pow, show a ^ p = 1 from Subtype.ext (by simpa using hAel.2 a a.2), map_one]
  have hrange : Nat.card σ.range = p ^ (n / p) := by
    refine le_antisymm ?_ hge
    have := AltInputs.card_le_pow_div (α := Fin n) hrangeel
    rwa [Fintype.card_fin] at this
  set Bb : Subgroup (Perm (Fin n)) := (B₀.subgroupOf A).map σ with hBb
  have hBbA : Bb ≤ σ.range := Subgroup.map_le_range σ _
  have hBbmem : ∀ β ∈ Bb, β ≠ 1 → ∃ (b : G) (hb : b ∈ B₀), b ≠ 1 ∧ β = σ ⟨b, hBA (hB₀B hb)⟩ := by
    rintro _ ⟨a, ha, rfl⟩ hβ1
    refine ⟨(a : G), Subgroup.mem_subgroupOf.1 ha, fun h => hβ1 ?_, rfl⟩
    rw [show a = 1 from Subtype.ext h, map_one]
  have hBbcard : p < Nat.card Bb := by
    let ρ : ↥(B₀.subgroupOf A) →* Perm (Fin n) := σ.comp (B₀.subgroupOf A).subtype
    have hρ : Function.Injective ρ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      by_contra hy1
      have h1 : σ (y : ↥A) = 1 := hy
      apply hker ((y : ↥A) : G) (Subgroup.mem_subgroupOf.1 y.2)
        (fun h => hy1 (Subtype.ext (Subtype.ext h))) ((hσ1 _).1 h1)
    have hr : Bb = ρ.range := by
      rw [hBb, MonoidHom.range_comp, Subgroup.range_subtype]
    have h1 : Nat.card Bb = Nat.card B₀ := by
      rw [hr, ← Nat.card_congr (MonoidHom.ofInjective hρ).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hB₀B.trans hBA)).toEquiv]
    rw [h1, hB₀card]
    exact lt_self_pow₀ hp.one_lt (by norm_num)
  have hgen := alt_le_of_blocks hp3 hpn hpdvd h5 (Γ := (barX p K H).map ψ) hrangeel hrange hBbA hBbcard
    (fun β hβ hβ1 h5' => by
      obtain ⟨b, hb, hb1, rfl⟩ := hBbmem β hβ hβ1
      exact (altOn_le_of_fix hp hp2 (hB₀N b hb) (hB₀p b hb) f _ (hσ ⟨b, hBA (hB₀B hb)⟩) h5').trans
        (Subgroup.map_mono (hKe_le b hb hb1)))
    (fun β hβ hβ1 h4 => by
      obtain ⟨b, hb, hb1, rfl⟩ := hBbmem β hβ hβ1
      exact (kleinOn_le_of_fix hp hp2 (hB₀N b hb) (hB₀p b hb) f _ (hσ ⟨b, hBA (hB₀B hb)⟩) h4).trans
        (Subgroup.map_mono (hKe_le b hb hb1)))
  refine eq_top_iff.2 fun z _ => ?_
  obtain ⟨m, hm, hmz⟩ := Subgroup.mem_map.1 (hgen (AltFacts3.permHom_mem f z))
  exact (AltFacts3.permHom_injective f hmz) ▸ hm

end Main23

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL34
