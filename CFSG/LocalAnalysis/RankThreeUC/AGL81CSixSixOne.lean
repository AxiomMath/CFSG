module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenInputs
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.Infrastructure
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.proposition_4_8_b
import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
import CFSG.LocalAnalysis.RankThreeTheoremC.ConstrainedRankTwo
import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SubgroupRank
import CFSG.Quasithin.Background.A1cRank
import CFSG.RankThree.PartOne.K1214.CycAlg
import Mathlib.Tactic.Group

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C

open Subgroup CFSG.Open
open scoped commutatorElement

variable {p : ℕ} {X : Type} [Group X] [Finite X]

private theorem exists_extraspecial_char (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup X}
    (hRp : IsPGroup p R) (hsymp : CFSG.RankThree.PartTwo.IsSymplecticType ↥R)
    (hrk : CFSG.Open.pRank p R = 2) :
    ∃ D : Subgroup R, ∃ _ : D.Characteristic, (∀ x ∈ D, x ^ p = 1) ∧ Nat.card D = p ^ 3 ∧
      (∃ a b : D, a * b ≠ b * a) ∧
        IsPGroup p (CFSG.SectionRank.Ccomm.frattiniAction D).ker := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hrkR : CFSG.Open.pRank p (⊤ : Subgroup R) = 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hrk
  obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup R)
  rw [hrkR] at hEc
  haveI : Nontrivial R := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    calc 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp1
      _ = Nat.card E := hEc.symm
      _ ≤ Nat.card R := Subgroup.card_le_card_group E
  obtain ⟨D, hDc, hDne, hDp, -, htors, hker⟩ :=
    CFSG.SectionRank.Ccomm.supercritical_witness hp2 hRp
  haveI := hDc
  have hnc : ∃ a b : D, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    have hcyc : IsCyclic D := hsymp D hDc ⟨⟨hcon⟩⟩
    have hDcard : Nat.card D = p := by
      have h1 : Nat.card D ∣ p := by
        rw [← IsCyclic.exponent_eq_card]
        exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hDp x x.2)
      rcases (Nat.dvd_prime hp).mp h1 with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hDne
      · exact h
    have hcen : ∀ x : R, x ∈ centralizer (D : Set R) := by
      intro x
      obtain ⟨m, hm⟩ := hRp x
      rw [mem_centralizer_iff]
      intro d hd
      have h1 := CFSG.RankThree.PartOne.K1214.conj_eq_of_card_prime hp hDcard
        (fun d hd => (inferInstance : D.Normal).conj_mem d hd x) hm d hd
      calc d * x = x * d * x⁻¹ * x := by rw [h1]
        _ = x * d := by group
    have hED : E ≤ D := by
      intro x hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact D.one_mem
      exact htors x (hcen x) (orderOf_eq_prime (hE.2 x hx) hx1)
    have h2 := Subgroup.card_le_of_le hED
    rw [hEc, hDcard] at h2
    have h3 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp1 (by norm_num)
    rw [pow_one] at h3
    omega
  have hrkD : CFSG.Open.pRank p (⊤ : Subgroup D) ≤ 2 := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact (CFSG.SectionRank.pRank_mono hp1 le_top).trans hrkR.le
  have hcard : Nat.card D = p ^ 3 :=
    CFSG.AGLEmbedding.card_eq_pow_three_of_not_comm (hRp.to_subgroup D)
      (fun x => Subtype.ext (by rw [Subgroup.coe_pow, hDp x x.2, Subgroup.coe_one])) hrkD hnc
  exact ⟨D, hDc, hDp, hcard, hnc, hker⟩

private theorem pRank_top_le_three (hp : p.Prime) {R : Subgroup X} [R.Normal]
    (hRp : IsPGroup p R) (hRmax : ∀ N : Subgroup X, N.Normal → IsPGroup p N → N ≤ R)
    (hcent : centralizer (R : Set X) ≤ R) (hrk : CFSG.Open.pRank p R ≤ 2)
    (D : Subgroup R) [D.Characteristic] (hcard : Nat.card D = p ^ 3)
    (hnc : ∃ a b : D, a * b ≠ b * a)
    (hker : IsPGroup p (CFSG.SectionRank.Ccomm.frattiniAction D).ker) :
    CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  obtain ⟨-, -, hVc, hVe, hVcard, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hcard hnc
  have hZΦ := (CFSG.AGLEmbedding.center_structure_of_card_eq_pow_three hcard hnc).2.1
  let ρ : X →* MulAut (D ⧸ center D) := (CFSG.SectionRank.Ccomm.autQuotient (center D)).comp
    ((MulAut.characteristic D).comp (MulAut.conjNormal (H := R)))
  have hK : IsPGroup p ρ.ker :=
    CFSG.AGLEmbedding.isPGroup_ker_centerQuotient_action hRp hcent D hZΦ hker
  have hKR : ρ.ker ≤ R := hRmax _ inferInstance hK
  refine CFSG.SectionRank.pRank_le hp1 fun A _ hA => ?_
  have hAp : IsPGroup p A := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hA.2 x x.2)⟩
  let f : A →* MulAut (D ⧸ center D) := ρ.comp A.subtype
  haveI : Finite f.range := Finite.of_surjective _ f.rangeRestrict_surjective
  have h1 : Nat.card f.range ≤ p :=
    CFSG.LocalAnalysis.RankThreeTheoremC.card_le_of_isPGroup_of_injective_mulAut hVc hVe
      hVcard.le (hAp.of_surjective f.rangeRestrict f.rangeRestrict_surjective) f.range.subtype
      f.range.subtype_injective
  have h2 : Nat.card f.ker ≤ p ^ 2 := by
    have hle : f.ker.map A.subtype ≤ R := by
      rintro _ ⟨a, ha, rfl⟩
      exact hKR ha
    have hel : IsElemAbelian p (f.ker.map A.subtype) := by
      obtain ⟨⟨⟨hc⟩⟩, hpow⟩ := hA
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hpow x (map_subtype_le _ hx)⟩
      have h := congrArg Subtype.val (hc ⟨a, map_subtype_le _ a.2⟩ ⟨b, map_subtype_le _ b.2⟩)
      exact h
    obtain ⟨j, hj⟩ := (hAp.to_subgroup f.ker).exists_card_eq
    have hj' : Nat.card (f.ker.map A.subtype) = p ^ j := by
      rw [Subgroup.card_map_of_injective A.subtype_injective, hj]
    have hjle := CFSG.SectionRank.le_pRank hp1 hle hel hj'
    rw [hj]
    exact Nat.pow_le_pow_right hp.pos (hjle.trans hrk)
  have h3 : Nat.card A = Nat.card f.ker * Nat.card f.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker, mul_comm,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  calc Nat.card A = Nat.card f.ker * Nat.card f.range := h3
    _ ≤ p ^ 2 * p := Nat.mul_le_mul h2 h1
    _ = p ^ 3 := by ring

private theorem three_le_pRank_top (hp : p.Prime) (hp3 : 3 < p) {R : Subgroup X} [R.Normal]
    (hRp : IsPGroup p R) (hRmax : ∀ N : Subgroup X, N.Normal → IsPGroup p N → N ≤ R)
    (hcent : centralizer (R : Set X) ≤ R)
    (D : Subgroup R) [D.Characteristic] (hDp : ∀ x ∈ D, x ^ p = 1)
    (hcard : Nat.card D = p ^ 3) (hnc : ∃ a b : D, a * b ≠ b * a)
    (hker : IsPGroup p (CFSG.SectionRank.Ccomm.frattiniAction D).ker)
    {u : X} (hu : orderOf u = p) (huR : u ∉ R) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 := hp.one_lt
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hcomm, hZcard, -, -, hVcard, -⟩ :=
    CFSG.SectionRank.Ccomm.nonabelian_prime_cube_central_structure hcard hnc
  have hZΦ := (CFSG.AGLEmbedding.center_structure_of_card_eq_pow_three hcard hnc).2.1
  let ρ : X →* MulAut (D ⧸ center D) := (CFSG.SectionRank.Ccomm.autQuotient (center D)).comp
    ((MulAut.characteristic D).comp (MulAut.conjNormal (H := R)))
  have hup : u ^ p = 1 := hu ▸ pow_orderOf_eq_one u
  have hDp' : ∀ d : D, d ^ p = 1 := fun d =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hDp _ d.2)
  let ι : D →* X := R.subtype.comp D.subtype
  have hι : Function.Injective ι := R.subtype_injective.comp D.subtype_injective
  have hιord : ∀ d : D, d ≠ 1 → orderOf (ι d) = p := fun d hd =>
    orderOf_eq_prime (by rw [← map_pow, hDp' d, map_one])
      (fun h => hd (hι (by rw [h, map_one])))
  set β : MulAut D := MulAut.characteristic D (MulAut.conjNormal (H := R) u) with hβ
  have hιβ : ∀ d : D, ι (β d) = u * ι d * u⁻¹ := by
    intro d
    simp only [ι, β, MonoidHom.comp_apply, Subgroup.coe_subtype,
      MulAut.characteristic_apply_apply_coe, MulAut.conjNormal_apply]
  have hUp : IsPGroup p (zpowers u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨e, he, hfix⟩ : ∃ e : D, e ∉ center D ∧ e⁻¹ * β e ∈ center D := by
    letI : MulDistribMulAction (zpowers u) (D ⧸ center D) :=
      MulDistribMulAction.compHom _ (ρ.comp (zpowers u).subtype)
    set F := FixedPoints.subgroup (zpowers u) (D ⧸ center D)
    have hpF : p ∣ Nat.card F :=
      (Nat.ModEq.dvd_iff (hUp.card_modEq_card_fixedPoints (D ⧸ center D)) dvd_rfl).mp
        (hVcard ▸ dvd_pow_self p two_ne_zero)
    have hFne : F ≠ ⊥ := by
      intro hF
      rw [hF, Subgroup.card_bot] at hpF
      exact hp.one_lt.ne' (Nat.dvd_one.mp hpF)
    obtain ⟨⟨v, hvF⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective v
    refine ⟨e, fun hec => hv1 (Subtype.ext ((QuotientGroup.eq_one_iff e).mpr hec)), ?_⟩
    have h1 : ρ u (e : D ⧸ center D) = e := hvF ⟨u, mem_zpowers u⟩
    have h2 : ((β e : D) : D ⧸ center D) = e := h1
    exact QuotientGroup.eq.mp h2.symm
  obtain ⟨c, hc⟩ : ∃ c : D, c = e⁻¹ * β e := ⟨_, rfl⟩
  rw [← hc] at hfix
  have hβe : β e = e * c := by rw [hc, mul_inv_cancel_left]
  have hβcen : ∀ z ∈ center D, β z ∈ center D := by
    intro z hz
    rw [Subgroup.mem_center_iff] at hz ⊢
    intro y
    obtain ⟨y', rfl⟩ := β.surjective y
    rw [← map_mul, ← map_mul, hz y']
  have hZ'p : Nat.card ((center D).map ι) = p := by
    rw [Subgroup.card_map_of_injective hι, hZcard]
  have hconjZ := CFSG.RankThree.PartOne.K1214.conj_eq_of_card_prime (m := 1) hp hZ'p (c := u)
    (fun d hd => by
      obtain ⟨z, hz, rfl⟩ := hd
      exact ⟨β z, hβcen z hz, hιβ z⟩) (by rw [pow_one]; exact hup)
  have hβZ : ∀ z ∈ center D, β z = z := fun z hz =>
    hι (by rw [hιβ]; exact hconjZ _ ⟨z, hz, rfl⟩)
  obtain ⟨g, hg⟩ : ∃ g : D, g * e ≠ e * g := by
    by_contra h
    push Not at h
    exact he (Subgroup.mem_center_iff.mpr h)
  obtain ⟨k, hk⟩ : ∃ k : D, k = g * e * g⁻¹ * e⁻¹ := ⟨_, rfl⟩
  have hkZ : k ∈ center D := by
    rw [← hcomm]
    have h1 : k = ⁅g, e⁆ := by rw [hk, commutatorElement_def]
    rw [h1]
    exact Subgroup.commutator_mem_commutator (mem_top g) (mem_top e)
  have hk1 : k ≠ 1 := by
    intro h
    apply hg
    calc g * e = g * e * g⁻¹ * e⁻¹ * e * g := by group
      _ = e * g := by rw [← hk, h, one_mul]
  have hZk : zpowers k = center D := by
    apply Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hkZ)
    rw [hZcard, Nat.card_zpowers, orderOf_eq_prime (hDp' k) hk1]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, k ^ m = c⁻¹ := by
    have h1 : c⁻¹ ∈ zpowers k := hZk ▸ inv_mem hfix
    exact (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 h1)
  have hconj : ∀ n : ℕ, g ^ n * e * (g ^ n)⁻¹ = k ^ n * e := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hk' : g * e * g⁻¹ = k * e := by
        rw [hk]
        group
      have hgk : g * k ^ n = k ^ n * g := Subgroup.mem_center_iff.mp (pow_mem hkZ n) g
      calc g ^ (n + 1) * e * (g ^ (n + 1))⁻¹ = g * (g ^ n * e * (g ^ n)⁻¹) * g⁻¹ := by group
        _ = g * (k ^ n * e) * g⁻¹ := by rw [ih]
        _ = (g * k ^ n) * e * g⁻¹ := by group
        _ = (k ^ n * g) * e * g⁻¹ := by rw [hgk]
        _ = k ^ n * (g * e * g⁻¹) := by group
        _ = k ^ (n + 1) * e := by rw [hk', pow_succ, mul_assoc]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : D, f₀ = g ^ m := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : X, x = u * ι f₀ := ⟨_, rfl⟩
  have hxe : x * ι e * x⁻¹ = ι e := by
    calc x * ι e * x⁻¹ = u * ι (f₀ * e * f₀⁻¹) * u⁻¹ := by
          simp only [hx, map_mul, map_inv]
          group
      _ = ι (β (f₀ * e * f₀⁻¹)) := (hιβ _).symm
      _ = ι e := by
        congr 1
        rw [hf₀, hconj m, map_mul, hβZ _ (pow_mem hkZ m), hβe, hm,
          Subgroup.mem_center_iff.mp hfix e, inv_mul_cancel_left]
  have hxe' : ι e * x = x * ι e := by
    calc ι e * x = x * ι e * x⁻¹ * x := by rw [hxe]
      _ = x * ι e := by group
  have hxZ : ∀ z ∈ center D, ι z * x = x * ι z := by
    intro z hz
    have h1 : u * ι z = ι z * u := by
      have h0 := hconjZ _ ⟨z, hz, rfl⟩
      calc u * ι z = u * ι z * u⁻¹ * u := by group
        _ = ι z * u := by rw [h0]
    have h2 : ι f₀ * ι z = ι z * ι f₀ := by
      rw [← map_mul, Subgroup.mem_center_iff.mp hz f₀, map_mul]
    calc ι z * x = ι z * u * ι f₀ := by rw [hx, mul_assoc]
      _ = u * ι z * ι f₀ := by rw [h1]
      _ = u * (ι z * ι f₀) := by rw [mul_assoc]
      _ = u * (ι f₀ * ι z) := by rw [h2]
      _ = x * ι z := by rw [hx, mul_assoc]
  set D' : Subgroup X := D.map R.subtype with hD'
  have hD'n : D'.Normal := by
    constructor
    rintro _ ⟨d, hd, rfl⟩ y
    refine ⟨((MulAut.characteristic D (MulAut.conjNormal (H := R) y) ⟨d, hd⟩ : D) : R),
      SetLike.coe_mem _, ?_⟩
    simp only [Subgroup.coe_subtype, MulAut.characteristic_apply_apply_coe,
      MulAut.conjNormal_apply]
  have hD'p : IsPGroup p D' := hRp.to_le (map_subtype_le D)
  have hD'card : Nat.card D' = p ^ 3 := by
    rw [hD', Subgroup.card_map_of_injective R.subtype_injective, hcard]
  set P : Subgroup X := zpowers u ⊔ D' with hP
  have hPp : IsPGroup p P := IsPGroup.to_sup_of_normal_right hUp hD'p
  have hPcard : Nat.card P ≤ p ^ 4 := by
    have h1 : D'.relIndex P = D'.relIndex (zpowers u) :=
      CFSG.QuasithinUnique.C5.relIndex_sup_eq_of_le_normalizer
        (fun y _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hD'n]; exact mem_top y)
    have h2 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex (le_sup_right : D' ≤ P)
    have h3 : D'.relIndex (zpowers u) ≤ p := by
      have h4 := CFSG.QuasithinUnique.C5.card_eq_card_mul_relIndex
        (inf_le_right : D' ⊓ zpowers u ≤ zpowers u)
      rw [inf_relIndex_right, Nat.card_zpowers, hu] at h4
      rw [h4]
      exact Nat.le_mul_of_pos_left _ Nat.card_pos
    rw [h2, hD'card, h1]
    calc p ^ 3 * D'.relIndex (zpowers u) ≤ p ^ 3 * p := Nat.mul_le_mul_left _ h3
      _ = p ^ 4 := by ring
  haveI : Fact (IsPGroup p P) := ⟨hPp⟩
  have hclass : CFSG.NilpotencyClassLe 3 P := CFSG.nilpotencyClassLe_of_card_le_p_four hPcard
  have huP : u ∈ P := mem_sup_left (mem_zpowers u)
  have hf₀P : ι f₀ ∈ P := mem_sup_right ⟨(f₀ : R), f₀.2, rfl⟩
  have hxp : x ^ p = 1 := by
    have h := CFSG.pth_mul_eq_one_of_class3 (R := P) hp2 hp3 hclass
      (u := ⟨u, huP⟩) (v := ⟨ι f₀, hf₀P⟩)
      (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hup))
      (Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hDp' f₀, map_one]))
    have h' := congrArg Subtype.val h
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_one] at h'
    rw [hx]
    exact h'
  have hxR : x ∉ R := by
    intro hxR
    apply huR
    have h1 : u = x * (ι f₀)⁻¹ := by
      rw [hx]
      group
    rw [h1]
    exact mul_mem hxR (inv_mem (f₀ : R).2)
  have he1 : e ≠ 1 := fun h => he (h ▸ (center D).one_mem)
  have hE1 : IsElemAbelian p (zpowers (ι k)) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← map_pow, hDp' k, map_one])
  have hE1c : Nat.card (zpowers (ι k)) = p := by rw [Nat.card_zpowers, hιord k hk1]
  have hE1eq : zpowers (ι k) = (zpowers k).map ι := (MonoidHom.map_zpowers ι k).symm
  have hιe : ι e ∉ zpowers (ι k) := by
    rw [hE1eq]
    rintro ⟨z, hz, hze⟩
    apply he
    rw [← hι hze, ← hZk]
    exact hz
  have hιeE1 : ∀ y ∈ zpowers (ι k), Commute y (ι e) := by
    rw [hE1eq]
    rintro _ ⟨z, hz, rfl⟩
    change ι z * ι e = ι e * ι z
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp (hZk ▸ hz) e)]
  obtain ⟨hE2, hE2c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE1 (hιord e he1)
    hιeE1 hιe
  have hE2R : zpowers (ι k) ⊔ zpowers (ι e) ≤ R :=
    sup_le (zpowers_le.mpr (k : R).2) (zpowers_le.mpr (e : R).2)
  have hx1 : x ≠ 1 := fun h => hxR (h ▸ R.one_mem)
  have hxE2 : ∀ y ∈ zpowers (ι k) ⊔ zpowers (ι e), Commute y x := by
    have hle : zpowers (ι k) ⊔ zpowers (ι e) ≤ centralizer ({x} : Set X) := by
      refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
      · rw [mem_centralizer_singleton_iff]
        exact hxZ k hkZ
      · rw [mem_centralizer_singleton_iff]
        exact hxe'
    intro y hy
    exact mem_centralizer_singleton_iff.mp (hle hy)
  obtain ⟨hE3, hE3c⟩ := CFSG.Quasithin.exists_elemAbelian_sup_zpowers hE2
    (orderOf_eq_prime hxp hx1) hxE2 (fun h => hxR (hE2R h))
  rw [hE2c, hE1c, ← pow_two, ← pow_succ] at hE3c
  exact CFSG.SectionRank.le_pRank hp1 (le_top : _ ≤ (⊤ : Subgroup X)) hE3 hE3c

theorem sixSixOneRank_holds : SixSixOneRank := by
  intro p X _ _ hp hp3 hgen hcent hne hsymp hrk
  have hp2 : p ≠ 2 := by omega
  haveI : (CFSG.pCore p X).Normal := CFSG.pCore_normal
  have hRp : IsPGroup p (CFSG.pCore p X) := CFSG.pCore_isPGroup
  have hRmax : ∀ N : Subgroup X, N.Normal → IsPGroup p N → N ≤ CFSG.pCore p X :=
    fun N hN hNp => le_sSup ⟨hN, hNp⟩
  obtain ⟨D, hDc, hDp, hcard, hnc, hker⟩ := exists_extraspecial_char hp hp2 hRp hsymp hrk
  haveI := hDc
  obtain ⟨u, hu, huR⟩ : ∃ u : X, orderOf u = p ∧ u ∉ CFSG.pCore p X := by
    by_contra h
    push Not at h
    apply hne
    rw [eq_top_iff, ← hgen]
    exact (closure_le _).mpr fun x hx => h x hx
  exact le_antisymm (pRank_top_le_three hp hRp hRmax hcent hrk.le D hcard hnc hker)
    (three_le_pRank_top hp hp3 hRp hRmax hcent D hDp hcard hnc hker hu huR)

end CFSG.LocalAnalysis.RankThreeUC.AGL81C

end
