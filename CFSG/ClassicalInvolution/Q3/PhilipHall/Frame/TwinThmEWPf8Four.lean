module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf8Hom
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWHull
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEWPf7Norm
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Hyp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf5Path
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Cls

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section FourC

variable [PrintedQuotOdd] [PrintedQuotCent] [PrintedHull]

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G}
  {S : Sylow 2 G} {R W H : Subgroup G}

private theorem sq_eq_of_orderOf_four' {J : Subgroup G} {z u : G} (hz : IsUniqueInvolution J z)
    (hu : u ∈ J) (h4 : orderOf u = 4) : u * u = z := by
  have h1 : (u * u) * (u * u) = 1 := by
    have := pow_orderOf_eq_one u
    rw [h4] at this
    calc (u * u) * (u * u) = u ^ 4 := by simp [pow_succ, mul_assoc]
      _ = 1 := this
  rcases hz.unique (u * u) (J.mul_mem hu hu) h1 with h | h
  · exfalso
    have : orderOf u ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
    rw [h4] at this
    omega
  · exact h

theorem MinCexQ8.fourGroup' (c : MinCexQ8 Ω K S R W H) {K' : Subgroup G} (hK' : K' ∈ twinSet Ω K)
    (hK'ne : K' ≠ K) {R' : Subgroup G} (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hRR'2 : IsPGroup 2 ↥(R ⊔ R')) :
    ∃ U : Subgroup G, U ≤ R ⊔ R' ∧ (∀ x ∈ U, ∀ y ∈ U, x * y = y * x) ∧
      (∀ x ∈ U, x * x = 1) ∧ 4 ≤ Nat.card U ∧
      ∀ e ∈ U, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ H := by
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  obtain ⟨hK'Ω, z, hzK, hzK'⟩ := hK'
  obtain ⟨S₂, hS₂⟩ := hRR'2.exists_le_sylow
  have hRS₂ : R ≤ (S₂ : Subgroup G) := le_sup_left.trans hS₂
  have hR'S₂ : R' ≤ (S₂ : Subgroup G) := le_sup_right.trans hS₂
  have hcz : Subgroup.centralizer ({z} : Set G) ≤ H := c.centralizer_le hzK
  obtain ⟨x, -, -, hW₂, hW₂S, -, hCW₂⟩ := exists_W_of_sylow hΩ hK c.hyp.trans hzK hcz hRR hRK hRS
    c.stand.hW.1 c.stand.hW.2.1 c.stand.hW.2.2 c.hyp.cent hRR hRK hRS₂
  obtain ⟨u₁, hu₁W, hu₁4, hu₁R⟩ := exists_order_four_inf_W hΩ hW₂ hW₂S hK hRR hRK hRS₂
  obtain ⟨u₂, hu₂W, hu₂4, hu₂R'⟩ := exists_order_four_inf_W hΩ hW₂ hW₂S hK'Ω hR' hR'K' hR'S₂
  have hu₁K : u₁ ∈ K := hRK hu₁R
  have hu₂K' : u₂ ∈ K' := hR'K' hu₂R'
  have hcomm' : Commutes R R' :=
    hΩ.commutes_of_twin_of_isPGroup hK hK'Ω (Ne.symm hK'ne) hzK hzK' hRK hR'K' hRR'2
  have hsq₁ : u₁ * u₁ = z := sq_eq_of_orderOf_four' hzK hu₁K hu₁4
  have hsq₂ : u₂ * u₂ = z := sq_eq_of_orderOf_four' hzK' hu₂K' hu₂4
  have hzR : z ∈ R := hsq₁ ▸ R.mul_mem hu₁R hu₁R
  have hdisj : ∀ {u : G}, u ∈ K → u ∈ K' → orderOf u = 4 → False := by
    intro u huK huK' hu4
    have := hΩ.eq_of_le_of_le hK hK'Ω
      (IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu4]; norm_num))
      (by rw [Nat.card_zpowers, hu4]) (Subgroup.zpowers_le.mpr huK)
      (Subgroup.zpowers_le.mpr huK')
    exact hK'ne this.symm
  have hu₂K : u₂ ∉ K := fun h => hdisj h hu₂K' hu₂4
  set a : G := u₁ * u₂⁻¹ with ha
  have haR : a ∈ R ⊔ R' :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left hu₁R)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_right hu₂R'))
  have hc : u₂⁻¹ * u₁ = u₁ * u₂⁻¹ := (hcomm' u₁ hu₁R u₂⁻¹ (R'.inv_mem hu₂R')).symm
  have haa : a * a = 1 := by
    have h2inv : u₂⁻¹ * u₂⁻¹ = z⁻¹ := by
      rw [← hsq₂, mul_inv_rev]
    calc a * a = u₁ * (u₂⁻¹ * u₁) * u₂⁻¹ := by rw [ha]; group
      _ = u₁ * (u₁ * u₂⁻¹) * u₂⁻¹ := by rw [hc]
      _ = (u₁ * u₁) * (u₂⁻¹ * u₂⁻¹) := by group
      _ = z * z⁻¹ := by rw [hsq₁, h2inv]
      _ = 1 := mul_inv_cancel z
  have haK : a ∉ K := by
    intro haK
    apply hu₂K
    have : u₂⁻¹ = u₁⁻¹ * a := by rw [ha]; group
    have h' : u₂⁻¹ ∈ K := this ▸ K.mul_mem (K.inv_mem hu₁K) haK
    simpa using K.inv_mem h'
  have hzK_mem : z ∈ K := hzK.mem
  have ha1 : a ≠ 1 := fun h => haK (h ▸ K.one_mem)
  have hza : z * a = a * z := by
    have hzu₁ : z * u₁ = u₁ * z := by rw [← hsq₁]; group
    have hzu₂ : z * u₂⁻¹ = u₂⁻¹ * z := hcomm' z hzR u₂⁻¹ (R'.inv_mem hu₂R')
    calc z * a = (z * u₁) * u₂⁻¹ := by rw [ha]; group
      _ = u₁ * (z * u₂⁻¹) := by rw [hzu₁]; group
      _ = u₁ * (u₂⁻¹ * z) := by rw [hzu₂]
      _ = a * z := by rw [ha]; group
  set U : Subgroup G := Subgroup.closure ({z, a} : Set G) with hU
  have hURR : U ≤ R ⊔ R' := by
    rw [hU, Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · exact Subgroup.mem_sup_left hzR
    · exact haR
  have hkcomm : ∀ x ∈ ({z, a} : Set G), ∀ y ∈ ({z, a} : Set G), x * y = y * x := by
    intro x hx y hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hza
    · exact hza.symm
    · rfl
  have hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    letI := Subgroup.closureCommGroupOfComm (fun x hx y hy _ => hkcomm x hx y hy)
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : U) ⟨y, hy⟩)
  have hsq : ∀ x ∈ U, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact hzK.sq
      · exact haa
    | one => simp
    | mul x y hx hy ihx ihy =>
      have hxy : y * x = x * y := (hcomm x hx y hy).symm
      calc x * y * (x * y) = x * (y * x) * y := by group
        _ = x * (x * y) * y := by rw [hxy]
        _ = (x * x) * (y * y) := by group
        _ = 1 := by rw [ihx, ihy]; simp
    | inv x hx ihx =>
      calc x⁻¹ * x⁻¹ = (x * x)⁻¹ := by group
        _ = 1 := by rw [ihx]; simp
  have hcard : 4 ≤ Nat.card U := by
    have hz2 : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hzK.sq) hzK.ne_one
    have hH1U : Subgroup.zpowers z ≤ U :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
    have hc2 : Nat.card (Subgroup.zpowers z) = 2 := by rw [Nat.card_zpowers, hz2]
    have hdvd : 2 ∣ Nat.card U := hc2 ▸ Subgroup.card_dvd_of_le hH1U
    have hne : Subgroup.zpowers z ≠ U := by
      intro h
      have haU : a ∈ U := Subgroup.subset_closure (by simp)
      rw [← h] at haU
      exact haK (Subgroup.zpowers_le.mpr hzK_mem haU)
    have hlt : 2 < Nat.card U := by
      by_contra hle
      have hle' := not_lt.mp hle
      exact hne (Subgroup.eq_of_le_of_card_ge hH1U (by omega))
    obtain ⟨m, hm⟩ := hdvd
    omega
  refine ⟨U, hURR, hcomm, hsq, hcard, fun e he he1 => ?_⟩
  have hKperp : K' ∈ KPerp Ω K := by
    refine Set.mem_insert_of_mem _ ⟨hK'Ω, hK'ne, R', hR', hR'K', fun x hx => ?_⟩
    exact hΩ.le_normalizer_of_twin hK'Ω hK hK'ne hzK' hzK (hR'K' hx)
  have hzW₂ : z ∈ conjSub x W := hsq₁ ▸ (conjSub x W).mul_mem hu₁W.2 hu₁W.2
  have haW₂ : a ∈ conjSub x W := (conjSub x W).mul_mem hu₁W.2 ((conjSub x W).inv_mem hu₂W.2)
  have hUW : U ≤ conjSub x W := by
    rw [hU, Subgroup.closure_le]
    rintro y (rfl | rfl)
    · exact hzW₂
    · exact haW₂
  exact hCW₂ K hK (inf_W_mem_USet' hΩ hW₂ hW₂S hK hRR hRK hRS₂) K' hKperp R R' hRR hRK hRS₂ hR'
    hR'K' hR'S₂ (Or.inl hcomm') e (hURR he) (hUW he) he1 (hsq e he)

theorem MinCexQ8.oddCoreOf_le' (c : MinCexQ8 Ω K S R W H) {K' : Subgroup G}
    (hK' : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G} (hR' : R' ∈ RSet Ω)
    (hR'K' : R' ≤ K') (hRR'2 : IsPGroup 2 ↥(R ⊔ R')) {Y : Subgroup G} (hY : R ⊔ R' ≤ Y) :
    oddCoreOf Y ≤ H := by
  obtain ⟨U, hUR, hcomm, hsq, hU4, hC⟩ := c.fourGroup' hK' hK'ne hR' hR'K' hRR'2
  have hUY : U ≤ Y := hUR.trans hY
  have : IsMulCommutative ↥U := ⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩
  exact CFSG.Goldschmidt.LemmaX.le_of_forall_inf_centralizer_le (E := U) (N := oddCoreOf Y)
    (J := H) this (fun x hx => by rw [pow_two]; exact hsq x hx) hU4
    (fun u hu => mem_normalizer_oddCoreOf (hUY hu)) (odd_natCard_oddCoreOf Y)
    (fun e he he1 => inf_le_right.trans (hC e he he1))

theorem MinCexQ8.e18_4C (c : MinCexQ8 Ω K S R W H) (hT4 : Thm4RTwinBelow 3 (Nat.card G))
    {K' : Subgroup G} (hK'tw : K' ∈ twinSet Ω K) (hK'ne : K' ≠ K) {R' : Subgroup G}
    (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K') (hRR2 : IsPGroup 2 ↥(R ⊔ R')) {w : G} (hw1 : w ≠ 1)
    (hw2 : w * w = 1) (hRw : R ⊔ R' ≤ Subgroup.centralizer ({w} : Set G))
    (hX : Subgroup.centralizer ({w} : Set G) ≠ ⊤) :
    Subgroup.centralizer ({w} : Set G) ≤ H := by
  set C := Subgroup.centralizer ({w} : Set G) with hCdef
  have hΩ : HypOmegaGen Ω := c.stand.hyp
  have hEA : EtaAbelian Ω := etaAbelian_of_gen hΩ
  have hEM : EtaMeet Ω := etaMeet_of_gen hΩ
  have hK : K ∈ Ω := c.stand.mem
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  have hK'Ω : K' ∈ Ω := hK'tw.1
  have hc2 : IsPGroup 2 (Subgroup.zpowers w) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hw2) hw1]
      norm_num)
  have hRsyl : IsSylow2In R K := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hRR hRK
  have hR'syl : IsSylow2In R' K' := Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK'Ω hR' hR'K'
  have hRC : R ≤ C := le_sup_left.trans hRw
  have hR'C : R' ≤ C := le_sup_right.trans hRw
  have hKm : K ∈ tqMembers3 Ω w :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ c.stand.two hK ⟨R, hRsyl, hRC⟩⟩
  have hK'm : K' ∈ tqMembers3 Ω w :=
    ⟨hK'Ω, TwinADescent3.mem_tq_of_sylCent hΩ c.stand.two hK'Ω ⟨R', hR'syl, hR'C⟩⟩
  have hAΩ : ∀ L ∈ Ω, AEmpty Ω L :=
    aEmpty_forall_of_transitive hΩ.conjInvariant (e18_3Q8 G Ω K S R W H c) c.stand.aEmpty
  have hq8 : ∀ M ∈ Ω, ∀ P : Subgroup G, IsSylow2In P M → Nonempty (↥P ≃* QuaternionGroup 2) :=
    fun M hM => forall_sylow_iso_of_exists (c.stand.q8 M hM)
  set X : Subgroup ↥C := coreHull Ω w with hXdef
  set ι := secEmb Ω w with hιdef
  have hι : Function.Injective ι := secEmb_injective
  have hXlt : Nat.card ↥X < Nat.card G :=
    (Subgroup.card_le_card_group X).trans_lt (natCard_lt_of_ne_top hX)
  have hΛ : HypOmegaGen (hullFam Ω w) :=
    hypOmegaGen_restrict (TwinADescent.hypOmegaGen_coreFamily hΩ hc2) X
  have hΛq8 := hullFam_q8 hc2 hq8
  have hΛ2 := hullFam_twoGroup (w := w) c.stand.two
  have hΛcls := classicalClause_of_q8 hΛ hΛq8 hΛ2
  have hRs : IsSylow2In R (TwinADescent.coreAt w K) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hKm.2).mpr ⟨hRsyl, hRC⟩
  have hR's : IsSylow2In R' (TwinADescent.coreAt w K') :=
    (TwinADescent.isSylow2In_coreAt_iff hc2 hK'm.2).mpr ⟨hR'syl, hR'C⟩
  have hR₁syl : IsSylow2In ((R.subgroupOf C).subgroupOf X) (secOf Ω w K) :=
    (hRs.subgroupOf (TwinADescent.coreAt_le_centralizer w K)).subgroupOf (le_coreHull hKm)
  have hR₁'syl : IsSylow2In ((R'.subgroupOf C).subgroupOf X) (secOf Ω w K') :=
    (hR's.subgroupOf (TwinADescent.coreAt_le_centralizer w K')).subgroupOf (le_coreHull hK'm)
  have hR₁ : (R.subgroupOf C).subgroupOf X ∈ RSet (hullFam Ω w) :=
    mem_RSet_of_isSylow2In (secOf_mem_hullFam hKm) hR₁syl
  have hR₁' : (R'.subgroupOf C).subgroupOf X ∈ RSet (hullFam Ω w) :=
    mem_RSet_of_isSylow2In (secOf_mem_hullFam hK'm) hR₁'syl
  have hRCX : R.subgroupOf C ≤ X :=
    (Subgroup.subgroupOf_mono _ hRs.1).trans (le_coreHull hKm)
  have hR'CX : R'.subgroupOf C ≤ X :=
    (Subgroup.subgroupOf_mono _ hR's.1).trans (le_coreHull hK'm)
  have hmapR : ((R.subgroupOf C).subgroupOf X).map ι = R := by
    rw [hιdef]
    unfold secEmb
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hRCX,
      Subgroup.map_subgroupOf_eq_of_le hRC]
  have hmapR' : ((R'.subgroupOf C).subgroupOf X).map ι = R' := by
    rw [hιdef]
    unfold secEmb
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hR'CX,
      Subgroup.map_subgroupOf_eq_of_le hR'C]
  have hRR'₁2 : IsPGroup 2 ↥(((R.subgroupOf C).subgroupOf X) ⊔ ((R'.subgroupOf C).subgroupOf X)) := by
    have hmap : (((R.subgroupOf C).subgroupOf X) ⊔ ((R'.subgroupOf C).subgroupOf X)).map ι =
        R ⊔ R' := by rw [Subgroup.map_sup, hmapR, hmapR']
    have e : ↥(((R.subgroupOf C).subgroupOf X) ⊔ ((R'.subgroupOf C).subgroupOf X)) ≃*
        ↥(R ⊔ R') :=
      (Subgroup.equivMapOfInjective _ ι hι).trans (MulEquiv.subgroupCongr hmap)
    exact hRR2.of_equiv e.symm
  obtain ⟨S₁, hS₁⟩ := hRR'₁2.exists_le_sylow
  have hK₁' : secOf Ω w K' ∈ twinSet (hullFam Ω w) (secOf Ω w K) := by
    obtain ⟨-, z, hz, hzK'⟩ := hK'tw
    have e1 : TwinADescent.coreAt w K' ∈
        twinSet (TwinADescent.coreFamily Ω w) (TwinADescent.coreAt w K) :=
      ⟨TwinADescent.coreAt_mem_coreFamily hK'm, z, isUniqueInvolution_coreAt_of_tq hΩ hc2 hKm hz,
        isUniqueInvolution_coreAt_of_tq hΩ hc2 hK'm hzK'⟩
    have e2 := twinSet_subgroupOf (TwinADescent.coreAt_le_centralizer w K)
      (TwinADescent.coreAt_le_centralizer w K') e1
    exact twinSet_subgroupOf (le_coreHull hKm) (le_coreHull hK'm) e2
  have hne₁ : secOf Ω w K' ≠ secOf Ω w K := by
    have h0 : TwinADescent.coreAt w K' ≠ TwinADescent.coreAt w K :=
      fun h => hK'ne (eq_of_coreAt_eq hΩ hc2 hK'm hKm h)
    exact subgroupOf_ne_of_ne (le_coreHull hKm) (le_coreHull hK'm)
      (subgroupOf_ne_of_ne (TwinADescent.coreAt_le_centralizer w K)
        (TwinADescent.coreAt_le_centralizer w K') h0)
  have hoc : oddCoreOf C ≤ H := c.oddCoreOf_le' hK'tw hK'ne hR' hR'K' hRR2 hRw
  have hNH : ∀ n ∈ classicalInvolutionOddCore ↥X, ι n ∈ H :=
    fun n hn => hoc (oddCore_coreHull_le hΩ hc2 hn)
  have hY1 : (∀ J ∈ hullFam Ω w, ∃ y : ↥X, conjSub y (secOf Ω w K) = J) →
      ∀ J ∈ dstarComp (hullFam Ω w) (secOf Ω w K),
        ∃ h ∈ H.comap ι, conjSub h (secOf Ω w K) = J := by
    intro hall J hJ
    have hJΛ : J ∈ hullFam Ω w := by
      rcases dstarComp_subset_insert _ hJ with h | h
      · rw [h]
        exact secOf_mem_hullFam hKm
      · exact h
    obtain ⟨y, rfl⟩ := hall J hJΛ
    refine ⟨y, ?_, rfl⟩
    obtain ⟨J₀, hJ₀, hJ₀eq, hJ₀K⟩ := coreGood_of_mem_dstarComp hΩ hc2 hKm hJ
    have hJ₀conj : J₀ = conjSub (ι y) K :=
      eq_conjSub_of_hull_eq hΩ hc2 hKm hJ₀ y hJ₀eq.symm
    exact Subgroup.mem_comap.mpr ((e18_1Q8 G Ω K S R W H c).1 (ι y) (hJ₀conj ▸ hJ₀K))
  have hWex := PrintedHull.exists_W G Ω K S R W H w c hw1 hw2 S₁ (by
    rw [← hmapR]
    exact Subgroup.map_mono (le_sup_left.trans hS₁))
  have hsec := c.section_le_H_hom hT4 ι hι hXlt hΛ hΛcls hΛq8 hΛ2 S₁
    (secOf_mem_hullFam hKm) hK₁' hne₁ hR₁ (hR₁syl.1) (le_sup_left.trans hS₁) hR₁'
    (hR₁'syl.1) (le_sup_right.trans hS₁) hNH hY1 hWex (coreGood Ω w K)
    ⟨K, hKm, rfl, Relation.ReflTransGen.refl⟩
    (fun L _ L' hL' hg hadj => coreGood_step hΩ hc2 hL' hg hadj)
    (fun L _ hg => by
      obtain ⟨J, hJ, rfl, hJK⟩ := hg
      rw [map_secOf hJ]
      exact (TwinADescent.coreAt_le_left w J).trans (c.le_H_of_mem_dstarComp hJK))
    (fun _ => TwinADescent3.aEmpty_restrict_coreFamily hΩ hAΩ hc2 X)
  set Y : Subgroup G := X.map C.subtype with hYdef
  have hYH : Y ≤ H := by
    rw [hYdef, hXdef]
    unfold coreHull
    rw [Subgroup.map_iSup]
    refine iSup_le fun L => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hL => ?_
    obtain ⟨_, ⟨J, hJ, rfl⟩, -, rfl⟩ := hL
    rw [Subgroup.map_subgroupOf_eq_of_le (TwinADescent.coreAt_le_centralizer w J)]
    have := hsec _ (secOf_mem_hullFam hJ)
    rwa [map_secOf hJ] at this
  have hRY : R ≤ Y := by
    rw [← hmapR, hιdef]
    unfold secEmb
    rw [← Subgroup.map_map]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hCN : ∀ g ∈ C, conjSub g Y = Y := by
    intro g hg
    have := conjSub_map C.subtype (⟨g, hg⟩ : ↥C) X
    rw [hXdef, conjSub_coreHull hΩ hc2] at this
    exact this
  intro x hx
  exact c.normalizer_le_of_le hEA hEM hRY hYH (mem_normalizer_iff_conjSub_eq.mpr (hCN x hx))

end FourC

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
