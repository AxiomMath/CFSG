module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Defs
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLT237
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLSecV
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLTwin

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

section WSet

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem inf_wSet_of_card (hΦ : HypOmegaGen Φ) (h2 : ∀ L ∈ Φ, IsPGroup 2 ↥L)
    (h8 : ∀ L ∈ Φ, Nat.card ↥L = 2 ^ 3) {W : Subgroup X} (hW1 : WSet Φ = {W}) :
    ∀ L ∈ Φ, Nat.card ↥(L ⊓ W) = 4 ∧ IsCyclic ↥(L ⊓ W) := by
  intro L hL
  have hW : W ∈ WSet Φ := by rw [hW1]; rfl
  have hWn : ∀ g : X, conjSub g W = W := fun g => by
    have := WSet.conj hΦ.conjInvariant hW g
    rwa [hW1] at this
  have hLsyl : IsSylow2In L L := ⟨le_rfl, h2 L hL, fun V' hVL _ hLV => le_antisymm hVL hLV⟩
  have hLD : L ∈ DSet Φ W :=
    ⟨mem_RSet_of_isSylow2In hL hLsyl, fun x _ => mem_normalizer_iff_conjSub_eq.mpr (hWn x)⟩
  obtain ⟨-, -, hcyc, -, hcard⟩ := Q3CL.Thompson.inf_W_of_mem_D hΦ hW hLD hL hLsyl
  have h8' : Nat.card ↥L = 8 := by rw [h8 L hL]; norm_num
  exact ⟨by omega, hcyc⟩

end WSet

section Frattini

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_eq_of_cover {E E₀ P : Subgroup G} (hE₀E : E₀ ≤ E)
    (hcov : E ≤ oddCoreOf E ⊔ E₀) (hPE₀ : P ≤ E₀) (hP2 : IsPGroup 2 ↥P) {x : G} (hxE : x ∈ E)
    (hxP : conjSub x P = P) :
    ∃ x₀ ∈ E₀, conjSub x₀ P = P ∧ ∀ q ∈ P, x₀ * q * x₀⁻¹ = x * q * x⁻¹ := by
  have hEN : E ≤ Subgroup.normalizer (oddCoreOf E : Set G) := fun y hy =>
    CFSG.ClassicalInvolution.Asc77.mem_normalizer_oddCoreOf hy
  have hxE' : x ∈ ((oddCoreOf E ⊔ E₀ : Subgroup G) : Set G) := hcov hxE
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hE₀E.trans hEN)] at hxE'
  obtain ⟨o, ho, x₁, hx₁, rfl⟩ := hxE'
  have hx₁E : x₁ ∈ E := hE₀E hx₁
  set N : Subgroup ↥E₀ := (oddCoreOf E).subgroupOf E₀ with hN
  haveI hNn : N.Normal := ⟨fun m hm g => by
    rw [hN, Subgroup.mem_subgroupOf] at hm ⊢
    exact T7R.conj_mem_oddCoreOf (hE₀E g.2) hm⟩
  have hNodd : Odd (Nat.card N) := by
    have h1 : N.map E₀.subtype ≤ oddCoreOf E := Subgroup.map_comap_le _ _
    rw [← Subgroup.card_map_of_injective E₀.subtype_injective]
    exact (oddCoreOf_odd_natCard E).of_dvd_nat (Subgroup.card_dvd_of_le h1)
  set A : Subgroup ↥E₀ := (conjSub x₁ P).subgroupOf E₀ with hA
  set B : Subgroup ↥E₀ := P.subgroupOf E₀ with hB
  have hA2 : IsPGroup 2 ↥A := (isPGroup_conjSub x₁ hP2).comap_subtype
  have hB2 : IsPGroup 2 ↥B := hP2.comap_subtype
  have hmap : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N) := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      have ha' : x₁⁻¹ * (a : G) * x₁ ∈ P := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp ha)
      have hb : o * x₁ * (x₁⁻¹ * (a : G) * x₁) * (o * x₁)⁻¹ ∈ P := by
        have := conj_mem_conjSub (n := o * x₁) ha'
        rwa [hxP] at this
      refine ⟨⟨_, hPE₀ hb⟩, Subgroup.mem_subgroupOf.mpr hb, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
        Subgroup.mem_subgroupOf]
      show (o * x₁ * (x₁⁻¹ * (a : G) * x₁) * (o * x₁)⁻¹)⁻¹ * (a : G) ∈ oddCoreOf E
      have e : (o * x₁ * (x₁⁻¹ * (a : G) * x₁) * (o * x₁)⁻¹)⁻¹ * (a : G) =
          o * ((a : G)⁻¹ * o⁻¹ * ((a : G)⁻¹)⁻¹) := by group
      rw [e]
      exact (oddCoreOf E).mul_mem ho
        (T7R.conj_mem_oddCoreOf (E.inv_mem (hE₀E a.2)) ((oddCoreOf E).inv_mem ho))
    · rintro _ ⟨b, hb, rfl⟩
      have hb' : (b : G) ∈ P := Subgroup.mem_subgroupOf.mp hb
      have hp : (o * x₁)⁻¹ * (b : G) * (o * x₁) ∈ P := by
        have : (b : G) ∈ conjSub (o * x₁) P := by rw [hxP]; exact hb'
        exact mem_conjSub_iff.mp this
      have ha : x₁ * ((o * x₁)⁻¹ * (b : G) * (o * x₁)) * x₁⁻¹ ∈ conjSub x₁ P :=
        conj_mem_conjSub hp
      have haE₀ : x₁ * ((o * x₁)⁻¹ * (b : G) * (o * x₁)) * x₁⁻¹ ∈ E₀ :=
        E₀.mul_mem (E₀.mul_mem hx₁ (hPE₀ hp)) (E₀.inv_mem hx₁)
      refine ⟨⟨_, haE₀⟩, Subgroup.mem_subgroupOf.mpr ha, ?_⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
        Subgroup.mem_subgroupOf]
      show (x₁ * ((o * x₁)⁻¹ * (b : G) * (o * x₁)) * x₁⁻¹)⁻¹ * (b : G) ∈ oddCoreOf E
      have e : (x₁ * ((o * x₁)⁻¹ * (b : G) * (o * x₁)) * x₁⁻¹)⁻¹ * (b : G) =
          o⁻¹ * ((b : G)⁻¹ * o * ((b : G)⁻¹)⁻¹) := by group
      rw [e]
      exact (oddCoreOf E).mul_mem ((oddCoreOf E).inv_mem ho)
        (T7R.conj_mem_oddCoreOf (E.inv_mem (hE₀E b.2)) ho)
  obtain ⟨m, hmN, hmA⟩ := TwinPerp23.exists_odd_conj N hNodd hA2 hB2 hmap
  have hmO : (m : G) ∈ oddCoreOf E := Subgroup.mem_subgroupOf.mp hmN
  have hle : conjSub (m : G) (conjSub x₁ P) ≤ E₀ := by
    have := conjSub_mono (n := (m : G)) (conjSub_mono (n := x₁) hPE₀)
    rwa [conjSub_eq_self_of_mem hx₁, conjSub_eq_self_of_mem m.2] at this
  have h1 : (conjSub (m : G) (conjSub x₁ P)).subgroupOf E₀ = P.subgroupOf E₀ := by
    rw [← conjSub_subgroupOf E₀ m (conjSub x₁ P)]
    exact hmA
  have h2 := Subgroup.subgroupOf_inj.mp h1
  rw [inf_eq_left.mpr hle, inf_eq_left.mpr hPE₀] at h2
  have hx₀P : conjSub ((m : G) * x₁) P = P := by rw [conjSub_mul]; exact h2
  refine ⟨(m : G) * x₁, E₀.mul_mem m.2 hx₁, hx₀P, fun q hq => ?_⟩
  have hr : o * x₁ * q * (o * x₁)⁻¹ ∈ P := by
    have := conj_mem_conjSub (n := o * x₁) hq
    rwa [hxP] at this
  have hs : (m : G) * x₁ * q * ((m : G) * x₁)⁻¹ ∈ P := by
    have := conj_mem_conjSub (n := (m : G) * x₁) hq
    rwa [hx₀P] at this
  have hsE : (x₁ * q * x₁⁻¹)⁻¹ ∈ E :=
    E.inv_mem (E.mul_mem (E.mul_mem hx₁E (hE₀E (hPE₀ hq))) (E.inv_mem hx₁E))
  have hmem : (o * x₁ * q * (o * x₁)⁻¹)⁻¹ * ((m : G) * x₁ * q * ((m : G) * x₁)⁻¹) ∈
      oddCoreOf E := by
    have e : (o * x₁ * q * (o * x₁)⁻¹)⁻¹ * ((m : G) * x₁ * q * ((m : G) * x₁)⁻¹) =
        o * ((x₁ * q * x₁⁻¹)⁻¹ * (o⁻¹ * (m : G)) * ((x₁ * q * x₁⁻¹)⁻¹)⁻¹) * (m : G)⁻¹ := by
      group
    rw [e]
    exact (oddCoreOf E).mul_mem ((oddCoreOf E).mul_mem ho
      (T7R.conj_mem_oddCoreOf hsE ((oddCoreOf E).mul_mem ((oddCoreOf E).inv_mem ho) hmO)))
      ((oddCoreOf E).inv_mem hmO)
  have hPmem : (o * x₁ * q * (o * x₁)⁻¹)⁻¹ * ((m : G) * x₁ * q * ((m : G) * x₁)⁻¹) ∈ P :=
    P.mul_mem (P.inv_mem hr) hs
  have h3 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard E) hmem
    (hP2.to_le (Subgroup.zpowers_le.mpr hPmem))
  exact (inv_mul_eq_one.mp h3).symm

end Frattini


section Fus

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem exists_fus_rLayer (hc : P23Cfg n Y R S t K' W u e g) (hA6 : SecAE R e 6)
    {P : Subgroup Y} (hP : IsSylow2In P (tightCore R))
    (hPe : P ≤ Subgroup.centralizer ({e} : Set Y)) :
    ∃ x ∈ rLayer (Om R) e, (∀ q ∈ P, x * q * x⁻¹ ∈ P) ∧
      ∀ q ∈ P, q ^ 2 ≠ 1 → x * q * x⁻¹ ≠ q ∧ x * q * x⁻¹ ≠ q⁻¹ := by
  classical
  obtain ⟨I⟩ := hA6
  have hΩ : HypOmegaGen (Om R) := (om_facts hc).1
  have h2Ω : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    (om_facts hc).2.2.1
  have hc2' : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hc.data.he2
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hJ : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK₀, TwinADescent3.mem_tq_of_sylCent hΩ h2Ω hK₀ ⟨P, hP, hPe⟩⟩
  have hS := p23_q8Section hc.std.perp hc.data.he2
  have h2all := TwinDisc.AE5.members_twoN (by norm_num : 5 ≤ 6) hS I
  obtain ⟨xb, hxbodd, hxbN, hxbmove⟩ :=
    Fus.ae_fusion_section (by norm_num : 5 ≤ 6) hS I (TwinDisc.secImg_mem_secFam hJ)
  set C := Subgroup.centralizer ({e} : Set Y) with hCdef
  set H := TwinDisc.coreHull (Om R) e with hHdef
  set N := classicalInvolutionOddCore ↥H with hNdef
  set π := QuotientGroup.mk' N with hπ
  set A : Subgroup ↥H := (P.subgroupOf C).subgroupOf H with hAdef
  have hAmap : A.map π = TwinDisc.secImg (Om R) e (tightCore R) :=
    Fus.map_syl_eq_secImg hc2' hJ hP hPe (h2all _ (TwinDisc.secImg_mem_secFam hJ))
  have hNodd : Odd (Nat.card N) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hA2 : IsPGroup 2 ↥A :=
    (hP.2.1.comap_of_injective C.subtype C.subtype_injective).comap_of_injective
      H.subtype H.subtype_injective
  have hAQ : ∀ a ∈ A, (((a : ↥H) : ↥C) : Y) ∈ P := fun a ha =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_subgroupOf.mp ha)
  have hxA : xb ∈ Subgroup.normalizer ((A.map π : Subgroup (↥H ⧸ N)) : Set (↥H ⧸ N)) := by
    rw [hAmap]; exact hxbN
  obtain ⟨x₂, -, hx₂π, hx₂A, -⟩ :=
    Fus.lift_odd_normalizing N hNodd hA2 (IsPGroup.of_bot (p := 2) (G := ↥H))
      (fun a _ b hb => by rw [Subgroup.mem_bot.mp hb, mul_one, one_mul]) hxbodd hxA
      (fun b hb => by rw [Subgroup.mem_bot.mp hb, map_one, mul_one, one_mul])
  have hTs : IsSylow2In P (TwinADescent.coreAt e (tightCore R)) :=
    (TwinADescent.isSylow2In_coreAt_iff hc2' hJ.2).mpr ⟨hP, hPe⟩
  have hqA : ∀ q ∈ P, ∃ a ∈ A, (((a : ↥H) : ↥C) : Y) = q := by
    intro q hq
    have hqC : q ∈ C := hPe hq
    have hqH : (⟨q, hqC⟩ : ↥C) ∈ H :=
      TwinDisc.le_coreHull hJ (Subgroup.mem_subgroupOf.mpr (hTs.1 hq))
    exact ⟨⟨⟨q, hqC⟩, hqH⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have hAN : A ⊓ N = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd N hA2 le_rfl
      (hNodd.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left))
  have hmap : H.map C.subtype = rLayer (Om R) e :=
    TwinPerpV3.coreHull_map_eq_rLayer hΩ hc2' h2Ω
  refine ⟨(((x₂ : ↥H) : ↥C) : Y), ?_, ?_, ?_⟩
  · rw [← hmap]
    exact ⟨(x₂ : ↥C), x₂.2, rfl⟩
  · intro q hq
    obtain ⟨a, ha, rfl⟩ := hqA q hq
    exact hAQ _ (hx₂A a ha)
  · intro q hq hq2
    obtain ⟨a, ha, rfl⟩ := hqA q hq
    have hja : π a ∈ TwinDisc.secImg (Om R) e (tightCore R) := hAmap ▸ ⟨a, ha, rfl⟩
    have hj2 : (π a) ^ 2 ≠ 1 := by
      intro h
      apply hq2
      have hπa2 : π (a ^ 2) = 1 := by rw [map_pow]; exact h
      have h1 : a ^ 2 ∈ A ⊓ N := ⟨A.pow_mem ha 2, (QuotientGroup.eq_one_iff _).mp hπa2⟩
      rw [hAN, Subgroup.mem_bot] at h1
      have h2 := congrArg (fun z : ↥H => (((z : ↥H) : ↥C) : Y)) h1
      simpa [pow_two] using h2
    obtain ⟨hm1, hm2⟩ := hxbmove _ hja hj2
    constructor
    · intro h
      apply hm1
      have h1 : x₂ * a * x₂⁻¹ = a := Subtype.ext (Subtype.ext h)
      rw [← hx₂π, ← map_inv, ← map_mul, ← map_mul, h1]
    · intro h
      apply hm2
      have h1 : x₂ * a * x₂⁻¹ = a⁻¹ := Subtype.ext (Subtype.ext h)
      rw [← hx₂π, ← map_inv, ← map_mul, ← map_mul, h1, map_inv]

end Fus

section Main

theorem l7NoW_of_coreTwo {n : ℕ} (hL1 : L7CoreTwo n) : L7NoW n := by
  intro hcit hP Y _ _ R S t K' W u e g Z f ctx ⟨Wh, hW⟩
  have hL := hL1 hcit hP Y R S t K' W u e g Z f ctx
  set V := aSub R Z e ⊓ aSub R Z f with hVdef
  set X := rLayerSub (Om R) V with hXdef
  have hc := ctx.cfg
  have hZd := ctx.zdata
  have hVZ : V ≤ Z := inf_le_left.trans (aSub_le R Z e)
  have hΦΩ := p23SecFamV_hypOmegaGen hc hZd hVZ hL
  have hWmem : Wh ∈ WSet (p23SecFamV R V) := by rw [hW]; rfl
  have hWn : ∀ y : SecQuot X, conjSub y Wh = Wh := fun y => by
    have h1 := WSet.conj hΦΩ.conjInvariant hWmem y
    rwa [hW] at h1
  have h4 := inf_wSet_of_card hΦΩ (p23SecFamV_isPGroup hL) (p23SecFamV_card hc hL) hW
  have hVeZ : V ⊔ Subgroup.zpowers e ≤ Z := sup_le hVZ (Subgroup.zpowers_le.mpr hZd.he)
  obtain ⟨⟨P₀, hP₀, hP₀C'⟩, -⟩ := exists_sylow_cent_twins hc hZd hVeZ
  have hK₀ : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hP₀R : P₀ ∈ RSet (Om R) := mem_RSet_of_isSylow2In hK₀ hP₀
  have hP₀C : P₀ ≤ Subgroup.centralizer (V : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left))
  have hP₀e : P₀ ≤ Subgroup.centralizer ({e} : Set Y) :=
    hP₀C'.trans (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))))
  have hP₀E₀ : P₀ ≤ rLayerSub (Om R) (V ⊔ Subgroup.zpowers e) := le_rLayerSub_of_mem hP₀R hP₀C'
  have hPh : secImage X P₀ ∈ p23SecFamV R V := ⟨P₀, hP₀R, hP₀C, rfl⟩
  obtain ⟨x, hxE, hxP, hxmove⟩ := exists_fus_rLayer hc ctx.ae6 hP₀ hP₀e
  have hxP' : conjSub x P₀ = P₀ := by
    have hle : conjSub x P₀ ≤ P₀ := by
      rintro _ ⟨q, hq, rfl⟩
      exact hxP q hq
    exact Subgroup.eq_of_le_of_card_ge hle
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj x).injective).symm)
  obtain ⟨-, hE₀E, hE₀X, hcov⟩ :=
    LemL.p23_cover_V hc hZd hVZ (⟨1, Subgroup.one_mem _, by group⟩ : e ∈ p23Orb Z t e)
      inf_le_left
  obtain ⟨x₀, hx₀E₀, hx₀P, hx₀q⟩ := exists_conj_eq_of_cover hE₀E hcov hP₀E₀ hP₀.2.1 hxE hxP'
  have hx₀X : x₀ ∈ X := hE₀X hx₀E₀
  set π := QuotientGroup.mk' (classicalInvolutionOddCore ↥X) with hπ
  have hPN : P₀.subgroupOf X ⊓ classicalInvolutionOddCore ↥X = ⊥ :=
    AscQuot.inf_eq_bot_of_isPGroup_of_odd _ hP₀.2.1.comap_subtype le_rfl
      ((CFSG.ComponentClassification.OddCore.odd_card ↥X).of_dvd_nat
        (Subgroup.card_dvd_of_le inf_le_left))
  have hinj : ∀ a₁ ∈ P₀.subgroupOf X, ∀ a₂ ∈ P₀.subgroupOf X, π a₁ = π a₂ → a₁ = a₂ := by
    intro a₁ h₁ a₂ h₂ he
    have h3 : a₁⁻¹ * a₂ ∈ P₀.subgroupOf X ⊓ classicalInvolutionOddCore ↥X :=
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ h₁) h₂, QuotientGroup.eq.mp he⟩
    rw [hPN, Subgroup.mem_bot] at h3
    exact inv_mul_eq_one.mp h3
  obtain ⟨hU4, hUcyc⟩ := h4 _ hPh
  obtain ⟨gen, hgen⟩ := hUcyc.exists_generator
  have hgenord : orderOf gen = 4 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hgen, hU4]
  set a : SecQuot X := ((gen : ↥(secImage X P₀ ⊓ Wh)) : SecQuot X) with ha
  have haU : a ∈ secImage X P₀ ⊓ Wh := gen.2
  have ha4 : a ^ 4 = 1 := by
    have := pow_orderOf_eq_one gen
    rw [hgenord] at this
    simpa using congrArg (fun z : ↥(secImage X P₀ ⊓ Wh) => (z : SecQuot X)) this
  have ha2 : a ^ 2 ≠ 1 := by
    intro h1
    have : orderOf gen ∣ 2 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [hgenord] at this
    omega
  have hazp : ∀ z ∈ secImage X P₀ ⊓ Wh, z ∈ Subgroup.zpowers a := by
    intro z hz
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨z, hz⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨i, by simpa using congrArg Subtype.val hi⟩
  obtain ⟨b, hbP, hba⟩ : ∃ b ∈ P₀.subgroupOf X, π b = a := haU.1
  have hbY : (b : Y) ∈ P₀ := Subgroup.mem_subgroupOf.mp hbP
  have hb2 : (b : Y) ^ 2 ≠ 1 := by
    intro h
    apply ha2
    have hb1 : b ^ 2 = 1 := Subtype.ext (by simpa using h)
    rw [← hba, ← map_pow, hb1, map_one]
  set xX : ↥X := ⟨x₀, hx₀X⟩ with hxX
  have hcb : xX * b * xX⁻¹ ∈ P₀.subgroupOf X := by
    rw [Subgroup.mem_subgroupOf]
    show x₀ * (b : Y) * x₀⁻¹ ∈ P₀
    have := conj_mem_conjSub (n := x₀) hbY
    rwa [hx₀P] at this
  have hconj : π xX * a * (π xX)⁻¹ = π (xX * b * xX⁻¹) := by
    rw [← hba, map_mul, map_mul, map_inv]
  have hconjU : π xX * a * (π xX)⁻¹ ∈ secImage X P₀ ⊓ Wh := by
    refine ⟨?_, ?_⟩
    · rw [hconj]
      exact ⟨_, hcb, rfl⟩
    · have := conj_mem_conjSub (n := π xX) haU.2
      rwa [hWn] at this
  have hconj2 : (π xX * a * (π xX)⁻¹) ^ 2 ≠ 1 := by
    intro h
    apply ha2
    have h' : π xX * a ^ 2 * (π xX)⁻¹ = 1 := by rw [← conj_pow]; exact h
    calc a ^ 2 = (π xX)⁻¹ * (π xX * a ^ 2 * (π xX)⁻¹) * π xX := by group
      _ = 1 := by rw [h']; group
  rcases Fus.eq_or_inv_of_mem_zpowers ha4 ha2 (hazp _ hconjU) hconj2 with h1 | h1
  · have h2 : xX * b * xX⁻¹ = b := hinj _ hcb _ hbP (by rw [← hconj, h1, hba])
    have h3 : x₀ * (b : Y) * x₀⁻¹ = (b : Y) := congrArg Subtype.val h2
    exact (hxmove _ hbY hb2).1 (by rw [← hx₀q _ hbY, h3])
  · have h2 : xX * b * xX⁻¹ = b⁻¹ :=
      hinj _ hcb _ (Subgroup.inv_mem _ hbP) (by rw [← hconj, h1, map_inv, hba])
    have h3 : x₀ * (b : Y) * x₀⁻¹ = (b : Y)⁻¹ := congrArg Subtype.val h2
    exact (hxmove _ hbY hb2).2 (by rw [← hx₀q _ hbY, h3])

end Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
