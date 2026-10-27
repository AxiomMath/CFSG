module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerpCentral
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E7

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

theorem exists_conj_of_mul_mem_odd {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    (hN : Odd (Nat.card N)) {a x : G} (ha : a * a = 1) (hx : x * x = 1) (hax : a⁻¹ * x ∈ N) :
    ∃ w : G, a = w * x * w⁻¹ := by
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  set d := a * x with hd
  have hdN : d ∈ N := by rw [hd, ← hainv]; exact hax
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf d ∣ Nat.card N := by
      rw [← Subgroup.orderOf_mk d hdN]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hN h1
  obtain ⟨k, hk⟩ := hodd
  set w := d ^ (k + 1) with hwdef
  have hw2 : w * w = d := by
    rw [hwdef, ← pow_add, show k + 1 + (k + 1) = orderOf d + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hconj : a * d * a⁻¹ = d⁻¹ := by
    rw [hd, mul_inv_rev, hxinv, hainv]
    calc a * (a * x) * a = (a * a) * x * a := by group
      _ = x * a := by rw [ha, one_mul]
  have hconjw : a * w * a⁻¹ = w⁻¹ := by
    rw [hwdef, ← conj_pow, hconj, inv_pow]
  have haw : a * w = w⁻¹ * a := by
    calc a * w = (a * w * a⁻¹) * a := by group
      _ = w⁻¹ * a := by rw [hconjw]
  have hx' : w⁻¹ * a * w = x := by
    calc w⁻¹ * a * w = w⁻¹ * (a * w) := by group
      _ = w⁻¹ * (w⁻¹ * a) := by rw [haw]
      _ = (w * w)⁻¹ * a := by group
      _ = d⁻¹ * a := by rw [hw2]
      _ = x := by rw [hd, mul_inv_rev, hxinv, hainv, mul_assoc, ha, mul_one]
  refine ⟨w, ?_⟩
  rw [← hx']
  group

section E7S

variable {n : ℕ}

@[expose] def P23E7Fus (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ x ∈ Subgroup.centralizer ({t} : Set Y), (∃ y : Y, x = y * t * y⁻¹) →
          x = t ∨ ∃ c ∈ Subgroup.centralizer ({t} : Set Y), x = c * (u * e) * c⁻¹

@[expose] def P23E7Orb (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ((⟨t, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
            ↥(Subgroup.centralizer ({t} : Set Y))) :
          ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
            classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))) ∈ p23ABar t u e ∧
        ∀ q ∈ p23ABar t u e, q ≠ 1 → ∃ x : ↥(Subgroup.centralizer ({t} : Set Y)),
          (∃ y : Y, (x : Y) = y * t * y⁻¹) ∧
            q = (x : ↥(Subgroup.centralizer ({t} : Set Y)) ⧸
              classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)))

theorem p23_isSylow_top {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
    {K' W : Subgroup Y} {u e g : Y} (hc : P23Cfg n Y R S t K' W u e g) {T : Subgroup Y}
    (hT : IsSylow2In T (Subgroup.centralizer ({t} : Set Y))) : IsSylow2In T ⊤ := by
  have hC := CoreData.of_S hc.std.perp.core
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hR₁ : IsSylow2In ((S : Subgroup R).map R.subtype) (tightCore R) := hC.datum.sylow_core
  have hR₁C : (S : Subgroup R).map R.subtype ≤ Subgroup.centralizer ({t} : Set Y) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxK : x ∈ tightCore R := hR₁.1 hx
    have hmem : x * t * x⁻¹ ∈ tightCore R :=
      (tightCore R).mul_mem ((tightCore R).mul_mem hxK hz.mem) ((tightCore R).inv_mem hxK)
    have hsq : (x * t * x⁻¹) * (x * t * x⁻¹) = 1 := by
      calc (x * t * x⁻¹) * (x * t * x⁻¹) = x * (t * t) * x⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    have hne : x * t * x⁻¹ ≠ 1 := by
      intro he
      apply hz.ne_one
      calc t = x⁻¹ * (x * t * x⁻¹) * x := by group
        _ = 1 := by rw [he]; group
    have hxt : x * t * x⁻¹ = t := (hz.unique _ hmem hsq).resolve_left hne
    calc x * t = x * t * x⁻¹ * x := by group
      _ = t * x := by rw [hxt]
  obtain ⟨T₀, hT₀, hRT⟩ := IsSylow2In.exists_ge hR₁.2.1 hR₁C
  have htop := CFSG.CGT.PushingUpLit.SolKNA.R4.isSylow2In_top_of_nbr_twin hC.hyp
    (CFSG.CGT.PushingUpLit.SolKNA.R4.nbr_twin_of_kPerp_eq (tightCore R) hc.std.perp.perp) hK hz
    hR₁ hT₀ hRT
  exact htop.of_natCard_le hT.2.1 le_top (hT₀.natCard_eq hT).le

theorem p23E7Elem_of_orb (hO : P23E7Orb n) : P23E7Elem n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ
  obtain ⟨-, horb⟩ := hO hcit hP Y R S t K' W u e g hc hno hE hZ
  have hz : IsUniqueInvolution (tightCore R) t :=
    Inner.isUniqueInvolution_core (CoreData.of_S hc.std.perp.core).datum
  have hsq : ∀ q ∈ p23ABar t u e, q * q = 1 := by
    intro q hq
    by_cases hq1 : q = 1
    · rw [hq1, one_mul]
    obtain ⟨x, ⟨y, hy⟩, rfl⟩ := horb q hq hq1
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have hxx : x * x = 1 := Subtype.ext (by
      show (x : Y) * x = 1
      rw [hy]
      calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group)
    rw [hxx]
    exact one_mem _
  intro a ha b hb
  have hab := hsq _ (mul_mem ha hb)
  calc a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left hab
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
      rw [inv_eq_of_mul_eq_one_right (hsq a ha), inv_eq_of_mul_eq_one_right (hsq b hb)]

theorem p23E7Strong_of_steps (hF : P23E7Fus n) (hO : P23E7Orb n) : P23E7Strong n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := Subgroup.centralizer ({t} : Set Y) with hCdef
  obtain ⟨htA, horb⟩ := hO hcit hP Y R S t K' W u e g hc hno hE hZ
  have hfus := hF hcit hP Y R S t K' W u e g hc hno hE hZ
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hd := hc.data
  have heW : e ∈ W := by
    have : e ∈ W ⊓ Asc77.centerIn (Subgroup.normalizer (W : Set Y)) := by
      rw [← hd.he]
      exact Subgroup.mem_closure_singleton_self e
    exact this.1
  have hWab := Q3CL.Thompson.commutes_of_mem_WSet hΩ hc.std.hW
  have hueC : u * e ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr
    (hWab _ (W.mul_mem hd.huW heW) _ hc.std.htW)
  have huesq : (u * e) * (u * e) = 1 := by
    rw [← hd.hgt]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [hz.sq]; group
  have htC : t ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨T₀, hT₀, hueT₀⟩ := IsSylow2In.exists_ge
    (CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one huesq)
    (Subgroup.zpowers_le.mpr hueC)
  have hueT : u * e ∈ T₀ := hueT₀ (Subgroup.mem_zpowers _)
  have htop := p23_isSylow_top hc hT₀
  let T : Sylow 2 Y :=
    { toSubgroup := T₀
      isPGroup' := htop.2.1
      is_maximal' := fun hQ hle => htop.2.2 _ le_top hQ hle }
  set Ah : Subgroup Y :=
    ((p23ABar t u e).comap (QuotientGroup.mk' (classicalInvolutionOddCore ↥C))).map C.subtype
    with hAh
  have hmemAh : ∀ c : ↥C, ((c : ↥C ⧸ classicalInvolutionOddCore ↥C) ∈ p23ABar t u e) →
      (c : Y) ∈ Ah := fun c h => ⟨c, h, rfl⟩
  have hgen : ∀ (c : Y) (hc' : c ∈ C) (x : Y) (hx : x ∈ C), x = c * (u * e) * c⁻¹ →
      ((⟨x, hx⟩ : ↥C) : ↥C ⧸ classicalInvolutionOddCore ↥C) ∈ p23ABar t u e :=
    fun c hc' x hx h => Subgroup.subset_closure ⟨⟨x, hx⟩, ⟨c, hc', h⟩, rfl⟩
  have hodd : Odd (Nat.card ↥(Asc77.oddCoreOf C)) := oddCoreOf_odd_natCard C
  refine ⟨T, T₀ ⊓ Ah, inf_le_left.trans hT₀.1, inf_le_left,
    Subgroup.mem_inf.2 ⟨hueT, hmemAh ⟨u * e, hueC⟩ (hgen 1 (one_mem _) _ hueC (by group))⟩,
    hT₀.2.1.to_le inf_le_left, ?_, ?_⟩
  · intro a ha
    obtain ⟨c, hc', hca⟩ := (Subgroup.mem_inf.1 ha).2
    have : (⟨a, (inf_le_left.trans hT₀.1) ha⟩ : ↥C) = c := Subtype.ext hca.symm
    rw [this]
    exact hc'
  · intro a ha x hxT
    have haT : a ∈ T₀ := (Subgroup.mem_inf.1 ha).1
    have haC : a ∈ C := hT₀.1 haT
    have hxC : x⁻¹ * a * x ∈ C := hT₀.1 hxT
    by_cases ha1 : a = 1
    · rw [ha1, mul_one, inv_mul_cancel]
      exact one_mem _
    have hbar : ((⟨a, haC⟩ : ↥C) : ↥C ⧸ classicalInvolutionOddCore ↥C) ∈ p23ABar t u e := by
      obtain ⟨c, hc', hca⟩ := (Subgroup.mem_inf.1 ha).2
      have : (⟨a, haC⟩ : ↥C) = c := Subtype.ext hca.symm
      rw [this]
      exact hc'
    have hq1 : ((⟨a, haC⟩ : ↥C) : ↥C ⧸ classicalInvolutionOddCore ↥C) ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff] at h
      exact ha1 (eq_one_of_isPGroup_of_mem_odd hodd ⟨_, h, rfl⟩
        (hT₀.2.1.to_le (Subgroup.zpowers_le.mpr haT)))
    obtain ⟨x₀, ⟨y, hy⟩, hqx⟩ := horb _ hbar hq1
    have hx₀sq : (x₀ : Y) * x₀ = 1 := by
      rw [hy]
      calc y * t * y⁻¹ * (y * t * y⁻¹) = y * (t * t) * y⁻¹ := by group
        _ = 1 := by rw [hz.sq]; group
    have haa : a * a = 1 := by
      have hx₀1 : x₀ * x₀ = 1 := Subtype.ext hx₀sq
      have h1 : ((⟨a, haC⟩ * ⟨a, haC⟩ : ↥C) : ↥C ⧸ classicalInvolutionOddCore ↥C) = 1 := by
        rw [QuotientGroup.mk_mul, hqx, ← QuotientGroup.mk_mul, hx₀1, QuotientGroup.mk_one]
      rw [QuotientGroup.eq_one_iff] at h1
      exact eq_one_of_isPGroup_of_mem_odd hodd ⟨_, h1, rfl⟩
        (hT₀.2.1.to_le (Subgroup.zpowers_le.mpr (T₀.mul_mem haT haT)))
    have hax : a⁻¹ * (x₀ : Y) ∈ Asc77.oddCoreOf C := ⟨_, QuotientGroup.eq.mp hqx, rfl⟩
    obtain ⟨w, hw⟩ := exists_conj_of_mul_mem_odd hodd haa hx₀sq hax
    refine Subgroup.mem_inf.2 ⟨hxT, ?_⟩
    rcases hfus _ hxC ⟨x⁻¹ * w * y, by rw [hw, hy]; group⟩ with h | ⟨c, hcC, hc'⟩
    · have : (⟨x⁻¹ * a * x, hxC⟩ : ↥C) = ⟨t, htC⟩ := Subtype.ext h
      exact ⟨⟨x⁻¹ * a * x, hxC⟩, by rw [this]; exact htA, rfl⟩
    · exact hmemAh ⟨x⁻¹ * a * x, hxC⟩ (hgen c hcC _ hxC hc')

end E7S

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
