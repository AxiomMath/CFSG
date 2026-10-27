module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7M1
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7TwoWTr
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23E4I0
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Fus

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL



namespace F7L

variable {Q : Type} [Group Q] [Finite Q]

theorem exists_lift_comm (x₀ : Q) (hx₂ : x₀ * x₀ = 1) (q : Q ⧸ classicalInvolutionOddCore Q)
    (hq : q * (x₀ : Q ⧸ classicalInvolutionOddCore Q) * q⁻¹ = x₀) :
    ∃ c : Q, (c : Q ⧸ classicalInvolutionOddCore Q) = q ∧ c * x₀ * c⁻¹ = x₀ := by
  obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective q
  set a := c₀ * x₀ * c₀⁻¹ with ha
  have ha2 : a * a = 1 := by
    rw [ha]
    calc c₀ * x₀ * c₀⁻¹ * (c₀ * x₀ * c₀⁻¹) = c₀ * (x₀ * x₀) * c₀⁻¹ := by group
      _ = 1 := by rw [hx₂]; group
  have hab : a⁻¹ * x₀ ∈ classicalInvolutionOddCore Q := by
    rw [← QuotientGroup.eq]
    rw [ha, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    exact hq
  obtain ⟨v, hv, hva⟩ := exists_conj_zpowers_of_mul_mem_odd
    (CFSG.ComponentClassification.OddCore.odd_card Q) ha2 hx₂ hab
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hvN : v ∈ classicalInvolutionOddCore Q := by
    have h1 : a * x₀ ∈ classicalInvolutionOddCore Q := by rw [← hainv]; exact hab
    exact (Subgroup.zpowers_le.mpr h1) hv
  refine ⟨v⁻¹ * c₀, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff v).mpr hvN, inv_one, one_mul]
  · calc v⁻¹ * c₀ * x₀ * (v⁻¹ * c₀)⁻¹ = v⁻¹ * a * v := by rw [ha]; group
      _ = x₀ := by rw [hva]; group

end F7L

section LemO

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem p23_conj_eq_of_le_normalizer (hc : P23Cfg n Y R S t K' W u e g) (y : Y)
    (hy : conjSub y W ≤ Subgroup.normalizer (W : Set Y)) : conjSub y W = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hPG : Q3CL.PartIHypG (Om R) := hC.partIHypG
  have hd := hc.data
  have htr : ∀ K₁ ∈ Om R, ∀ J ∈ Om R, ∃ a : Y, conjSub a K₁ = J := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    exact ⟨b * a⁻¹, by rw [conjSub_mul, conjSub_inv_conjSub]⟩
  obtain ⟨S₀, -, hwc, -⟩ := exists_weaklyClosed_conj_of_muIsoS4 hPG htr hd.hW hd.hS4
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hB2 : IsPGroup 2 (conjSub y W) := hW2.map _
  have hBW : IsPGroup 2 ↥(conjSub y W ⊔ W) := hB2.to_sup_of_normal_right' hW2 hy
  obtain ⟨S₁, hS₁⟩ := hBW.exists_le_sylow
  obtain ⟨a, ha⟩ := exists_conjSub_eq_of_sylow S₀ S₁
  have e2 : conjSub a⁻¹ W = W := hwc a⁻¹ (by
    rw [conjSub_le_iff, inv_inv, ha]
    exact le_sup_right.trans hS₁)
  have e3 : conjSub a W = W := by
    conv_lhs => rw [← e2]
    exact conjSub_conjSub_inv a W
  have e4 : conjSub (a⁻¹ * y) W = W := hwc _ (by
    rw [conjSub_mul, conjSub_le_iff, inv_inv, ha]
    exact le_sup_left.trans hS₁)
  calc conjSub y W = conjSub a (conjSub (a⁻¹ * y) W) := by
        rw [← conjSub_mul, mul_inv_cancel_left]
    _ = W := by rw [e4, e3]

theorem p23_wnorm (hc : P23Cfg n Y R S t K' W u e g) (hE : ECase1 R W e) {x : Y}
    (hxt : x ∈ Subgroup.centralizer ({t} : Set Y)) (hxe : x ∈ Subgroup.centralizer ({e} : Set Y)) :
    ∃ c ∈ oddCoreOf (rLayer (Om R) e), c ∈ Subgroup.centralizer ({t} : Set Y) ∧
      c⁻¹ * x ∈ Subgroup.normalizer (W : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hd.hW
  have hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := Q3CL.Thompson.commutes_of_mem_WSet hΩ hd.hW
  have hNe := normalizer_le_centralizer_e hd
  have hc2 : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  set E := rLayer (Om R) e with hEdef
  obtain ⟨S', hWS'⟩ := hW2.exists_le_sylow
  have hWE : W ≤ E := E4I.le_rLayer_of_mem_WSet hΩ h2 hc2 hd.hW hWS' hNe
  have hxE : conjSub x E = E := conjSub_rLayer_eq hΩ hxe
  have hAE : conjSub x W ≤ E := by
    have := conjSub_mono (n := x) hWE
    rwa [hxE] at this
  obtain ⟨o, ho, hoN⟩ := exists_oddCore_conj_le hE (hW2.map _) hAE
  have hxt' : x * t * x⁻¹ = t := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp hxt, mul_inv_cancel_right]
  have htA : t ∈ conjSub x W := by
    have h := conj_mem_conjSub (n := x) hd.hzW
    rwa [hxt'] at h
  have htE : t ∈ E := hWE hd.hzW
  have htN : t ∈ Subgroup.normalizer (W : Set Y) := Subgroup.le_normalizer hd.hzW
  set s := o⁻¹ * t * o with hs
  have hsN : s ∈ Subgroup.normalizer (W : Set Y) := hoN t htA
  have hoE : o ∈ E := oddCoreOf_le_self E ho
  have hEN : E ≤ Subgroup.normalizer (oddCoreOf E : Set Y) := Sec7.le_normalizer_oddCoreOf E
  have ht2 : t * t = 1 := (Inner.isUniqueInvolution_core hC.datum).sq
  have hs2 : s * s = 1 := by
    rw [hs]
    calc o⁻¹ * t * o * (o⁻¹ * t * o) = o⁻¹ * (t * t) * o := by group
      _ = 1 := by rw [ht2]; group
  set D := oddCoreOf E ⊓ Subgroup.normalizer (W : Set Y) with hDdef
  have hDodd : Odd (Nat.card D) :=
    (oddCoreOf_odd_natCard E).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hts : t⁻¹ * s ∈ D := by
    refine ⟨?_, Subgroup.mul_mem _ (Subgroup.inv_mem _ htN) hsN⟩
    have h1 : t⁻¹ * o⁻¹ * t⁻¹⁻¹ ∈ oddCoreOf E :=
      (Subgroup.mem_normalizer_iff.mp (hEN (E.inv_mem htE)) o⁻¹).mp ((oddCoreOf E).inv_mem ho)
    have e1 : t⁻¹ * s = (t⁻¹ * o⁻¹ * t⁻¹⁻¹) * o := by rw [hs]; group
    rw [e1]
    exact (oddCoreOf E).mul_mem h1 ho
  obtain ⟨v, hv, hvt⟩ := exists_conj_zpowers_of_mul_mem_odd hDodd ht2 hs2 hts
  have hvD : v ∈ D := by
    have hts' : t * s ∈ D := by rw [← htinv]; exact hts
    exact (Subgroup.zpowers_le.mpr hts') hv
  refine ⟨o * v⁻¹, (oddCoreOf E).mul_mem ho ((oddCoreOf E).inv_mem hvD.1), ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have e : t = (o * v⁻¹)⁻¹ * t * (o * v⁻¹) := by
      calc t = v * s * v⁻¹ := hvt
        _ = (o * v⁻¹)⁻¹ * t * (o * v⁻¹) := by rw [hs]; group
    calc o * v⁻¹ * t = (o * v⁻¹) * ((o * v⁻¹)⁻¹ * t * (o * v⁻¹)) := by rw [← e]
      _ = t * (o * v⁻¹) := by group
  · apply mem_normalizer_iff_conjSub_eq.mpr
    apply p23_conj_eq_of_le_normalizer hc
    rintro _ ⟨w, hw, rfl⟩
    have hw' : x * w * x⁻¹ ∈ conjSub x W := conj_mem_conjSub hw
    have h1 := hoN _ hw'
    have e : (MulAut.conj ((o * v⁻¹)⁻¹ * x)).toMonoidHom w =
        v * (o⁻¹ * (x * w * x⁻¹) * o) * v⁻¹ := by
      show (o * v⁻¹)⁻¹ * x * w * ((o * v⁻¹)⁻¹ * x)⁻¹ = _
      group
    rw [e]
    have hvN := hvD.2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hvN h1) (Subgroup.inv_mem _ hvN)

theorem p23_conjSub_twins_of_odd (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hct : c ∈ Subgroup.centralizer ({t} : Set Y)) (hodd : Odd (orderOf c)) :
    conjSub c (tightCore R) = tightCore R ∧ conjSub c K' = K' := by
  rcases p23_conj_twins hc hct with h | ⟨h1, h2⟩
  · exact h
  exfalso
  have hev : ∀ k : ℕ, conjSub (c ^ (2 * k)) (tightCore R) = tightCore R ∧
      conjSub (c ^ (2 * k)) K' = K' := by
    intro k
    induction k with
    | zero => simp [conjSub_one]
    | succ k ih =>
      have e : c ^ (2 * (k + 1)) = c ^ (2 * k) * (c * c) := by
        rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, sq]
      rw [e, conjSub_mul, conjSub_mul, conjSub_mul, conjSub_mul, h1, h2, h1, ih.1, ih.2]
      exact ⟨rfl, rfl⟩
  obtain ⟨k, hk⟩ := hodd
  have e1 : (1 : Y) = c ^ (2 * k) * c := by
    rw [← pow_succ, ← hk, pow_orderOf_eq_one]
  have h3 : conjSub (1 : Y) (tightCore R) = K' := by
    rw [e1, conjSub_mul, h1, (hev k).2]
  rw [conjSub_one] at h3
  exact hc.std.hne h3.symm

theorem p23_cent_le_stabMod (hc : P23Cfg n Y R S t K' W u e g) (hE : ECase1 R W e) {C : Subgroup Y}
    (hCdef : C = Subgroup.centralizer ({t} : Set Y))
    (xe xt xu : ↥C) (hxe : (xe : Y) = e) (hxt : (xt : Y) = t) (hxu : (xu : Y) = u)
    (q : ↥C ⧸ classicalInvolutionOddCore ↥C) (hq : q * F7I.piC C xe * q⁻¹ = F7I.piC C xe) :
    q ∈ F7K.stabMod (F7I.piC C xe) (F7I.piC C xt) (F7I.piC C xu) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hNe := normalizer_le_centralizer_e hd
  have toC : ∀ {y : Y}, y ∈ Subgroup.centralizer ({t} : Set Y) → y ∈ C := fun h => by
    rw [hCdef]; exact h
  have ofC : ∀ {y : Y}, y ∈ C → y ∈ Subgroup.centralizer ({t} : Set Y) := fun h => by
    rw [← hCdef]; exact h
  set E := rLayer (Om R) e with hEdef
  have hEe : E ≤ Subgroup.centralizer ({e} : Set Y) := rLayer_le_centralizer _ _
  have hEN : E ≤ Subgroup.normalizer (oddCoreOf E : Set Y) := Sec7.le_normalizer_oddCoreOf E
  have htc : ∀ c ∈ C, c * t = t * c := fun c hc =>
    Subgroup.mem_centralizer_singleton_iff.mp (ofC hc)
  have hzq : ∀ q : ↥C ⧸ classicalInvolutionOddCore ↥C, q * F7I.piC C xt = F7I.piC C xt * q := by
    intro q
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective (classicalInvolutionOddCore ↥C) q
    change F7I.piC C c * _ = _ * F7I.piC C c
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hxt]; exact htc _ c.2))
  have hxe2 : xe * xe = 1 := Subtype.ext (by rw [Subgroup.coe_mul, hxe]; exact hd.he2)
  obtain ⟨x, rfl, hxx⟩ := F7L.exists_lift_comm xe hxe2 q hq
  have hxeY : (x : Y) ∈ Subgroup.centralizer ({e} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := congrArg Subtype.val hxx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxe] at h
    calc (x : Y) * e = ((x : Y) * e * (x : Y)⁻¹) * x := by group
      _ = e * x := by rw [h]
  obtain ⟨c, hcO, hct, hcN⟩ := p23_wnorm hc hE (ofC x.2) hxeY
  set cC : ↥C := ⟨c, toC hct⟩ with hcC
  have hx : x = cC * (cC⁻¹ * x) := by group
  change F7I.piC C x ∈ _
  rw [hx, map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  ·
    have hcE : c ∈ E := oddCoreOf_le_self E hcO
    have hodd : Odd (orderOf c) := (oddCoreOf_odd_natCard E).of_dvd_nat
      (Subgroup.orderOf_dvd_natCard _ hcO)
    obtain ⟨hcK, hcK'⟩ := p23_conjSub_twins_of_odd hc hct hodd
    obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hR₁D, hR₁'D, -, hb₁R, hb'R', -, -, hub, -⟩ := e_decomp hc
    have hRE : ∀ T : Subgroup Y, T ∈ DSet (Om R) W → T ≤ E := by
      intro T hT
      rw [hEdef]
      unfold rLayer
      exact le_iSup₂_of_le T hT.1 (le_iSup_of_le (hT.2.trans hNe) le_rfl)
    have htC : t ∈ C := hxt ▸ xt.2
    have heC : e ∈ C := hxe ▸ xe.2
    obtain ⟨-, -, h8A, h8B, -⟩ := p23_twin_q8 hc hCdef htC heC
    have hfix : ∀ (L T : Subgroup Y), conjSub c L = L → T ≤ L → T ≤ E →
        Nat.card ((L.subgroupOf C).map (F7I.piC C)) = 8 → ∀ b ∈ T, ∀ hbC : b ∈ C,
          F7I.piC C (cC * ⟨b, hbC⟩ * cC⁻¹) = F7I.piC C ⟨b, hbC⟩ := by
      intro L T hcL hTL hTE h8 b hb hbC
      set k : ↥C := cC * ⟨b, hbC⟩ * cC⁻¹ * (⟨b, hbC⟩ : ↥C)⁻¹ with hk
      have hkO : (k : Y) ∈ oddCoreOf E := by
        have h1 : b * c⁻¹ * b⁻¹ ∈ oddCoreOf E :=
          (Subgroup.mem_normalizer_iff.mp (hEN (hTE hb)) c⁻¹).mp ((oddCoreOf E).inv_mem hcO)
        have e : (k : Y) = c * (b * c⁻¹ * b⁻¹) := by
          simp only [hk, Subgroup.coe_mul, Subgroup.coe_inv, hcC]; group
        rw [e]
        exact (oddCoreOf E).mul_mem hcO h1
      have hkL : (k : Y) ∈ L := by
        have h1 : c * b * c⁻¹ ∈ conjSub c L := conj_mem_conjSub (hTL hb)
        rw [hcL] at h1
        have e : (k : Y) = (c * b * c⁻¹) * b⁻¹ := by
          simp only [hk, Subgroup.coe_mul, Subgroup.coe_inv, hcC]
        rw [e]
        exact L.mul_mem h1 (L.inv_mem (hTL hb))
      have hkodd : Odd (orderOf k) := by
        rw [← Subgroup.orderOf_coe]
        exact (oddCoreOf_odd_natCard E).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hkO)
      have hmem : F7I.piC C k ∈ (L.subgroupOf C).map (F7I.piC C) :=
        ⟨k, Subgroup.mem_subgroupOf.mpr hkL, rfl⟩
      have h1 : orderOf (F7I.piC C k) ∣ 8 := by
        rw [← h8]; exact Subgroup.orderOf_dvd_natCard _ hmem
      have h2 : orderOf (F7I.piC C k) ∣ orderOf k := orderOf_map_dvd _ _
      have hcop : Nat.Coprime 8 (orderOf k) :=
        Nat.Coprime.pow_left 3 (Nat.coprime_two_left.mpr hkodd)
      have h3 : orderOf (F7I.piC C k) = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
      have h4 : F7I.piC C k = 1 := orderOf_eq_one_iff.mp h3
      rw [hk, map_mul, map_inv] at h4
      exact mul_inv_eq_one.mp h4
    have hb₁C : b₁ ∈ C := toC (le_centralizer_of_unique (Inner.isUniqueInvolution_core hC.datum)
      (hR₁.1 hb₁R))
    have hb'C : b' ∈ C := toC (le_centralizer_of_unique
      (isUniqueInvolution_of_mem_twinSet (Inner.isUniqueInvolution_core hC.datum) hc.std.hK')
      (hR₁'.1 hb'R'))
    have hu' : xu = ⟨b₁, hb₁C⟩ * ⟨b', hb'C⟩ := Subtype.ext (by rw [hxu, Subgroup.coe_mul, hub])
    refine F7K.mem_stabMod_of_modZ (hzq _) ?_ (Or.inl ?_)
    · have e : cC * xe * cC⁻¹ = xe := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hcC, hxe]
        rw [Subgroup.mem_centralizer_singleton_iff.mp (hEe hcE), mul_inv_cancel_right])
      rw [← map_inv, ← map_mul, ← map_mul, e]
    · have key : F7I.piC C (cC * xu * cC⁻¹) = F7I.piC C xu := by
        have e : cC * (⟨b₁, hb₁C⟩ * ⟨b', hb'C⟩) * cC⁻¹ =
            (cC * ⟨b₁, hb₁C⟩ * cC⁻¹) * (cC * ⟨b', hb'C⟩ * cC⁻¹) := by group
        rw [hu', e, map_mul, hfix _ R₁ hcK hR₁.1 (hRE R₁ hR₁D) h8A b₁ hb₁R hb₁C,
          hfix _ R₁' hcK' hR₁'.1 (hRE R₁' hR₁'D) h8B b' hb'R' hb'C, ← map_mul]
      rw [map_mul, map_mul, map_inv] at key
      exact key
  ·
    have hnN : ((cC⁻¹ * x : ↥C) : Y) ∈ Subgroup.normalizer (W : Set Y) := hcN
    have hnC := ofC (cC⁻¹ * x).2
    refine F7K.mem_stabMod_of_modZ (hzq _) ?_ ?_
    · have e : (cC⁻¹ * x) * xe * (cC⁻¹ * x)⁻¹ = xe := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxe,
          Subgroup.mem_centralizer_singleton_iff.mp (hNe hnN), mul_inv_cancel_right])
      rw [← map_inv, ← map_mul, ← map_mul, e]
    · rw [← map_inv, ← map_mul, ← map_mul]
      rcases conj_u_cases hc hnN hnC with h | h
      · left
        exact congrArg _ (Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hxu]; exact h))
      · right
        rw [← map_mul]
        exact congrArg _ (Subtype.ext (by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hxu, hxt] at h ⊢
          exact h))

theorem p23_stabMod_eq (hc : P23Cfg n Y R S t K' W u e g) (hE : ECase1 R W e)
    (xe xt xu : ↥(Subgroup.centralizer ({t} : Set Y))) (hxe : (xe : Y) = e) (hxt : (xt : Y) = t)
    (hxu : (xu : Y) = u) :
    F7K.stabMod (F7I.piC _ xe) (F7I.piC _ xt) (F7I.piC _ xu) =
      Subgroup.centralizer ({F7I.piC _ xe} : Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
        classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y)))) := by
  ext q
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hq
    have h := hq.1
    calc q * F7I.piC _ xe = (q * F7I.piC _ xe * q⁻¹) * q := by group
      _ = F7I.piC _ xe * q := by rw [h]
  · intro hq
    exact p23_cent_le_stabMod hc hE rfl xe xt xu hxe hxt hxu q (by rw [hq, mul_inv_cancel_right])

@[expose] def P23E7Not9C (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
      ∀ xe : ↥(Subgroup.centralizer ({t} : Set Y)), (xe : Y) = e →
        (Subgroup.centralizer ({F7I.piC (Subgroup.centralizer ({t} : Set Y)) xe} :
          Set (↥(Subgroup.centralizer ({t} : Set Y)) ⧸
            classicalInvolutionOddCore ↥(Subgroup.centralizer ({t} : Set Y))))).index ≠ 9

theorem p23E7Not9_of_C (h : P23E7Not9C n) : P23E7Not9 n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ xe xt xu hxe hxt hxu
  rw [p23_stabMod_eq hc hE xe xt xu hxe hxt hxu]
  exact h hcit hP Y R S t K' W u e g hc hno hE hZ xe hxe

end LemO

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
