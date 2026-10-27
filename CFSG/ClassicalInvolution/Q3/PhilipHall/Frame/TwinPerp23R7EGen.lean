module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7ECent
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Cover
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7E8
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LL2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6jB
import CFSG.ClassicalInvolution.Q3.Q3CPSat
import CFSG.ClassicalInvolution.Q3.Q3CLBasic
import CFSG.ClassicalInvolution.Asc77.AscSixBasic
import CFSG.ClassicalInvolution.Asc77.AscSixInv
import CFSG.ClassicalInvolution.AschTight.Sec7L714D
import CFSG.ClassicalInvolution.AschTight.Sec7L714F
import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
import CFSG.ClassicalInvolution.Q3.Sec13L94Tight
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusE6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7Y
public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL

namespace F7G

variable {G : Type} [Group G] [Finite G]

theorem inf_OCW_le {E W : Subgroup G}
    (hE : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set G))) :
    E ⊓ OCW W ≤ oddCoreOf E := by
  refine F7L.le_oddCoreOf_of_cover inf_le_left hE ?_ ?_
    (Odd.of_dvd_nat (odd_natCard_oddCoreOf _) (Subgroup.card_dvd_of_le inf_le_right))
  · exact le_inf inf_le_left (inf_le_right.trans (Asc77.Thompson.OCW_le_normalizer W))
  · intro x hx
    have h1 : x ∈ Subgroup.normalizer ((E : Subgroup G) : Set G) := Subgroup.le_normalizer hx.1
    have h2 : x ∈ Subgroup.normalizer ((OCW W : Subgroup G) : Set G) :=
      Asc77.Thompson.normalizer_le_normalizer_OCW W hx.2
    rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
    intro y
    simp only [Subgroup.mem_inf]
    exact and_congr (h1 y) (h2 y)

theorem inv_mem_W {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {Q J : Subgroup G} (hQ : Q ∈ DSet Ω W) (hJ : J ∈ Ω) (hQJ : IsSylow2In Q J) {z : G}
    (hz : IsUniqueInvolution J z) : z ∈ W := by
  obtain ⟨-, -, -, h4, -⟩ := Q3CL.Thompson.inf_W_of_mem_D hΩ hW hQ hJ hQJ
  have hW2 : IsPGroup 2 W := Asc77.Thompson.isPGroup_of_mem_WSet hW
  have h2 : IsPGroup 2 ↥(Q ⊓ W) := hW2.to_le inf_le_right
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
  have hdvd : 2 ∣ Nat.card ↥(Q ⊓ W) := by
    rw [hk]
    rcases k with _ | k
    · rw [hk] at h4; norm_num at h4
    · exact dvd_pow_self 2 (Nat.succ_ne_zero k)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have hxx : (x : G) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, pow_two] at this
    exact congrArg Subtype.val this
  have hx1 : (x : G) ≠ 1 := by
    intro h
    have : x = 1 := Subtype.ext h
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hxJ : (x : G) ∈ J := hQJ.1 x.2.1
  rcases hz.unique _ hxJ hxx with h | h
  · exact absurd h hx1
  · rw [← h]
    exact x.2.2

theorem exists_D_conj {Ω : Set (Subgroup G)} (hΩ : HypOmegaGen Ω) {W : Subgroup G} (hW : W ∈ WSet Ω)
    {E J R' : Subgroup G} (hE : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set G)))
    (hR'E : R' ≤ E) (hJ : J ∈ Ω) (hR' : IsSylow2In R' J) {z : G} (hz : IsUniqueInvolution J z)
    (hzW : z ∈ W) (hfix : ∀ c : G, c * z = z * c → Odd (orderOf c) → conjSub c J = J) :
    ∃ Q : Subgroup G, Q ∈ DSet Ω W ∧ IsSylow2In Q J ∧ Q ≤ oddCoreOf E ⊔ R' := by
  obtain ⟨o, ho, hoN⟩ := exists_oddCore_conj_le hE hR'.2.1 hR'E
  set Q := conjSub o⁻¹ R' with hQdef
  have hmemQ : ∀ x ∈ Q, o * x * o⁻¹ ∈ R' := by
    intro x hx
    rw [hQdef, mem_conjSub_iff, inv_inv] at hx
    exact hx
  have hQN : Q ≤ Subgroup.normalizer (W : Set G) := by
    intro x hx
    have := hoN _ (hmemQ x hx)
    have e : o⁻¹ * (o * x * o⁻¹) * o = x := by group
    rwa [e] at this
  have hQR : Q ∈ RSet Ω :=
    Q3CL.Thompson.conjSub_mem_RSet hΩ (Asc77.mem_RSet_of_isSylow2In hJ hR') o⁻¹
  have hQD : Q ∈ DSet Ω W := ⟨hQR, hQN⟩
  have hJo : conjSub o⁻¹ J ∈ Ω := hΩ.conjInvariant o⁻¹ J hJ
  have hQJo : IsSylow2In Q (conjSub o⁻¹ J) := hR'.conj o⁻¹
  have hzo : IsUniqueInvolution (conjSub o⁻¹ J) (o⁻¹ * z * o⁻¹⁻¹) :=
    TwinPerpV3.A6jB.isUniqueInvolution_conjSub hz o⁻¹
  have hzoW : o⁻¹ * z * o⁻¹⁻¹ ∈ W := inv_mem_W hΩ hW hQD hJo hQJo hzo
  have hzR' : z ∈ R' := Q3CP.mem_of_isSylow2In_of_isUniqueInvolution hz hR'
  have hzE : z ∈ E := hR'E hzR'
  have hd1 : z⁻¹ * (o⁻¹ * z * o⁻¹⁻¹) ∈ W := W.mul_mem (W.inv_mem hzW) hzoW
  have hd2 : z⁻¹ * (o⁻¹ * z * o⁻¹⁻¹) ∈ oddCoreOf E := by
    have hzN := Sec7.le_normalizer_oddCoreOf E (E.inv_mem hzE)
    have h1 : z⁻¹ * o⁻¹ * z⁻¹⁻¹ ∈ oddCoreOf E :=
      (Subgroup.mem_normalizer_iff.mp hzN _).mp ((oddCoreOf E).inv_mem ho)
    have e : z⁻¹ * (o⁻¹ * z * o⁻¹⁻¹) = (z⁻¹ * o⁻¹ * z⁻¹⁻¹) * o := by group
    rw [e]
    exact (oddCoreOf E).mul_mem h1 ho
  have hd := Sec13.L94T.eq_one_of_isPGroup_of_odd (Asc77.Thompson.isPGroup_of_mem_WSet hW)
    (odd_natCard_oddCoreOf E) hd1 hd2
  have hoz : o⁻¹ * z = z * o⁻¹ := by
    have h := congrArg (z * ·) hd
    simp only [mul_one, mul_inv_cancel_left] at h
    calc o⁻¹ * z = (o⁻¹ * z * o⁻¹⁻¹) * o⁻¹ := by group
      _ = z * o⁻¹ := by rw [h]
  have hodd : Odd (orderOf o⁻¹) := by
    rw [orderOf_inv]
    exact Odd.of_dvd_nat (odd_natCard_oddCoreOf E) (Subgroup.orderOf_dvd_natCard _ ho)
  have hfixJ := hfix o⁻¹ hoz hodd
  refine ⟨Q, hQD, hfixJ ▸ hQJo, fun x hx => ?_⟩
  have e : x = o⁻¹ * (o * x * o⁻¹) * o := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left ((oddCoreOf E).inv_mem ho))
    (Subgroup.mem_sup_right (hmemQ x hx))) (Subgroup.mem_sup_left ho)

end F7G

section Steps


variable {n : ℕ}

@[expose] def P23EGenD (n : ℕ) : Prop :=
  CIT3Below n → TL4.TightBelowRPlus 3 n →
  ∀ (Y : Type) [Group Y] [Finite Y] (R : Subgroup Y) (S : Sylow 2 R) (t : Y) (K' W : Subgroup Y)
    (u e g : Y), P23Cfg n Y R S t K' W u e g → ¬ SecNoExit R e → ECase1 R W e →
      u * e ∈ zStarOf (Subgroup.centralizer ({u} : Set Y)) →
        ∀ Q₀ Q₀' Q₁ : Subgroup Y, Q₀ ∈ DSet (Om R) W → Q₀' ∈ DSet (Om R) W → Q₁ ∈ DSet (Om R) W →
          IsSylow2In Q₀ (tightCore R) → IsSylow2In Q₀' K' → IsSylow2In Q₁ (conjSub g (tightCore R)) →
            rLayer (Om R) e ≤ oddCoreOf (rLayer (Om R) e) ⊔ (Q₀ ⊔ Q₀' ⊔ Q₁)

section Facts

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem P23Cfg.conjSub_eq_of_odd (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hcC : c ∈ Subgroup.centralizer ({t} : Set Y)) (hodd : Odd (orderOf c)) :
    conjSub c (tightCore R) = tightCore R ∧ conjSub c K' = K' := by
  rcases p23_conj_twins hc hcC with h | ⟨h1, h2⟩
  · exact h
  · exfalso
    have hcc : c * c ∈ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := by
      rw [mem_normalizer_iff_conjSub_eq, conjSub_mul, h1, h2]
    obtain ⟨m, hm⟩ := hodd
    have e1 : (c * c) ^ (m + 1) = c := by
      have h3 : (c * c) ^ (m + 1) = c ^ (orderOf c) * c := by
        rw [hm, ← sq, ← pow_mul, ← pow_succ]
        congr 1
      rw [h3, pow_orderOf_eq_one, one_mul]
    have hcN : c ∈ Subgroup.normalizer ((tightCore R : Subgroup Y) : Set Y) := by
      rw [← e1]
      exact Subgroup.pow_mem _ hcc _
    have h4 := mem_normalizer_iff_conjSub_eq.mp hcN
    rw [h1] at h4
    exact hc.std.hne h4

theorem P23Cfg.conjSub_eq_of_odd_ue (hc : P23Cfg n Y R S t K' W u e g) {c : Y}
    (hcue : c * (u * e) = (u * e) * c) (hodd : Odd (orderOf c)) :
    conjSub c (conjSub g (tightCore R)) = conjSub g (tightCore R) := by
  have hd := hc.data
  have hdt : g⁻¹ * c * g ∈ Subgroup.centralizer ({t} : Set Y) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * (g * t * g⁻¹) = (g * t * g⁻¹) * c := by rw [hd.hgt]; exact hcue
    calc g⁻¹ * c * g * t = g⁻¹ * (c * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * c) * g := by rw [h1]
      _ = t * (g⁻¹ * c * g) := by group
  have hodd' : Odd (orderOf (g⁻¹ * c * g)) := by
    have := Sec7.orderOf_conj_eq g⁻¹ c
    rw [inv_inv] at this
    rw [this]
    exact hodd
  have h1 := (hc.conjSub_eq_of_odd hdt hodd').1
  calc conjSub c (conjSub g (tightCore R)) = conjSub g (conjSub (g⁻¹ * c * g) (tightCore R)) := by
        rw [← conjSub_mul, ← conjSub_mul]
        congr 1
        group
    _ = conjSub g (tightCore R) := by rw [h1]

end Facts

theorem p23EGen_of_genD (hgen : P23EGenD n) : P23EGen n := by
  intro hcit hP Y _ _ R S t K' W u e g hc hno hE hZ R₀ R₀' R₁ hR₀ hR₀' hR₁ hR₀e hR₀'e hR₁e
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hd := hc.data
  have hW : W ∈ WSet (Om R) := hd.hW
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hK' : K' ∈ Om R := hc.std.hK'.1
  have hKg : conjSub g (tightCore R) ∈ Om R := hΩ.conjInvariant g _ hK
  have hz : IsUniqueInvolution (tightCore R) t := Inner.isUniqueInvolution_core hC.datum
  have hz' : IsUniqueInvolution K' t := isUniqueInvolution_of_mem_twinSet hz hc.std.hK'
  have hzg : IsUniqueInvolution (conjSub g (tightCore R)) (u * e) := by
    have := TwinPerpV3.A6jB.isUniqueInvolution_conjSub hz g
    rwa [hd.hgt] at this
  have heW : e ∈ W := (T7K.e_mem_inf hd).1
  have hueW : u * e ∈ W := W.mul_mem hd.huW heW
  set E := rLayer (Om R) e with hEdef
  have hEc : E ≤ oddCoreOf E ⊔ (E ⊓ Subgroup.normalizer (W : Set Y)) := hE
  have hle : ∀ {J R' : Subgroup Y}, J ∈ Om R → IsSylow2In R' J →
      R' ≤ Subgroup.centralizer ({e} : Set Y) → R' ≤ E := fun hJ hR' hR'e =>
    F7C.le_rLayer (Asc77.mem_RSet_of_isSylow2In hJ hR') hR'e
  have hfixK : ∀ c : Y, c * t = t * c → Odd (orderOf c) → conjSub c (tightCore R) = tightCore R :=
    fun c hct hodd => (hc.conjSub_eq_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hct) hodd).1
  have hfixK' : ∀ c : Y, c * t = t * c → Odd (orderOf c) → conjSub c K' = K' :=
    fun c hct hodd => (hc.conjSub_eq_of_odd (Subgroup.mem_centralizer_singleton_iff.mpr hct) hodd).2
  have hfixKg : ∀ c : Y, c * (u * e) = (u * e) * c → Odd (orderOf c) →
      conjSub c (conjSub g (tightCore R)) = conjSub g (tightCore R) :=
    fun c hc' hodd => hc.conjSub_eq_of_odd_ue hc' hodd
  obtain ⟨Q₀, hQ₀D, hQ₀, hQ₀le⟩ :=
    F7G.exists_D_conj hΩ hW hEc (hle hK hR₀ hR₀e) hK hR₀ hz hd.hzW hfixK
  obtain ⟨Q₀', hQ₀'D, hQ₀', hQ₀'le⟩ :=
    F7G.exists_D_conj hΩ hW hEc (hle hK' hR₀' hR₀'e) hK' hR₀' hz' hd.hzW hfixK'
  obtain ⟨Q₁, hQ₁D, hQ₁, hQ₁le⟩ :=
    F7G.exists_D_conj hΩ hW hEc (hle hKg hR₁ hR₁e) hKg hR₁ hzg hueW hfixKg
  refine (hgen hcit hP Y R S t K' W u e g hc hno hE hZ Q₀ Q₀' Q₁ hQ₀D hQ₀'D hQ₁D hQ₀ hQ₀' hQ₁).trans ?_
  refine sup_le le_sup_left (sup_le (sup_le ?_ ?_) ?_)
  · exact hQ₀le.trans (sup_le_sup_left (le_sup_left.trans le_sup_left) _)
  · exact hQ₀'le.trans (sup_le_sup_left (le_sup_right.trans le_sup_left) _)
  · exact hQ₁le.trans (sup_le_sup_left le_sup_right _)

end Steps

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23
