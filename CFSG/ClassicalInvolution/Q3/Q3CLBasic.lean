module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen611
public import CFSG.ClassicalInvolution.Asc77.AscT3Sym
public import CFSG.ClassicalInvolution.Asc77.AscP1ThompsonBasic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Asc77.AscP1Nine3
public import CFSG.ClassicalInvolution.Asc77.AscT8Basic
public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64A
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Uniqueness.Section174Frame
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.StronglyEmbedded.UniqueCosetBasic

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3CL

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

namespace T3

open CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.AscL62

theorem twin_mem_omegaNbr (hΩ : HypOmegaGen Ω) {K L : Subgroup G} (hK : K ∈ Ω)
    (hL : L ∈ Ω) (hLK : L ≠ K) {z : G} (hzK : IsUniqueInvolution K z)
    (hzL : IsUniqueInvolution L z) : L ∈ omegaNbr Ω K := by
  obtain ⟨R, hR, hRL, -⟩ := exists_mem_RSet_ge hL (isPGroup_two_bot' (G := G)) bot_le
  exact ⟨hL, hLK, R, hR, hRL.1, hRL.1.trans (Sec6Gen.le_normalizer_of_twin hΩ hL hK hLK hzL hzK)⟩

theorem isSylow2In_of_mem_RSet_of_le (hΩ : HypOmegaGen Ω)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : R ∈ RSet Ω) (hRK : R ≤ K) : IsSylow2In R K :=
  CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.isSylow2In_of_mem_RSet_of_le hΩ hK hR hRK

theorem omegaNbr_symm (h62 : Sec6Gen.L6_2Gen) (hΩ : HypOmegaGen Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω)
    (h : J ∈ omegaNbr Ω K) : K ∈ omegaNbr Ω J := by
  obtain ⟨-, hJK, R, hR, hRJ, hRN⟩ := h
  have hRs : IsSylow2In R J := isSylow2In_of_mem_RSet_of_le hΩ hJ hR hRJ
  obtain ⟨zK, hzK⟩ := Sec6Gen.exists_uniqueInvolution hΩ hK
  obtain ⟨zJ, hzJ⟩ := Sec6Gen.exists_uniqueInvolution hΩ hJ
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hR
  have hzJR : zJ ∈ R := mem_of_isPGroup hzJ hRJ hRs.2.1 (by omega)
  have hRc : R ≤ Subgroup.centralizer ({zK} : Set G) := le_centralizer_of_le_normalizer' hzK hRN
  by_cases hz : zK = zJ
  · exact twin_mem_omegaNbr hΩ hJ hK (Ne.symm hJK) hzJ (hz ▸ hzK)
  · have hnt : J ∉ twinSet Ω K := by
      rintro ⟨-, z', hz'K, hz'J⟩
      exact hz ((hzK.eq hz'K).trans (hzJ.eq hz'J).symm)
    have hV : IsSylow2In R (J ⊓ Subgroup.centralizer ({zK} : Set G)) :=
      ⟨le_inf hRJ hRc, hRs.2.1, fun V' hV'P hV'2 hle =>
        hRs.2.2 V' (hV'P.trans inf_le_left) hV'2 hle⟩
    have hcomm : ⁅R, K⁆ ≤ oddCoreOf K := by
      rcases h62 G Ω hΩ K hK zK hzK J hJ hnt zJ hzJ R hV hzJR with
        ⟨hR1, -⟩ | ⟨hR1, -⟩ | ⟨hRU, -⟩ | ⟨-, hc⟩
      · exfalso
        have : Nat.card R = 2 := by
          rw [hR1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzJ.sq) hzJ.ne_one]
        omega
      · exfalso
        have : Nat.card R = 2 := by
          rw [hR1, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hzJ.sq) hzJ.ne_one]
        omega
      · exfalso
        obtain ⟨R', -, J', hJ', hR'J', hRR', -, hcard, -⟩ := Sec6Gen.exists_data_of_mem_USet hΩ hRU
        have e1 := Sec6Gen.natCard_isSylow2In_eq hΩ hJ' hJ hR'J' hRs
        have h0 : 0 < Nat.card R := Nat.card_pos
        omega
      · exact hc
    obtain ⟨RK, hRK, hRKinv⟩ := T3.exists_sylow_normalized hRs.2.1 hRN
    have hRK2 : IsPGroup 2 RK := hRK.2.1
    have hcRK : ∀ r ∈ R, ∀ x ∈ RK, r * x = x * r := by
      intro r hr x hx
      have h1 : ⁅r, x⁆ ∈ oddCoreOf K := hcomm (Subgroup.commutator_mem_commutator hr (hRK.1 hx))
      have h2 : ⁅r, x⁆ ∈ RK := by
        have : r * x * r⁻¹ ∈ conjSub r RK := conj_mem_conjSub hx
        rw [hRKinv r hr] at this
        rw [commutatorElement_def]
        exact RK.mul_mem this (RK.inv_mem hx)
      have h3 : ⁅r, x⁆ = 1 :=
        eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) h1
          (hRK2.to_le (Subgroup.zpowers_le.mpr h2))
      exact commutatorElement_eq_one_iff_mul_comm.mp h3
    have hRKc : RK ≤ Subgroup.centralizer ({zJ} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hcRK zJ hzJR x hx).symm
    have hRKR : RK ∈ RSet Ω := mem_RSet_of_isSylow2In hK hRK
    have h8K := Sec6Gen.eight_le_of_mem_RSet hΩ hRKR
    have hRKN : RK ≤ Subgroup.normalizer (J : Set G) :=
      Sec6Gen.le_normalizer_of_le_centralizer hΩ hJ hK hJK hzJ hRK.1 hRK2 (by omega) hRKc
    exact ⟨hK, Ne.symm hJK, RK, hRKR, hRK.1, hRKN⟩

end T3

namespace Thompson

open CFSG.ClassicalInvolution.Asc77.Thompson

theorem inf_W_of_mem_D (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R K : Subgroup G} (hR : R ∈ DSet Ω W) (hK : K ∈ Ω)
    (hRK : IsSylow2In R K) :
    R ⊓ W = K ⊓ W ∧ K ⊓ W ∈ USet Ω ∧ IsCyclic ↥(R ⊓ W) ∧ 4 ≤ Nat.card ↥(R ⊓ W) ∧
      Nat.card R = 2 * Nat.card ↥(R ⊓ W) := by
  have hW2 : IsPGroup 2 W := isPGroup_of_mem_WSet hW
  obtain ⟨η, hη, hWη⟩ := hW
  have hRW2 : IsPGroup 2 ↥(R ⊔ W) := hRK.2.1.to_sup_of_normal_right' hW2 hR.2
  obtain ⟨S', hS'⟩ := hRW2.exists_le_sylow
  have hWS' : W ≤ (S' : Subgroup G) := le_sup_right.trans hS'
  have hRS' : R ≤ (S' : Subgroup G) := le_sup_left.trans hS'
  have hηS : ∀ V ∈ η, V ≤ (S' : Subgroup G) := fun V hV =>
    (hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV : V ≤ W).trans hWS'
  have hR8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hK hRK)
  have hRle : R ≤ K ⊓ (S' : Subgroup G) := le_inf hRK.1 hRS'
  have hcard : 2 < Nat.card ↥(K ⊓ (S' : Subgroup G)) :=
    lt_of_lt_of_le (by omega) ((Subgroup.card_le_of_le hRle).trans' hR8)
  have h611 := Sec6Gen.l6_11Gen G Ω hΩ S' η hη hηS K hK hcard
  rw [← hWη] at h611
  have hUUSet : K ⊓ W ∈ USet Ω := by
    obtain ⟨S₀, hηS₀, -⟩ := hη
    exact (hηS₀.1 h611).1
  have hKS : K ⊓ (S' : Subgroup G) = R :=
    hRK.eq_of_le (S'.isPGroup'.to_inf_right) inf_le_left hRle
  have hKWR : K ⊓ W ≤ R := by
    rw [← hKS]
    exact inf_le_inf_left K hWS'
  have hRWeq : R ⊓ W = K ⊓ W :=
    le_antisymm (inf_le_inf_right W hRK.1) (le_inf hKWR inf_le_right)
  obtain ⟨R'', -, J, hJ, hR''J, hUR'', hcyc, hcard'', h4⟩ :=
    Sec6Gen.exists_data_of_mem_USet hΩ hUUSet
  have hRR'' : Nat.card R = Nat.card R'' := by
    exact Sec6Gen.natCard_isSylow2In_eq hΩ hK hJ hRK hR''J
  refine ⟨hRWeq, hUUSet, hRWeq ▸ hcyc, hRWeq ▸ h4, ?_⟩
  rw [hRWeq, hRR'', hcard'']

theorem commutes_of_mem_WSet (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
  obtain ⟨η, ⟨S, hη, hinv⟩, rfl⟩ := hW
  exact (Sec6Gen.eta_abelian_of_cyc66 hΩ (Sec6Gen.cyc66 hΩ) hη hinv).1

theorem conjSub_mem_RSet (hΩ : HypOmegaGen Ω) {R : Subgroup G} (hR : R ∈ RSet Ω) (g : G) :
    conjSub g R ∈ RSet Ω := by
  obtain ⟨J, hJ, hRJ⟩ := exists_isSylow2In_of_mem_RSet hR
  exact mem_RSet_of_isSylow2In (hΩ.conjInvariant g J hJ) (hRJ.conj g)

theorem conjSub_mem_D (hΩ : HypOmegaGen Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W) {n : G}
    (hn : n ∈ Subgroup.normalizer (W : Set G)) : conjSub n R ∈ DSet Ω W := by
  refine ⟨conjSub_mem_RSet hΩ hR.1 n, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 : n * (n⁻¹ * x * n) * n⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hn (hR.2 hx)) (Subgroup.inv_mem _ hn)
  simpa [mul_assoc] using h1

theorem D_card (hΩ : HypOmegaGen Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    Nat.card R = 2 * Nat.card ↥(R ⊓ W) := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR.1
  exact (inf_W_of_mem_D hΩ hW hR hK hRK).2.2.2.2

theorem D_sq_mem (hΩ : HypOmegaGen Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r : G} (hr : r ∈ R) : r * r ∈ W :=
  (sq_mem_of_card_eq_two_mul inf_le_left (D_card hΩ hW hR) hr).2

theorem D_inv_mul_mem (hΩ : HypOmegaGen Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (hrW : r ∉ W) (hr'W : r' ∉ W) : r⁻¹ * r' ∈ W :=
  (inv_mul_mem_of_card_eq_two_mul (inf_le_left : R ⊓ W ≤ R) (D_card hΩ hW hR) hr hr'
    (fun h => hrW h.2) (fun h => hr'W h.2)).2

theorem D_piG_eq (hΩ : HypOmegaGen Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) {r r' : G} (hr : r ∈ R) (hr' : r' ∈ R)
    (hrW : r ∉ W) (hr'W : r' ∉ W) : piG W r = piG W r' :=
  (piG_eq_iff (hR.2 hr) (hR.2 hr')).mpr
    (Subgroup.mem_sup_left (D_inv_mul_mem hΩ hW hR hr hr' hrW hr'W))

theorem exists_not_mem_of_mem_D (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R : Subgroup G} (hR : R ∈ DSet Ω W) :
    ∃ r ∈ R, r ∉ W := by
  by_contra h
  push Not at h
  have h1 : R ⊓ W = R := inf_eq_left.mpr h
  have h2 := D_card hΩ hW hR
  rw [h1] at h2
  have : 0 < Nat.card R := Nat.card_pos
  omega

theorem piG_eq_of_le_sup (hΩ : HypOmegaGen Ω)
    {W : Subgroup G} (hW : W ∈ WSet Ω) {R T : Subgroup G} (hR : R ∈ DSet Ω W)
    (hT : T ∈ DSet Ω W) (hTR : T ≤ R ⊔ W ⊔ OCW W) {r t : G} (hr : r ∈ R) (ht : t ∈ T)
    (hrW : r ∉ W) (htW : t ∉ W) : piG W t = piG W r := by
  have hrN := hR.2 hr
  set g := piG W r with hg
  have hgg : g * g = 1 := by
    rw [hg, ← piG_mul hrN hrN]
    exact piG_of_mem_sup (Subgroup.mem_sup_left (D_sq_mem hΩ hW hR hr))
  let Y : Subgroup G :=
    ((Subgroup.zpowers g).comap (piN W)).map (Subgroup.normalizer (W : Set G)).subtype
  have hY : ∀ x : G, x ∈ Subgroup.normalizer (W : Set G) → piG W x ∈ Subgroup.zpowers g →
      x ∈ Y := fun x hx hxg =>
    ⟨⟨x, hx⟩, by simpa [piG_of_mem hx] using hxg, rfl⟩
  have hY' : ∀ x ∈ Y, piG W x ∈ Subgroup.zpowers g := by
    rintro _ ⟨y, hy, rfl⟩
    have : piG W (y : G) = piN W y := by rw [piG_of_mem y.2]
    show piG W (y : G) ∈ _
    rw [this]
    exact hy
  have hRY : R ≤ Y := fun x hx => by
    refine hY x (hR.2 hx) ?_
    by_cases hxW : x ∈ W
    · rw [piG_of_mem_sup (Subgroup.mem_sup_left hxW)]
      exact Subgroup.one_mem _
    · rw [D_piG_eq hΩ hW hR hx hr hxW hrW]
      exact Subgroup.mem_zpowers g
  have hWY : W ≤ Y := fun x hx => by
    refine hY x (Subgroup.le_normalizer hx) ?_
    rw [piG_of_mem_sup (Subgroup.mem_sup_left hx)]
    exact Subgroup.one_mem _
  have hXY : OCW W ≤ Y := fun x hx => by
    refine hY x (OCW_le_normalizer W hx) ?_
    rw [piG_of_mem_sup (Subgroup.mem_sup_right hx)]
    exact Subgroup.one_mem _
  have htY : t ∈ Y := (sup_le (sup_le hRY hWY) hXY) (hTR ht)
  have h1 := hY' t htY
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hk2 : g ^ k = g ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    have : g ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hgg
    rw [this, one_zpow, mul_one]
  have hne : piG W t ≠ 1 := fun h =>
    D_not_mem_sup hW hT ht htW ((piG_eq_one_iff (hT.2 ht)).mp h)
  rw [← hk, hk2] at hne ⊢
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · rw [h, zpow_zero] at hne
    exact absurd rfl hne
  · rw [h, zpow_one]

end Thompson

namespace T8

open CFSG.ClassicalInvolution.Asc77.T8
  CFSG.ClassicalInvolution.Asc77.Thompson
  CFSG.ClassicalInvolution.Asc77.AscP1Nine3
  CFSG.GH74.Uniqueness
  CFSG.StronglyEmbedded.UniqueCoset

theorem conjSub_eq_of_conjSub_eq (hΩ : HypOmegaGen Ω) {J T : Subgroup G}
    (hJ : J ∈ Ω) (hT : T ∈ RSet Ω) (hTJ : T ≤ J) {s : G} (hs : conjSub s T = T) :
    conjSub s J = J :=
  Sec6Gen.eq_of_le_of_le hΩ (hΩ.conjInvariant s J hJ) hJ
    (T3.isSylow2In_of_mem_RSet_of_le hΩ hJ hT hTJ).2.1
    (by have := Sec6Gen.eight_le_of_mem_RSet hΩ hT; omega) (hs ▸ conjSub_mono hTJ) hTJ

theorem mul_comm_of_mem_omegaNbr {K J : Subgroup G} {z t : G} (hΩ : HypOmegaGen Ω)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K)
    (ht : IsUniqueInvolution J t) : z * t = t * z := by
  obtain ⟨hJΩ, -, T', hT', hT'J, hT'N⟩ := hJ
  have hsyl := T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT' hT'J
  have h8 := Sec6Gen.eight_le_of_mem_RSet hΩ hT'
  have htT : t ∈ T' := T3.mem_of_isPGroup ht hT'J hsyl.2.1 (by omega)
  have hN : conjSub t K = K := mem_normalizer_iff_conjSub_eq.mp (hT'N htT)
  have h := hz.conj_eq hN
  calc z * t = (t * z * t⁻¹) * t := by rw [h]
    _ = t * z := by group

theorem mul_self_zt {K J : Subgroup G} {z t : G} (hΩ : HypOmegaGen Ω)
    (hz : IsUniqueInvolution K z) (hJ : J ∈ omegaNbr Ω K) (ht : IsUniqueInvolution J t) :
    z * t * (z * t) = 1 := by
  have hc := mul_comm_of_mem_omegaNbr hΩ hz hJ ht
  calc z * t * (z * t) = z * (t * z) * t := by group
    _ = z * (z * t) * t := by rw [hc]
    _ = (z * z) * (t * t) := by group
    _ = 1 := by rw [hz.sq, ht.sq]; group

theorem exists_orderFour_acting_by_sign (hΩ : HypOmegaGen Ω) {L : Subgroup G}
    (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {P : Subgroup G} (hP : IsPGroup 2 P)
    (hPN : ∀ q ∈ P, conjSub q L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧ ∀ q ∈ P, q * x * q⁻¹ = x ∨ q * x * q⁻¹ = x⁻¹ := by
  obtain ⟨R, hRL, hRfix⟩ := T3.exists_sylow_normalized hP
    (fun q hq => mem_normalizer_iff_conjSub_eq.mpr (hPN q hq))
  have h8 : 8 ≤ Nat.card R := Sec6Gen.eight_le_of_mem_RSet hΩ (mem_RSet_of_isSylow2In hL hRL)
  have hbR : b ∈ R := T3.mem_of_isPGroup hb hRL.1 hRL.2.1 (by omega)
  have hb' : IsUniqueInvolution R b := uniqueInvolution_restrict hb hRL.1 hbR
  have hRn : P ≤ Subgroup.normalizer (R : Set G) := fun q hq =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix q hq)
  have hPR : IsPGroup 2 ↥(P ⊔ R) := hP.to_sup_of_normal_right' hRL.2.1 hRn
  have hTn : ∀ q ∈ P ⊔ R, conjSub q R = R := fun q hq =>
    mem_normalizer_iff_conjSub_eq.mp ((sup_le hRn Subgroup.le_normalizer : P ⊔ R ≤ _) hq)
  obtain ⟨A, hAR, hAc, hA4, hAP⟩ :=
    exists_invariant_cyclic_order_four hPR (le_sup_right : R ≤ P ⊔ R) hTn hb' (by omega)
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥A)
  have hxo : orderOf (g : G) = 4 := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hA4]
  have hgen : ∀ y ∈ A, y ∈ Subgroup.zpowers (g : G) := by
    intro y hy
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
    exact Subgroup.mem_zpowers_iff.mpr ⟨m, by simpa using congrArg Subtype.val hm⟩
  exact ⟨g, hRL.1 (hAR g.2), hxo, fun q hq =>
    conj_eq_or_inv_of_cyclic_four hgen g.2 hxo (hAP q ((le_sup_left : P ≤ P ⊔ R) hq))⟩

theorem exists_orderFour_centralizes_sq (hΩ : HypOmegaGen Ω) {L : Subgroup G}
    (hL : L ∈ Ω) {b : G} (hb : IsUniqueInvolution L b) {q : G}
    (hq : IsPGroup 2 (Subgroup.zpowers q)) (hqL : conjSub q L = L) :
    ∃ x ∈ L, orderOf x = 4 ∧ x * (q * q) = (q * q) * x := by
  have hqN : Subgroup.zpowers q ≤ Subgroup.normalizer (L : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hqL)
  obtain ⟨x, hxL, hxo, hx⟩ := exists_orderFour_acting_by_sign hΩ hL hb hq
    (fun w hw => mem_normalizer_iff_conjSub_eq.mp (hqN hw))
  refine ⟨x, hxL, hxo, ?_⟩
  rcases hx q (Subgroup.mem_zpowers q) with h | h
  · have h1 : q * x = x * q := by
      calc q * x = (q * x * q⁻¹) * q := by group
        _ = x * q := by rw [h]
    calc x * (q * q) = (x * q) * q := by group
      _ = (q * x) * q := by rw [h1]
      _ = q * (x * q) := by group
      _ = q * (q * x) := by rw [h1]
      _ = (q * q) * x := by group
  · have h1 : q * x = x⁻¹ * q := by
      calc q * x = (q * x * q⁻¹) * q := by group
        _ = x⁻¹ * q := by rw [h]
    have h2 : q * x⁻¹ = x * q := by
      calc q * x⁻¹ = (q * x * q⁻¹)⁻¹ * q := by group
        _ = x * q := by rw [h, inv_inv]
    calc x * (q * q) = (x * q) * q := by group
      _ = (q * x⁻¹) * q := by rw [h2]
      _ = q * (x⁻¹ * q) := by group
      _ = q * (q * x) := by rw [h1]
      _ = (q * q) * x := by group

end T8


end CFSG.ClassicalInvolution.Q3.Q3CL
