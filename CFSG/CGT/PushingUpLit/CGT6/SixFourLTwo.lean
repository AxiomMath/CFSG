module

public import CFSG.CGT.PushingUpLit.CGT6.SixFourPrinted
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.CGT.PushingUpLit.CGT6.SixFourNine
public import CFSG.CGT.Timmesfeld75.StrongClosureCentral

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.SixThree CFSG.CGT.PushingUpLit.EightOneRel
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem eight_O2_quot {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R)
    (N : Subgroup (G ⧸ R)) (hN : N.Normal) (hN2 : IsPGroup 2 N) : N = ⊥ := by
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  have hc2 : IsPGroup 2 (N.comap π) :=
    hN2.comap_of_ker_isPGroup π (by rw [QuotientGroup.ker_mk']; exact h.hR2)
  have hcn : (N.comap π).Normal := hN.comap π
  have hle : N.comap π ≤ R := (normal_setting_facts h.hchar h.hRP).1 _ hcn hc2
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  have hg : g ∈ N.comap π := hx
  exact (QuotientGroup.eq_one_iff g).mpr (hle hg)

theorem eq_one_of_central_SL2 {Q : Type*} [Group Q] {F : Type} [Field F] [CharP F 2]
    (φ : Q ≃* Matrix.SpecialLinearGroup (Fin 2) F) {q : Q} (hq : ∀ q' : Q, q' * q = q * q') :
    q = 1 := by
  have hc : φ q ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro B
    obtain ⟨q', rfl⟩ := φ.surjective B
    rw [← map_mul, ← map_mul, hq q']
  obtain ⟨r, hr, hrq⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := eq_one_of_pow_two_pow_eq_one (k := 1) (by simpa using hr2)
  subst hr1
  have : φ q = 1 :=
    Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_one]; exact hrq.symm.trans (map_one _))
  exact φ.map_eq_one_iff.mp this

theorem EightCtx.quasisimple_of_SL {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n) : CFSG.IsQuasisimple (↥Y ⧸ pCore 2 ↥Y) := by
  have hY := h.hY.1
  rcases hY.quotient_type with hq | hp
  · exact hq
  · exfalso
    obtain ⟨φ, -⟩ := hnat
    have hcard : Nat.card (↥Y ⧸ pCore 2 ↥Y) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) := Nat.card_congr φ.toEquiv
    rw [hcard, card_SL2_eq, GaloisField.card 2 n (by omega)] at hp
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have h3 : 2 ≤ (2 ^ n) ^ 2 - 1 := by omega
    exact Nat.not_prime_mul (by omega) (by omega) hp

theorem EightCtx.mem_pCore_of_mem_R {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal]
    (h : EightCtx Y T R) (y : ↥Y) (hy : (y : G) ∈ R) : y ∈ pCore 2 ↥Y := by
  have hN : (R.subgroupOf Y).Normal := inferInstance
  have hN2 : IsPGroup 2 (R.subgroupOf Y) :=
    h.hR2.comap_of_injective Y.subtype Y.subtype_injective
  have hle : R.subgroupOf Y ≤ pCore 2 ↥Y := le_sSup ⟨hN, hN2⟩
  exact hle (Subgroup.mem_subgroupOf.mpr hy)

theorem eight_sl_Y_le {Y R : Subgroup G} {T : Sylow 2 G} [R.Normal] (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n) (K : Subgroup (G ⧸ R)) [K.Normal]
    (hJK : (jIn (T : Subgroup G)).map (QuotientGroup.mk' R) ≤ K) :
    Y ≤ K.comap (QuotientGroup.mk' R) := by
  classical
  obtain ⟨A, hA, hnot, hJA, hJY, hrel, -, -, ⟨x, hxJ, hxR⟩, -, -⟩ := eight_sl_nine h hn hnat
  have hq := h.quasisimple_of_SL hn hnat
  obtain ⟨φ, -⟩ := hnat
  let π : G →* G ⧸ R := QuotientGroup.mk' R
  set Kt : Subgroup G := K.comap π with hKt
  have hKtn : Kt.Normal := inferInstance
  have hRKt : R ≤ Kt := fun r hr => by
    have hπr : π r = 1 := (QuotientGroup.eq_one_iff r).mpr hr
    show π r ∈ K
    rw [hπr]
    exact K.one_mem
  have hOY : oTwoIn Y ≤ R := h.le_R_of_le_centralizerModCore
    (ThreeFromEight.isPGroup_oTwoIn Y) (EightOneWindow.oTwoIn_le_centralizerModCore Y)
  let Qm : Subgroup (↥Y ⧸ pCore 2 ↥Y) := (Kt.subgroupOf Y).map (QuotientGroup.mk' (pCore 2 ↥Y))
  have hQmn : Qm.Normal :=
    Subgroup.Normal.map (Subgroup.Normal.subgroupOf hKtn Y) _ (QuotientGroup.mk'_surjective _)
  rcases isSubnormal_le_center_or_eq_top_of_quasisimple hq hQmn.isSubnormal with hc | htop
  · exfalso
    obtain ⟨y, hy, r, hr, hyr⟩ := Subgroup.mem_sup_of_normal_right.mp (hJY hxJ)
    have hxKt : x ∈ Kt := hJK (Subgroup.mem_map_of_mem _ hxJ)
    have hyKt : y ∈ Kt := by
      have : y = x * r⁻¹ := by rw [← hyr]; group
      rw [this]
      exact Kt.mul_mem hxKt (Kt.inv_mem (hRKt hr))
    have hmem : (QuotientGroup.mk' (pCore 2 ↥Y) ⟨y, hy⟩ : ↥Y ⧸ pCore 2 ↥Y) ∈ Qm :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyKt)
    have hcen := hc hmem
    have hone : (QuotientGroup.mk' (pCore 2 ↥Y) ⟨y, hy⟩ : ↥Y ⧸ pCore 2 ↥Y) = 1 :=
      eq_one_of_central_SL2 φ (Subgroup.mem_center_iff.mp hcen)
    have hyp : (⟨y, hy⟩ : ↥Y) ∈ pCore 2 ↥Y := (QuotientGroup.eq_one_iff _).mp hone
    have hyR : y ∈ R := hOY ⟨⟨y, hy⟩, hyp, rfl⟩
    exact hxR (by rw [← hyr]; exact R.mul_mem hyR hr)
  · intro y hy
    have hmem : (QuotientGroup.mk' (pCore 2 ↥Y) ⟨y, hy⟩ : ↥Y ⧸ pCore 2 ↥Y) ∈ Qm := by
      rw [htop]; trivial
    obtain ⟨y', hy'K, hy'⟩ := hmem
    have hq1 : (y' : ↥Y)⁻¹ * ⟨y, hy⟩ ∈ pCore 2 ↥Y := QuotientGroup.eq.mp hy'
    have hR1 : ((y' : ↥Y)⁻¹ * ⟨y, hy⟩ : ↥Y).1 ∈ R := hOY ⟨_, hq1, rfl⟩
    have hy'Kt : (y' : G) ∈ Kt := Subgroup.mem_subgroupOf.mp hy'K
    have : y = (y' : G) * (((y' : ↥Y)⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by
      simp
    rw [this]
    exact Kt.mul_mem hy'Kt (hRKt hR1)

theorem card_sl2_gf2_eq_six :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)) = 6 := by
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 2 1 one_ne_zero, pow_one]
  rw [Matrix.card_SL_field 2, hq, Fin.prod_univ_two]
  decide

theorem not_isPerfect_of_card_eq_six {Q : Type*} [Group Q] (h : Nat.card Q = 6) :
    ¬ Group.IsPerfect Q := by
  intro hperf
  have : Finite Q := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Q) 3 (by rw [h]; norm_num)
  have hN : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers x)
    rw [hN, h] at this
    omega
  have hle : commutator Q ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have key : ⁅a, b⁆ = a * b * (a⁻¹ * b⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [key, Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
      Subgroup.mul_mem_iff_of_index_two hidx, inv_mem_iff, inv_mem_iff]
  have htop : Subgroup.zpowers x = ⊤ := top_le_iff.mp (hperf.commutator_eq_top ▸ hle)
  have hcard := congrArg (fun H : Subgroup Q => Nat.card H) htop
  simp only [Subgroup.card_top, hN, h] at hcard
  omega

theorem EightCtx.two_le_of_SL {Y R : Subgroup G} {T : Sylow 2 G} (h : EightCtx Y T R) {n : ℕ}
    (hn : 1 ≤ n) (hnat : IsNaturalSLTwoModule ↥Y n) : 2 ≤ n := by
  by_contra hlt
  have hn1 : n = 1 := by omega
  subst hn1
  have hq := h.quasisimple_of_SL le_rfl hnat
  obtain ⟨φ, -⟩ := hnat
  have hc : Nat.card (↥Y ⧸ pCore 2 ↥Y) = 6 :=
    (Nat.card_congr φ.toEquiv).trans card_sl2_gf2_eq_six
  exact not_isPerfect_of_card_eq_six hc hq.1

theorem card_psl2_two_pow {K' : Type} [Field K'] [Finite K'] {f : ℕ} (hf1 : 1 ≤ f)
    (hK' : Nat.card K' = 2 ^ f) :
    Nat.card (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSL 2 K')) =
      2 ^ f * ((2 ^ f) ^ 2 - 1) := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK']
  have hodd : Odd (2 ^ f - 1) := by
    have h2 : 2 ∣ 2 ^ f := dvd_pow_self 2 (by omega)
    obtain ⟨c, hc⟩ := h2
    have hpos : 0 < 2 ^ f := by positivity
    exact ⟨c - 1, by omega⟩
  have hg : Nat.gcd 2 (2 ^ f - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [hg]
  simp [Finset.Icc_self]

theorem card_map_central_odd_eq {K : Type*} [Group K] [Finite K] {T : Subgroup K}
    (hT : CFSG.Open.IsElemAbelian 2 T) (Z : Subgroup K) [Z.Normal] (hZodd : Odd (Nat.card Z)) :
    Nat.card (T.map (QuotientGroup.mk' Z)) = Nat.card T := by
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun t : T => (⟨QuotientGroup.mk' Z t, Subgroup.mem_map_of_mem _ t.2⟩ :
      T.map (QuotientGroup.mk' Z))) ⟨?_, ?_⟩)
  · intro a b hab
    have h1 : QuotientGroup.mk' Z (a : K) = QuotientGroup.mk' Z (b : K) := congrArg Subtype.val hab
    have h2 : (a : K)⁻¹ * b ∈ Z := QuotientGroup.eq.mp h1
    have h3 : (a : K)⁻¹ * b ∈ T := T.mul_mem (T.inv_mem a.2) b.2
    have h4 := CFSG.CGT.Timmesfeld75.eq_one_of_mem_of_odd_card hT hZodd h3 h2
    exact Subtype.ext (inv_mul_eq_one.mp h4)
  · rintro ⟨_, t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

end CFSG.CGT.PushingUpLit.CGT6
