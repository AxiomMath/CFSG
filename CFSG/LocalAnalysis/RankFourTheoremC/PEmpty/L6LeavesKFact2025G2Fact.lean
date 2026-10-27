module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025G2Abs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFact2025G2Tor
public import CFSG.RankThree.PartOne.S11c.G2Plane

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025.G2

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.Open
open scoped MatrixGroups

section Arith

theorem sixteen_dvd_ordG2 {q : ℕ} (hq : Odd q) : 16 ∣ ordG2 q := by
  have hq1 : 1 ≤ q := hq.pos
  have h8 : 8 ∣ q ^ 2 - 1 := by
    obtain ⟨k, rfl⟩ := hq
    have : (2 * k + 1) ^ 2 - 1 = 4 * (k * (k + 1)) := by
      rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
      ring
    rw [this]
    have h2 : 2 ∣ k * (k + 1) := (Nat.even_mul_succ_self k).two_dvd
    obtain ⟨m, hm⟩ := h2
    exact ⟨m, by rw [hm]; ring⟩
  have h6 : q ^ 2 - 1 ∣ q ^ 6 - 1 := by
    have := Nat.sub_dvd_pow_sub_pow (q ^ 2) 1 3
    simpa [← pow_mul] using this
  have h64 : 8 * 8 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := Nat.mul_dvd_mul (h8.trans h6) h8
  have : 16 ∣ (q ^ 6 - 1) * (q ^ 2 - 1) := (by norm_num : 16 ∣ 8 * 8).trans h64
  unfold ordG2
  rw [mul_assoc]
  exact this.mul_left _

theorem three_dvd_mul_sq_sub_one {q : ℕ} (hq : 1 ≤ q) : 3 ∣ q * (q ^ 2 - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  have h1 : (n + 1) ^ 2 - 1 = n * (n + 2) := by
    rw [Nat.sub_eq_iff_eq_add (Nat.one_le_pow _ _ (by omega))]
    ring
  rw [h1]
  have h3 : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases h3 with h0 | h0 | h0
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h0) _) _
  · exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) _) _
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero (by omega)) _

end Arith

section Center

variable {K : Type} [Field K]

theorem sq_eq_one_of_mem_center {A : SL2 K} (hA : A ∈ Subgroup.center (SL2 K)) : A * A = 1 := by
  obtain ⟨u, hu, rfl⟩ := exists_eq_HSL_of_mem_center hA
  rw [HSL_mul_HSL', hu, HSL_one']

end Center

section Facts


variable {F : Type} [Field F] [Finite F]

theorem finite_adjointGroup_G2 (hF : 2 ≤ Nat.card F) : Finite ↥(adjointGroup .G2 F) := by
  have hc := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := F)
  refine Nat.finite_of_card_ne_zero ?_
  rw [hc]
  unfold ordG2
  have h1 : 1 ≤ Nat.card F ^ 2 - 1 := by
    have : 4 ≤ Nat.card F ^ 2 := by nlinarith
    omega
  have h2 : 1 ≤ Nat.card F ^ 6 - 1 := by
    have : 4 ≤ Nat.card F ^ 6 := by
      calc 4 ≤ Nat.card F ^ 2 := by nlinarith
        _ ≤ Nat.card F ^ 6 := Nat.pow_le_pow_right (by omega) (by norm_num)
    omega
  have h3 : 0 < Nat.card F ^ 6 := by positivity
  positivity

theorem isElementaryAbelian_of_isElemAbelian {G : Type*} [Group G] {E : Subgroup G}
    (hE : IsElemAbelian 2 E) : CFSG.IsElementaryAbelian 2 ↥E :=
  { toIsMulCommutative := hE.1
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun x =>
      Subtype.ext (by simpa using hE.2 x x.2) }

theorem sixteen_dvd_card_g2 (hodd : Odd (Nat.card F)) :
    16 ∣ Nat.card ↥(adjointGroup .G2 F) := by
  rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
  exact sixteen_dvd_ordG2 hodd

theorem exists_g2_pair_of_odd (hodd : Odd (Nat.card F)) :
    ∃ (b : Fin Tag.G2.rank → Fˣ) (α β : Fin Tag.G2.rank → ℤ) (h : G2SignPair α β),
      (∀ i, b i = 1 ∨ b i = -1) ∧ b ≠ 1 ∧
        (g2Mul h F).range = rootSpan .G2 F (rootCharKernel b) := by
  have hF : 2 ≤ Nat.card F := Finite.one_lt_card
  haveI := finite_adjointGroup_G2 hF
  have h2 : 2 ∣ Nat.card ↥(adjointGroup .G2 F) :=
    (by norm_num : 2 ∣ 16).trans (sixteen_dvd_card_g2 hodd)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(adjointGroup .G2 F)) 2 h2
  have ht1 : (t : ModGL .G2 F) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht
    omega
  have ht2 : (t : ModGL .G2 F) ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht] at this
    simpa using congrArg Subtype.val this
  obtain ⟨b, L, _, ψ, ι, hb, hb1, -⟩ := exists_involution_transport hodd t.2 ht2 ht1
  obtain ⟨α, β, h, hS⟩ := exists_g2_pair hodd hb hb1
  exact ⟨b, α, β, h, hb, hb1, hS⟩

theorem two_le_pRank_of_dvd_card_sl2 (hodd : Odd (Nat.card F)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card (SL2 F)) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup .G2 F)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hF : 2 ≤ Nat.card F := Finite.one_lt_card
  haveI := finite_adjointGroup_G2 hF
  obtain ⟨b, α, β, h, hb, hb1, hS⟩ := exists_g2_pair_of_odd hodd
  obtain ⟨A₁, hA₁⟩ := exists_prime_orderOf_dvd_card' (G := SL2 F) p hdvd
  have hSle : (g2Mul h F).range ≤ adjointGroup .G2 F := hS ▸ rootSpan_le_adjointGroup F _
  have hxm : rootSL2 .G2 F α A₁ ∈ adjointGroup .G2 F := by
    have := hSle ⟨(A₁, 1), rfl⟩
    rwa [g2Mul_apply, map_one, mul_one] at this
  have hym : rootSL2 .G2 F β A₁ ∈ adjointGroup .G2 F := by
    have := hSle ⟨(1, A₁), rfl⟩
    rwa [g2Mul_apply, map_one, one_mul] at this
  let x : ↥(adjointGroup .G2 F) := ⟨_, hxm⟩
  let y : ↥(adjointGroup .G2 F) := ⟨_, hym⟩
  have hxo : orderOf x = p := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (rootSL2 .G2 F α A₁) = p
    rw [orderOf_injective _ (rootSL2_injective_of_field α), hA₁]
  have hyo : orderOf y = p := by
    rw [← Subgroup.orderOf_coe]
    show orderOf (rootSL2 .G2 F β A₁) = p
    rw [orderOf_injective _ (rootSL2_injective_of_field β), hA₁]
  have hxy : Commute x y := Subtype.ext (g2_pair_commute h A₁ A₁).eq
  have hyx : y ∉ Subgroup.zpowers x := by
    rintro ⟨k, hk⟩
    have hk' : rootSL2 .G2 F α A₁ ^ k = rootSL2 .G2 F β A₁ := congrArg Subtype.val hk
    have hker : ((A₁ ^ k, A₁⁻¹) : SL2 F × SL2 F) ∈ (g2Mul h F).ker := by
      rw [MonoidHom.mem_ker, g2Mul_apply, map_zpow, hk', map_inv, mul_inv_cancel]
    obtain ⟨-, hinv⟩ := ker_g2Mul_central h _ hker
    have hA₁c : A₁ ∈ Subgroup.center (SL2 F) := by simpa using Subgroup.inv_mem _ hinv
    have hsq := sq_eq_one_of_mem_center hA₁c
    have : orderOf A₁ ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [hA₁] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  exact CFSG.GroupTheory.two_le_pRank_of_commute (p := p) (H := (⊤ : Subgroup _))
    (Subgroup.mem_top x) (Subgroup.mem_top y) hxo hyo hxy hyx

theorem two_le_pRank_three_g2 (hodd : Odd (Nat.card F)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(adjointGroup .G2 F)) := by
  refine two_le_pRank_of_dvd_card_sl2 hodd Nat.prime_three (by norm_num) ?_
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two]
  exact three_dvd_mul_sq_sub_one Nat.card_pos

theorem twoRankLeThree_g2 (hodd : Odd (Nat.card F)) : TwoRankLeThree ↥(adjointGroup .G2 F) := by
  intro E hE
  haveI hEel : CFSG.IsElementaryAbelian 2 E := isElementaryAbelian_of_isElemAbelian hE
  let eR : E ≃* E.map (adjointGroup .G2 F).subtype :=
    E.equivMapOfInjective (adjointGroup .G2 F).subtype (adjointGroup .G2 F).subtype_injective
  haveI : Finite (E.map (adjointGroup .G2 F).subtype) := Finite.of_equiv E eR.toEquiv
  haveI : CFSG.IsElementaryAbelian 2 (E.map (adjointGroup .G2 F).subtype) :=
    CFSG.IsElementaryAbelian.of_mulEquiv eR hEel
  have := (g2_elementary_two hodd (Subgroup.map_subtype_le E)).1
  rwa [← Nat.card_congr eR.toEquiv] at this

theorem noCentralInvolution_g2 (hodd : Odd (Nat.card F)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup ↥(adjointGroup .G2 F)) ≤ 1) {z : ↥(adjointGroup .G2 F)}
    (hzp : orderOf z = p) : NoCentralInvolution z := by
  intro t ht2 hcomm
  haveI : Fact p.Prime := ⟨hp⟩
  have hF2 := ringChar_ne_two_of_odd_card hodd
  have ht1 : (t : ModGL .G2 F) ≠ 1 := by
    intro h1
    have : t = 1 := Subtype.ext h1
    rw [this, orderOf_one] at ht2
    omega
  have ht2' : (t : ModGL .G2 F) ^ 2 = 1 := by
    have := pow_orderOf_eq_one t
    rw [ht2] at this
    simpa using congrArg Subtype.val this
  obtain ⟨b, L, _, ψ, ι, hb, hb1, hψ, hι, himg, -⟩ := exists_involution_transport hodd t.2 ht2' ht1
  obtain ⟨α, β, h, hS⟩ := exists_g2_pair hodd hb hb1
  have hzmem : (z : ModGL .G2 F) ∈ adjointGroup .G2 F ⊓ Subgroup.centralizer {(t : ModGL .G2 F)} :=
    ⟨z.2, Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hcomm)⟩
  have hψz : ψ (z : ModGL .G2 F) ∈ (toralCentralizer .G2 F b).map ι := by
    rw [← himg]
    exact Subgroup.mem_map_of_mem ψ hzmem
  obtain ⟨z₀, hz₀X, hz₀e⟩ := hψz
  have hz₀p : orderOf z₀ = p := by
    rw [← orderOf_injective ι hι z₀, hz₀e, orderOf_injective ψ hψ, Subgroup.orderOf_coe, hzp]
  have hz₀p1 : z₀ ^ p = 1 := hz₀p ▸ pow_orderOf_eq_one z₀
  have hz₀sq := g2_sq_mem hF2 hb h hS hz₀X
  obtain ⟨m, hm⟩ : ∃ m, p = 2 * m + 1 := (hp.eq_two_or_odd'.resolve_left hp2).exists_bit1
  have hz₀S : z₀ ∈ (g2Mul h F).range := by
    have : z₀ = (z₀ ^ 2) ^ (m + 1) := by
      rw [← pow_mul, show 2 * (m + 1) = p + 1 by omega, pow_succ, hz₀p1, one_mul]
    rw [this]
    exact Subgroup.pow_mem _ hz₀sq (m + 1)
  obtain ⟨⟨A, B⟩, hAB⟩ := hz₀S
  have hpow : g2Mul h F (A ^ p, B ^ p) = 1 := by
    rw [← Prod.pow_mk, map_pow, hAB, hz₀p1]
  obtain ⟨hAc, hBc⟩ := ker_g2Mul_central h _ (MonoidHom.mem_ker.mpr hpow)
  have hA2 := sq_eq_one_of_mem_center hAc
  have hB2 := sq_eq_one_of_mem_center hBc
  have hA₂ : (A ^ (p + 1)) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm (p + 1) p, pow_mul, show p + 1 = 2 * (m + 1) by omega, pow_mul,
      pow_two, hA2, one_pow]
  have hB₂ : (B ^ (p + 1)) ^ p = 1 := by
    rw [← pow_mul, Nat.mul_comm (p + 1) p, pow_mul, show p + 1 = 2 * (m + 1) by omega, pow_mul,
      pow_two, hB2, one_pow]
  have hz₀AB : g2Mul h F (A ^ (p + 1), B ^ (p + 1)) = z₀ := by
    rw [← Prod.pow_mk, map_pow, hAB, pow_succ, hz₀p1, one_mul]
  have hex : ∃ A₁ : SL2 F, orderOf A₁ = p := by
    by_cases hA1 : A ^ (p + 1) = 1
    · by_cases hB1 : B ^ (p + 1) = 1
      · exfalso
        rw [hA1, hB1] at hz₀AB
        have h11 : g2Mul h F (1, 1) = 1 := map_one (g2Mul h F)
        have : z₀ = 1 := by rw [← hz₀AB, h11]
        rw [this, orderOf_one] at hz₀p
        exact hp.one_lt.ne hz₀p
      · exact ⟨_, orderOf_eq_prime hB₂ hB1⟩
    · exact ⟨_, orderOf_eq_prime hA₂ hA1⟩
  obtain ⟨A₁, hA₁⟩ := hex
  have hdvd : p ∣ Nat.card (SL2 F) := hA₁ ▸ orderOf_dvd_natCard A₁
  have := two_le_pRank_of_dvd_card_sl2 hodd hp hp2 hdvd
  omega

theorem selfCentralizingEight_g2 (hodd : Odd (Nat.card F)) :
    SelfCentralizingEight ↥(adjointGroup .G2 F) := by
  intro E hE h8 g hg
  haveI hEel : CFSG.IsElementaryAbelian 2 E := isElementaryAbelian_of_isElemAbelian hE
  have hF2 := ringChar_ne_two_of_odd_card hodd
  let eR : E ≃* E.map (adjointGroup .G2 F).subtype :=
    E.equivMapOfInjective (adjointGroup .G2 F).subtype (adjointGroup .G2 F).subtype_injective
  haveI : Finite (E.map (adjointGroup .G2 F).subtype) := Finite.of_equiv E eR.toEquiv
  haveI : CFSG.IsElementaryAbelian 2 (E.map (adjointGroup .G2 F).subtype) :=
    CFSG.IsElementaryAbelian.of_mulEquiv eR hEel
  have hRK : E.map (adjointGroup .G2 F).subtype ≤ adjointGroup .G2 F := Subgroup.map_subtype_le E
  have hR8 : Nat.card (E.map (adjointGroup .G2 F).subtype) = 8 := by
    rw [← Nat.card_congr eR.toEquiv]
    exact h8
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨t, ht1⟩ := exists_ne (1 : E)
  have ht1' : ((t : ↥(adjointGroup .G2 F)) : ModGL .G2 F) ≠ 1 := fun h1 =>
    ht1 (Subtype.ext (Subtype.ext h1))
  have ht2 : ((t : ↥(adjointGroup .G2 F)) : ModGL .G2 F) ^ 2 = 1 := by
    simpa using congrArg Subtype.val (hE.2 (t : ↥(adjointGroup .G2 F)) t.2)
  obtain ⟨b, L, _, ψ, ι, hb, hb1, hψ, hι, himg, -⟩ :=
    exists_involution_transport hodd (t : ↥(adjointGroup .G2 F)).2 ht2 ht1'
  obtain ⟨α, β, h, hS⟩ := exists_g2_pair hodd hb hb1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hRle : E.map (adjointGroup .G2 F).subtype ≤
      adjointGroup .G2 F ⊓ Subgroup.centralizer {((t : ↥(adjointGroup .G2 F)) : ModGL .G2 F)} := by
    rintro _ ⟨e, he, rfl⟩
    refine ⟨e.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (hcomm _ he _ t.2)
  obtain ⟨R₀, hR₀X, hR₀, ⟨eR₀⟩⟩ := exists_corresponding_subgroup hψ hι himg hRle
  haveI : Finite R₀ := Finite.of_equiv _ eR₀.toEquiv
  haveI : CFSG.IsElementaryAbelian 2 R₀ := CFSG.IsElementaryAbelian.of_mulEquiv eR₀ inferInstance
  have hR₀8 : Nat.card R₀ = 8 := by
    rw [← Nat.card_congr eR₀.toEquiv]
    exact hR8
  have hgmem : ((g : ↥(adjointGroup .G2 F)) : ModGL .G2 F) ∈
      adjointGroup .G2 F ⊓ Subgroup.centralizer {((t : ↥(adjointGroup .G2 F)) : ModGL .G2 F)} :=
    ⟨g.2, Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val (hg _ t.2))⟩
  have hψg : ψ (g : ModGL .G2 F) ∈ (toralCentralizer .G2 F b).map ι := by
    rw [← himg]
    exact Subgroup.mem_map_of_mem ψ hgmem
  obtain ⟨g₀, hg₀X, hg₀e⟩ := hψg
  have hg₀R : ∀ r₀ ∈ R₀, g₀ * r₀ = r₀ * g₀ := by
    intro r₀ hr₀
    have : ι r₀ ∈ (E.map (adjointGroup .G2 F).subtype).map ψ := hR₀ ▸ Subgroup.mem_map_of_mem ι hr₀
    obtain ⟨r, ⟨e, he, rfl⟩, hre⟩ := this
    apply hι
    rw [map_mul, map_mul, hg₀e, ← hre, ← map_mul, ← map_mul]
    exact congrArg ψ (congrArg Subtype.val (hg e he))
  have hg₀mem := g2_toral_selfCentralizing hF2 hb h hS hR₀X hR₀8 g₀ hg₀X hg₀R
  have : ι g₀ ∈ (E.map (adjointGroup .G2 F).subtype).map ψ := hR₀ ▸ Subgroup.mem_map_of_mem ι hg₀mem
  obtain ⟨r, ⟨e, he, rfl⟩, hre⟩ := this
  rw [hg₀e] at hre
  have : ((e : ↥(adjointGroup .G2 F)) : ModGL .G2 F) = (g : ModGL .G2 F) := hψ hre
  have hge : e = g := Subtype.ext this
  rw [← hge]
  exact he

end Facts

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KF2025.G2
