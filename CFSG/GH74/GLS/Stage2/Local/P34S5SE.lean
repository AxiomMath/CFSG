module

public import CFSG.GH74.GLS.Stage2.Local.P34S5Jbar
public import CFSG.GH74.GLS.Stage2.Local.P34Pair
public import CFSG.GH74.Uniqueness.SU.KI6BStrong
public import CFSG.GroupTheory.OrderBelowSixtySolvable
public import CFSG.LocalAnalysis.LargeEvenClassification.WeakCoreOddNormal

public section

namespace CFSG.GH74.GLS.Stage2.Local.P34

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12

section Lift
variable {G : Type} [Group G] [Finite G]

theorem exists_lift_involution_in {H X : Subgroup G} {t : HBar H} (ht : t ∈ barIn H X)
    (ht2 : orderOf t = 2) : ∃ u : ↥H, (u : G) ∈ X ∧ orderOf u = 2 ∧ mkH H u = t := by
  obtain ⟨h, hhX, rfl⟩ := Subgroup.mem_map.1 ht
  have hhX' : (h : G) ∈ X := Subgroup.mem_subgroupOf.1 hhX
  have hn : orderOf h ≠ 0 := (orderOf_pos h).ne'
  obtain ⟨a, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  have hdvd : m ∣ orderOf h := ⟨2 ^ a, by rw [hord]; ring⟩
  have ht' : orderOf (h ^ m) = 2 ^ a := by
    rw [orderOf_pow_of_dvd hm0 hdvd, hord]
    exact Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)
  have hu2 : (mkH H h) ^ 2 = 1 := by
    have h' := pow_orderOf_eq_one (mkH H h)
    rw [ht2] at h'
    exact h'
  have hmk : mkH H (h ^ m) = mkH H h := by
    obtain ⟨k, hk⟩ := hm
    rw [map_pow, hk, pow_succ, pow_mul, hu2, one_pow, one_mul]
  have hu1 : mkH H h ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at ht2
    omega
  refine ⟨h ^ m, ?_, ?_, hmk⟩
  · rw [Subgroup.coe_pow]
    exact X.pow_mem hhX' m
  have hht2 : (h ^ m) ^ 2 ∈ pPrimeCore 2 ↥H := by
    rw [← mkH_eq_one_iff, map_pow, hmk, hu2]
  have hodd := odd_orderOf_of_mem_core H hht2
  have hd1 : orderOf ((h ^ m) ^ 2) ∣ 2 ^ a := ht' ▸ orderOf_pow_dvd 2
  have hcop : Nat.Coprime (orderOf ((h ^ m) ^ 2)) (2 ^ a) :=
    (Nat.coprime_two_right.2 hodd).pow_right a
  have hone : orderOf ((h ^ m) ^ 2) = 1 := Nat.Coprime.eq_one_of_dvd hcop hd1
  have hsq : (h ^ m) ^ 2 = 1 := orderOf_eq_one_iff.1 hone
  have hne : h ^ m ≠ 1 := by
    intro h1
    apply hu1
    rw [← hmk, h1, map_one]
  exact orderOf_eq_prime hsq hne

end Lift

section Solv
variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_barIn {J X : Subgroup G} (hXJ : X ≤ J) (h : Group.IsSolvable ↥(barIn J X)) :
    Group.IsSolvable ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let f : ↥X →* HBar J := (mkH J).comp (Subgroup.inclusion hXJ)
  have hrange : f.range ≤ barIn J X := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mem_map.2 ⟨Subgroup.inclusion hXJ x, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  have hsolvR : Group.IsSolvable ↥f.range :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hrange)
  have hker : Odd (Nat.card ↥f.ker) := by
    let g : ↥f.ker →* pPrimeCore 2 ↥J := 
      { toFun := fun x => ⟨Subgroup.inclusion hXJ x.1, (mkH_eq_one_iff J).1 x.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      have := congrArg (fun w : pPrimeCore 2 ↥J => ((w : ↥J) : G)) hxy
      exact this
    have hdvd := Subgroup.card_dvd_of_injective g hg
    exact Odd.of_dvd_nat (odd_card_pPrimeCore J) hdvd
  have hsolvK : Group.IsSolvable ↥f.ker := CFSG.Milestones.odd_order_solvable hker
  exact Group.isSolvable_of_ker_le_range (f := f.ker.subtype) (g := f.rangeRestrict) (by
    rw [MonoidHom.ker_rangeRestrict]
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩)

end Solv

section SE
variable {G : Type} [Group G] [Finite G]

theorem helpers_to_order {X : Type} [Group X] {M : Subgroup X}
    (h : DisconnectedInvolutionGraph.Helpers.IsStronglyEmbedded M) :
    BenderSuzuki.IsStronglyEmbeddedOrder M := by
  refine ⟨h.1, h.2.1, fun g hg => ?_⟩
  have h' := h.2.2 g hg
  have heq : DisconnectedInvolutionGraph.Helpers.conjugateSubgroup M g =
      M.map (MulAut.conj g).toMonoidHom := by
    ext x
    simp only [DisconnectedInvolutionGraph.Helpers.conjugateSubgroup, Subgroup.mem_comap,
      Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨g⁻¹ * x * g, by simpa using hx, by group⟩
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
  rwa [heq] at h'

theorem barIn_closed {J J₀ : Subgroup G}
    (hclo : ∀ u ∈ J₀, orderOf u = 2 → centralizer ({u} : Set G) ⊓ J ≤ J₀) :
    ∀ t ∈ barIn J J₀, orderOf t = 2 → centralizer ({t} : Set (HBar J)) ≤ barIn J J₀ := by
  intro t ht ht2 y hy
  obtain ⟨u, huJ₀, hu2, hut⟩ := exists_lift_involution_in ht ht2
  have hu2' : orderOf (u : G) = 2 := by rw [← hu2]; exact Subgroup.orderOf_coe u
  have hcen := centralizer_mk_eq J hu2' u.2
  have hty : y ∈ centralizer ({mkH J ⟨(u : G), u.2⟩} : Set (HBar J)) := by
    have : mkH J ⟨(u : G), u.2⟩ = t := hut
    rw [this]
    exact hy
  rw [hcen] at hty
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hty
  rw [Subgroup.mem_subgroupOf] at hw
  have hwJ₀ : (w : G) ∈ J₀ := hclo (u : G) huJ₀ hu2' ⟨hw, w.2⟩
  exact Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 hwJ₀, rfl⟩

end SE

section Main
variable {G : Type} [Group G] [Finite G]

theorem exists_two_nontrivial {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : Open.IsElemAbelian 2 E) (hcard : 4 ≤ Nat.card ↥E) :
    ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  have hnt : E ≠ ⊥ := by
    intro h
    rw [h] at hcard
    simp at hcard
  obtain ⟨a, haE, ha1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left hnt
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hE.2 a haE) ha1
  have hz : Nat.card ↥(zpowers a) = 2 := by rw [Nat.card_zpowers, ha2]
  obtain ⟨b, hbE, hbz⟩ : ∃ b ∈ E, b ∉ zpowers a := by
    by_contra hno
    push Not at hno
    have hle : E ≤ zpowers a := fun b hb => hno b hb
    have := Subgroup.card_le_of_le hle
    omega
  exact ⟨a, haE, b, hbE, ha1, fun h => hbz (h ▸ one_mem _), fun h => hbz (h ▸ mem_zpowers a)⟩

theorem J_le_J0 {J J₀ : Subgroup G}
    (hle : J₀ ≤ J) (hD : DihJ (HBar J)) (hns : ¬ Group.IsSolvable ↥J₀)
    (hclo : ∀ u ∈ J₀, orderOf u = 2 → centralizer ({u} : Set G) ⊓ J ≤ J₀) : J ≤ J₀ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbarns : ¬ Group.IsSolvable (HBar J) := by
    intro hs
    exact hns (isSolvable_of_barIn hle inferInstance)
  have hs : IsSimpleGroup (HBar J) := hD.isSimple hbarns
  have hnab := hD.nonabelian hbarns
  have hKtop : barIn J J₀ = ⊤ := by
    by_contra hne
    have heven : Even (Nat.card ↥J₀) := by
      by_contra hodd
      exact hns (CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.1 hodd))
    obtain ⟨u, hu2⟩ := exists_prime_orderOf_dvd_card' (G := ↥J₀) 2 (even_iff_two_dvd.1 heven)
    have huJ : (u : G) ∈ J := hle u.2
    have hu2G : orderOf (u : G) = 2 := by rw [← hu2]; exact Subgroup.orderOf_coe u
    have hu2' : orderOf (⟨(u : G), huJ⟩ : ↥J) = 2 := by rw [Subgroup.orderOf_mk]; exact hu2G
    have ht0 : orderOf (mkH J ⟨(u : G), huJ⟩) = 2 := orderOf_mk_eq_two J hu2'
    have ht0K : mkH J ⟨(u : G), huJ⟩ ∈ barIn J J₀ :=
      Subgroup.mem_map.2 ⟨⟨(u : G), huJ⟩, Subgroup.mem_subgroupOf.2 u.2, rfl⟩
    obtain ⟨M, hM⟩ := exists_stronglyEmbedded_of_closed hs hne ht0 ht0K (barIn_closed hclo)
    have hB := BenderSuzuki.bender_suzuki M (helpers_to_order hM)
    obtain ⟨e⟩ := Uniqueness.SU.K.R6.Strong.nonempty_mulEquiv_alt5_of_bender_dihedral hB
      hD.hasDihedralSylowTwo
    have hcard : Nat.card (HBar J) = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    have hlt : Nat.card ↥(barIn J J₀) < 60 := by
      have := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hne)
      rwa [Subgroup.card_top, hcard] at this
    exact hns (isSolvable_of_barIn hle (CFSG.GroupTheory.groups_order_below_sixty_solvable hlt))
  have hevenJ : Even (Nat.card (HBar J)) := CFSG.GH74.even_card_of_nonabelian_simple hnab
  have h2rk : 2 ≤ Open.pRank 2 (⊤ : Subgroup (HBar J)) :=
    CFSG.Walter.two_le_twoRank (HBar J) hnab hevenJ
  obtain ⟨E, -, hEa, hEcard⟩ := SectionRank.exists_pRank (G := HBar J) (p := 2) (by norm_num) ⊤
  have hE4 : 4 ≤ Nat.card ↥E := by
    rw [hEcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ Open.pRank 2 (⊤ : Subgroup (HBar J)) := Nat.pow_le_pow_right (by norm_num) h2rk
  obtain ⟨a, haE, b, hbE, ha1, hb1, hab⟩ := exists_two_nontrivial hEa hE4
  have ha2 : orderOf a = 2 := orderOf_eq_prime (hEa.2 a haE) ha1
  have hb2 : orderOf b = 2 := orderOf_eq_prime (hEa.2 b hbE) hb1
  have hcomm : a * b = b * a := by
    have := hEa.1
    exact congrArg Subtype.val (mul_comm' (⟨a, haE⟩ : ↥E) ⟨b, hbE⟩)
  have haK : a ∈ barIn J J₀ := hKtop ▸ Subgroup.mem_top a
  obtain ⟨u, huJ₀, hu2, hua⟩ := exists_lift_involution_in haK ha2
  have hu2' : orderOf (u : G) = 2 := by rw [← hu2]; exact Subgroup.orderOf_coe u
  have hcenu := centralizer_mk_eq J hu2' u.2
  have hbc : b ∈ centralizer ({mkH J ⟨(u : G), u.2⟩} : Set (HBar J)) := by
    have : mkH J ⟨(u : G), u.2⟩ = a := hua
    rw [this, Subgroup.mem_centralizer_singleton_iff]
    exact hcomm.symm
  rw [hcenu] at hbc
  obtain ⟨w, hw, hwb⟩ := Subgroup.mem_map.1 hbc
  rw [Subgroup.mem_subgroupOf] at hw
  have hwJ₀ : (w : G) ∈ J₀ := hclo (u : G) huJ₀ hu2' ⟨hw, w.2⟩
  have hbK : b ∈ barIn J (centralizer ({(u : G)} : Set G) ⊓ J₀) :=
    Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 ⟨hw, hwJ₀⟩, hwb⟩
  obtain ⟨v, hvX, hv2, hvb⟩ := exists_lift_involution_in hbK hb2
  have huv : u * v = v * u := Subtype.ext
    (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hvX).1).symm
  have hu1 : u * u = 1 := by
    have h' := pow_orderOf_eq_one u
    rw [hu2] at h'
    simpa [pow_two] using h'
  have hv1 : v * v = 1 := by
    have h' := pow_orderOf_eq_one v
    rw [hv2] at h'
    simpa [pow_two] using h'
  have hu1ne : u ≠ 1 := fun h => by rw [h, orderOf_one] at hu2; omega
  have hv1ne : v ≠ 1 := fun h => by rw [h, orderOf_one] at hv2; omega
  have huvne : u ≠ v := fun h => hab (by rw [← hua, ← hvb, h])
  have hK₁₂ : ∀ x ∈ zpowers u, ∀ y ∈ zpowers v, x * y = y * x := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_zpow (show Commute u v from huv) m n).eq
  have hinf : zpowers u ⊓ zpowers v = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases mem_zpowers_of_sq hu1 hx.1 with rfl | rfl
    · exact Subgroup.one_mem _
    · rcases mem_zpowers_of_sq hv1 hx.2 with h | h
      · exact absurd h hu1ne
      · exact absurd h huvne
  obtain ⟨F, hFle, hFea, hFcard⟩ := exists_elemAbelian_join hK₁₂ hinf (E := zpowers u)
    (E' := zpowers v) le_rfl le_rfl (isElemAbelian_zpowers hu1) (isElemAbelian_zpowers hv1)
    (card_zpowers_sq hu1 hu1ne) (card_zpowers_sq hv1 hv1ne)
  have hFcard' : Nat.card ↥F = 2 ^ 2 := by simpa using hFcard
  have hnorm : F ≤ normalizer ((pPrimeCore 2 ↥J : Subgroup ↥J) : Set ↥J) :=
    le_of_le_of_eq le_top (Subgroup.normalizer_eq_top_iff.2 inferInstance).symm
  have hcop : ¬ 2 ∣ Nat.card ↥(pPrimeCore 2 ↥J) := fun hd =>
    (Nat.not_even_iff_odd.2 (odd_card_pPrimeCore J)) (even_iff_two_dvd.2 hd)
  have hgen := CFSG.LargeEvenClassification.Helpers.coprime_plane_centralizers_generate Nat.prime_two
    F (pPrimeCore 2 ↥J) hFea hFcard' hnorm hcop
  have hFJ₀ : zpowers u ⊔ zpowers v ≤ J₀.subgroupOf J :=
    sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 huJ₀))
      (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 hvX).2))
  have hOle : pPrimeCore 2 ↥J ≤ J₀.subgroupOf J := by
    rw [← hgen]
    refine iSup_le fun el => ?_
    intro y hy
    obtain ⟨-, hyC⟩ := Subgroup.mem_inf.1 hy
    have helJ₀ : ((el.1.1 : ↥J) : G) ∈ J₀ := Subgroup.mem_subgroupOf.1 (hFJ₀ (hFle el.1.2))
    have hel2 : orderOf ((el.1.1 : ↥J) : G) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime (hFea.2 _ el.1.2) (fun h => el.2 (Subtype.ext h))
    have hyc : (y : G) * ((el.1.1 : ↥J) : G) = ((el.1.1 : ↥J) : G) * (y : G) := by
      have := Subgroup.mem_centralizer_singleton_iff.1 hyC
      exact congrArg Subtype.val this
    have hycent : (y : G) ∈ centralizer ({((el.1.1 : ↥J) : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hyc
    exact Subgroup.mem_subgroupOf.2 (hclo _ helJ₀ hel2 ⟨hycent, y.2⟩)
  intro j hj
  have hjK : mkH J ⟨j, hj⟩ ∈ barIn J J₀ := hKtop ▸ Subgroup.mem_top _
  obtain ⟨j₀, hj₀, hmk⟩ := Subgroup.mem_map.1 hjK
  have hq : j₀⁻¹ * ⟨j, hj⟩ ∈ pPrimeCore 2 ↥J := QuotientGroup.eq.1 hmk
  have hq' : j₀⁻¹ * ⟨j, hj⟩ ∈ J₀.subgroupOf J := hOle hq
  have hmul := (J₀.subgroupOf J).mul_mem hj₀ hq'
  have : (⟨j, hj⟩ : ↥J) ∈ J₀.subgroupOf J := by simpa using hmul
  exact this

end Main

end CFSG.GH74.GLS.Stage2.Local.P34
