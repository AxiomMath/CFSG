module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoUnipotentCentralizer
import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerTwoGroups
import CFSG.GroupTheory.HyperplaneGeneration

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

variable {G : Type} [Group G] [Finite G]

open CFSG.GorensteinWalter CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC in
private theorem lq_factorization {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) {L : Subgroup G}
    (e : L ≃* CFSG.AGLEmbedding.PSL2GF p n) :
    (Nat.card L).factorization p = n := by
  have hp : p.Prime := Fact.out
  obtain ⟨T⟩ := (inferInstance : Nonempty (Sylow p (CFSG.AGLEmbedding.PSL2GF p n)))
  have h1 := (CFSG.AGLEmbedding.psl2GF_sylow p n hn T).2
  have h2 := Sylow.card_eq_multiplicity T
  have h3 : (Nat.card (CFSG.AGLEmbedding.PSL2GF p n)).factorization p = n :=
    Nat.pow_right_injective hp.two_le (h2.symm.trans h1)
  rw [Nat.card_congr e.toEquiv]
  exact h3

open CFSG.GorensteinWalter CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC in
private theorem lq_exists_mulEquiv {p n : ℕ} [Fact p.Prime] (hn : 1 ≤ n) {L U : Subgroup G}
    (e : L ≃* PSL2 (GaloisField p n)) (hU : IsSylowOf p U L) :
    ∃ e' : L ≃* PSL2 (GaloisField p n), ∀ g : L,
      (g : G) ∈ U ↔ e' g ∈ psl2UpperUnipotentSubgroup (GaloisField p n) := by
  have hK : Nat.card (GaloisField p n) = p ^ n := GaloisField.card p n (by omega)
  set U'' : Subgroup L := (psl2UpperUnipotentSubgroup (GaloisField p n)).map e.symm.toMonoidHom
    with hU''
  have hU''mem : ∀ g : L, g ∈ U'' ↔ e g ∈ psl2UpperUnipotentSubgroup (GaloisField p n) := by
    intro g
    rw [hU'', Subgroup.mem_map_equiv]
    simp
  have hU''card : Nat.card U'' = p ^ n := by
    rw [hU'', Subgroup.card_map_of_injective e.symm.injective, psl2UpperUnipotentSubgroup_card,
      hK]
  have hU''syl : IsSylowOf p (U''.map L.subtype) L := by
    refine isSylowOf_of_card (map_subtype_le _) ?_
    rw [Subgroup.card_map_of_injective L.subtype_injective, hU''card, lq_factorization hn e]
  obtain ⟨k, hk, hconj⟩ := hU''syl.exists_mem_conj hU
  refine ⟨(MulAut.conj (⟨k, hk⟩ : L)⁻¹).trans e, fun g => ?_⟩
  have h1 := hconj (g : G)
  have h2 : (k⁻¹ * (g : G) * k) = L.subtype ((⟨k, hk⟩ : L)⁻¹ * g * ⟨k, hk⟩) := by simp
  rw [h1, h2, Subgroup.mem_map_iff_mem L.subtype_injective, hU''mem]
  simp

open CFSG.GorensteinWalter CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC in
theorem eq_bot_of_coprime_of_le_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n)
    {L : Subgroup G} (e : L ≃* CFSG.AGLEmbedding.PSL2GF p n) {U : Subgroup G} (hUL : U ≤ L)
    (hUp : IsPGroup p U) (hUc : Nat.card U = p ^ n) {W : Subgroup G} (hWL : W ≤ L)
    (hUW : U ≤ normalizer (W : Set G)) (hW : Nat.Coprime p (Nat.card W)) : W = ⊥ := by
  have hp : p.Prime := Fact.out
  have hSyl : IsSylowOf p U L :=
    isSylowOf_of_card hUL (by rw [hUc, lq_factorization (by omega) e])
  obtain ⟨e', he'⟩ := lq_exists_mulEquiv (by omega) e hSyl
  have hroot : ∀ u : G, ∀ hu : u ∈ U, ∃ a : GaloisField p n,
      e' ⟨u, hUL hu⟩ = psl2Root a := fun u hu =>
    (mem_psl2UpperUnipotentSubgroup_iff _).1 ((he' ⟨u, hUL hu⟩).1 hu)
  have hcommU : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u := by
    intro u hu v hv
    obtain ⟨a, ha⟩ := hroot u hu
    obtain ⟨b, hb⟩ := hroot v hv
    have h : e' (⟨u, hUL hu⟩ * ⟨v, hUL hv⟩) = e' (⟨v, hUL hv⟩ * ⟨u, hUL hu⟩) := by
      rw [map_mul, map_mul, ha, hb, ← psl2Root_add, ← psl2Root_add, add_comm]
    exact congrArg Subtype.val (e'.injective h)
  have hpowU : ∀ u ∈ U, u ^ p = 1 := by
    intro u hu
    obtain ⟨a, ha⟩ := hroot u hu
    have h1 : e' ((⟨u, hUL hu⟩ : L) ^ p) = 1 := by rw [map_pow, ha, psl2Root_pow_prime]
    exact congrArg Subtype.val (e'.injective (h1.trans (map_one e').symm))
  have hUel : CFSG.Open.IsElemAbelian p U :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommU a a.2 b b.2)⟩⟩, hpowU⟩
  letI : CFSG.IsElementaryAbelian p U :=
    { toIsMulCommutative := hUel.1
      exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun g => by
        apply Subtype.ext
        simpa using hUel.2 g.1 g.2 }
  letI inst : MulDistribMulAction U W := Subgroup.conjMulDistribMulActionOfLeNormalizer U W hUW
  have hA2 : p ^ 2 ≤ Nat.card U := by
    rw [hUc]
    exact Nat.pow_le_pow_right hp.pos hn
  have hpW : ¬ p ∣ Nat.card W := (Nat.Prime.coprime_iff_not_dvd hp).mp hW
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation hA2 hpW
  have hWU : W ⊓ U = ⊥ := by
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [hUc]
    exact (Nat.Coprime.pow_right n hW.symm)
  have hle : (⊤ : Subgroup ↥W) ≤ ⊥ := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha g hg => ?_
    have hag : a • g = g := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a g).mp hg
    have hcon0 := congrArg Subtype.val hag
    have hcon : (a : G) * (g : G) * (a : G)⁻¹ = (g : G) := hcon0
    have hcomm' : (g : G) * (a : G) = (a : G) * (g : G) := (mul_inv_eq_iff_eq_mul.mp hcon).symm
    have hane : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    obtain ⟨a₀, ha₀⟩ := hroot a a.2
    have ha₀ne : a₀ ≠ 0 := by
      rintro rfl
      apply hane
      have h1 : e' (⟨(a : G), hUL a.2⟩ : L) = 1 := by rw [ha₀, psl2Root_zero]
      exact congrArg Subtype.val (e'.injective (h1.trans (map_one e').symm))
    have hcl : e' ⟨(g : G), hWL g.2⟩ * psl2Root a₀ = psl2Root a₀ * e' ⟨(g : G), hWL g.2⟩ := by
      rw [← ha₀, ← map_mul, ← map_mul]
      exact congrArg e' (Subtype.ext hcomm')
    have hgU : (g : G) ∈ U := (he' ⟨(g : G), hWL g.2⟩).2 (mem_upperUnipotent_of_commute ha₀ne hcl)
    have h2 : (g : G) ∈ W ⊓ U := ⟨g.2, hgU⟩
    rw [hWU, Subgroup.mem_bot] at h2
    exact Subgroup.mem_bot.mpr (Subtype.ext h2)
  rw [eq_bot_iff]
  intro w hw
  have h := hle (Subgroup.mem_top (⟨w, hw⟩ : ↥W))
  rw [Subgroup.mem_bot] at h ⊢
  exact congrArg Subtype.val h

open CFSG.GorensteinWalter CFSG.ABGLocalTools CFSG.LocalAnalysis.RankThreeTheoremC in
theorem le_centralizer_of_coprime_of_psl2GF {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hn : 2 ≤ n)
    {L : Subgroup G} (e : L ≃* CFSG.AGLEmbedding.PSL2GF p n) {U : Subgroup G} (hUL : U ≤ L)
    (hUp : IsPGroup p U) (hUc : Nat.card U = p ^ n) {Y : Subgroup G}
    (hYL : Y ≤ normalizer (L : Set G)) (hUY : U ≤ normalizer (Y : Set G))
    (hY : Nat.Coprime p (Nat.card Y)) : Y ≤ centralizer (L : Set G) := by
  have hp : p.Prime := Fact.out
  have hSyl : IsSylowOf p U L :=
    isSylowOf_of_card hUL (by rw [hUc, lq_factorization (by omega) e])
  have hYLbot : Y ⊓ L = ⊥ := by
    refine eq_bot_of_coprime_of_le_of_psl2GF hp2 hn e hUL hUp hUc inf_le_right ?_ ?_
    · intro u hu
      rw [mem_normalizer_iff]
      intro h
      have h1 := mem_normalizer_iff.mp (hUY hu) h
      have h2 : h ∈ L ↔ u * h * u⁻¹ ∈ L :=
        ⟨fun hh => L.mul_mem (L.mul_mem (hUL hu) hh) (L.inv_mem (hUL hu)), fun hh => by
          simpa [mul_assoc] using L.mul_mem (L.mul_mem (L.inv_mem (hUL hu)) hh) (hUL hu)⟩
      exact ⟨fun hh => ⟨h1.mp hh.1, h2.mp hh.2⟩, fun hh => ⟨h1.mpr hh.1, h2.mpr hh.2⟩⟩
    · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hY
  intro y hy
  have hyN : y ∈ normalizer (L : Set G) := hYL hy
  have hcommU : ∀ u ∈ U, y * u * y⁻¹ = u := by
    intro u hu
    have hmemY : y * u * y⁻¹ * u⁻¹ ∈ Y := by
      have h1 : u * y⁻¹ * u⁻¹ ∈ Y := (mem_normalizer_iff.mp (hUY hu) y⁻¹).mp (Y.inv_mem hy)
      have := Y.mul_mem hy h1
      simpa [mul_assoc] using this
    have hmemL : y * u * y⁻¹ * u⁻¹ ∈ L := by
      have h1 : y * u * y⁻¹ ∈ L := (mem_normalizer_iff.mp hyN u).mp (hUL hu)
      exact L.mul_mem h1 (L.inv_mem (hUL hu))
    have h3 : y * u * y⁻¹ * u⁻¹ ∈ Y ⊓ L := ⟨hmemY, hmemL⟩
    rw [hYLbot, Subgroup.mem_bot, mul_inv_eq_one] at h3
    exact h3
  obtain ⟨T, hT⟩ := hSyl
  have hes : Function.Surjective (e : L →* CFSG.AGLEmbedding.PSL2GF p n) := e.surjective
  set U' : Sylow p (CFSG.AGLEmbedding.PSL2GF p n) := T.mapSurjective hes with hU'
  have hU'mem : ∀ u ∈ (U' : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)),
      ∃ t ∈ (T : Subgroup L), e t = u := by
    intro u hu
    rw [hU', Sylow.coe_mapSurjective] at hu
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hu
    exact ⟨t, ht, rfl⟩
  have htU : ∀ t ∈ (T : Subgroup L), ((t : L) : G) ∈ U := fun t ht =>
    hT ▸ Subgroup.mem_map_of_mem L.subtype ht
  set φ : MulAut L := L.normalizerMonoidHom ⟨y, hyN⟩ with hφ
  have hφapp : ∀ l : L, ((φ l : L) : G) = y * l * y⁻¹ := fun l => rfl
  set α : MulAut (CFSG.AGLEmbedding.PSL2GF p n) := MulAut.congr e φ with hα
  have hαe : ∀ k : L, α (e k) = e (φ k) := fun k => by simp [hα, MulAut.congr]
  have hfix : ∀ u ∈ (U' : Subgroup (CFSG.AGLEmbedding.PSL2GF p n)), α u = u := by
    intro u hu
    obtain ⟨t, ht, rfl⟩ := hU'mem u hu
    rw [hαe]
    congr 1
    exact Subtype.ext (by rw [hφapp]; exact hcommU _ (htU t ht))
  obtain ⟨u, hu, hαu⟩ := CFSG.AGLEmbedding.kFactL2UnipotentCentralizer p n hp2 (by omega) U' α
    hfix
  obtain ⟨t, ht, rfl⟩ := hU'mem u hu
  have hconj : ∀ l ∈ L, y * l * y⁻¹ = (t : G) * l * (t : G)⁻¹ := by
    intro l hlL
    have h := hαe ⟨l, hlL⟩
    rw [hαu, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul] at h
    have h' := congrArg Subtype.val (e.injective h)
    rw [hφapp] at h'
    simpa using h'.symm
  have hz : (t : G)⁻¹ * y ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro l hlL
    have h := hconj l hlL
    calc l * ((t : G)⁻¹ * y) = (t : G)⁻¹ * ((t : G) * l * (t : G)⁻¹) * y := by group
      _ = (t : G)⁻¹ * (y * l * y⁻¹) * y := by rw [← h]
      _ = (t : G)⁻¹ * y * l := by group
  have htU' : (t : G) ∈ U := htU t ht
  have htL : (t : G) ∈ L := hUL htU'
  have hty : y * (t : G) = (t : G) * y := by
    have := hcommU _ htU'
    exact mul_inv_eq_iff_eq_mul.mp this
  have hcz : Commute (t : G) ((t : G)⁻¹ * y) := by
    show (t : G) * ((t : G)⁻¹ * y) = ((t : G)⁻¹ * y) * (t : G)
    rw [mul_inv_cancel_left, mul_assoc, hty, inv_mul_cancel_left]
  have hym : y ^ Nat.card Y = 1 := by
    have := pow_card_eq_one' (G := Y) (x := ⟨y, hy⟩)
    exact congrArg Subtype.val this
  have htm : (t : G) ^ Nat.card Y = 1 := by
    have h1 : y = (t : G) * ((t : G)⁻¹ * y) := by group
    have h2 : y ^ Nat.card Y = (t : G) ^ Nat.card Y * ((t : G)⁻¹ * y) ^ Nat.card Y := by
      conv_lhs => rw [h1]
      exact hcz.mul_pow _
    have hzm : ((t : G)⁻¹ * y) ^ Nat.card Y ∈ centralizer (L : Set G) :=
      Subgroup.pow_mem _ hz _
    have htmL : (t : G) ^ Nat.card Y ∈ L := Subgroup.pow_mem _ htL _
    have htmc : (t : G) ^ Nat.card Y ∈ centralizer (L : Set G) := by
      have h3 : (t : G) ^ Nat.card Y = (((t : G)⁻¹ * y) ^ Nat.card Y)⁻¹ := by
        rw [hym] at h2
        exact eq_inv_of_mul_eq_one_left (h2.symm)
      rw [h3]
      exact Subgroup.inv_mem _ hzm
    have hc : (⟨(t : G) ^ Nat.card Y, htmL⟩ : L) ∈ Subgroup.center L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (mem_centralizer_iff.mp htmc l l.2)
    have hc' : e ⟨(t : G) ^ Nat.card Y, htmL⟩ ∈ Subgroup.center (CFSG.AGLEmbedding.PSL2GF p n) := by
      rw [Subgroup.mem_center_iff]
      intro z'
      obtain ⟨l, rfl⟩ := e.surjective z'
      rw [← map_mul, ← map_mul]
      exact congrArg e (Subtype.ext (mem_centralizer_iff.mp htmc l l.2))
    rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot] at hc'
    have h4 : (⟨(t : G) ^ Nat.card Y, htmL⟩ : L) = 1 := e.injective (hc'.trans (map_one e).symm)
    exact congrArg Subtype.val h4
  have hord1 : orderOf (t : G) ∣ Nat.card U := by
    have := orderOf_dvd_natCard (⟨(t : G), htU'⟩ : U)
    rwa [← Subgroup.orderOf_coe] at this
  have hord2 : orderOf (t : G) ∣ Nat.card Y := orderOf_dvd_of_pow_eq_one htm
  have hcop : Nat.Coprime (Nat.card U) (Nat.card Y) := by
    rw [hUc]
    exact Nat.Coprime.pow_left n hY
  have ht1 : (t : G) = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord1 hord2)
  rw [ht1, inv_one, one_mul] at hz
  exact hz

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
