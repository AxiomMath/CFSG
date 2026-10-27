module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.TableL2
public import CFSG.RankThree.ThinCatalog.MathieuThreeRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J2Local
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HSLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.HeLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.RuLocal
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4Local
public import CFSG.LocalAnalysis.SectionRank.SporadicWitnesses
public import CFSG.Sporadic.Schreier.J1OddCore
public import CFSG.Sporadic.J1

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG.Blueprint
open scoped commutatorElement

@[expose] def SporadicBridges : Prop :=
  ∀ s : TauCeti.SporadicName, Nonempty (NativeSporadic.Carrier s ≃* s.Group)

theorem two_le_pRank_of_square_witness' {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {x y : G} (hx : x ^ r = 1) (hy : y ^ r = 1) (hxy : x * y = y * x)
    (hcard : Nat.card (Subgroup.closure ({x, y} : Set G)) = r ^ 2) :
    2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 := hr.two_le
  have hcyc : ∀ z : G, z ^ r = 1 → Nat.card (Subgroup.zpowers z) ≤ r := fun z hz => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd hr.pos (orderOf_dvd_of_pow_eq_one hz)
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hy hxy ?_
    fun n hn => ?_
  · rintro rfl
    have hle : Subgroup.closure ({1, y} : Set G) ≤ Subgroup.zpowers y := by
      rw [Subgroup.closure_le]
      rintro a (rfl | rfl)
      · exact Subgroup.one_mem _
      · exact Subgroup.mem_zpowers _
    have := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    have h1 := hcyc y hy
    rw [hcard] at this
    nlinarith
  · have hle : Subgroup.closure ({x, y} : Set G) ≤ Subgroup.zpowers x := by
      rw [Subgroup.closure_le]
      rintro a (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · rw [← hn]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
    have := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    have h1 := hcyc x hx
    rw [hcard] at this
    nlinarith

theorem two_le_pRank_of_cubic_witness' {G : Type*} [Group G] [Finite G] {r : ℕ} (hr : r.Prime)
    {x y : G} (hx : x ^ r = 1) (hz1 : ⁅x, y⁆ ≠ 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) : 2 ≤ CFSG.Open.pRank r (⊤ : Subgroup G) := by
  have : Fact r.Prime := ⟨hr⟩
  have hzr : ⁅x, y⁆ ^ r = 1 := by
    rw [CFSG.SectionRank.LocalWitness.commutator_pow_eq hzx, hx, commutatorElement_one_left]
  refine CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_of_gens hx hzr hzx.symm ?_
    fun n hn => ?_
  · rintro rfl
    exact hz1 (commutatorElement_one_left y)
  · have hnr : ¬ r ∣ n := by
      rintro ⟨k, rfl⟩
      apply hz1
      rw [← hn, pow_mul, hx, one_pow]
    have hcop : Nat.Coprime n r := (Nat.Prime.coprime_iff_not_dvd hr).2 hnr |>.symm
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
    have hxz : x = ⁅x, y⁆ ^ m := by
      rw [← hn, ← pow_mul, pow_eq_pow_mod _ (show x ^ r = 1 from hx), hm, pow_one]
    apply hz1
    have hxy : Commute x y := by
      rw [hxz]
      exact hzy.pow_left m
    exact commutatorElement_eq_one_iff_mul_comm.2 hxy.eq

theorem two_le_pRank_three_of_equiv {G C : Type} [Group G] [Finite G] [Group C] [Finite C]
    (e : G ≃* C) (h : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup C)) :
    2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G) := by
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e]
  exact h

theorem threeTwoWitness_of_equiv_J1
    {G : Type} [Group G] [Finite G]
    (e : G ≃* NativeSporadic.J1) : ThreeTwoWitness G := by
  have hcard : Nat.card G = 175560 := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.J1.card_J1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := G) 2 (by rw [hcard]; norm_num)
  have h120 := (CFSG.Sporadic.Schreier.ctugs_j1_involution_centralizer_odd_core_free ⟨e⟩ t ht).1
  have h3 : 3 ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
    rw [h120]
    norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({t} : Set G)) 3 h3
  refine ThreeTwoWitness.of_commuting (g := t) (x := (x : G)) ?_ ?_ ?_ ?_
  · rw [← ht]
    exact pow_orderOf_eq_one t
  · intro h
    rw [h, orderOf_one] at ht
    omega
  · rw [Subgroup.orderOf_coe]
    exact hx
  · exact Subgroup.mem_centralizer_iff.1 x.2 t rfl

theorem sporadicLocalCensus_of_bridges
    (hB : SporadicBridges) : SporadicLocalCensus := by
  intro s _ hnt
  obtain ⟨b⟩ := hB s
  have e : s.Group ≃* NativeSporadic.Carrier s := b.symm
  have hfinC : Finite (NativeSporadic.Carrier s) := Finite.of_equiv _ e.toEquiv
  have hntC : Nontrivial (NativeSporadic.Carrier s) := e.injective.nontrivial
  have h14 : s ∉ CFSG.SectionRank.sqtkSporadicNames → s ≠ .M →
      2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup s.Group) := fun h1 h2 => by
    obtain ⟨E, hE, k, hk, hc⟩ := CFSG.SectionRank.sporadicThreeRankWitnesses s h1 h2
    refine two_le_pRank_three_of_equiv e ?_
    exact (by omega : 2 ≤ k).trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)
  have hnames : ∀ t : TauCeti.SporadicName, t ∈ CFSG.SectionRank.sqtkSporadicNames ↔
      (t = .M11 ∨ t = .M12 ∨ t = .M22 ∨ t = .M23 ∨ t = .M24 ∨ t = .J1 ∨ t = .J2 ∨ t = .J4 ∨
        t = .HS ∨ t = .He ∨ t = .Ru) := fun t => by
    cases t <;> simp [CFSG.SectionRank.sqtkSporadicNames]
  have h3 : Nat.Prime 3 := Nat.prime_three
  cases s with
  | M11 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.ThinCatalog.two_le_pRank_three_M11_sylow (MulEquiv.refl _)
  | M22 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.ThinCatalog.two_le_pRank_three_M22_sylow (MulEquiv.refl _)
  | M23 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact CFSG.RankThree.ThinCatalog.two_le_pRank_three_M23_sylow (MulEquiv.refl _)
  | M12 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.M12_sylow3_cubic_witness
    exact two_le_pRank_of_cubic_witness' h3 hx hz hzx hzy
  | M24 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.M24_sylow3_cubic_witness
    exact two_le_pRank_of_cubic_witness' h3 hx hz hzx hzy
  | J2 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.J2_sylow3_cubic_witness
    exact two_le_pRank_of_cubic_witness' h3 hx hz hzx hzy
  | J4 =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.J4_sylow3_cubic_witness
    exact two_le_pRank_of_cubic_witness' h3 hx hz hzx hzy
  | He =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.He_sylow3_cubic_witness
    exact two_le_pRank_of_cubic_witness' h3 hx hz hzx hzy
  | Ru =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, -, hz, hzx, hzy, -⟩ := CFSG.SectionRank.Ru_sylow3_cubic_witness
    exact two_le_pRank_of_cubic_witness' h3 hx hz hzx hzy
  | HS =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    obtain ⟨x, y, -, hx, hy, hxy, hQ, -⟩ := CFSG.SectionRank.HS_sylow3_square_witness
    exact two_le_pRank_of_square_witness' h3 hx hy hxy hQ
  | J1 =>
    exact Or.inr (ThreeTwoWitness.of_mulEquiv e.symm
      (threeTwoWitness_of_equiv_J1 (G := _) (MulEquiv.refl _)))
  | M =>
    left
    refine two_le_pRank_three_of_equiv e ?_
    have : Nontrivial NativeSporadic.M := hntC
    have : Finite NativeSporadic.M := hfinC
    obtain ⟨E, hE, hc⟩ := CFSG.SectionRank.M_nontrivial_elementary_three_rank_four
    exact (by norm_num : 2 ≤ 4).trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hE hc)
  | _ => exact Or.inl (h14 (by simp [hnames]) (by simp))

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
