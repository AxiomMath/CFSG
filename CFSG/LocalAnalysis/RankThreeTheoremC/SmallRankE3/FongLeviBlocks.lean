module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviLevi
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockGroups
public import CFSG.GroupTheory.PGroup.RankTwoCommute

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open

theorem leviBlock_mulSingle_mem_pi {ι : Type} [DecidableEq ι] {G : ι → Type}
    [∀ j, Group (G j)] (S : ∀ j, Subgroup (G j)) {k : ι} {w : G k} (hw : w ∈ S k) :
    (Pi.mulSingle k w : ∀ j, G j) ∈ Subgroup.pi Set.univ S := by
  rw [Subgroup.mem_pi]
  intro i _
  by_cases h : i = k
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact hw
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (S i).one_mem

theorem leviBlock_pRank_range_le_one {X : Type} [Group X] [Finite X] {P : Subgroup X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1)
    {M : Type} [Group M] [Finite M] (β : ↥P →* M) (hβ : IsPGroup 2 β.ker) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥β.range) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcard : ¬ p ∣ Nat.card β.ker := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hβ
    intro hdvd
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))
  have hq := CFSG.SectionRank.pRank_quotient_eq β.ker hcard
  have he := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
    (QuotientGroup.quotientKerEquivRange β)
  have hP := CFSG.SectionRank.pRank_top_le_of_injective hp.one_lt P.subtype P.subtype_injective
  rw [← he, hq]
  exact hP.trans hrk

theorem leviBlock_eq_one_of_ne {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ j, Group (G j)] [∀ j, Finite (G j)] {p : ℕ} (hp : p.Prime)
    (S : ∀ j, Subgroup (G j)) (R : Subgroup (∀ j, G j)) (hS : Subgroup.pi Set.univ S ≤ R)
    (hrankR : CFSG.Open.pRank p (⊤ : Subgroup ↥R) ≤ 1)
    {j₀ : ι} {u₀ : G j₀} (hu₀S : u₀ ∈ S j₀) (hu₀ord : orderOf u₀ = p)
    {j : ι} (hj : j ≠ j₀) {v : G j} (hvS : v ∈ S j) (hvp : v ^ p = 1) : v = 1 := by
  by_contra hv
  haveI : Fact p.Prime := ⟨hp⟩
  have hvord : orderOf v = p := orderOf_eq_prime hvp hv
  have haord : orderOf (Pi.mulSingle j₀ u₀ : ∀ j, G j) = p := by
    rw [orderOf_piMulSingle, hu₀ord]
  have hbord : orderOf (Pi.mulSingle j v : ∀ j, G j) = p := by
    rw [orderOf_piMulSingle, hvord]
  have hcomm : Commute (Pi.mulSingle j₀ u₀ : ∀ j, G j) (Pi.mulSingle j v) :=
    Pi.mulSingle_commute (Ne.symm hj) u₀ v
  have hnot : (Pi.mulSingle j v : ∀ j, G j) ∉ Subgroup.zpowers (Pi.mulSingle j₀ u₀ : ∀ j, G j) := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have h1 : ((Pi.mulSingle j₀ u₀ : ∀ j, G j) ^ n) j = (Pi.mulSingle j v : ∀ j, G j) j := by
      rw [hn]
    rw [Pi.pow_apply, Pi.mulSingle_eq_of_ne hj, one_zpow, Pi.mulSingle_eq_same] at h1
    exact hv h1.symm
  have haR := hS (leviBlock_mulSingle_mem_pi S hu₀S)
  have hbR := hS (leviBlock_mulSingle_mem_pi S hvS)
  have h2 := CFSG.GroupTheory.two_le_pRank_of_commute haR hbR haord hbord hcomm hnot
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup R] at h2
  exact absurd (le_trans h2 hrankR) (by norm_num)

theorem leviBlock_eq_one_of_mem_center {H : Type} [Group H] (c : Subgroup H) {p : ℕ}
    (hp : p.Prime) (hc : ¬ p ∣ Nat.card c) {h : H} (hh : h ∈ c) (hpow : h ^ p = 1) : h = 1 := by
  have hpow' : (⟨h, hh⟩ : c) ^ p = 1 := Subtype.ext (by simpa using hpow)
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hpow') with h1 | h1
  · exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
  · exfalso
    apply hc
    have h3 := orderOf_dvd_natCard (⟨h, hh⟩ : c)
    rwa [h1] at h3

theorem leviBlock_eq_one_of_coord {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type}
    [∀ j, Group (G j)] {p : ℕ} (hp : p.Prime) (S : ∀ j, Subgroup (G j)) {j₀ : ι}
    (hc : ¬ p ∣ Nat.card (Subgroup.center ↥(S j₀)))
    (huniq : ∀ j, j ≠ j₀ → ∀ v : G j, v ∈ S j → v ^ p = 1 → v = 1)
    {y : ∀ j, G j} (hyS : y ∈ Subgroup.pi Set.univ S) (hypow : ∀ j, y j ^ p = 1)
    (hy0 : (⟨y j₀, (Subgroup.mem_pi _).1 hyS j₀ (Set.mem_univ j₀)⟩ : ↥(S j₀)) ∈
      Subgroup.center ↥(S j₀)) :
    y = 1 := by
  have hcentral : y j₀ = 1 := by
    have hpow' : (⟨y j₀, (Subgroup.mem_pi _).1 hyS j₀ (Set.mem_univ j₀)⟩ : ↥(S j₀)) ^ p = 1 :=
      Subtype.ext (by simpa using hypow j₀)
    exact congrArg Subtype.val (leviBlock_eq_one_of_mem_center _ hp hc hy0 hpow')
  funext j
  show y j = (1 : G j)
  by_cases hj : j = j₀
  · rw [hj]
    exact hcentral
  · exact huniq j hj (y j) ((Subgroup.mem_pi _).1 hyS j (Set.mem_univ j)) (hypow j)

theorem leviSurj_of_blocks {X : Type} [Group X] [Finite X] {P : Subgroup X} {z : X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzP : z ∈ P) (hz : orderOf z = p)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (β : ↥P →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (S : ∀ j, Subgroup (G j)) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hperf : ∀ j, ⁅S j, S j⁆ = S j)
    (hpR : ∀ x ∈ β.range, x ^ p = 1 → x ∈ Subgroup.pi Set.univ S)
    (hblk : ∀ j, (∃ u ∈ S j, orderOf u = p) →
      CFSG.Open.IsQuasisimple ↥(S j) ∧ ¬ p ∣ Nat.card (Subgroup.center ↥(S j))) :
    ∃ j₀ : ι, (∃ u ∈ S j₀, orderOf u = p) ∧
      LeviSurj p P z (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨j₀, u₀, hu₀S, hu₀ord⟩ : ∃ j₀ : ι, ∃ u ∈ S j₀, orderOf u = p := by
    have hz0ord : orderOf (⟨z, hzP⟩ : ↥P) = p := by rw [Subgroup.orderOf_mk, hz]
    have hz0ne : β ⟨z, hzP⟩ ≠ 1 := by
      intro h1
      have hker : (⟨z, hzP⟩ : ↥P) ∈ β.ker := MonoidHom.mem_ker.2 h1
      have hpow : (⟨z, hzP⟩ : ↥P) ^ p = 1 := by
        rw [← hz0ord]
        exact pow_orderOf_eq_one _
      have h0 := eq_one_of_mem_ker_of_pow_eq_one β hβ hp hp2 hker hpow
      rw [h0, orderOf_one] at hz0ord
      exact hp.one_lt.ne hz0ord
    have hz0pow : β ⟨z, hzP⟩ ^ p = 1 := by
      rw [← map_pow, ← hz0ord, pow_orderOf_eq_one, map_one]
    have hz0R : β ⟨z, hzP⟩ ∈ β.range := MonoidHom.mem_range.2 ⟨_, rfl⟩
    have hz0S : ∀ j, β ⟨z, hzP⟩ j ∈ S j := fun j =>
      (Subgroup.mem_pi _).1 (hpR _ hz0R hz0pow) j (Set.mem_univ j)
    obtain ⟨j₀, hj₀⟩ : ∃ j₀, β ⟨z, hzP⟩ j₀ ≠ 1 := by
      by_contra h
      push Not at h
      exact hz0ne (by funext j; exact h j)
    refine ⟨j₀, β ⟨z, hzP⟩ j₀, hz0S j₀, orderOf_eq_prime ?_ hj₀⟩
    have h := congrFun hz0pow j₀
    simpa using h
  refine ⟨j₀, ⟨u₀, hu₀S, hu₀ord⟩, ?_⟩
  obtain ⟨hqs, hcz⟩ := hblk j₀ ⟨u₀, hu₀S, hu₀ord⟩
  have hrankR : CFSG.Open.pRank p (⊤ : Subgroup ↥β.range) ≤ 1 :=
    leviBlock_pRank_range_le_one hp hp2 hrk β hβ
  have huniq : ∀ j, j ≠ j₀ → ∀ v : G j, v ∈ S j → v ^ p = 1 → v = 1 :=
    fun j hj v hv hvp => leviBlock_eq_one_of_ne hp S β.range hS hrankR hu₀S hu₀ord hj hv hvp
  have hNperf : ⁅Subgroup.pi Set.univ S, Subgroup.pi Set.univ S⁆ = Subgroup.pi Set.univ S := by
    simp only [Subgroup.commutator_pi_pi_of_finite, hperf]
  have hab : ∀ x ∈ β.range, ∀ y ∈ β.range, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.pi Set.univ S := by
    intro x hx y hy
    have h := hcomm (Subgroup.commutator_mem_commutator hx hy)
    rwa [commutatorElement_def] at h
  let ev : ↥(Subgroup.pi Set.univ S) →* ↥(S j₀) :=
    MonoidHom.mk' (fun x => ⟨x.1 j₀, (Subgroup.mem_pi _).1 x.2 j₀ (Set.mem_univ j₀)⟩)
      (fun x y => Subtype.ext rfl)
  let ρ : ↥(Subgroup.pi Set.univ S) →* ↥(S j₀) ⧸ Subgroup.center ↥(S j₀) :=
    (QuotientGroup.mk' (Subgroup.center ↥(S j₀))).comp ev
  have hρsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨Pi.mulSingle j₀ (s : G j₀), leviBlock_mulSingle_mem_pi S s.2⟩, ?_⟩
    have hev : ev ⟨Pi.mulSingle j₀ (s : G j₀), leviBlock_mulSingle_mem_pi S s.2⟩ = s :=
      Subtype.ext (Pi.mulSingle_eq_same j₀ (s : G j₀))
    exact congrArg (QuotientGroup.mk' (Subgroup.center ↥(S j₀))) hev
  have hρk : ¬ p ∣ Nat.card ρ.ker := by
    intro hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hxp : x ^ p = 1 := by
      rw [← hx]
      exact pow_orderOf_eq_one x
    have hxN : (x.1 : ∀ j, G j) ^ p = 1 := by
      have h := congrArg (fun t : ↥ρ.ker => (t.1 : ∀ j, G j)) hxp
      simpa using h
    have hypow : ∀ j, (x.1 : ∀ j, G j) j ^ p = 1 := fun j => by
      have h := congrFun hxN j
      simpa using h
    have hρx : ρ x.1 = 1 := MonoidHom.mem_ker.1 x.2
    have hy0 : (⟨(x.1 : ∀ j, G j) j₀, (Subgroup.mem_pi _).1 x.1.2 j₀ (Set.mem_univ j₀)⟩ :
        ↥(S j₀)) ∈ Subgroup.center ↥(S j₀) :=
      (QuotientGroup.eq_one_iff (ev x.1)).1 hρx
    have hy1 : (x.1 : ∀ j, G j) = 1 :=
      leviBlock_eq_one_of_coord hp S hcz huniq x.1.2 hypow hy0
    have hx1 : x = 1 := Subtype.ext (Subtype.ext hy1)
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hL : IsSimpleGroup (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) := by
    obtain ⟨-, h⟩ := hqs
    exact h
  have hLn := CFSG.AGLEmbedding.LeviBlock.exists_noncomm_centerQuotient hqs
  have hpL : p ∣ Nat.card (↥(S j₀) ⧸ Subgroup.center ↥(S j₀)) := by
    have h1 : orderOf (⟨u₀, hu₀S⟩ : ↥(S j₀)) = p := by rw [Subgroup.orderOf_mk, hu₀ord]
    have h2 : p ∣ Nat.card ↥(S j₀) := by
      rw [← h1]
      exact orderOf_dvd_natCard _
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(S j₀))] at h2
    exact ((Nat.Prime.dvd_mul hp).1 h2).resolve_right hcz
  exact leviSurj_of_levi_comm hp hp2 hzP hz β hβ (Subgroup.pi Set.univ S) hS hNperf hab hpR
    ρ hρsurj hρk hL hLn hpL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
