module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLeviBlocks

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi

open Subgroup CFSG.Open
open scoped commutatorElement

theorem blocksGen_isSolvable_quotient {M : Type} [Group M] {R Sg N : Subgroup M}
    (hRSg : ∀ x ∈ R, ∀ y ∈ R, x * y * x⁻¹ * y⁻¹ ∈ Sg)
    (hSgN : ∀ u ∈ Sg, ∀ v ∈ Sg, u * v * u⁻¹ * v⁻¹ ∈ N)
    [hNn : (N.subgroupOf R).Normal] : Group.IsSolvable (↥R ⧸ N.subgroupOf R) := by
  have h1 : ⁅(⊤ : Subgroup (↥R ⧸ N.subgroupOf R)), ⊤⁆ ≤
      (Sg.subgroupOf R).map (QuotientGroup.mk' (N.subgroupOf R)) := by
    rw [Subgroup.commutator_le]
    intro a _ b _
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective b
    have hmem : ⁅r, s⁆ ∈ Sg.subgroupOf R := by
      rw [Subgroup.mem_subgroupOf, commutatorElement_def]
      simpa using hRSg r r.2 s s.2
    have key : ⁅(QuotientGroup.mk r : ↥R ⧸ N.subgroupOf R),
        (QuotientGroup.mk s : ↥R ⧸ N.subgroupOf R)⁆ =
        QuotientGroup.mk' (N.subgroupOf R) ⁅r, s⁆ :=
      (map_commutatorElement (QuotientGroup.mk' (N.subgroupOf R)) r s).symm
    rw [key]
    exact Subgroup.mem_map_of_mem _ hmem
  have h2 : ⁅(Sg.subgroupOf R).map (QuotientGroup.mk' (N.subgroupOf R)),
      (Sg.subgroupOf R).map (QuotientGroup.mk' (N.subgroupOf R))⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hb
    have hmem : ⁅u, v⁆ ∈ N.subgroupOf R := by
      rw [Subgroup.mem_subgroupOf, commutatorElement_def]
      simpa using hSgN u (Subgroup.mem_subgroupOf.1 hu) v (Subgroup.mem_subgroupOf.1 hv)
    rw [Subgroup.mem_bot, ← map_commutatorElement (QuotientGroup.mk' (N.subgroupOf R)) u v]
    exact (QuotientGroup.eq_one_iff _).2 hmem
  have h3 : derivedSeries (↥R ⧸ N.subgroupOf R) 2 ≤ ⊥ :=
    (Subgroup.commutator_mono h1 h1).trans h2
  exact ⟨⟨2, le_bot_iff.1 h3⟩⟩

theorem leviSurj_of_blocks_gen {X : Type} [Group X] [Finite X] {P : Subgroup X} {z : X} {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hzP : z ∈ P) (hz : orderOf z = p)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ j, Group (G j)] [∀ j, Finite (G j)]
    (β : ↥P →* ∀ j, G j) (hβ : IsPGroup 2 β.ker)
    (S : ∀ j, Subgroup (G j)) (hS : Subgroup.pi Set.univ S ≤ β.range)
    (hcomm : ⁅β.range, β.range⁆ ≤ Subgroup.pi Set.univ S)
    (hperf : ∀ j, ⁅S j, S j⁆ = S j ∨
      ((∀ a ∈ S j, ∀ b ∈ S j, a * b = b * a) ∧ ∀ x ∈ S j, x ^ p = 1 → x = 1))
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
  have hperf₀ : ⁅S j₀, S j₀⁆ = S j₀ := by
    rcases hperf j₀ with h | ⟨-, hx⟩
    · exact h
    · exfalso
      have h1 : u₀ = 1 := hx u₀ hu₀S (by rw [← hu₀ord]; exact pow_orderOf_eq_one u₀)
      rw [h1, orderOf_one] at hu₀ord
      exact hp.one_lt.ne hu₀ord
  classical
  obtain ⟨T, hT⟩ : ∃ T : ∀ j, Subgroup (G j), ∀ j,
      T j = if ⁅S j, S j⁆ = S j then S j else ⊥ :=
    ⟨fun j => if ⁅S j, S j⁆ = S j then S j else ⊥, fun j => rfl⟩
  have hTperf : ∀ j, ⁅S j, S j⁆ = S j → T j = S j := fun j h => by rw [hT j, if_pos h]
  have hTbot : ∀ j, ¬ ⁅S j, S j⁆ = S j → T j = ⊥ := fun j h => by rw [hT j, if_neg h]
  have hTS : ∀ j, T j ≤ S j := by
    intro j
    by_cases h : ⁅S j, S j⁆ = S j
    · exact (hTperf j h).le
    · rw [hTbot j h]
      exact bot_le
  have hTeq : T j₀ = S j₀ := hTperf j₀ hperf₀
  have hTcomm : ∀ j, ⁅T j, T j⁆ = T j := by
    intro j
    by_cases h : ⁅S j, S j⁆ = S j
    · rw [hTperf j h]
      exact h
    · rw [hTbot j h, Subgroup.commutator_bot_left]
  have hNS : Subgroup.pi Set.univ T ≤ Subgroup.pi Set.univ S := by
    intro x hx
    rw [Subgroup.mem_pi] at hx ⊢
    intro j hj
    exact hTS j (hx j hj)
  have hNr : Subgroup.pi Set.univ T ≤ β.range := fun x hx => hS (hNS hx)
  have hNperf : ⁅Subgroup.pi Set.univ T, Subgroup.pi Set.univ T⁆ = Subgroup.pi Set.univ T := by
    simp only [Subgroup.commutator_pi_pi_of_finite, hTcomm]
  have hRcomm : ∀ x ∈ β.range, ∀ y ∈ β.range,
      x * y * x⁻¹ * y⁻¹ ∈ Subgroup.pi Set.univ S := by
    intro x hx y hy
    have h := hcomm (Subgroup.commutator_mem_commutator hx hy)
    rwa [commutatorElement_def] at h
  have hSnorm : ∀ x ∈ β.range, ∀ n ∈ Subgroup.pi Set.univ S,
      x * n * x⁻¹ ∈ Subgroup.pi Set.univ S := by
    intro x hx n hn
    have h2 := hRcomm x hx n (hS hn)
    have h3 : x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
    rw [h3]
    exact (Subgroup.pi Set.univ S).mul_mem h2 hn
  have hconjS : ∀ x ∈ β.range, ∀ j, ∀ s ∈ S j, x j * s * (x j)⁻¹ ∈ S j := by
    intro x hx j s hs
    have h1 := hSnorm x hx (Pi.mulSingle j s) (leviBlock_mulSingle_mem_pi S hs)
    have h2 := (Subgroup.mem_pi _).1 h1 j (Set.mem_univ j)
    simpa only [Pi.mul_apply, Pi.inv_apply, Pi.mulSingle_eq_same] using h2
  have hNconj : ∀ x ∈ β.range, ∀ n ∈ Subgroup.pi Set.univ T,
      x * n * x⁻¹ ∈ Subgroup.pi Set.univ T := by
    intro x hx n hn
    rw [Subgroup.mem_pi]
    intro j _
    have hnj : n j ∈ T j := (Subgroup.mem_pi _).1 hn j (Set.mem_univ j)
    simp only [Pi.mul_apply, Pi.inv_apply]
    by_cases h : ⁅S j, S j⁆ = S j
    · rw [hTperf j h] at hnj ⊢
      exact hconjS x hx j (n j) hnj
    · rw [hTbot j h] at hnj ⊢
      rw [Subgroup.mem_bot] at hnj
      rw [hnj, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
  have hSab : ∀ u ∈ Subgroup.pi Set.univ S, ∀ v ∈ Subgroup.pi Set.univ S,
      u * v * u⁻¹ * v⁻¹ ∈ Subgroup.pi Set.univ T := by
    intro u hu v hv
    rw [Subgroup.mem_pi]
    intro j _
    have huj : u j ∈ S j := (Subgroup.mem_pi _).1 hu j (Set.mem_univ j)
    have hvj : v j ∈ S j := (Subgroup.mem_pi _).1 hv j (Set.mem_univ j)
    simp only [Pi.mul_apply, Pi.inv_apply]
    by_cases h : ⁅S j, S j⁆ = S j
    · rw [hTperf j h]
      have h1 : ⁅u j, v j⁆ ∈ ⁅S j, S j⁆ := Subgroup.commutator_mem_commutator huj hvj
      rw [h, commutatorElement_def] at h1
      exact h1
    · rw [hTbot j h, Subgroup.mem_bot]
      obtain ⟨hcj, -⟩ := (hperf j).resolve_left h
      rw [hcj (u j) huj (v j) hvj]
      group
  have hpN : ∀ x ∈ β.range, x ^ p = 1 → x ∈ Subgroup.pi Set.univ T := by
    intro x hx hxp
    have hxS := hpR x hx hxp
    rw [Subgroup.mem_pi]
    intro j _
    have hxj : x j ∈ S j := (Subgroup.mem_pi _).1 hxS j (Set.mem_univ j)
    by_cases h : ⁅S j, S j⁆ = S j
    · rw [hTperf j h]
      exact hxj
    · have hxjp : x j ^ p = 1 := by simpa using congrFun hxp j
      have h1 := ((hperf j).resolve_left h).2 (x j) hxj hxjp
      rw [hTbot j h, h1]
      exact Subgroup.one_mem _
  haveI hNnorm : ((Subgroup.pi Set.univ T).subgroupOf β.range).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hNconj _ g.2 _ hn⟩
  have hsolv : Group.IsSolvable (↥β.range ⧸ (Subgroup.pi Set.univ T).subgroupOf β.range) :=
    blocksGen_isSolvable_quotient hRcomm hSab
  let ev : ↥(Subgroup.pi Set.univ T) →* ↥(S j₀) :=
    MonoidHom.mk' (fun x => ⟨x.1 j₀, hTS j₀ ((Subgroup.mem_pi _).1 x.2 j₀ (Set.mem_univ j₀))⟩)
      (fun x y => Subtype.ext rfl)
  let ρ : ↥(Subgroup.pi Set.univ T) →* ↥(S j₀) ⧸ Subgroup.center ↥(S j₀) :=
    (QuotientGroup.mk' (Subgroup.center ↥(S j₀))).comp ev
  have hρsurj : Function.Surjective ρ := by
    intro q
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    have hs : (s : G j₀) ∈ T j₀ := by
      rw [hTeq]
      exact s.2
    have hmem : (Pi.mulSingle j₀ (s : G j₀) : ∀ j, G j) ∈ Subgroup.pi Set.univ T :=
      leviBlock_mulSingle_mem_pi T hs
    refine ⟨⟨Pi.mulSingle j₀ (s : G j₀), hmem⟩, ?_⟩
    have hev : ev ⟨Pi.mulSingle j₀ (s : G j₀), hmem⟩ = s :=
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
    have hy0 : (⟨(x.1 : ∀ j, G j) j₀, (Subgroup.mem_pi _).1 (hNS x.1.2) j₀ (Set.mem_univ j₀)⟩ :
        ↥(S j₀)) ∈ Subgroup.center ↥(S j₀) :=
      (QuotientGroup.eq_one_iff (ev x.1)).1 hρx
    have hy1 : (x.1 : ∀ j, G j) = 1 :=
      leviBlock_eq_one_of_coord hp S hcz huniq (hNS x.1.2) hypow hy0
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
  exact leviSurj_of_levi hp hp2 hzP hz β hβ (Subgroup.pi Set.univ T) hNr hNperf hsolv hpN
    ρ hρsurj hρk hL hLn hpL

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.FongLevi
