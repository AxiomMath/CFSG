module

public import CFSG.LocalAnalysis.AGL81TheoremCD.CStarGenRank
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenFiveA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CNineTenG1
public import CFSG.LocalAnalysis.RankThreeUC.AGL81CSixThreeOneBasic
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.Defs
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourStmt

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeUC.AGL81C
open CFSG.LocalAnalysis.RankThreeUC.AGL81C.S631
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

@[expose] def IsL3TwoPow (n : ℕ) (X : Type) [Group X] : Prop :=
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPSLType 3 (GaloisField 2 n) X

@[expose] def TwelveFive (M H : Subgroup G) (d : ℕ) : Prop :=
  jSub M H = oPPrimeHull d M ∧
    ∃ L₁ L₂ L₃ : Subgroup G,
      L₁ ∈ weakBlockSet M H ∧ L₂ ∈ weakBlockSet M H ∧ L₃ ∈ weakBlockSet M H ∧
        jSub M H = L₁ ⊔ L₂ ⊔ L₃ ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₁ ⧸ pCore 2 ↥L₁)) ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₂ ⧸ pCore 2 ↥L₂)) ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₃ ⧸ pCore 2 ↥L₃))

omit [Finite G] in
theorem TwelveFive.part_one {M H : Subgroup G} {d : ℕ} (h : TwelveFive M H d) :
    jSub M H = oPPrimeHull d M :=
  h.1

theorem oPPrimeHull_le_jSub_of_sylow {M H : Subgroup G} {d : ℕ}
    (hSylow : ∀ D : Subgroup G, IsSylowOf d D M → D ≤ jSub M H) :
    oPPrimeHull d M ≤ jSub M H := by
  classical
  rw [oPPrimeHull, Subgroup.closure_le]
  rintro x ⟨hxM, k, hk⟩
  rcases k with _ | k
  · rw [pow_zero] at hk
    rw [orderOf_eq_one_iff.mp hk]
    exact (jSub M H).one_mem
  · have hZ : IsPGroup d ((Subgroup.zpowers x).subgroupOf M) := by
      rw [isPGroup_iff_card_dvd_pow]
      refine ⟨k + 1, ?_⟩
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (Subgroup.zpowers_le.mpr hxM)).toEquiv, Nat.card_zpowers, hk]
    obtain ⟨P, hP⟩ := hZ.exists_le_sylow
    refine hSylow ((P : Subgroup ↥M).map M.subtype) ⟨P, rfl⟩ ?_
    have hxP : (⟨x, hxM⟩ : ↥M) ∈ (P : Subgroup ↥M) :=
      hP (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers x))
    exact Subgroup.mem_map_of_mem (f := M.subtype) hxP

omit [Finite G] in
theorem jSub_le_oPPrimeHull_of_forall {M H : Subgroup G} {d : ℕ}
    (hLle : ∀ L : Subgroup G, L ∈ weakBlockSet M H → L ≤ oPPrimeHull d M) :
    jSub M H ≤ oPPrimeHull d M :=
  sSup_le hLle

theorem oPPrimeHull_top_eq_of_isSimpleGroup {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {d : ℕ} (hd : d.Prime) (hdvd : d ∣ Nat.card X) :
    oPPrimeHull d (⊤ : Subgroup X) = ⊤ := by
  haveI : Fact d.Prime := ⟨hd⟩
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := X) d hdvd
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hxord
    exact hd.ne_one hxord.symm
  have hN : Subgroup.normalClosure (Subgroup.zpowers x : Set X) = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.normalClosure (Subgroup.zpowers x : Set X)) with h | h
    · exfalso
      exact hx1 (Subgroup.mem_bot.mp (h ▸ Subgroup.le_normalClosure (Subgroup.mem_zpowers x)))
    · exact h
  have hgen : (Subgroup.zpowers x : Subgroup X) ≤ oPPrimeHull d (⊤ : Subgroup X) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure ⟨trivial, 1, by simpa using hxord⟩
  haveI : (oPPrimeHull d (⊤ : Subgroup X)).Normal := oPPrimeHull_top_normal d
  have hle : Subgroup.normalClosure (Subgroup.zpowers x : Set X) ≤
      oPPrimeHull d (⊤ : Subgroup X) :=
    Subgroup.normalClosure_le_normal (fun y hy => hgen hy)
  rw [hN] at hle
  rw [eq_top_iff]
  exact hle

theorem oPPrimeHull_top_eq_of_perfect_of_simple_quotient {H : Type} [Group H] [Finite H]
    [Group.IsPerfect H] {Z : Subgroup H} [Z.Normal] {d : ℕ} (hd : d.Prime)
    (hZ2 : IsPGroup 2 Z) (hsimple : IsSimpleGroup (H ⧸ Z)) (hdvd : d ∣ Nat.card (H ⧸ Z)) :
    oPPrimeHull d (⊤ : Subgroup H) = ⊤ := by
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := oPPrimeHull d (⊤ : Subgroup H) with hNdef
  haveI hNn : N.Normal := oPPrimeHull_top_normal d
  have hgen : oPPrimeHull d (⊤ : Subgroup (H ⧸ Z)) = ⊤ :=
    oPPrimeHull_top_eq_of_isSimpleGroup hd hdvd
  have hmap : N.map (QuotientGroup.mk' Z) = ⊤ := by
    have h := map_oPPrimeHull (p := d) (f := QuotientGroup.mk' Z) (⊤ : Subgroup H)
    rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z), hgen] at h
    exact h
  have hNZ : N ⊔ Z = ⊤ := by
    have h := Subgroup.comap_map_eq (f := QuotientGroup.mk' Z) N
    rw [hmap, Subgroup.comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hQ2 : IsPGroup 2 (H ⧸ N) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N q
    have hh : h ∈ N ⊔ Z := by rw [hNZ]; exact Subgroup.mem_top h
    obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hh
    obtain ⟨k, hk⟩ := hZ2 ⟨z, hz⟩
    have hzk : z ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    refine ⟨k, ?_⟩
    change (QuotientGroup.mk' N n * QuotientGroup.mk' N z) ^ 2 ^ k = 1
    rw [show QuotientGroup.mk' N n = 1 from (QuotientGroup.eq_one_iff n).mpr hn, one_mul,
      ← map_pow, hzk, map_one]
  have hsub : Subsingleton (H ⧸ N) := by
    by_contra hnt
    haveI : Nontrivial (H ⧸ N) := not_subsingleton_iff_nontrivial.mp hnt
    haveI : Group.IsNilpotent (H ⧸ N) := hQ2.isNilpotent
    exact Group.IsPerfect.not_isSolvable (H ⧸ N) inferInstance
  exact QuotientGroup.subsingleton_iff.mp hsub

theorem IsL3TwoPow.isSimpleGroup {n : ℕ} {X : Type} [Group X] (h : IsL3TwoPow n X) :
    IsSimpleGroup X := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (PSL(3, GaloisField 2 n)) :=
    (CFSG.LinearGroups.linear_projective_simple (K := GaloisField 2 n) (n := 3)
      (by norm_num) (Or.inl (by norm_num))).2.1
  exact e.isSimpleGroup

theorem le_oPPrimeHull_of_isL3TwoPow {L M : Subgroup G} {d n : ℕ} (hd : d.Prime)
    (hd3 : 3 < d) (hLM : L ≤ M) (hperf : ⁅L, L⁆ = L) (hdvdL : d ∣ Nat.card L)
    (hL3 : IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    L ≤ oPPrimeHull d M := by
  haveI : Fact d.Prime := ⟨hd⟩
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have hZ2 : IsPGroup 2 (pCore 2 ↥L) := CFSG.pCore_isPGroup
  have hd2 : d ≠ 2 := by omega
  have hdZ : ¬ d ∣ Nat.card (pCore 2 ↥L) := by
    obtain ⟨k, hk⟩ := isPGroup_iff_card_dvd_pow.mp hZ2
    intro hdvd
    have hdvd2 : d ∣ 2 ^ k := hdvd.trans hk
    have hddvd := hd.dvd_of_dvd_pow hdvd2
    exact hd2 ((Nat.prime_dvd_prime_iff_eq hd Nat.prime_two).mp hddvd)
  have hdvdq : d ∣ Nat.card (↥L ⧸ pCore 2 ↥L) := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 ↥L)
    rw [hcard] at hdvdL
    rcases hd.dvd_mul.mp hdvdL with h | h
    · exact h
    · exact absurd h hdZ
  have hsimple : IsSimpleGroup (↥L ⧸ pCore 2 ↥L) := hL3.isSimpleGroup
  have hgen : oPPrimeHull d (⊤ : Subgroup ↥L) = ⊤ :=
    oPPrimeHull_top_eq_of_perfect_of_simple_quotient hd hZ2 hsimple hdvdq
  have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hLgen : oPPrimeHull d L = L := by
    rw [← map_subtype_oPPrimeHull_top L d, hgen, htop]
  rw [← hLgen]
  unfold oPPrimeHull
  exact Subgroup.closure_mono (fun x hx => ⟨hLM hx.1, hx.2⟩)

theorem jSub_le_oPPrimeHull_of_blocks {M H : Subgroup G} {d : ℕ} (hd : d.Prime) (hd3 : 3 < d)
    (hdvdL : ∀ L : Subgroup G, L ∈ weakBlockSet M H → d ∣ Nat.card L)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    jSub M H ≤ oPPrimeHull d M := by
  refine jSub_le_oPPrimeHull_of_forall fun L hL => ?_
  obtain ⟨n, -, hL3n⟩ := hL3 L hL
  exact le_oPPrimeHull_of_isL3TwoPow hd hd3 hL.le hL.toIsTwoPrimeComponent.perfect
    (hdvdL L hL) hL3n

theorem pRank_three_le_three_of_twelveFour {M H : Subgroup G} (hC : CStarGen G)
    (hM : rankThreeIsMaxTwoLocal M) (hσ : (sigmaSet G M).Nonempty) (h124 : TwelveFour M H) :
    CFSG.Open.pRank 3 M ≤ 3 := by
  obtain ⟨d, hd⟩ := hσ
  exact CStarGen.pRank_le_three_of_not_mem_sigmaSet hC hM Nat.prime_three (by norm_num)
    (h124 d hd).2.2

theorem pRank_three_le_three_of_twelveCtx {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}
    (h : TwelveCtx G M p Q H) (h124 : TwelveFour M H) : CFSG.Open.pRank 3 M ≤ 3 :=
  pRank_three_le_three_of_twelveFour h.cstar h.maxLocal h.sigma_nonempty h124

omit [Finite G] in
theorem sSup_three (a b c : Subgroup G) :
    sSup ({a, b, c} : Set (Subgroup G)) = a ⊔ b ⊔ c := by
  refine le_antisymm (sSup_le ?_) ?_
  · intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · refine sup_le (sup_le (le_sSup (by simp)) (le_sSup (by simp))) (le_sSup (by simp))

omit [Finite G] in
theorem twelveFive_part_two_of_ncard_three {M H : Subgroup G}
    (hcard : (weakBlockSet M H).ncard = 3)
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    ∃ L₁ L₂ L₃ : Subgroup G,
      L₁ ∈ weakBlockSet M H ∧ L₂ ∈ weakBlockSet M H ∧ L₃ ∈ weakBlockSet M H ∧
        jSub M H = L₁ ⊔ L₂ ⊔ L₃ ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₁ ⧸ pCore 2 ↥L₁)) ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₂ ⧸ pCore 2 ↥L₂)) ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₃ ⧸ pCore 2 ↥L₃)) := by
  obtain ⟨L₁, L₂, L₃, -, -, -, hset⟩ := Set.ncard_eq_three.mp hcard
  have hL₁ : L₁ ∈ weakBlockSet M H := by rw [hset]; simp
  have hL₂ : L₂ ∈ weakBlockSet M H := by rw [hset]; simp
  have hL₃ : L₃ ∈ weakBlockSet M H := by rw [hset]; simp
  refine ⟨L₁, L₂, L₃, hL₁, hL₂, hL₃, ?_, hL3 L₁ hL₁, hL3 L₂ hL₂, hL3 L₃ hL₃⟩
  rw [jSub, hset, sSup_three]

theorem ncard_weakBlockSet_eq_three_of_rank_count {M H : Subgroup G} {d : ℕ}
    (hm3M : CFSG.Open.pRank 3 M ≤ 3)
    (hr3 : (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 (jSub M H))
    (hdr : CFSG.Open.pRank d (jSub M H) ≤ (weakBlockSet M H).ncard)
    (hd3 : 3 ≤ CFSG.Open.pRank d (jSub M H)) :
    (weakBlockSet M H).ncard = 3 := by
  have h3 : (weakBlockSet M H).ncard ≤ 3 :=
    hr3.trans ((CFSG.SectionRank.pRank_mono (p := 3) (by norm_num) (jSub_le M H)).trans hm3M)
  omega

theorem twelveFive_part_two_of_rank_count {M H : Subgroup G} {d : ℕ}
    (hm3M : CFSG.Open.pRank 3 M ≤ 3)
    (hr3 : (weakBlockSet M H).ncard ≤ CFSG.Open.pRank 3 (jSub M H))
    (hdr : CFSG.Open.pRank d (jSub M H) ≤ (weakBlockSet M H).ncard)
    (hd3 : 3 ≤ CFSG.Open.pRank d (jSub M H))
    (hL3 : ∀ L : Subgroup G, L ∈ weakBlockSet M H →
      ∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L ⧸ pCore 2 ↥L)) :
    ∃ L₁ L₂ L₃ : Subgroup G,
      L₁ ∈ weakBlockSet M H ∧ L₂ ∈ weakBlockSet M H ∧ L₃ ∈ weakBlockSet M H ∧
        jSub M H = L₁ ⊔ L₂ ⊔ L₃ ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₁ ⧸ pCore 2 ↥L₁)) ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₂ ⧸ pCore 2 ↥L₂)) ∧
        (∃ n : ℕ, Odd n ∧ IsL3TwoPow n (↥L₃ ⧸ pCore 2 ↥L₃)) :=
  twelveFive_part_two_of_ncard_three
    (ncard_weakBlockSet_eq_three_of_rank_count hm3M hr3 hdr hd3) hL3

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
