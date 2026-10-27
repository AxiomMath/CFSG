module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceJ3
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3CoverA6
import CFSG.LocalAnalysis.SectionRank.ClassicalEven.Basic

public section

namespace CFSG.AGLEmbedding

open KFactProofs.J3Cover CFSG.Open CFSG.PreuniquenessRankFour.Helpers

theorem j3Cover_gen
    {K J : Type} [Group K] [Finite K] [Group J] [Finite J] (π : K →* J)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center K) (hperf : Group.IsPerfect K)
    (he : Nonempty (J ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)) {z : K} (hz : z ∈ π.ker)
    (hzo : orderOf z = 3) :
    ∃ U B : Subgroup K, IsMulCommutative U ∧ (∀ a ∈ U, a ^ 3 = 1) ∧ Nat.card U = 9 ∧ z ∈ U ∧
      B ≤ Subgroup.centralizer (U : Set K) ∧ (∃ t ∈ B, orderOf t = 3 ∧ t ∉ U) ∧
      ∀ Y : Subgroup K, B ≤ Y → (∃ S : Sylow 3 K, (S : Subgroup K) ≤ Y) → Y = ⊤ := by
  obtain ⟨⟨x, d₁, d₂, g, u, hd⟩, hover⟩ := j3CoverFacts J he
  obtain ⟨U, B, hUc, hU3, hUcard, hzU, hBU, ⟨t, htB, hto, htU⟩, hDB⟩ :=
    exists_cover_subgroups π hπ hker hd hz hzo
  refine ⟨U, B, hUc, hU3, hUcard, hzU, hBU, ⟨t, htB, hto, htU⟩, ?_⟩
  rintro Y hBY ⟨S, hSY⟩
  have hDY : Subgroup.closure ({d₁, d₂} : Set J) ≤ Y.map π :=
    hDB.trans (Subgroup.map_mono hBY)
  set T := S.mapSurjective hπ with hT
  have hTY : (T : Subgroup J) ≤ Y.map π := by
    rw [hT, Sylow.coe_mapSurjective]
    exact Subgroup.map_mono hSY
  rcases hover T _ hTY with hN | htop
  · exfalso
    have hsolv := isSolvable_normalizer_of_facts T.isPGroup' (kFactJ3Sylow _ he T)
    exact not_isSolvable_of_perfect (commutator_self_eq hd.rel₁ hd.rel₂ hd.rel₃ hd.rel₄)
      ⟨u, hd.u_mem, hd.u_ne_one⟩ (hDY.trans hN) hsolv
  · exact eq_top_of_map_eq_top hker hperf.commutator_eq_top htop

theorem map_centralizer_le {K L : Type*} [Group K] [Group L] (c : K →* L) (V : Subgroup K) :
    (Subgroup.centralizer (V : Set K)).map c ≤
      Subgroup.centralizer ((V.map c : Subgroup L) : Set L) := by
  rintro _ ⟨y, hy, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨v, hv, rfl⟩
  rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy v hv]

theorem j3CoverWeakGenThree :
    J3CoverWeakGenThree := by
  intro K _ _ π hπ hker hperf hZne hZp hZcyc T
  have hp : Nat.Prime 3 := Nat.prime_three
  have : Fact (Nat.Prime 3) := ⟨hp⟩
  have : Finite (Blueprint.NativeSporadic.Carrier .J3) := Finite.of_surjective π hπ
  obtain ⟨b⟩ : Nonempty (Blueprint.NativeSporadic.Carrier .J3 ≃*
      (TauCeti.CFSGIndex.sporadic .J3).Group) := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  obtain ⟨z, hzZ, hzo⟩ : ∃ z ∈ Subgroup.center K, orderOf z = 3 := by
    obtain ⟨n, hn⟩ := hZp.exists_card_eq
    have hn0 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at hn
      exact hZne hn
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) 3
      (by rw [hn]; exact dvd_pow_self 3 hn0)
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩
  obtain ⟨U, B, hUc, hU3, hUcard, hzU, hBU, ⟨t, htB, hto, htU⟩, hgen⟩ :=
    j3Cover_gen π hπ hker.le hperf ⟨b⟩ (hker.ge hzZ) hzo
  have hUel : IsElemAbelian 3 U := ⟨hUc, hU3⟩
  have ht3 : t ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one t
    rwa [hto] at h1
  have htc : ∀ a ∈ U, t * a = a * t := fun a ha =>
    (Subgroup.mem_centralizer_iff.mp (hBU htB) a ha).symm
  set E : Subgroup K := U ⊔ Subgroup.zpowers t with hE
  have hzE : z ∈ E := Subgroup.mem_sup_left hzU
  have htE : t ∈ E := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hz1 : z ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hzo; norm_num at hzo
  obtain ⟨u, huU, huz⟩ : ∃ u ∈ U, u ∉ Subgroup.zpowers z := by
    by_contra h
    push Not at h
    have h1 := Subgroup.card_le_of_le (h : U ≤ Subgroup.zpowers z)
    rw [hUcard, Nat.card_zpowers, hzo] at h1
    omega
  have huE : u ∈ E := Subgroup.mem_sup_left huU
  have hcU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hUc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEp : IsPGroup 3 E := by
    have hUp : IsPGroup 3 U := IsPGroup.of_card (n := 2) (by rw [hUcard]; norm_num)
    have htp : IsPGroup 3 (Subgroup.zpowers t) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers, hto]
      exact ⟨1, by norm_num⟩
    exact hUp.to_sup_of_normal_left' htp (Subgroup.zpowers_le.mpr
      (Subgroup.mem_normalizer_fintype fun a ha => by
        rw [htc a ha, mul_inv_cancel_right]
        exact ha))
  have hE3 : 3 ≤ Open.pRank 3 E := by
    have h3top : 3 ≤ Open.pRank 3 (⊤ : Subgroup E) := by
      refine CFSG.SectionRank.ClassicalEven.three_le_pRank_of_gens (x := ⟨z, hzE⟩)
        (y := ⟨u, huE⟩) (z := ⟨t, htE⟩) (Subtype.ext (by simpa using hU3 z hzU))
        (Subtype.ext (by simpa using hU3 u huU)) (Subtype.ext (by simpa using ht3))
        (Subtype.ext (hcU z hzU u huU)) (Subtype.ext (htc z hzU).symm)
        (Subtype.ext (htc u huU).symm) (fun h1 => hz1 (by simpa using congrArg Subtype.val h1))
        (fun n hn => huz ?_) (fun n m hnm => htU ?_)
      · have : z ^ n = u := by simpa using congrArg Subtype.val hn
        rw [← this]
        exact Subgroup.npow_mem_zpowers z n
      · have : z ^ n * u ^ m = t := by simpa using congrArg Subtype.val hnm
        rw [← this]
        exact U.mul_mem (U.pow_mem hzU n) (U.pow_mem huU m)
    have h1 := pRank_map_of_injective 3 hp E.subtype E.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [h1]
    exact h3top
  obtain ⟨S, hES⟩ := hEp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S T
  set c : K →* K := (MulAut.conj g).toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g).injective
  have hTS : (T : Subgroup K) = (S : Subgroup K).map c := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  set W := GLBWeakCore 3 (T : Subgroup K) with hW
  have hBW : B.map c ≤ W := by
    have hUT : U.map c ≤ (T : Subgroup K) :=
      hTS ▸ Subgroup.map_mono ((le_sup_left : U ≤ E).trans hES)
    have h2 : 2 ≤ Open.pRank 3 (U.map c) := by
      rw [pRank_map_of_injective 3 hp c hcinj U]
      exact le_csSup (pRank_bddAbove 3 hp U) ⟨U, le_rfl, hUel, by rw [hUcard]; norm_num⟩
    have hEsub : E.map c ≤ U.map c ⊔
        ((T : Subgroup K) ⊓ Subgroup.centralizer ((U.map c : Subgroup K) : Set K)) := by
      rw [hE, Subgroup.map_sup]
      refine sup_le_sup_left (le_inf ?_ ?_) _
      · rw [hTS]
        exact Subgroup.map_mono (Subgroup.zpowers_le.mpr (hES htE))
      · refine le_trans (Subgroup.map_mono ?_) (map_centralizer_le c U)
        rw [Subgroup.zpowers_le]
        exact hBU htB
    have h3 : 3 ≤ Open.pRank 3 (U.map c ⊔
        ((T : Subgroup K) ⊓ Subgroup.centralizer ((U.map c : Subgroup K) : Set K))) :=
      (hE3.trans (pRank_map_of_injective 3 hp c hcinj E).ge).trans (pRank_mono 3 hp hEsub)
    exact ((Subgroup.map_mono hBU).trans (map_centralizer_le c U)).trans
      ((Subgroup.centralizer_le_normalizer _).trans (normalizer_le_weakCore 3 hUT h2 h3))
  have hTW : (T : Subgroup K) ≤ W := by
    have hET : E.map c ≤ (T : Subgroup K) := hTS ▸ Subgroup.map_mono hES
    have h3T : 3 ≤ Open.pRank 3 (T : Subgroup K) :=
      (hE3.trans (pRank_map_of_injective 3 hp c hcinj E).ge).trans (pRank_mono 3 hp hET)
    exact Subgroup.le_normalizer.trans (normalizer_le_weakCore 3 le_rfl
      (le_trans (by norm_num : (2 : ℕ) ≤ 3) h3T)
      (h3T.trans (pRank_mono 3 hp le_sup_left)))
  have hY : W.comap c = ⊤ := by
    refine hgen _ (fun x hx => hBW ⟨x, hx, rfl⟩) ⟨S, fun x hx => ?_⟩
    have hcx : c x ∈ (T : Subgroup K) := by
      rw [hTS]
      exact ⟨x, hx, rfl⟩
    exact hTW hcx
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, rfl⟩ := (MulAut.conj g).surjective x
  have hy : y ∈ W.comap c := hY ▸ Subgroup.mem_top y
  exact hy

end CFSG.AGLEmbedding
