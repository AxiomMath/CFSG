module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallResidues
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.AThreePLiftAux
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallConfig
import CFSG.LocalAnalysis.AGLEmbedding.AThreePLift

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

theorem exists_rank_seven_of_le {X : Type*} [Group X] [Finite X] {n : ℕ} (hn : 21 ≤ n)
    {ι : alternatingGroup (Fin n) →* X} (hι : Function.Injective ι) :
    ∃ Y : Subgroup X, IsPGroup 3 Y ∧ Group.rank Y = 7 := by
  obtain ⟨φ, hφ⟩ := exists_injective_pi_alternatingGroup (k := 7) (m := 3) (n := n) (by omega)
  exact ⟨_, isPGroup_range_rank Nat.prime_three (φ := ι.comp φ) (hι.comp hφ)
    (fun a b => funext fun i => alternatingGroup_three_comm (a i) (b i))
    (fun a => funext fun i => alternatingGroup_three_pow (a i))
    (by rw [Nat.card_fun, natCard_alternatingGroup_three, Nat.card_eq_fintype_card,
      Fintype.card_fin])⟩

section Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfig.three_mem_betaFour (hT : ThompsonNormalAbelianGen)
    (hcfg : D1ComponentConfig p P M H R Rbar)
    {Y : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hY : IsPGroup 3 Y)
    (hr : 7 ≤ Group.rank Y) : 3 ∈ GLBBetaFour G := by
  have h4 : 3 < Open.pRank 3 H :=
    lt_pRank_of_quotient hT (by norm_num) _ hY (Subgroup.map_subtype_le _) (by omega)
  refine ⟨Nat.prime_three, by norm_num,
    PreuniquenessRankFour.Helpers.prime_dvd_card_of_positive_rank 3 Nat.prime_three H
      (by omega), ?_⟩
  have h4' : 4 ≤ Open.pRank 3 H := h4
  exact h4'.trans (le_csSup (PreuniquenessRankFour.Helpers.twoLocalRank_bddAbove 3
    Nat.prime_three) ⟨H, hcfg.ext.maxTwoLocal_H.1, rfl⟩)

theorem D1ComponentConfig.three_le_pRank_inf (hT : ThompsonNormalAbelianGen)
    (hcfg : D1ComponentConfig p P M H R Rbar)
    {Y : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hY : IsPGroup 3 Y)
    (hYX₀ : Y ≤ d1X0 p M H) (hr : 4 ≤ Group.rank Y) : 3 ≤ Open.pRank 3 (H ⊓ M) := by
  set N := primeComplementCore (G := H) p with hNdef
  have hOM : N ≤ (H ⊓ M).subgroupOf H := by
    rw [hNdef, ← glbPrimeCore_subgroupOf]
    exact glbPrimeCore_subgroupOf_le_inf hcfg.ext.primeCore_le
  have hle : (Y.comap (QuotientGroup.mk' N)).map H.subtype ≤ H ⊓ M := by
    calc _ ≤ ((((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' N)).comap
          (QuotientGroup.mk' N)).map H.subtype := Subgroup.map_mono (Subgroup.comap_mono hYX₀)
      _ = H ⊓ M := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOM,
          Subgroup.map_subgroupOf_eq_of_le inf_le_left]
  exact lt_pRank_of_quotient hT (by norm_num) N hY hle (r := 2) (lt_of_lt_of_le (by norm_num) hr)

theorem D1OneSmallData.exists_rank_four_le_of_altTwoP (hd : D1OneSmallData p P M H R Rbar K)
    (hA : IsAltTwoP p K) (hp7 : 7 ≤ p) :
    ∃ Y : Subgroup (H ⧸ primeComplementCore (G := H) p), Y ≤ d1X0 p M H ∧ IsPGroup 3 Y ∧
      Group.rank Y = 4 := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := hA
  obtain ⟨zb, hzbR, hzbK, hzbp, hzbc⟩ := hd.z
  obtain ⟨hN, -⟩ := hd.cfg.red.rankOne_principle hd.comp hd.noncyclic hzbR hzbK hzbp hzbc
  obtain ⟨T₁, hT₁, -⟩ := hd.exists_sylow
  obtain ⟨Ψ₁, hΨ₁⟩ := exists_injective_pi_alternatingGroup (k := 2) (m := p) (n := 2 * p) le_rfl
  obtain ⟨c, hc⟩ :=
    exists_prime_orderOf_dvd_card' p (prime_dvd_natCard_alternatingGroup hp hd.cfg.red.ne_two)
  set C : Subgroup (alternatingGroup (Fin p)) := Subgroup.zpowers c
  have hCcard : Nat.card C = p := by rw [Nat.card_zpowers, hc]
  have hCcomm : ∀ x y : C, x * y = y * x := (Subgroup.zpowers_isMulCommutative c).is_comm.comm
  have hCexp : ∀ x : C, x ^ p = 1 := fun x => by
    have h := pow_card_eq_one' (x := x)
    rwa [hCcard] at h
  set j : (Fin 2 → C) →* (Fin 2 → alternatingGroup (Fin p)) := C.subtype.compLeft (Fin 2)
    with hjdef
  have hj : Function.Injective j := fun x y hxy => funext fun i => Subtype.ext (congrFun hxy i)
  have hjs : ∀ k : Fin 2, j (Pi.mulSingle k ⟨c, Subgroup.mem_zpowers c⟩) = Pi.mulSingle k c :=
    fun k => funext fun i => by
      by_cases hi : i = k
      · subst hi
        simp [hjdef]
      · simp [hjdef, Pi.mulSingle_eq_of_ne hi]
  set φ₀ : (Fin 2 → alternatingGroup (Fin p)) →* K := e.symm.toMonoidHom.comp Ψ₁
  have hφ₀ : Function.Injective φ₀ := e.symm.injective.comp hΨ₁
  obtain ⟨S, hS⟩ := (isPGroup_range_rank hp (φ := φ₀.comp j) (hφ₀.comp hj)
    (fun x y => funext fun i => hCcomm (x i) (y i)) (fun x => funext fun i => hCexp (x i))
    (k := 2) (by rw [Nat.card_fun, hCcard, Nat.card_eq_fintype_card, Fintype.card_fin])).1
    |>.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K S T₁
  set Ψ : (Fin 2 → alternatingGroup (Fin p)) →* (H ⧸ primeComplementCore (G := H) p) :=
    K.subtype.comp ((MulAut.conj g).toMonoidHom.comp φ₀)
  have hΨ : Function.Injective Ψ :=
    K.subtype_injective.comp ((MulAut.conj g).injective.comp hφ₀)
  have hΨK : ∀ x, Ψ x ∈ K := fun x => ((MulAut.conj g).toMonoidHom.comp φ₀ x).2
  have hΨT : ∀ k : Fin 2, Ψ (Pi.mulSingle k c) ∈
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓ K := by
    intro k
    rw [← hT₁, ← hjs]
    refine ⟨_, ?_, rfl⟩
    have hx : (φ₀.comp j) (Pi.mulSingle k ⟨c, Subgroup.mem_zpowers c⟩) ∈ (S : Subgroup K) :=
      hS ⟨_, rfl⟩
    rw [← hg, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ (MulAut.conj g) _ hx
  have hblock : ∀ k k' : Fin 2, k ≠ k' → ∀ u, Ψ (Pi.mulSingle k u) ∈ d1X0 p M H := by
    intro k k' hkk' u
    have hy1 : Ψ (Pi.mulSingle k' c) ≠ 1 := by
      intro h1
      have h2 : Pi.mulSingle k' c = (1 : Fin 2 → alternatingGroup (Fin p)) :=
        hΨ (by rw [map_one]; exact h1)
      have hc1 : c = 1 := by simpa using congrFun h2 k'
      rw [hc1, orderOf_one] at hc
      exact hp.one_lt.ne hc
    have hU : Subgroup.zpowers (Ψ (Pi.mulSingle k' c)) ≠ ⊥ := by
      rwa [Ne, Subgroup.zpowers_eq_bot]
    have hcomm : Ψ (Pi.mulSingle k' c) * Ψ (Pi.mulSingle k u) =
        Ψ (Pi.mulSingle k u) * Ψ (Pi.mulSingle k' c) := by
      rw [← map_mul, ← map_mul]
      exact congrArg Ψ (Pi.mulSingle_commute (f := fun _ : Fin 2 => alternatingGroup (Fin p))
        hkk' u c).symm.eq
    have hle : Subgroup.zpowers (Ψ (Pi.mulSingle k' c)) ≤
        Subgroup.centralizer ({Ψ (Pi.mulSingle k u)} : Set _) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    refine hN _ (Subgroup.zpowers_le.mpr (hΨT k')) hU ⟨hΨK _, ?_⟩
    exact Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun q hq =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hq))
  have hall : ∀ x, Ψ x ∈ d1X0 p M H := by
    intro x
    have hx : x = Pi.mulSingle 0 (x 0) * Pi.mulSingle 1 (x 1) := by
      funext i
      fin_cases i <;> simp
    rw [hx, map_mul]
    exact (d1X0 p M H).mul_mem (hblock 0 1 (by decide) _) (hblock 1 0 (by decide) _)
  obtain ⟨ιU, hιU⟩ := exists_injective_pi_alternatingGroup (k := 2) (m := 3) (n := p) (by omega)
  set χ := Ψ.comp (ιU.compLeft (Fin 2))
  have hχ : Function.Injective χ :=
    hΨ.comp fun x y hxy => funext fun i => hιU (congrFun hxy i)
  obtain ⟨hχp, hχr⟩ := isPGroup_range_rank Nat.prime_three hχ
    (fun a b => funext fun i => funext fun l => alternatingGroup_three_comm (a i l) (b i l))
    (fun a => funext fun i => funext fun l => alternatingGroup_three_pow (a i l)) (k := 4)
    (by rw [Nat.card_fun, Nat.card_fun, natCard_alternatingGroup_three]; simp)
  refine ⟨χ.range, ?_, hχp, hχr⟩
  rintro _ ⟨v, rfl⟩
  exact hall _

end Config

theorem stmtSmallGuest_of (hT : ThompsonNormalAbelianGen) (hK6 : KFactFi22GuestRank) :
    StmtSmallGuest := by
  intro G _ _ p P M H R Rbar K hd hcase
  obtain ⟨hq, hrank, h3p⟩ : 3 ∈ GLBBetaFour G ∧ 3 ≤ Open.pRank 3 (H ⊓ M) ∧ 3 < p := by
    rcases hcase with ⟨hA, hp7, h11⟩ | ⟨rfl, hF, hq⟩
    · obtain ⟨Y, hYX₀, hY, hr⟩ := hd.exists_rank_four_le_of_altTwoP hA hp7
      refine ⟨?_, hd.cfg.three_le_pRank_inf hT hY hYX₀ hr.ge, by omega⟩
      rcases h11 with h11 | hq
      · obtain ⟨e⟩ := hA
        obtain ⟨Y₇, hY₇, hr₇⟩ := exists_rank_seven_of_le (n := 2 * p) (by omega)
          (ι := K.subtype.comp e.symm.toMonoidHom) (K.subtype_injective.comp e.symm.injective)
        exact hd.cfg.three_mem_betaFour hT hY₇ hr₇.ge
      · exact hq
    · obtain ⟨T₁, -, -, -, -, -, -, hΓX₀⟩ := hd.exists_sylow
      obtain ⟨E, hEΓ, hE, hEcard⟩ := hK6 K hF T₁
      have hY := elementary_abelian_map 3 hE K.subtype
      have hYcard : Nat.card (E.map K.subtype) = 3 ^ 4 := by
        rw [Subgroup.card_map_of_injective K.subtype_injective, hEcard]
      have hr : Group.rank (E.map K.subtype) = 4 :=
        rank_eq_of_elementary Nat.prime_three hY.1.is_comm.comm
          (fun a => Subtype.ext (by simpa using hY.2 a a.2)) hYcard
      exact ⟨hq, hd.cfg.three_le_pRank_inf hT (IsPGroup.of_card hYcard)
        ((Subgroup.map_mono hEΓ).trans hΓX₀) hr.ge, by norm_num⟩
  exact false_of_guestPrime hd.cfg.glob.pre hq (hd.cfg.ind 3 hq h3p) hd.cfg.loc.maxLocal
    hd.cfg.ext.maxTwoLocal_H hd.cfg.ext.not_le hrank

end CFSG.AGLEmbedding
