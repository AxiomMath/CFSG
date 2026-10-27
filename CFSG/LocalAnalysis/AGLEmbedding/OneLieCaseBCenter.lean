module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCaseBRank
import CFSG.LocalAnalysis.AGLEmbedding.LinTwoCompetitorAux2
import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitorReduced
import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

structure D1OneLieCompetitorData (p : ℕ) (P : Sylow p G) (M H R : Subgroup G)
    (Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p))
    (K : Subgroup (H ⧸ primeComplementCore (G := H) p)) (R₁ : Subgroup G) (P' : Sylow p G)
    (H₁ S : Subgroup G) : Prop where
  data : D1OneLieData p P M H R Rbar K
  le_R : R₁ ≤ R
  liftX_le : d1LiftX p H R K ≤ R₁
  inf_eq_bot : R₁ ⊓ d1PlusCore p H K = ⊥
  escape : D1Escape p P' M H₁ S
  nclIn_le : nclIn H (d1LiftX p H R K) ≤ H₁
  le_S : R₁ ≤ S
  card_le : Nat.card S ≤ p * Nat.card R₁
  pRank_le : Open.pRank p S ≤ Open.pRank p R₁

theorem exists_mem_inf_centralizer_orderOf_eq {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [Fact p.Prime] {P A : Subgroup Y} (hP : IsPGroup p P) (hAP : A ≤ P)
    (hPA : P ≤ Subgroup.normalizer (A : Set Y)) (hA : A ≠ ⊥) :
    ∃ b ∈ A, b ∈ Subgroup.centralizer (P : Set Y) ∧ orderOf b = p := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hn : (A.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr hPA
  have hne : A.subgroupOf P ≠ ⊥ := by
    intro hbot
    apply hA
    rw [eq_bot_iff]
    intro a ha
    have : (⟨a, hAP ha⟩ : P) ∈ A.subgroupOf P := Subgroup.mem_subgroupOf.mpr ha
    rw [hbot, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  obtain ⟨⟨⟨w, hwP⟩, hwA, hwZ⟩, hw1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  set B := A ⊓ Subgroup.centralizer (P : Set Y) with hB
  have hwB : w ∈ B := by
    refine ⟨Subgroup.mem_subgroupOf.mp hwA, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hwZ ⟨r, hr⟩))
  have hB1 : B ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.mem_bot] at hwB
    exact hw1 (Subtype.ext (Subtype.ext hwB))
  obtain ⟨b, ⟨hbA, hbC⟩, hbp, -⟩ :=
    exists_mem_centralizer_orderOf_eq ((hP.to_le hAP).to_le inf_le_left) hB1
  exact ⟨b, hbA, hbC, hbp⟩

namespace D1OneLieCompetitorData

variable {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)} {R₁ : Subgroup G} {P' : Sylow p G}
  {H₁ S : Subgroup G}

theorem exists_eq_mk_of_mem_center (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    {a : H₁ ⧸ primeComplementCore (G := H₁) p}
    (haS : a ∈ (S.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)))
    (haC : a ∈ Subgroup.centralizer (((S.subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) : Subgroup _) : Set _))
    (hap : orderOf a = p) :
    ∃ s : H₁, (s : G) ∈ R₁ ∧ QuotientGroup.mk' (primeComplementCore (G := H₁) p) s = a ∧
      s ≠ 1 := by
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  have hbot : S ⊓ GLBPrimeCore p H₁ = ⊥ :=
    inf_eq_bot_of_isPGroup hp hc.escape.isPGroup (glbPrimeCore_coprime p H₁)
  have key : ∀ t : H₁, (t : G) ∈ S → π₁ t = 1 → t = 1 := by
    intro t htS ht
    have hmem : (t : G) ∈ S ⊓ GLBPrimeCore p H₁ :=
      ⟨htS, (mk'_primeComplementCore_eq_one_iff p t).mp ht⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact Subtype.ext hmem
  obtain ⟨s, hsS, rfl⟩ := haS
  have hsS' : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hsS
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hap
    exact hp.one_lt.ne hap
  have hsp : s ^ p = 1 :=
    key _ (S.pow_mem hsS' p) (by
      rw [map_pow]
      exact orderOf_dvd_iff_pow_eq_one.mp (by rw [hap]))
  have hso : orderOf (s : G) = p := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hsp hs1
  have hsC : (s : G) ∈ Subgroup.centralizer (S : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t htS
    have htH : t ∈ H₁ := hc.escape.le_H htS
    have hcomm := Subgroup.mem_centralizer_iff.mp haC (π₁ ⟨t, htH⟩)
      (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htS))
    have h1 : π₁ ((⟨t, htH⟩ : H₁) * s * (⟨t, htH⟩ : H₁)⁻¹ * s⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
      group
    have h2 := key _ (S.mul_mem (S.mul_mem (S.mul_mem htS hsS') (S.inv_mem htS))
      (S.inv_mem hsS')) h1
    have h3 : (t : G) * s * t⁻¹ * (s : G)⁻¹ = 1 := congrArg Subtype.val h2
    calc (t : G) * s = (t : G) * s * t⁻¹ * (s : G)⁻¹ * (s * t) := by group
      _ = s * t := by rw [h3, one_mul]
  exact ⟨s, mem_of_mem_centralizer_of_pRank_le hp hc.le_S hc.pRank_le hsS' hsC hso, rfl, hs1⟩

theorem eq_one_of_mk_mem_centralizer (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    {s : H₁} (hsR : (s : G) ∈ R₁)
    (hsC : QuotientGroup.mk' (primeComplementCore (G := H₁) p) s ∈ Subgroup.centralizer
      ((((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
        (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) : Subgroup _) : Set _)) :
    s = 1 := by
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  refine Subtype.ext (hc.data.eq_one_of_commutator_le hc.le_R hc.inf_eq_bot hc.nclIn_le hsR
    fun j hj => ?_)
  have hjH : j ∈ H₁ := hc.nclIn_le hj
  have hcomm := Subgroup.mem_centralizer_iff.mp hsC (π₁ ⟨j, hjH⟩)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hj))
  have h1 : π₁ (s * ⟨j, hjH⟩ * s⁻¹ * (⟨j, hjH⟩ : H₁)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
    group
  exact (mk'_primeComplementCore_eq_one_iff p _).mp h1

theorem false_of_mem_center (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    {a : H₁ ⧸ primeComplementCore (G := H₁) p}
    (haS : a ∈ (S.subgroupOf H₁).map (QuotientGroup.mk' (primeComplementCore (G := H₁) p)))
    (haC : a ∈ Subgroup.centralizer (((S.subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) : Subgroup _) : Set _))
    (hap : orderOf a = p)
    (haJ : a ∈ Subgroup.centralizer ((((nclIn H (d1LiftX p H R K)).subgroupOf H₁).map
      (QuotientGroup.mk' (primeComplementCore (G := H₁) p)) : Subgroup _) : Set _)) :
    False := by
  obtain ⟨s, hsR, rfl, hs1⟩ := hc.exists_eq_mk_of_mem_center haS haC hap
  exact hs1 (hc.eq_one_of_mk_mem_centralizer hsR haJ)

theorem eq_bot_of_normal_of_isPGroup (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S)
    (U : Subgroup (H₁ ⧸ primeComplementCore (G := H₁) p)) (hU : U.Normal)
    (hUp : IsPGroup p U) : U = ⊥ := by
  have hd := hc.data
  have hp := hc.escape.prime
  have : Fact p.Prime := ⟨hp⟩
  set π₁ := QuotientGroup.mk' (primeComplementCore (G := H₁) p) with hπ₁
  set X := d1LiftX p H R K with hXdef
  set J := nclIn H X with hJdef
  set Jt := (J.subgroupOf H₁).map π₁ with hJt
  set Xt := (X.subgroupOf H₁).map π₁ with hXt
  set St := (S.subgroupOf H₁).map π₁ with hSt
  by_contra hU1
  obtain ⟨Rb₁, hRb₁, -⟩ := hc.escape.reducedNongeneration
  have hRbS : (Rb₁ : Subgroup _) = St := hRb₁
  have hUS : U ≤ St := hRbS ▸ hUp.le_sylow_of_normal Rb₁
  have hStp : IsPGroup p St := hRbS ▸ Rb₁.isPGroup'
  obtain ⟨b, hbU, hbC, hbp⟩ := exists_mem_inf_centralizer_orderOf_eq hStp hUS
    (fun x _ => Subgroup.mem_normalizer_iff.mpr fun y => ⟨fun hy => hU.conj_mem y hy x,
      fun hy => by simpa [mul_assoc] using hU.conj_mem _ hy x⁻¹⟩) hU1
  obtain ⟨s, hsR, hsb, -⟩ := hc.exists_eq_mk_of_mem_center (hUS hbU) hbC hbp
  have hXp : IsPGroup p X := hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)
  have hXtp : IsPGroup p Xt := hXp.comap_subtype.map _
  have hncl : nclIn Jt Xt = Jt :=
    nclIn_map_eq π₁ (le_nclIn (d1LiftX_le_H p H R K)) hc.nclIn_le hd.nclIn_nclIn
  obtain ⟨φ, hφs, hφk, -⟩ :=
    exists_competitorHom_apply_of_map_eq (hd.map_nclIn_eq le_rfl hd.d1LiftX_ne_bot) hc.nclIn_le
  obtain ⟨hKs, hKnab⟩ := hd.isSimpleGroup
  have hUJ : ∀ y ∈ U, y ∈ Jt → y = 1 := by
    have : (U.subgroupOf Jt).Normal := Subgroup.normal_subgroupOf
    rcases eq_top_or_le_ker_of_nclIn_eq hKs hXtp hncl φ hφs hφk (U.subgroupOf Jt) with
      htop | hker
    · exfalso
      have hJp : IsPGroup p Jt := by
        intro j
        obtain ⟨k, hk⟩ := hUp ⟨j, Subgroup.mem_subgroupOf.mp (htop ▸ Subgroup.mem_top j)⟩
        exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
      have hKp : IsPGroup p K := hJp.of_surjective φ hφs
      have : Group.IsNilpotent K := hKp.isNilpotent
      obtain ⟨x, y, hxy⟩ := hKnab
      exact hxy ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance x y)
    · intro y hyU hyJ
      have hbot : U.subgroupOf Jt ⊓ φ.ker = ⊥ :=
        inf_eq_bot_of_isPGroup hp (hUp.comap_subtype (K := Jt)) hφk
      have hmem : (⟨y, hyJ⟩ : Jt) ∈ U.subgroupOf Jt ⊓ φ.ker :=
        ⟨Subgroup.mem_subgroupOf.mpr hyU, hker (Subgroup.mem_subgroupOf.mpr hyU)⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact congrArg Subtype.val hmem
  have hsH : (s : G) ∈ H := hd.cfg.ext.le_H (hc.le_R hsR)
  have hbJ : b ∈ Subgroup.centralizer (Jt : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨j, hj, rfl⟩
    have hjJ : (j : G) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have hsj : (s : G) * j * (s : G)⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_nclIn H X hsH) j).mp hjJ
    have hcJ : b * π₁ j * b⁻¹ * (π₁ j)⁻¹ ∈ Jt := by
      rw [← hsb]
      refine Jt.mul_mem ?_ (Jt.inv_mem (Subgroup.mem_map_of_mem _ hj))
      have : π₁ s * π₁ j * (π₁ s)⁻¹ = π₁ (s * j * s⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [this]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (by simpa using hsj))
    have hcU : b * π₁ j * b⁻¹ * (π₁ j)⁻¹ ∈ U := by
      have e : b * π₁ j * b⁻¹ * (π₁ j)⁻¹ = b * (π₁ j * b⁻¹ * (π₁ j)⁻¹) := by group
      rw [e]
      exact U.mul_mem hbU (hU.conj_mem _ (U.inv_mem hbU) _)
    have h1 := hUJ _ hcU hcJ
    calc π₁ j * b = (b * π₁ j * b⁻¹ * (π₁ j)⁻¹)⁻¹ * (b * π₁ j) := by group
      _ = b * π₁ j := by rw [h1, inv_one, one_mul]
  exact hc.false_of_mem_center (hUS hbU) hbC hbp hbJ

theorem not_hasPrimeConstraint (hc : D1OneLieCompetitorData p P M H R Rbar K R₁ P' H₁ S) :
    ¬ HasPrimeConstraint (G := H₁) p := by
  rintro ⟨U, hUn, hUp, hC⟩
  have hd := hc.data
  have hU := hc.eq_bot_of_normal_of_isPGroup U hUn hUp
  have hXH : d1LiftX p H R K ≤ H₁ := (le_nclIn (d1LiftX_le_H p H R K)).trans hc.nclIn_le
  apply map_mk_ne_bot_of_isPGroup hc.escape.prime hXH
    (hd.cfg.ext.isPGroup.to_le (d1LiftX_le p H R K)) hd.d1LiftX_ne_bot
  rw [eq_bot_iff]
  intro x _
  have hx : x ∈ Subgroup.centralizer (U : Set (H₁ ⧸ primeComplementCore (G := H₁) p)) := by
    rw [hU]
    exact Subgroup.mem_centralizer_iff.mpr fun y hy => by
      rw [Subgroup.mem_bot.mp hy, one_mul, mul_one]
  have := hC hx
  rwa [hU] at this

end D1OneLieCompetitorData

end CFSG.AGLEmbedding
