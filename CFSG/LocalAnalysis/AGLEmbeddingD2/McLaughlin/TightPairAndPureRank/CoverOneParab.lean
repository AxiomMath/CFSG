module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneShort
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverA2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.TitsRankTwoCount2
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOneNodeLie
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneCore

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open CFSG.HallHigman CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime
  CFSG.AGLEmbedding.LieOut CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.AGLEmbeddingD2.McLaughlin.Lie
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

section Index

variable {K Y : Type} [Group K] [Finite K] [Group Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem iSup_torus_le_centralizer (h : BorelQuotient D n H π M) {i : Fin D.rank}
    (h6 : Nat.card (rankOne D.rootGroup i) = 6) :
    ∀ t ∈ (⨆ k, H k : Subgroup K), ∀ g ∈ rankOne D.rootGroup i, t * g = g * t := by
  have : (⨆ k, H k : Subgroup K) ≤ Subgroup.centralizer (rankOne D.rootGroup i : Set K) :=
    iSup_le fun k t ht => by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact (torus_centralizes_rankOne_of_card_six h h6 ht g hg).symm
  intro t ht g hg
  exact (Subgroup.mem_centralizer_iff.1 (this ht) g hg).symm

theorem card_borel_sup_rankOne_of_torus (h : BorelQuotient D n H π M) (i : Fin D.rank)
    (h6 : Nat.card (rankOne D.rootGroup i) = 6)
    (hnc : ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a) :
    Nat.card (borel D H ⊔ rankOne D.rootGroup i : Subgroup K) = 3 * Nat.card (borel D H) := by
  haveI := cartan_borel_weylN_normal h.ct h.extras
  set L := rankOne D.rootGroup i with hL
  set U := ⨆ j ∈ ({i} : Set (Fin D.rank))ᶜ, radical D j with hU
  set T₀ : Subgroup K := ⨆ k, H k with hT₀
  have hU2 : IsPGroup 2 (posUnipotent D) := isPGroup_iSup_pos h.extras h.pGroup
  have hUB : U ≤ borel D H :=
    (iSup₂_le fun j _ => radical_le_posUnipotent j).trans posUnipotent_le_borel
  have hLN : L ≤ Subgroup.normalizer (U : Set K) :=
    le_normalizer_sup_radicals ({i} : Set (Fin D.rank)) fun j hj =>
      rankOne_le_normalizer_radical h.extras fun e => hj e.symm
  have hBN : borel D H ≤ Subgroup.normalizer (U : Set K) :=
    le_normalizer_sup_radicals ({i} : Set (Fin D.rank)) fun j _ =>
      borel_le_normalizer_radical h.ct h.extras j
  have hU2' : IsPGroup 2 U := sup_radicals_isPGroup hU2 ({i} : Set (Fin D.rank))
  have hUL : U ⊓ L = ⊥ :=
    eq_bot_of_isPGroup_two_of_card_six h6 hnc inf_le_right
      ((le_inf hLN Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf)
      (hU2'.to_le inf_le_left)
  have hTc : ∀ t ∈ T₀, ∀ g ∈ L, t * g = g * t := iSup_torus_le_centralizer h h6
  have hLT : L ≤ Subgroup.normalizer (T₀ : Set K) := le_normalizer_of_commute (A := T₀) (B := L) hTc
  have hTB : T₀ ≤ borel D H := iSup_le_borel
  have hTU : T₀ ≤ Subgroup.normalizer (U : Set K) := hTB.trans hBN
  set Ũ : Subgroup K := T₀ ⊔ U with hŨ
  have hŨB : Ũ ≤ borel D H := sup_le hTB hUB
  have hLŨ : L ≤ Subgroup.normalizer (Ũ : Set K) := le_normalizer_sup hLT hLN
  have hα : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hBsup : borel D H ≤ (T₀ ⊔ (borel D H ⊓ L)) ⊔ U :=
    borel_le_sup_radicals_of_torus_le ({i} : Set (Fin D.rank)) (T₀ ⊔ (borel D H ⊓ L))
      (fun k => (le_iSup H k).trans le_sup_left)
      (fun γ hγ hpos hh => (le_inf (rootGroup_le_borel hγ hpos)
        (h.ct.le_rankOne i γ hγ fun k hk => hh k hk)).trans le_sup_right)
  have hB : borel D H ≤ (borel D H ⊓ L) ⊔ Ũ := by
    refine hBsup.trans (sup_le (sup_le ?_ le_sup_left) ?_)
    · exact le_sup_of_le_right le_sup_left
    · exact le_sup_of_le_right le_sup_right
  have hŨL : Ũ ⊓ L = ⊥ := by
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨hwŨ, hwL⟩ := hw
    have hset : (↑(T₀ ⊔ U) : Set K) = (T₀ : Set K) * (U : Set K) :=
      Subgroup.coe_mul_of_left_le_normalizer_right T₀ U hTU
    obtain ⟨t, ht, r, hr, rfl⟩ := hset ▸ hwŨ
    refine Subgroup.mem_bot.2 (Lie.eq_one_of_central_of_card_six h6 hnc hwL fun l hl => ?_)
    have hcom : l * (t * r) * l⁻¹ * (t * r)⁻¹ ∈ U := by
      have hr' : l * r * l⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hLN hl) r).1 hr
      have hlt : l * t * l⁻¹ = t := by
        rw [← hTc t ht l hl]; group
      have e : l * (t * r) * l⁻¹ * (t * r)⁻¹ = t * ((l * r * l⁻¹) * r⁻¹) * t⁻¹ := by
        calc l * (t * r) * l⁻¹ * (t * r)⁻¹ = (l * t * l⁻¹) * (l * r * l⁻¹) * r⁻¹ * t⁻¹ := by group
          _ = _ := by rw [hlt]; group
      rw [e]
      have : (l * r * l⁻¹) * r⁻¹ ∈ U := U.mul_mem hr' (U.inv_mem hr)
      exact (Subgroup.mem_normalizer_iff.1 (hTU ht) _).1 this
    have hcomL : l * (t * r) * l⁻¹ * (t * r)⁻¹ ∈ L :=
      L.mul_mem (L.mul_mem (L.mul_mem hl hwL) (L.inv_mem hl)) (L.inv_mem hwL)
    have h1 : l * (t * r) * l⁻¹ * (t * r)⁻¹ ∈ U ⊓ L := ⟨hcom, hcomL⟩
    rw [hUL, Subgroup.mem_bot] at h1
    have h2 : l * (t * r) * l⁻¹ = t * r := mul_inv_eq_one.1 h1
    calc t * r * l = (l * (t * r) * l⁻¹) * l := by rw [h2]
      _ = l * (t * r) := by group
  have hnB : n i ∉ borel D H := by
    have hBNp := isBNPair_borel_weylN h.ct h.extras
    set s : WeylGroup (borel D H) (weylN n H) :=
      ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) with hs
    have hsS : s ∈ simpleRefl D n H := ⟨i, rfl⟩
    have hDB : Disjoint ((borel D H : Subgroup K) : Set K) (dc (borel D H) (weylN n H) s) := by
      rw [← dc_one (B := borel D H) (N := weylN n H)]
      exact hBNp.pairwise_disjoint_dc (hBNp.ne_one hsS).symm
    have hnD : n i ∈ dc (borel D H) (weylN n H) s :=
      mem_dc_mk_iff.2 ⟨1, one_mem _, 1, one_mem _, by simp⟩
    intro hnb
    exact Set.disjoint_left.1 hDB hnb hnD
  have hXBL : D.rootGroup (Pi.single i 1) ≤ borel D H ⊓ L :=
    le_inf (rootGroup_le_borel hα (ht_single_pos i)) le_sup_left
  have hBL2 : Nat.card (borel D H ⊓ L : Subgroup K) = 2 := by
    obtain ⟨k, hk⟩ := (h.pGroup _ hα).exists_card_eq
    have hk0 : k ≠ 0 := fun h0 => h.extras.ne_bot _ hα
      (Subgroup.eq_bot_of_card_eq _ (by rw [hk, h0, pow_zero]))
    have h2 : 2 ∣ Nat.card (borel D H ⊓ L : Subgroup K) := by
      have := Subgroup.card_dvd_of_le hXBL
      rw [hk] at this
      exact (dvd_pow_self 2 hk0).trans this
    have hd : Nat.card (borel D H ⊓ L : Subgroup K) ∣ 6 :=
      h6 ▸ Subgroup.card_dvd_of_le inf_le_right
    have hpos : 0 < Nat.card (borel D H ⊓ L : Subgroup K) := Nat.card_pos
    have hle : Nat.card (borel D H ⊓ L : Subgroup K) ≤ 6 := Nat.le_of_dvd (by norm_num) hd
    have hcases : Nat.card (borel D H ⊓ L : Subgroup K) = 2 ∨
        Nat.card (borel D H ⊓ L : Subgroup K) = 6 := by
      generalize Nat.card (borel D H ⊓ L : Subgroup K) = d at h2 hd hle hpos
      interval_cases d <;> simp_all
    rcases hcases with h2' | h6'
    · exact h2'
    · exfalso
      have heq : borel D H ⊓ L = L :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h6, h6'])
      exact hnB ((inf_eq_right.1 heq) (h.ct.n_mem i))
  have hP : borel D H ⊔ L = Ũ ⊔ L :=
    le_antisymm (sup_le (hB.trans (sup_le (inf_le_right.trans le_sup_right) le_sup_left))
      le_sup_right) (sup_le (hŨB.trans le_sup_left) le_sup_right)
  have hcL := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer hLŨ
  rw [hŨL, Subgroup.card_bot, mul_one, h6] at hcL
  have hBeq : borel D H = Ũ ⊔ (borel D H ⊓ L) :=
    le_antisymm (hB.trans (le_of_eq (sup_comm _ _))) (sup_le hŨB inf_le_left)
  have hcB := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    ((inf_le_right : borel D H ⊓ L ≤ L).trans hLŨ)
  have hUBL : Ũ ⊓ (borel D H ⊓ L) = ⊥ :=
    eq_bot_iff.2 ((inf_le_inf_left Ũ inf_le_right).trans hŨL.le)
  rw [hUBL, Subgroup.card_bot, mul_one, hBL2, ← hBeq] at hcB
  rw [hP, hcL, hcB]
  ring


theorem not_nine_dvd_card_rankOne_sup_torus (h : BorelQuotient D n H π M) {i j : Fin D.rank}
    (h6i : Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (h6j : Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a)
    (hij : i ≠ j) (hAij : D.cartan i j = -1) (hAji : D.cartan j i = -1)
    (hVT : (rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) ⊓ (⨆ k, H k) = ⊥) :
    ¬ 9 ∣ Nat.card ↥(rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) := by
  haveI := cartan_borel_weylN_normal h.ct h.extras
  have hBN := isBNPair_borel_weylN h.ct h.extras
  set T₀ : Subgroup K := ⨆ k, H k with hT₀
  set U := posUnipotent D with hU
  have hU2 : IsPGroup 2 U := isPGroup_iSup_pos h.extras h.pGroup
  have hUB : U ≤ borel D H := posUnipotent_le_borel
  have hTB : T₀ ≤ borel D H := iSup_le_borel
  have hTN : T₀ ≤ Subgroup.normalizer (U : Set K) :=
    hTB.trans (borel_le_normalizer_posUnipotent h.ct)
  have hbor : borel D H = T₀ ⊔ U := rfl
  have hBcard : Nat.card (borel D H) = Nat.card U * Nat.card T₀ := by
    have h1 := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
      (A := U) (B := T₀) hTN
    have hinf : U ⊓ T₀ = ⊥ := by rw [inf_comm]; exact h.extras.torus_inf_posPart
    rw [hinf, Subgroup.card_bot, mul_one] at h1
    rw [hbor, sup_comm, h1]
  have hUN : ∀ g ∈ weylN n H, ∀ b ∈ borel D H, ∃ u ∈ U, ∃ b' ∈ borel D H,
      b * g = u * g * b' := by
    intro g hg b hb
    have hset : (↑(T₀ ⊔ U) : Set K) = (T₀ : Set K) * (U : Set K) :=
      Subgroup.coe_mul_of_left_le_normalizer_right T₀ U hTN
    obtain ⟨t, ht, u, hu, rfl⟩ : b ∈ (T₀ : Set K) * (U : Set K) := hset ▸ hb
    have hgT : g⁻¹ * t * g ∈ T₀ := inv_conj_mem_iSup_of_mem_weylN h.ct hg ht
    refine ⟨t * u * t⁻¹, (Subgroup.mem_normalizer_iff.1 (hTN ht) u).1 hu, g⁻¹ * t * g,
      hTB hgT, ?_⟩
    group
  set a : WeylGroup (borel D H) (weylN n H) :=
    ((⟨n i, n_mem_weylN i⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) with ha
  set b : WeylGroup (borel D H) (weylN n H) :=
    ((⟨n j, n_mem_weylN j⟩ : weylN n H) : WeylGroup (borel D H) (weylN n H)) with hb
  have haS : a ∈ simpleRefl D n H := ⟨i, rfl⟩
  have hbS : b ∈ simpleRefl D n H := ⟨j, rfl⟩
  have hPa : Nat.card (parabolic (borel D H) (weylN n H) {a}) = 3 * Nat.card (borel D H) := by
    rw [ha, parabolic_single_eq h.ct h.extras i]
    exact card_borel_sup_rankOne_of_torus h i h6i.1 h6i.2
  have hPb : Nat.card (parabolic (borel D H) (weylN n H) {b}) = 3 * Nat.card (borel D H) := by
    rw [hb, parabolic_single_eq h.ct h.extras j]
    exact card_borel_sup_rankOne_of_torus h j h6j.1 h6j.2
  have hab : a ≠ b := simpleRefl_ne h.ct h.extras hij hAji
  have hbraid : a * b * a = b * a * b := by
    have h1 := braid_three h.ct hij hAij hAji
    have h2 : (⟨n i, n_mem_weylN i⟩ * ⟨n j, n_mem_weylN j⟩ * ⟨n i, n_mem_weylN i⟩ : weylN n H) =
        ⟨n j, n_mem_weylN j⟩ * ⟨n i, n_mem_weylN i⟩ * ⟨n j, n_mem_weylN j⟩ := Subtype.ext h1
    rw [ha, hb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, h2]
  obtain ⟨o, ho⟩ := card_parabolic_pair_eq hBN hU2 hUB hUN haS hbS hab hbraid hPa hPb
  have hJS : ({a, b} : Set (WeylGroup (borel D H) (weylN n H))) ⊆ simpleRefl D n H := by
    intro x hx
    rcases hx with rfl | rfl
    · exact haS
    · exact hbS
  have hsingle : ∀ (c : WeylGroup (borel D H) (weylN n H)), c ∈ ({a, b} : Set _) →
      parabolic (borel D H) (weylN n H) {c} ≤ parabolic (borel D H) (weylN n H) {a, b} :=
    fun c hc => (hBN.parabolic_le_iff (Set.singleton_subset_iff.2 (hJS hc)) hJS).2
      (Set.singleton_subset_iff.2 hc)
  set V : Subgroup K := rankOne D.rootGroup i ⊔ rankOne D.rootGroup j with hV
  have hVP : V ≤ parabolic (borel D H) (weylN n H) {a, b} :=
    sup_le ((rankOne_le_parabolic h.ct h.extras i).trans (hsingle a (by simp)))
      ((rankOne_le_parabolic h.ct h.extras j).trans (hsingle b (by simp)))
  have hTP : T₀ ≤ parabolic (borel D H) (weylN n H) {a, b} := hTB.trans (hBN.le_parabolic hJS)
  have hVc : ∀ t ∈ T₀, ∀ g ∈ V, t * g = g * t := by
    have hle : V ≤ Subgroup.centralizer (T₀ : Set K) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        exact fun t ht => iSup_torus_le_centralizer h h6i.1 t ht g hg
      · rw [Subgroup.mem_centralizer_iff]
        exact fun t ht => iSup_torus_le_centralizer h h6j.1 t ht g hg
    exact fun t ht g hg => Subgroup.mem_centralizer_iff.1 (hle hg) t ht
  have hVN : V ≤ Subgroup.normalizer (T₀ : Set K) :=
    le_normalizer_of_commute (A := T₀) (B := V) hVc
  have hcTV := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (A := T₀) (B := V) hVN
  have hTV : T₀ ⊓ V = ⊥ := by rw [inf_comm]; exact hVT
  rw [hTV, Subgroup.card_bot, mul_one] at hcTV
  have hdvd : Nat.card T₀ * Nat.card V ∣ Nat.card (parabolic (borel D H) (weylN n H) {a, b}) := by
    rw [← hcTV]
    exact Subgroup.card_dvd_of_le (sup_le hTP hVP)
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hTpos : 0 < Nat.card T₀ := Nat.card_pos
  rw [ho, hBcard, hm] at hdvd
  have hVd : Nat.card V ∣ 3 * 2 ^ m * (3 + 2 ^ o) := by
    have e : 3 * (2 ^ m * Nat.card T₀) * (3 + 2 ^ o) =
        Nat.card T₀ * (3 * 2 ^ m * (3 + 2 ^ o)) := by ring
    rw [e] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hTpos hdvd
  intro h9
  have h9' : 9 ∣ 3 * 2 ^ m * (3 + 2 ^ o) := h9.trans hVd
  have h3 : 3 ∣ 2 ^ m * (3 + 2 ^ o) := by
    have : 3 * 3 ∣ 3 * (2 ^ m * (3 + 2 ^ o)) := by
      have e1 : 3 * 2 ^ m * (3 + 2 ^ o) = 3 * (2 ^ m * (3 + 2 ^ o)) := by ring
      rw [← e1]; simpa using h9'
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h4 | h4
  · have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
    omega
  · have h5 : 3 ∣ 2 ^ o := (Nat.dvd_add_right (dvd_refl 3)).1 h4
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h5
    omega


theorem not_isPSolvable_map_A2_torus [Finite Y] (h : BorelQuotient D n H π M) {i j : Fin D.rank}
    (h6i : Nat.card (rankOne D.rootGroup i) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup i, ∃ b ∈ rankOne D.rootGroup i, a * b ≠ b * a)
    (h6j : Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a)
    (h3 : HasOrderThree D i) (hij : i ≠ j) (hAij : D.cartan i j = -1) (hAji : D.cartan j i = -1)
    (hVT : (rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) ⊓ (⨆ k, H k) = ⊥)
    (hperf : ⁅rankOne D.rootGroup i ⊔ rankOne D.rootGroup j,
      rankOne D.rootGroup i ⊔ rankOne D.rootGroup j⁆ =
        rankOne D.rootGroup i ⊔ rankOne D.rootGroup j) :
    ¬ IsPSolvable 3 ↥((rankOne D.rootGroup i ⊔ rankOne D.rootGroup j).map π) := by
  intro hs
  have hker : π.ker ≤ Subgroup.center K := fun z hz => h.ker_central z hz
  have hnot9 := not_nine_dvd_card_rankOne_sup_torus h h6i h6j hij hAij hAji hVT
  set V : Subgroup K := rankOne D.rootGroup i ⊔ rankOne D.rootGroup j with hV
  obtain ⟨u, hu, hord⟩ := exists_order_three_map (π := π) h3 hker
  have hu' : u ∈ V.map π := Subgroup.map_mono (le_sup_left (b := rankOne D.rootGroup j)) hu
  have h3dvd : 3 ∣ Nat.card (V.map π) := by
    have := Subgroup.orderOf_dvd_natCard _ hu'
    rwa [hord] at this
  have h9 : ¬ 9 ∣ Nat.card (V.map π) := fun h9 => hnot9 (h9.trans (Subgroup.card_map_dvd _ _))
  exact false_of_perfect_three_pSolvable hs (map_commutator_self_eq π hperf) h3dvd h9

end Index

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
