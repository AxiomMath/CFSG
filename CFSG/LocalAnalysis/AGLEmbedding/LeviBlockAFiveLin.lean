module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockAFiveDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusLinThreeSetup
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Lin
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockL28Symp
import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockLinTorus
import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial LinearFlag LeviBlock
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

private theorem flag_eq_two_of_lt {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4) {a b : Fin 4}
    (hab : (a : ℕ) < b) (ha : linBlockLen 4 I a = 2) (hb : linBlockLen 4 I b = 2) :
    I = {2} := by
  have hstart : ∀ c : Fin 4, linBlockLen 4 I c = 2 → (c : ℕ) = 0 ∨ (c : ℕ) ∈ I := by
    intro c hc
    by_contra hns
    rw [linBlockLen_of_not_start hns] at hc
    omega
  obtain ⟨-, -, -, ha4⟩ := linBlockLen_spec (hstart a ha)
  obtain ⟨hb1, -, -, hb4⟩ := linBlockLen_spec (hstart b hb)
  rw [ha] at ha4
  rw [hb] at hb1 hb4
  have hne : a ≠ b := fun h => by rw [h] at hab; exact lt_irrefl _ hab
  have hab2 : (a : ℕ) + 2 ≤ b := by
    by_contra hlt
    exact linBlock_disjoint (I := I) hne (r := (b : ℕ)) hab.le (by rw [ha]; omega) le_rfl
      (by rw [hb]; omega)
  have h2I : 2 ∈ I := by
    rcases hstart b hb with h0 | hmem
    · omega
    · rwa [show (b : ℕ) = 2 by omega] at hmem
  ext i
  simp only [Set.mem_singleton_iff]
  refine ⟨fun hi => ?_, fun hi => by rw [hi]; exact h2I⟩
  have := hI i hi
  have h1 := ha4 i hi
  have h3 := hb4 i hi
  omega

private theorem flag_eq_two_of_two_blocks {I : Set ℕ} (hI : ∀ i ∈ I, 1 ≤ i ∧ i < 4)
    {a b : Fin 4} (hab : a ≠ b) (ha : linBlockLen 4 I a = 2) (hb : linBlockLen 4 I b = 2) :
    I = {2} := by
  rcases lt_or_gt_of_ne (fun h => hab (Fin.ext h) : (a : ℕ) ≠ b) with h | h
  · exact flag_eq_two_of_lt hI h ha hb
  · exact flag_eq_two_of_lt hI h hb ha

private theorem e9_of_rankThree {Y : Type} [Group Y] {L : Subgroup Y} {M : Type*} [CommGroup M]
    (hM : Nat.card M = 3) (φ : (Fin 3 → M) →* Y) (hφ : Function.Injective φ)
    (hL : φ.range ≤ L) (hc : ∀ a, φ a ∈ Subgroup.centralizer (L : Set Y) → a = 1) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  set ι : (Fin 2 → M) →* (Fin 3 → M) :=
    Function.ExtendByOne.hom M (Fin.castLE (by norm_num : 2 ≤ 3))
  have hι : Function.Injective ι := sympL28_extendByOne_injective (by norm_num)
  refine ⟨(φ.comp ι).range, ?_, isElemAbelian_range_of_pow (fun a b => mul_comm a b)
    (fun a => ?_) _, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩
    exact hL ⟨ι a, rfl⟩
  · funext j
    rw [Pi.pow_apply, Pi.one_apply, ← hM]
    exact pow_card_eq_one'
  · rw [← Nat.card_congr (MonoidHom.ofInjective (f := φ.comp ι) (hφ.comp hι)).toEquiv,
      Nat.card_fun, hM, Nat.card_fin]
  · rw [eq_bot_iff]
    rintro _ ⟨⟨a, rfl⟩, hxC⟩
    have h1 : ι a = 1 := hc _ hxC
    rw [Subgroup.mem_bot, MonoidHom.comp_apply, h1, map_one]

private theorem e9_of_ker_eq_center {Y : Type} [Group Y] {L : Subgroup Y} {K : Type} [Field K]
    (hK : Nat.card K = 4) (ρ : Matrix.SpecialLinearGroup (Fin 3) K →* ↥L)
    (hker : ρ.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K))
    (e : ↥L ⧸ Subgroup.center ↥L ≃* projectiveSL 3 K)
    (hcompat : ∀ g, e (QuotientGroup.mk (ρ g)) = proj 3 K g) :
    ∃ E : Subgroup Y, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      E ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
  set Q := LinearThreeFourFixedNine.qSub (k := K) with hQ
  set φ : Matrix.SpecialLinearGroup (Fin 3) K →* Y := L.subtype.comp ρ
  have hφker : φ.ker = scalars 3 K := by
    rw [scalars_eq_center, ← hker]
    ext g
    simp [φ, MonoidHom.mem_ker]
  have hcard : Nat.card (Q.map φ) = 9 := by
    have h := Subgroup.card_ker_mul_card_range (φ.comp Q.subtype)
    rw [MonoidHom.range_comp, Subgroup.range_subtype, LinearThreeFourFixedNine.card_qSub hK] at h
    have hk : (φ.comp Q.subtype).ker = (scalars 3 K).subgroupOf Q := by
      rw [← MonoidHom.comap_ker, hφker]
      rfl
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      LinearThreeFourFixedNine.scalars_le_qSub).toEquiv,
      LinearThreeFourFixedNine.card_scalars hK] at h
    omega
  have hpow : ∀ x ∈ Q.map φ, x ^ 3 = 1 := by
    rintro _ ⟨g, hg, rfl⟩
    rw [hQ, LinearThreeFourFixedNine.coe_qSub] at hg
    obtain ⟨y, rfl⟩ := hg
    rw [← map_pow, LinearThreeFourFixedNine.qElt_pow_three hK, map_one]
  refine ⟨Q.map φ, ?_, ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hcard, hpow⟩,
    hcard, ?_⟩
  · rintro _ ⟨g, -, rfl⟩
    exact (ρ g).2
  · rw [eq_bot_iff]
    rintro _ ⟨⟨g, -, rfl⟩, hxC⟩
    have hZ : ρ g ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxC h h.2
    have h2 : g ∈ ρ.ker := by
      rw [hker, ← scalars_eq_center, ← proj_eq_one_iff, ← hcompat,
        (QuotientGroup.eq_one_iff _).mpr hZ, map_one]
    rw [Subgroup.mem_bot, MonoidHom.comp_apply, MonoidHom.mem_ker.mp h2]
    rfl

theorem kFactCompParabTwoFivesOn_linear
    (hLB : LeviBlocksOfFiveComponents)
    (hGA : GriessAllModelsStatement) : KFactCompParabTwoFivesOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA h3 C₁ C₂ hne hC₁ hC₂
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hcompat, hI, -, -, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨β, hβk, hβp, hβc⟩ := exists_linLeviData_of_comap_eq (by omega) ρ hcomap
  obtain ⟨a, b, hab, ha, hb, ha60, hb60⟩ := (hLB Y L P hCP.parab.1 _ ρ hρs hker (Fin n)
    (fun a => Matrix.GeneralLinearGroup (Fin (linBlockLen n I a)) (GaloisField 2 f))
    (linBlockSL (GaloisField 2 f) n I) β hβk hβp hβc
    (isQuasisimple_or_isSolvable_linBlockSL I)).2 C₁ C₂ hne hC₁ hC₂
  obtain ⟨hla, hK4⟩ := linBlock_eq_two_of_sixty hK ha ha60
  obtain ⟨hlb, -⟩ := linBlock_eq_two_of_sixty hK hb hb60
  have h4 := linL28_four_le_of_two_blocks hab hla hlb
  have hu : Nat.card (GaloisField 2 f)ˣ = 3 := by rw [Nat.card_units, hK4]
  obtain rfl : n = 4 := by
    by_contra hn4
    obtain ⟨φ, hinj, hrange, -⟩ := exists_linTorus_embedding (r := 4) (by omega)
      (by rw [hu]; norm_num) ρ hker e hcompat hcomap
    have hpow : ∀ x : Fin 4 → (GaloisField 2 f)ˣ, x ^ 3 = 1 := fun x => by
      funext j
      rw [Pi.pow_apply, Pi.one_apply, ← hu]
      exact pow_card_eq_one'
    have hcard : Nat.card (Fin 4 → (GaloisField 2 f)ˣ) = 3 ^ 4 := by
      rw [Nat.card_fun, hu, Nat.card_fin]
    have := CFSG.SectionRank.le_pRank_of_injective (by norm_num) (fun x y => mul_comm x y) hpow
      hcard φ hinj (hrange.trans hCP.parab.1)
    omega
  obtain rfl : f = 2 :=
    Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by rw [← hK, hK4])
  obtain rfl : I = {2} := flag_eq_two_of_two_blocks hI hab hla hlb
  exact Or.inl ⟨ρ, e, hρs, hker, hcompat, hcomap⟩

theorem kFactCompParabOneFiveOn_linear
    (hLB : LeviBlocksOfFiveComponents)
    (hGA : GriessAllModelsStatement) : KFactCompParabOneFiveOn (IsLieOf IdxA) := by
  intro Y _ _ L P hCP hA C hC
  obtain ⟨n, f, ρ, e, I, hn, hf, hρs, hker, hcompat, hI, hIne, hInb, hcomap⟩ :=
    ToralCensus.exists_cover_comap_eq_flagStabilizer hGA hCP hA
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  obtain ⟨β, hβk, hβp, hβc⟩ := exists_linLeviData_of_comap_eq (by omega) ρ hcomap
  obtain ⟨a, ha, ha60⟩ := (hLB Y L P hCP.parab.1 _ ρ hρs hker (Fin n)
    (fun a => Matrix.GeneralLinearGroup (Fin (linBlockLen n I a)) (GaloisField 2 f))
    (linBlockSL (GaloisField 2 f) n I) β hβk hβp hβc
    (isQuasisimple_or_isSolvable_linBlockSL I)).1 C hC
  obtain ⟨-, hK4⟩ := linBlock_eq_two_of_sixty hK ha ha60
  have hu : Nat.card (GaloisField 2 f)ˣ = 3 := by rw [Nat.card_units, hK4]
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · obtain rfl : n = 3 := by omega
    obtain rfl : f = 2 :=
      Nat.pow_right_injective le_rfl (show 2 ^ f = 2 ^ 2 by rw [← hK, hK4])
    by_cases hbot : ρ.ker = ⊥
    · right
      obtain ⟨i, hiI⟩ := hIne
      obtain ⟨j, hj1, hj3, hjI⟩ := hInb
      have hi := hI i hiI
      have hIi : I = {i} := by
        ext x
        simp only [Set.mem_singleton_iff]
        refine ⟨fun hx => ?_, fun hx => by rw [hx]; exact hiI⟩
        have hx' := hI x hx
        by_contra hxi
        have hj : j = x ∨ j = i := by omega
        rcases hj with rfl | rfl
        · exact hjI hx
        · exact hjI hiI
      refine ⟨ρ, e, i, ⟨(MonoidHom.ker_eq_bot_iff ρ).mp hbot, hρs⟩, hcompat, by omega, ?_⟩
      rw [hcomap, hIi]
    · left
      have hcard3 : Nat.card (Subgroup.center
          (Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))) = 3 := by
        rw [← scalars_eq_center, LinearThreeFourFixedNine.card_scalars hK4]
      have hkc : ρ.ker = Subgroup.center _ := by
        apply Subgroup.eq_of_le_of_card_ge hker
        rw [hcard3]
        have hdvd := Subgroup.card_dvd_of_le hker
        rw [hcard3] at hdvd
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
        · exact absurd (Subgroup.eq_bot_of_card_eq _ h1) hbot
        · omega
      exact e9_of_ker_eq_center hK4 ρ hkc e hcompat
  · left
    obtain ⟨φ, hinj, hrange, hc⟩ := exists_linTorus_embedding (r := 3) (by omega)
      (by rw [hu]; norm_num) ρ hker e hcompat hcomap
    exact e9_of_rankThree hu φ hinj (hrange.trans hCP.parab.1) hc

end CFSG.AGLEmbedding
