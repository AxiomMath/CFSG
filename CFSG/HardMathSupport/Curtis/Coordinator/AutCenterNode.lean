module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSL
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHub
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel

public section

namespace CFSG.HardMathSupport.Curtis.Coordinator

open CFSG.Open CFSG.QuasithinUnique CFSG.AGLEmbedding CFSG.AGLEmbedding.ParabHub
  CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.LieType.Steinberg

section Quotient

variable {K Y : Type*} [Group K] [Finite K] [Group Y] [Finite Y] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* Y} {M : ℕ}

theorem exists_sl2_perfect_of_borelQuotient (h : BorelQuotient D n H π M) {F : Type} [Field F]
    [Finite F] [CharP F 2] (hF4 : 4 ≤ Nat.card F) (hsl : ∀ i, HasSL2Node D i F) (T : Sylow 2 Y)
    (J : Subgroup Y) (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hJ : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y)) :
    ∃ V : Subgroup Y, V ≤ J ∧ ⁅V, V⁆ = V ∧
      Nat.card V = Nat.card (Matrix.SpecialLinearGroup (Fin 2) F) := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : borel D H ≤ J.comap π' := fun b hb => by
    rw [Subgroup.mem_comap]
    exact hNJ (by rw [hNπ]; exact ⟨b, hb, rfl⟩)
  have hne : J.comap π' ≠ borel D H := by
    intro he
    apply hJ
    rw [hNπ, ← he, Subgroup.map_comap_eq_self_of_surjective hπ']
  obtain ⟨i, hi⟩ := exists_negRoot_le_of_borel_lt h.ct h.extras hBJ hne
  have hLi : rankOne D.rootGroup i ≤ J.comap π' :=
    sup_le ((rootGroup_le_borel ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
      (ht_single_pos i)).trans hBJ) hi
  obtain ⟨φ, hφ, hx, hy⟩ := hsl i
  have hrange : ∀ A, φ A ∈ rankOne D.rootGroup i := by
    have hle : Subgroup.closure (Set.range (sl2Upper (k := F)) ∪ Set.range sl2Lower) ≤
        (rankOne D.rootGroup i).comap φ := by
      rw [Subgroup.closure_le]
      rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
      · exact le_sup_left (b := D.rootGroup (-Pi.single i 1)) (hx c)
      · exact le_sup_right (a := D.rootGroup (Pi.single i 1)) (hy c)
    exact fun A => hle (Sp.mem_closure_sl2 A)
  set ψ : Matrix.SpecialLinearGroup (Fin 2) F →* Y := π'.comp φ with hψ
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_iff.2 fun A hA => ?_
    have hz : φ A ∈ Subgroup.center K := hQ.ker_central _ (by simpa [hψ] using hA)
    have hAc : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro B
      apply hφ
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.1 hz (φ B)
    rw [sl2_center_eq_bot] at hAc
    exact hAc
  refine ⟨ψ.range, ?_, ?_, ?_⟩
  · rintro _ ⟨A, rfl⟩
    exact hLi (hrange A)
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
    congr 1
    exact (sl2_isPerfect hF4).commutator_eq_top
  · exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm

end Quotient

section Parabolic

theorem exists_sylow_normalizer_lt_map {G X : Type*} [Group G] [Finite G] [Group X] [Finite X]
    (ψ : G →* X) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center G)
    (hodd : Odd (Nat.card ψ.ker)) {J T : Subgroup G} (hT : IsSylowTwoOf T ⊤)
    (hNJ : Subgroup.normalizer (T : Set G) ≤ J) (hneB : J ≠ Subgroup.normalizer (T : Set G)) :
    ∃ T' : Sylow 2 X, Subgroup.normalizer ((T' : Subgroup X) : Set X) ≤ J.map ψ ∧
      J.map ψ ≠ Subgroup.normalizer ((T' : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : ¬ 2 ∣ T.index := by
    have h := hT.2.2
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at h
  let T₀ : Sylow 2 G := hT.2.1.toSylow hidx
  refine ⟨T₀.mapSurjective hψ, ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective hψ T₀]
    exact ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1 hNJ
  · intro hJe
    apply hneB
    refine le_antisymm (fun x hx => ?_) hNJ
    have hJe' : J.map ψ = Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := by
      rw [hJe, Sylow.coe_mapSurjective hψ T₀]
      rfl
    have hmem : ψ x ∈ Subgroup.normalizer ((T.map ψ : Subgroup X) : Set X) := by
      rw [← hJe']
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hyN, hyx⟩ := ToralCensus.normalizer_map_le_map ψ hψ hker hodd hT.2.1
      (le_refl (Subgroup.normalizer (T : Set G))) hmem
    have hxy : y⁻¹ * x ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    have hzN : y⁻¹ * x ∈ Subgroup.normalizer (T : Set G) :=
      (Subgroup.center_le_normalizer ((T : Subgroup G) : Set G)) (hker hxy)
    simpa using Subgroup.mul_mem _ hyN hzN

theorem exists_isSylowTwoOf_normalizer_lt_subgroupOf {Y : Type} [Group Y] [Finite Y]
    {L J : Subgroup Y} (hP : CompParab L J) :
    ∃ T : Subgroup ↥L, IsSylowTwoOf T ⊤ ∧ Subgroup.normalizer (T : Set ↥L) ≤ J.subgroupOf L ∧
      J.subgroupOf L ≠ Subgroup.normalizer (T : Set ↥L) := by
  obtain ⟨hJL, T, ⟨hTL, hT2, hTi⟩, hNJ⟩ := hP.parab
  refine ⟨T.subgroupOf L, ⟨le_top, hT2.comap_subtype (K := L), ?_⟩, ?_, ?_⟩
  · have e : ((T.subgroupOf L).subgroupOf ⊤).index = (T.subgroupOf L).index :=
      Subgroup.relIndex_top_right _
    rw [e]
    exact hTi
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNJ ⟨x.2, Subgroup.mem_normalizer_fintype fun t ht => ?_⟩
    have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨t, hTL ht⟩).1 h1
    simpa [Subgroup.mem_subgroupOf] using h2
  · intro hJe
    apply hP.ne_borel T ⟨hTL, hT2, hTi⟩
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · have hyL : y ∈ L := hJL hy
      refine ⟨hyL, ?_⟩
      have hyG : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
      rw [hJe] at hyG
      refine Subgroup.mem_normalizer_fintype fun t ht => ?_
      have h1 : (⟨t, hTL ht⟩ : ↥L) ∈ T.subgroupOf L := Subgroup.mem_subgroupOf.2 ht
      have h2 := (Subgroup.mem_normalizer_iff.1 hyG ⟨t, hTL ht⟩).1 h1
      simpa [Subgroup.mem_subgroupOf] using h2
    · obtain ⟨hyL, hyN⟩ := hy
      have : (⟨y, hyL⟩ : ↥L) ∈ J.subgroupOf L := by
        rw [hJe, Subgroup.mem_normalizer_iff]
        intro g
        have := Subgroup.mem_normalizer_iff.1 hyN g.1
        simp only [Subgroup.mem_subgroupOf]
        exact this
      exact Subgroup.mem_subgroupOf.1 this

end Parabolic

theorem nine_dvd_four_pow_sub_one {e : ℕ} (h3 : 3 ∣ e) : 9 ∣ 4 ^ e - 1 := by
  obtain ⟨k, rfl⟩ := h3
  have h : 4 ^ (3 * k) = 64 ^ k := by rw [pow_mul]; norm_num
  rw [h]
  have := Nat.sub_dvd_pow_sub_pow 64 1 k
  rw [one_pow] at this
  exact (show 9 ∣ 64 - 1 by norm_num).trans this

theorem exists_perfect_nine_dvd_of_compParab {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    (hP : CompParab L J) {e : ℕ} (he : 2 ≤ e) (h3 : 3 ∣ e)
    (ι : ↥L ⧸ Subgroup.center ↥L ≃*
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 (GaloisField 2 e)) :
    ∃ W : Subgroup Y, W ≤ J ∧ ⁅W, W⁆ = W ∧ 9 ∣ Nat.card W := by
  have : NeZero e := ⟨by omega⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 e) = 2 ^ e := GaloisField.card 2 e (by omega)
  have hF4 : 4 ≤ Nat.card (GaloisField 2 e) := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
  set ψ := QuotientGroup.mk' (Subgroup.center ↥L) with hψ
  have hker : ψ.ker = Subgroup.center ↥L := QuotientGroup.ker_mk' _
  have hsurj : Function.Surjective ψ := QuotientGroup.mk'_surjective _
  obtain ⟨T, hT, hNJ, hneB⟩ := exists_isSylowTwoOf_normalizer_lt_subgroupOf hP
  obtain ⟨T', hNJ', hneB'⟩ := exists_sylow_normalizer_lt_map ψ hsurj hker.le
    (by rw [hker]; exact hP.odd) hT hNJ hneB
  let e' : Matrix.ProjectiveSpecialLinearGroup (Fin (2 + 1)) (GaloisField 2 e) ≃*
      (↥L ⧸ Subgroup.center ↥L) :=
    (CFSG.LocalAnalysis.ComponentInitial.LinearCover.projectiveSpecialLinearEquivProjectiveSL 3
      (GaloisField 2 e)).trans ι.symm
  obtain ⟨V, hVJ, hV, hVcard⟩ := exists_sl2_perfect_of_borelQuotient (borelQuotient_sl e') hF4
    (fun i => hasSL2Node_sl i) T' ((J.subgroupOf L).map ψ) hNJ' hneB'
  obtain ⟨W₀, hW₀, hW₀le, hW₀map⟩ := CFSG.AGLEmbedding.ParabPrime.exists_perfect_map_eq ψ hker.le hV
    (by rw [MonoidHom.range_eq_top.2 hsurj]; exact le_top)
  have hkJ : ψ.ker ≤ J.subgroupOf L :=
    hker.le.trans ((Subgroup.center_le_normalizer (T : Set ↥L)).trans hNJ)
  have hcomap : ((J.subgroupOf L).map ψ).comap ψ = J.subgroupOf L :=
    Subgroup.comap_map_eq_self hkJ
  have hW₀J : W₀ ≤ J.subgroupOf L :=
    hW₀le.trans (by rw [← hcomap]; exact Subgroup.comap_mono hVJ)
  refine ⟨W₀.map L.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hW₀J hx)
  · rw [← Subgroup.map_commutator, hW₀]
  · rw [Subgroup.card_map_of_injective L.subtype_injective]
    have h9 : 9 ∣ Nat.card V := by
      rw [hVcard, CFSG.AGLEmbedding.ParabPrime.card_sl2, hF, ← pow_mul]
      refine Dvd.dvd.mul_left ?_ _
      have h4 : (2 : ℕ) ^ (e * 2) = 4 ^ e := by rw [pow_mul']; norm_num
      rw [h4]
      exact nine_dvd_four_pow_sub_one h3
    rw [← hW₀map] at h9
    exact h9.trans (Subgroup.card_map_dvd W₀ ψ)

end CFSG.HardMathSupport.Curtis.Coordinator
