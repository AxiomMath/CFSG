module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDeduce

public section

namespace CFSG.AGLEmbedding.LieOut

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.LieType.Universal
  CFSG.LieType.CurtisTits

theorem exists_rankOne_le_of_borel {K Y : Type} [Group K] [Finite K] [Group Y] [Finite Y]
    {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
    {π : K →* Y} {M : ℕ} (h : BorelQuotient D n H π M) (S : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer (S : Set Y) ≤ J) (hJ : J ≠ Subgroup.normalizer (S : Set Y)) :
    ∃ π' : K →* Y, Function.Surjective π' ∧ π'.ker = π.ker ∧
      Subgroup.normalizer (((CFSG.LieType.Steinberg.posUnipotent D).map π' : Subgroup Y) :
        Set Y) ≤ J ∧
      ∃ i, (CFSG.LieType.CurtisTits.rankOne D.rootGroup i).map π' ≤ J := by
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq S
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hNπ := hQ.normalizer_map_posUnipotent
  rw [← hT] at hNπ
  have hBJ : (CFSG.LieType.Steinberg.borel D H).map π' ≤ J := by
    rw [← hNπ]
    exact hNJ
  have hne : J ≠ (CFSG.LieType.Steinberg.borel D H).map π' := by
    rw [← hNπ]
    exact hJ
  have hBA : CFSG.LieType.Steinberg.borel D H ≤ J.comap π' := fun b hb => hBJ ⟨b, hb, rfl⟩
  have hAne : J.comap π' ≠ CFSG.LieType.Steinberg.borel D H := by
    intro h'
    apply hne
    rw [← Subgroup.map_comap_eq_self_of_surjective hπ' J, h']
  obtain ⟨i₀, hi₀⟩ := negIndices_nonempty_of_ne h.ct h.extras hBA hAne
  exact ⟨π', hπ', hker, by rw [← hT]; exact hNJ, i₀,
    Subgroup.map_le_iff_le_comap.2 (rankOne_le_of_mem_negIndices hBA hi₀)⟩

theorem quotImage_ne_normalizer {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (hT : IsSylowTwoOf T L) (hJL : J ≤ L) (hJ : J ≠ L ⊓ Subgroup.normalizer (T : Set Y))
    (hNT : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J) :
    quotImage L J ≠ Subgroup.normalizer ((barSylow hT : Subgroup (↥L ⧸ Subgroup.center ↥L)) :
      Set (↥L ⧸ Subgroup.center ↥L)) := by
  intro h
  apply hJ
  exact le_antisymm (le_borel_of_quotImage_le hT hJL h.le) hNT

section SL

variable {F : Type} [Field F] [Finite F] [CharP F 2] {m : ℕ}

open CFSG.LieType.Universal.SpecialLinear CFSG.LieType.Steinberg

theorem exists_node_of_psl {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* (↥L ⧸ Subgroup.center ↥L))
    (hT : IsSylowTwoOf T L) (hJL : J ≤ L) (hNT : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J)
    (hJ : J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) :
    ∃ S : Subgroup (↥L ⧸ Subgroup.center ↥L), S ≤ quotImage L J ∧
      Nonempty (↥S ≃* Matrix.SpecialLinearGroup (Fin 2) F) := by
  have h := borelQuotient_sl e
  obtain ⟨π', hπ', hker, -, i, hi⟩ := exists_rankOne_le_of_borel h (barSylow hT) (quotImage L J)
    (normalizer_barSylow_le_quotImage hT hNT) (quotImage_ne_normalizer hT hJL hJ hNT)
  obtain ⟨φ, hφ, hx, hy⟩ := SL.rankOne (m := m) (F := F) i
  have hrank := rankOne_eq_range_of_sl2 SL.isParametrization hx hy
  refine ⟨(π'.comp φ).range, ?_, ?_⟩
  · rw [MonoidHom.range_comp, ← hrank]
    exact hi
  · have hinj : Function.Injective (π'.comp φ) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      have hs1 : π' (φ s) = 1 := hs
      have hc : φ s ∈ Subgroup.center _ := h.ker_central _ (hker ▸ MonoidHom.mem_ker.2 hs1)
      have hs' : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
        rw [Subgroup.mem_center_iff]
        intro t
        apply hφ
        rw [map_mul, map_mul]
        exact Subgroup.mem_center_iff.1 hc (φ t)
      rw [sl2_center_eq_bot, Subgroup.mem_bot] at hs'
      rw [hs']
      exact Subgroup.one_mem _
    exact ⟨(MonoidHom.ofInjective hinj).symm⟩

theorem exists_quasisimple_of_psl {Y : Type} [Group Y] [Finite Y] {L T J : Subgroup Y}
    (e : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* (↥L ⧸ Subgroup.center ↥L))
    (hT : IsSylowTwoOf T L) (hJL : J ≤ L) (hNT : L ⊓ Subgroup.normalizer (T : Set Y) ≤ J)
    (hJ : J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hpq : p ∣ Nat.card F - 1)
    (hq : Nat.card (alternatingGroup (Fin p)) < Nat.card F * (Nat.card F ^ 2 - 1) ∨
      (p = 7 ∧ Nat.card F = 8)) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X := by
  obtain ⟨S, hSJ, ⟨eS⟩⟩ := exists_node_of_psl e hT hJL hNT hJ
  have hA : 60 ≤ Nat.card (alternatingGroup (Fin p)) := by
    rcases hp57 with rfl | rfl
    · rw [nat_card_alt_five]
    · rw [nat_card_alt_seven]; norm_num
  have hF4 : 4 ≤ Nat.card F := by
    by_contra hlt
    have h3 : Nat.card F ≤ 3 := by omega
    rcases hq with hq | ⟨-, hq⟩
    · have : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 3 * (3 ^ 2 - 1) := by
        apply Nat.mul_le_mul h3
        have := Nat.pow_le_pow_left h3 2
        omega
      omega
    · omega
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F) := sl2_isPerfect hF4
  have hsimple : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := sl2_isSimpleGroup hF4
  have hSperf : Group.IsPerfect ↥S :=
    Group.IsPerfect.ofSurjective (f := eS.symm.toMonoidHom) eS.symm.surjective
  have hSs : IsSimpleGroup ↥S := eS.isSimpleGroup
  have hcard : Nat.card S = Nat.card F * (Nat.card F ^ 2 - 1) := by
    rw [Nat.card_congr eS.toEquiv, card_sl2]
  have hpS : p ∣ Nat.card S := by
    rw [hcard]
    refine Dvd.dvd.mul_left (hpq.trans ?_) _
    simpa using Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
  have hno : NoAp p ↥S := by
    rcases hq with hq | ⟨rfl, hq8⟩
    · exact NoAp.of_card_lt (by rw [hcard]; exact hq)
    · exact noAp_seven_of_card_eq (by rw [hcard, hq8]; norm_num)
  exact exists_quasisimple_of_node (fun z hz => center_le_of_normalizer_le hT hNT hz) hSJ
    (commutator_eq_self_of_isPerfect S hSperf) hSs hpS hno

end SL



section Main

theorem four_le_of_five_dvd {f : ℕ} (hf : 1 ≤ f) (h : 5 ∣ 2 ^ f - 1) : 4 ≤ f := by
  by_contra hlt
  have : f < 4 := by omega
  interval_cases f <;> simp at h

theorem three_le_of_seven_dvd {f : ℕ} (hf : 1 ≤ f) (h : 7 ∣ 2 ^ f - 1) : 3 ≤ f := by
  by_contra hlt
  have : f < 3 := by omega
  interval_cases f <;> simp at h

theorem exists_quasisimple_of_model_psl {Y : Type} [Group Y] [Finite Y] {L J : Subgroup Y}
    {n f p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (h : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL n 2 f)
    (hpf : p ∣ 2 ^ f - 1) (hpar : IsParabolicTwo L J)
    (hnB : ∀ T : Subgroup Y, IsSylowTwoOf T L → J ≠ L ⊓ Subgroup.normalizer (T : Set Y)) :
    ∃ X : Subgroup Y, X ≤ J ∧ CFSG.Open.IsQuasisimple ↥X ∧ p ∣ Nat.card X ∧
      ∀ φ : ↥X →* alternatingGroup (Fin p), ¬ φ.ker ≤ Subgroup.center ↥X := by
  obtain ⟨hJL, T, hT, hNT⟩ := hpar
  obtain ⟨⟨-, hf, hn, -⟩, F, hF, hFfin, hcard, ⟨e⟩⟩ := h
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e' : Matrix.ProjectiveSpecialLinearGroup (Fin (m + 1)) F ≃* (↥L ⧸ Subgroup.center ↥L) :=
    (projectiveSpecialLinearGroupEquivStatedProj (m + 1) F).trans e.symm
  have hpq : p ∣ Nat.card F - 1 := by rw [hcard]; exact hpf
  refine exists_quasisimple_of_psl e' hT hJL hNT (hnB T hT) hp57 hpq ?_
  rw [hcard]
  rcases hp57 with rfl | rfl
  · left
    have := four_le_of_five_dvd hf hpf
    rw [nat_card_alt_five]
    calc 60 < 16 * (16 ^ 2 - 1) := by norm_num
      _ ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
        have h16 : 16 ≤ 2 ^ f := by
          calc 16 = 2 ^ 4 := by norm_num
            _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) this
        exact Nat.mul_le_mul h16 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 2) 1)
  · have h3 := three_le_of_seven_dvd hf hpf
    rcases Nat.lt_or_ge f 4 with h4 | h4
    · right
      refine ⟨rfl, ?_⟩
      have : f = 3 := by omega
      subst this
      norm_num
    · left
      rw [nat_card_alt_seven]
      calc 2520 < 16 * (16 ^ 2 - 1) := by norm_num
        _ ≤ 2 ^ f * ((2 ^ f) ^ 2 - 1) := by
          have h16 : 16 ≤ 2 ^ f := by
            calc 16 = 2 ^ 4 := by norm_num
              _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h4
          exact Nat.mul_le_mul h16 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h16 2) 1)

end Main

end CFSG.AGLEmbedding.LieOut
