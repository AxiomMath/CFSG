module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.KFactLinThreeOut
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.Unitary
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Torus

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq

open CFSG.Open CFSG.AGLEmbedding CFSG.AGLEmbeddingD2

variable {X : Type} [Group X] [Finite X]

theorem k1Core_inf_eq {Z F F' : Subgroup X} (hZ : Z ≠ ⊥) (hZF : Z ≤ F) (hZF' : Z ≤ F')
    (hF : Nat.card F = 9) (hF' : Nat.card F' = 9) (hne : F ≠ F') :
    F ⊓ F' = Z ∧ Nat.card Z = 3 := by
  have hI9 : Nat.card (F ⊓ F' : Subgroup X) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← hF]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hIne : Nat.card (F ⊓ F' : Subgroup X) ≠ 9 := by
    intro h9
    apply hne
    have h1 : F ⊓ F' = F := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hF, h9])
    have h2 : F ⊓ F' = F' := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hF', h9])
    rw [← h1, h2]
  have hZI : Nat.card Z ∣ Nat.card (F ⊓ F' : Subgroup X) :=
    Subgroup.card_dvd_of_le (le_inf hZF hZF')
  have hZ1 : Nat.card Z ≠ 1 := fun h => hZ (Subgroup.card_eq_one.mp h)
  obtain ⟨i, hi, hIi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hI9
  have hI3 : Nat.card (F ⊓ F' : Subgroup X) = 3 := by
    interval_cases i
    · rw [hIi, pow_zero, Nat.dvd_one] at hZI
      exact absurd hZI hZ1
    · rw [hIi, pow_one]
    · exact absurd (by rw [hIi]; norm_num) hIne
  have hZ3 : Nat.card Z = 3 := by
    rw [hI3] at hZI
    rcases (Nat.dvd_prime Nat.prime_three).mp hZI with h | h
    · exact absurd h hZ1
    · exact h
  exact ⟨(Subgroup.eq_of_le_of_card_ge (le_inf hZF hZF') (by rw [hI3, hZ3])).symm, hZ3⟩

theorem k1Core_false_of_five {R Z : Subgroup X} (hR : Nat.card R = 27) (hZ : Z ≠ ⊥)
    (F : Fin 5 → Subgroup X) (hne : ∀ i j, i ≠ j → F i ≠ F j) (hZF : ∀ i, Z ≤ F i)
    (hFR : ∀ i, F i ≤ R) (hF : ∀ i, Nat.card (F i) = 9) : False := by
  classical
  have := Fintype.ofFinite X
  have hZ3 : Nat.card Z = 3 := (k1Core_inf_eq hZ (hZF 0) (hZF 1) (hF 0) (hF 1)
    (hne 0 1 (by decide))).2
  have hc : ∀ H : Subgroup X, ((H : Set X).toFinset).card = Nat.card H := fun H => by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    rfl
  let T : Fin 5 → Finset X := fun i => (F i : Set X).toFinset \ (Z : Set X).toFinset
  have hdisj : ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)).PairwiseDisjoint T := by
    intro i _ j _ hij
    change Disjoint (T i) (T j)
    rw [Finset.disjoint_left]
    intro x hxi hxj
    simp only [T, Finset.mem_sdiff, Set.mem_toFinset, SetLike.mem_coe] at hxi hxj
    have hx : x ∈ F i ⊓ F j := ⟨hxi.1, hxj.1⟩
    rw [(k1Core_inf_eq hZ (hZF i) (hZF j) (hF i) (hF j) (hne i j hij)).1] at hx
    exact hxi.2 hx
  have hT : ∀ i, (T i).card = 6 := by
    intro i
    simp only [T]
    rw [Finset.card_sdiff_of_subset (Set.toFinset_subset_toFinset.mpr (hZF i)), hc, hc, hF i,
      hZ3]
  have hsub : (Finset.univ : Finset (Fin 5)).biUnion T ⊆
      (R : Set X).toFinset \ (Z : Set X).toFinset := by
    intro x hx
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, T, Finset.mem_sdiff,
      Set.mem_toFinset, SetLike.mem_coe] at hx ⊢
    obtain ⟨i, hxi, hxZ⟩ := hx
    exact ⟨hFR i hxi, hxZ⟩
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Finset.card_sdiff_of_subset
    (Set.toFinset_subset_toFinset.mpr ((hZF 0).trans (hFR 0))), hc, hc, hR, hZ3] at h1
  simp only [hT, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  omega

theorem k1Core_mem_normalizer_center {R : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (R : Set X)) :
    g ∈ Subgroup.normalizer ((R ⊓ Subgroup.centralizer (R : Set X) : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro z
  have hgi : ∀ r, r ∈ R ↔ g⁻¹ * r * g⁻¹⁻¹ ∈ R := fun r => by
    rw [hg (g⁻¹ * r * g⁻¹⁻¹)]
    group
  constructor
  · intro hz
    obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨(hg z).mp hzR, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    intro r hr
    have h1 := hzC (g⁻¹ * r * g) (by simpa using (hgi r).mp hr)
    calc r * (g * z * g⁻¹) = g * ((g⁻¹ * r * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * r * g)) * g⁻¹ := by rw [h1]
      _ = g * z * g⁻¹ * r := by group
  · intro hz
    obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
    refine Subgroup.mem_inf.mpr ⟨(hg z).mpr hzR, ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hzC ⊢
    intro r hr
    have h1 := hzC (g * r * g⁻¹) ((hg r).mp hr)
    have h2 : g * (r * z) * g⁻¹ = g * (z * r) * g⁻¹ := by
      calc g * (r * z) * g⁻¹ = (g * r * g⁻¹) * (g * z * g⁻¹) := by group
        _ = (g * z * g⁻¹) * (g * r * g⁻¹) := h1
        _ = g * (z * r) * g⁻¹ := by group
    simpa using h2

theorem k1Core_map_conj_center {R : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (R : Set X)) :
    (R ⊓ Subgroup.centralizer (R : Set X)).map (MulAut.conj g).toMonoidHom =
      R ⊓ Subgroup.centralizer (R : Set X) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (k1Core_mem_normalizer_center hg)

theorem k1Core_center_le {R F : Subgroup X} (hR : Nat.card R = 27)
    (hnab : ¬ R ≤ Subgroup.centralizer (R : Set X)) (hFR : F ≤ R) (hFc : Nat.card F = 9)
    (hFab : IsMulCommutative F) :
    R ⊓ Subgroup.centralizer (R : Set X) ≤ F := by
  intro z hz
  by_contra hzF
  obtain ⟨hzR, hzC⟩ := Subgroup.mem_inf.mp hz
  set S : Subgroup X := F ⊔ Subgroup.zpowers z with hS
  have hSR : S ≤ R := sup_le hFR (Subgroup.zpowers_le.mpr hzR)
  have hFS : F < S := lt_of_le_of_ne le_sup_left fun h =>
    hzF (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hSc : Nat.card S = 27 := by
    have hdvd : Nat.card S ∣ 27 := hR ▸ Subgroup.card_dvd_of_le hSR
    have hdvd' : 9 ∣ Nat.card S := hFc ▸ Subgroup.card_dvd_of_le hFS.le
    have hlt : 9 < Nat.card S := hFc ▸ Subgroup.card_lt_of_lt hFS
    have hle : Nat.card S ≤ 27 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card S <;> omega
  have hSRe : S = R := Subgroup.eq_of_le_of_card_ge hSR (by rw [hR, hSc])
  apply hnab
  rw [← hSRe]
  have hzC' : Subgroup.zpowers z ≤ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.zpowers_le]
    rw [hSRe]
    exact hzC
  have hFC : F ≤ Subgroup.centralizer (S : Set X) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.le_centralizer_iff_isMulCommutative.mpr hFab) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.centralizer_le hFR hzC
  exact sup_le hFC hzC'

theorem k1Core_center_ne_bot {R : Subgroup X} (hRp : IsPGroup 3 R) (hR1 : R ≠ ⊥) :
    R ⊓ Subgroup.centralizer (R : Set X) ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  have := hRp.center_nontrivial
  obtain ⟨w, hw1⟩ := exists_ne (1 : Subgroup.center R)
  intro hbot
  apply hw1
  have hwZ : ((w : R) : X) ∈ R ⊓ Subgroup.centralizer (R : Set X) := by
    refine Subgroup.mem_inf.mpr ⟨(w : R).2, Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp w.2 ⟨r, hr⟩))
  rw [hbot, Subgroup.mem_bot] at hwZ
  exact Subtype.ext (Subtype.ext hwZ)

theorem k1Core_false_of_u3 {R : Sylow 3 X} {A X₀ K B : Subgroup X}
    (h : D2AlmostSimple 3 X R A X₀ K) {d : TauCeti.ValidLieTypeIndex}
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hd : ∃ q : TauCeti.PrimePower, q.p = 3 ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q)
    (hBR : B ≤ R) (hB : IsElemAbelian 3 B) (hBc : Nat.card B = 9)
    (hconj : ∀ g : X, B.map (MulAut.conj g).toMonoidHom ≠ A) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨q, hqp, hq1, hdq⟩ := hd
  have hRK : (R : Subgroup X) ≤ K := h.sylow_le_of_not_dvd_card_outer
    (kFactLieCharOut K d ⟨e⟩ 3 Nat.prime_three (by norm_num) ⟨q, hqp, Or.inr ⟨hq1, Or.inr hdq⟩⟩)
  have hf1 : d.1.fieldExponent = 1 := by rw [hdq]; simp [hq1]
  obtain ⟨hcard, hcomm, -, -⟩ :=
    kFactUnitarySylowStructure K 3 d (by norm_num) ⟨q, hqp, hdq⟩ ⟨e⟩ (R.subtype hRK)
  rw [hf1, Sylow.coe_subtype] at hcard
  rw [Sylow.coe_subtype] at hcomm
  have hR27 : Nat.card (R : Subgroup X) = 27 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRK).toEquiv, hcard]
    norm_num
  have hnab : ¬ (R : Subgroup X) ≤ Subgroup.centralizer ((R : Subgroup X) : Set X) := by
    intro hab
    have hab' : (R : Subgroup X).subgroupOf K ≤
        Subgroup.centralizer (((R : Subgroup X).subgroupOf K : Subgroup K) : Set K) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hab (Subgroup.mem_subgroupOf.mp hx)) y
        (Subgroup.mem_subgroupOf.mp hy))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hab', inf_eq_left.mpr hab'] at hcomm
    have h1 : Nat.card ((R : Subgroup X).subgroupOf K) = 1 := by rw [← hcomm, Subgroup.card_bot]
    rw [hcard] at h1
    norm_num at h1
  set Z := (R : Subgroup X) ⊓ Subgroup.centralizer ((R : Subgroup X) : Set X) with hZ
  have hZA : Z ≤ A := k1Core_center_le hR27 hnab h.A_le (by rw [h.card_A]; norm_num) h.elem.1
  have hZB : Z ≤ B := k1Core_center_le hR27 hnab hBR hBc hB.1
  have hZne : Z ≠ ⊥ := k1Core_center_ne_bot R.isPGroup' fun hbot => by
    rw [hbot, Subgroup.card_bot] at hR27
    norm_num at hR27
  obtain ⟨t, -, htN, -, -, -, hlines⟩ := exists_lines_torus_u3
    Nat.prime_three (by norm_num) e ⟨q, hqp, hq1, hdq⟩ hRK
  have h4 : (3 + 1) / Nat.gcd 3 (3 + 1) = 4 := by decide
  rw [h4] at hlines
  have hBidx : B.relIndex (R : Subgroup X) = 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := B) (K := (R : Subgroup X))
    rw [inf_eq_left.mpr hBR, hBc, hR27] at h1
    omega
  set G : ℕ → Subgroup X := fun j => B.map (MulAut.conj (t ^ j)).toMonoidHom with hG
  have htj : ∀ j : ℕ, t ^ j ∈ Subgroup.normalizer ((R : Subgroup X) : Set X) :=
    fun j => Subgroup.pow_mem _ htN j
  have hGR : ∀ j, G j ≤ R := fun j =>
    (Subgroup.map_mono hBR).trans (Subgroup.mem_normalizer_iff_map_conj_eq.mp (htj j)).le
  have hZG : ∀ j, Z ≤ G j := fun j =>
    (k1Core_map_conj_center (htj j)).symm.le.trans (Subgroup.map_mono hZB)
  have hGc : ∀ j, Nat.card (G j) = 9 := fun j => by
    rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hBc]
  have hAG : ∀ j, A ≠ G j := fun j h1 => hconj (t ^ j) h1.symm
  have hGG : ∀ i j, i < j → j < 4 → G i ≠ G j := by
    intro i j hij hj h1
    refine hlines (j - i) (by omega) (by omega) B hZB hBR hBidx
      (Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_)
    have h2 : (B.map (MulAut.conj (t ^ (j - i))).toMonoidHom).map
        (MulAut.conj (t ^ i)).toMonoidHom = G i := by
      rw [map_map_conj_eq_map_conj_mul, ← pow_add, Nat.add_sub_cancel' hij.le, h1]
    exact Subgroup.map_injective (MulAut.conj (t ^ i)).injective h2
  let F : Fin 5 → Subgroup X := fun i => if (i : ℕ) = 0 then A else G ((i : ℕ) - 1)
  refine k1Core_false_of_five hR27 hZne F ?_ ?_ ?_ ?_
  · intro i j hij
    have hij' : (i : ℕ) ≠ j := fun h1 => hij (Fin.ext h1)
    have hi5 := i.2
    have hj5 := j.2
    dsimp only [F]
    split_ifs with hi hj hj
    · exact absurd (hi.trans hj.symm) hij'
    · exact hAG _
    · exact (hAG _).symm
    · rcases Nat.lt_or_gt_of_ne hij' with h1 | h1
      · exact hGG _ _ (by omega) (by omega)
      · exact (hGG _ _ (by omega) (by omega)).symm
  · intro i
    dsimp only [F]
    split_ifs
    exacts [hZA, hZG _]
  · intro i
    dsimp only [F]
    split_ifs
    exacts [h.A_le, hGR _]
  · intro i
    dsimp only [F]
    split_ifs
    exacts [by rw [h.card_A]; norm_num, hGc _]

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.RankTwoUniq
