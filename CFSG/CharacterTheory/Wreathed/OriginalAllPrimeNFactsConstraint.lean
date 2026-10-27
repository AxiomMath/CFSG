module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeNFactsBasic
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization

public section

namespace CFSG.Wreathed.OriginalAllPrime

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGLocalTools
open CFSG.Wreathed.OriginalSylowCentralizerCoverage
open scoped commutatorElement Pointwise

section General

variable {H : Type*} [Group H] [Finite H]

theorem map_Op_p'p_le_of_normal (p : ℕ) [Fact p.Prime] (A : Subgroup H) [A.Normal] :
    (Op_p'p p A).map A.subtype ≤ Op_p'p p H := by
  have hchar : (Op_p'p p A).Characteristic :=
    Subgroup.Characteristic.comap_quotient_mk
      (pCore_characteristic (G := A ⧸ pPrimeCore p A) (p := p))
  have hX : (pPrimeCore p A).map A.subtype ≤ pPrimeCore p H := by
    apply le_sSup
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_map_of_injective A.subtype_injective]
    exact pPrimeCore_coprime_card
  apply Subgroup.map_le_iff_le_comap.mp
  apply le_sSup
  refine ⟨(inferInstance : ((Op_p'p p A).map A.subtype).Normal).map _
    (QuotientGroup.mk'_surjective _), ?_⟩
  rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩⟩
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := A ⧸ pPrimeCore p A)) ⟨_, ha⟩
  refine ⟨k, Subtype.ext ?_⟩
  have ha' : a ^ p ^ k ∈ pPrimeCore p A := by
    rw [← QuotientGroup.eq_one_iff]
    simpa using congrArg Subtype.val hk
  have hx : (a : H) ^ p ^ k ∈ pPrimeCore p H := hX ⟨a ^ p ^ k, ha', by simp⟩
  simpa [← map_pow] using (QuotientGroup.eq_one_iff _).mpr hx

theorem Op_p'p_subgroupOf_le (p : ℕ) [Fact p.Prime] (A : Subgroup H) :
    (Op_p'p p H).subgroupOf A ≤ Op_p'p p A := by
  have hX : (pPrimeCore p H).subgroupOf A ≤ pPrimeCore p A := by
    apply le_sSup
    refine ⟨inferInstance, Nat.Coprime.of_dvd_right ?_ (pPrimeCore_coprime_card (G := H))⟩
    rw [← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : ((Op_p'p p H).subgroupOf A).map (QuotientGroup.mk' (pPrimeCore p A)) ≤
      pCore p (A ⧸ pPrimeCore p A) := by
    apply le_sSup
    refine ⟨(inferInstance : ((Op_p'p p H).subgroupOf A).Normal).map _
      (QuotientGroup.mk'_surjective _), ?_⟩
    rintro ⟨_, ⟨a, ha, rfl⟩⟩
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := p) (G := H ⧸ pPrimeCore p H)) ⟨_, ha⟩
    refine ⟨k, Subtype.ext ?_⟩
    have ha' : (a : H) ^ p ^ k ∈ pPrimeCore p H := by
      rw [← QuotientGroup.eq_one_iff]
      simpa using congrArg Subtype.val hk
    have hx : a ^ p ^ k ∈ pPrimeCore p A := hX (by simpa [Subgroup.mem_subgroupOf] using ha')
    simpa [← map_pow] using (QuotientGroup.eq_one_iff _).mpr hx
  intro a ha
  exact hle (Subgroup.mem_map_of_mem _ ha)

theorem map_Op_p'p_eq_of_le (p : ℕ) [Fact p.Prime] (A : Subgroup H) [A.Normal]
    (hKA : Op_p'p p H ≤ A) : (Op_p'p p A).map A.subtype = Op_p'p p H := by
  apply le_antisymm (map_Op_p'p_le_of_normal p A)
  calc Op_p'p p H = ((Op_p'p p H).subgroupOf A).map A.subtype := by
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hKA]
    _ ≤ (Op_p'p p A).map A.subtype := Subgroup.map_mono (Op_p'p_subgroupOf_le p A)

theorem isSylowOf_of_le_of_not_dvd {p : ℕ} [Fact p.Prime] {P L K : Subgroup H}
    (hP : IsSylowOf p P L) (hLK : L ≤ K) (hdvd : ¬ p ∣ L.relIndex K) : IsSylowOf p P K := by
  rw [isSylowOf_iff] at hP ⊢
  obtain ⟨hPL, hPp, hPdvd⟩ := hP
  refine ⟨hPL.trans hLK, hPp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex P L K hPL hLK]
  intro h
  rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
  · exact hPdvd h
  · exact hdvd h

omit [Finite H] in
theorem le_of_isPGroup_two_of_le_sup {B O Q : Subgroup H} [B.Normal] (hQ : IsPGroup 2 Q)
    (hO : Odd (Nat.card O)) (hle : Q ≤ B ⊔ O) : Q ≤ B := by
  have hBbot : B.map (QuotientGroup.mk' B) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hmap : Q.map (QuotientGroup.mk' B) ≤ O.map (QuotientGroup.mk' B) := by
    have h := Subgroup.map_mono (f := QuotientGroup.mk' B) hle
    rwa [Subgroup.map_sup, hBbot, bot_sup_eq] at h
  have hodd : Odd (Nat.card (Q.map (QuotientGroup.mk' B))) :=
    Odd.of_dvd_nat hO ((Subgroup.card_dvd_of_le hmap).trans (Subgroup.card_map_dvd _ _))
  have hbot : Q.map (QuotientGroup.mk' B) = ⊥ :=
    eq_bot_of_odd_of_le_two_group le_rfl (hQ.map _) hodd
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  exact hbot

theorem centralizer_le_Op_p'p_of_le_solvable {p : ℕ} [Fact p.Prime] (A : Subgroup H) [A.Normal]
    (hA : Group.IsSolvable A) (hKA : Op_p'p p H ≤ A) {P : Subgroup H}
    (hP : IsSylowOf p P (Op_p'p p H)) (hCA : Subgroup.centralizer (P : Set H) ≤ A) :
    Subgroup.centralizer (P : Set H) ≤ Op_p'p p H := by
  have hPA : P ≤ A := hP.le.trans hKA
  have hmapP : (P.subgroupOf A).map A.subtype = P := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPA]
  have hPA' : IsSylowOf p (P.subgroupOf A) (Op_p'p p A) := by
    rw [← isSylowOf_map_subtype_iff A, hmapP, map_Op_p'p_eq_of_le p A hKA]
    exact hP
  have hcon := isPConstrained_of_isSolvable (p := p) hA _ hPA'
  intro c hc
  have hcA : c ∈ A := hCA hc
  have hc' : (⟨c, hcA⟩ : A) ∈ Subgroup.centralizer ((P.subgroupOf A : Subgroup A) : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc (x : H) hx
  rw [← map_Op_p'p_eq_of_le p A hKA]
  exact ⟨⟨c, hcA⟩, hcon hc', rfl⟩

end General

variable {G : Type} [Group G] [Finite G]

theorem wreathed_quaternion_le_of_normal
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (B : Subgroup (involutionCentralizer n S e)) [B.Normal]
    (hB : ¬ B ≤ centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) :
    centralizerQuaternion n hn S e ≤ B := by
  have hY : centralizerQuaternion n hn S e ≤ B ⊔ centralizerOddCore n S e := by
    rw [← centralizerOddCoreMap_ker, ← Subgroup.comap_map_eq, ← Subgroup.map_le_iff_le_comap]
    exact (original_quaternion_image_le_layer hnonab n hn S e hfour).trans
      (wreathed_layer_le_map_of_normal hnonab n hn S e hfour B hB)
  exact le_of_isPGroup_two_of_le_sup
    ((centralizerSylow n hn S e).isPGroup'.to_le (centralizerQuaternion_le_sylow n hn S e))
    (centralizerOddCore_card_odd n S e) hY

omit [Finite G] in
theorem wreathed_quaternion_not_le_fullCenter (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) :
    ¬ centralizerQuaternion n hn S e ≤ centralizerFullCenter n hn S e := fun h =>
  original_quaternion_not_isCyclic n hn S e (Subgroup.isCyclic_of_le h)

theorem wreathed_quaternion_not_le_centralizer (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (R' : Subgroup (involutionCentralizer n S e))
    (hC : Subgroup.centralizer (R' : Set (involutionCentralizer n S e)) ≤
      centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e) :
    ¬ centralizerQuaternion n hn S e ≤
      Subgroup.centralizer (R' : Set (involutionCentralizer n S e)) := by
  intro hY
  apply wreathed_quaternion_not_le_fullCenter n hn S e
  rw [← original_center_product_inf_sylow n hn S e]
  exact le_inf (hY.trans hC) (centralizerQuaternion_le_sylow n hn S e)

theorem wreathed_constrained_iff_centralizer_le
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {r : ℕ} [Fact r.Prime] (hr2 : r ≠ 2) (R' : Subgroup (involutionCentralizer n S e))
    (hR' : IsSylowOf r R' (centralizerOddCore n S e))
    (hSR' : (centralizerSylow n hn S e : Subgroup (involutionCentralizer n S e)) ≤
      Subgroup.normalizer (R' : Set (involutionCentralizer n S e))) :
    PConstrainedWithin r (involutionCentralizer n S e)
        (CFSG.solvableRadical (involutionCentralizer n S e)) ↔
      Subgroup.centralizer (R' : Set (involutionCentralizer n S e)) ≤
        centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e := by
  have hrad := wreathed_solvableRadical_eq hnonab n hn S e hfour
  have hsolv := wreathed_oddCore_sup_fullCenter_isSolvable n hn S e
  have hOodd := centralizerOddCore_card_odd n S e
  have hZtwo : IsPGroup 2 (centralizerFullCenter n hn S e) :=
    IsPGroup.of_card (centralizerFullCenter_card n hn S e)
  have hYtwo : IsPGroup 2 (centralizerQuaternion n hn S e) :=
    (centralizerSylow n hn S e).isPGroup'.to_le (centralizerQuaternion_le_sylow n hn S e)
  have hYS := centralizerQuaternion_le_sylow n hn S e
  set O := centralizerOddCore n S e
  set Z := centralizerFullCenter n hn S e
  set Y := centralizerQuaternion n hn S e
  set X := pPrimeCore r (involutionCentralizer n S e)
  set K := Op_p'p r (involutionCentralizer n S e)
  have hAn : (O ⊔ Z).Normal := by
    rw [← hrad]
    exact CFSG.ABGLocalTools.solvableRadical_normal
  have hRX : R' ⊓ X = ⊥ := by
    obtain ⟨k, hk⟩ := hR'.isPGroup.exists_card_eq
    apply disjoint_iff.mp
    apply Subgroup.disjoint_of_coprime_natCard
    rw [hk]
    exact (pPrimeCore_coprime_card (p := r) (G := involutionCentralizer n S e)).pow_left k
  rw [hrad]
  constructor
  · rintro ⟨hKA, hcon⟩
    have h1 : IsSylowOf r (R' ⊓ (K ⊓ O)) (K ⊓ O) :=
      hR'.inf_of_le_normalizer (N := K ⊓ O) inf_le_right
        (by rw [Subgroup.normalizer_eq_top]; exact le_top)
    have heq : R' ⊓ (K ⊓ O) = R' ⊓ K := by
      rw [inf_comm K O, ← inf_assoc, inf_eq_left.mpr hR'.le]
    rw [heq] at h1
    have hP₀ : IsSylowOf r (R' ⊓ K) K := by
      refine isSylowOf_of_le_of_not_dvd h1 inf_le_left ?_
      rw [Subgroup.inf_relIndex_left, ← QuotientGroup.ker_mk' O, Subgroup.relIndex_ker]
      have hmap : K.map (QuotientGroup.mk' O) ≤ Z.map (QuotientGroup.mk' O) := by
        have h := Subgroup.map_mono (f := QuotientGroup.mk' O) hKA
        rwa [Subgroup.map_sup,
          (Subgroup.map_eq_bot_iff _).mpr (QuotientGroup.ker_mk' O).ge, bot_sup_eq] at h
      obtain ⟨k, hk⟩ := ((hZtwo.map _).to_le hmap).exists_card_eq
      rw [hk]
      intro hdvd
      exact hr2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Fact.out hdvd))
    exact (Subgroup.centralizer_le (inf_le_left : R' ⊓ K ≤ R')).trans ((hcon _ hP₀).trans hKA)
  · intro hC
    have hYC := wreathed_quaternion_not_le_centralizer n hn S e R' hC
    have hXA : X ≤ O ⊔ Z := by
      by_contra hXnot
      apply hYC
      have hYX : Y ≤ X := wreathed_quaternion_le_of_normal hnonab n hn S e hfour X hXnot
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hc : ⁅y, x⁆ ∈ R' ⊓ X := by
        constructor
        · have hyx : y * x * y⁻¹ ∈ R' :=
            (Subgroup.mem_normalizer_iff.mp (hSR' (hYS hy)) x).mp hx
          rw [commutatorElement_def]
          exact R'.mul_mem hyx (R'.inv_mem hx)
        · have h : ⁅y, x⁆ = y * (x * y⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
          rw [h]
          exact X.mul_mem (hYX hy)
            ((inferInstance : X.Normal).conj_mem _ (X.inv_mem (hYX hy)) x)
      rw [hRX, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
    have hKA : K ≤ O ⊔ Z := by
      have h := Op_p'p_le_solvableRadical (p := r) (H := involutionCentralizer n S e)
        (by rw [hrad]; exact hXA)
      rwa [hrad] at h
    have hKbar : (K.map (QuotientGroup.mk' X)).Normal :=
      (inferInstance : K.Normal).map _ (QuotientGroup.mk'_surjective X)
    set W := (Subgroup.centralizer ((K.map (QuotientGroup.mk' X)) :
      Set (involutionCentralizer n S e ⧸ X))).comap (QuotientGroup.mk' X)
    have hWn : W.Normal := Subgroup.Normal.comap inferInstance _
    have hWA : W ≤ O ⊔ Z := by
      by_contra hWnot
      apply hYC
      have hYW : Y ≤ W := wreathed_quaternion_le_of_normal hnonab n hn S e hfour W hWnot
      have hP₁K : R' ⊓ (Op_p'p r O).map O.subtype ≤ K :=
        inf_le_right.trans (map_Op_p'p_le_of_normal r O)
      have hYP₁ : Y ≤ Subgroup.centralizer ((R' ⊓ (Op_p'p r O).map O.subtype :
          Subgroup (involutionCentralizer n S e)) : Set (involutionCentralizer n S e)) := by
        intro y hy
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hc : ⁅y, x⁆ ∈ R' ⊓ X := by
          constructor
          · have hyx : y * x * y⁻¹ ∈ R' :=
              (Subgroup.mem_normalizer_iff.mp (hSR' (hYS hy)) x).mp hx.1
            rw [commutatorElement_def]
            exact R'.mul_mem hyx (R'.inv_mem hx.1)
          · have hxK : QuotientGroup.mk' X x ∈ K.map (QuotientGroup.mk' X) :=
              Subgroup.mem_map_of_mem _ (hP₁K hx)
            have hcomm := Subgroup.mem_centralizer_iff.mp (hYW hy) _ hxK
            have h1 : QuotientGroup.mk' X ⁅y, x⁆ = 1 := by
              rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
              exact hcomm.symm
            exact (QuotientGroup.eq_one_iff _).mp h1
        rw [hRX, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc.symm
      exact (two_group_centralizes_sylow_iff hOodd hYtwo
        (by rw [Subgroup.normalizer_eq_top]; exact le_top) hR' (hYS.trans hSR')).mpr hYP₁
    refine ⟨hKA, fun P hP => ?_⟩
    have hsup : X ⊔ P = K := (sup_eq_Op_p'p_iff_isSylowOf hP.isPGroup).mpr hP
    have hCW : Subgroup.centralizer (P : Set (involutionCentralizer n S e)) ≤ W := by
      intro c hc
      change QuotientGroup.mk' X c ∈ Subgroup.centralizer ((K.map (QuotientGroup.mk' X)) :
        Set (involutionCentralizer n S e ⧸ X))
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨k, hk, rfl⟩
      rw [← hsup] at hk
      obtain ⟨x, hx, q, hq, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hk
      have hx1 : QuotientGroup.mk' X x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
      have hcq := Subgroup.mem_centralizer_iff.mp hc q hq
      rw [map_mul, hx1, one_mul, ← map_mul, ← map_mul, hcq]
    exact centralizer_le_Op_p'p_of_le_solvable (O ⊔ Z) hsolv hKA hP (hCW.trans hWA)

omit [Finite G] in
theorem wreathed_sylow_inf_centralizer_le_iff (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) {ell : ℕ} (P : Sylow ell (centralizerOddCore n S e)) :
    originalSylowCentralizer n S e P ≤ Subgroup.center S ↔
      (S : Subgroup G) ⊓ Subgroup.centralizer
          (((originalPrimeSubgroup n S e P).map (involutionCentralizer n S e).subtype) : Set G) ≤
        centerOf (S : Subgroup G) := by
  rw [originalSylowCentralizer_eq_ambient n hn S e P,
    ← Subgroup.map_le_map_iff_of_injective (S : Subgroup G).subtype_injective,
    Subgroup.subgroupOf_map_subtype, BrauerWong.center_map_eq_modelCenter n hn S e, centerOf,
    BrauerWong.sylow_inf_centralizer n hn S e, inf_comm]

theorem wreathed_isSylowOf_center_inf_iff (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G)
    (e : S ≃* Wreath (2 ^ n)) (R : Subgroup G)
    (hSR : (S : Subgroup G) ≤ Subgroup.normalizer (R : Set G)) :
    IsSylowOf 2 (centerOf (S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G))
        (involutionCentralizer n S e ⊓ Subgroup.centralizer (R : Set G)) ↔
      (S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G) ≤ centerOf (S : Subgroup G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSN := sylow_le_involutionCentralizer n hn S e
  set N := involutionCentralizer n S e
  set C := N ⊓ Subgroup.centralizer (R : Set G)
  have hSK : IsSylowOf 2 (S : Subgroup G) (N ⊓ Subgroup.normalizer (R : Set G)) := by
    rw [isSylowOf_iff]
    refine ⟨le_inf hSN hSR, S.isPGroup', fun h => S.not_dvd_index ?_⟩
    exact h.trans (Subgroup.relIndex_dvd_index_of_le (le_inf hSN hSR))
  have hCK : C ≤ N ⊓ Subgroup.normalizer (R : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le_normalizer _)
  have hKC : N ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg.1,
        BaseFourCentralizerStructure.normalizer_le_centralizer_normalizer R hg.2⟩
  have hSC : (S : Subgroup G) ⊓ C = (S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G) := by
    rw [← inf_assoc, inf_eq_left.mpr hSN]
  have hSyl : IsSylowOf 2 ((S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G)) C := by
    rw [← hSC]
    exact hSK.inf_of_le_normalizer hCK hKC
  have hZS : centerOf (S : Subgroup G) ≤ (S : Subgroup G) := inf_le_left
  constructor
  · intro h
    have heq := h.eq_of_le (inf_le_inf_right _ hZS) (inf_le_inf_right _ hSN)
      (S.isPGroup'.to_le inf_le_left)
    rw [heq]
    exact inf_le_left
  · intro h
    have heq : centerOf (S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G) =
        (S : Subgroup G) ⊓ Subgroup.centralizer (R : Set G) :=
      le_antisymm (inf_le_inf_right _ hZS) (le_inf h inf_le_right)
    rw [heq]
    exact hSyl

theorem wreathedSetting_N_constraint_criterion
    [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    (n : ℕ) (hn : 2 ≤ n) (S : Sylow 2 G) (e : S ≃* Wreath (2 ^ n))
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    (p f : ℕ) (_hp : p.Prime) (_hpodd : Odd p) (_hf : 1 ≤ f) (_hq : 5 < p ^ f)
    (_hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (wreathedSetting n S e p f).ON → ∀ R : Subgroup G,
      IsSylowOf r R (wreathedSetting n S e p f).ON →
        ((wreathedSetting n S e p f).S : Subgroup G) ≤ Subgroup.normalizer (R : Set G) →
          ((wreathedSetting n S e p f).Constrained r ↔
            IsSylowOf 2 (centerOf ((wreathedSetting n S e p f).S : Subgroup G) ⊓
              Subgroup.centralizer (R : Set G))
              ((wreathedSetting n S e p f).N ⊓ Subgroup.centralizer (R : Set G))) := by
  intro r hr hdiv R hRsyl hSR
  have : Fact r.Prime := ⟨hr⟩
  have hdiv' : r ∣ Nat.card (centralizerOddCore n S e) := by
    rwa [wreathedSetting_ON, card_ambientOddCore] at hdiv
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr (centralizerOddCore_card_odd n S e))
      (even_iff_two_dvd.mpr hdiv')
  obtain ⟨P, rfl⟩ := exists_original_sylow_of_isSylowOf n S e hRsyl
  have hinv := (original_Sylow_invariance_iff (n := n) hn (S := S) (e := e) (P := P)).mp hSR
  have hcrit := original_coverage_criterion_fullCenterQuotient hnonab n hn S e hfour hr hdiv' P
  have hB : originalPrimeCentralizer n S e P ≤
        centralizerOddCore n S e ⊔ centralizerFullCenter n hn S e ↔
      originalSylowCentralizer n S e P ≤ Subgroup.center S :=
    not_iff_not.mp (hcrit.1.symm.trans (hcrit.2.2.1 hinv).1)
  have hC := wreathed_constrained_iff_centralizer_le hnonab n hn S e hfour hr2
    (originalPrimeSubgroup n S e P) ⟨P, rfl⟩ hinv
  change PConstrainedWithin r (involutionCentralizer n S e)
      (CFSG.solvableRadical (involutionCentralizer n S e)) ↔
    IsSylowOf 2 (centerOf (S : Subgroup G) ⊓ Subgroup.centralizer
        (((originalPrimeSubgroup n S e P).map (involutionCentralizer n S e).subtype) : Set G))
      (involutionCentralizer n S e ⊓ Subgroup.centralizer
        (((originalPrimeSubgroup n S e P).map (involutionCentralizer n S e).subtype) : Set G))
  rw [hC, wreathed_isSylowOf_center_inf_iff n hn S e
    ((originalPrimeSubgroup n S e P).map (involutionCentralizer n S e).subtype) hSR,
    ← wreathed_sylow_inf_centralizer_le_iff n hn S e P]
  exact hB

end CFSG.Wreathed.OriginalAllPrime
