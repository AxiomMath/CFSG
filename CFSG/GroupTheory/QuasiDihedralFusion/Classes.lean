module

public import CFSG.GroupTheory.QuasiDihedralFusion.SemidihedralClassification
public import CFSG.GroupTheory.QuasiDihedralFusion.WreathedClassification
public import CFSG.GroupTheory.QuasiDihedralFusion.QGroup
public import CFSG.GroupTheory.QuasiDihedralFusion.Structure

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.Open CFSG.Semidihedral CFSG.Wreathed CFSG.Wreathed.BrauerWong CFSG.GorensteinWalter
open CFSG.BenderSuzuki.External CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {H : Type u} [Group H] [Finite H]

section Common

omit [Finite H] in
theorem isConj_of_conjClassCountOfOrder_eq_one {k : ℕ} (h : conjClassCountOfOrder H k = 1)
    (x y : H) (hx : orderOf x = k) (hy : orderOf y = k) : IsConj x y := by
  rw [conjClassCountOfOrder, Set.ncard_eq_one] at h
  obtain ⟨c, hc⟩ := h
  have hxc : ConjClasses.mk x ∈ ConjClasses.mk '' {x : H | orderOf x = k} := ⟨x, hx, rfl⟩
  have hyc : ConjClasses.mk y ∈ ConjClasses.mk '' {x : H | orderOf x = k} := ⟨y, hy, rfl⟩
  rw [hc, Set.mem_singleton_iff] at hxc hyc
  exact ConjClasses.mk_eq_mk_iff_isConj.mp (hxc.trans hyc.symm)

theorem hasSemidihedralSylow_of {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : HasSemidihedralSylow H n :=
  ⟨hn, fun S' => ⟨f.trans (Sylow.equiv S S')⟩⟩

theorem hasWreathedSylow_of {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) : HasWreathedSylow H n :=
  ⟨hn, fun S' => ⟨(Sylow.equiv S' S).trans e⟩⟩

omit [Finite H] in
theorem four_dvd_card_of_semidihedral {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : 4 ∣ Nat.card H := by
  have h1 : Nat.card (S : Subgroup H) = 2 ^ n := by
    rw [← Nat.card_congr f.toEquiv, CFSG.Semidihedral.card n (by omega)]
  have h2 : Nat.card (S : Subgroup H) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  rw [h1] at h2
  exact dvd_trans (by rw [show (4 : ℕ) = 2 ^ 2 by norm_num]; exact pow_dvd_pow 2 (by omega)) h2

omit [Finite H] in
theorem four_dvd_card_of_wreathed {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) : 4 ∣ Nat.card H := by
  have h1 : Nat.card (S : Subgroup H) = 2 * (2 ^ n) ^ 2 := by
    rw [Nat.card_congr e.toEquiv, card_wreath]
  have h2 : Nat.card (S : Subgroup H) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  rw [h1] at h2
  have h2n : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
  have h4 : 4 ∣ (2 ^ n) ^ 2 := by
    rw [sq]
    exact mul_dvd_mul h2n h2n
  exact dvd_trans (dvd_mul_of_dvd_right h4 2) h2

theorem two_dvd_of_four_dvd {m : ℕ} (h : 4 ∣ m) : 2 ∣ m := dvd_trans ⟨2, rfl⟩ h

omit [Finite H] in
theorem two_dvd_card_of_index_two {K : Subgroup H} (hK : K.index = 2) (h4 : 4 ∣ Nat.card H) :
    2 ∣ Nat.card K := by
  have h := K.card_mul_index
  rw [hK] at h
  rw [← h] at h4
  exact Nat.dvd_of_mul_dvd_mul_right two_pos (by simpa using h4)

theorem two_dvd_card_of_sylow {K : Type*} [Group K] [Finite K] (P : Sylow 2 K)
    (hP : 2 ∣ Nat.card P) : 2 ∣ Nat.card K :=
  dvd_trans hP (Subgroup.card_subgroup_dvd_card _)

theorem two_dvd_card_of_hasGeneralizedQuaternionSylow {K : Type*} [Group K] [Finite K]
    (hK : HasGeneralizedQuaternionSylow K) : 2 ∣ Nat.card K := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨k, -, ⟨e⟩⟩ := hK P
  apply two_dvd_card_of_sylow P
  rw [Nat.card_congr e.toEquiv, card_quaternionGroup_two_pow]
  exact ⟨2 * 2 ^ k, by ring⟩

theorem two_dvd_card_of_hasDihedralSylowTwo {K : Type*} [Group K] [Finite K]
    (hK : HasDihedralSylowTwo K) : 2 ∣ Nat.card K := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨m, -, ⟨e⟩⟩ := hK P
  apply two_dvd_card_of_sylow P
  rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact ⟨2 ^ m, rfl⟩

theorem IsQGroupData.not_hasNormalPComplement {R : Sylow 2 H} {K : Subgroup H}
    (h : IsQGroupData R K) : ¬ HasNormalPComplement 2 H := by
  intro hC
  have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement hC K h.noIndexTwo
  obtain ⟨k, -, ⟨eY⟩⟩ := h.quaternion.exists_quaternion_equiv
  have hcard : Nat.card (K ⊓ (R : Subgroup H) : Subgroup H) = 4 * 2 ^ k := by
    rw [Nat.card_congr eY.toEquiv, card_quaternionGroup_two_pow]
  have hdvd : Nat.card (K ⊓ (R : Subgroup H) : Subgroup H) ∣ Nat.card K :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hcard] at hdvd
  have h2 : 2 ∣ Nat.card K := dvd_trans ⟨2 * 2 ^ k, by ring⟩ hdvd
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

omit [Finite H] in
theorem weaklyClosedIn_bot (R : Subgroup H) : WeaklyClosedIn R ⊥ := by
  refine ⟨bot_le, fun g _ => ?_⟩
  change (⊥ : Subgroup H).map (MulAut.conj g⁻¹).toMonoidHom = ⊥
  exact Subgroup.map_bot _

omit [Finite H] in
theorem weaklyClosedIn_of_le_of_card_two {R Z Z₀ : Subgroup H} (hZ : WeaklyClosedIn R Z)
    (hcard : Nat.card Z = 2) (hZ₀ : Z₀ ≤ Z) : WeaklyClosedIn R Z₀ := by
  have : Fact (Nat.card Z).Prime := ⟨by rw [hcard]; exact Nat.prime_two⟩
  rcases Subgroup.eq_bot_or_eq_top_of_prime_card (Z₀.subgroupOf Z) with h | h
  · have hdis := Subgroup.subgroupOf_eq_bot.mp h
    have : Z₀ = ⊥ := (hdis.mono_right hZ₀ |>.eq_bot_of_le le_rfl)
    rw [this]
    exact weaklyClosedIn_bot R
  · rw [le_antisymm hZ₀ (Subgroup.subgroupOf_eq_top.mp h)]
    exact hZ

end Common

section Semidihedral

variable {n : ℕ}

theorem IsQDGroup.of_semidihedralFusionQD (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (h : SemidihedralFusionQD S f) : IsQDGroup H where
  sylow := ⟨1, Or.inl ⟨rfl, n, hasSemidihedralSylow_of hn S f⟩⟩
  noIndexTwo := h.noIndexTwo
  involutions_isConj := isConj_of_conjClassCountOfOrder_eq_one h.involutionClasses

theorem semidihedralFusionQD_of_noIndexTwo (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (h : ∀ K : Subgroup H, K.index ≠ 2) :
    SemidihedralFusionQD S f := by
  rcases semidihedral_two_fusion_classification hn S f with h1 | h2 | h3 | h4
  · exact h1
  · obtain ⟨K, -, hK, -⟩ := h2.exists_kernel
    exact absurd hK (h K)
  · obtain ⟨K, -, hK, -⟩ := h3.exists_kernel
    exact absurd hK (h K)
  · obtain ⟨M, hM⟩ := exists_index_two_of_hasNormalPComplement h4.normalComplement
      (two_dvd_of_four_dvd (four_dvd_card_of_semidihedral hn S f))
    exact absurd hM (h M)

theorem semidihedral_isQDGroup_iff {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : IsQDGroup H ↔ SemidihedralFusionQD S f :=
  ⟨fun hQD => semidihedralFusionQD_of_noIndexTwo hn S f hQD.noIndexTwo,
    IsQDGroup.of_semidihedralFusionQD hn S f⟩

theorem isQGroup_of_semidihedralFusionQ (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (h : SemidihedralFusionQ S f) : IsQGroup H := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  have ha : ¬ IsConj (ι (s n)) (ι (z n)) := by
    intro ha
    have h6 := automizerIndex_qdFour_eq_six hn S f ha
    rw [h.fourIndex] at h6
    norm_num at h6
  have hb : IsConj (ι (r n * s n)) (ι (r n ^ (2 ^ (n - 3)))) := by
    by_contra hb
    have h2 := outerAutomizerIndex_qdQuaternion_eq_two hn S f hb
    rw [h.quaternionIndex] at h2
    norm_num at h2
  have hF := (focal_cases_ambient hn S f).2.2.1 ha hb
  obtain ⟨K, hK, hKindex, -, hKS⟩ := exists_focal_kernel S
  rw [hF] at hKindex hKS
  have : K.Normal := hK
  have hK2 : K.index = 2 :=
    hKindex.trans ((supplied_index_two n hn f _).mpr (Or.inr (Or.inr rfl)))
  have hsub : (K ⊓ (S : Subgroup H)).subgroupOf (S : Subgroup H) =
      Subgroup.closure {f (r n) ^ 2, f (r n) * f (s n)} := by
    rw [hKS]
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem (S : Subgroup H).subtype_injective
  have hcard : Nat.card (centerOf (S : Subgroup H)) = 2 := by
    rw [centerOf_eq_zpowers_z hn (S : Subgroup H) f, Nat.card_zpowers, orderOf_ambientHom,
      orderOf_z n (by omega)]
  refine ⟨S, K, ⟨hK, ⟨1, by rw [hK2, pow_one]⟩, quaternion_kernel_noIndexTwo hn S f hb K hK2 hKS,
    ⟨inf_le_right, Or.inl ⟨n, hn, f.symm.toMonoidHom, f.symm.injective, ?_⟩⟩,
    fun Z₀ hZ₀ => weaklyClosedIn_of_le_of_card_two h.center_weaklyClosed hcard hZ₀⟩⟩
  rw [hsub, ← map_quaternionSubgroup n f, Subgroup.map_map]
  have hid : f.symm.toMonoidHom.comp (f : SemidihedralGroup n →* S) =
      MonoidHom.id (SemidihedralGroup n) := by
    ext x
    simp
  rw [hid, Subgroup.map_id]

theorem semidihedralFusionQ_of_isQGroup (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (hQ : IsQGroup H) : SemidihedralFusionQ S f := by
  set ι := FocalFusion.ambientHom n (S : Subgroup H) f with hι
  obtain ⟨K, hK⟩ := hQ.exists_data S
  have hiso := centerOf_isolated S hK.center_weaklyClosed
  have hzC : ι (z n) ∈ centerOf (S : Subgroup H) := by
    rw [centerOf_eq_zpowers_z hn (S : Subgroup H) f]
    exact Subgroup.mem_zpowers _
  have ha : ¬ IsConj (ι (s n)) (ι (z n)) := by
    intro hsz
    obtain ⟨c, hc⟩ := isConj_iff.mp hsz
    have h2 : c⁻¹ * ι (z n) * c = ι (s n) := by
      rw [← hc]
      group
    have h1 := hiso _ hzC c (h2 ▸ ambientHom_mem (S : Subgroup H) f (s n))
    exact s_ne_z hn (FocalFusion.ambientHom_injective n _ f (h2.symm.trans h1))
  have h2 := automizerIndex_qdFour_eq_two hn S f ha
  rcases semidihedral_two_fusion_classification hn S f with h1 | h2' | h3 | h4
  · exact absurd (h1.fourIndex.symm.trans h2) (by norm_num)
  · exact h2'
  · exact absurd (h3.fourIndex.symm.trans h2) (by norm_num)
  · exact (hK.not_hasNormalPComplement h4.normalComplement).elim

theorem semidihedral_isQGroup_iff {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : IsQGroup H ↔ SemidihedralFusionQ S f :=
  ⟨semidihedralFusionQ_of_isQGroup hn S f, isQGroup_of_semidihedralFusionQ hn S f⟩

theorem semidihedralFusionD_of_isDGroup (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (hD : IsDGroup H) : SemidihedralFusionD S f := by
  have hSD := hasSemidihedralSylow_of hn S f
  rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
  · exact (not_hasSemidihedralSylow_and_dihedral hSD hdih).elim
  · have : K.Normal := hK.normal
    rcases hK.sylow with ⟨m, -, hKD⟩ | ⟨m, hW, -⟩
    · rcases semidihedral_two_fusion_classification hn S f with h1 | h2 | h3 | h4
      · exact absurd hK.index_eq_two (h1.noIndexTwo K)
      · exfalso
        obtain ⟨K', hK'n, hK'2, hK'3, hK'Q⟩ := h2.exists_kernel
        have : K'.Normal := hK'n
        have hKK' : K = K' := eq_of_noIndexTwo K K' ⟨1, by rw [hK.index_eq_two, pow_one]⟩
          ⟨1, by rw [hK'2, pow_one]⟩ hK.noIndexTwo hK'3
        subst hKK'
        obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
        obtain ⟨k, hk, ⟨eQ⟩⟩ := hK'Q P
        obtain ⟨m', -, ⟨eD⟩⟩ := hKD P
        exact not_injective_quaternion_dihedral (two_le_two_pow hk)
          (eQ.symm.trans eD).toMonoidHom (eQ.symm.trans eD).injective
      · exact h3
      · exfalso
        have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement h4.normalComplement K
          hK.noIndexTwo
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
          (two_dvd_card_of_index_two hK.index_eq_two (four_dvd_card_of_semidihedral hn S f)))
    · exact (not_hasSemidihedralSylow_and_wreathed hSD hW).elim

theorem isDGroup_of_semidihedralFusionD (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) (h : SemidihedralFusionD S f) : IsDGroup H := by
  obtain ⟨K, hK, hK2, hK3, hKD⟩ := h.exists_kernel
  exact Or.inr ⟨K, ⟨hK, hK2, hK3, Or.inl ⟨n, hasSemidihedralSylow_of hn S f, hKD⟩⟩⟩

theorem semidihedral_isDGroup_iff {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) : IsDGroup H ↔ SemidihedralFusionD S f :=
  ⟨semidihedralFusionD_of_isDGroup hn S f, isDGroup_of_semidihedralFusionD hn S f⟩

theorem semidihedral_hasNormalPComplement_iff {n : ℕ} (hn : 4 ≤ n) (S : Sylow 2 H)
    (f : SemidihedralGroup n ≃* S) :
    HasNormalPComplement 2 H ↔ SemidihedralFusionComplement S f := by
  refine ⟨fun hC => ?_, fun h => h.normalComplement⟩
  rcases semidihedral_two_fusion_classification hn S f with h1 | h2 | h3 | h4
  · obtain ⟨M, hM⟩ := exists_index_two_of_hasNormalPComplement hC
      (two_dvd_of_four_dvd (four_dvd_card_of_semidihedral hn S f))
    exact absurd hM (h1.noIndexTwo M)
  · obtain ⟨K, -, -, hK3, hKQ⟩ := h2.exists_kernel
    have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement hC K hK3
    exact ((Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
      (two_dvd_card_of_hasGeneralizedQuaternionSylow hKQ))).elim
  · obtain ⟨K, -, -, hK3, hKD⟩ := h3.exists_kernel
    have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement hC K hK3
    exact ((Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
      (two_dvd_card_of_hasDihedralSylowTwo hKD))).elim
  · exact h4

end Semidihedral

section Wreathed

variable {n : ℕ}

theorem IsQDGroup.of_wreathedFusionQD (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) (h : WreathedFusionQD S e) : IsQDGroup H where
  sylow := ⟨n, Or.inr (hasWreathedSylow_of hn S e)⟩
  noIndexTwo := h.noIndexTwo
  involutions_isConj := isConj_of_conjClassCountOfOrder_eq_one h.involutionClasses

theorem wreathedFusionQD_of_noIndexTwo (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) (h : ∀ K : Subgroup H, K.index ≠ 2) :
    WreathedFusionQD S e := by
  rcases wreathed_two_fusion_classification hn S e with h1 | h2 | h3 | h4
  · exact h1
  · obtain ⟨K, hKn, hK, -⟩ := h2.exists_kernel
    have : K.Normal := hKn
    obtain ⟨M, hM⟩ := exists_index_two_of_two_pow_index K hK (by omega)
    exact absurd hM (h M)
  · exfalso
    have hβ : Nat.card (Subgroup.normalizer (modelV S e : Set H) ⧸
        modelVInnerCentralizer S e) = 2 := by
      rw [← outerAutomizerIndex_modelV]
      exact h3.quaternionIndex
    have hF := model_base_contains_focal_of_v_order_two n hn S e hβ
    obtain ⟨M, -, hM⟩ := FocalTransfer.exists_index_two_of_focal_ne S (fun hF' =>
      modelBase_proper_in_sylow S e (le_antisymm (modelBase_le_sylow S e)
        (by rw [← hF']; exact hF)))
    exact h M hM
  · obtain ⟨M, hM⟩ := exists_index_two_of_hasNormalPComplement h4.normalComplement
      (two_dvd_of_four_dvd (four_dvd_card_of_wreathed hn S e))
    exact absurd hM (h M)

theorem wreathed_isQDGroup_iff {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) : IsQDGroup H ↔ WreathedFusionQD S e :=
  ⟨fun hQD => wreathedFusionQD_of_noIndexTwo hn S e hQD.noIndexTwo,
    IsQDGroup.of_wreathedFusionQD hn S e⟩

omit [Finite H] in
theorem baseIndex_ne_six_of_base_order_two (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n))
    (hα : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2) :
    automizerIndex (modelBase S e) ≠ 6 := by
  rw [automizerIndex_modelBase, hα]
  norm_num

theorem isQGroup_of_wreathedFusionQ (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) (h : WreathedFusionQ S e) : IsQGroup H := by
  have hα : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2 := by
    rw [← automizerIndex_modelBase]
    exact h.baseIndex
  have hβ : Nonempty (Subgroup.normalizer (modelV S e : Set H) ⧸ modelVInnerCentralizer S e ≃*
      Equiv.Perm (Fin 3)) := by
    rcases modelVNormalizerQuotient_alternatives n hn S e with h2 | h6
    · rw [← outerAutomizerIndex_modelV, h.quaternionIndex] at h2
      norm_num at h2
    · exact h6
  obtain ⟨G₀, hG₀, hidx, hQ⟩ := typeII_of_base_order_two n hn S e hα hβ
  have : G₀.Normal := hG₀
  have hKS : G₀ ⊓ (S : Subgroup H) = modelY S e := by
    rw [inf_comm]
    exact (typeII_subgroup_spec n hn S e G₀ hidx hQ).1
  have hpow : ∃ k : ℕ, G₀.index = 2 ^ k := ⟨n, hidx⟩
  have hnoindex : ∀ M : Subgroup G₀, M.index ≠ 2 := by
    intro M hM
    have hYK : modelY S e ≤ G₀ := by
      rw [← hKS]
      exact inf_le_left
    have hY := modelY_le_commutator hn S e hβ G₀ hpow hYK
    apply inf_sylow_not_le_map_of_index_two S G₀ hM
    rw [hKS]
    exact hY.trans (Subgroup.map_mono (commutator_le_of_index_two hM))
  have hsub : (G₀ ⊓ (S : Subgroup H)).subgroupOf (S : Subgroup H) =
      (Original.Y (2 ^ n)).map e.symm.toMonoidHom := by
    rw [hKS, modelY, wreathModelHom, ← Subgroup.map_map]
    ext x
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_map_iff_mem (S : Subgroup H).subtype_injective
  refine ⟨S, G₀, ⟨hG₀, hpow, hnoindex,
    ⟨inf_le_right, Or.inr ⟨n, hn, e.toMonoidHom, e.injective, ?_⟩⟩, h.center_weaklyClosed⟩⟩
  rw [hsub, Subgroup.map_map]
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (Wreath (2 ^ n)) :=
    MonoidHom.ext fun x => by simp
  rw [hid, Subgroup.map_id]

theorem wreathedFusionQ_of_isQGroup (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) (hQ : IsQGroup H) : WreathedFusionQ S e := by
  obtain ⟨K, hK⟩ := hQ.exists_data S
  have hiso := centerOf_isolated S hK.center_weaklyClosed
  have hα : Nat.card (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H))) = 2 := by
    rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with h2 | h6
    · exact h2
    · exfalso
      obtain ⟨c, hc⟩ := isConj_iff.mp (isConj_x_x2_of_base_sym3 hn S e h6)
      have hxC : wreathModelHom S e (Original.x (2 ^ n)) ∈ centerOf (S : Subgroup H) := by
        rw [centerOf_eq_modelCenter hn S e]
        exact wreath_x_mem_modelCenter S e
      have h1 := hiso _ hxC c⁻¹ (by rw [inv_inv, hc]; exact wreathModelHom_mem S e _)
      rw [inv_inv, hc] at h1
      exact modelHom_x_ne_x2 S e (by omega) h1.symm
  rcases wreathed_two_fusion_classification hn S e with h1 | h2 | h3 | h4
  · exact absurd h1.baseIndex (baseIndex_ne_six_of_base_order_two S e hα)
  · exact h2
  · exact absurd h3.baseIndex (baseIndex_ne_six_of_base_order_two S e hα)
  · exact (hK.not_hasNormalPComplement h4.normalComplement).elim

theorem wreathed_isQGroup_iff {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) : IsQGroup H ↔ WreathedFusionQ S e :=
  ⟨wreathedFusionQ_of_isQGroup hn S e, isQGroup_of_wreathedFusionQ hn S e⟩

theorem isDGroup_of_wreathedFusionD (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) (h : WreathedFusionD S e) : IsDGroup H := by
  have hα : Nonempty (Subgroup.normalizer (modelBase S e : Set H) ⧸
      (Subgroup.centralizer (modelBase S e : Set H)).subgroupOf
        (Subgroup.normalizer (modelBase S e : Set H)) ≃* Equiv.Perm (Fin 3)) := by
    rcases modelBaseNormalizerQuotient_alternatives n (by omega) S e with h2 | h6
    · rw [← automizerIndex_modelBase, h.baseIndex] at h2
      norm_num at h2
    · exact h6
  have hβ : Nat.card (Subgroup.normalizer (modelV S e : Set H) ⧸
      modelVInnerCentralizer S e) = 2 := by
    rw [← outerAutomizerIndex_modelV]
    exact h.quaternionIndex
  obtain ⟨K, hK, hKindex, hKpow, hKS⟩ := exists_focal_kernel S
  have : K.Normal := hK
  have hF : K ⊓ (S : Subgroup H) = modelBase S e := by
    rw [hKS, Subgroup.subgroupOf_map_subtype, Subgroup.commutator_inf_eq_focalSubgroup S]
    apply le_antisymm (model_base_contains_focal_of_v_order_two n hn S e hβ)
    rw [← Subgroup.commutator_inf_eq_focalSubgroup S]
    exact le_inf (modelBase_le_derived hn S e hα) (modelBase_le_sylow S e)
  have hsub : (commutator H).subgroupOf (S : Subgroup H) =
      (baseSubgroup (2 ^ n)).map e.symm.toMonoidHom := by
    have h1 : ((commutator H).subgroupOf (S : Subgroup H)).map (S : Subgroup H).subtype =
        ((baseSubgroup (2 ^ n)).map e.symm.toMonoidHom).map (S : Subgroup H).subtype := by
      rw [← hKS, hF, modelBase, wreathModelHom, ← Subgroup.map_map]
    exact Subgroup.map_injective (S : Subgroup H).subtype_injective h1
  have hK2 : K.index = 2 := by
    rw [hKindex, hsub, index_map_mulEquiv, ← Original.U_eq]
    exact (wreath_center_involution_and_quaternion_coordinates n hn).base_index
  have hnoindex : ∀ M : Subgroup K, M.index ≠ 2 := by
    intro M hM
    have hUK : modelBase S e ≤ K := by
      rw [← hF]
      exact inf_le_left
    have hU := modelBase_le_commutator hn S e hα K hKpow hUK
    apply inf_sylow_not_le_map_of_index_two S K hM
    rw [hF]
    exact hU.trans (Subgroup.map_mono (commutator_le_of_index_two hM))
  refine Or.inr ⟨K, ⟨hK, hK2, hnoindex, Or.inr ⟨n, hasWreathedSylow_of hn S e, fun P => ?_⟩⟩⟩
  obtain ⟨eP⟩ := nonempty_sylow_equiv_inf S K P
  rw [hF] at eP
  exact isMulCommutative_of_mulEquiv eP.symm
    (isMulCommutative_of_le_modelBase S e (le_refl _))

theorem wreathedFusionD_of_isDGroup (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) (hD : IsDGroup H) : WreathedFusionD S e := by
  have hW := hasWreathedSylow_of hn S e
  rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
  · exact (not_hasWreathedSylow_and_dihedral hW hdih).elim
  · have : K.Normal := hK.normal
    rcases hK.sylow with ⟨m, hSD, -⟩ | ⟨m, -, hKab⟩
    · exact (not_hasSemidihedralSylow_and_wreathed hSD hW).elim
    · rcases wreathed_two_fusion_classification hn S e with h1 | h2 | h3 | h4
      · exact absurd hK.index_eq_two (h1.noIndexTwo K)
      · exfalso
        obtain ⟨K', hK'n, hK'idx, hK'3, hK'Q⟩ := h2.exists_kernel
        have : K'.Normal := hK'n
        have hKK' : K = K' := eq_of_noIndexTwo K K' ⟨1, by rw [hK.index_eq_two, pow_one]⟩
          ⟨n, hK'idx⟩ hK.noIndexTwo hK'3
        subst hKK'
        obtain ⟨P⟩ : Nonempty (Sylow 2 K) := inferInstance
        obtain ⟨k, hk, ⟨eQ⟩⟩ := hK'Q P
        exact quaternionGroup_not_isMulCommutative (two_le_two_pow hk)
          (isMulCommutative_of_mulEquiv eQ (hKab P))
      · exact h3
      · exfalso
        have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement h4.normalComplement K
          hK.noIndexTwo
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
          (two_dvd_card_of_index_two hK.index_eq_two (four_dvd_card_of_wreathed hn S e)))

theorem wreathed_isDGroup_iff {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) : IsDGroup H ↔ WreathedFusionD S e :=
  ⟨wreathedFusionD_of_isDGroup hn S e, isDGroup_of_wreathedFusionD hn S e⟩

theorem wreathed_hasNormalPComplement_iff {n : ℕ} (hn : 2 ≤ n) (S : Sylow 2 H)
    (e : (S : Subgroup H) ≃* Wreath (2 ^ n)) :
    HasNormalPComplement 2 H ↔ WreathedFusionComplement S e := by
  refine ⟨fun hC => ?_, fun h => h.normalComplement⟩
  rcases wreathed_two_fusion_classification hn S e with h1 | h2 | h3 | h4
  · obtain ⟨M, hM⟩ := exists_index_two_of_hasNormalPComplement hC
      (two_dvd_of_four_dvd (four_dvd_card_of_wreathed hn S e))
    exact absurd hM (h1.noIndexTwo M)
  · obtain ⟨K, -, -, hK3, hKQ⟩ := h2.exists_kernel
    have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement hC K hK3
    exact ((Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
      (two_dvd_card_of_hasGeneralizedQuaternionSylow hKQ))).elim
  · obtain ⟨K, -, hK3, hKS⟩ := h3.exists_kernel
    have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement hC K hK3
    have hxK : wreathModelHom S e (Original.x (2 ^ n)) ∈ K := by
      have h := BrauerWong.modelHom_x_mem_modelBase S e
      rw [← hKS] at h
      exact h.1
    have h2 : 2 ∣ Nat.card K := by
      rw [← orderOf_wreath_x hn S e, ← Subgroup.orderOf_mk _ hxK]
      exact orderOf_dvd_natCard _
    exact ((Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)).elim
  · exact h4

end Wreathed

section General

theorem isQDGroup_iff :
    IsQDGroup H ↔ HasQDOrWreathedSylow H ∧ ∀ K : Subgroup H, K.index ≠ 2 := by
  refine ⟨fun h => ⟨h.sylow, h.noIndexTwo⟩, fun ⟨hS, hK⟩ => ?_⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨h, hh⟩ := hS
  rcases hh with ⟨-, n, hn, hSD⟩ | ⟨hn, hW⟩
  · obtain ⟨f⟩ := hSD S
    exact IsQDGroup.of_semidihedralFusionQD hn S f (semidihedralFusionQD_of_noIndexTwo hn S f hK)
  · obtain ⟨e⟩ := hW S
    exact IsQDGroup.of_wreathedFusionQD hn S e (wreathedFusionQD_of_noIndexTwo hn S e hK)

omit [Finite H] in
theorem exists_sylow_model (hH : HasQDOrWreathedSylow H) (S : Sylow 2 H) :
    (∃ n : ℕ, 4 ≤ n ∧ Nonempty (SemidihedralGroup n ≃* S)) ∨
      ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((S : Subgroup H) ≃* Wreath (2 ^ n)) := by
  obtain ⟨h, hh⟩ := hH
  rcases hh with ⟨-, n, hn, hSD⟩ | ⟨hn, hW⟩
  · exact Or.inl ⟨n, hn, hSD S⟩
  · exact Or.inr ⟨h, hn, hW S⟩

omit [Finite H] in
theorem IsDGroupData.hasQDOrWreathedSylow {K : Subgroup H} (h : IsDGroupData K) :
    HasQDOrWreathedSylow H := by
  rcases h.sylow with ⟨n, hSD, -⟩ | ⟨n, hW, -⟩
  · exact ⟨1, Or.inl ⟨rfl, n, hSD⟩⟩
  · exact ⟨n, Or.inr hW⟩

theorem fusion_classes_disjoint :
    (IsQDGroup H → ¬ IsQGroup H) ∧ (IsQDGroup H → ¬ IsDGroup H) ∧
      (IsQDGroup H → ¬ HasNormalPComplement 2 H) ∧ (IsQGroup H → ¬ IsDGroup H) ∧
      (IsQGroup H → ¬ HasNormalPComplement 2 H) ∧ (IsDGroup H → ¬ HasNormalPComplement 2 H) := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  refine ⟨fun hQD hQ => ?_, fun hQD hD => ?_, fun hQD hC => ?_, fun hQ hD => ?_,
    fun hQ hC => ?_, fun hD hC => ?_⟩
  · rcases exists_sylow_model hQD.sylow S with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact absurd (((semidihedral_isQDGroup_iff hn S f).mp hQD).fourIndex.symm.trans
        ((semidihedral_isQGroup_iff hn S f).mp hQ).fourIndex) (by norm_num)
    · exact absurd (((wreathed_isQDGroup_iff hn S e).mp hQD).baseIndex.symm.trans
        ((wreathed_isQGroup_iff hn S e).mp hQ).baseIndex) (by norm_num)
  · rcases exists_sylow_model hQD.sylow S with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact absurd (((semidihedral_isQDGroup_iff hn S f).mp hQD).quaternionIndex.symm.trans
        ((semidihedral_isDGroup_iff hn S f).mp hD).quaternionIndex) (by norm_num)
    · exact absurd (((wreathed_isQDGroup_iff hn S e).mp hQD).quaternionIndex.symm.trans
        ((wreathed_isDGroup_iff hn S e).mp hD).quaternionIndex) (by norm_num)
  · rcases exists_sylow_model hQD.sylow S with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · exact absurd (((semidihedral_isQDGroup_iff hn S f).mp hQD).fourIndex.symm.trans
        ((semidihedral_hasNormalPComplement_iff hn S f).mp hC).fourIndex) (by norm_num)
    · exact absurd (((wreathed_isQDGroup_iff hn S e).mp hQD).baseIndex.symm.trans
        ((wreathed_hasNormalPComplement_iff hn S e).mp hC).baseIndex) (by norm_num)
  · rcases hD with ⟨hdih, -⟩ | ⟨K, hK⟩
    · obtain ⟨R, K, hRK⟩ := hQ
      obtain ⟨k, hk, ⟨eY⟩⟩ := hRK.quaternion.exists_quaternion_equiv
      obtain ⟨m, -, ⟨eD⟩⟩ := hdih R
      let φ : QuaternionGroup (2 ^ k) →* DihedralGroup (2 ^ m) :=
        eD.toMonoidHom.comp ((Subgroup.inclusion (inf_le_right : K ⊓ (R : Subgroup H) ≤ R)).comp
          eY.symm.toMonoidHom)
      exact not_injective_quaternion_dihedral (two_le_two_pow hk) φ
        (eD.injective.comp ((Subgroup.inclusion_injective
          (inf_le_right : K ⊓ (R : Subgroup H) ≤ R)).comp eY.symm.injective))
    · rcases exists_sylow_model hK.hasQDOrWreathedSylow S with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨e⟩⟩
      · exact absurd (((semidihedral_isQGroup_iff hn S f).mp hQ).fourIndex.symm.trans
          ((semidihedral_isDGroup_iff hn S f).mp (Or.inr ⟨K, hK⟩)).fourIndex) (by norm_num)
      · exact absurd (((wreathed_isQGroup_iff hn S e).mp hQ).baseIndex.symm.trans
          ((wreathed_isDGroup_iff hn S e).mp (Or.inr ⟨K, hK⟩)).baseIndex) (by norm_num)
  · obtain ⟨R, K, hRK⟩ := hQ
    exact hRK.not_hasNormalPComplement hC
  · rcases hD with ⟨-, hc⟩ | ⟨K, hK⟩
    · exact hc hC
    · have : K.Normal := hK.normal
      have hodd := odd_card_of_noIndexTwo_of_hasNormalPComplement hC K hK.noIndexTwo
      have h4 : 4 ∣ Nat.card H := by
        rcases exists_sylow_model hK.hasQDOrWreathedSylow S with ⟨n, hn, ⟨f⟩⟩ |
          ⟨n, hn, ⟨e⟩⟩
        · exact four_dvd_card_of_semidihedral hn S f
        · exact four_dvd_card_of_wreathed hn S e
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr
        (two_dvd_card_of_index_two hK.index_eq_two h4))

theorem fusion_class_cases (hH : HasQDOrWreathedSylow H ∨ HasDihedralSylowTwo H) :
    IsQDGroup H ∨ IsQGroup H ∨ IsDGroup H ∨ HasNormalPComplement 2 H := by
  rcases hH with hH | hD
  · obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
    rcases exists_sylow_model hH S with ⟨n, hn, ⟨f⟩⟩ | ⟨n, hn, ⟨e⟩⟩
    · rcases semidihedral_two_fusion_classification hn S f with h1 | h2 | h3 | h4
      · exact Or.inl (IsQDGroup.of_semidihedralFusionQD hn S f h1)
      · exact Or.inr (Or.inl (isQGroup_of_semidihedralFusionQ hn S f h2))
      · exact Or.inr (Or.inr (Or.inl (isDGroup_of_semidihedralFusionD hn S f h3)))
      · exact Or.inr (Or.inr (Or.inr h4.normalComplement))
    · rcases wreathed_two_fusion_classification hn S e with h1 | h2 | h3 | h4
      · exact Or.inl (IsQDGroup.of_wreathedFusionQD hn S e h1)
      · exact Or.inr (Or.inl (isQGroup_of_wreathedFusionQ hn S e h2))
      · exact Or.inr (Or.inr (Or.inl (isDGroup_of_wreathedFusionD hn S e h3)))
      · exact Or.inr (Or.inr (Or.inr h4.normalComplement))
  · by_cases hC : HasNormalPComplement 2 H
    · exact Or.inr (Or.inr (Or.inr hC))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨hD, hC⟩)))

end General

end CFSG.QuasiDihedralFusion
