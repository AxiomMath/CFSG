module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213CaseB
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.Lemma213Signalizer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.Lemma213

open CFSG CFSG.LocalCores CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
  CFSG.LocalAnalysis.RankThreeTheoremC CFSG.ComponentClassification.OuterAutomorphisms Subgroup

theorem fixes_of_normalizes_conj {p : ℕ} (hp : p.Prime) {S : Type} [Group S] [Finite S]
    [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (hdvd : p ∣ Nat.card S)
    (hinv : InvolvedInSymm p S) {x : S} (hx : orderOf x = p) (A : Subgroup (MulAut S))
    (hAcop : p.Coprime (Nat.card A))
    (hAnorm : MulAut.conj x ∈ normalizer (A : Set (MulAut S))) : ∀ a ∈ A, a x = x := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨V, f, hf⟩ := hinv
  have hfinj := injective_of_surjective_perm hp hdvd f hf
  let e : V ≃* S := MulEquiv.ofBijective f ⟨hfinj, hf⟩
  have hconjinj : Function.Injective (MulAut.conj : S →* MulAut S) :=
    conj_injective_of_center_eq_bot (center_eq_bot_of_simple hnab)
  let A' : Subgroup S := A.comap (MulAut.conj : S →* MulAut S)
  have hA'cop : p.Coprime (Nat.card A') := by
    have h1 : Nat.card A' ∣ Nat.card A := Subgroup.card_dvd_of_injective
      ((MulAut.conj : S →* MulAut S).subgroupComap A) (fun a b hab => Subtype.ext (hconjinj
        (congrArg Subtype.val hab)))
    exact hAcop.coprime_dvd_right h1
  have hxA' : x ∈ normalizer (A' : Set S) := by
    rw [mem_normalizer_iff]
    intro a
    have hconj : (MulAut.conj (x * a * x⁻¹) : MulAut S) =
        MulAut.conj x * MulAut.conj a * (MulAut.conj x)⁻¹ := by
      simp [map_mul, map_inv]
    show MulAut.conj a ∈ A ↔ MulAut.conj (x * a * x⁻¹) ∈ A
    rw [hconj]
    exact mem_normalizer_iff.1 hAnorm (MulAut.conj a)
  have hA'bot : A' = ⊥ := by
    let B : Subgroup (Equiv.Perm (Fin p)) := (A'.map e.symm.toMonoidHom).map V.subtype
    have hc'ord : orderOf (((e.symm x : V)) : Equiv.Perm (Fin p)) = p := by
      rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      exact hx
    have hc'1 : (((e.symm x : V)) : Equiv.Perm (Fin p)) ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hc'ord
      exact hp.one_lt.ne hc'ord
    have hc'p : (((e.symm x : V)) : Equiv.Perm (Fin p)) ^ p = 1 := by
      have h1 := pow_orderOf_eq_one (((e.symm x : V)) : Equiv.Perm (Fin p))
      rwa [hc'ord] at h1
    have hBcop : p.Coprime (Nat.card B) := by
      rw [Subgroup.card_map_of_injective V.subtype_injective,
        Subgroup.card_map_of_injective e.symm.injective]
      exact hA'cop
    have hBnorm : (((e.symm x : V)) : Equiv.Perm (Fin p)) ∈ normalizer (B : Set _) := by
      have h1 : e.symm.toMonoidHom x ∈
          normalizer ((A'.map e.symm.toMonoidHom : Subgroup V) : Set V) :=
        Subgroup.le_normalizer_map e.symm.toMonoidHom ⟨x, hxA', rfl⟩
      exact Subgroup.le_normalizer_map V.subtype ⟨e.symm x, h1, rfl⟩
    have hB := eq_bot_of_pCycle_mem_normalizer hp (Fintype.card_fin p) hc'1 hc'p hBcop hBnorm
    have h2 := (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).1 hB
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).1 h2
  intro a ha
  have h1 : MulAut.conj x * a⁻¹ * (MulAut.conj x)⁻¹ ∈ A :=
    (mem_normalizer_iff.1 hAnorm a⁻¹).1 (A.inv_mem ha)
  have h2 : a * (MulAut.conj x * a⁻¹ * (MulAut.conj x)⁻¹) ∈ A := A.mul_mem ha h1
  have h3 : a * (MulAut.conj x * a⁻¹ * (MulAut.conj x)⁻¹) = MulAut.conj (a x * x⁻¹) := by
    refine MulEquiv.ext fun s => ?_
    simp [MulAut.conj_apply]
  have h4 : a x * x⁻¹ ∈ A' := by
    show MulAut.conj (a x * x⁻¹) ∈ A
    rw [← h3]
    exact h2
  rw [hA'bot, Subgroup.mem_bot] at h4
  exact mul_inv_eq_one.1 h4

variable {K : Type} [Group K] [Finite K] {n p : ℕ} {P : Sylow p K} {z : K} {D : Subgroup K}

namespace Red

theorem caseB_central (R : Red n p K P z D)
    (hOut : ∀ C : ComponentIndex K, Group.IsSolvable (Outer C.1))
    (hemb : CentralizerSectionEmbeds p D z) {w : K} (hw : w ∈ D) {C₀ : ComponentIndex K}
    (hmove : w • C₀ ≠ C₀) :
    ∀ T : Subgroup K, p.Coprime (Nat.card T) → D ≤ normalizer (T : Set K) →
      T ≤ centralizer ({z} : Set K) := by
  intro T hT hDT
  haveI := R.fact
  have hcard := R.card_comp hw hmove
  have hTY : T ≤ (actHom K).ker := by
    have hbot : T.map (actHom K) = ⊥ := by
      refine eq_bot_of_pCycle_mem_normalizer R.prime hcard (c := actHom K w) ?_ ?_ ?_ ?_
      · intro h1
        exact hmove (mem_ker_actHom.1 (MonoidHom.mem_ker.2 h1) C₀)
      · rw [← map_pow, R.conf.elem.2 w hw, map_one]
      · exact hT.coprime_dvd_right (Subgroup.card_map_dvd T (actHom K))
      · exact Subgroup.le_normalizer_map (actHom K) ⟨w, hDT hw, rfl⟩
    intro t ht
    have : actHom K t ∈ T.map (actHom K) := Subgroup.mem_map_of_mem _ ht
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  have hfix : ∀ t ∈ T, ∀ C : ComponentIndex K, t * R.zc C * t⁻¹ = R.zc C := by
    intro t ht C
    obtain ⟨hsimple, hnonab⟩ := R.isSimpleGroup_comp C
    haveI := hsimple
    have hTN : T ≤ normalizer (C.1 : Set K) := hTY.trans (ker_actHom_le_normalizer C)
    let H : Subgroup (normalizer (C.1 : Set K)) := T.subgroupOf (normalizer (C.1 : Set K))
    let A : Subgroup (MulAut C.1) := H.map C.1.normalizerMonoidHom
    have hAcop : p.Coprime (Nat.card A) := by
      have h1 : Nat.card A ∣ Nat.card H := Subgroup.card_map_dvd H _
      have h2 : Nat.card H = Nat.card T :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv
      rw [h2] at h1
      exact hT.coprime_dvd_right h1
    let x : C.1 := ⟨R.zc C, R.zc_mem C⟩
    have hx : orderOf x = p :=
      orderOf_eq_prime (Subtype.ext (R.zc_pow C)) (fun h => R.zc_ne_one C (congrArg Subtype.val h))
    let z' : normalizer (C.1 : Set K) := ⟨z, R.z_mem_normalizer C⟩
    have hz'ρ : C.1.normalizerMonoidHom z' = MulAut.conj x := by
      refine MulEquiv.ext fun c => Subtype.ext ?_
      exact R.z_conj_eq C c.2
    have hz'N : z' ∈ normalizer (H : Set (normalizer (C.1 : Set K))) := by
      have h1 : (normalizer (T : Set K)).subgroupOf (normalizer (C.1 : Set K)) =
          normalizer (H : Set (normalizer (C.1 : Set K))) := Subgroup.subgroupOf_normalizer_eq hTN
      rw [← h1]
      exact Subgroup.mem_subgroupOf.2 (hDT R.conf.mem)
    have hAnorm : MulAut.conj x ∈ normalizer (A : Set (MulAut C.1)) := by
      rw [← hz'ρ]
      exact Subgroup.le_normalizer_map C.1.normalizerMonoidHom ⟨z', hz'N, rfl⟩
    have hfixA := fixes_of_normalizes_conj R.prime hnonab (dvd_card_comp R.core C)
      (R.involvedInSymm_comp hOut hemb hw hmove C) hx A hAcop hAnorm
    have htA : C.1.normalizerMonoidHom ⟨t, hTN ht⟩ ∈ A :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ht)
    exact congrArg (fun a : C.1 => (a : K)) (hfixA _ htA)
  intro t ht
  rw [mem_centralizer_singleton_iff]
  have hzt : t * z * t⁻¹ = z := by
    refine π_ext (hZ := R.hZ) (conj_mem_layer t R.hzL) R.hzL fun C => ?_
    have h1 := π_conj (hZ := R.hZ) t C R.hzL
    have ec : cjComp t C = C := mem_ker_actHom.1 (hTY ht) C
    rw [ec] at h1
    exact h1.trans (hfix t ht C)
  exact mul_inv_eq_iff_eq_mul.1 hzt

end Red

end CFSG.LocalAnalysis.RankFourTheoremC.Lemma213
