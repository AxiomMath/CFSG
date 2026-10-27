module

public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.U6RealCore
public import CFSG.HardMathSupport.Dickson.Sec6.I1431Fam.PsuBFam

public section

namespace CFSG.HardMathSupport.Dickson.Sec6.I1431

open CFSG CFSG.Open CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.RankThree.PartTwo.KFacts
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Dickson.Sec6.I923

theorem u6r_desc_map_fixSub {Y : Type*} [Group Y] {η ε : MulAut Y} (h : ε * η = η * ε) :
    (Lemma510Ns.fixSub η).map ε.toMonoidHom = Lemma510Ns.fixSub η := by
  ext y
  simp only [Subgroup.mem_map, Lemma510Ns.mem_fixSub, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have h1 : (ε * η) x = (η * ε) x := by rw [h]
    simp only [MulAut.mul_apply] at h1
    rw [← h1, hx]
  · intro hy
    refine ⟨ε.symm y, ?_, by simp⟩
    have h1 : (ε * η) (ε.symm y) = (η * ε) (ε.symm y) := by rw [h]
    simp only [MulAut.mul_apply, MulEquiv.apply_symm_apply, hy] at h1
    have h2 := congrArg ε.symm h1
    simpa using h2

theorem u6r_desc_type {Y P : Type} [Group Y] [Finite Y] [Group P] [Finite P] (π : Y →* P)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center Y) (α : MulAut Y)
    (β : MulAut P) (hαβ : ∀ y, π (α y) = β (π y)) {H : Subgroup Y}
    (hH : GLAPComponent 3 (fixSubgroup α) H) {r : ℕ} (hT : IsTypeL2 r (barOf 3 (H.map π))) :
    IsTypeL2 r (barOf 3 H) := by
  have hq := CaseThreeNs.isQuasisimple_barOf_of_glaPComponent Nat.prime_three hH
  exact (isTypeL2_congr_of_central (Group.isPerfect_def.2 hq.1) (barMap π H)
    (barMap_surjective π H) (barMap_ker_le_center π hπ hker α β hαβ hH)).2 hT

theorem u6r_concl_of_descend {V : InndiagVocab} {Y P : Type} [Group Y] [Finite Y] [Group P]
    [Finite P] {Â : Subgroup (MulAut Y)} {ξ : MulAut Y} {J : Subgroup Y} {q : ℕ}
    (c : Y1431Cfg V Y Â ξ J q) (e : (Y ⧸ Subgroup.center Y) ≃* P) {r0 : ℕ} (hr0 : r0 ^ 3 = q)
    (hpsu : IsPSUn 6 r0 (Y ⧸ Subgroup.center Y))
    (hlayer : ∀ J' : Subgroup P, GLAPComponent 3 (Lemma510Ns.fixSub (descendHom e ξ)) J' →
      J' = J.map (descendProj e))
    (htriple : ∃ η ∈ Â.map (descendHom e), η ≠ 1 ∧ ∃ H₁ H₂ H₃ : Subgroup P,
      (∀ H : Subgroup P, GLAPComponent 3 (Lemma510Ns.fixSub η) H ↔ (H = H₁ ∨ H = H₂ ∨ H = H₃)) ∧
      H₁ ≠ H₂ ∧ H₁ ≠ H₃ ∧ H₂ ≠ H₃ ∧
      (∀ H : Subgroup P, (H = H₁ ∨ H = H₂ ∨ H = H₃) → IsTypeL2 r0 (barOf 3 H)) ∧
      ∀ H H' : Subgroup P, (H = H₁ ∨ H = H₂ ∨ H = H₃) → (H' = H₁ ∨ H' = H₂ ∨ H' = H₃) →
        ∃ e' ∈ Â.map (descendHom e), H.map e'.toMonoidHom = H') :
    Y1431Concl Y Â ξ J q := by
  set π := descendProj e with hπdef
  have hπ : Function.Surjective π := descendProj_surjective e
  have hker : π.ker ≤ Subgroup.center Y := descendProj_ker_le e
  obtain ⟨ηP, hηP, hηP1, H₁, H₂, H₃, hiff, h12, h13, h23, htype, htrans⟩ := htriple
  obtain ⟨η, hη, rfl⟩ := Subgroup.mem_map.1 hηP
  have hη1 : η ≠ 1 := by
    rintro rfl
    exact hηP1 (map_one _)
  have hcompat := descendHom_compat e η
  have hdown : ∀ H : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub η) H →
      GLAPComponent 3 (Lemma510Ns.fixSub (descendHom e η)) (H.map π) := fun H hH =>
    glaPComponent_map_fixSubgroup π hker η (descendHom e η) hcompat hπ Nat.prime_three hH
  have hup : ∀ H : Subgroup P, GLAPComponent 3 (Lemma510Ns.fixSub (descendHom e η)) H →
      ∃ H' : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub η) H' ∧ H'.map π = H :=
    fun H hH =>
      exists_glaPComponent_map_fixSubgroup π hker η (descendHom e η) hcompat hπ Nat.prime_three hH
  have huniq : ∀ {H H' : Subgroup Y}, GLAPComponent 3 (Lemma510Ns.fixSub η) H →
      GLAPComponent 3 (Lemma510Ns.fixSub η) H' → H.map π = H'.map π → H = H' :=
    fun hH hH' h => CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq_of_ker_le_center π
      hker hH hH' h
  obtain ⟨H₁', hH₁', hm₁⟩ := hup H₁ ((hiff H₁).2 (Or.inl rfl))
  obtain ⟨H₂', hH₂', hm₂⟩ := hup H₂ ((hiff H₂).2 (Or.inr (Or.inl rfl)))
  obtain ⟨H₃', hH₃', hm₃⟩ := hup H₃ ((hiff H₃).2 (Or.inr (Or.inr rfl)))
  have hiff' : ∀ H : Subgroup Y, GLAPComponent 3 (Lemma510Ns.fixSub η) H ↔
      (H = H₁' ∨ H = H₂' ∨ H = H₃') := by
    intro H
    constructor
    · intro hH
      rcases (hiff _).1 (hdown H hH) with h | h | h
      · exact Or.inl (huniq hH hH₁' (h.trans hm₁.symm))
      · exact Or.inr (Or.inl (huniq hH hH₂' (h.trans hm₂.symm)))
      · exact Or.inr (Or.inr (huniq hH hH₃' (h.trans hm₃.symm)))
    · rintro (rfl | rfl | rfl)
      · exact hH₁'
      · exact hH₂'
      · exact hH₃'
  have hmapin : ∀ H : Subgroup Y, (H = H₁' ∨ H = H₂' ∨ H = H₃') →
      (H.map π = H₁ ∨ H.map π = H₂ ∨ H.map π = H₃) := fun H hH =>
    (hiff _).1 (hdown H ((hiff' H).2 hH))
  refine ⟨⟨r0, hr0, hpsu⟩, ?_, ⟨η, hη, hη1, r0, hr0, H₁', H₂', H₃', hiff', ?_, ?_, ?_, ?_, ?_⟩⟩
  ·
    intro J' hJ'
    exact CFSG.LocalAnalysis.GLTheoremA.glaPComponent_eq_of_map_eq_of_ker_le_center π hker hJ'
      c.comp (hlayer _ (glaPComponent_map_fixSubgroup π hker ξ (descendHom e ξ)
        (descendHom_compat e ξ) hπ Nat.prime_three hJ'))
  · intro h
    exact h12 (by rw [← hm₁, ← hm₂, h])
  · intro h
    exact h13 (by rw [← hm₁, ← hm₃, h])
  · intro h
    exact h23 (by rw [← hm₂, ← hm₃, h])
  · intro H hH
    exact u6r_desc_type π hπ hker η (descendHom e η) hcompat ((hiff' H).2 hH)
      (htype _ (hmapin H hH))
  · intro H H' hH hH'
    obtain ⟨e', he', hmap⟩ := htrans _ _ (hmapin H hH) (hmapin H' hH')
    obtain ⟨ε, hε, rfl⟩ := Subgroup.mem_map.1 he'
    refine ⟨ε, hε, huniq ?_ ((hiff' H').2 hH') ?_⟩
    · have hcomm : ε * η = η * ε :=
        congrArg Subtype.val (c.elemAbelian.1.is_comm.comm ⟨ε, hε⟩ ⟨η, hη⟩)
      have hk : Nat.Coprime 3 (Nat.card ↥(Lemma510Ns.fixSub η ⊓ ε.toMonoidHom.ker)) := by
        rw [show ε.toMonoidHom.ker = ⊥ from (MonoidHom.ker_eq_bot_iff _).2 ε.injective,
          inf_bot_eq, Subgroup.card_bot]
        exact Nat.coprime_one_right 3
      have h1 := glaPComponent_map Nat.prime_three ε.toMonoidHom hk ((hiff' H).2 hH)
      rwa [u6r_desc_map_fixSub hcomm] at h1
    · rw [Subgroup.map_map, show π.comp ε.toMonoidHom = (descendHom e ε).toMonoidHom.comp π from
        MonoidHom.ext (descendHom_compat e ε), ← Subgroup.map_map, hmap]

theorem y1431_lieRest_u6Real (hO : CFSG.ComponentClassification.CatLeaf.LieOrderFormulasInput) :
    Y1431LieRestAt FamU6Real := by
  intro Y _ _ Â ξ J q c t n p f hadm ht hF hm q0 hq0 hqq
  obtain ⟨rfl, rfl, rfl, hf⟩ := hF
  obtain ⟨K, _, h, ⟨e0⟩⟩ := exists_psu_model hadm hm
  haveI := h.finite
  haveI : Finite (GL (Fin 6) K) :=
    Finite.of_injective (fun g : GL (Fin 6) K => (g : Matrix (Fin 6) (Fin 6) K)) Units.val_injective
  haveI : Finite (primeFormP h (idGram K 6)) := inferInstance
  have cS := c.descend e0
  have hA : ∀ a ∈ Â.map (descendHom e0),
      ∃ B : primeFormUnitary h (idGram K 6), primeFormConjHom h (idGram K 6) B = a := by
    rintro _ ⟨a', ha', rfl⟩
    have h1 : MulAut.congr e0 (centerDescend Y a') ∈ innAutDerived (primeFormP h (idGram K 6)) :=
      (mem_innAutDerived_congr e0).2 (centerDescend_mem_innAutDerived (c.mem_innAutDerived ha'))
    exact t6psub_innAutDerived_le h (by norm_num) (fun hc => absurd hc.1 (by norm_num)) h1
  have h64 : 64 ≤ q := by
    have : 4 ^ 3 ≤ q0 ^ 3 := Nat.pow_le_pow_left hq0 3
    omega
  obtain ⟨hqr, hlayer, htriple⟩ := u6r_core hO h hf cS h64 hA
  have hpsu : IsPSUn 6 (2 ^ f) (Y ⧸ Subgroup.center Y) := by
    obtain ⟨-, K', hK', hK'f, hcard, he⟩ :=
      (CFSG.RankThree.PartOne.Sec66T.lieModel_classical_iff (by decide)).mp hm
    exact ⟨K', hK', hK'f, hcard, he⟩
  exact u6r_concl_of_descend c e0 hqr.symm hpsu hlayer htriple

end CFSG.HardMathSupport.Dickson.Sec6.I1431
