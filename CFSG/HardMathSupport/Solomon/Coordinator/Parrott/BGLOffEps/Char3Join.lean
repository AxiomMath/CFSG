module

public import CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3Core
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUMain
public import CFSG.HardMathSupport.Solomon.Coordinator.BGLUTMain

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.ComponentInitial
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
  CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54Ns
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma514CoverNs Matrix
  CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

section Certified


section Matrix

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Solomon.Coordinator.BGL

theorem su3SubfieldJoin_any {F : Type} [Field F] [Finite F] {q : ℕ} (hcard : Nat.card F = q ^ 2)
    (hq8 : q ≠ 8) {σ : F ≃+* F} (hσ : orderOf σ = 3) (h : GL (Fin 3) F)
    (hunit : ((h : Matrix (Fin 3) (Fin 3) F).map (· ^ q))ᵀ * (h : Matrix (Fin 3) (Fin 3) F) = 1)
    (hnot : ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * (h : Matrix (Fin 3) (Fin 3) F) i j) =
      c * (h : Matrix (Fin 3) (Fin 3) F) i j) :
    StatedSU 3 q F ≤ (StatedSU 3 q F ⊓ fixGL σ) ⊔
      (StatedSU 3 q F ⊓ fixGL σ).map (MulAut.conj h).toMonoidHom := by
  classical
  obtain ⟨p, hp⟩ := CharP.exists F
  have : Fact p.Prime := ⟨CharP.char_is_prime F p⟩
  have := Fintype.ofFinite F
  obtain ⟨n, hpn, hcn⟩ := FiniteField.card F p
  have h1 : q ^ 2 = p ^ (n : ℕ) := by
    rw [← hcard, Nat.card_eq_fintype_card]; exact hcn
  have h2 : q ∣ p ^ (n : ℕ) := ⟨q, by rw [← h1]; ring⟩
  obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpn).1 h2
  subst hf
  have hF : Nat.card F = (p ^ f) ^ 2 := hcard
  set ι := unitaryInvolution F p f with hιdef
  have hι : IsUnitaryInvolution ι := isUnitaryInvolution_unitaryInvolution hF
  have hιx : ∀ x, ι x = x ^ p ^ f := fun x => unitaryInvolution_apply F p f x
  have hcomm : ∀ x, σ (ι x) = ι (σ x) := fun x => by rw [hιx, hιx, map_pow]
  have hρ3 : orderOf (σ : RingAut F) = 3 := hσ
  have hcount := galois_counts ι σ hι.invol hι.exists_ne hρ3 hcomm
  have hE : Nat.card (Efix ι) = p ^ f := by
    have := hcount.2.2
    rw [hF] at this
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0)) this.symm
  have FH : FieldHypAny ι σ := ⟨hι, hρ3, hcomm, by rw [hE]; exact hq8⟩
  have hk3 := FH.card_k_ge
  have hq2 : p ^ f ≠ 2 := by
    intro h2'
    have h5 := FH.counts.1
    rw [hE, h2'] at h5
    have h6 : 3 ^ 3 ≤ Nat.card (kfix ι σ) ^ 3 := Nat.pow_le_pow_left hk3 3
    omega
  have h3 : ∃ s : F, s ≠ 0 ∧ ι s * s ≠ 1 := exists_norm_ne_one hF hq2
  have hiso : ∀ x y, herm ι ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ x)
      ((h : Matrix (Fin 3) (Fin 3) F) *ᵥ y) = herm ι x y := by
    intro x y
    rw [herm_mulVec ι]
    have e : conjTr ι (h : Matrix (Fin 3) (Fin 3) F) =
        ((h : Matrix (Fin 3) (Fin 3) F).map (· ^ p ^ f))ᵀ := by
      unfold conjTr
      congr 2
    rw [e, hunit, Matrix.one_mulVec]
  have hGeq : CFSG.Open.StatedSU 3 (p ^ f) F = SUid ι 3 := (SUid_eq_statedSU hF 3).symm
  rw [hGeq]
  let H : Subgroup (SUid ι 3) :=
    ((SUid ι 3 ⊓ fixGL σ) ⊔ (SUid ι 3 ⊓ fixGL σ).map (MulAut.conj h).toMonoidHom).comap
      (SUid ι 3).subtype
  have hrat : ∀ g : SUid ι 3, RatM σ ((g.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →
      g ∈ H := by
    intro g hg
    refine Subgroup.mem_sup_left ?_
    exact Subgroup.mem_inf.mpr ⟨g.2, (mem_fixGL_iff σ _).mpr hg⟩
  have hconj : ∀ g g' : SUid ι 3, RatM σ ((g.1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) →
      (g'.1 : GL (Fin 3) F) = h * g.1 * h⁻¹ → g' ∈ H := by
    intro g g' hg hg'
    refine Subgroup.mem_sup_right ?_
    refine ⟨g.1, Subgroup.mem_inf.mpr ⟨g.2, (mem_fixGL_iff σ _).mpr hg⟩, ?_⟩
    exact hg'.symm
  have hH : H = ⊤ :=
    su3_core_any hι h3 FH.uctx FH.exists_u FH.exists_ω (FieldHyp.kE ι σ)
      (fun e => FieldHyp.mem_kE e) FH.hcard FH.hk2 FH.span h hiso hnot H hrat hconj
  intro g hg
  have : (⟨g, hg⟩ : SUid ι 3) ∈ H := by rw [hH]; trivial
  exact this

end Matrix

variable {p f : ℕ} {F : Type} [Field F] (hF : UnitaryFieldData p f F)

theorem bglu_model_join_any (hq8 : p ^ f ≠ 8) {σ : F ≃+* F} (hσ : orderOf σ = 3)
    (H : unitaryIsom3 hF)
    (hnot : ¬ ∃ c : F, c ≠ 0 ∧ ∀ i j, σ (c * ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) =
      c * ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) i j) :
    bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom = ⊤ := by
  have := hF.finite
  have hHu : (((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).map (· ^ (p ^ f)))ᵀ *
      ((H : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    have h1 := H.2
    rw [mem_unitaryIsom3] at h1
    have hb : (⇑hF.bar : F → F) = (· ^ (p ^ f)) := funext fun c => hF.bar_apply c
    rw [← hb]
    exact h1
  have hc := su3SubfieldJoin_any hF.card_eq_sq hq8 hσ (H : GL (Fin 3) F) hHu hnot
  set W : Subgroup (unitarySU p f F 3) :=
    (bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom).comap (unitaryProj hF 3)
    with hW
  have h1 : StatedSU 3 (p ^ f) F ⊓ BGL.fixGL σ ≤ W.map (unitarySU p f F 3).subtype := by
    intro s hs
    refine ⟨⟨s, hs.1⟩, ?_, rfl⟩
    change unitaryProj hF 3 ⟨s, hs.1⟩ ∈
      bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom
    exact Subgroup.mem_sup_left
      (mem_bgluSub.2 ⟨⟨s, hs.1⟩, (bglu_mem_fixGL_iff σ s).1 hs.2, rfl⟩)
  have h2 : (StatedSU 3 (p ^ f) F ⊓ BGL.fixGL σ).map
      (MulAut.conj (H : GL (Fin 3) F)).toMonoidHom ≤ W.map (unitarySU p f F 3).subtype := by
    rintro _ ⟨s, hs, rfl⟩
    refine ⟨suConj hF H ⟨s, hs.1⟩, ?_, rfl⟩
    change unitaryProj hF 3 (suConj hF H ⟨s, hs.1⟩) ∈
      bgluSub hF σ ⊔ (bgluSub hF σ).map (psuConj hF H).toMonoidHom
    have hmem : unitaryProj hF 3 ⟨s, hs.1⟩ ∈ bgluSub hF σ :=
      mem_bgluSub.2 ⟨⟨s, hs.1⟩, (bglu_mem_fixGL_iff σ s).1 hs.2, rfl⟩
    exact Subgroup.mem_sup_right ⟨_, hmem, rfl⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨g, rfl⟩ := unitaryProj_surjective hF 3 x
  obtain ⟨g', hg', hgg'⟩ := sup_le h1 h2 (hc g.2)
  have hg : g' = g := Subtype.ext hgg'
  rw [← hg]
  exact hg'

theorem bglu_pair_generation_any {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (hU : ∃ (F : Type) (_ : Field F) (_ : Finite F) (q : ℕ), Nat.card F = q ^ 2 ∧ q ≠ 8 ∧
      Nonempty ((K ⧸ Subgroup.center K) ≃* StatedProj (StatedSU 3 q F)))
    {b x : MulAut K} (hb : IsFieldAutThree b) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hx : IsInnDiagThree x) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hbx : b * x = x * b) :
    (⊤ : Subgroup K) ≤
      GLAPLayer 3 (Lemma512Ns.fixedSub b) ⊔ GLAPLayer 3 (Lemma512Ns.fixedSub (b * x)) := by
  obtain ⟨F0, hF0, hfin0, q, hcard0, hq8, ⟨e0⟩⟩ := hU
  obtain ⟨p, f, F, hFf, hF, η, σ, A, hσ, hq, hηb, hηx⟩ :=
    bglu_data hK ⟨F0, hF0, hfin0, q, hcard0, ⟨e0⟩⟩ hb hb1 hb3 hx
  have hFfin := hF.finite
  have hqe : q = p ^ f := bglu_q_eq ⟨F0, hF0, hfin0, hcard0, ⟨e0⟩⟩
    ⟨F, hFf, hFfin, hF.card_eq_sq, ⟨η.trans (psuO hF)⟩⟩
  subst hqe
  have hcomm : psuConj hF A * psuField hF σ = psuField hF σ * psuConj hF A := by
    have := congrArg (fun z : MulAut K => MulAut.congr η (centerDescend K z)) hbx
    simp only [map_mul] at this
    rw [hηb, hηx] at this
    exact this.symm
  have h3 : psuConj hF A ^ 3 = 1 := by
    rw [← hηx, ← map_pow, ← map_pow, hx3, map_one, map_one]
  have hA1 : psuConj hF A ≠ 1 := by
    intro h1
    apply hx1
    refine eq_one_of_centerDescend_eq_one hK ?_
    apply (MulAut.congr η).injective
    rw [hηx, h1, map_one]
  obtain ⟨H, hh⟩ := bglu_exists_H hF hq hσ A hcomm h3
  have hnot := bglu_not_scalar_fixed hF A H hh hA1
  have hN₁ : BglNSP (psuField hF σ) (bgluSub hF σ) := bgluSub_nsp hF hσ hq8
  have hjoin := bglu_model_join_any hF hq8 hσ H hnot
  have hβ₂ : MulAut.congr η (centerDescend K (b * x)) =
      psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹ := by
    rw [map_mul, map_mul, hηb, hηx, ← hcomm]
    exact hh
  have hN₂ : BglNSP (psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹)
      ((bgluSub hF σ).map (psuConj hF H).toMonoidHom) := by
    refine bglNSP_map ((psuConj hF H).symm) ?_ hN₁
    change (psuConj hF H)⁻¹ * (psuConj hF H * psuField hF σ * (psuConj hF H)⁻¹) *
      (psuConj hF H)⁻¹⁻¹ = _
    group
  have hB₁ := bglNSP_map η hηb hN₁
  have hB₂ := bglNSP_map η hβ₂ hN₂
  have hQ : (bgluSub hF σ).map η.symm.toMonoidHom ⊔
      ((bgluSub hF σ).map (psuConj hF H).toMonoidHom).map η.symm.toMonoidHom = ⊤ := by
    rw [← Subgroup.map_sup, hjoin, Subgroup.map_top_of_surjective _ η.symm.surjective]
  have hK1 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have := hK.1
    rwa [commutator_def] at this
  have key := glaPLayer_fixSubgroup_sup_eq_top_of_perfect (QuotientGroup.mk' (Subgroup.center K))
    (QuotientGroup.ker_mk' _).le (QuotientGroup.mk'_surjective _) hK1 b (b * x)
    (centerDescend K b) (centerDescend K (b * x)) (fun _ => rfl) (fun _ => rfl) Nat.prime_three
    (bglNSP_le_layer hB₁) (bglNSP_le_layer hB₂) hQ
  exact le_of_eq key.symm

end Certified

end CFSG.HardMathSupport.Solomon.Coordinator.Parrott.BGLOffEps.Char3
