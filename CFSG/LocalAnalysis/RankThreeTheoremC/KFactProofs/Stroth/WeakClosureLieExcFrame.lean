module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtExact

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LocalTwo
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar
  CFSG.LieType.SeitzGeneration CFSG.RankThree.Lattice Polynomial
  CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped Matrix

set_option linter.unusedSectionVars false

theorem exists_untw_frame {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (w : WeylGroup τ)
    (hperf : commutator ↥(adjointGroup τ K) = ⊤) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : IsAlgClosure K L) (D : LangDatum τ L)
      (Fr : L →+* L), (∀ c, Fr c = c ^ Nat.card K) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
      D.q = Nat.card K ∧ D.n = canonicalRep (coxeterSystem τ) L w ∧
      ((Nat.card K : ℕ) : L) = 0 ∧
      LangDescent D p ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  haveI : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  haveI : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let D : LangDatum τ L := LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0
  have hD : D.Φ = Units.map (entrywiseHom Fr) := rfl
  have hd := langDescent_untw (K := K) (L := L) d hτ hFr D hD hp hp3 hperf
  have hK0 : ((Nat.card K : ℕ) : L) = 0 := by
    rw [← map_natCast (algebraMap K L), Nat.card_eq_fintype_card, FiniteField.cast_card_eq_zero K,
      map_zero]
  exact ⟨L, inferInstance, inferInstance, inferInstance, D, Fr, hFr, hD, rfl, rfl, hK0, hd⟩

theorem exists_sylow_of_hord {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] (D : LangDatum τ L)
    {p : ℕ} (hp : p.Prime) {C : Type} [Group C] (ι : C →* ModGL τ L)
    (hι : Function.Injective ι) (hd : LangDescent D p ι)
    (hord : ∃ H : Subgroup (ModGL τ L), H ≤ D.torus ∧
      (Nat.card C).factorization p ≤ (Nat.card H).factorization p) :
    ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hfm := hd.finite_model
  have hTM := D.torus_le_model
  haveI hTfin : Finite D.torus :=
    Finite.of_injective (Subgroup.inclusion hTM) (Subgroup.inclusion_injective hTM)
  have hΓfin : Finite D.Γ :=
    Finite.of_injective (Subgroup.inclusion hd.Γ_le_model) (Subgroup.inclusion_injective _)
  obtain ⟨H, hHT, hCH⟩ := hord
  have hord' : (Nat.card C).factorization p ≤ (Nat.card D.torus).factorization p := by
    refine hCH.trans ?_
    haveI : Finite H :=
      Finite.of_injective (Subgroup.inclusion hHT) (Subgroup.inclusion_injective hHT)
    have hdvd : Nat.card H ∣ Nat.card D.torus := Subgroup.card_dvd_of_le hHT
    exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd p
  obtain ⟨P0⟩ : Nonempty (Sylow p D.torus) := inferInstance
  set P1 : Subgroup (ModGL τ L) := (P0 : Subgroup D.torus).map D.torus.subtype with hP1
  have hP1T : P1 ≤ D.torus := Subgroup.map_subtype_le _
  have hP1p : IsPGroup p P1 := P0.isPGroup'.map _
  have hP1Γ : P1 ≤ D.Γ := hd.pgroup_le_Γ P1 (hP1T.trans hTM) hP1p
  have hP1card : Nat.card P1 = p ^ (Nat.card D.torus).factorization p := by
    rw [hP1, Subgroup.card_map_of_injective D.torus.subtype_injective, Sylow.card_eq_multiplicity]
  set P2 : Subgroup D.Γ := P1.subgroupOf D.Γ with hP2
  have hP2card : Nat.card P2 = Nat.card P1 := by
    rw [← Subgroup.card_map_of_injective D.Γ.subtype_injective, hP2,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hP1Γ]
  have hΓcard : Nat.card D.Γ = Nat.card C := (Nat.card_congr (hd.mulEquiv hι).toEquiv).symm
  have hle : (Nat.card D.torus).factorization p ≤ (Nat.card D.Γ).factorization p := by
    have hdvd : p ^ (Nat.card D.torus).factorization p ∣ Nat.card D.Γ := by
      rw [← hP1card, ← hP2card]
      exact Subgroup.card_subgroup_dvd_card P2
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 hdvd
  have hcard : Nat.card P2 = p ^ (Nat.card D.Γ).factorization p := by
    rw [hP2card, hP1card]
    congr 1
    rw [hΓcard]
    exact le_antisymm (hΓcard ▸ hle) hord'
  refine ⟨Sylow.ofCard P2 hcard, ?_⟩
  rw [Sylow.coe_ofCard]
  intro x hx
  exact Subgroup.mem_subgroupOf.2 (hP1T hx)

theorem exists_exact_frame_sylow {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) (F : Type) [Field F] [Finite F]
    {p : ℕ} (hp : p.Prime) (w : WeylGroup τ) (hperf : commutator ↥(adjointGroup τ F) = ⊤)
    (hord : ∀ {L : Type} [Field L] [Algebra F L] [IsAlgClosure F L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card F) →
      ∃ H : Subgroup (ModGL τ L), H ≤
          twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) ∧
        (Nat.card (adjointGroup τ F)).factorization p ≤ (Nat.card H).factorization p) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (D : LangDatum τ L),
      (∀ c, Fr c = c ^ Nat.card F) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
      D.n = canonicalRep (coxeterSystem τ) L w ∧ D.model ≤ D.Γ ∧
      Nonempty (adjointGroup τ F ≃* D.Γ) ∧
      ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨L, _, _, _, D, Fr, hFr, hD, hDq, hDn, hK0, hd⟩ :=
    exists_exact_frame (K := F) hτ (p := p) w hperf
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  set ι : adjointGroup τ F →* ModGL τ L :=
    (baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype with hιdef
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hT : D.torus = twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr)) := by
    show twistedTorusOf D.n D.Φ = _
    rw [hD, hDn]
  have hord' : ∃ H : Subgroup (ModGL τ L), H ≤ D.torus ∧
      (Nat.card (adjointGroup τ F)).factorization p ≤ (Nat.card H).factorization p := by
    rw [hT]
    exact hord Fr hFr
  have hsyl := exists_sylow_of_hord D hp ι hι hd hord'
  have hex := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices τ hτ F L Fr
    hFr).1
  have hfix : D.fix = (adjointGroup τ F).map (baseChangeGL (algebraMap F L)) := by
    rw [← hex]
    ext x
    rw [LangDatum.mem_fix, hD]
    rfl
  have hrange : ι.range = (adjointGroup τ F).map (baseChangeGL (algebraMap F L)) := by
    rw [hιdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hMΓ : D.model ≤ D.Γ := by
    rw [LangDescent.model_eq D, hd.Γ_eq, hfix, ← hrange]
  exact ⟨L, inferInstance, inferInstance, Fr, D, hFr, hD, hDn, hMΓ, ⟨hd.mulEquiv hι⟩, hsyl⟩

theorem exists_exact_frame_sylow_of_S {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) (F : Type) [Field F]
    [Finite F] {p : ℕ} (hp : p.Prime) (w : WeylGroup τ)
    (hperf : commutator ↥(adjointGroup τ F) = ⊤)
    (hS : ∀ {L : Type} [Field L] [Algebra F L] [IsAlgClosure F L] (Fr : L →+* L),
      (∀ c, Fr c = c ^ Nat.card F) → ∀ g0 : ModGL τ L, g0 ∈ adjointGroup τ L →
      Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ) L w →
      ∃ S : Sylow p (adjointGroup τ F), ∀ x ∈ (S : Subgroup (adjointGroup τ F)),
        g0⁻¹ * baseChangeGL (algebraMap F L) (x : ModGL τ F) * g0 ∈
          twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr))) :
    ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (Fr : L →+* L) (D : LangDatum τ L),
      (∀ c, Fr c = c ^ Nat.card F) ∧ D.Φ = Units.map (entrywiseHom Fr) ∧
      D.n = canonicalRep (coxeterSystem τ) L w ∧ D.model ≤ D.Γ ∧
      Nonempty (adjointGroup τ F ≃* D.Γ) ∧
      ∃ S₀ : Sylow p D.Γ, (S₀ : Subgroup D.Γ) ≤ D.torus.subgroupOf D.Γ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (ModGL τ F) := finite_modGL
  obtain ⟨L, _, _, _, D, Fr, hFr, hD, hDq, hDn, hK0, hd⟩ :=
    exists_exact_frame (K := F) hτ (p := p) w hperf
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed F
  set ι : adjointGroup τ F →* ModGL τ L :=
    (baseChangeGL (algebraMap F L)).comp (adjointGroup τ F).subtype with hιdef
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hlang : Units.map (entrywiseHom Fr) D.g0 = D.g0 * canonicalRep (coxeterSystem τ) L w := by
    have := D.lang
    rwa [hD, hDn] at this
  obtain ⟨S, hn⟩ := hS Fr hFr D.g0 D.g0_mem hlang
  have hsyl := exists_sylow_Γ_of_conj hp hι hd S (fun x hx => by
    have h1 := hn x hx
    show _ ∈ twistedTorusOf D.n D.Φ
    rw [hD, hDn]
    exact h1)
  have hex := (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices τ hτ F L Fr
    hFr).1
  have hfix : D.fix = (adjointGroup τ F).map (baseChangeGL (algebraMap F L)) := by
    rw [← hex]
    ext x
    rw [LangDatum.mem_fix, hD]
    rfl
  have hrange : ι.range = (adjointGroup τ F).map (baseChangeGL (algebraMap F L)) := by
    rw [hιdef, MonoidHom.range_comp, Subgroup.range_subtype]
  have hMΓ : D.model ≤ D.Γ := by
    rw [LangDescent.model_eq D, hd.Γ_eq, hfix, ← hrange]
  exact ⟨L, inferInstance, inferInstance, Fr, D, hFr, hD, hDn, hMΓ, ⟨hd.mulEquiv hι⟩, hsyl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross.Untw
