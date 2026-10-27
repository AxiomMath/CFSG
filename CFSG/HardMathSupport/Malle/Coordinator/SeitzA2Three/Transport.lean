module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanP1ThreeLieOffCharOuterCube
public import CFSG.LieType.SeitzGeneration.OutdiagScope

public section

namespace CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three

open CFSG.Open CFSG.AGLEmbedding CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

@[expose] def ModelHyperGen {M : Type*} [Group M] (p : ℕ) (B : Subgroup (MulAut M)) : Prop :=
  Subgroup.closure {x : M | ∃ H : Subgroup (MulAut M), H ≤ B ∧ H.relIndex B = p ∧
    ∀ b ∈ H, b x = x} = ⊤

section Transport

variable {Y : Type*} [Group Y] {K : Subgroup Y} [hKn : K.Normal] {M : Type*} [Group M]

@[expose] noncomputable def conjModel (e : K ≃* M) : Y →* MulAut M :=
  (MulAut.congr e).toMonoidHom.comp MulAut.conjNormal

theorem conjModel_apply (e : K ≃* M) (y : Y) (k : K) :
    conjModel e y (e k) = e ⟨y * k * y⁻¹, hKn.conj_mem k k.2 y⟩ := by
  change e ((MulAut.conjNormal y) (e.symm (e k))) = _
  rw [MulEquiv.symm_apply_apply]
  rfl

theorem conjModel_injective (e : K ≃* M) (hC : Subgroup.centralizer (K : Set Y) = ⊥) :
    Function.Injective (conjModel e) := by
  rw [injective_iff_map_eq_one]
  intro y hy
  have hyC : y ∈ Subgroup.centralizer (K : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun φ : MulAut M => φ (e ⟨k, hk⟩)) hy
    simp only [MulAut.one_apply] at h1
    rw [conjModel_apply] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    simp only at h2
    calc k * y = y * k * y⁻¹ * y := by rw [h2]
      _ = y * k := by group
  rw [hC] at hyC
  exact hyC

theorem hyperGen_of_modelHyperGen (e : K ≃* M) (hC : Subgroup.centralizer (K : Set Y) = ⊥)
    {p : ℕ} {E : Subgroup Y} (h : ModelHyperGen p (E.map (conjModel e))) : HyperGen p K E := by
  have hinj := conjModel_injective e hC
  set S : Set K := {k | ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧
    ∀ f ∈ F, f * (k : Y) = (k : Y) * f} with hS
  have himg : {x : M | ∃ H : Subgroup (MulAut M), H ≤ E.map (conjModel e) ∧
      H.relIndex (E.map (conjModel e)) = p ∧ ∀ b ∈ H, b x = x} ⊆ e '' S := by
    rintro x ⟨H, hHB, hHi, hHx⟩
    refine ⟨e.symm x, ⟨E ⊓ H.comap (conjModel e), inf_le_left, ?_, ?_⟩, by simp⟩
    · have hmap : (E ⊓ H.comap (conjModel e)).map (conjModel e) = H := by
        apply le_antisymm
        · rintro _ ⟨y, hy, rfl⟩
          exact hy.2
        · intro b hb
          obtain ⟨y, hyE, rfl⟩ := hHB hb
          exact ⟨y, ⟨hyE, hb⟩, rfl⟩
      rw [← Subgroup.relIndex_map_map_of_injective _ _ hinj, hmap, hHi]
    · intro f hf
      have hfix := hHx _ hf.2
      have h1 : conjModel e f (e (e.symm x)) = e (e.symm x) := by
        rw [MulEquiv.apply_symm_apply]; exact hfix
      rw [conjModel_apply] at h1
      have h2 := congrArg Subtype.val (e.injective h1)
      simp only at h2
      calc f * ((e.symm x : K) : Y) = f * ((e.symm x : K) : Y) * f⁻¹ * f := by group
        _ = ((e.symm x : K) : Y) * f := by rw [h2]
  have htop : Subgroup.closure S = ⊤ := by
    have h1 : Subgroup.closure (e '' S) = ⊤ := top_le_iff.1 (h ▸ Subgroup.closure_mono himg)
    have h2 := congrArg (Subgroup.map e.symm.toMonoidHom) h1
    rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective] at h2
    have h3 : e.symm.toMonoidHom '' (e '' S) = S := by
      ext k
      constructor
      · rintro ⟨_, ⟨k', hk', rfl⟩, rfl⟩
        simpa using hk'
      · intro hk
        exact ⟨e k, ⟨k, hk, rfl⟩, by simp⟩
    rwa [h3] at h2
  intro y hy
  have hk : (⟨y, hy⟩ : K) ∈ Subgroup.closure S := htop ▸ Subgroup.mem_top _
  have hmap : (Subgroup.closure S).map K.subtype ≤ Subgroup.closure {k : Y | k ∈ K ∧
      ∃ F : Subgroup Y, F ≤ E ∧ F.relIndex E = p ∧ ∀ f ∈ F, f * k = k * f} := by
    rw [MonoidHom.map_closure]
    apply Subgroup.closure_mono
    rintro _ ⟨k, hkS, rfl⟩
    exact ⟨k.2, hkS⟩
  exact hmap ⟨⟨y, hy⟩, hk, rfl⟩

end Transport

@[expose] def A2ThreeModelGen : Prop :=
  ∀ (F : Type) [Field F] [Finite F], 3 ∣ Nat.card F - 1 →
    ∀ B : Subgroup (MulAut (projectiveSL 3 F)), IsElemAbelian 3 B → Nat.card B = 3 ^ 3 →
      ModelHyperGen 3 B

theorem kFactSeitzOuterCubeRankTwoAtPrime_A2_three_of_model {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A 2 q).Valid) (h3 : 3 ∣ q.card - 1) (hM : A2ThreeModelGen) :
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    KFactSeitzOuterCubeRankTwoAtPrime ⟨.A 2 q, hv⟩ 3 := by
  intro _ Y _ _ K hKn hC ⟨e₀⟩ _ _ _ E hEa hEc
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  set e : K ≃* projectiveSL 3 (GaloisField q.p q.exponent) := e₀.trans (linearModel hv) with he
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hinj := conjModel_injective e hC
  refine hyperGen_of_modelHyperGen e hC (hM _ (by rw [hcardF]; exact h3) _ ?_ ?_)
  · exact CFSG.SectionRank.isElemAbelian_map hEa _
  · rw [Subgroup.card_map_of_injective hinj, hEc]

end CFSG.HardMathSupport.Malle.Coordinator.SeitzA2Three
