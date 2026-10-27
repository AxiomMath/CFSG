module

public import CFSG.HardMathSupport.Dickson.Bal207.SU38Frame
public import CFSG.HardMathSupport.Dickson.Bal207.SU38Block
public import CFSG.HardMathSupport.Dickson.Bal207.UniInner
public import CFSG.HardMathSupport.Dickson.Bal207.UniOuter
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.UnitaryAut
import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.Export

public section

namespace CFSG.HardMathSupport.Dickson.Bal207.Uni

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Dickson.Bal207.FirstClaim

theorem uni_su38Toral_of_block {X : Type} [Group X] [Finite X] {K B J : Subgroup X} {S : Type}
    [Group S] {ℓ f m : ℕ} {E : Type} [Field E] (hB : IsSCp 3 ⊤ B)
    (hBK : B ≤ Subgroup.normalizer (K : Set X))
    (hZ : Nat.Coprime 3 (Nat.card (Subgroup.center ↥K))) (e : (↥K ⧸ Subgroup.center ↥K) ≃* S)
    (hJ : CFSG.Open.IsQuasisimple ↥J) (hJK : J ≤ K) (hBJ : B ≤ Subgroup.normalizer (J : Set X))
    (h : UnitaryFieldData ℓ f E) (hℓ : ℓ = 2) (hf : f = 1 ∨ f = 3) (hne : ℓ ^ f ≠ 2)
    (hm : m = 3) {ι : ↥(primeFormUnitary h (oneGram E m)) →* S} (hι : Function.Injective ι)
    (hJι : (J.comap K.subtype).map (uniMap e) = (blockSU h m).map ι)
    (x : ↥B → blockGamma h m)
    (hx : ∀ (b : ↥B) (g : ↥(primeFormUnitary h (oneGram E m))),
      uniAut e ⟨b, hBK b.2⟩ (ι g) = ι ((x b * SemidirectProduct.inl g * (x b)⁻¹).left))
    (P : ↥(primeFormUnitary h (oneGram E m)))
    (hP : ∀ b : ↥B, ∃ D : ↥(primeFormUnitary h (oneGram E m)),
      ((D : GL (Fin m) E) : Matrix (Fin m) (Fin m) E).IsDiag ∧ ∃ φ : E ≃+* E,
        (∀ c : E, c ^ 3 = 1 → φ c = c) ∧
          (SemidirectProduct.inl P)⁻¹ * x b * SemidirectProduct.inl P =
            SemidirectProduct.inl D * SemidirectProduct.inr φ) :
    SU38Toral B J := by
  subst hm
  exact su38Toral_of_block hB hBK hZ e hJ hJK hBJ h hℓ hf hne hι hJι x hx P hP

end CFSG.HardMathSupport.Dickson.Bal207.Uni

namespace CFSG.HardMathSupport.Dickson.Bal207

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Dickson.Bal207.FirstClaim
  CFSG.HardMathSupport.Dickson.Bal207.Uni

theorem su38FrameUni (hGA : CFSG.Open.GriessAllModelsStatement)
    (G : ∀ (S : Type) [Group S], MulAut S → Prop) : SU38FrameUni G := by
  intro X _ _ _ K B A hctx hL _ a ha ha1 J hJ hJ38 hBJ
  have hK : CFSG.Open.IsQuasisimple ↥K := hctx.comp.2.2
  obtain ⟨-, hZ, f, F, _, h, n, hf, hn, h3, ⟨e₀⟩⟩ := uni_model hGA hK hL
  have hn3 : 3 ≤ n := by omega
  obtain ⟨e, σ, hσ, hframe⟩ := uni_frame h hctx.scp hctx.norm hf hn3 h3 e₀
  have haB : a ∈ B := hctx.le ha
  obtain ⟨D, hD, hD3, k, hk⟩ := hframe a haB
  have hlay : PerfectInLayer (uniAut e ⟨a, hctx.norm haB⟩) := by
    refine LieSemisimple.perfectInLayer_primeFormP h hn3 (fun h' => absurd h'.1 (by omega))
      Nat.prime_three (by norm_num) (by norm_num) _ ?_
    have h1 : (⟨a, hctx.norm haB⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hctx.scp.2.1.2 a haB)
    rw [← map_pow, h1, map_one]
  obtain ⟨hJcomp, hψJ, -⟩ := uni_component e Nat.prime_three hK hZ (hctx.norm haB) hlay hJ
  have hJK : J ≤ K := fun y hy => (hJcomp.1 hy).1
  have hJq : CFSG.Open.IsQuasisimple ↥J := hJcomp.2.2
  obtain ⟨eJL⟩ := LieComp.nonempty_centralQuotient_mulEquiv hJq.1 (uniRestr e hJK)
    (uniRestr_surjective e hJK) (ker_uniRestr_le_center e hJK)
  have hcardL : Nat.card (↥((J.comap K.subtype).map (uniMap e)) ⧸
      Subgroup.center ↥((J.comap K.subtype).map (uniMap e))) = 5515776 := by
    rw [← Nat.card_congr eJL.toEquiv]
    exact uni_card_su38 hJ38
  rw [hk] at hψJ
  by_cases hτ1 : σ ^ k = 1
  swap
  ·
    have hτ3 : (σ ^ k) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσ, one_pow]
    exact absurd hcardL (uni_outer_card_ne hf hn h3 D hD hD3 hτ3 hτ1 hψJ)
  have hΨ : primeFormPsi h uni_isPrimeFormGram_one
      (SemidirectProduct.inl D * SemidirectProduct.inr (σ ^ k)) =
        primeFormConjHom h (oneGram F n) D := by
    rw [hτ1, map_one, mul_one, uni_psi_inl]
  rw [hΨ] at hψJ
  have hD1 : primeFormConjHom h (oneGram F n) D ≠ 1 := by
    intro h1
    have hc : a ∈ Subgroup.centralizer (K : Set X) :=
      mem_centralizer_of_uniAut_eq_one e hK.1 (hctx.norm haB) (by rw [hk, hΨ, h1])
    have hmem : a ∈ A ⊓ Subgroup.centralizer (K : Set X) := ⟨ha, hc⟩
    rw [hctx.disj] at hmem
    exact ha1 (Subgroup.mem_bot.1 hmem)
  obtain ⟨I, ⟨j₀, hj₀⟩, ⟨j₁, hj₁⟩, hJι⟩ := uni_inner_component hf hn3 h3 D hD hD3 hD1 hψJ
  have hι := uni_theta_uniBlk_injective (h := h) hf hn3 h3 hj₀
  have hm1 : 1 ≤ I.card := Finset.card_pos.2 ⟨j₁, hj₁⟩
  obtain ⟨eJP⟩ := LieComp.nonempty_centralQuotient_mulEquiv hJq.1 (blockHom e h hJK hι hJι 1)
    (blockHom_surjective e h hJK hι hJι 1) (ker_blockHom_le_center e h hJK hι hJι hJq.1 1)
  have hcardP : Nat.card (primeFormP h (oneGram F I.card) ⧸
      Subgroup.center (primeFormP h (oneGram F I.card))) = 5515776 := by
    rw [← Nat.card_congr eJP.toEquiv]
    exact uni_card_su38 hJ38
  have hdvd : 5515776 ∣ Nat.card (primeFormP h (oneGram F I.card)) := by
    rw [← hcardP]
    exact Subgroup.index_dvd_card _
  obtain ⟨hm3, hne⟩ := uni_nine_le_cases hf (uni_nine_le_of_dvd h hm1 hdvd)
  have hZP : Subgroup.center (primeFormP h (oneGram F I.card)) = ⊥ :=
    CFSG.RankThree.PartOne.KCUnitaryRegular.center_primeFormP_eq_bot h uni_isPrimeFormGram_one
      hm3 hne
  have e0 : Nat.card (primeFormP h (oneGram F I.card) ⧸
      (⊥ : Subgroup (primeFormP h (oneGram F I.card)))) =
        Nat.card (primeFormP h (oneGram F I.card)) := Subgroup.index_bot
  rw [hZP, e0] at hcardP
  obtain ⟨hf3, hm⟩ := uni_nine_cases hf (uni_eq_nine_of_card h hm1 hcardP)
  obtain ⟨x, hx, hP⟩ := uni_block_frame h hctx.norm hf hn3 h3 e hσ hframe I
  exact Or.inr (uni_su38Toral_of_block hctx.scp hctx.norm hZ e hJq hJK hBJ h rfl hf
    (by rw [hf3]; norm_num) hm hι hJι x hx 1 hP)

end CFSG.HardMathSupport.Dickson.Bal207

end
