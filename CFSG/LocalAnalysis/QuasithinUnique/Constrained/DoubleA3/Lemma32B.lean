module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32K
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Remark31Phi
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Id2519
open scoped MatrixGroups

@[expose] def KBig {G : Type} [Group G] (K : Subgroup G) : Prop :=
  StatedClassicalModel ↥K .PSL 2 17 1 ∨ StatedClassicalModel ↥K .PSL 3 3 1 ∨
    Nonempty (↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier .M11)

@[expose] def TabBigSylow : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), KBig K → 16 ∣ Nat.card ↥K

@[expose] def TabBigA4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K L U : Subgroup G), KBig K → L ≤ K → IsA4Block L U →
    ∀ P : Subgroup G, P ≤ K → IsPGroup 2 ↥P → P ≤ Subgroup.normalizer (L : Set G) →
      Nat.card ↥P ≤ 8

section Excl

variable {G : Type} [Group G] [Finite G] {T M H S L K : Subgroup G} {s x z₁ z₂ : G}

theorem A3A3x.relIndex_baum_sOne' (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3)
    (hA : A3A3x T M H S L s x z₁ z₂) : (baum S).relIndex (sOne S x) = 2 := by
  have hB := basic31 hD h27_1 hA.toA3A3
  have hRS₁ : baum S ≤ sOne S x := le_sup_left
  have h1 : Nat.card (sOne S x) = Nat.card (baum S) * (baum S).relIndex (sOne S x) :=
    C5.card_eq_card_mul_relIndex hRS₁
  have h2 : Nat.card T = Nat.card (sOne S x) * (sOne S x).relIndex T :=
    C5.card_eq_card_mul_relIndex hA.sOne_le_T
  have hm := hA.relIndex_sOne hD h27_1
  have hpos : 0 < Nat.card (baum S) := Nat.card_pos
  have h3 : Nat.card (baum S) * ((baum S).relIndex (sOne S x) * 2) = Nat.card (baum S) * 4 := by
    calc Nat.card (baum S) * ((baum S).relIndex (sOne S x) * 2) = Nat.card T := by
          rw [h2, h1, hm]; ring
      _ = Nat.card (baum S) * 4 := by rw [hB.card_T]; ring
  have h4 := Nat.eq_of_mul_eq_mul_left hpos h3
  omega

theorem k32ExclBig_of (hD : AppC.C56DoubleA3) (h27_1 : Lemma2_4_27_1A3) (hS : TabBigSylow)
    (hA : TabBigA4) : K32ExclBig := by
  intro G _ _ T M H S L s x z₁ z₂ K ctx hpre hbig
  have hbig' : KBig K := hbig
  have hcs := ctx.a3.cs
  have h3 := ctx.a3.a3
  have hB := basic31 hD h27_1 ctx.a3.toA3A3
  have hA4 : IsA4Block L (blockU L) := IsA4Block.of_alt3 hcs.block.1.1 h3
  have hLK : L ≤ K := hpre.L_le_K
  have hUK : blockU L ≤ K := hA4.le.trans hLK
  have hUR : blockU L ≤ baum S := blockU_le_baum hcs h3
  have hRL : baum S ≤ Subgroup.normalizer (L : Set G) := by
    rw [← hB.N_eq]; exact inf_le_right
  have hS₁p : IsPGroup 2 (sOne S x) := ctx.sylow.2.1
  have hRp : IsPGroup 2 (baum S) := isPGroup_baum hcs
  have hSyl : IsSylowTwoOf (sOne S x ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal ctx.sylow ctx.comp.1 hpre.K_norm
  have hP16 : 16 ≤ Nat.card ↥(sOne S x ⊓ K) := by
    have hdvd := hS G K hbig'
    obtain ⟨n, hn⟩ := hSyl.2.1.exists_card_eq
    have hcard : Nat.card ↥K = Nat.card ↥(sOne S x ⊓ K) * (sOne S x ⊓ K).relIndex K :=
      C5.card_eq_card_mul_relIndex hSyl.1
    have hodd : Odd ((sOne S x ⊓ K).relIndex K) := by
      have h2 : ¬ 2 ∣ (sOne S x ⊓ K).relIndex K := hSyl.2.2
      exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h2)
    rw [hcard, hn] at hdvd
    have h16 : 2 ^ 4 ∣ 2 ^ n := by
      have hcop : Nat.Coprime (2 ^ 4) ((sOne S x ⊓ K).relIndex K) :=
        Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr hodd)
      exact hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    rw [hn]
    exact Nat.le_of_dvd (by positivity) h16
  have hex : ∃ y ∈ sOne S x ⊓ K, y ∉ baum S := by
    by_contra hcon
    push Not at hcon
    have hPR : sOne S x ⊓ K ≤ baum S := hcon
    have h8 := hA G K L (blockU L) hbig' hLK hA4 (sOne S x ⊓ K) inf_le_right
      (hS₁p.to_le inf_le_left) (fun y hy => hRL (hPR hy))
    omega
  obtain ⟨x', hx'P, hx'R⟩ := hex
  have hx'S₁ : x' ∈ sOne S x := hx'P.1
  have hx'K : x' ∈ K := hx'P.2
  have hx'T : x' ∈ T := ctx.a3.sOne_le_T hx'S₁
  have hRx := A3A3x.relIndex_baum_sOne' hD h27_1 ctx.a3
  have hxS₁ : x ∈ sOne S x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxR : x ∉ baum S := fun h => ctx.a3.x_not_mem ((inf_le_left : baum S ≤ S) h)
  have hx'S : x' ∉ S := by
    intro hx'S
    rcases mem_or_inv_mul_mem_of_relIndex_two hRx hxS₁ hxR hx'S₁ with h | h
    · exact hx'R h
    · apply ctx.a3.x_not_mem
      have h1 : x⁻¹ ∈ S := by
        have := S.mul_mem ((inf_le_left : baum S ≤ S) h) (S.inv_mem hx'S)
        simpa using this
      simpa using S.inv_mem h1
  have hQR : pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x' = baum S :=
    ((lemma2_4_30 hD h27_1 G T M H S L s ctx.a3.toA3A3).1 x' hx'T hx'S).1
  have hQle : pCoreOf 2 H ≤ baum S := hB.Q_le_R
  have hQcard : Nat.card ↥(baum S) = 4 * Nat.card ↥(pCoreOf 2 H) := hB.card_R_Q
  have hUQ : blockU L ≤ pCoreOf 2 H := by
    have hU0 : blockU0 S L = blockU L ⊔ blockU2 L s := ctx.a3.toA3A3.blockU0_eq hB.hU0
    have h1 : blockU0 S L ≤ pCoreOf 2 H := by rw [hB.hQ]; exact le_sup_right
    exact le_sup_left.trans (hU0 ▸ h1 : blockU L ⊔ blockU2 L s ≤ pCoreOf 2 H)
  have hSH : S ≤ H := hcs.sylow.1
  have hQnorm : S ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    hSH.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H)
  have hRS : baum S ≤ S := inf_le_left
  have hS₁G : sOne S x ≤ centralizerElem z₂ := ctx.sylow.1
  have hS₁K : sOne S x ≤ Subgroup.normalizer (K : Set G) := fun g hg => hpre.K_norm (hS₁G hg)
  have hQS₁ : pCoreOf 2 H ≤ sOne S x := hQle.trans le_sup_left
  have hconj : conjR (pCoreOf 2 H) x' ≤ pCoreOf 2 H ⊔ (baum S ⊓ K) := by
    intro y hy
    have hq : x' * y * x'⁻¹ ∈ pCoreOf 2 H := mem_conjR.mp hy
    set q : G := x' * y * x'⁻¹ with hqdef
    have hy' : y = x'⁻¹ * q * x' := by rw [hqdef]; group
    have hyR : y ∈ baum S := hQR ▸ (Subgroup.mem_sup_right hy)
    have hqR : q ∈ baum S := hQle hq
    have hqy : q⁻¹ * y ∈ baum S ⊓ K := by
      refine ⟨(baum S).mul_mem ((baum S).inv_mem hqR) hyR, ?_⟩
      have e : q⁻¹ * y = (q⁻¹ * x'⁻¹ * q) * x' := by rw [hy']; group
      rw [e]
      have hqN : q ∈ Subgroup.normalizer (K : Set G) := hS₁K (hQS₁ hq)
      have h1 : q⁻¹ * x'⁻¹ * q ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hqN)
          x'⁻¹).mp (K.inv_mem hx'K)
        simpa using this
      exact K.mul_mem h1 hx'K
    have : y = q * (q⁻¹ * y) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hq hqy
  have hRle : baum S ≤ pCoreOf 2 H ⊔ (baum S ⊓ K) :=
    calc baum S = pCoreOf 2 H ⊔ conjR (pCoreOf 2 H) x' := hQR.symm
      _ ≤ pCoreOf 2 H ⊔ (baum S ⊓ K) := sup_le le_sup_left hconj
  have hRK : pCoreOf 2 H ⊔ (baum S ⊓ K) = baum S :=
    le_antisymm (sup_le hQle inf_le_left) hRle
  have hNK : baum S ⊓ K ≤ Subgroup.normalizer ((pCoreOf 2 H : Subgroup G) : Set G) :=
    inf_le_left.trans (hRS.trans hQnorm)
  have hc := C5.card_sup_mul_card_inf_of_le_normalizer hNK
  rw [sup_comm, hRK, hQcard] at hc
  have hU4 : Nat.card ↥(blockU L) = 4 := hA4.card_U
  have hUin : blockU L ≤ (baum S ⊓ K) ⊓ pCoreOf 2 H := le_inf (le_inf hUR hUK) hUQ
  have hUle : 4 ≤ Nat.card ↥((baum S ⊓ K) ⊓ pCoreOf 2 H) := by
    rw [← hU4]; exact Subgroup.card_le_of_le hUin
  have hQpos : 0 < Nat.card ↥(pCoreOf 2 H) := Nat.card_pos
  have h16 : 16 ≤ Nat.card ↥(baum S ⊓ K) := by
    have : 4 * Nat.card ↥(pCoreOf 2 H) * Nat.card ↥((baum S ⊓ K) ⊓ pCoreOf 2 H) =
        Nat.card ↥(baum S ⊓ K) * Nat.card ↥(pCoreOf 2 H) := hc
    have h2 : 4 * Nat.card ↥((baum S ⊓ K) ⊓ pCoreOf 2 H) = Nat.card ↥(baum S ⊓ K) := by
      apply Nat.eq_of_mul_eq_mul_right hQpos
      calc 4 * Nat.card ↥((baum S ⊓ K) ⊓ pCoreOf 2 H) * Nat.card ↥(pCoreOf 2 H)
          = 4 * Nat.card ↥(pCoreOf 2 H) * Nat.card ↥((baum S ⊓ K) ⊓ pCoreOf 2 H) := by ring
        _ = _ := this
    omega
  have h8 := hA G K L (blockU L) hbig' hLK hA4 (baum S ⊓ K) inf_le_right
    (hRp.to_le inf_le_left) (fun y hy => hRL hy.1)
  omega

end Excl

end CFSG.QuasithinUnique.DoubleA3
