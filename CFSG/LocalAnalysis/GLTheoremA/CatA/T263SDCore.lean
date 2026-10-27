module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDAut
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem sd_hBN {S : Subgroup Ω} (hSn : S.Normal) (B : Subgroup Ω) :
    B ≤ Subgroup.normalizer (S : Set Ω) := fun _ _ => t263_normalizer_of_normal hSn

theorem sd_conj_coe {S B : Subgroup Ω} (hBN : B ≤ Subgroup.normalizer (S : Set Ω)) (b : ↥B) (k : ↥S) :
    ((CFSG.normalizerConjAutOfMem S B hBN b k : ↥S) : Ω) = (b : Ω) * (k : Ω) * (b : Ω)⁻¹ := by
  simp [CFSG.normalizerConjAutOfMem]

theorem sd_mem_fix_iff {S B : Subgroup Ω} (hBN : B ≤ Subgroup.normalizer (S : Set Ω)) (b : ↥B)
    (s : ↥S) : s ∈ fixSubgroup (CFSG.normalizerConjAutOfMem S B hBN b) ↔
      (s : Ω) ∈ Subgroup.centralizer ({(b : Ω)} : Set Ω) := by
  rw [mem_fixSubgroup, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [sd_conj_coe hBN b s] at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    apply Subtype.ext
    rw [sd_conj_coe hBN b s, mul_inv_eq_iff_eq_mul]
    exact h.symm

@[expose] def sdσ {S : Subgroup Ω} {P : Type} [Group P] (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) :
    ↥S →* P :=
  θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥S))

theorem sdσ_surjective {S : Subgroup Ω} {P : Type} [Group P] (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) :
    Function.Surjective (sdσ θ) :=
  θ.surjective.comp (QuotientGroup.mk'_surjective _)

theorem sdσ_eq_one_iff {S : Subgroup Ω} {P : Type} [Group P] (θ : ↥S ⧸ Subgroup.center ↥S ≃* P)
    (s : ↥S) : sdσ θ s = 1 ↔ s ∈ Subgroup.center ↥S := by
  change θ (QuotientGroup.mk s) = 1 ↔ _
  rw [map_eq_one_iff θ θ.injective, QuotientGroup.eq_one_iff]

theorem sdσ_ker_le {S : Subgroup Ω} {P : Type} [Group P] (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) :
    (sdσ θ).ker ≤ Subgroup.center ↥S := fun s hs => (sdσ_eq_one_iff θ s).1 hs

theorem sd_rho_apply {S B : Subgroup Ω} (hBN : B ≤ Subgroup.normalizer (S : Set Ω)) {P : Type}
    [Group P] (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) (b : ↥B) (k : ↥S) :
    (kd264Rho hBN θ b) (sdσ θ k) = sdσ θ (CFSG.normalizerConjAutOfMem S B hBN b k) := by
  have h1 := CFSG.normalizerConjAutOfMem_comp_mk S B hBN b k
  show (MulAut.congr θ (CFSG.normalizerToCenterQuotientAut S B hBN b))
      (θ (QuotientGroup.mk' (Subgroup.center ↥S) k)) =
    θ (QuotientGroup.mk' (Subgroup.center ↥S) (CFSG.normalizerConjAutOfMem S B hBN b k))
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [← h1]

section Comm

variable {S B B₀ T' : Subgroup Ω} {x : Ω}

theorem sd_S₁_le_T' (hB₀B : B₀ ≤ B) (hBT' : B ≤ Subgroup.normalizer (T' : Set Ω)) :
    (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤ T' := by
  rw [Subgroup.commutator_le]
  intro b hb y hy
  have hy' : y ∈ T' := (Subgroup.mem_inf.1 hy).1
  have h1 : b * y * b⁻¹ ∈ T' := (Subgroup.mem_normalizer_iff.1 (hBT' (hB₀B hb)) y).1 hy'
  rw [commutatorElement_def]
  exact T'.mul_mem h1 (T'.inv_mem hy')

theorem sd_S₁_le_C (hBel : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hB₀B : B₀ ≤ B) (hxB₀ : x ∈ B₀) :
    (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      Subgroup.centralizer ({x} : Set Ω) := by
  rw [Subgroup.commutator_le]
  intro b hb y hy
  have hy' : y ∈ Subgroup.centralizer ({x} : Set Ω) := (Subgroup.mem_inf.1 hy).2
  rw [Subgroup.mem_centralizer_singleton_iff] at hy' ⊢
  have hxb : x * b = b * x := hBel x (hB₀B hxB₀) b (hB₀B hb)
  have hc1 : Commute x b := hxb
  have hc2 : Commute x y := hy'.symm
  have : Commute x ⁅b, y⁆ := by
    rw [commutatorElement_def]
    exact ((hc1.mul_right hc2).mul_right hc1.inv_right).mul_right hc2.inv_right
  exact this.eq.symm

end Comm


section AutComm

variable {S B B₀ T' : Subgroup Ω} {x : Ω} {P : Type} [Group P]

theorem sd_autComm_le (hSn : S.Normal) (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) :
    autComm ((B₀.subgroupOf B).map (kd264Rho (sd_hBN hSn B) θ))
      (((T' ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S).map (sdσ θ)) ≤
    ((⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω).subgroupOf S).map (sdσ θ) := by
  unfold autComm
  rw [Subgroup.closure_le]
  rintro z ⟨b, hb, y, hy, rfl⟩
  obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.1 hb
  obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
  have hβB₀ : (β : Ω) ∈ B₀ := Subgroup.mem_subgroupOf.1 hβ
  have hsY : (s : Ω) ∈ T' ⊓ Subgroup.centralizer ({x} : Set Ω) := Subgroup.mem_subgroupOf.1 hs
  rw [sd_rho_apply (sd_hBN hSn B) θ β s]
  refine ⟨CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) β s * s⁻¹, ?_, ?_⟩
  · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    have : ((CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) β s * s⁻¹ : ↥S) : Ω) =
        ⁅(β : Ω), (s : Ω)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, sd_conj_coe, commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator hβB₀ hsY
  · rw [map_mul, map_inv]

theorem sd_le_autComm (hSn : S.Normal) (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) (hB₀B : B₀ ≤ B)
    (hT'S : T' ≤ S) :
    ((⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω).subgroupOf S).map (sdσ θ) ≤
    autComm ((B₀.subgroupOf B).map (kd264Rho (sd_hBN hSn B) θ))
      (((T' ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S).map (sdσ θ)) := by
  rintro z ⟨g, hg, rfl⟩
  have hg' : (g : Ω) ∈ (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) :=
    Subgroup.mem_subgroupOf.1 hg
  have key : ∀ w ∈ (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω),
      ∃ hw : w ∈ S, sdσ θ ⟨w, hw⟩ ∈
        autComm ((B₀.subgroupOf B).map (kd264Rho (sd_hBN hSn B) θ))
          (((T' ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S).map (sdσ θ)) := by
    intro w hw
    rw [Subgroup.commutator_def] at hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      obtain ⟨β, hβ, t, ht, rfl⟩ := hw
      have htS : t ∈ S := hT'S (Subgroup.mem_inf.1 ht).1
      let β' : ↥B := ⟨β, hB₀B hβ⟩
      let ts : ↥S := ⟨t, htS⟩
      have hcoe : ((CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) β' ts * ts⁻¹ : ↥S) : Ω) =
          ⁅β, t⁆ := by
        rw [Subgroup.coe_mul, Subgroup.coe_inv, sd_conj_coe, commutatorElement_def]
      refine ⟨hcoe ▸ (CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) β' ts * ts⁻¹).2, ?_⟩
      have heq : (⟨⁅β, t⁆, hcoe ▸ (CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) β' ts *
          ts⁻¹).2⟩ : ↥S) = CFSG.normalizerConjAutOfMem S B (sd_hBN hSn B) β' ts * ts⁻¹ :=
        Subtype.ext hcoe.symm
      rw [heq, map_mul, map_inv, ← sd_rho_apply (sd_hBN hSn B) θ β' ts]
      refine Subgroup.subset_closure ⟨kd264Rho (sd_hBN hSn B) θ β', ?_, sdσ θ ts, ?_, rfl⟩
      · exact Subgroup.mem_map.2 ⟨β', Subgroup.mem_subgroupOf.2 hβ, rfl⟩
      · exact Subgroup.mem_map.2 ⟨ts, Subgroup.mem_subgroupOf.2 ht, rfl⟩
    | one =>
      refine ⟨S.one_mem, ?_⟩
      have : (⟨1, S.one_mem⟩ : ↥S) = 1 := rfl
      rw [this, map_one]
      exact Subgroup.one_mem _
    | mul w₁ w₂ _ _ ih₁ ih₂ =>
      obtain ⟨h₁, i₁⟩ := ih₁
      obtain ⟨h₂, i₂⟩ := ih₂
      refine ⟨S.mul_mem h₁ h₂, ?_⟩
      have : (⟨w₁ * w₂, S.mul_mem h₁ h₂⟩ : ↥S) = ⟨w₁, h₁⟩ * ⟨w₂, h₂⟩ := rfl
      rw [this, map_mul]
      exact Subgroup.mul_mem _ i₁ i₂
    | inv w _ ih =>
      obtain ⟨h₁, i₁⟩ := ih
      refine ⟨S.inv_mem h₁, ?_⟩
      have : (⟨w⁻¹, S.inv_mem h₁⟩ : ↥S) = (⟨w, h₁⟩ : ↥S)⁻¹ := rfl
      rw [this, map_inv]
      exact Subgroup.inv_mem _ i₁
  obtain ⟨hw, hmem⟩ := key _ hg'
  exact hmem

end AutComm

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
