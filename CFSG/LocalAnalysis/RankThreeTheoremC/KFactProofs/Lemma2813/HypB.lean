module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.GenericB
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627L32Data
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.BasicB

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem Hyp2813.pCore_X_le_R (h : Hyp2813 X K R P) : pCoreOf 2 X ≤ R :=
  pCoreOf_le_of_odd_index h.R_two h.R_le h.R_sylow

theorem Hyp2813.R_sylow_P (h : Hyp2813 X K R P) : ¬ 2 ∣ (R.subgroupOf P).index := by
  intro h2
  apply h.R_sylow
  have hmul := Subgroup.relIndex_mul_relIndex R P X h.R_le_P h.P_le
  show 2 ∣ R.relIndex X
  rw [← hmul]
  exact Dvd.dvd.mul_right h2 _

theorem Hyp2813.pCore_P_le_R (h : Hyp2813 X K R P) : pCoreOf 2 P ≤ R :=
  pCoreOf_le_of_odd_index h.R_two h.R_le_P h.R_sylow_P

theorem Hyp2813.pCore_X_le_pCore_P (h : Hyp2813 X K R P) :
    pCoreOf 2 X ≤ pCoreOf 2 P :=
  le_pCoreOf_of_normalizes (isPGroup_pCoreOf X) (h.pCore_X_le_R.trans h.R_le_P)
    (h.P_le.trans (normalizer_pCoreOf X))

theorem Hyp2813.mem_X_iff (h : Hyp2813 X K R P) {g : A} :
    g ∈ X ↔ ∃ k ∈ K, ∃ o ∈ pCoreOf 2 X, g = k * o := by
  constructor
  · intro hg
    have hset : ((K ⊔ pCoreOf 2 X : Subgroup A) : Set A) = (K : Set A) * (pCoreOf 2 X : Set A) :=
      Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 X)
        (h.K_le.trans (normalizer_pCoreOf X))
    have hg' : g ∈ ((K ⊔ pCoreOf 2 X : Subgroup A) : Set A) := h.X_eq.le hg
    rw [hset] at hg'
    obtain ⟨k, hk, o, ho, rfl⟩ := hg'
    exact ⟨k, hk, o, ho, rfl⟩
  · rintro ⟨k, hk, o, ho, rfl⟩
    exact X.mul_mem (h.K_le hk) (pCoreOf_le_self X ho)

end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem Hyp2813.exists_psi (h : Hyp2813 X K R P) :
    ∃ ψ : ↥X →* GL32, Function.Surjective ψ ∧ ψ.ker = (pCoreOf 2 X).subgroupOf X := by
  obtain ⟨f, hf, hker⟩ := h.quot
  have hle : pCoreOf 2 X ≤ X := pCoreOf_le_self X
  haveI hN : ((pCoreOf 2 X).subgroupOf X).Normal :=
    (normal_subgroupOf_iff_le_normalizer hle).2 (normalizer_pCoreOf X)
  let g : ↥K →* ↥X ⧸ (pCoreOf 2 X).subgroupOf X :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion h.K_le)
  have hg_surj : Function.Surjective g := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk, o, ho, hxko⟩ := h.mem_X_iff.1 x.2
    refine ⟨⟨k, hk⟩, ?_⟩
    show QuotientGroup.mk (Subgroup.inclusion h.K_le ⟨k, hk⟩) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hxko] using ho
  have hg_ker : g.ker = f.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hker k]
    show QuotientGroup.mk (Subgroup.inclusion h.K_le k) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  let e : (↥X ⧸ (pCoreOf 2 X).subgroupOf X) ≃* GL32 :=
    (QuotientGroup.quotientKerEquivOfSurjective g hg_surj).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hg_ker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf))
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' _), ?_, ?_⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
    simp

theorem Hyp2813.card_X (h : Hyp2813 X K R P) :
    Nat.card ↥X = Nat.card ↥(pCoreOf 2 X) * 168 := by
  obtain ⟨ψ, hψ, hψker⟩ := h.exists_psi
  have h1 := Subgroup.card_ker_mul_card_of_surjective hψ
  rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le_self X)).toEquiv,
    L32Insp.card_GL] at h1
  exact h1.symm
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
