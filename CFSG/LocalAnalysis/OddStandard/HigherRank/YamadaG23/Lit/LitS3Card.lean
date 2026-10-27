module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitBlock
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitGam

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three CFSG.OddStandard.HigherRank.G2Three.Sec1
  CFSG.GH74.GLS
open scoped commutatorElement

private lemma nat_eq_sixteen_of {i c : ℕ} (h : i * c = 720) (hi : ¬ 2 ∣ i)
    (hc : ∃ k, c = 2 ^ k) : c = 16 := by
  obtain ⟨k, rfl⟩ := hc
  have hk4 : k ≤ 4 := by
    by_contra hk
    have h5 : 5 ≤ k := by omega
    have hdvd : 2 ^ k ∣ 720 := ⟨i, by rw [mul_comm]; exact h.symm⟩
    have h32 : 2 ^ 5 ∣ 2 ^ k := pow_dvd_pow 2 h5
    have : (32 : ℕ) ∣ 720 := by simpa using h32.trans hdvd
    norm_num at this
  interval_cases k
  · exfalso
    norm_num at h
    have hi' : i = 720 := by omega
    rw [hi'] at hi
    norm_num at hi
  · exfalso
    norm_num at h
    have hi' : i = 360 := by omega
    rw [hi'] at hi
    norm_num at hi
  · exfalso
    norm_num at h
    have hi' : i = 180 := by omega
    rw [hi'] at hi
    norm_num at hi
  · exfalso
    norm_num at h
    have hi' : i = 90 := by omega
    rw [hi'] at hi
    norm_num at hi
  · norm_num

variable {Γ : Type} [Group Γ] {Gh Zh Ah : Subgroup Γ} {t : Γ}

theorem lit_s3_not_le_T [Finite Γ] (h : LitGam Gh Zh Ah t)
    (hq : IsQuotIso (normIn Gh Ah) (Gh ⊓ centralizerSection Ah Zh) (Equiv.Perm (Fin 6)))
    (hT : IsQuotIso (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh)
      (Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh ⊓ (Gh ⊓ centralizerSection Ah Zh))
      ↥blockStab)
    {S : Subgroup Γ} (hSN : S ≤ normIn Gh Ah) (hS2 : IsPGroup 2 S)
    (hSidx : ¬ 2 ∣ S.relIndex (normIn Gh Ah)) :
    ¬ S ≤ Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh := by
  classical
  let N : Subgroup Γ := normIn Gh Ah
  let C : Subgroup Γ := Gh ⊓ centralizerSection Ah Zh
  let T : Subgroup Γ := Gh ⊓ centralizerSection (Zh ⊔ zpowers t) Zh
  have hTN : T ≤ N := by
    intro x hx
    exact ⟨hx.1, h.five_b hx⟩
  rintro hST
  obtain ⟨-, φ, hφsurj, hφker⟩ := hq
  obtain ⟨-, ψ, hψsurj, hψker⟩ := hT
  have hrelT : (C.subgroupOf N).relIndex (T.subgroupOf N) = 72 := by
    rw [← Subgroup.inf_relIndex_right (C.subgroupOf N) (T.subgroupOf N)]
    have hinf : C.subgroupOf N ⊓ T.subgroupOf N = (T ⊓ C).subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf, and_comm]
    rw [hinf, Subgroup.relIndex_subgroupOf hTN]
    change ((T ⊓ C).subgroupOf T).index = 72
    rw [← hψker, Subgroup.index_ker, ψ.range_eq_top_of_surjective hψsurj]
    simpa [Nat.card_eq_fintype_card] using lit_card_blockStab
  have hcardT : Nat.card ((T.subgroupOf N).map φ) = 72 := by
    rw [← Subgroup.relIndex_ker φ (K := T.subgroupOf N), hφker, hrelT]
  have hSidx : ¬ 2 ∣ (S.subgroupOf N).index := by
    simpa [Subgroup.relIndex] using hSidx
  have hS2' : IsPGroup 2 (S.subgroupOf N) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hH2 : IsPGroup 2 ((S.subgroupOf N).map φ) := hS2'.map φ
  have hHidx : ¬ 2 ∣ ((S.subgroupOf N).map φ).index := by
    intro h2
    exact hSidx (h2.trans (Subgroup.index_map_dvd (H := S.subgroupOf N) hφsurj))
  have hcardS : Nat.card ((S.subgroupOf N).map φ) = 16 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hH2.exists_card_eq
    refine nat_eq_sixteen_of ?_ hHidx ⟨k, hk⟩
    rw [Subgroup.index_mul_card, Nat.card_perm, Nat.card_fin]
    norm_num
  have hle : (S.subgroupOf N).map φ ≤ (T.subgroupOf N).map φ := by
    apply Subgroup.map_mono
    intro x hx
    exact hST hx
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hcardS, hcardT] at hdvd
  norm_num at hdvd

end CFSG.OddStandard.HigherRank.YamadaG23
