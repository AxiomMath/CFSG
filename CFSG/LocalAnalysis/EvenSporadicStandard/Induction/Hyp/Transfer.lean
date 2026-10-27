module

import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.SolStdInL
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Setting
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Normal

public section

namespace CFSG.EvenSporadicStandard.Induction.Hyp

open Subgroup CFSG.EvenSporadicStandard.Solomon78

section Transfer

variable {A B : Type} [Group A] [Group B]

theorem map_map_conj (θ : A →* B) (K : Subgroup A) (a : A) :
    (K.map θ).map (MulAut.conj (θ a)).toMonoidHom =
      (K.map (MulAut.conj a).toMonoidHom).map θ := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem centralizer_map_of_surj (θ : A →* B) (hθ : Function.Surjective θ) {P M : Subgroup A}
    [M.Normal] (hPM : P ≤ M) (hC1 : θ.ker ⊓ M = ⊥) :
    centralizer ((P.map θ : Subgroup B) : Set B) = (centralizer (P : Set A)).map θ := by
  ext y
  constructor
  · intro hy
    obtain ⟨a, rfl⟩ := hθ y
    refine ⟨a, mem_centralizer_iff.2 fun p hp => ?_, rfl⟩
    have h1 := mem_centralizer_iff.1 hy (θ p) ⟨p, hp, rfl⟩
    have hM : p * a * p⁻¹ * a⁻¹ ∈ M := by
      have := (inferInstance : M.Normal).conj_mem p⁻¹ (inv_mem (hPM hp)) a
      have h2 : p * a * p⁻¹ * a⁻¹ = p * (a * p⁻¹ * a⁻¹) := by group
      rw [h2]
      exact mul_mem (hPM hp) this
    have hK : p * a * p⁻¹ * a⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker]
      calc θ (p * a * p⁻¹ * a⁻¹) = (θ p * θ a) * (θ p)⁻¹ * (θ a)⁻¹ := by
            simp only [map_mul, map_inv]
        _ = (θ a * θ p) * (θ p)⁻¹ * (θ a)⁻¹ := by rw [h1]
        _ = 1 := by group
    have h3 : p * a * p⁻¹ * a⁻¹ ∈ θ.ker ⊓ M := ⟨hK, hM⟩
    rw [hC1, Subgroup.mem_bot] at h3
    calc p * a = (p * a * p⁻¹ * a⁻¹) * (a * p) := by group
      _ = a * p := by rw [h3, one_mul]
  · rintro ⟨c, hc, rfl⟩
    exact mem_centralizer_iff.2 fun z hz => by
      obtain ⟨p, hp, rfl⟩ := hz
      show θ p * θ c = θ c * θ p
      rw [← map_mul, ← map_mul, mem_centralizer_iff.1 hc p hp]

theorem stdBare_map_of_surj [Finite A] (θ : A →* B) (hθ : Function.Surjective θ)
    {P M : Subgroup A} [M.Normal] (hPM : P ≤ M) (hC1 : θ.ker ⊓ M = ⊥)
    (hC2 : θ.ker ≤ centralizer (M : Set A)) (hP : StdBare P) : StdBare (P.map θ) := by
  have hcent := centralizer_map_of_surj θ hθ hPM hC1
  refine ⟨fun g => ?_, fun g hg => ?_⟩
  · obtain ⟨a, rfl⟩ := hθ g
    rw [map_map_conj, ← Subgroup.map_commutator]
    intro hbot
    apply hP.1 a
    have hle : ⁅P, P.map (MulAut.conj a).toMonoidHom⁆ ≤ θ.ker := (Subgroup.map_eq_bot_iff _).1 hbot
    have hPa : P.map (MulAut.conj a).toMonoidHom ≤ M := by
      rintro _ ⟨x, hx, rfl⟩
      exact (inferInstance : M.Normal).conj_mem x (hPM hx) a
    have hM : ⁅P, P.map (MulAut.conj a).toMonoidHom⁆ ≤ M :=
      (Subgroup.commutator_mono hPM hPa).trans (Subgroup.commutator_le_right M M)
    have : ⁅P, P.map (MulAut.conj a).toMonoidHom⁆ ≤ θ.ker ⊓ M := le_inf hle hM
    rw [hC1] at this
    exact le_bot_iff.1 this
  · obtain ⟨a, rfl⟩ := hθ g
    have ha : a ∉ normalizer (P : Set A) := by
      intro han
      apply hg
      rw [Solomon78.mem_normalizer_iff_map_conj_eq] at han ⊢
      rw [map_map_conj, han]
    have hodd := hP.2 a ha
    have hker1 : θ.ker ≤ centralizer (P : Set A) :=
      hC2.trans (Subgroup.centralizer_le hPM)
    have hker2 : θ.ker ≤ (centralizer (P : Set A)).map (MulAut.conj a).toMonoidHom := by
      intro x hx
      have hx' : a⁻¹ * x * a ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, MonoidHom.mem_ker.1 hx, mul_one,
          inv_mul_cancel]
      exact ⟨a⁻¹ * x * a, hker1 hx', by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group⟩
    have hinter : centralizer ((P.map θ : Subgroup B) : Set B) ⊓
        (centralizer ((P.map θ : Subgroup B) : Set B)).map (MulAut.conj (θ a)).toMonoidHom =
        (centralizer (P : Set A) ⊓
          (centralizer (P : Set A)).map (MulAut.conj a).toMonoidHom).map θ := by
      rw [hcent, map_map_conj]
      ext y
      constructor
      · rintro ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvu⟩⟩
        have hk : v⁻¹ * u ∈ θ.ker := by
          rw [MonoidHom.mem_ker, map_mul, map_inv, hvu, inv_mul_cancel]
        refine ⟨u, ⟨hu, ?_⟩, rfl⟩
        have : u = v * (v⁻¹ * u) := by group
        rw [this]
        exact mul_mem hv (hker2 hk)
      · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
        exact ⟨⟨u, hu1, rfl⟩, ⟨u, hu2, rfl⟩⟩
    rw [hinter]
    have hdvd : Nat.card ↥((centralizer (P : Set A) ⊓
        (centralizer (P : Set A)).map (MulAut.conj a).toMonoidHom).map θ) ∣
        Nat.card ↥(centralizer (P : Set A) ⊓
        (centralizer (P : Set A)).map (MulAut.conj a).toMonoidHom) :=
      Subgroup.card_dvd_of_surjective (MonoidHom.subgroupMap_surjective _ _)
    exact hodd.of_dvd_nat hdvd

end Transfer

theorem solStd_of_stdBare_of_involution {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}
    (hstd : StdBare L) (hq : CFSG.IsQuasisimple ↥L) {t : Y} (ht2 : orderOf t = 2)
    (htL : t ∈ centralizer (L : Set Y)) : SolStd L :=
  hstd.solStd_of_involution hq ht2 htL

end CFSG.EvenSporadicStandard.Induction.Hyp
