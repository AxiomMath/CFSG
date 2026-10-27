module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7CACj
public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Sec1Proof.SylowConj

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped Pointwise

variable {Γ : Type} [Group Γ] [Finite Γ] {t : Γ}

private lemma y7c_conj_invol (ht : t ^ 2 = 1) (x : Γ) : t * (t * x * t⁻¹) * t⁻¹ = x := by
  have h2 : t * t = 1 := by simpa [pow_two] using ht
  rw [show t⁻¹ = t from inv_eq_of_mul_eq_one_right h2]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [h2, one_mul, mul_one]

private lemma y7c_mem_normalizer_of_conj {X : Subgroup Γ} (ht : t ^ 2 = 1)
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : t ∈ Subgroup.normalizer (X : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨hX x, fun hx => ?_⟩
  have h := hX (t * x * t⁻¹) hx
  rwa [y7c_conj_invol ht x] at h

private noncomputable def y7c_conjAut (ht : t ^ 2 = 1) (X : Subgroup Γ)
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : MulAut ↥X :=
  ((MulAut.conj t).subgroupMap X).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp
      (y7c_mem_normalizer_of_conj ht hX)))

private lemma y7c_conjAut_apply (ht : t ^ 2 = 1) {X : Subgroup Γ}
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) (x : ↥X) :
    ((y7c_conjAut ht X hX x : ↥X) : Γ) = t * (x : Γ) * t⁻¹ := by
  simp [y7c_conjAut, MulAut.conj_apply]

private lemma y7c_conjAut_sq (ht : t ^ 2 = 1) {X : Subgroup Γ}
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) : y7c_conjAut ht X hX ^ 2 = 1 := by
  ext x
  rw [pow_two, MulAut.mul_apply, y7c_conjAut_apply, y7c_conjAut_apply,
    y7c_conj_invol ht (x : Γ)]
  simp

private theorem isSylowIn_map_subtype {p : ℕ} [Fact p.Prime] {V : Subgroup Γ}
    (P : Sylow p ↥V) : IsSylowIn p V ((P : Subgroup ↥V).map V.subtype) := by
  refine ⟨Subgroup.map_subtype_le _, P.isPGroup'.map V.subtype, ?_⟩
  have h := Subgroup.relIndex_map_map_of_injective (f := V.subtype)
    (P : Subgroup ↥V) (⊤ : Subgroup ↥V) V.subtype_injective
  rw [Subgroup.map_top V.subtype, Subgroup.range_subtype, Subgroup.relIndex_top_right] at h
  rw [h]
  exact P.not_dvd_index

private lemma y7c_isPGroup_zpowers (ht : t ^ 2 = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers t) :=
  IsPGroup.of_card_dvd_pow (G := ↥(Subgroup.zpowers t)) (p := 2) (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mpr ht)

theorem y7c_exists_inv_sylow (ht : t ^ 2 = 1) {X : Subgroup Γ}
    (hX : ∀ x ∈ X, t * x * t⁻¹ ∈ X) :
    ∃ W : Subgroup Γ, IsSylowIn 2 X W ∧ ∀ w ∈ W, t * w * t⁻¹ ∈ W := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σ : MulAut ↥X := y7c_conjAut ht X hX
  have hσ2 : σ ^ 2 = 1 := y7c_conjAut_sq ht hX
  have hσapply : ∀ x : ↥X, ((σ x : ↥X) : Γ) = t * (x : Γ) * t⁻¹ := y7c_conjAut_apply ht hX
  have hHp : IsPGroup 2 ↥(Subgroup.zpowers σ) :=
    IsPGroup.of_card_dvd_pow (G := ↥(Subgroup.zpowers σ)) (p := 2) (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_iff_pow_eq_one.mpr hσ2)
  haveI : Finite (Sylow 2 ↥X) :=
    Sylow.finite_of_finiteIndex (Classical.arbitrary (Sylow 2 ↥X))
  have hnotdvd : ¬ 2 ∣ Nat.card (Sylow 2 ↥X) := not_dvd_card_sylow 2 ↥X
  obtain ⟨P, hPfix⟩ := hHp.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 ↥X) hnotdvd
  have hσP : σ • P = P := by
    simpa using (MulAction.mem_fixedPoints.mp hPfix) ⟨σ, Subgroup.mem_zpowers σ⟩
  have hsub : σ • (P : Subgroup ↥X) = (P : Subgroup ↥X) := by
    have h1 := congrArg (fun Q : Sylow 2 ↥X => (Q : Subgroup ↥X)) hσP
    simpa [Sylow.pointwise_smul_def] using h1
  refine ⟨(P : Subgroup ↥X).map X.subtype, isSylowIn_map_subtype P, ?_⟩
  intro w hw
  rw [Subgroup.mem_map] at hw
  obtain ⟨p, hp, rfl⟩ := hw
  refine Subgroup.mem_map.mpr ⟨σ p, ?_, hσapply p⟩
  have hmem := Subgroup.smul_mem_pointwise_smul p σ (P : Subgroup ↥X) hp
  simpa [MulAut.smul_def, hsub] using hmem

theorem y7c_two_group_join (ht : t ^ 2 = 1) {W : Subgroup Γ} (hW : IsPGroup 2 ↥W)
    (hn : ∀ w ∈ W, t * w * t⁻¹ ∈ W) : IsPGroup 2 ↥(W ⊔ Subgroup.zpowers t) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.to_sup_of_normal_left' hW (y7c_isPGroup_zpowers ht) ?_
  rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨hn w, fun hw => ?_⟩
  have h := hn (t * w * t⁻¹) hw
  rwa [y7c_conj_invol ht w] at h

theorem y7c_exists_conj_le_sylow {X E W : Subgroup Γ} (g : Γ) (hW : IsSylowIn 2 (conjSub g X) W)
    (hE : E ≤ X) (hE2 : IsPGroup 2 ↥E) : ∃ h : Γ, conjSub h E ≤ W := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE' : conjSub g E ≤ conjSub g X := y7c_conjSub_le hE
  have hE2' : IsPGroup 2 ↥(conjSub g E) := hE2.map (MulAut.conj g).toMonoidHom
  obtain ⟨P, hPle⟩ := (hE2'.comap_subtype (K := conjSub g X)).exists_le_sylow
  let PΓ : Subgroup Γ := (P : Subgroup ↥(conjSub g X)).map (conjSub g X).subtype
  have hPΓ : IsSylowIn 2 (conjSub g X) PΓ := isSylowIn_map_subtype P
  have hE'P : conjSub g E ≤ PΓ := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hE' hx⟩, hPle (by rw [Subgroup.mem_comap]; exact hx), rfl⟩
  obtain ⟨k, -, hkW⟩ :=
    CFSG.OddStandard.HigherRank.G2Three.Sec1Proof.exists_conj_of_isSylowIn hPΓ hW
  refine ⟨k * g, ?_⟩
  rw [y7c_conjSub_mul, hkW]
  exact y7c_conjSub_le hE'P

end CFSG.OddStandard.HigherRank.YamadaG23
