module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Normalizer
public import CFSG.ClassicalInvolution.Q3.Q3TLT2OutO8
public import CFSG.HardMathSupport.Curtis.Coordinator.PerfThreeOrthModel

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Spin

variable {V : Type} [CommGroup V]

theorem mem_of_conjAut_eq_conj [Finite V] (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)}
    (hirr : X1.IsIrrOn L) {e : MulAut V} (heN : e ∈ Subgroup.normalizer (L : Set (MulAut V)))
    (he2 : e * e = 1) (l : L) (hl : ∀ x : L, X1.conjAut L heN x = l * x * l⁻¹) : e ∈ L := by
  set c : MulAut V := (l : MulAut V)⁻¹ * e with hc
  have hconj : ∀ x ∈ L, c * x * c⁻¹ = x := by
    intro x hx
    have h2 := congrArg (fun y : L => (y : MulAut V)) (hl ⟨x, hx⟩)
    rw [X1.coe_conjAut, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hc]
    calc ((l : MulAut V)⁻¹ * e) * x * ((l : MulAut V)⁻¹ * e)⁻¹
        = (l : MulAut V)⁻¹ * (e * x * e⁻¹) * (l : MulAut V) := by group
      _ = x := by rw [h2]; group
  have hcomm : ∀ x ∈ L, x * c = c * x := by
    intro x hx
    calc x * c = (c * x * c⁻¹) * c := by rw [hconj x hx]
      _ = c * x := by group
  have hcC : c ∈ Subgroup.centralizer (L : Set (MulAut V)) :=
    Subgroup.mem_centralizer_iff.2 hcomm
  have hcH : c ∈ L ⊔ Subgroup.zpowers e :=
    Subgroup.mul_mem_sup (L.inv_mem l.2) (Subgroup.mem_zpowers e)
  have hE'N : Subgroup.zpowers e ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
    Subgroup.zpowers_le.2 heN
  have hE'el : IsElemAbelian2 (Subgroup.zpowers e) := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have h2 : e ^ (2 : ℕ) = 1 := by rw [pow_two]; exact he2
      rw [h2, one_zpow]
  have hcL : c ∈ L := X1.centralizer_inf_le hV hirr hE'N hE'el ⟨hcH, hcC⟩
  have hbc : e = (l : MulAut V) * c := by rw [hc]; group
  rw [hbc]
  exact L.mul_mem l.2 hcL

theorem lieModel_of_card_two {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {L : Type}
    [Group L] (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) :
    CFSG.Blueprint.LieModel L .POmegaPlus 4 2 1 :=
  Or.inl ⟨by decide, ⟨Nat.prime_two, le_rfl, le_rfl⟩, K, inferInstance, inferInstance,
    by rw [hK]; norm_num,
    ⟨θ.trans (CFSG.HardMathSupport.Curtis.Coordinator.projEquivElementary K hK
      (by norm_num)).symm⟩⟩

theorem card_le_two_mul_card_inf {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) [Finite V] (hV : ∀ v : V, v * v = 1) (L E : Subgroup (MulAut V))
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ L : Subgroup (MulAut V)) := by
  classical
  have : Finite (MulAut V) :=
    Finite.of_injective (fun e : MulAut V => (e : V → V)) fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite ↥L := inferInstance
  have : Finite (MulAut ↥L) :=
    Finite.of_injective (fun e : MulAut ↥L => (e : ↥L → ↥L)) fun _ _ h => MulEquiv.ext (congrFun h)
  have hOut : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) = 6 :=
    CFSG.ClassicalInvolution.Nobq.card_outer_omega8plus2 (lieModel_of_card_two hK θ)
  have : Finite (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) := by
    rw [← not_infinite_iff_finite]
    intro hinf
    have h0 : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L) = 0 :=
      Nat.card_eq_zero.mpr (Or.inr hinf)
    rw [hOut] at h0
    norm_num at h0
  let f : ↥E →* MulAut ↥L :=
    { toFun := fun e => X1.conjAut L (hEN e.2)
      map_one' := by
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        simp only [MulAut.one_apply, X1.coe_conjAut, Subgroup.coe_one, one_mul, mul_one, inv_one]
      map_mul' := by
        intro e₁ e₂
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        simp only [MulAut.mul_apply, X1.coe_conjAut, Subgroup.coe_mul]
        group }
  let φ : ↥E →* CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥L :=
    (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp f
  have hker : φ.ker = (E ⊓ L).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro he
      have hfe : f e ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
        refine (QuotientGroup.eq_one_iff (f e)).mp ?_
        exact he
      obtain ⟨l, hl⟩ := MonoidHom.mem_range.1 hfe
      have hl' : ∀ x : ↥L, X1.conjAut L (hEN e.2) x = l * x * l⁻¹ := by
        intro x
        rw [← MulAut.conj_apply (l : ↥L) x, hl]
        rfl
      have he2 : (e : MulAut V) * (e : MulAut V) = 1 := by
        have := hEel.2 (e : MulAut V) e.2
        simpa [pow_two] using this
      exact ⟨e.2, mem_of_conjAut_eq_conj hV hirr (hEN e.2) he2 l hl'⟩
    · rintro he
      have hfe : X1.conjAut L (hEN e.2) ∈
          CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
        refine MonoidHom.mem_range.2 ⟨⟨(e : MulAut V), (Subgroup.mem_inf.1 he).2⟩, ?_⟩
        apply MulEquiv.ext
        intro x
        apply Subtype.ext
        rw [MulAut.conj_apply, X1.coe_conjAut, Subgroup.coe_mul, Subgroup.coe_mul,
          Subgroup.coe_inv]
      exact (QuotientGroup.eq_one_iff (f e)).mpr hfe
  have hkercard : Nat.card φ.ker = Nat.card ↥(E ⊓ L) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ L ≤ E)).toEquiv
  have hrange : Nat.card φ.range ≤ 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsq : ∀ x ∈ φ.range, x * x = 1 := by
      rintro _ ⟨e, rfl⟩
      rw [← map_mul]
      have he : (e : ↥E) * e = 1 := by
        apply Subtype.ext
        have := hEel.2 (e : MulAut V) e.2
        simpa [pow_two] using this
      rw [he, map_one]
    have hpgrp : IsPGroup 2 φ.range := by
      rw [IsPGroup.iff_orderOf]
      intro x
      have hx2 : x ^ 2 = 1 := by
        apply Subtype.ext
        simpa [pow_two] using hsq x.1 x.2
      have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h]; norm_num⟩
    obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq hpgrp
    have hdvd : 2 ^ n ∣ 6 := by
      rw [← hn]
      have := Subgroup.card_subgroup_dvd_card φ.range
      rw [hOut] at this
      exact this
    have hn2 : n ≤ 2 := by
      by_contra h
      have h3 : 3 ≤ n := by omega
      have h8 : 8 ≤ 2 ^ n := by
        have hpow : 2 ^ 3 ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) (by omega)
        simpa using hpow
      have hle6 : 2 ^ n ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have hnne : n ≠ 2 := by
      intro hn2
      rw [hn2] at hdvd
      norm_num at hdvd
    have hn1 : n ≤ 1 := by omega
    rw [hn]
    calc 2 ^ n ≤ 2 ^ 1 := pow_le_pow_right₀ (by norm_num) hn1
      _ = 2 := by norm_num
  have hcard := Subgroup.card_ker_mul_card_range φ
  calc Nat.card E = Nat.card φ.ker * Nat.card φ.range := hcard.symm
    _ = Nat.card ↥(E ⊓ L) * Nat.card φ.range := by rw [hkercard]
    _ ≤ Nat.card ↥(E ⊓ L) * 2 := Nat.mul_le_mul_left _ hrange
    _ = 2 * Nat.card ↥(E ⊓ L) := Nat.mul_comm _ _

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
