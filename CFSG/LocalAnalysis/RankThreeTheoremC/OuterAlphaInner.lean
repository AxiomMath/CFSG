module

public import CFSG.LocalAnalysis.AGLEmbedding.ConstrainedSLAux
import CFSG.LocalAnalysis.AGLEmbedding.RankOneAutomizer
import CFSG.LocalAnalysis.RankThreeTheoremC.OuterExtraspecial

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (centerQuotientAction centerQuotientAction_eq mk_eq_mk_iff_conjNormal_eq)

section Nonabelian

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

omit [Finite X] in
theorem exists_nonabelian_isPGroup_mulAut {K : Subgroup X} [K.Normal] {E : Subgroup X}
    (hEp : ∀ x ∈ E, x ^ p = 1)
    (hEC : E ⊓ Subgroup.centralizer (K : Set X) = (Subgroup.center E).map E.subtype)
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) {u : X}
    (hu : u ∈ Subgroup.normalizer (E : Set X)) {n : ℕ} (hun : u ^ (p ^ n) = 1)
    (hψ : centerQuotientAction E e ⟨u, hu⟩ ≠ 1) :
    ∃ B : Subgroup (MulAut K), IsPGroup p B ∧ ¬ IsMulCommutative B := by
  have hp : p.Prime := Fact.out
  set N : Subgroup X := Subgroup.normalizer (E : Set X) with hN
  have hupg : IsPGroup p (Subgroup.zpowers (⟨u, hu⟩ : N)) := by
    refine IsPGroup.of_card (n := (orderOf (⟨u, hu⟩ : N)).factorization p) ?_
    rw [Nat.card_zpowers]
    have hdvd : orderOf (⟨u, hu⟩ : N) ∣ p ^ n :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hun))
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    rw [hj, Nat.Prime.factorization_pow hp]
    simp
  obtain ⟨S, hS⟩ := hupg.exists_le_sylow
  have hEn : (E.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer Subgroup.le_normalizer).mpr le_rfl
  have hEpg : IsPGroup p (E.subgroupOf N) := fun x => ⟨1, Subtype.ext (Subtype.ext
    (by simpa using hEp x.1.1 (Subgroup.mem_subgroupOf.mp x.2)))⟩
  have hES : E.subgroupOf N ≤ (S : Subgroup N) := hEpg.le_sylow_of_normal S
  refine ⟨(S : Subgroup N).map ((MulAut.conjNormal (H := K)).comp N.subtype),
    S.isPGroup'.map _, fun hcomm => hψ ?_⟩
  have hρu : MulAut.conjNormal (H := K) u ∈
      (S : Subgroup N).map ((MulAut.conjNormal (H := K)).comp N.subtype) :=
    ⟨⟨u, hu⟩, hS (Subgroup.mem_zpowers _), rfl⟩
  refine centerQuotientAction_eq E e ⟨u, hu⟩ 1 fun x v hxv => ?_
  have hρx : MulAut.conjNormal (H := K) (x : X) ∈
      (S : Subgroup N).map ((MulAut.conjNormal (H := K)).comp N.subtype) :=
    ⟨⟨x, Subgroup.le_normalizer x.2⟩, hES (Subgroup.mem_subgroupOf.mpr x.2), rfl⟩
  have hc := isMulCommutative_iff.mp hcomm ⟨_, hρu⟩ ⟨_, hρx⟩
  have hc' : MulAut.conjNormal (H := K) u * MulAut.conjNormal (H := K) (x : X) =
      MulAut.conjNormal (H := K) (x : X) * MulAut.conjNormal (H := K) u :=
    congrArg Subtype.val hc
  have hvx : (v : E ⧸ Subgroup.center E) = x := by
    refine (mk_eq_mk_iff_conjNormal_eq hEC v x).mpr ?_
    rw [hxv, map_mul, map_mul, map_inv, hc', mul_assoc, mul_inv_cancel, mul_one]
  rw [Units.val_one, Matrix.one_mulVec, hvx]

end Nonabelian

section Commutator

variable {X : Type*} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]

theorem exists_commutator_eq_of_mem_inf_sup (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hcomm : ∀ c₁ ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X),
      ∀ c₂ ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), c₁ * c₂ = c₂ * c₁)
    {u v : X} (hu : u ∈ (R : Subgroup X)) (hv : v ∈ (R : Subgroup X))
    (huK : u ∈ K ⊔ Subgroup.centralizer (K : Set X))
    (hvK : v ∈ K ⊔ Subgroup.centralizer (K : Set X)) :
    ∃ t₁ ∈ (R : Subgroup X) ⊓ K, ∃ t₂ ∈ (R : Subgroup X) ⊓ K,
      u * v * u⁻¹ * v⁻¹ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by
  obtain ⟨t₁, ht₁, c₁, hc₁, rfl⟩ := exists_mul_eq_of_mem_inf_sup R hu huK
  obtain ⟨t₂, ht₂, c₂, hc₂, rfl⟩ := exists_mul_eq_of_mem_inf_sup R hv hvK
  refine ⟨t₁, ht₁, t₂, ht₂, ?_⟩
  have e1 : c₁ * t₂ = t₂ * c₁ := (Subgroup.mem_centralizer_iff.mp hc₁.2 t₂ ht₂.2).symm
  have e2 : c₂ * t₁⁻¹ = t₁⁻¹ * c₂ :=
    (Subgroup.mem_centralizer_iff.mp hc₂.2 t₁⁻¹ (K.inv_mem ht₁.2)).symm
  have e3 : c₁ * c₂ = c₂ * c₁ := hcomm c₁ hc₁ c₂ hc₂
  calc t₁ * c₁ * (t₂ * c₂) * (t₁ * c₁)⁻¹ * (t₂ * c₂)⁻¹
      = t₁ * (c₁ * t₂) * c₂ * c₁⁻¹ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by group
    _ = t₁ * t₂ * (c₁ * c₂) * c₁⁻¹ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by rw [e1]; group
    _ = t₁ * t₂ * c₂ * t₁⁻¹ * c₂⁻¹ * t₂⁻¹ := by rw [e3]; group
    _ = t₁ * t₂ * (c₂ * t₁⁻¹) * c₂⁻¹ * t₂⁻¹ := by group
    _ = t₁ * t₂ * t₁⁻¹ * t₂⁻¹ := by rw [e2]; group

omit [Finite X] in
theorem commutator_mem_center_of_mulEquiv' {E : Type*} [Group E]
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) (u v : E) :
    u * v * u⁻¹ * v⁻¹ ∈ Subgroup.center E := by
  have hQ : ∀ a b : E ⧸ Subgroup.center E, a * b = b * a := fun a b =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
    hQ (u : E ⧸ Subgroup.center E) (v : E ⧸ Subgroup.center E)]
  group

theorem mem_commutator_inf_of_le_sup (R : Sylow p X) {K : Subgroup X} [K.Normal]
    (hcomm : ∀ c₁ ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X),
      ∀ c₂ ∈ (R : Subgroup X) ⊓ Subgroup.centralizer (K : Set X), c₁ * c₂ = c₂ * c₁)
    {z : X} (hzp : orderOf z = p) {E : Subgroup X} (hER : E ≤ (R : Subgroup X))
    (hEZ : (Subgroup.center E).map E.subtype = Subgroup.zpowers z)
    (hEY : E ≤ K ⊔ Subgroup.centralizer (K : Set X))
    (e : E ⧸ Subgroup.center E ≃* Multiplicative (Fin 2 → ZMod p)) :
    z ∈ ⁅(R : Subgroup X) ⊓ K, (R : Subgroup X) ⊓ K⁆ := by
  have hp : p.Prime := Fact.out
  have hne := not_forall_mul_comm_of_mulEquiv e
  push Not at hne
  obtain ⟨u, v, huv⟩ := hne
  obtain ⟨t₁, ht₁, t₂, ht₂, hc⟩ := exists_commutator_eq_of_mem_inf_sup R hcomm (hER u.2)
    (hER v.2) (hEY u.2) (hEY v.2)
  have hcT : (u : X) * v * (u : X)⁻¹ * (v : X)⁻¹ ∈
      ⁅(R : Subgroup X) ⊓ K, (R : Subgroup X) ⊓ K⁆ := by
    rw [hc]
    exact Subgroup.commutator_mem_commutator ht₁ ht₂
  have hcz : (u : X) * v * (u : X)⁻¹ * (v : X)⁻¹ ∈ Subgroup.zpowers z := by
    rw [← hEZ]
    exact ⟨_, commutator_mem_center_of_mulEquiv' e u v, by simp⟩
  have hc1 : (u : X) * v * (u : X)⁻¹ * (v : X)⁻¹ ≠ 1 := by
    intro h1
    refine huv (Subtype.ext ?_)
    have h2 : (u : X) * v = v * u := by
      calc (u : X) * v = ((u : X) * v * (u : X)⁻¹ * (v : X)⁻¹) * ((v : X) * u) := by group
        _ = (v : X) * u := by rw [h1, one_mul]
    simpa using h2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  have hcp : ((u : X) * v * (u : X)⁻¹ * (v : X)⁻¹) ^ p = 1 := by
    rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
      (hzp ▸ pow_orderOf_eq_one z : z ^ p = 1), one_zpow]
  have hord := orderOf_eq_prime hcp hc1
  have hle : Subgroup.zpowers ((u : X) * v * (u : X)⁻¹ * (v : X)⁻¹) ≤ Subgroup.zpowers z :=
    Subgroup.zpowers_le.mpr hcz
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hzp])
  have hzmem : z ∈ Subgroup.zpowers ((u : X) * v * (u : X)⁻¹ * (v : X)⁻¹) := by
    rw [heq]
    exact Subgroup.mem_zpowers z
  exact Subgroup.zpowers_le.mpr hcT hzmem

end Commutator

end CFSG.LocalAnalysis.RankThreeTheoremC
