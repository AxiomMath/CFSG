module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitaryC1NextBasic

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3C1Next

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {d : G} {V U U₁ : Subgroup G} {k : ℕ} {K : Type} [Field K] [Fintype K] [CharP K 2]
  {v : G → K} {μ : K}

section NoU'

variable (H : U3C1Next G L f t T d V U U₁ k K v μ)
include H

theorem mem_U_of_perm_zero {P : Subgroup G} (hP2 : IsPGroup 2 P) (hUP : U ≤ P)
    (n : normalizer (U : Set G)) (hnP : (n : G) ∈ P) (h0 : H.perm n 0 = 0) : (n : G) ∈ U := by
  rw [H.perm_zero] at h0
  have hV := H.stage.mem_V_of_X_eq_zero H.card_K H.coords H.nu (H.comm_t_mem_V₁ n.2) h0
  exact H.stage.mem_U_of_comm_t_mem hP2 hUP hnP hV

theorem card_le_of_isPGroup {P : Subgroup G} (hPN : P ≤ normalizer (U : Set G))
    (hP2 : IsPGroup 2 P) (hUP : U ≤ P) : Nat.card P ≤ 2 ^ f * Nat.card U := by
  classical
  set N := U.subgroupOf P with hN
  have key : ∀ a b : P, H.perm ⟨a, hPN a.2⟩ 0 = H.perm ⟨b, hPN b.2⟩ 0 ↔ a⁻¹ * b ∈ N := by
    intro a b
    rw [hN, mem_subgroupOf]
    have e : (⟨((a⁻¹ * b : P) : G), hPN (a⁻¹ * b).2⟩ : normalizer (U : Set G)) =
        (⟨a, hPN a.2⟩ : normalizer (U : Set G))⁻¹ * ⟨b, hPN b.2⟩ := rfl
    constructor
    · intro hab
      refine H.mem_U_of_perm_zero hP2 hUP ⟨_, hPN (a⁻¹ * b).2⟩ (a⁻¹ * b).2 ?_
      rw [e, map_mul, map_inv, Equiv.Perm.mul_apply, ← hab, ← Equiv.Perm.mul_apply, inv_mul_cancel,
        Equiv.Perm.one_apply]
    · intro hU
      have h1 := H.perm_eq_one_of_mem_U ⟨_, hPN (a⁻¹ * b).2⟩ hU
      rw [e, map_mul, map_inv, inv_mul_eq_one] at h1
      rw [h1]
  let ψ : P ⧸ N → K := Quotient.lift (fun a : P => H.perm ⟨a, hPN a.2⟩ 0) fun a b hab =>
    (key a b).mpr (QuotientGroup.leftRel_apply.mp hab)
  have hψ : Function.Injective ψ := by
    intro a b hab
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    exact QuotientGroup.eq.mpr ((key a b).mp hab)
  have h1 : N.index ≤ 2 ^ f := by
    have := Nat.card_le_card_of_injective ψ hψ
    rwa [Nat.card_eq_fintype_card (α := K), H.card_K] at this
  have h2 := N.card_mul_index
  rw [hN, Nat.card_congr (subgroupOfEquivOfLe hUP).toEquiv] at h2
  rw [← h2, mul_comm]
  exact Nat.mul_le_mul_right _ h1

end NoU'

namespace NextUData

variable {H : U3C1Next G L f t T d V U U₁ k K v μ} {U' : Subgroup G} (hD : H.NextUData U')
include hD

theorem conj_szA₁ {x : G} (hx : x ∈ U') : ∀ b ∈ szA₁ (szT₁ L T), x * b * x⁻¹ = b :=
  H.conj_szA₁_of_perm_eq_add ⟨x, hD.le hx⟩ (hD.trans x hx)

theorem X_conj {x : G} (hx : x ∈ U') {w : G} (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) :
    v ((x * w * x⁻¹) ^ 2 ^ (k + 1)) = v (w ^ 2 ^ (k + 1)) := by
  rw [conj_pow, hD.conj_szA₁ hx _ (H.stage.pow_mem_szA₁_V₁ hw)]

theorem chi_mem_V {x : G} (hx : x ∈ U') {w : G}
    (hw : w ∈ U₁ ⊓ centralizer (szT₁ L T : Set G)) : w⁻¹ * (x * w * x⁻¹) ∈ V :=
  (H.X_eq_iff hw (H.conj_mem_V₁ (hD.le hx) hw)).mp (hD.X_conj hx hw).symm

theorem perm_zero_mul {x y : G} (hx : x ∈ U') (hy : y ∈ U') :
    H.perm ⟨x * y, hD.le (mul_mem hx hy)⟩ 0 =
      H.perm ⟨x, hD.le hx⟩ 0 + H.perm ⟨y, hD.le hy⟩ 0 := by
  have e : (⟨x * y, hD.le (mul_mem hx hy)⟩ : normalizer (U : Set G)) =
      ⟨x, hD.le hx⟩ * ⟨y, hD.le hy⟩ := rfl
  rw [e, map_mul, Equiv.Perm.mul_apply, hD.trans x hx]

theorem mem_U_iff {x : G} (hx : x ∈ U') : x ∈ U ↔ H.perm ⟨x, hD.le hx⟩ 0 = 0 := by
  refine ⟨fun hxU => ?_, hD.mem_U x hx⟩
  rw [H.perm_eq_one_of_mem_U ⟨x, hD.le hx⟩ hxU]
  rfl

@[expose] noncomputable def transHom : U' →* Multiplicative K where
  toFun x := Multiplicative.ofAdd (H.perm ⟨x, hD.le x.2⟩ 0)
  map_one' := by
    show Multiplicative.ofAdd (H.perm 1 0) = 1
    rw [map_one]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (H.perm ⟨(x : G) * y, hD.le (mul_mem x.2 y.2)⟩ 0) = _
    rw [hD.perm_zero_mul x.2 y.2]
    rfl

theorem transHom_apply (x : U') :
    hD.transHom x = Multiplicative.ofAdd (H.perm ⟨x, hD.le x.2⟩ 0) := rfl

theorem ker_transHom : hD.transHom.ker = U.subgroupOf U' := by
  ext x
  rw [MonoidHom.mem_ker, mem_subgroupOf, hD.mem_U_iff x.2, transHom_apply]
  exact ⟨fun h => by simpa using congrArg Multiplicative.toAdd h,
    fun h => by rw [h]; rfl⟩

theorem range_transHom : hD.transHom.range = ⊤ := by
  rw [eq_top_iff]
  intro s _
  obtain ⟨x, hx, hxs⟩ := hD.surj (Multiplicative.toAdd s)
  exact ⟨⟨x, hx⟩, by rw [transHom_apply, hxs]; rfl⟩

theorem card : Nat.card U' = 2 * (2 ^ f) ^ (k + 1 + 4) := by
  have h1 := hD.transHom.ker.card_mul_index
  rw [Subgroup.index_ker, hD.range_transHom, Subgroup.card_top, hD.ker_transHom,
    Nat.card_congr (subgroupOfEquivOfLe hD.U_le).toEquiv, H.stage.card_U] at h1
  rw [← h1, show Nat.card (Multiplicative K) = 2 ^ f by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card]; exact H.card_K]
  ring

theorem isPGroup : IsPGroup 2 U' :=
  IsPGroup.of_card (n := 1 + f * (k + 1 + 4)) (by rw [hD.card, pow_add 2 1, pow_one, pow_mul])

theorem isSylowOf : CFSG.ABGLocalTools.IsSylowOf 2 U' (normalizer (U : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP, hUP⟩ := exists_isSylowOf_le_of_isPGroup hD.le hD.isPGroup
  have hle : Nat.card P ≤ Nat.card U' := by
    rw [hD.card]
    calc Nat.card P ≤ 2 ^ f * Nat.card U :=
          H.card_le_of_isPGroup hP.le hP.isPGroup (hD.U_le.trans hUP)
      _ = 2 * (2 ^ f) ^ (k + 1 + 4) := by rw [H.stage.card_U]; ring
  have heq : U' = P := Subgroup.eq_of_le_of_card_ge hUP hle
  rw [heq]
  exact hP

theorem inf_centralizer : U' ⊓ centralizer ({t} : Set G) = szT₁ L T ⊔ zpowers t := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxU', hxC⟩ := mem_inf.mp hx
    have hxU := hD.mem_U x hxU' (H.perm_zero_of_mem_centralizer ⟨x, hD.le hxU'⟩ hxC)
    rw [← H.stage.inf_centralizer]
    exact mem_inf.mpr ⟨hxU, hxC⟩
  · rw [← H.stage.inf_centralizer]
    exact inf_le_inf_right _ hD.U_le

theorem conj_t_not_mem {x : G} (hx : x ∈ U') (hxU : x ∉ U) : x * t * x⁻¹ ∉ szA L T t := by
  intro hA
  have htN : t ∈ normalizer (szA₁ (szT₁ L T) : Set G) :=
    mem_normalizer_of_forall_inv_mul_mul_mem fun b hb => by
      rw [H.stage.t_inv, ← H.stage.t_comm (szA₁_le _ hb), mul_assoc, H.stage.t_mul_self, mul_one]
      exact hb
  rcases CFSG.SeitzReduction.mem_or_mul_mem_of_mem_sup_zpowers H.stage.t_mul_self htN hA with
    h1 | h1
  · exact H.stage.conj_not_mem_U₁ x (H.stage.V_le_U₁ (H.stage.le h1))
  · apply hxU
    refine hD.mem_U x hx ?_
    rw [H.perm_zero]
    show v ((x * t * x⁻¹ * t⁻¹) ^ 2 ^ (k + 1)) = 0
    rw [H.stage.t_inv]
    exact H.stage.X_eq_zero_of_mem_V H.card_K H.coords (H.stage.le h1)

end NextUData

end U3C1Next

end CFSG.SeitzReduction.RankOne
