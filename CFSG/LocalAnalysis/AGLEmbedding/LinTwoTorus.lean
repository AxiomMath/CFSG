module

public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
import CFSG.CharacterTheory.PSL2Table.Tori

public section

namespace CFSG.AGLEmbedding

open CFSG.PSL2Table
open scoped MatrixGroups

@[expose] def unipMonoidHom (F : Type) [Field F] : Multiplicative F →* PSL(2, F) where
  toFun t := mk (unip (Multiplicative.toAdd t))
  map_one' := by rw [toAdd_one, unip_zero, map_one]
  map_mul' s t := by rw [toAdd_mul, unip_add, map_mul]

theorem unipMonoidHom_apply {F : Type} [Field F] (t : Multiplicative F) :
    unipMonoidHom F t = mk (unip (Multiplicative.toAdd t)) := rfl

theorem exists_torus_param_of_mulEquiv_psl2GF {Y : Type} [Group Y] {p n : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hn : 1 ≤ n) {K : Subgroup Y} (e : K ≃* PSL2GF p n) (U : Subgroup Y)
    (hUK : U ≤ K) (hcard : Nat.card U = p ^ n) :
    ∃ ψ : Multiplicative (GaloisField p n) →* Y, Function.Injective ψ ∧ ψ.range = U ∧
      ∀ μ : (GaloisField p n)ˣ, ∃ c ∈ K, ∀ a : Multiplicative (GaloisField p n),
        c * ψ a * c⁻¹ =
          ψ (Multiplicative.ofAdd ((μ : GaloisField p n) ^ 2 * Multiplicative.toAdd a)) := by
  have hF : ringChar (GaloisField p n) ≠ 2 := by rw [ringChar.eq (GaloisField p n) p]; exact hp2
  have h2 : (2 : GaloisField p n) ≠ 0 := Ring.two_ne_zero hF
  have hmemV : ∀ x, x ∈ (U.subgroupOf K).map e.toMonoidHom ↔ ((e.symm x : K) : Y) ∈ U :=
    fun x => by rw [Subgroup.mem_map_equiv, Subgroup.mem_subgroupOf]
  have hVcard : Nat.card ((U.subgroupOf K).map e.toMonoidHom) = p ^ n := by
    rw [Subgroup.card_map_of_injective e.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv, hcard]
  obtain ⟨T, hVT⟩ := (IsPGroup.of_card hVcard).exists_le_sylow
  have hVT : (U.subgroupOf K).map e.toMonoidHom = T :=
    Subgroup.eq_of_le_of_card_ge hVT (by rw [hVcard, (psl2GF_sylow p n hn T).2])
  obtain ⟨U₀, hU₀⟩ := exists_sylow_eq_unipotent_psl2GF hp2 hn
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq (PSL2GF p n) U₀ T
  have hmem : ∀ x, x ∈ (U.subgroupOf K).map e.toMonoidHom ↔
      g⁻¹ * x * g ∈ unipotent (GaloisField p n) := by
    intro x
    rw [hVT, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, hU₀]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y * g⁻¹) * g ∈ _
      simpa [mul_assoc] using hy
    · intro h
      refine ⟨g⁻¹ * x * g, h, ?_⟩
      change g * (g⁻¹ * x * g) * g⁻¹ = x
      group
  let ψ : Multiplicative (GaloisField p n) →* Y := K.subtype.comp (e.symm.toMonoidHom.comp
    ((MulAut.conj g).toMonoidHom.comp (unipMonoidHom (GaloisField p n))))
  have hψ : ∀ a, ψ a = ((e.symm (g * mk (unip (Multiplicative.toAdd a)) * g⁻¹) : K) : Y) :=
    fun a => rfl
  refine ⟨ψ, fun a b hab => ?_, ?_, fun μ => ?_⟩
  · rw [hψ, hψ] at hab
    have h := mul_left_cancel (mul_right_cancel (e.symm.injective (Subtype.ext hab)))
    exact Multiplicative.toAdd.injective ((mk_unip_eq_mk_unip_iff h2 _ _).mp h)
  · ext y
    constructor
    · rintro ⟨a, rfl⟩
      rw [hψ, ← hmemV, hmem]
      simpa [mul_assoc] using mk_unip_mem_unipotent (Multiplicative.toAdd a)
    · intro hy
      obtain ⟨t, ht⟩ := (mem_unipotent_iff_exists _).mp
        ((hmem (e ⟨y, hUK hy⟩)).mp ((hmemV _).mpr (by simpa using hy)))
      refine ⟨Multiplicative.ofAdd t, ?_⟩
      rw [hψ, toAdd_ofAdd, ← ht]
      simp [mul_assoc]
  ·
    refine ⟨((e.symm (g * mk (diag μ) * g⁻¹) : K) : Y), (e.symm _).2, fun a => ?_⟩
    rw [hψ, hψ, toAdd_ofAdd, ← Subgroup.coe_inv, ← Subgroup.coe_mul, ← Subgroup.coe_mul,
      ← map_inv, ← map_mul, ← map_mul, ← diag_conj_unip, ← mk_conj]
    congr 2
    group

end CFSG.AGLEmbedding
