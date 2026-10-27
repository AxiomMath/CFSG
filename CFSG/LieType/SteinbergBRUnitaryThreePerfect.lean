module

public import CFSG.LieType.SteinbergBRUnitaryThreeCore
public import CFSG.LieType.SteinbergBRTriangularSolvable

public section

namespace CFSG.LieType.SteinbergBR

open Matrix Module CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LinearGroups CFSG.LieType.CentralExt CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

theorem eq_bot_of_perfect_of_isSolvable {G : Type*} [Group G] {B : Subgroup G}
    (hB : ⁅B, B⁆ = B) [Group.IsSolvable B] : B = ⊥ := by
  have htop : commutator B = ⊤ := by
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_subtype_commutator, hB, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hder : ∀ n, derivedSeries B n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, htop]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := B)
  rw [hder] at hn
  rw [eq_bot_iff]
  intro x hx
  have hx' : (⟨x, hx⟩ : B) ∈ (⊥ : Subgroup B) := hn ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hx' ⊢
  exact congrArg Subtype.val hx'

@[expose] def unitaryToSL : unitarySU p f K 3 →* SpecialLinearGroup (Fin 3) K where
  toFun g := ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K), ((mem_unitarySU_iff h).1 g.2).1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem unitaryToSL_injective : Function.Injective (unitaryToSL h) := fun _ _ e =>
  Subtype.ext (Units.ext (congrArg Subtype.val e))

theorem map_mulVecLin_eq {g : GL (Fin 3) K} {J : Submodule K (Fin 3 → K)}
    (h1 : ∀ v ∈ J, g • v ∈ J) (h2 : ∀ v ∈ J, g⁻¹ • v ∈ J) :
    J.map (mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) = J := by
  refine le_antisymm ?_ fun v hv => ⟨g⁻¹ • v, h2 v hv, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact h1 v hv
  · rw [mulVecLin_apply]
    exact smul_inv_smul g v

theorem not_dvd_card_of_le_unitaryScalars {G : Type*} [Group G]
    {φ : unitarySU p f K 3 →* G} (hker : φ.ker ≤ unitaryScalars h 3) : ¬ p ∣ Nat.card φ.ker := by
  intro hdvd
  have := h.finite
  have h1 : Nat.card φ.ker ∣ Nat.card (unitaryScalars h 3) := Subgroup.card_dvd_of_le hker
  rw [card_unitaryScalars h (by norm_num)] at h1
  have h2 : p ∣ p ^ f + 1 := (hdvd.trans h1).trans (Nat.gcd_dvd_right _ _)
  have h3 : p ∣ p ^ f := dvd_pow_self p (by have := h.one_le; omega)
  have h4 : p ∣ 1 := (Nat.dvd_add_right h3).1 h2
  exact h.prime.one_lt.ne' (Nat.dvd_one.1 h4)

theorem eq_bot_of_perfect_of_le_unitaryScalars {A : Type*} [Group A]
    (φ : unitarySU p f K 3 →* A) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ unitaryScalars h 3) {B N : Subgroup A} (hB : ⁅B, B⁆ = B) (hNB : N ≤ B)
    (hNn : (N.subgroupOf B).Normal) (hNp : IsPGroup p N) : N = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have := h.finite
  by_contra hN
  have hcen : φ.ker ≤ Subgroup.center (unitarySU p f K 3) :=
    hker.trans (unitaryScalars_le_center h 3)
  have hC := not_dvd_card_of_le_unitaryScalars h hker
  set U := liftSubgroup p φ N with hU
  have hUp : IsPGroup p U := liftSubgroup_isPGroup hcen hNp
  have hU1 : U ≠ ⊥ := by
    intro hbot
    apply hN
    apply Subgroup.eq_bot_of_card_eq
    rw [← Nat.card_congr (liftSubgroupEquiv hφ hcen hC hNp).toEquiv, ← hU, hbot,
      Subgroup.card_bot]
  have hnorm : ∀ g ∈ B.comap φ, ∀ e ∈ U, g * e * g⁻¹ ∈ U := by
    intro g hg e he
    obtain ⟨he1, n, hn⟩ := (mem_liftSubgroup_iff hcen hNp).1 he
    refine (mem_liftSubgroup_iff hcen hNp).2 ⟨?_, n, ?_⟩
    · have hconj := hNn.conj_mem ⟨φ e, hNB he1⟩ (by rw [Subgroup.mem_subgroupOf]; exact he1)
        ⟨φ g, hg⟩
      rw [Subgroup.mem_subgroupOf] at hconj
      rw [map_mul, map_mul, map_inv]
      exact hconj
    · rw [← hn]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective e
  obtain ⟨J, J₂, hJJ, hJ1, hJ2, hinv⟩ := exists_flag_of_isPGroup h
    (U := U.map (unitarySU p f K 3).subtype) (Subgroup.map_subtype_le U) (hUp.map _)
    (fun hbot => hU1 ((Subgroup.map_eq_bot_iff_of_injective _
      (unitarySU p f K 3).subtype_injective).1 hbot))
  have hgl : ∀ g ∈ B.comap φ, ∀ u ∈ U.map (unitarySU p f K 3).subtype,
      (g : GL (Fin 3) K) * u * (g : GL (Fin 3) K)⁻¹ ∈ U.map (unitarySU p f K 3).subtype := by
    rintro g hg _ ⟨e, he, rfl⟩
    exact ⟨g * e * g⁻¹, hnorm g hg e he, rfl⟩
  have hstab : ∀ g ∈ B.comap φ, unitaryToSL h g ∈ stabilizer J ⊓ stabilizer J₂ := by
    intro g hg
    have hgi : ((g⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) = (g : GL (Fin 3) K)⁻¹ := rfl
    have hc2 : ∀ u ∈ U.map (unitarySU p f K 3).subtype,
        (g : GL (Fin 3) K)⁻¹ * u * (g : GL (Fin 3) K) ∈ U.map (unitarySU p f K 3).subtype := by
      intro u hu
      have e := hgl g⁻¹ (inv_mem hg) u hu
      rwa [hgi, inv_inv] at e
    have h1 := hinv g g.2 (hgl g hg) hc2
    have h2 := hinv (g : GL (Fin 3) K)⁻¹ (inv_mem g.2)
      (fun u hu => by rw [inv_inv]; exact hc2 u hu)
      (fun u hu => by rw [inv_inv]; exact hgl g hg u hu)
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact mem_stabilizer.2 (map_mulVecLin_eq h1.1 h2.1)
    · exact mem_stabilizer.2 (map_mulVecLin_eq h1.2 h2.2)
  let ψ : B.comap φ →* (stabilizer J ⊓ stabilizer J₂ :
      Subgroup (SpecialLinearGroup (Fin 3) K)) :=
    ((unitaryToSL h).comp (B.comap φ).subtype).codRestrict _ fun g => hstab g g.2
  have hψ : Function.Injective ψ := fun x y e =>
    Subtype.ext (unitaryToSL_injective h (congrArg Subtype.val e))
  have := isSolvable_stabilizer_inf_stabilizer h.prime h.card hJJ hJ1 hJ2
  have : Group.IsSolvable (B.comap φ) := Group.isSolvable_of_isSolvable_injective hψ
  have hBs : Group.IsSolvable ((B.comap φ).map φ) :=
    Group.isSolvable_of_surjective (φ.subgroupMap_surjective (B.comap φ))
  rw [Subgroup.map_comap_eq_self_of_surjective hφ] at hBs
  exact hN (le_bot_iff.1 (hNB.trans (eq_bot_of_perfect_of_isSolvable hB).le))

end CFSG.LieType.SteinbergBR

namespace CFSG.LieType

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial SteinbergBR

variable {p f : ℕ} {K : Type} [Field K]

theorem unitary_three_perfect_defining_prime_core_trivial (h : UnitaryFieldData p f K)
    (D : Subgroup (unitarySU p f K 3)) [D.Normal] (hD : D ≤ unitaryScalars h 3)
    {B N : Subgroup (unitarySU p f K 3 ⧸ D)} (hB : ⁅B, B⁆ = B) (hNB : N ≤ B)
    (hNn : (N.subgroupOf B).Normal) (hNp : IsPGroup p N) : N = ⊥ :=
  eq_bot_of_perfect_of_le_unitaryScalars h (QuotientGroup.mk' D) (QuotientGroup.mk'_surjective D)
    (by rw [QuotientGroup.ker_mk']; exact hD) hB hNB hNn hNp

end CFSG.LieType
