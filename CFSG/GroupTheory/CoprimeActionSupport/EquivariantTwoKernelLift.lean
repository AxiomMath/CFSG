module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.GroupTheory.CoprimeActionSupport.EquivariantTwoKernelLift

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_equivariant_lift_of_two_kernel
    {L : Subgroup G} {b : G} (hb : b ∈ normalizer (L : Set G))
    {N : Subgroup ↥L} [N.Normal] (hN : IsPGroup 2 N)
    {r q : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    [Fact q.Prime] (hq2 : q ≠ 2)
    {A : Type} [Group A] (hA : IsPGroup q A)
    (ι : A →* (↥L ⧸ N)) (hι : Function.Injective ι) (κ : A →* A)
    (β : MulAut (↥L ⧸ N))
    (hβ : ∀ x : ↥L, β (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (L.normalizerMonoidHom ⟨b, hb⟩ x))
    (hκ : ∀ a, β (ι a) = ι (κ a)) :
    ∃ ψ : A →* G, Function.Injective ψ ∧ (∀ a, ψ a ∈ L) ∧
      ∀ a, b * ψ a * b⁻¹ = ψ (κ a) := by
  classical
  have hq : q.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : ↥L →* (↥L ⧸ N) := QuotientGroup.mk' N
  let U : Subgroup (↥L ⧸ N) := ι.range
  have hUp : IsPGroup q ↥U := hA.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  let E : Subgroup G := (U.comap π).map L.subtype
  have hEL : E ≤ L := Subgroup.map_subtype_le _
  have hbE : b ∈ normalizer (E : Set G) := by
    refine Subgroup.mem_normalizer_fintype ?_
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha⟩ := hx
    refine ⟨L.normalizerMonoidHom ⟨b, hb⟩ x, ⟨κ a, ?_⟩, rfl⟩
    change ι (κ a) = π (L.normalizerMonoidHom ⟨b, hb⟩ x)
    rw [← hβ x, ← ha, hκ]
  have hB : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hbr])
  have hBE : zpowers b ≤ normalizer (E : Set G) := Subgroup.zpowers_le.2 hbE
  have hfE : ∀ x : ↥E, π (Subgroup.inclusion hEL x) ∈ U := by
    rintro ⟨_, y, hy, rfl⟩
    exact hy
  let f : ↥E →* ↥U := (π.comp (Subgroup.inclusion hEL)).codRestrict U hfE
  have hf : Function.Surjective f := by
    rintro ⟨u, hu⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N u
    exact ⟨⟨x, x, hu, rfl⟩, rfl⟩
  have hker : IsPGroup 2 f.ker := by
    have hkerEq : f.ker = N.comap (Subgroup.inclusion hEL) := by
      ext x
      show f x = 1 ↔ Subgroup.inclusion hEL x ∈ N
      rw [← QuotientGroup.eq_one_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [hkerEq]
    exact IsPGroup.comap_of_injective hN _ (Subgroup.inclusion_injective hEL)
  have hnd : ¬ r ∣ Nat.card (Sylow q ↥E) := by
    obtain ⟨P₀⟩ := (Sylow.nonempty : Nonempty (Sylow q ↥E))
    have h1 : Nat.card (Sylow q ↥E) ∣ Nat.card ↥E :=
      (Sylow.card_dvd_index P₀).trans (Subgroup.index_dvd_card _)
    rw [← Subgroup.card_ker_mul_card_of_surjective hf] at h1
    obtain ⟨a, ha⟩ := hker.exists_card_eq
    obtain ⟨k, hk⟩ := hUp.exists_card_eq
    rw [ha, hk] at h1
    have hcop : Nat.Coprime (Nat.card (Sylow q ↥E)) (q ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_comm.1
        ((Nat.Prime.coprime_iff_not_dvd hq).2 (not_dvd_card_sylow q ↥E)))
    have h2 := hcop.dvd_of_dvd_mul_right h1
    intro hr'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1
      (hr.dvd_of_dvd_pow (hr'.trans h2)))
  let φ : ↥(zpowers b) →* MulAut ↥E := E.normalizerMonoidHom.comp (Subgroup.inclusion hBE)
  let : MulDistribMulAction ↥(zpowers b) ↥E := MulDistribMulAction.compHom ↥E φ
  obtain ⟨P, hP⟩ := hB.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q ↥E) hnd
  have hPb : ∀ x ∈ (P : Subgroup ↥E), E.normalizerMonoidHom ⟨b, hbE⟩ x ∈ (P : Subgroup ↥E) := by
    intro x hx
    have h := congrArg (fun Q : Sylow q ↥E => (Q : Subgroup ↥E))
      (MulAction.mem_fixedPoints.mp hP (⟨b, mem_zpowers b⟩ : ↥(zpowers b)))
    rw [Sylow.pointwise_smul_def] at h
    rw [← h]
    exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2 ⟨x, hx, rfl⟩
  have hdisj : Disjoint (P : Subgroup ↥E) f.ker :=
    IsPGroup.disjoint_of_ne q 2 hq2 _ _ P.isPGroup' hker
  have hinj : ∀ x ∈ (P : Subgroup ↥E), ∀ y ∈ (P : Subgroup ↥E), f x = f y → x = y := by
    intro x hx y hy hxy
    have hxy' : x⁻¹ * y ∈ (P : Subgroup ↥E) ⊓ f.ker :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem hx) hy,
        MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at hxy'
    exact inv_mul_eq_one.1 hxy'
  have hsurj : ∀ u : ↥U, ∃ x ∈ (P : Subgroup ↥E), f x = u := by
    intro u
    have hS : ((P.mapSurjective hf : Sylow q ↥U) : Subgroup ↥U) = ⊤ :=
      ((P.mapSurjective hf).is_maximal' (hUp.to_subgroup ⊤) le_top).symm
    have hu : u ∈ ((P.mapSurjective hf : Sylow q ↥U) : Subgroup ↥U) := by
      rw [hS]
      exact Subgroup.mem_top u
    rw [Sylow.coe_mapSurjective] at hu
    obtain ⟨x, hx, hxu⟩ := hu
    exact ⟨x, hx, hxu⟩
  let ρ : ↥(P : Subgroup ↥E) →* ↥U := f.comp (P : Subgroup ↥E).subtype
  have hρ : Function.Bijective ρ := by
    refine ⟨fun x y hxy => Subtype.ext (hinj x x.2 y y.2 hxy), fun u => ?_⟩
    obtain ⟨x, hx, hxu⟩ := hsurj u
    exact ⟨⟨x, hx⟩, hxu⟩
  let e : ↥(P : Subgroup ↥E) ≃* ↥U := MulEquiv.ofBijective ρ hρ
  let j : A →* ↥(P : Subgroup ↥E) := e.symm.toMonoidHom.comp ι.rangeRestrict
  have hj : ∀ a, f (j a : ↥E) = ι.rangeRestrict a := fun a => e.apply_symm_apply _
  refine ⟨E.subtype.comp ((P : Subgroup ↥E).subtype.comp j), ?_, fun a => hEL (j a : ↥E).2,
    fun a => ?_⟩
  · intro a a' h
    have h1 : (j a : ↥E) = j a' := Subtype.ext h
    have h2 : ι.rangeRestrict a = ι.rangeRestrict a' := by rw [← hj, ← hj, h1]
    exact hι (congrArg Subtype.val h2)
  · have hy : E.normalizerMonoidHom ⟨b, hbE⟩ (j a : ↥E) ∈ (P : Subgroup ↥E) := hPb _ (j a).2
    have hfy : f (E.normalizerMonoidHom ⟨b, hbE⟩ (j a : ↥E)) = f (j (κ a) : ↥E) := by
      rw [hj]
      apply Subtype.ext
      change π (L.normalizerMonoidHom ⟨b, hb⟩ (Subgroup.inclusion hEL (j a : ↥E))) = ι (κ a)
      rw [← hβ (Subgroup.inclusion hEL (j a : ↥E))]
      rw [← hκ]
      congr 1
      exact congrArg Subtype.val (hj a)
    exact congrArg Subtype.val (hinj _ hy _ (j (κ a)).2 hfy)

end CFSG.GroupTheory.CoprimeActionSupport.EquivariantTwoKernelLift
