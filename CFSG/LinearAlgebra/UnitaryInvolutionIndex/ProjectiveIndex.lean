module

public import CFSG.LieType.CentralExt.CoprimeLift
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.AbelianIndex
public import CFSG.LinearAlgebra.UnitaryInvolutionIndex.InvariantAbelian

public section

namespace CFSG.UnitaryInvolutionIndex

open Matrix Module

section Index

variable {G G' : Type*} [Group G] [Group G']

theorem relIndex_centralizer_map_dvd (f : G →* G') (Q : Subgroup G) (s : G) :
    (Q.map f ⊓ Subgroup.centralizer {f s}).relIndex (Q.map f) ∣
      (Q ⊓ Subgroup.centralizer {s}).relIndex Q := by
  set C' := (Q.map f ⊓ Subgroup.centralizer {f s}).subgroupOf (Q.map f)
  have hcomap : (C'.comap (f.subgroupMap Q)).index = C'.index :=
    Subgroup.index_comap_of_surjective C' (f.subgroupMap_surjective Q)
  have hle : (Q ⊓ Subgroup.centralizer {s}).subgroupOf Q ≤ C'.comap (f.subgroupMap Q) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff] at hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    refine ⟨(f.subgroupMap Q x).2, ?_⟩
    change f x * f s = f s * f x
    rw [← map_mul, ← map_mul, hx.2]
  rw [Subgroup.relIndex, Subgroup.relIndex, ← hcomap]
  exact Subgroup.index_dvd_of_le hle

theorem relIndex_centralizer_map_of_injective {f : G →* G'} (hf : Function.Injective f)
    (Q : Subgroup G) (s : G) :
    (Q.map f ⊓ Subgroup.centralizer {f s}).relIndex (Q.map f) =
      (Q ⊓ Subgroup.centralizer {s}).relIndex Q := by
  have hmap : Q.map f ⊓ Subgroup.centralizer {f s} = (Q ⊓ Subgroup.centralizer {s}).map f := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨⟨x, hx, rfl⟩, hxs⟩
      refine ⟨x, ⟨hx, hf ?_⟩, rfl⟩
      rw [map_mul, map_mul, hxs]
    · rintro ⟨x, ⟨hx, hxs⟩, rfl⟩
      exact ⟨⟨x, hx, rfl⟩, by rw [← map_mul, ← map_mul, hxs]⟩
  rw [hmap, Subgroup.relIndex_map_map_of_injective _ _ hf]

theorem relIndex_centralizer_le_mul [Finite G] {Q A : Subgroup G} (hAQ : A ≤ Q) (s : G) :
    (Q ⊓ Subgroup.centralizer {s}).relIndex Q ≤
      (A ⊓ Subgroup.centralizer {s}).relIndex A * A.relIndex Q := by
  rw [Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hAQ]
  refine Nat.le_of_dvd ?_ (Subgroup.relIndex_dvd_of_le_left Q (inf_le_inf_right _ hAQ))
  exact Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero

end Index

variable {F : Type*} [Field F]

theorem relIndex_centralizer_le_of_le_unitaryGroup [Finite F] {q : ℕ} (hq : IsPrimePow q)
    (hF : Nat.card F = q ^ 2) {σ : F →+* F} (hσ : ∀ c, σ c = c ^ q)
    {h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F} (hh : h.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (Q : Subgroup (GL (Fin 3) F)) (hQU : Q ≤ unitaryGroup h)
    (hQ : IsPGroup p Q) (s : GL (Fin 3) F) (hs : s ^ 2 = 1)
    (hsQ : s ∈ Subgroup.normalizer (Q : Set (GL (Fin 3) F))) :
    (Q ⊓ Subgroup.centralizer {s}).relIndex Q ≤ 3 * p ^ (q + 1).factorization p ∧
      (p ≠ 3 → (Q ⊓ Subgroup.centralizer {s}).relIndex Q ≤ p ^ (q + 1).factorization p) := by
  classical
  obtain ⟨ℓ, f, hℓ, hf, hℓq, hchar⟩ := exists_charP_of_card_eq_sq hq hF
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set k := AlgebraicClosure F
  have : CharP k ℓ := charP_of_injective_algebraMap (algebraMap F k).injective ℓ
  obtain ⟨hpℓ, -, -⟩ := prime_facts_of_dvd_succ hp hp2 hℓ hf (hℓq ▸ hpq)
  have hpk : ringChar k ≠ p := by rw [ringChar.eq k ℓ]; exact hpℓ.symm
  set Φ : GL (Fin 3) F →* GL (Fin 3) k := GeneralLinearGroup.map (algebraMap F k)
  have hΦ : Function.Injective Φ := by
    intro g g' hgg'
    apply Units.ext
    ext i j
    have := congrArg (fun x : GL (Fin 3) k => (x : Matrix (Fin 3) (Fin 3) k) i j) hgg'
    simp only [Φ, GeneralLinearGroup.map_apply] at this
    exact (algebraMap F k).injective this
  set Q' := Q.map Φ
  have : Finite Q' := Finite.of_surjective _ (Φ.subgroupMap_surjective Q)
  have hQ' : IsPGroup p Q' := hQ.of_surjective _ (Φ.subgroupMap_surjective Q)
  have hs' : Φ s ^ 2 = 1 := by rw [← map_pow, hs, map_one]
  have hsQ' : Φ s ∈ Subgroup.normalizer (Q' : Set (GL (Fin 3) k)) :=
    Subgroup.le_normalizer_map Φ (Subgroup.mem_map_of_mem Φ hsQ)
  obtain ⟨⟨A', hA'Q', -, hA'c, hsA', hA'i⟩, habel⟩ :=
    odd_three_dimensional_invariant_abelian_subgroup hp hp2 hpk Q' hQ' (Φ s) hs' hsQ'
  have hbound : ∀ A : Subgroup (GL (Fin 3) F), A ≤ Q → IsMulCommutative A →
      s ∈ Subgroup.normalizer (A : Set (GL (Fin 3) F)) →
      (Q ⊓ Subgroup.centralizer {s}).relIndex Q ≤
        p ^ (q + 1).factorization p * A.relIndex Q := by
    intro A hAQ hAc hsA
    obtain ⟨hidx, -⟩ := unitary_three_abelian_involution_index_bound hq hF hσ hh hp hp2 hpq A
      (hAQ.trans hQU) hAc (hQ.to_le hAQ) s hs hsA
    exact (relIndex_centralizer_le_mul hAQ s).trans (Nat.mul_le_mul_right _ hidx)
  have hcommQ : p ≠ 3 → IsMulCommutative Q := by
    intro hp3
    have := habel hp3
    refine isMulCommutative_iff.mpr fun x y => Subtype.ext (hΦ ?_)
    have hxy := mul_comm' (⟨Φ x, Subgroup.mem_map_of_mem Φ x.2⟩ : Q')
      ⟨Φ y, Subgroup.mem_map_of_mem Φ y.2⟩
    have := congrArg Subtype.val hxy
    simpa only [Subgroup.coe_mul, map_mul] using this
  refine ⟨?_, fun hp3 => ?_⟩
  · set A := A'.comap Φ
    have hAQ : A ≤ Q := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hA'Q' hx
      rwa [hΦ hyx] at hy
    have hAmap : A.map Φ = A' := by
      rw [Subgroup.map_comap_eq, inf_eq_right]
      exact hA'Q'.trans (Subgroup.map_le_range Φ Q)
    have hAc : IsMulCommutative A := by
      refine isMulCommutative_iff.mpr fun x y => Subtype.ext (hΦ ?_)
      have hxy := mul_comm' (⟨Φ x, x.2⟩ : A') ⟨Φ y, y.2⟩
      have := congrArg Subtype.val hxy
      simpa only [Subgroup.coe_mul, map_mul] using this
    have hsA : s ∈ Subgroup.normalizer (A : Set (GL (Fin 3) F)) := by
      refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
      change Φ g ∈ A' ↔ Φ (s * g * s⁻¹) ∈ A'
      rw [map_mul, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp hsA' (Φ g)
    have hAi : A.relIndex Q ≤ 3 := by
      rw [← Subgroup.relIndex_map_map_of_injective _ _ hΦ, hAmap]
      exact hA'i
    calc (Q ⊓ Subgroup.centralizer {s}).relIndex Q
        ≤ p ^ (q + 1).factorization p * A.relIndex Q := hbound A hAQ hAc hsA
      _ ≤ p ^ (q + 1).factorization p * 3 := Nat.mul_le_mul_left _ hAi
      _ = 3 * p ^ (q + 1).factorization p := mul_comm _ _
  · have := hbound Q le_rfl (hcommQ hp3) hsQ
    rwa [Subgroup.relIndex_self, mul_one] at this

variable {σ : F →+* F}

theorem pow_three_eq_one_of_mem_unitaryScalars {h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F}
    {z : specialUnitaryGroup h} (hz : z ∈ unitaryScalars h) : z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := hz
  have hdet := SpecialLinearGroup.det_coe (z : SpecialLinearGroup (Fin 3) F)
  rw [hc, scalar_apply, det_diagonal, Fin.prod_const] at hdet
  apply Subtype.ext
  apply Subtype.ext
  rw [SubgroupClass.coe_pow, SpecialLinearGroup.coe_pow, hc, ← map_pow, hdet, map_one]
  rfl

theorem projective_unitary_three_odd_subgroup_involution_index_bound [Finite F] {q : ℕ}
    (hq : IsPrimePow q) (hF : Nat.card F = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    {h : (Fin 3 → F) →ₛₗ[σ] (Fin 3 → F) →ₗ[F] F} (hh : h.Nondegenerate) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ q + 1) (P : Subgroup (projectiveSpecialUnitaryGroup h))
    (hP : IsPGroup p P) (t : projectiveSpecialUnitaryGroup h) (ht : t ^ 2 = 1)
    (htP : t ∈ Subgroup.normalizer (P : Set (projectiveSpecialUnitaryGroup h))) :
    (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ 3 * p ^ (q + 1).factorization p ∧
      (p ≠ 3 → (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ p ^ (q + 1).factorization p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set S := specialUnitaryGroup h
  set π : S →* projectiveSpecialUnitaryGroup h := QuotientGroup.mk' (unitaryScalars h)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hmemZ : ∀ x : S, π x = 1 ↔ x ∈ unitaryScalars h := fun x => QuotientGroup.eq_one_iff x
  have hcen : π.ker ≤ Subgroup.center S := fun z hz =>
    mem_center_of_mem_unitaryScalars ((hmemZ z).mp (MonoidHom.mem_ker.mp hz))
  obtain ⟨x, hx⟩ := hπ t
  have hx2 : x ^ 2 ∈ unitaryScalars h := (hmemZ _).mp (by rw [map_pow, hx, ht])
  set s := x ^ 3
  have hs : s ^ 2 = 1 := by
    rw [← pow_mul, show 3 * 2 = 2 * 3 by rfl, pow_mul]
    exact pow_three_eq_one_of_mem_unitaryScalars hx2
  have hst : π s = t := by
    rw [map_pow, hx, pow_succ, ht, one_mul]
  set ψ : S →* GL (Fin 3) F := SpecialLinearGroup.toGL.comp S.subtype
  have hψ : Function.Injective ψ := SpecialLinearGroup.toGL_injective.comp S.subtype_injective
  have hψU : ∀ g : S, ψ g ∈ unitaryGroup h := fun g => g.2
  have hS : ∀ Q : Subgroup S, IsPGroup p Q → s ∈ Subgroup.normalizer (Q : Set S) →
      Q.map π = P →
      (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ 3 * p ^ (q + 1).factorization p ∧
        (p ≠ 3 → (P ⊓ Subgroup.centralizer {t}).relIndex P ≤ p ^ (q + 1).factorization p) := by
    intro Q hQ hsQ hQP
    have hQU : Q.map ψ ≤ unitaryGroup h := by
      rintro _ ⟨g, -, rfl⟩
      exact hψU g
    have hQ' : IsPGroup p (Q.map ψ) := hQ.of_surjective _ (ψ.subgroupMap_surjective Q)
    have hsQ' : ψ s ∈ Subgroup.normalizer ((Q.map ψ : Subgroup (GL (Fin 3) F)) :
        Set (GL (Fin 3) F)) :=
      Subgroup.le_normalizer_map ψ (Subgroup.mem_map_of_mem ψ hsQ)
    obtain ⟨h3, h1⟩ := relIndex_centralizer_le_of_le_unitaryGroup hq hF hσ hh hp hp2 hpq
      (Q.map ψ) hQU hQ' (ψ s) (by rw [← map_pow, hs, map_one]) hsQ'
    rw [relIndex_centralizer_map_of_injective hψ] at h3 h1
    have hdvd := relIndex_centralizer_map_dvd π Q s
    rw [hQP, hst] at hdvd
    have hpos : 0 < (Q ⊓ Subgroup.centralizer {s}).relIndex Q :=
      Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
    exact ⟨(Nat.le_of_dvd hpos hdvd).trans h3, fun hp3 => (Nat.le_of_dvd hpos hdvd).trans (h1 hp3)⟩
  by_cases hp3 : p = 3
  · subst hp3
    refine hS (P.comap π) (fun e => ?_) ?_ (Subgroup.map_comap_eq_self_of_surjective hπ P)
    · obtain ⟨n, hn⟩ := hP ⟨π e, e.2⟩
      refine ⟨n + 1, Subtype.ext ?_⟩
      have h1 : π ((e : S) ^ 3 ^ n) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hn
      have h2 := pow_three_eq_one_of_mem_unitaryScalars ((hmemZ _).mp h1)
      rw [SubgroupClass.coe_pow, pow_succ, pow_mul, h2, OneMemClass.coe_one]
    · refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
      change π g ∈ P ↔ π (s * g * s⁻¹) ∈ P
      rw [map_mul, map_mul, map_inv, hst]
      exact Subgroup.mem_normalizer_iff.mp htP (π g)
  · have hC : ¬p ∣ Nat.card π.ker := by
      intro hdvd
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
      have hz3 : (z : S) ^ 3 = 1 :=
        pow_three_eq_one_of_mem_unitaryScalars ((hmemZ z).mp (MonoidHom.mem_ker.mp z.2))
      have h3 : orderOf (z : S) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      rw [Subgroup.orderOf_coe, hz] at h3
      exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3)
    set Q := CFSG.LieType.CentralExt.liftSubgroup p π P
    have hmem : ∀ e, e ∈ Q ↔ π e ∈ P ∧ ∃ n : ℕ, orderOf e = p ^ n := fun e =>
      CFSG.LieType.CentralExt.mem_liftSubgroup_iff hcen hP
    refine hS Q (CFSG.LieType.CentralExt.liftSubgroup_isPGroup hcen hP) ?_ ?_
    · refine Subgroup.mem_normalizer_iff.mpr fun g => ?_
      have hord : orderOf (s * g * s⁻¹) = orderOf g := by
        rw [← MulAut.conj_apply]
        exact orderOf_injective (MulAut.conj s).toMonoidHom (MulAut.conj s).injective g
      rw [hmem, hmem, map_mul, map_mul, map_inv, hst, hord,
        ← Subgroup.mem_normalizer_iff.mp htP (π g)]
    · refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr fun e he => ((hmem e).mp he).1)
        fun u hu => ?_
      exact ⟨_, CFSG.LieType.CentralExt.pLift_mem_liftSubgroup hπ hcen hC hP hu,
        CFSG.LieType.CentralExt.map_pLift hπ hC
          (CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_mem hP ⟨u, hu⟩)⟩

end CFSG.UnitaryInvolutionIndex
