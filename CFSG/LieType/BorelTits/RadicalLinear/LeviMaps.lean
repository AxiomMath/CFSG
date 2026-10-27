module

public import CFSG.LieType.BorelTits.RadicalLinear.Levels
public import CFSG.LieType.BorelTits.RadicalLinear.Blocks
public import CFSG.LieType.BorelTits.RadicalLinear.ProjectiveLinear

public section

namespace CFSG.LieType.BorelTits.RadicalLinear

open Matrix CFSG.StandardType.GGOppRad

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : Type*} [Field K] [Finite K]
  {G : Type*} [Group G]

abbrev leviN (U : Subgroup G) : Subgroup G := Subgroup.normalizer (U : Set G)

abbrev leviX (U : Subgroup G) : Type _ := ↥(leviN U) ⧸ U.subgroupOf (leviN U)

noncomputable abbrev leviP (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) :
    Subgroup (SpecialLinearGroup ι K) :=
  (stdP (K := K) ℓ).map (MulAut.conj g).toMonoidHom

noncomputable abbrev leviU (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) :
    Subgroup (SpecialLinearGroup ι K) :=
  (stdU (K := K) ℓ).map (MulAut.conj g).toMonoidHom

@[expose] noncomputable def leviTheta (π : SpecialLinearGroup ι K →* G) (U : Subgroup G) (ℓ : ι → ℕ)
    (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g) :
    leviP ℓ g →* leviX U :=
  (QuotientGroup.mk' (U.subgroupOf (leviN U))).comp
    ((π.comp (leviP ℓ g).subtype).codRestrict (leviN U) fun p => by
      show π (p : SpecialLinearGroup ι K) ∈ leviN U
      exact Subgroup.mem_comap.mp (by rw [hP]; exact p.2))

theorem leviTheta_apply (π : SpecialLinearGroup ι K →* G) (U : Subgroup G) (ℓ : ι → ℕ)
    (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g) (p : leviP ℓ g) :
    leviTheta π U ℓ g hP p =
      QuotientGroup.mk' (U.subgroupOf (leviN U))
        ⟨π p.val, Subgroup.mem_comap.mp (hP.symm ▸ p.2)⟩ :=
  rfl

@[expose] noncomputable def leviInner (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) :
    leviP ℓ g →* stdP (K := K) ℓ :=
  ((MulAut.conj g).symm.toMonoidHom.comp (leviP ℓ g).subtype).codRestrict (stdP ℓ)
    fun p => Subgroup.mem_map_equiv.mp p.2

theorem leviInner_apply (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (p : leviP ℓ g) :
    ((leviInner ℓ g p : stdP (K := K) ℓ) : SpecialLinearGroup ι K) =
      (MulAut.conj g).symm p.val :=
  rfl

@[expose] noncomputable def leviF (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (x : ℕ) :
    leviP ℓ g →* PGL (Block ℓ x) K :=
  (QuotientGroup.mk' (Subgroup.center (GL (Block ℓ x) K))).comp
    ((blockHom ℓ x).comp (leviInner ℓ g))

theorem leviF_apply (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (x : ℕ) (p : leviP ℓ g) :
    leviF ℓ g x p =
      QuotientGroup.mk' (Subgroup.center (GL (Block ℓ x) K))
        (blockHom ℓ x (leviInner ℓ g p)) :=
  rfl

theorem leviTheta_surjective (π : SpecialLinearGroup ι K →* G) (U : Subgroup G) (ℓ : ι → ℕ)
    (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g)
    (hπ : Function.Surjective π) : Function.Surjective (leviTheta π U ℓ g hP) := by
  intro x
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective (U.subgroupOf (leviN U)) x
  obtain ⟨s, hs⟩ := hπ (n : G)
  have hsP : s ∈ leviP ℓ g := by
    rw [← hP]
    exact Subgroup.mem_comap.mpr (hs ▸ n.2)
  refine ⟨⟨s, hsP⟩, ?_⟩
  rw [leviTheta_apply]
  rw [show (⟨π s, _⟩ : ↥(leviN U)) = n from Subtype.ext hs]

theorem leviTheta_ker_le_leviF_ker (π : SpecialLinearGroup ι K →* G) (U : Subgroup G)
    (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g)
    (hU : U = (leviU ℓ g).map π) (hker : π.ker = Subgroup.center (SpecialLinearGroup ι K))
    (x : ℕ) : (leviTheta π U ℓ g hP).ker ≤ (leviF ℓ g x).ker := by
  intro p hp
  rw [MonoidHom.mem_ker] at hp ⊢
  have hmemU : π p.val ∈ U := by
    have h1 := hp
    rw [leviTheta_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_subgroupOf.mp h1
  have hp_sup : p.val ∈ leviU ℓ g ⊔ Subgroup.center (SpecialLinearGroup ι K) := by
    have h2 : p.val ∈ ((leviU ℓ g).map π).comap π := by
      rw [Subgroup.mem_comap, ← hU]
      exact hmemU
    rwa [Subgroup.comap_map_eq, hker] at h2
  obtain ⟨u, hu, z, hz, huz⟩ := Subgroup.mem_sup_of_normal_right.mp hp_sup
  set u' : SpecialLinearGroup ι K := (MulAut.conj g).symm u with hu'def
  set z' : SpecialLinearGroup ι K := (MulAut.conj g).symm z with hz'def
  have hu' : u' ∈ stdU (K := K) ℓ := by
    rw [hu'def]
    exact Subgroup.mem_map_equiv.mp hu
  have hz'c : z' ∈ Subgroup.center (SpecialLinearGroup ι K) := by
    rw [hz'def]
    have h := Subgroup.map_center_eq
      ((MulAut.conj g).symm : SpecialLinearGroup ι K ≃* SpecialLinearGroup ι K)
    rw [← h]
    exact Subgroup.mem_map_of_mem _ hz
  have huP : u' ∈ stdP (K := K) ℓ := stdU_le_stdP ℓ hu'
  have hzP : z' ∈ stdP (K := K) ℓ := center_le_stdP ℓ hz'c
  have hcoe : ((leviInner ℓ g p : stdP (K := K) ℓ) : SpecialLinearGroup ι K) = u' * z' := by
    rw [leviInner_apply, huz.symm, map_mul]
  have hb : leviInner ℓ g p = ⟨u', huP⟩ * ⟨z', hzP⟩ :=
    Subtype.ext (by simpa using hcoe)
  rw [leviF_apply, hb, map_mul]
  have hbu : blockHom ℓ x ⟨u', huP⟩ = 1 :=
    (mem_stdU_iff_blockHom_eq_one ⟨u', huP⟩).mp (by simpa using hu') x
  have hbz : blockHom ℓ x ⟨z', hzP⟩ ∈ Subgroup.center (GL (Block ℓ x) K) :=
    blockHom_mem_center x ⟨z', hzP⟩ hz'c
  rw [hbu, one_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hbz

theorem leviBlock_central (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (p : leviP ℓ g) {x : ℕ}
    (hp : leviF ℓ g x p = 1) :
    blockHom ℓ x (leviInner ℓ g p) ∈ Subgroup.center (GL (Block ℓ x) K) := by
  have h1 := hp
  rw [leviF_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem leviInner_commutator_mem_stdU (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K)
    (p q : leviP ℓ g)
    (hp : ∀ i : Fin (levelsCard ℓ), leviF ℓ g (levels ℓ i) p = 1)
    (hq : ∀ i : Fin (levelsCard ℓ), leviF ℓ g (levels ℓ i) q = 1) :
    ((leviInner ℓ g p * leviInner ℓ g q * (leviInner ℓ g p)⁻¹ * (leviInner ℓ g q)⁻¹ :
        stdP (K := K) ℓ) : SpecialLinearGroup ι K) ∈ stdU (K := K) ℓ := by
  set P' : stdP (K := K) ℓ := leviInner ℓ g p with hP'
  set Q' : stdP (K := K) ℓ := leviInner ℓ g q with hQ'
  have hPc : ∀ i : Fin (levelsCard ℓ),
      blockHom ℓ (levels ℓ i) P' ∈ Subgroup.center (GL (Block ℓ (levels ℓ i)) K) := by
    intro i
    have h := leviBlock_central ℓ g p (hp i)
    simpa using h
  have hQc : ∀ i : Fin (levelsCard ℓ),
      blockHom ℓ (levels ℓ i) Q' ∈ Subgroup.center (GL (Block ℓ (levels ℓ i)) K) := by
    intro i
    have h := leviBlock_central ℓ g q (hq i)
    simpa using h
  set C' : stdP (K := K) ℓ := P' * Q' * P'⁻¹ * Q'⁻¹ with hC'
  have hmem : ((C' : stdP (K := K) ℓ) : SpecialLinearGroup ι K) ∈ stdU (K := K) ℓ := by
    refine (mem_stdU_iff_blockHom_eq_one C').mpr fun x => ?_
    by_cases hne : Nonempty (Block ℓ x)
    · obtain ⟨a⟩ := hne
      obtain ⟨i, hi⟩ := exists_levels_eq ℓ a.1
      have hx : levels ℓ i = x := hi.trans a.2
      have hPx : blockHom ℓ x P' ∈ Subgroup.center (GL (Block ℓ x) K) := by
        rw [← hx]
        exact hPc i
      have hQx : blockHom ℓ x Q' ∈ Subgroup.center (GL (Block ℓ x) K) := by
        rw [← hx]
        exact hQc i
      have hAB : blockHom ℓ x P' * blockHom ℓ x Q' =
          blockHom ℓ x Q' * blockHom ℓ x P' :=
        ((Subgroup.mem_center_iff.mp hPx) (blockHom ℓ x Q')).symm
      rw [hC']
      simp only [map_mul, map_inv]
      rw [hAB]
      group
    · haveI : IsEmpty (Block ℓ x) := not_nonempty_iff.mp hne
      haveI : Subsingleton (Matrix (Block ℓ x) (Block ℓ x) K) :=
        Matrix.subsingleton_of_empty_left
      exact Subsingleton.elim _ _
  simpa only [hP', hQ', hC'] using hmem

@[expose] noncomputable def leviPsi (π : SpecialLinearGroup ι K →* G) (U : Subgroup G)
    (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g)
    (hθ : Function.Surjective (leviTheta π U ℓ g hP)) (x : ℕ)
    (hx : (leviTheta π U ℓ g hP).ker ≤ (leviF ℓ g x).ker) :
    leviX U →* PGL (Block ℓ x) K :=
  (QuotientGroup.lift (leviTheta π U ℓ g hP).ker (leviF ℓ g x) hx).comp
    (QuotientGroup.liftEquiv (leviTheta π U ℓ g hP).ker hθ rfl).symm.toMonoidHom

theorem leviPsi_apply (π : SpecialLinearGroup ι K →* G) (U : Subgroup G)
    (ℓ : ι → ℕ) (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g)
    (hθ : Function.Surjective (leviTheta π U ℓ g hP)) (x : ℕ)
    (hx : (leviTheta π U ℓ g hP).ker ≤ (leviF ℓ g x).ker) (p : leviP ℓ g) :
    leviPsi π U ℓ g hP hθ x hx (leviTheta π U ℓ g hP p) = leviF ℓ g x p := by
  have hsymm : (QuotientGroup.liftEquiv (leviTheta π U ℓ g hP).ker hθ rfl).symm
        (leviTheta π U ℓ g hP p) =
      QuotientGroup.mk' (leviTheta π U ℓ g hP).ker p := by
    apply (QuotientGroup.liftEquiv (leviTheta π U ℓ g hP).ker hθ rfl).injective
    rw [MulEquiv.apply_symm_apply, QuotientGroup.mk'_apply, QuotientGroup.liftEquiv_mk]
  rw [leviPsi]
  change (QuotientGroup.lift (leviTheta π U ℓ g hP).ker (leviF ℓ g x) hx)
      ((QuotientGroup.liftEquiv (leviTheta π U ℓ g hP).ker hθ rfl).symm
        (leviTheta π U ℓ g hP p)) = leviF ℓ g x p
  rw [hsymm, QuotientGroup.mk'_apply, QuotientGroup.lift_mk']

theorem leviTheta_comm (π : SpecialLinearGroup ι K →* G) (U : Subgroup G) (ℓ : ι → ℕ)
    (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g)
    (hU : U = (leviU ℓ g).map π)
    {p q : leviP ℓ g}
    (hp : ∀ i : Fin (levelsCard ℓ), leviF ℓ g (levels ℓ i) p = 1)
    (hq : ∀ i : Fin (levelsCard ℓ), leviF ℓ g (levels ℓ i) q = 1) :
    leviTheta π U ℓ g hP p * leviTheta π U ℓ g hP q =
      leviTheta π U ℓ g hP q * leviTheta π U ℓ g hP p := by
  set P' : stdP (K := K) ℓ := leviInner ℓ g p with hP'
  set Q' : stdP (K := K) ℓ := leviInner ℓ g q with hQ'
  set C' : stdP (K := K) ℓ := P' * Q' * P'⁻¹ * Q'⁻¹ with hC'
  set C : leviP ℓ g := p * q * p⁻¹ * q⁻¹ with hC
  have hC'stdU : ((C' : stdP (K := K) ℓ) : SpecialLinearGroup ι K) ∈ stdU (K := K) ℓ := by
    rw [hC']
    simpa only [← hP', ← hQ'] using leviInner_commutator_mem_stdU ℓ g p q hp hq
  have hinnerC : leviInner ℓ g C = C' := by
    rw [hC, hC']
    simp only [map_mul, map_inv, ← hP', ← hQ']
  have hcoeC : (C : SpecialLinearGroup ι K) =
      MulAut.conj g (C' : SpecialLinearGroup ι K) := by
    have h : (MulAut.conj g).symm (C : SpecialLinearGroup ι K) =
        (C' : SpecialLinearGroup ι K) := by
      rw [← leviInner_apply, hinnerC]
    calc (C : SpecialLinearGroup ι K)
        = MulAut.conj g ((MulAut.conj g).symm (C : SpecialLinearGroup ι K)) :=
          ((MulAut.conj g).apply_symm_apply (C : SpecialLinearGroup ι K)).symm
      _ = MulAut.conj g (C' : SpecialLinearGroup ι K) := by rw [h]
  have hCU : (C : SpecialLinearGroup ι K) ∈ leviU ℓ g := by
    rw [hcoeC, leviU]
    exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hC'stdU
  have hπC : π (C : SpecialLinearGroup ι K) ∈ U := by
    rw [hU]
    exact Subgroup.mem_map_of_mem π hCU
  have hθC : leviTheta π U ℓ g hP C = 1 := by
    rw [leviTheta_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hπC
  have h1 : leviTheta π U ℓ g hP p * leviTheta π U ℓ g hP q *
      (leviTheta π U ℓ g hP p)⁻¹ * (leviTheta π U ℓ g hP q)⁻¹ = 1 := by
    rw [← hθC, hC]
    simp only [map_mul, map_inv]
  calc leviTheta π U ℓ g hP p * leviTheta π U ℓ g hP q
      = (leviTheta π U ℓ g hP p * leviTheta π U ℓ g hP q *
          (leviTheta π U ℓ g hP p)⁻¹ * (leviTheta π U ℓ g hP q)⁻¹) *
          (leviTheta π U ℓ g hP q * leviTheta π U ℓ g hP p) := by group
    _ = 1 * (leviTheta π U ℓ g hP q * leviTheta π U ℓ g hP p) := by rw [h1]
    _ = leviTheta π U ℓ g hP q * leviTheta π U ℓ g hP p := one_mul _

theorem leviPsi_comm (π : SpecialLinearGroup ι K →* G) (U : Subgroup G) (ℓ : ι → ℕ)
    (g : SpecialLinearGroup ι K) (hP : (leviN U).comap π = leviP ℓ g)
    (hU : U = (leviU ℓ g).map π)
    (hθ : Function.Surjective (leviTheta π U ℓ g hP))
    (h3 : ∀ x : ℕ, (leviTheta π U ℓ g hP).ker ≤ (leviF ℓ g x).ker)
    (x y : leviX U)
    (hx : ∀ i : Fin (levelsCard ℓ),
      leviPsi π U ℓ g hP hθ (levels ℓ i) (h3 (levels ℓ i)) x = 1)
    (hy : ∀ i : Fin (levelsCard ℓ),
      leviPsi π U ℓ g hP hθ (levels ℓ i) (h3 (levels ℓ i)) y = 1) :
    x * y = y * x := by
  obtain ⟨p, rfl⟩ := hθ x
  obtain ⟨q, rfl⟩ := hθ y
  have hp : ∀ i : Fin (levelsCard ℓ), leviF ℓ g (levels ℓ i) p = 1 := fun i =>
    (leviPsi_apply π U ℓ g hP hθ (levels ℓ i) (h3 (levels ℓ i)) p).symm.trans (hx i)
  have hq : ∀ i : Fin (levelsCard ℓ), leviF ℓ g (levels ℓ i) q = 1 := fun i =>
    (leviPsi_apply π U ℓ g hP hθ (levels ℓ i) (h3 (levels ℓ i)) q).symm.trans (hy i)
  exact leviTheta_comm π U ℓ g hP hU hp hq

end CFSG.LieType.BorelTits.RadicalLinear
