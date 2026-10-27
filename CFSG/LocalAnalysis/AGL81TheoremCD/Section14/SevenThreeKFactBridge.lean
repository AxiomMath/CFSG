module

public import CFSG.Open.StatedDefs

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin

open CFSG.Open

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {K : Type} [Field K]
variable {H : Subgroup (GL ι K)}

private abbrev projHom (H : Subgroup (GL ι K)) : H →* StatedProj H :=
  QuotientGroup.mk' ((StatedScalars ι K).subgroupOf H)

private def preimageSubgroup {S : Type} [Group S] (e : S ≃* StatedProj H)
    (I : Subgroup S) : Subgroup (GL ι K) :=
  ((I.map e.toMonoidHom).comap (projHom H)).map H.subtype

private lemma preimageSubgroup_le {S : Type} [Group S] (e : S ≃* StatedProj H)
    (I : Subgroup S) : preimageSubgroup e I ≤ H :=
  Subgroup.map_subtype_le _

private def liftHom {S : Type} [Group S] (e : S ≃* StatedProj H) (I : Subgroup S) :
    preimageSubgroup e I →* I :=
  { toFun := fun x =>
      ⟨e.symm (projHom H ⟨x.1, preimageSubgroup_le e I x.2⟩), by
        have hx : projHom H ⟨x.1, preimageSubgroup_le e I x.2⟩ ∈
            I.map e.toMonoidHom := by
          obtain ⟨h, hh, hxeq⟩ := Subgroup.mem_map.mp x.2
          rw [show (⟨x.1, preimageSubgroup_le e I x.2⟩ : H) = h from
            Subtype.ext hxeq.symm]
          exact (Subgroup.mem_comap).mp hh
        exact (Subgroup.mem_map_iff_mem (f := e.toMonoidHom) e.injective).mp
          (by simpa using hx)⟩
    map_one' := Subtype.ext (by
      show e.symm (projHom H ⟨(1 : preimageSubgroup e I).1,
        preimageSubgroup_le e I (1 : preimageSubgroup e I).2⟩) = (1 : S)
      rw [show (⟨(1 : preimageSubgroup e I).1,
          preimageSubgroup_le e I (1 : preimageSubgroup e I).2⟩ : H) = 1 from
          Subtype.ext rfl, map_one, map_one])
    map_mul' := fun x y => Subtype.ext (by
      show e.symm (projHom H ⟨(x * y).1,
          preimageSubgroup_le e I (x * y).2⟩) =
        e.symm (projHom H ⟨x.1, preimageSubgroup_le e I x.2⟩) *
          e.symm (projHom H ⟨y.1, preimageSubgroup_le e I y.2⟩)
      rw [show (⟨(x * y).1, preimageSubgroup_le e I (x * y).2⟩ : H) =
        ⟨x.1, preimageSubgroup_le e I x.2⟩ *
          ⟨y.1, preimageSubgroup_le e I y.2⟩ from Subtype.ext rfl]
      simp only [map_mul]) }

private lemma liftHom_apply {S : Type} [Group S] (e : S ≃* StatedProj H)
    (I : Subgroup S) (x : preimageSubgroup e I) :
    ((liftHom e I x : I) : S) =
      e.symm (projHom H ⟨x.1, preimageSubgroup_le e I x.2⟩) :=
  rfl

private lemma liftHom_surjective {S : Type} [Group S] (e : S ≃* StatedProj H)
    (I : Subgroup S) : Function.Surjective (liftHom e I) := by
  intro i
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective
    ((StatedScalars ι K).subgroupOf H) (e i)
  have hh' : projHom H h = e i := by simpa [projHom] using hh
  have hmem : h ∈ (I.map e.toMonoidHom).comap (projHom H) := by
    rw [Subgroup.mem_comap, hh']
    exact Subgroup.mem_map_of_mem e.toMonoidHom i.2
  let x : preimageSubgroup e I :=
    ⟨H.subtype h, Subgroup.mem_map_of_mem H.subtype hmem⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  rw [liftHom_apply,
    show (⟨x.1, preimageSubgroup_le e I x.2⟩ : H) = h from Subtype.ext rfl, hh',
    MulEquiv.symm_apply_apply]

private lemma eq_one_of_orderOf_eq_three {S : Type} [Group S] (e : S ≃* StatedProj H)
    (I : Subgroup S) (hsc : ∀ g ∈ H, g ∈ StatedScalars ι K → g ^ 3 = 1 → g = 1)
    {Q : Subgroup I} (hQ : IsPGroup 2 Q) (g : preimageSubgroup e I)
    (hgord : orderOf g = 3) (hQmem : liftHom e I g ∈ Q) : g = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨liftHom e I g, hQmem⟩
  have hpow2 : orderOf (liftHom e I g) = 2 ^ n :=
    (Subgroup.orderOf_coe ⟨liftHom e I g, hQmem⟩).trans hn
  have hord_dvd : orderOf (liftHom e I g) ∣ 3 := by
    rw [← hgord]
    exact orderOf_map_dvd (liftHom e I) g
  have hone : orderOf (liftHom e I g) = 1 := by
    refine Nat.eq_one_of_dvd_coprimes (a := 2 ^ n) (b := 3) ?_ ?_ hord_dvd
    · exact (Nat.coprime_two_left.mpr (by norm_num : Odd 3)).pow_left n
    · rw [hpow2]
  have hg1 : liftHom e I g = 1 := orderOf_eq_one_iff.mp hone
  have hπ : projHom H ⟨g.1, preimageSubgroup_le e I g.2⟩ = 1 := by
    have h := congrArg e (liftHom_apply e I g)
    simp only [hg1, Subgroup.coe_one, map_one, MulEquiv.apply_symm_apply] at h
    exact h.symm
  have hscalar : g.1 ∈ StatedScalars ι K := by
    have hHker : (⟨g.1, preimageSubgroup_le e I g.2⟩ : H) ∈ (projHom H).ker := by
      rw [MonoidHom.mem_ker]
      exact hπ
    have hker : (projHom H).ker = (StatedScalars ι K).subgroupOf H :=
      QuotientGroup.ker_mk' _
    rw [hker, Subgroup.mem_subgroupOf] at hHker
    exact hHker
  have hg3 : (g : GL ι K) ^ 3 = 1 := by
    have h : g ^ 3 = 1 := by
      rw [← hgord]
      exact pow_orderOf_eq_one g
    have h' := congrArg (fun y : preimageSubgroup e I => (y : GL ι K)) h
    simpa using h'
  have hone_gl : g.1 = 1 := hsc g.1 (preimageSubgroup_le e I g.2) hscalar hg3
  exact Subtype.ext hone_gl

theorem exists_subgroup_surjective_of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] [Finite K] {H : Subgroup (GL ι K)}
    (hsc : ∀ g ∈ H, g ∈ StatedScalars ι K → g ^ 3 = 1 → g = 1)
    {S : Type} [Group S] (e : S ≃* StatedProj H) (I : Subgroup S)
    (φ : I →* alternatingGroup (Fin 9)) (hφ : Function.Surjective φ)
    (hker : IsPGroup 2 φ.ker) :
    ∃ (X : Subgroup (GL ι K)) (ψ : X →* alternatingGroup (Fin 9)),
      X ≤ H ∧ Function.Surjective ψ ∧ ¬ 3 ∣ Nat.card ψ.ker := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let ψ : preimageSubgroup e I →* alternatingGroup (Fin 9) := φ.comp (liftHom e I)
  refine ⟨preimageSubgroup e I, ψ, preimageSubgroup_le e I, ?_, ?_⟩
  · exact hφ.comp (liftHom_surjective e I)
  · intro hdiv
    obtain ⟨g, hgord⟩ := exists_prime_orderOf_dvd_card' (G := ψ.ker) 3 hdiv
    have hψg : ψ g.1 = 1 := MonoidHom.mem_ker.mp g.2
    have hφg : liftHom e I g.1 ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hψg
    have hgordX : orderOf g.1 = 3 := by
      rw [Subgroup.orderOf_coe g, hgord]
    have hone : g.1 = 1 :=
      eq_one_of_orderOf_eq_three e I hsc hker g.1 hgordX hφg
    have h1 : orderOf g.1 = 1 := by rw [hone, orderOf_one]
    omega

end CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A9Lin
