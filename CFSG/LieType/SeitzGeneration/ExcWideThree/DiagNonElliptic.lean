module

public import CFSG.LieType.SeitzGeneration.ExcHighThree.NonEllipticCore
public import CFSG.LieType.SeitzGeneration.ExcWideThree.DiagKill

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.Torality CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem conjHom_apply {G : Type*} [Group G] (g x : G) :
    (MulAut.conj g).toMonoidHom x = g * x * g⁻¹ := rfl

section NonElliptic


theorem exists_normalized_rGroup_of_fixed {K : Type} [Field K] [Finite K] (hp : ringChar K ≠ 3)
    {A : Subgroup (ModGL Tag.E6 K)}
    (hA : A ≤ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)))
    (D : LangGLData Tag.E6 K A) (l : Fin Tag.E6.rank → ℤ) (hl : l ≠ 0)
    (hfix : ∀ v : Fin Tag.E6.rank → ℤ, ∑ i, l i * (D.w • v) i = ∑ i, l i * v i) :
    ∃ R : Subgroup (ModGL Tag.E6 K), R ≤ adjointGroup Tag.E6 K ∧ R ≠ ⊥ ∧
      IsPGroup (ringChar K) R ∧ ∀ y ∈ A, ∀ z ∈ R, y * z * y⁻¹ ∈ R := by
  classical
  obtain ⟨e, he, hcard⟩ := card_eq_pow_ringChar K
  haveI : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K (ringChar K)⟩
  set L := AlgebraicClosure K with hL
  set ι : K →+* L := algebraMap K L with hι
  obtain ⟨m, hm, hVcomm, hVpow, v, hvV, hvF, hv1⟩ :=
    exists_nonelliptic_cycle_element (L := L) (ringChar K) e he D.w l hl hfix
  set V := rootLevel Tag.E6 L l m with hV
  have hFrEq : D.Fr = iterateFrobenius L (ringChar K) e :=
    RingHom.ext fun c => by rw [D.hFr c, iterateFrobenius_def, hcard]
  have hFrob : ∀ g : ModGL Tag.E6 L,
      Units.map (entrywiseHom D.Fr) g = entrywiseFrobGL Tag.E6 L (ringChar K) e g := by
    intro g
    rw [hFrEq]
  have hg0F : entrywiseFrobGL Tag.E6 L (ringChar K) e D.g0 =
      D.g0 * canonicalRep (coxeterSystem Tag.E6) L D.w := by
    rw [← hFrob]
    exact D.hg0
  have hFvQ : canonicalRep (coxeterSystem Tag.E6) L D.w *
      entrywiseFrobGL Tag.E6 L (ringChar K) e v *
      (canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹ = v := by
    rw [frobTwistGL_apply] at hvF
    exact hvF
  have hFv : entrywiseFrobGL Tag.E6 L (ringChar K) e v =
      (canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹ * v *
        canonicalRep (coxeterSystem Tag.E6) L D.w := by
    calc entrywiseFrobGL Tag.E6 L (ringChar K) e v
        = (canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹ *
            (canonicalRep (coxeterSystem Tag.E6) L D.w *
              entrywiseFrobGL Tag.E6 L (ringChar K) e v *
              (canonicalRep (coxeterSystem Tag.E6) L D.w)⁻¹) *
            canonicalRep (coxeterSystem Tag.E6) L D.w := by group
      _ = _ := by rw [hFvQ]
  have hvadj : v ∈ adjointGroup Tag.E6 L := rootLevel_le_adjoint l m hvV
  have huLad : D.g0 * v * D.g0⁻¹ ∈ adjointGroup Tag.E6 L :=
    mul_mem (mul_mem D.hg0C hvadj) (inv_mem D.hg0C)
  have huLF : Units.map (entrywiseHom D.Fr) (D.g0 * v * D.g0⁻¹) = D.g0 * v * D.g0⁻¹ := by
    rw [hFrob, map_mul, map_mul, map_inv, hg0F, hFv]
    group
  have huL1 : D.g0 * v * D.g0⁻¹ ≠ 1 := by
    intro h
    apply hv1
    calc v = D.g0⁻¹ * (D.g0 * v * D.g0⁻¹) * D.g0 := by group
      _ = 1 := by rw [h]; group
  have huLp : (D.g0 * v * D.g0⁻¹) ^ ringChar K = 1 := by
    rw [conj_pow, hVpow v hvV]
    group
  have hcop : ringChar K ≠ 3 → Nat.Coprime 3 (orderOf (D.g0 * v * D.g0⁻¹)) := by
    intro _
    rw [orderOf_eq_prime huLp huL1]
    exact (Nat.coprime_primes Nat.prime_three (Fact.out : (ringChar K).Prime)).2 (Ne.symm hp)
  obtain ⟨u', hu'mem, hu'eq⟩ := Subgroup.mem_map.1
    (CFSG.HardMathSupport.Malle.SeitzCube.mem_map_baseChange_of_frobenius_fixed_E6 D.Fr D.hFr
      huLad huLF hcop)
  have hinj := baseChangeGL_injective (τ := Tag.E6) ι
  set R₁ : Subgroup (ModGL Tag.E6 K) :=
    adjointGroup Tag.E6 K ⊓ (V.map (MulAut.conj D.g0).toMonoidHom).comap (baseChangeGL ι) with hR₁
  have hu'R₁ : u' ∈ R₁ := by
    refine ⟨hu'mem, Subgroup.mem_comap.2 ?_⟩
    rw [hu'eq]
    exact ⟨v, hvV, by simp [conjHom_apply]⟩
  have hcinv : D.c⁻¹ ∈ Subgroup.normalizer (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) :=
    inv_mem D.hcN
  have hconj_adj : ∀ z ∈ adjointGroup Tag.E6 K, D.c⁻¹ * z * D.c ∈ adjointGroup Tag.E6 K := by
    intro z hz
    have := (Subgroup.mem_normalizer_iff.1 hcinv z).1 hz
    rwa [inv_inv] at this
  refine ⟨R₁.map (MulAut.conj D.c⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    simpa [MulAut.conj_apply] using hconj_adj z hz.1
  · intro h
    have hu : D.c⁻¹ * u' * D.c ∈ R₁.map (MulAut.conj D.c⁻¹).toMonoidHom :=
      ⟨u', hu'R₁, by simp [conjHom_apply]⟩
    rw [h, Subgroup.mem_bot] at hu
    apply huL1
    rw [← hu'eq]
    have : u' = 1 := by
      calc u' = D.c * (D.c⁻¹ * u' * D.c) * D.c⁻¹ := by group
        _ = 1 := by rw [hu]; group
    rw [this, map_one]
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨z, hz, hzg⟩ := g.2
    apply Subtype.ext
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one, ← hzg]
    obtain ⟨-, hzV⟩ := hz
    obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hzV)
    have hzp : z ^ ringChar K = 1 := by
      apply hinj
      rw [map_pow, ← hxz, map_one]
      simp only [conjHom_apply]
      rw [conj_pow, hVpow x hx]
      group
    simp only [conjHom_apply]
    rw [conj_pow, hzp]
    group
  · intro y hy z hz
    obtain ⟨z₁, hz₁, rfl⟩ := hz
    have hy' : D.c * y * D.c⁻¹ ∈ Subgroup.normalizer
        (adjointGroup Tag.E6 K : Set (ModGL Tag.E6 K)) :=
      mul_mem (mul_mem D.hcN (hA hy)) (inv_mem D.hcN)
    refine ⟨(D.c * y * D.c⁻¹) * z₁ * (D.c * y * D.c⁻¹)⁻¹, ⟨?_, Subgroup.mem_comap.2 ?_⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 hy' z₁).1 hz₁.1
      exact this
    ·
      obtain ⟨t, ht, hte⟩ := D.hc y hy
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_of_mem_torusGroup (Subgroup.mem_inf.1 ht).1
      obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.1 (Subgroup.mem_comap.1 hz₁.2)
      rw [map_mul, map_mul, map_inv, ← hte, ← hxz]
      refine ⟨rootDiagUnit Tag.E6 a * x * (rootDiagUnit Tag.E6 a)⁻¹,
        rootLevel_conj_diag a hx, ?_⟩
      simp only [conjHom_apply]
      group
    · simp only [conjHom_apply]
      group

end NonElliptic

end CFSG.LieType.SeitzGeneration.ExcWideThree
