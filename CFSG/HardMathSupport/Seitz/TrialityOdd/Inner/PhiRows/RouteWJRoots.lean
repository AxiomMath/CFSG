module

public import CFSG.RankThree.PartOne.KGD.D4T36Family

set_option linter.unusedSectionVars false

public section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD


section Roots

variable {L : Type} [Field L]

theorem diagramMap_single' (b : Label TwistTag.D4.tag) (r : L) :
    (diagramMap TwistTag.D4 L : Module.End L (RootModule TwistTag.D4.tag L))
      (Finsupp.single b r) =
      Finsupp.single (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm b) r := by
  simp [diagramMap]

theorem labelPerm_d4_cube (b : Label TwistTag.D4.tag) :
    labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm
      (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm
        (labelPerm TwistTag.D4.perm TwistTag.D4.cartan_perm b)) = b := by
  have hc : ∀ i : Fin TwistTag.D4.tag.rank,
      TwistTag.D4.perm (TwistTag.D4.perm (TwistTag.D4.perm i)) = i := by
    have key : ∀ i : Fin 4, (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4))
      ((Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4))
        ((Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) i)) = i := by decide
    exact key
  rcases b with i | ⟨α, hα⟩
  · simp only [labelPerm, Equiv.coe_fn_mk, hc]
  · simp only [labelPerm, Equiv.coe_fn_mk, Sum.inr.injEq, Subtype.mk.injEq]
    ext j
    simp only [permLattice, Function.comp_apply]
    have e : TwistTag.D4.perm.symm (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm j)) = j := by
      have := hc (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm (TwistTag.D4.perm.symm j)))
      simpa only [Equiv.apply_symm_apply] using this.symm
    rw [e]

theorem diagramMap_d4_pow_three : diagramMap TwistTag.D4 L ^ 3 = 1 := by
  apply Units.ext
  apply Finsupp.lhom_ext'
  intro b
  ext l
  simp only [pow_succ, pow_zero, one_mul, Units.val_mul, Units.val_one,
    LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.mul_apply, Module.End.one_apply,
    diagramMap_single', labelPerm_d4_cube]

theorem diagramMap_conj_pinnedX_of_fixed {β : Fin TwistTag.D4.tag.rank → ℤ}
    (hβ : IsRoot TwistTag.D4.tag β) (hfix : permLattice TwistTag.D4.perm β = β) (c : L) :
    diagramMap TwistTag.D4 L * pinnedX TwistTag.D4.tag L β c * (diagramMap TwistTag.D4 L)⁻¹ =
      pinnedX TwistTag.D4.tag L β c := by
  obtain ⟨ε, hε, hP⟩ := diagramMap_conj_pinnedX (K := L) TwistTag.D4 hβ
  rw [hfix] at hP
  have h3 : ∀ c : L, pinnedX TwistTag.D4.tag L β c =
      pinnedX TwistTag.D4.tag L β (ε * ε * ε * c) := fun c => by
    have e : ∀ k : ℕ, diagramMap TwistTag.D4 L ^ k * pinnedX TwistTag.D4.tag L β c *
        (diagramMap TwistTag.D4 L ^ k)⁻¹ = pinnedX TwistTag.D4.tag L β (ε ^ k * c) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have : diagramMap TwistTag.D4 L ^ (k + 1) * pinnedX TwistTag.D4.tag L β c *
            (diagramMap TwistTag.D4 L ^ (k + 1))⁻¹ =
            diagramMap TwistTag.D4 L * (diagramMap TwistTag.D4 L ^ k *
              pinnedX TwistTag.D4.tag L β c * (diagramMap TwistTag.D4 L ^ k)⁻¹) *
              (diagramMap TwistTag.D4 L)⁻¹ := by
          rw [pow_succ', mul_inv_rev]
          group
        rw [this, ih, hP]
        congr 1
        ring
    have := e 3
    rw [diagramMap_d4_pow_three] at this
    simp only [inv_one, one_mul, mul_one] at this
    rw [this]
    congr 1
    ring
  have h1 : ε = 1 := by
    have := pinnedX_injective TwistTag.D4.tag L β (h3 1)
    have e3 : ε * ε * ε = ε := by rw [hε, one_mul]
    rw [e3, mul_one] at this
    exact this.symm
  rw [hP, h1, one_mul]

theorem diagramMap_comm_of_mem_rootSpan_fixed {S : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hS : ∀ β ∈ S, IsRoot TwistTag.D4.tag β ∧ permLattice TwistTag.D4.perm β = β)
    {z : ModGL TwistTag.D4.tag L} (hz : z ∈ rootSpan TwistTag.D4.tag L S) :
    diagramMap TwistTag.D4 L * z = z * diagramMap TwistTag.D4 L := by
  have hle : rootSpan TwistTag.D4.tag L S ≤
      Subgroup.centralizer ({diagramMap TwistTag.D4 L} : Set (ModGL TwistTag.D4.tag L)) := by
    refine iSup₂_le fun β hβ => (Subgroup.closure_le _).2 ?_
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have := diagramMap_conj_pinnedX_of_fixed (L := L) (hS β hβ).1 (hS β hβ).2 c
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hz)).symm

theorem conj_mem_rootSpan_of_monomial_to {n : ModGL TwistTag.D4.tag L}
    (hn : n ∈ monomialSubgroup TwistTag.D4.tag L) {S S' : Set (Fin TwistTag.D4.tag.rank → ℤ)}
    (hS : ∀ γ ∈ S, IsRoot TwistTag.D4.tag γ ∧
      weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ • γ ∈ S') {g : ModGL TwistTag.D4.tag L}
    (hg : g ∈ rootSpan TwistTag.D4.tag L S) : n * g * n⁻¹ ∈ rootSpan TwistTag.D4.tag L S' := by
  have hle : rootSpan TwistTag.D4.tag L S ≤
      (rootSpan TwistTag.D4.tag L S').comap (MulAut.conj n).toMonoidHom := by
    refine iSup₂_le fun γ hγ => ?_
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn (hS γ hγ).1
    change n * pinnedX TwistTag.D4.tag L γ c * n⁻¹ ∈ rootSpan TwistTag.D4.tag L S'
    rw [hμ c]
    exact pinnedX_mem_rootSpan (hS γ hγ).2 _
  exact hle hg

theorem diagramMap_comm_conj_rootSpan_sigma {i : Fin 4} {u : WeylGroup TwistTag.D4.tag}
    (hu : (fun x => u • x) '' {x | IsRoot TwistTag.D4.tag x ∧
      permLattice TwistTag.D4.perm x = x} = d4Sigma i)
    {g₂ : ModGL TwistTag.D4.tag L}
    (hg₂ : diagramMap TwistTag.D4 L * g₂ = g₂ * diagramMap TwistTag.D4 L)
    {z : ModGL TwistTag.D4.tag L} (hz : z ∈ rootSpan TwistTag.D4.tag L (d4Sigma i)) :
    diagramMap TwistTag.D4 L *
        (g₂ * (canonicalRep (coxeterSystem TwistTag.D4.tag) L u)⁻¹ * z *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L u * g₂⁻¹) =
      (g₂ * (canonicalRep (coxeterSystem TwistTag.D4.tag) L u)⁻¹ * z *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L u * g₂⁻¹) *
        diagramMap TwistTag.D4 L := by
  set nu := canonicalRep (coxeterSystem TwistTag.D4.tag) L u with hnu
  have hnuM : nu ∈ monomialSubgroup TwistTag.D4.tag L := canonicalRep_mem_monomialSubgroup L u
  have hnuW : weylQuotientHom TwistTag.D4.tag L ⟨nu, hnuM⟩ = u :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep u)
  have hinvM : nu⁻¹ ∈ monomialSubgroup TwistTag.D4.tag L := inv_mem hnuM
  have hinvW : weylQuotientHom TwistTag.D4.tag L ⟨nu⁻¹, hinvM⟩ = u⁻¹ := by
    have : (⟨nu⁻¹, hinvM⟩ : monomialSubgroup TwistTag.D4.tag L) = (⟨nu, hnuM⟩)⁻¹ := rfl
    rw [this, map_inv, hnuW]
  have hS : ∀ γ ∈ d4Sigma i, IsRoot TwistTag.D4.tag γ ∧
      weylQuotientHom TwistTag.D4.tag L ⟨nu⁻¹, hinvM⟩ • γ ∈
        {x | IsRoot TwistTag.D4.tag x ∧ permLattice TwistTag.D4.perm x = x} := by
    intro γ hγ
    refine ⟨isRoot_of_mem_d4Sigma hγ, ?_⟩
    rw [← hu] at hγ
    obtain ⟨a, ha, rfl⟩ := hγ
    rw [hinvW, inv_smul_smul]
    exact ha
  have h1 := conj_mem_rootSpan_of_monomial_to hinvM hS hz
  have h2 : nu⁻¹ * z * nu⁻¹⁻¹ ∈ rootSpan TwistTag.D4.tag L
      {x | IsRoot TwistTag.D4.tag x ∧ permLattice TwistTag.D4.perm x = x} := h1
  rw [inv_inv] at h2
  have h3 := diagramMap_comm_of_mem_rootSpan_fixed (L := L) (fun β hβ => hβ) h2
  have h4 : g₂⁻¹ * diagramMap TwistTag.D4 L = diagramMap TwistTag.D4 L * g₂⁻¹ := by
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hg₂, mul_assoc, mul_inv_cancel, mul_one]
  set y := nu⁻¹ * z * nu with hy
  have key : diagramMap TwistTag.D4 L * (g₂ * y * g₂⁻¹) =
      (g₂ * y * g₂⁻¹) * diagramMap TwistTag.D4 L := by
    calc diagramMap TwistTag.D4 L * (g₂ * y * g₂⁻¹)
        = (diagramMap TwistTag.D4 L * g₂) * y * g₂⁻¹ := by simp only [mul_assoc]
      _ = g₂ * (diagramMap TwistTag.D4 L * y) * g₂⁻¹ := by rw [hg₂]; simp only [mul_assoc]
      _ = g₂ * (y * diagramMap TwistTag.D4 L) * g₂⁻¹ := by rw [h3]
      _ = g₂ * y * (diagramMap TwistTag.D4 L * g₂⁻¹) := by simp only [mul_assoc]
      _ = g₂ * y * (g₂⁻¹ * diagramMap TwistTag.D4 L) := by rw [← h4]
      _ = (g₂ * y * g₂⁻¹) * diagramMap TwistTag.D4 L := by simp only [mul_assoc]
  simpa only [hy, mul_assoc] using key

end Roots

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
