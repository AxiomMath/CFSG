module

public import CFSG.HardMathSupport.Malle.SeitzCube.RootPairFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley


theorem exists_rootSingle_fixed {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {r : ℕ}
    [Fact r.Prime] [CharP L r] (Fr : L →+* L) {q : ℕ} (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q)
    (w : WeylGroup τ) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hwγ : w • γ = γ) :
    ∃ R : Subgroup (ModGL τ L),
      R ≤ twistFix τ Fr (canonicalRep (coxeterSystem τ) L w) ∧ R ≠ ⊥ ∧ IsPGroup r R ∧
        ∀ t ∈ torusGroup τ L, t ∈ twistFix τ Fr (canonicalRep (coxeterSystem τ) L w) →
          R.map (MulAut.conj t).toMonoidHom = R := by
  classical
  set n := canonicalRep (coxeterSystem τ) L w with hn
  let ψ : Multiplicative L →* ModGL τ L :=
    { toFun := fun x => pinnedX τ L γ x.toAdd
      map_one' := by simp [pinnedX_zero]
      map_mul' := fun x y => by simp [pinnedX_add] }
  have hX : ∀ a, pinnedX τ L γ a ∈ ψ.range := fun a => ⟨Multiplicative.ofAdd a, rfl⟩
  have hmem : ∀ x, x ∈ ψ.range ↔ ∃ a, x = pinnedX τ L γ a := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.toAdd, rfl⟩
    · rintro ⟨a, rfl⟩
      exact hX a
  obtain ⟨ε, hε, hn₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
  rw [hwγ] at hn₁
  have hR0t : ∀ t ∈ torusGroup τ L, ∀ x ∈ ψ.range, t * x * t⁻¹ ∈ ψ.range := by
    intro t ht x hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨a, rfl⟩ := (hmem x).1 hx
    rw [rootDiagUnit_conj_pinnedX l hγ a]
    exact hX _
  set R : Subgroup (ModGL τ L) := ψ.range ⊓ twistFix τ Fr n with hR
  have hstep : ∀ t ∈ torusGroup τ L, t ∈ twistFix τ Fr n → ∀ x ∈ R, t * x * t⁻¹ ∈ R :=
    fun t ht htf x hx =>
      ⟨hR0t t ht x hx.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ htf hx.2) (Subgroup.inv_mem _ htf)⟩
  have hq1 : 0 < q - 1 := by omega
  obtain ⟨a₀, ha₀⟩ := IsAlgClosed.exists_pow_nat_eq ε hq1
  have hε0 : ε ≠ 0 := fun h => by
    have := hε
    rw [h, zero_mul] at this
    exact zero_ne_one this
  have ha0ne : a₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hq1.ne'] at ha₀
    exact hε0 ha₀.symm
  have hfix : ε * Fr a₀ = a₀ := by
    rw [hFr, show q = (q - 1) + 1 by omega, pow_succ, ha₀, ← mul_assoc, hε, one_mul]
  have hxfix : n * Units.map (entrywiseHom Fr) (pinnedX τ L γ a₀) * n⁻¹ = pinnedX τ L γ a₀ := by
    rw [entrywiseUnits_pinnedX, hn₁, hfix]
  have hx0 : pinnedX τ L γ a₀ ∈ R :=
    ⟨hX a₀, mem_twistFix.2 ⟨pinnedX_mem_adjointGroup _ _, hxfix⟩⟩
  refine ⟨R, inf_le_right, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.mem_bot] at hx0
    exact ha0ne (pinnedX_injective τ L γ (by rw [hx0, pinnedX_zero]))
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := g.2.1
    refine Subtype.ext ?_
    have hyr : y ^ r = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      simp [nsmul_eq_mul, CharP.cast_eq_zero]
    change (g : ModGL τ L) ^ r ^ 1 = 1
    rw [pow_one, ← hy, ← map_pow, hyr, map_one]
  · intro t ht htf
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hstep t ht htf x hx
    · intro hy
      refine ⟨t⁻¹ * y * t, ?_, ?_⟩
      · simpa using hstep t⁻¹ (inv_mem ht) (inv_mem htf) y hy
      · simp [MulAut.conj_apply, mul_assoc]

end CFSG.HardMathSupport.Malle.SeitzCube
