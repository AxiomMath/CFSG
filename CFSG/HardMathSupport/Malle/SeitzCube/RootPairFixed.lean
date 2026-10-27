module

public import CFSG.HardMathSupport.Malle.SeitzCube.Landing

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExcTwo
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Entrywise


theorem entrywiseUnits_pinnedX {τ : Tag} {L : Type} [Field L] (Fr : L →+* L)
    (α : Fin τ.rank → ℤ) (c : L) :
    Units.map (entrywiseHom Fr) (pinnedX τ L α c) = pinnedX τ L α (Fr c) := by
  rw [Units.ext_iff, Units.coe_map]
  show entrywise Fr _ = _
  rw [entrywise_pinnedX]

end Entrywise


theorem exists_rootPair_fixed {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1) {L : Type}
    [Field L] [IsAlgClosed L] {r : ℕ} [Fact r.Prime] [CharP L r] (Fr : L →+* L) {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup τ) {γ δ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) (hδ : IsRoot τ δ) (hne : γ ≠ δ) (hγp : 0 < height γ)
    (hδp : 0 < height δ) (horth : iform γ δ = 0) (hwγ : w • γ = δ) (hwδ : w • δ = γ) :
    ∃ R : Subgroup (ModGL τ L),
      R ≤ twistFix τ Fr (canonicalRep (coxeterSystem τ) L w) ∧ R ≠ ⊥ ∧ IsPGroup r R ∧
        ∀ t ∈ torusGroup τ L, t ∈ twistFix τ Fr (canonicalRep (coxeterSystem τ) L w) →
          R.map (MulAut.conj t).toMonoidHom = R := by
  classical
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have hc : ∀ a b, Commute (pinnedX τ L γ a) (pinnedX τ L δ b) :=
    commute_pinnedX_of_iform_eq_zero L hsym hγ hδ horth
  let ψ : Multiplicative (L × L) →* ModGL τ L :=
    { toFun := fun x => pinnedX τ L γ x.toAdd.1 * pinnedX τ L δ x.toAdd.2
      map_one' := by simp [pinnedX_zero]
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pinnedX_add]
        have key : pinnedX τ L γ y.toAdd.1 * pinnedX τ L δ x.toAdd.2 =
            pinnedX τ L δ x.toAdd.2 * pinnedX τ L γ y.toAdd.1 := (hc _ _).eq
        calc pinnedX τ L γ x.toAdd.1 * pinnedX τ L γ y.toAdd.1 *
              (pinnedX τ L δ x.toAdd.2 * pinnedX τ L δ y.toAdd.2)
            = pinnedX τ L γ x.toAdd.1 * (pinnedX τ L γ y.toAdd.1 * pinnedX τ L δ x.toAdd.2) *
              pinnedX τ L δ y.toAdd.2 := by group
          _ = pinnedX τ L γ x.toAdd.1 * (pinnedX τ L δ x.toAdd.2 * pinnedX τ L γ y.toAdd.1) *
              pinnedX τ L δ y.toAdd.2 := by rw [key]
          _ = _ := by group }
  have hψ : ∀ a b, ψ (Multiplicative.ofAdd (a, b)) = pinnedX τ L γ a * pinnedX τ L δ b :=
    fun a b => rfl
  have hX : ∀ a b, pinnedX τ L γ a * pinnedX τ L δ b ∈ ψ.range := fun a b =>
    ⟨Multiplicative.ofAdd (a, b), rfl⟩
  obtain ⟨ε₁, hε₁, hn₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hγ
  obtain ⟨ε₂, hε₂, hn₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w hδ
  rw [hwγ] at hn₁
  rw [hwδ] at hn₂
  have hmem : ∀ x, x ∈ ψ.range ↔ ∃ a b, x = pinnedX τ L γ a * pinnedX τ L δ b := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.toAdd.1, y.toAdd.2, rfl⟩
    · rintro ⟨a, b, rfl⟩
      exact hX a b
  have hR0t : ∀ t ∈ torusGroup τ L, ∀ x ∈ ψ.range, t * x * t⁻¹ ∈ ψ.range := by
    intro t ht x hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨a, b, rfl⟩ := (hmem x).1 hx
    have e : rootDiagUnit τ l * (pinnedX τ L γ a * pinnedX τ L δ b) * (rootDiagUnit τ l)⁻¹ =
        (rootDiagUnit τ l * pinnedX τ L γ a * (rootDiagUnit τ l)⁻¹) *
          (rootDiagUnit τ l * pinnedX τ L δ b * (rootDiagUnit τ l)⁻¹) := by group
    rw [e, rootDiagUnit_conj_pinnedX l hγ a, rootDiagUnit_conj_pinnedX l hδ b]
    exact hX _ _
  set R : Subgroup (ModGL τ L) := ψ.range ⊓ twistFix τ Fr n with hR
  have hstep : ∀ t ∈ torusGroup τ L, t ∈ twistFix τ Fr n → ∀ x ∈ R, t * x * t⁻¹ ∈ R :=
    fun t ht htf x hx =>
      ⟨hR0t t ht x hx.1, Subgroup.mul_mem _ (Subgroup.mul_mem _ htf hx.2) (Subgroup.inv_mem _ htf)⟩
  set s : L := ε₂ * ε₁ ^ q with hs
  have hss : s * s = 1 := by
    rw [hs, show ε₂ * ε₁ ^ q * (ε₂ * ε₁ ^ q) = (ε₂ * ε₂) * (ε₁ * ε₁) ^ q by
      rw [mul_pow]; ring, hε₁, hε₂, one_pow, one_mul]
  have hq4 : 0 < q ^ 2 - 1 := by
    have : 4 ≤ q ^ 2 := by nlinarith
    omega
  obtain ⟨a₀, ha₀⟩ := IsAlgClosed.exists_pow_nat_eq s hq4
  have ha0ne : a₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hq4.ne'] at ha₀
    have := hss
    rw [← ha₀, zero_mul] at this
    exact zero_ne_one this
  have hsq : a₀ ^ q ^ 2 = s * a₀ := by
    rw [show q ^ 2 = (q ^ 2 - 1) + 1 by omega, pow_succ, ha₀]
  set b₀ : L := ε₁ * a₀ ^ q with hb₀
  have hb : ε₂ * b₀ ^ q = a₀ := by
    rw [hb₀, mul_pow, ← pow_mul, show q * q = q ^ 2 by ring, hsq]
    calc ε₂ * (ε₁ ^ q * (s * a₀)) = (ε₂ * ε₁ ^ q) * (s * a₀) := by ring
      _ = s * (s * a₀) := rfl
      _ = a₀ := by rw [← mul_assoc, hss, one_mul]
  have hxfix : n * Units.map (entrywiseHom Fr) (pinnedX τ L γ a₀ * pinnedX τ L δ b₀) * n⁻¹ =
      pinnedX τ L γ a₀ * pinnedX τ L δ b₀ := by
    rw [map_mul, entrywiseUnits_pinnedX, entrywiseUnits_pinnedX]
    have e : n * (pinnedX τ L γ (Fr a₀) * pinnedX τ L δ (Fr b₀)) * n⁻¹ =
        (n * pinnedX τ L γ (Fr a₀) * n⁻¹) * (n * pinnedX τ L δ (Fr b₀) * n⁻¹) := by group
    rw [e, hn₁, hn₂, (hc _ _).symm.eq, hFr, hFr, hb]
  have hx0 : pinnedX τ L γ a₀ * pinnedX τ L δ b₀ ∈ R :=
    ⟨hX a₀ b₀, mem_twistFix.2 ⟨mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _), hxfix⟩⟩
  refine ⟨R, inf_le_right, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.mem_bot] at hx0
    have h1 : pinnedX τ L γ a₀ * pinnedX τ L δ b₀ = pinnedX τ L γ 0 * pinnedX τ L δ 0 := by
      rw [hx0, pinnedX_zero, pinnedX_zero, mul_one]
    exact ha0ne (CFSG.LieType.Ree.pinnedX_mul_pinnedX_inj (Or.inl ⟨⟨hγ, hγp⟩, ⟨hδ, hδp⟩⟩) hne h1).1
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := g.2.1
    refine Subtype.ext ?_
    have hyr : y ^ r = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      refine Prod.ext ?_ ?_ <;> simp [nsmul_eq_mul, CharP.cast_eq_zero]
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
