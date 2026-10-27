module

public import CFSG.HardMathSupport.Malle.SeitzCube.RootPairFixed

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.StandardType.TableBExcTwo
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem mul_mul_mul_of_commute {G : Type*} [Group G] (P C P' C' : G) (h : C * P' = P' * C) :
    P * C * (P' * C') = (P * P') * (C * C') := by
  calc P * C * (P' * C') = P * (C * P') * C' := by group
    _ = P * (P' * C) * C' := by rw [h]
    _ = _ := by group


theorem exists_rootTriple_fixed {τ : Tag} (hsym : ∀ i, τ.symmetrizer i i = 1) {L : Type}
    [Field L] [IsAlgClosed L] {r : ℕ} [Fact r.Prime] [CharP L r] (Fr : L →+* L) {q : ℕ}
    (hq : 2 ≤ q) (hFr : ∀ c, Fr c = c ^ q) (w : WeylGroup τ)
    {γ₁ γ₂ γ₃ : Fin τ.rank → ℤ} (h₁ : IsRoot τ γ₁) (h₂ : IsRoot τ γ₂) (h₃ : IsRoot τ γ₃)
    (p₁ : 0 < height γ₁) (p₂ : 0 < height γ₂) (p₃ : 0 < height γ₃)
    (n₁₂ : γ₁ ≠ γ₂) (n₁₃ : γ₁ ≠ γ₃) (n₂₃ : γ₂ ≠ γ₃)
    (o₁₂ : iform γ₁ γ₂ = 0) (o₁₃ : iform γ₁ γ₃ = 0) (o₂₃ : iform γ₂ γ₃ = 0)
    (w₁ : w • γ₁ = γ₂) (w₂ : w • γ₂ = γ₃) (w₃ : w • γ₃ = γ₁) :
    ∃ R : Subgroup (ModGL τ L),
      R ≤ twistFix τ Fr (canonicalRep (coxeterSystem τ) L w) ∧ R ≠ ⊥ ∧ IsPGroup r R ∧
        ∀ t ∈ torusGroup τ L, t ∈ twistFix τ Fr (canonicalRep (coxeterSystem τ) L w) →
          R.map (MulAut.conj t).toMonoidHom = R := by
  classical
  set n := canonicalRep (coxeterSystem τ) L w with hn
  have c12 : ∀ a b, Commute (pinnedX τ L γ₁ a) (pinnedX τ L γ₂ b) :=
    commute_pinnedX_of_iform_eq_zero L hsym h₁ h₂ o₁₂
  have c13 : ∀ a b, Commute (pinnedX τ L γ₁ a) (pinnedX τ L γ₃ b) :=
    commute_pinnedX_of_iform_eq_zero L hsym h₁ h₃ o₁₃
  have c23 : ∀ a b, Commute (pinnedX τ L γ₂ a) (pinnedX τ L γ₃ b) :=
    commute_pinnedX_of_iform_eq_zero L hsym h₂ h₃ o₂₃
  let ψ : Multiplicative (L × L × L) →* ModGL τ L :=
    { toFun := fun x => pinnedX τ L γ₁ x.toAdd.1 * pinnedX τ L γ₂ x.toAdd.2.1 *
        pinnedX τ L γ₃ x.toAdd.2.2
      map_one' := by simp [pinnedX_zero]
      map_mul' := fun x y => by
        simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, pinnedX_add]
        have k12 : pinnedX τ L γ₂ x.toAdd.2.1 * pinnedX τ L γ₁ y.toAdd.1 =
            pinnedX τ L γ₁ y.toAdd.1 * pinnedX τ L γ₂ x.toAdd.2.1 := (c12 _ _).symm.eq
        have k3 : pinnedX τ L γ₃ x.toAdd.2.2 *
            (pinnedX τ L γ₁ y.toAdd.1 * pinnedX τ L γ₂ y.toAdd.2.1) =
            (pinnedX τ L γ₁ y.toAdd.1 * pinnedX τ L γ₂ y.toAdd.2.1) *
              pinnedX τ L γ₃ x.toAdd.2.2 :=
          ((c13 _ _).symm.mul_right (c23 _ _).symm).eq
        rw [mul_mul_mul_of_commute _ _ _ _ k3, mul_mul_mul_of_commute _ _ _ _ k12] }
  have hX : ∀ a b c, pinnedX τ L γ₁ a * pinnedX τ L γ₂ b * pinnedX τ L γ₃ c ∈ ψ.range :=
    fun a b c => ⟨Multiplicative.ofAdd (a, b, c), rfl⟩
  have hmem : ∀ x, x ∈ ψ.range ↔ ∃ a b c, x = pinnedX τ L γ₁ a * pinnedX τ L γ₂ b *
      pinnedX τ L γ₃ c := by
    intro x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y.toAdd.1, y.toAdd.2.1, y.toAdd.2.2, rfl⟩
    · rintro ⟨a, b, c, rfl⟩
      exact hX a b c
  obtain ⟨ε₁, hε₁, hn₁⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w h₁
  obtain ⟨ε₂, hε₂, hn₂⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w h₂
  obtain ⟨ε₃, hε₃, hn₃⟩ := exists_canonicalRep_mul_pinnedX_mul_inv L w h₃
  rw [w₁] at hn₁
  rw [w₂] at hn₂
  rw [w₃] at hn₃
  have hR0t : ∀ t ∈ torusGroup τ L, ∀ x ∈ ψ.range, t * x * t⁻¹ ∈ ψ.range := by
    intro t ht x hx
    obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    obtain ⟨a, b, c, rfl⟩ := (hmem x).1 hx
    have e : rootDiagUnit τ l * (pinnedX τ L γ₁ a * pinnedX τ L γ₂ b * pinnedX τ L γ₃ c) *
        (rootDiagUnit τ l)⁻¹ =
        (rootDiagUnit τ l * pinnedX τ L γ₁ a * (rootDiagUnit τ l)⁻¹) *
          (rootDiagUnit τ l * pinnedX τ L γ₂ b * (rootDiagUnit τ l)⁻¹) *
          (rootDiagUnit τ l * pinnedX τ L γ₃ c * (rootDiagUnit τ l)⁻¹) := by group
    rw [e, rootDiagUnit_conj_pinnedX l h₁ a, rootDiagUnit_conj_pinnedX l h₂ b,
      rootDiagUnit_conj_pinnedX l h₃ c]
    exact hX _ _ _
  set R : Subgroup (ModGL τ L) := ψ.range ⊓ twistFix τ Fr n with hR
  have hstep : ∀ t ∈ torusGroup τ L, t ∈ twistFix τ Fr n → ∀ x ∈ R, t * x * t⁻¹ ∈ R :=
    fun t ht htf x hx =>
      ⟨hR0t t ht x hx.1,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ htf hx.2) (Subgroup.inv_mem _ htf)⟩
  set s : L := ε₃ * ε₂ ^ q * ε₁ ^ (q ^ 2) with hs
  have hss : s * s = 1 := by
    rw [hs, show ε₃ * ε₂ ^ q * ε₁ ^ (q ^ 2) * (ε₃ * ε₂ ^ q * ε₁ ^ (q ^ 2)) =
      (ε₃ * ε₃) * (ε₂ * ε₂) ^ q * (ε₁ * ε₁) ^ (q ^ 2) by rw [mul_pow, mul_pow]; ring,
      hε₁, hε₂, hε₃, one_pow, one_pow, one_mul, one_mul]
  have hq4 : 0 < q ^ 3 - 1 := by
    have : 8 ≤ q ^ 3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℕ) ≤ 2) hq 3]
    omega
  obtain ⟨a₀, ha₀⟩ := IsAlgClosed.exists_pow_nat_eq s hq4
  have ha0ne : a₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hq4.ne'] at ha₀
    have := hss
    rw [← ha₀, zero_mul] at this
    exact zero_ne_one this
  have hsq : a₀ ^ q ^ 3 = s * a₀ := by
    rw [show q ^ 3 = (q ^ 3 - 1) + 1 by omega, pow_succ, ha₀]
  set b₀ : L := ε₁ * a₀ ^ q with hb₀
  set c₀ : L := ε₂ * b₀ ^ q with hc₀
  have hc : ε₃ * c₀ ^ q = a₀ := by
    have key : ε₃ * (ε₂ * (ε₁ * a₀ ^ q) ^ q) ^ q = s * a₀ ^ (q ^ 3) := by
      rw [hs]; ring
    rw [hc₀, hb₀, key, hsq, ← mul_assoc, hss, one_mul]
  have hxfix : n * Units.map (entrywiseHom Fr) (pinnedX τ L γ₁ a₀ * pinnedX τ L γ₂ b₀ *
      pinnedX τ L γ₃ c₀) * n⁻¹ = pinnedX τ L γ₁ a₀ * pinnedX τ L γ₂ b₀ * pinnedX τ L γ₃ c₀ := by
    rw [map_mul, map_mul, entrywiseUnits_pinnedX, entrywiseUnits_pinnedX, entrywiseUnits_pinnedX]
    have e : n * (pinnedX τ L γ₁ (Fr a₀) * pinnedX τ L γ₂ (Fr b₀) * pinnedX τ L γ₃ (Fr c₀)) *
        n⁻¹ = (n * pinnedX τ L γ₁ (Fr a₀) * n⁻¹) * (n * pinnedX τ L γ₂ (Fr b₀) * n⁻¹) *
          (n * pinnedX τ L γ₃ (Fr c₀) * n⁻¹) := by group
    rw [e, hn₁, hn₂, hn₃]
    have rot : pinnedX τ L γ₂ (ε₁ * Fr a₀) * pinnedX τ L γ₃ (ε₂ * Fr b₀) *
        pinnedX τ L γ₁ (ε₃ * Fr c₀) =
        pinnedX τ L γ₁ (ε₃ * Fr c₀) * (pinnedX τ L γ₂ (ε₁ * Fr a₀) *
          pinnedX τ L γ₃ (ε₂ * Fr b₀)) := by
      exact ((c12 _ _).mul_right (c13 _ _)).eq.symm
    rw [rot, hFr, hFr, hFr, hc, ← hb₀, ← hc₀, mul_assoc]
  have hx0 : pinnedX τ L γ₁ a₀ * pinnedX τ L γ₂ b₀ * pinnedX τ L γ₃ c₀ ∈ R :=
    ⟨hX a₀ b₀ c₀, mem_twistFix.2 ⟨mul_mem (mul_mem (pinnedX_mem_adjointGroup _ _)
      (pinnedX_mem_adjointGroup _ _)) (pinnedX_mem_adjointGroup _ _), hxfix⟩⟩
  refine ⟨R, inf_le_right, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, Subgroup.mem_bot] at hx0
    have hnd : [γ₁, γ₂, γ₃].Nodup := by simp [n₁₂, n₁₃, n₂₃]
    have hpos : ∀ α ∈ [γ₁, γ₂, γ₃], IsRoot τ α ∧ 0 < height α := by
      intro α hα
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hα
      rcases hα with rfl | rfl | rfl
      exacts [⟨h₁, p₁⟩, ⟨h₂, p₂⟩, ⟨h₃, p₃⟩]
    have heq := CFSG.LieType.Chevalley.pinnedX_list_prod_injective (R := L)
      [γ₁, γ₂, γ₃] hnd hpos
      (fun α => if α = γ₁ then a₀ else if α = γ₂ then b₀ else c₀) (fun _ => 0)
      (by
        simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, ite_true,
          n₁₂.symm, n₁₃.symm, n₂₃.symm, ite_false, pinnedX_zero, mul_one]
        rw [← mul_assoc]
        exact hx0)
    exact ha0ne (by simpa using heq γ₁ (by simp))
  · intro g
    refine ⟨1, ?_⟩
    obtain ⟨y, hy⟩ := g.2.1
    refine Subtype.ext ?_
    have hyr : y ^ r = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp [nsmul_eq_mul, CharP.cast_eq_zero]
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
