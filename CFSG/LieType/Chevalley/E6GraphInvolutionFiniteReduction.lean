module

public import CFSG.LieType.Chevalley.LangFiniteSubfieldCongruence
public import CFSG.LieType.Chevalley.LangFiniteNormalizerOddIndex
public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley

theorem exists_finset_descent
    {τ : Tag} {k : Type} [Field k] {x : ModGL τ k}
    (hx : x ∈ adjointGroup τ k) :
    ∃ E : Finset k, ∀ K : Subfield k, (E : Set k) ⊆ K →
      ∃ y ∈ adjointGroup τ K, baseChangeGL K.subtype y = x := by
  classical
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, c, hc | hc⟩ := hg
    · refine ⟨{c}, fun K hK =>
        ⟨xUnit τ K i ⟨c, hK (Finset.mem_coe.2 (Finset.mem_singleton_self c))⟩,
          xUnit_mem_adjointGroup i _, ?_⟩⟩
      rw [baseChangeGL_xUnit]
      exact Units.ext hc.symm
    · refine ⟨{c}, fun K hK =>
        ⟨yUnit τ K i ⟨c, hK (Finset.mem_coe.2 (Finset.mem_singleton_self c))⟩,
          yUnit_mem_adjointGroup i _, ?_⟩⟩
      rw [baseChangeGL_yUnit]
      exact Units.ext hc.symm
  | one => exact ⟨∅, fun K _ => ⟨1, one_mem _, map_one _⟩⟩
  | mul g h _ _ ihg ihh =>
    obtain ⟨E₁, h₁⟩ := ihg
    obtain ⟨E₂, h₂⟩ := ihh
    refine ⟨E₁ ∪ E₂, fun K hK => ?_⟩
    rw [Finset.coe_union, Set.union_subset_iff] at hK
    obtain ⟨y₁, hy₁, e₁⟩ := h₁ K hK.1
    obtain ⟨y₂, hy₂, e₂⟩ := h₂ K hK.2
    exact ⟨y₁ * y₂, mul_mem hy₁ hy₂, by rw [map_mul, e₁, e₂]⟩
  | inv g _ ih =>
    obtain ⟨E, hE⟩ := ih
    refine ⟨E, fun K hK => ?_⟩
    obtain ⟨y, hy, e⟩ := hE K hK
    exact ⟨y⁻¹, inv_mem hy, by rw [map_inv, e]⟩

theorem baseChangeGL_weylElt_one
    {R S : Type} [Field R] [Field S] (f : R →+* S) {τ : Tag}
    (i : Fin τ.rank) : baseChangeGL f (weylElt τ R i 1) = weylElt τ S i 1 := by
  rw [weylElt_eq_xUnit_mul, map_mul, map_mul, baseChangeGL_xUnit, baseChangeGL_yUnit,
    weylElt_eq_xUnit_mul]
  simp

theorem baseChangeGL_mem_monomialSubgroup
    {R S : Type} [Field R] [Field S] (f : R →+* S)
    {τ : Tag} {g : ModGL τ R} (hg : g ∈ monomialSubgroup τ R) :
    baseChangeGL f g ∈ monomialSubgroup τ S := by
  have hle : monomialSubgroup τ R ≤ (monomialSubgroup τ S).comap (baseChangeGL f) := by
    rw [monomialSubgroup, sup_le_iff, torusGroup, Subgroup.closure_le, Subgroup.closure_le]
    constructor
    · rintro _ ⟨⟨i, t⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
      exact torusElt_mem_monomialSubgroup i _
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_weylElt_one]
      exact weylElt_mem_monomialSubgroup i
  exact hle hg

theorem diagramMap_conj_mem_monomialSubgroup
    {t : TwistTag} {K : Type} [Field K]
    {g : ModGL t.tag K} (hg : g ∈ monomialSubgroup t.tag K) :
    diagramMap t K * g * (diagramMap t K)⁻¹ ∈ monomialSubgroup t.tag K := by
  have hle : monomialSubgroup t.tag K ≤
      (monomialSubgroup t.tag K).comap (MulAut.conj (diagramMap t K)).toMonoidHom := by
    rw [monomialSubgroup, sup_le_iff, torusGroup, Subgroup.closure_le, Subgroup.closure_le,
      conj_diagramMap_eq_twistHom]
    constructor
    · rintro _ ⟨⟨i, s⟩, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_torusElt]
      exact torusElt_mem_monomialSubgroup _ _
    · rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, twistHom_weylElt_one]
      exact weylElt_mem_monomialSubgroup _
  simpa using hle hg

theorem diagramMap_conj_mem_adjointGroup
    {t : TwistTag} {K : Type} [Field K]
    {g : ModGL t.tag K} (hg : g ∈ adjointGroup t.tag K) :
    diagramMap t K * g * (diagramMap t K)⁻¹ ∈ adjointGroup t.tag K := by
  have h := twistHom_mem_adjointGroup t K (RingHom.id K) hg
  rw [← conj_diagramMap_eq_twistHom] at h
  simpa using h

theorem exists_fixed_of_involutive_of_odd {α : Type*} [Finite α] {f : α → α}
    (hf : Function.Involutive f) (hodd : Odd (Nat.card α)) : ∃ a, f a = a := by
  set σ : Equiv.Perm α := hf.toPerm f with hσ
  have hσ2 : σ ^ 2 = 1 := by
    ext a
    simp [sq, hσ, hf a]
  have hpg : IsPGroup 2 (Subgroup.zpowers σ) := by
    rintro ⟨g, j, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    change (σ ^ j) ^ 2 ^ 1 = 1
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ2, one_zpow]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hpg.nonempty_fixed_point_of_prime_not_dvd_card α
    (Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hodd))
  exact ⟨a, ha ⟨σ, Subgroup.mem_zpowers σ⟩⟩

theorem E6_graph_involution_finite_extension_monomial_reduction
    {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (halg : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    {x : ModGL TwistTag.E6.tag k} (hx : x ∈ adjointGroup TwistTag.E6.tag k)
    (hx2 : (x * diagramMap TwistTag.E6 k) ^ 2 = 1) :
    ∃ u ∈ adjointGroup TwistTag.E6.tag k, ∃ n ∈ monomialSubgroup TwistTag.E6.tag k,
      u * (x * diagramMap TwistTag.E6 k) * u⁻¹ = n * diagramMap TwistTag.E6 k := by
  classical
  let := ZMod.algebra k p
  obtain ⟨E, hE⟩ := exists_finset_descent hx
  set M := Nat.card (WeylGroup TwistTag.E6.tag) with hMdef
  have hM : 1 ≤ M := Nat.card_pos
  have hWM : ¬ 2 ^ M ∣ M := fun h => absurd (Nat.le_of_dvd (by omega) h) (by
    have := Nat.lt_two_pow_self (n := M)
    omega)
  obtain ⟨K, hKfin, hEK, hKq⟩ := exceptional_Lang_finite_subfield_congruence_enlargement hp2 E
    (fun z _ => Algebra.IsAlgebraic.isAlgebraic z) hM
  have hKodd : Odd (Nat.card K) := by
    have h2 : Nat.card K ≡ 1 [MOD 2] := Nat.ModEq.of_dvd (dvd_pow_self 2 (by omega)) hKq
    exact Nat.odd_iff.2 h2
  obtain ⟨y, hyC, hyx⟩ := hE K hEK
  set ι := K.subtype with hι
  set P := diagramMap TwistTag.E6 K with hP
  have hy2 : (y * P) ^ 2 = 1 := by
    apply baseChangeGL_injective ι
    rw [map_pow, map_mul, hyx, hP, baseChangeGL_diagramMap, hx2, map_one]
  have hPP : P * P = 1 := diagramMap_E6_mul_self
  have hyγ : y * (P * y * P⁻¹) = 1 := by
    calc y * (P * y * P⁻¹) = (y * P) * (y * P) * (P * P)⁻¹ := by group
      _ = 1 := by rw [← sq, hy2, hPP, inv_one, one_mul]
  set C := adjointGroup TwistTag.E6.tag K with hC
  set N := (monomialSubgroup TwistTag.E6.tag K).subgroupOf C with hN
  have hγC : ∀ z : ModGL TwistTag.E6.tag K, z ∈ C → P * z * P⁻¹ ∈ C := fun z hz =>
    diagramMap_conj_mem_adjointGroup hz
  let γ : C → C := fun z => ⟨P * (z : ModGL TwistTag.E6.tag K) * P⁻¹, hγC z z.2⟩
  have hγmul : ∀ a b : C, γ (a * b) = γ a * γ b := fun a b => Subtype.ext (by
    change P * ((a : ModGL TwistTag.E6.tag K) * b) * P⁻¹ =
      (P * (a : ModGL TwistTag.E6.tag K) * P⁻¹) * (P * (b : ModGL TwistTag.E6.tag K) * P⁻¹)
    group)
  have hγinv : ∀ a : C, γ a⁻¹ = (γ a)⁻¹ := fun a => Subtype.ext (by
    change P * ((a : ModGL TwistTag.E6.tag K))⁻¹ * P⁻¹ = (P * (a : ModGL TwistTag.E6.tag K) * P⁻¹)⁻¹
    group)
  have hγN : ∀ a : C, a ∈ N → γ a ∈ N := fun a ha =>
    Subgroup.mem_subgroupOf.2 (diagramMap_conj_mem_monomialSubgroup (Subgroup.mem_subgroupOf.1 ha))
  set y' : C := ⟨y, hyC⟩ with hy'
  let T : C ⧸ N → C ⧸ N := Quotient.map' (fun z => y' * γ z) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab ⊢
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel_left, ← hγinv, ← hγmul]
    exact hγN _ hab)
  have hT : ∀ z : C, T (z : C ⧸ N) = ((y' * γ z : C) : C ⧸ N) := fun z => rfl
  have hγγ : ∀ z : C, γ (γ z) = z := fun z => Subtype.ext (by
    change P * (P * (z : ModGL TwistTag.E6.tag K) * P⁻¹) * P⁻¹ = (z : ModGL TwistTag.E6.tag K)
    calc P * (P * (z : ModGL TwistTag.E6.tag K) * P⁻¹) * P⁻¹ =
          (P * P) * (z : ModGL TwistTag.E6.tag K) * (P * P)⁻¹ := by group
      _ = z := by rw [hPP, one_mul, inv_one, mul_one])
  have hyγ' : y' * γ y' = 1 := Subtype.ext hyγ
  have hTinv : Function.Involutive T := by
    intro q
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hT, hT, hγmul, hγγ, ← mul_assoc, hyγ', one_mul]
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  have hodd : Odd (Nat.card (C ⧸ N)) := by
    have h := (exceptional_Lang_finite_normalizer_odd_index_involutions TwistTag.E6.tag K hKodd hM
      hKq hWM).1
    exact h
  obtain ⟨q, hq⟩ := exists_fixed_of_involutive_of_odd hTinv hodd
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective q
  rw [hT, QuotientGroup.eq] at hq
  have hn : (z : ModGL TwistTag.E6.tag K)⁻¹ * y * (P * (z : ModGL TwistTag.E6.tag K) * P⁻¹) ∈
      monomialSubgroup TwistTag.E6.tag K := by
    have h1 := inv_mem hq
    rw [mul_inv_rev, inv_inv] at h1
    have h2 := Subgroup.mem_subgroupOf.1 h1
    have e : ((z⁻¹ * (y' * γ z) : C) : ModGL TwistTag.E6.tag K) =
        (z : ModGL TwistTag.E6.tag K)⁻¹ * y * (P * (z : ModGL TwistTag.E6.tag K) * P⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [mul_assoc]
    rw [← e]
    exact h2
  have hKeq : (z : ModGL TwistTag.E6.tag K)⁻¹ * (y * P) * ((z : ModGL TwistTag.E6.tag K)⁻¹)⁻¹ =
      ((z : ModGL TwistTag.E6.tag K)⁻¹ * y * (P * (z : ModGL TwistTag.E6.tag K) * P⁻¹)) * P := by
    group
  refine ⟨baseChangeGL ι (z : ModGL TwistTag.E6.tag K)⁻¹,
    baseChangeGL_mem_adjointGroup ι (inv_mem z.2),
    baseChangeGL ι ((z : ModGL TwistTag.E6.tag K)⁻¹ * y *
      (P * (z : ModGL TwistTag.E6.tag K) * P⁻¹)),
    baseChangeGL_mem_monomialSubgroup ι hn, ?_⟩
  calc baseChangeGL ι (z : ModGL TwistTag.E6.tag K)⁻¹ * (x * diagramMap TwistTag.E6 k) *
        (baseChangeGL ι (z : ModGL TwistTag.E6.tag K)⁻¹)⁻¹ =
      baseChangeGL ι ((z : ModGL TwistTag.E6.tag K)⁻¹ * (y * P) *
        ((z : ModGL TwistTag.E6.tag K)⁻¹)⁻¹) := by
        rw [← hyx, ← baseChangeGL_diagramMap ι TwistTag.E6]
        simp only [map_mul, map_inv, inv_inv]
        rfl
    _ = _ := by rw [hKeq, map_mul, baseChangeGL_diagramMap]

end CFSG.LieType.Chevalley
