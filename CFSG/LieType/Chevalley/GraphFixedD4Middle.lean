module

public import CFSG.LieType.Chevalley.GraphFixedRootNormal
public import CFSG.LieType.Chevalley.GraphFixedParameterFields
public import CFSG.LieType.Chevalley.D4TripleA2

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley
open scoped commutatorElement

theorem list_prod_torusElt_conj_xUnit_scale
    {τ : Tag} {K : Type} [Field K]
    (ω : List (Fin τ.rank)) (U : Fin τ.rank → Kˣ) (j : Fin τ.rank) (e : K) :
    (ω.map fun i => torusElt τ K i (U i)).prod * xUnit τ K j e *
        ((ω.map fun i => torusElt τ K i (U i)).prod)⁻¹ =
      xUnit τ K j ((ω.map fun i => ((U i ^ τ.cartan i j : Kˣ) : K)).prod * e) := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    rw [List.map_cons, List.prod_cons]
    set P := (ω.map fun i => torusElt τ K i (U i)).prod
    have e1 : torusElt τ K i (U i) * P * xUnit τ K j e * (torusElt τ K i (U i) * P)⁻¹ =
        torusElt τ K i (U i) * (P * xUnit τ K j e * P⁻¹) * (torusElt τ K i (U i))⁻¹ := by
      group
    have hsum : ∑ m, τ.cartan i m * (Pi.single j 1 : Fin τ.rank → ℤ) m = τ.cartan i j := by
      simp [Pi.single_apply]
    rw [e1, ih, ← pinnedX_single, root_torus_conjugation i (isRoot_single _ j), pinnedX_single,
      hsum, List.map_cons, List.prod_cons, mul_assoc]

section TripleA2

variable {K : Type} [Field K] {σ : K →+* K}

local notation "ν" n => (⟨n, by decide⟩ : Fin TwistTag.D4.tag.rank)

private abbrev A4
    (K : Type) [Field K] (i : Fin TwistTag.D4.tag.rank) (c : K) :
    ModGL TwistTag.D4.tag K :=
  weylElt TwistTag.D4.tag K i (-1) * xUnit TwistTag.D4.tag K (ν 2) c *
    weylElt TwistTag.D4.tag K i 1

private theorem twistHom_A4
    (i : Fin TwistTag.D4.tag.rank) (c : K) :
    twistHom TwistTag.D4 K σ (A4 K i c) = A4 K (TwistTag.D4.perm i) (σ c) := by
  have hρ2 : TwistTag.D4.perm (ν 2) = ν 2 := rfl
  have hu : Units.map σ.toMonoidHom (-1 : Kˣ) = -1 := Units.ext (by simp)
  rw [A4, map_mul, map_mul, twistHom_weylElt, twistHom_xUnit, twistHom_weylElt_one, hu, hρ2]

private theorem d4Y_mem :
    yUnit TwistTag.D4.tag K (ν 0) (-1) * yUnit TwistTag.D4.tag K (ν 1) (-1) *
        yUnit TwistTag.D4.tag K (ν 3) (-1) ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  have h := orbitYProd_neg_one_mem_graphFixedNegUnipotent (t := TwistTag.D4) (K := K) (σ := σ)
    ⟨0, by decide⟩
  have hword : TwistTag.D4.orbitWord ⟨0, by decide⟩ = [ν 0, ν 1, ν 3] := by
    decide
  rw [orbitYProd, hword] at h
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at h
  rw [mul_assoc]
  exact graphFixedNegUnipotent_le_graphFixedRootGroup _ K σ h

private theorem d4A_mem
    {c : K} (hc : σ c = c) :
    A4 K (ν 0) c * A4 K (ν 1) c * A4 K (ν 3) c ∈ graphFixedRootGroup TwistTag.D4 K σ := by
  obtain ⟨-, hroot, hcomm⟩ := d4_triple_a2_commutator K c
  have h0 : d4Node 0 ≠ d4Node 2 := by decide
  have h1 : d4Node 1 ≠ d4Node 2 := by decide
  have h3 : d4Node 3 ≠ d4Node 2 := by decide
  have hpos : ∀ i : Fin Tag.D4.rank, i ≠ d4Node 2 →
      d4TripleA K i c ∈ posUnipotent Tag.D4 K := by
    intro i hi
    have hle : rootSubgroup Tag.D4 K (Pi.single i 1 + Pi.single (d4Node 2) 1) ≤
        posUnipotent Tag.D4 K :=
      le_iSup₂_of_le (f := fun α (_ : IsRoot Tag.D4 α ∧ 0 < height α) => rootSubgroup Tag.D4 K α)
        _ ⟨d4_isRoot_outer i hi, by simp [height, Finset.sum_add_distrib]⟩ le_rfl
    exact hle (hroot i hi)
  have hC : ∀ i : Fin TwistTag.D4.tag.rank, A4 K i c ∈ adjointGroup TwistTag.D4.tag K := fun i =>
    mul_mem (mul_mem (weylElt_mem_adjointGroup i _) (xUnit_mem_adjointGroup _ c))
      (weylElt_mem_adjointGroup i _)
  have hc₃₀ : Commute (A4 K (ν 3) c) (A4 K (ν 0) c) := (hcomm _ _ h3 h0).2
  have hc₁₀ : Commute (A4 K (ν 1) c) (A4 K (ν 0) c) := (hcomm _ _ h1 h0).2
  have hfix : twistHom TwistTag.D4 K σ (A4 K (ν 0) c * A4 K (ν 1) c * A4 K (ν 3) c) =
      A4 K (ν 0) c * A4 K (ν 1) c * A4 K (ν 3) c := by
    rw [map_mul, map_mul, twistHom_A4, twistHom_A4, twistHom_A4, hc]
    change A4 K (ν 1) c * A4 K (ν 3) c * A4 K (ν 0) c = _
    rw [mul_assoc, hc₃₀.eq, ← mul_assoc, hc₁₀.eq]
  have hP : A4 K (ν 0) c * A4 K (ν 1) c * A4 K (ν 3) c ∈ posUnipotent TwistTag.D4.tag K :=
    mul_mem (mul_mem (hpos _ h0) (hpos _ h1)) (hpos _ h3)
  exact graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ (Subgroup.mem_inf.2
    ⟨hP, mul_mem (mul_mem (hC _) (hC _)) (hC _), hfix⟩)

theorem xUnit_three_mul_mem_commutator_D4
    {c : K} (hc : σ c = c) :
    xUnit TwistTag.D4.tag K (ν 2) (3 * c) ∈
      ⁅graphFixedRootGroup TwistTag.D4 K σ, graphFixedRootGroup TwistTag.D4 K σ⁆ := by
  have h := Subgroup.commutator_mem_commutator (d4Y_mem (σ := σ)) (d4A_mem hc)
  have e : ⁅yUnit TwistTag.D4.tag K (ν 0) (-1) * yUnit TwistTag.D4.tag K (ν 1) (-1) *
      yUnit TwistTag.D4.tag K (ν 3) (-1), A4 K (ν 0) c * A4 K (ν 1) c * A4 K (ν 3) c⁆ =
      xUnit TwistTag.D4.tag K (ν 2) (3 * c) :=
    (d4_triple_a2_commutator K c).1
  rwa [e] at h

local notation "a₀" => (⟨0, by decide⟩ : Fin TwistTag.D4.foldedTag.rank)

private theorem orbitH_conj_xUnit_middle
    (u : (orbitField TwistTag.D4 K σ a₀)ˣ) (b : K) :
    (orbitH TwistTag.D4 K σ a₀ u : ModGL TwistTag.D4.tag K) * xUnit TwistTag.D4.tag K (ν 2) b *
        (orbitH TwistTag.D4 K σ a₀ u : ModGL TwistTag.D4.tag K)⁻¹ =
      xUnit TwistTag.D4.tag K (ν 2)
        ((((u : orbitField TwistTag.D4 K σ a₀) : K) * σ ((u : orbitField TwistTag.D4 K σ a₀) : K) *
          σ (σ ((u : orbitField TwistTag.D4 K σ a₀) : K)))⁻¹ * b) := by
  rw [coe_orbitH_eq, list_prod_torusElt_conj_xUnit_scale, TwistTag.orbitWord_eq_map_range,
    List.map_map]
  congr 2
  have hcard : (TwistTag.D4.orbit a₀).card = 3 := by decide
  have hcartan : ∀ k < (TwistTag.D4.orbit a₀).card,
      TwistTag.D4.tag.cartan ((TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin a₀)) (ν 2) = -1 := by
    decide
  have hfun : ∀ k ∈ List.range (TwistTag.D4.orbit a₀).card,
      ((fun i => ((orbitUnitParam TwistTag.D4 σ a₀ (orbitFieldUnit TwistTag.D4 σ u) i ^
        TwistTag.D4.tag.cartan i (ν 2) : Kˣ) : K)) ∘
        fun k => (TwistTag.D4.perm ^ k) (TwistTag.D4.orbitMin a₀)) k =
      ((σ ^ k) ((u : orbitField TwistTag.D4 K σ a₀) : K))⁻¹ := by
    intro k hk
    rw [Function.comp_apply, orbitUnitParam_pow _ σ _ (List.mem_range.1 hk),
      hcartan k (List.mem_range.1 hk), zpow_neg_one, Units.val_inv_eq_inv_val]
    rfl
  rw [List.map_congr_left hfun, hcard]
  simp [List.range_succ]
  ring

private theorem exists_norm_ne_one {q : ℕ} (hq : 3 ≤ q) (hK : Nat.card K = q ^ 3)
    (hσ : ∀ c, σ c = c ^ q) :
    ∃ z : Kˣ, σ ((z : K) * σ z * σ (σ z)) = (z : K) * σ z * σ (σ z) ∧
      (z : K) * σ z * σ (σ z) ≠ 1 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ x : K, x ^ q ^ 3 = x := fun x => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf z = q ^ 3 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hz, Nat.card_units, hK]
  have ha : (z : K) * σ z * σ (σ z) = (z : K) ^ (1 + q + q ^ 2) := by
    rw [hσ, hσ, ← pow_mul, ← sq, pow_add, pow_add, pow_one]
  refine ⟨z, ?_, fun h1 => ?_⟩
  · rw [ha, hσ, ← pow_mul]
    have e : (1 + q + q ^ 2) * q = q + q ^ 2 + q ^ 3 := by ring
    rw [e, pow_add, hpow, pow_add, pow_add, pow_add, pow_one]
    ring
  · rw [ha] at h1
    have h1' : z ^ (1 + q + q ^ 2) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, h1]; rfl)
    have hdvd := orderOf_dvd_of_pow_eq_one h1'
    rw [hord] at hdvd
    have hle := Nat.le_of_dvd (by positivity) hdvd
    have hle' : q ^ 3 ≤ 2 + q + q ^ 2 := by omega
    have h3 : q ^ 3 = q * q ^ 2 := by ring
    nlinarith

private theorem xUnit_mem_commutator_of_three_le
    {q : ℕ} (hq : 3 ≤ q)
    (hK : Nat.card K = q ^ 3) (hσ : ∀ c, σ c = c ^ q) {c : K} (hc : σ c = c) :
    xUnit TwistTag.D4.tag K (ν 2) c ∈
      ⁅graphFixedRootGroup TwistTag.D4 K σ, graphFixedRootGroup TwistTag.D4 K σ⁆ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ x : K, x ^ q ^ 3 = x := fun x => by
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  obtain ⟨z, hza, hz1⟩ := exists_norm_ne_one hq hK hσ
  have htop : ∀ x : K, x ∈ orbitField TwistTag.D4 K σ a₀ := fun x => by
    rw [mem_orbitField, show (TwistTag.D4.orbit a₀).card = 3 by decide, pow_succ, pow_succ,
      pow_one, RingHom.coe_mul, RingHom.coe_mul, Function.comp_apply, Function.comp_apply, hσ, hσ,
      hσ, ← pow_mul, ← pow_mul, show q * (q * q) = q ^ 3 by ring, hpow]
  obtain ⟨u, hu⟩ : ∃ u : (orbitField TwistTag.D4 K σ a₀)ˣ,
      ((u : orbitField TwistTag.D4 K σ a₀) : K) = z :=
    ⟨Units.mk0 ⟨z, htop z⟩ fun h => z.ne_zero (congrArg Subtype.val h), rfl⟩
  have hden : ((z : K) * σ z * σ (σ z))⁻¹ - 1 ≠ 0 := fun h =>
    hz1 (inv_eq_one.1 (sub_eq_zero.1 h))
  have hb : σ (c / (((z : K) * σ z * σ (σ z))⁻¹ - 1)) =
      c / (((z : K) * σ z * σ (σ z))⁻¹ - 1) := by
    rw [map_div₀, map_sub, map_inv₀, map_one, hc, hza]
  have hh := orbitH_mem_graphFixedRootGroup TwistTag.D4 σ a₀ u
  have hx := graphFixedPosUnipotent_le_graphFixedRootGroup _ K σ
    (xUnit_mem_graphFixedPosUnipotent (t := TwistTag.D4) (σ := σ) (j := ν 2) rfl hb)
  have hcomm := Subgroup.commutator_mem_commutator hh hx
  have e : ⁅(orbitH TwistTag.D4 K σ a₀ u : ModGL TwistTag.D4.tag K),
      xUnit TwistTag.D4.tag K (ν 2) (c / (((z : K) * σ z * σ (σ z))⁻¹ - 1))⁆ =
      xUnit TwistTag.D4.tag K (ν 2) c := by
    rw [commutatorElement_def, orbitH_conj_xUnit_middle, hu, ← xUnit_neg, ← xUnit_add]
    congr 1
    rw [← sub_eq_add_neg, ← sub_one_mul]
    exact mul_div_cancel₀ c hden
  rwa [e] at hcomm

theorem D4_fixed_middle_derived
    {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (p ^ f) ^ 3) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (c : K)
    (hc : σ c = c) :
    xUnit TwistTag.D4.tag K (ν 2) c ∈
        ⁅graphFixedRootGroup TwistTag.D4 K σ, graphFixedRootGroup TwistTag.D4 K σ⁆ ∧
      yUnit TwistTag.D4.tag K (ν 2) c ∈
        ⁅graphFixedRootGroup TwistTag.D4 K σ, graphFixedRootGroup TwistTag.D4 K σ⁆ := by
  have hx : ∀ d : K, σ d = d → xUnit TwistTag.D4.tag K (ν 2) d ∈
      ⁅graphFixedRootGroup TwistTag.D4 K σ, graphFixedRootGroup TwistTag.D4 K σ⁆ := by
    intro d hd
    have hq2 : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) p)
    rcases Nat.lt_or_ge (p ^ f) 3 with hq | hq
    ·
      have hq' : p ^ f = 2 := by omega
      have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1
        (hq' ▸ dvd_pow_self p (by omega))
      have hK' : Nat.card K = p ^ (f * 3) := by rw [hK, pow_mul]
      have := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp
        (by omega) hK'
      rw [hp2] at this
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have h3 : (3 : K) * d = d := by linear_combination d * h2
      rw [← h3]
      exact xUnit_three_mul_mem_commutator_D4 hd
    · exact xUnit_mem_commutator_of_three_le hq hK hσ hd
  refine ⟨hx c hc, ?_⟩
  have hn := weylElt_mem_graphFixedRootGroup (t := TwistTag.D4) (K := K) (σ := σ) (j := ν 2) rfl
  have h := conj_mem_commutator_self hn (hx (-c) (by rw [map_neg, hc]))
  rwa [weylElt_mul_xUnit_mul_inv, neg_neg] at h

end TripleA2

end CFSG.LieType.Chevalley
