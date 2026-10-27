module

public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.LayerAssembly
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.ShortElt
public import CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3.NestedComm

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.Triality CFSG.HardMathSupport.Lang.E27Lie
open CFSG.HardMathSupport.Solomon.Coordinator
open scoped commutatorElement

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3


private theorem jk_pow_three_mul_of_comm {G : Type*} [Group G] {x y d : G}
    (hyx : y * x = d * (x * y)) (hdx : Commute d x) (hdy : Commute d y) :
    (x * y) ^ 3 = d ^ 3 * x ^ 3 * y ^ 3 := by
  have hyd : y * d = d * y := hdy.eq.symm
  have hxd : x * d = d * x := hdx.eq.symm
  have hdd1 : Commute (d * d) x := hdx.mul_left hdx
  have hdd : Commute (d * d) (x * x) := hdd1.mul_right hdd1
  have hyyx : y * y * x = d * d * (x * y * y) := by
    calc y * y * x = y * (y * x) := by group
      _ = y * (d * (x * y)) := by rw [hyx]
      _ = (y * d) * (x * y) := by group
      _ = (d * y) * (x * y) := by rw [hyd]
      _ = d * (y * (x * y)) := by group
      _ = d * ((y * x) * y) := by group
      _ = d * ((d * (x * y)) * y) := by rw [hyx]
      _ = d * d * (x * y * y) := by group
  have hxyxy : (x * y) * (x * y) = d * (x * x) * (y * y) := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (d * (x * y)) * y := by rw [hyx]
      _ = (x * d) * (x * y) * y := by group
      _ = (d * x) * (x * y) * y := by rw [hxd]
      _ = d * (x * x) * (y * y) := by group
  calc (x * y) ^ 3 = (x * y) * (x * y) * (x * y) := pow_three' (x * y)
    _ = d * (x * x) * (y * y) * (x * y) := by rw [hxyxy]
    _ = d * (x * x) * (y * y * x) * y := by group
    _ = d * (x * x) * (d * d * (x * y * y)) * y := by rw [hyyx]
    _ = d * ((d * d) * (x * x)) * (x * y * y) * y := by
      rw [show d * (x * x) * (d * d * (x * y * y)) * y = d * ((x * x) * (d * d)) * (x * y * y) * y
        by group, ← hdd.eq]
    _ = d ^ 3 * x ^ 3 * y ^ 3 := by rw [pow_three' d, pow_three' x, pow_three' y]; group

private theorem jk_prod_rev_of_pairwise {G : Type*} [Group G] {a b c : G} (hab : Commute a b)
    (hac : Commute a c) (hbc : Commute b c) : c * (b * a) = a * b * c := by
  calc c * (b * a) = c * (a * b) := by rw [← hab.eq]
    _ = c * a * b := by group
    _ = a * c * b := by rw [← hac.eq]
    _ = a * (c * b) := by group
    _ = a * (b * c) := by rw [← hbc.eq]
    _ = a * b * c := by group

private theorem jk_conj_decomp {G : Type*} [Group G] {M C D A : G} (h : Commute (C * D) A) :
    M⁻¹ * (A⁻¹ * (M * C * D) * A) = ⁅M⁻¹, A⁻¹⁆ * (C * D) := by
  have hAcomm : A * (C * D) = C * D * A := h.eq.symm
  calc M⁻¹ * (A⁻¹ * (M * C * D) * A) = M⁻¹ * A⁻¹ * M * (C * D * A) := by group
    _ = M⁻¹ * A⁻¹ * M * (A * (C * D)) := by rw [hAcomm]
    _ = ⁅M⁻¹, A⁻¹⁆ * (C * D) := by rw [commutatorElement_def]; group

section Char3

variable {K : Type} [Field K] [Finite K] [CharP K 3]

private theorem jk_three_eq_zero : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3

private theorem jk_cube_injective : Function.Injective (fun x : K => x ^ 3) := by
  intro x y hxy
  have h : (x - y) ^ 3 = 0 := by
    rw [sub_pow_char]
    exact sub_eq_zero.2 hxy
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by norm_num)).1 h)

private theorem jk_exists_cube_eq (c : K) : ∃ t : K, t ^ 3 = c :=
  Finite.injective_iff_surjective.1 jk_cube_injective c

private theorem jk_pinnedX_pow_three (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    pinnedX TwistTag.D4.tag K α c ^ 3 = 1 := by
  have h3 : c + c + c = 0 := by linear_combination c * (jk_three_eq_zero (K := K))
  rw [pow_three', ← pinnedX_add, ← pinnedX_add, h3, pinnedX_zero]

private theorem jk_not_isRoot_of_not_mem {v : Fin TwistTag.D4.tag.rank → ℤ}
    (h : v ∉ rootFinset TwistTag.D4.tag) : ¬ IsRoot TwistTag.D4.tag v :=
  fun hv => h (mem_rootFinset.2 hv)

private theorem jk_isRoot_A0 : IsRoot TwistTag.D4.tag rootA0 := mem_rootFinset.1 (by decide +kernel)
private theorem jk_isRoot_A1 : IsRoot TwistTag.D4.tag rootA1 := mem_rootFinset.1 (by decide +kernel)
private theorem jk_isRoot_A3 : IsRoot TwistTag.D4.tag rootA3 := mem_rootFinset.1 (by decide +kernel)

private theorem jk_commute_CD_short (r r' t : K) :
    Commute (pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r')
      (pinnedX TwistTag.D4.tag K rootA0 t * pinnedX TwistTag.D4.tag K rootA1 t *
        pinnedX TwistTag.D4.tag K rootA3 t) := by
  have hC0 : Commute (pinnedX TwistTag.D4.tag K rootC r) (pinnedX TwistTag.D4.tag K rootA0 t) :=
    (commute_pinnedX_of_not_isRoot_add jk_isRoot_A0 isRoot_rootC (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) t r).symm
  have hC1 : Commute (pinnedX TwistTag.D4.tag K rootC r) (pinnedX TwistTag.D4.tag K rootA1 t) :=
    (commute_pinnedX_of_not_isRoot_add jk_isRoot_A1 isRoot_rootC (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) t r).symm
  have hC3 : Commute (pinnedX TwistTag.D4.tag K rootC r) (pinnedX TwistTag.D4.tag K rootA3 t) :=
    (commute_pinnedX_of_not_isRoot_add jk_isRoot_A3 isRoot_rootC (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) t r).symm
  have hD0 : Commute (pinnedX TwistTag.D4.tag K rootD r') (pinnedX TwistTag.D4.tag K rootA0 t) :=
    (commute_pinnedX_of_not_isRoot_add jk_isRoot_A0 isRoot_rootD (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) t r').symm
  have hD1 : Commute (pinnedX TwistTag.D4.tag K rootD r') (pinnedX TwistTag.D4.tag K rootA1 t) :=
    (commute_pinnedX_of_not_isRoot_add jk_isRoot_A1 isRoot_rootD (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) t r').symm
  have hD3 : Commute (pinnedX TwistTag.D4.tag K rootD r') (pinnedX TwistTag.D4.tag K rootA3 t) :=
    (commute_pinnedX_of_not_isRoot_add jk_isRoot_A3 isRoot_rootD (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) t r').symm
  have h0 := (Commute.mul_left hC0 hD0)
  have h1 := (Commute.mul_left hC1 hD1)
  have h3 := (Commute.mul_left hC3 hD3)
  exact Commute.mul_right (Commute.mul_right h0 h1) h3

private theorem jk_inv_shortA (t : K) :
    (pinnedX TwistTag.D4.tag K rootA0 t * pinnedX TwistTag.D4.tag K rootA1 t *
        pinnedX TwistTag.D4.tag K rootA3 t)⁻¹ =
      pinnedX TwistTag.D4.tag K rootA0 (-t) * pinnedX TwistTag.D4.tag K rootA1 (-t) *
        pinnedX TwistTag.D4.tag K rootA3 (-t) := by
  have c01 : Commute (pinnedX TwistTag.D4.tag K rootA0 (-t))
      (pinnedX TwistTag.D4.tag K rootA1 (-t)) :=
    commute_pinnedX_of_not_isRoot_add jk_isRoot_A0 jk_isRoot_A1 (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  have c03 : Commute (pinnedX TwistTag.D4.tag K rootA0 (-t))
      (pinnedX TwistTag.D4.tag K rootA3 (-t)) :=
    commute_pinnedX_of_not_isRoot_add jk_isRoot_A0 jk_isRoot_A3 (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  have c13 : Commute (pinnedX TwistTag.D4.tag K rootA1 (-t))
      (pinnedX TwistTag.D4.tag K rootA3 (-t)) :=
    commute_pinnedX_of_not_isRoot_add jk_isRoot_A1 jk_isRoot_A3 (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  rw [mul_inv_rev, mul_inv_rev, pinnedX_neg, pinnedX_neg, pinnedX_neg]
  exact jk_prod_rev_of_pairwise c01 c03 c13

private theorem jk_pow_three_longForm (s r r' : K) :
    (pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      pinnedX TwistTag.D4.tag K rootD r') ^ 3 = 1 := by
  obtain ⟨ε, -, hcomm⟩ := exists_commutator_pinnedX_of_sum (K := K) (α := rootB) (β := rootC)
    (γ := rootD) isRoot_rootB isRoot_rootC (by decide) (by decide) (by decide) isRoot_rootD
  have hc : pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r *
      (pinnedX TwistTag.D4.tag K rootB s)⁻¹ * (pinnedX TwistTag.D4.tag K rootC r)⁻¹ =
        pinnedX TwistTag.D4.tag K rootD (ε * s * r) := by
    rw [← commutatorElement_def]
    exact hcomm s r
  have hyx : pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootB s =
      pinnedX TwistTag.D4.tag K rootD (-(ε * s * r)) *
        (pinnedX TwistTag.D4.tag K rootB s * pinnedX TwistTag.D4.tag K rootC r) := by
    rw [← pinnedX_neg, ← hc]
    group
  have hdx : Commute (pinnedX TwistTag.D4.tag K rootD (-(ε * s * r)))
      (pinnedX TwistTag.D4.tag K rootB s) :=
    commute_pinnedX_of_not_isRoot_add isRoot_rootD isRoot_rootB (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  have hdy : Commute (pinnedX TwistTag.D4.tag K rootD (-(ε * s * r)))
      (pinnedX TwistTag.D4.tag K rootC r) :=
    commute_pinnedX_of_not_isRoot_add isRoot_rootD isRoot_rootC (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  have hxz : Commute (pinnedX TwistTag.D4.tag K rootB s) (pinnedX TwistTag.D4.tag K rootD r') :=
    commute_pinnedX_of_not_isRoot_add isRoot_rootB isRoot_rootD (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  have hyz : Commute (pinnedX TwistTag.D4.tag K rootC r) (pinnedX TwistTag.D4.tag K rootD r') :=
    commute_pinnedX_of_not_isRoot_add isRoot_rootC isRoot_rootD (by decide) (by decide)
      (jk_not_isRoot_of_not_mem (by decide +kernel)) _ _
  rw [(Commute.mul_left hxz hyz).mul_pow 3, jk_pow_three_mul_of_comm hyx hdx hdy]
  simp only [jk_pinnedX_pow_three, one_mul, mul_one]

end Char3

section Coord

variable {K : Type} [Field K] [Finite K]

private theorem jk_pinnedX_rootC_mem (r : K) :
    pinnedX TwistTag.D4.tag K rootC r ∈ heightSeries TwistTag.D4.tag K 2 :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧ (2 : ℤ) ≤ height α})
    ⟨isRoot_rootC, by rw [height_rootC]; norm_num, by rw [height_rootC]; norm_num⟩ r

private theorem jk_pinnedX_rootD_mem (r : K) :
    pinnedX TwistTag.D4.tag K rootD r ∈ heightSeries TwistTag.D4.tag K 2 :=
  pinnedX_mem_rootSpan (S := {α | IsRoot TwistTag.D4.tag α ∧ 0 < height α ∧ (2 : ℤ) ≤ height α})
    ⟨isRoot_rootD, by rw [height_rootD]; norm_num, by rw [height_rootD]; norm_num⟩ r

private theorem jk_coordC_CD (r r' : K) :
    coordC (pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r') = r := by
  rw [coordC_mul (jk_pinnedX_rootC_mem r) (jk_pinnedX_rootD_mem r'),
    coordC_pinnedX isRoot_rootC (by rw [height_rootC]; norm_num) r,
    coordC_pinnedX isRoot_rootD (by rw [height_rootD]; norm_num) r', if_pos rfl,
    if_neg (show ¬ (rootD = rootC) by decide), add_zero]

private theorem jk_coordC_one : coordC (1 : ModGL TwistTag.D4.tag K) = 0 := by
  have h := coordC_mul (K := K) (x := 1) (y := 1)
    ((heightSeries TwistTag.D4.tag K 2).one_mem) ((heightSeries TwistTag.D4.tag K 2).one_mem)
  rw [mul_one] at h
  linear_combination -h

private theorem jk_coordC_inv {x : ModGL TwistTag.D4.tag K}
    (hx : x ∈ heightSeries TwistTag.D4.tag K 2) : coordC x⁻¹ = -coordC x := by
  have h := coordC_mul (K := K) (x := x) (y := x⁻¹) hx
    ((heightSeries TwistTag.D4.tag K 2).inv_mem hx)
  rw [mul_inv_cancel, jk_coordC_one] at h
  linear_combination -h

end Coord

private theorem jk_fa_pow_three {f : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f)) :
    fieldActor (t := TwistTag.D4) σ σ ^ 3 = 1 := by
  have hσ3 : σ ^ 3 = 1 := by
    ext c
    exact ringEquiv_cube_apply_eq hK hσ c
  have h1 : fieldActor (t := TwistTag.D4) σ (σ ^ 3) = fieldActor σ σ ^ 3 :=
    map_pow (fieldActorHom (t := TwistTag.D4) σ) σ 3
  rw [← h1, hσ3, fieldActor_one]

variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 3]
  (hK : Nat.card K = (3 ^ f) ^ 3) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ f))
include hf hK hσ

private theorem jk_fieldActor_longElt {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) (c : K) (hc : σ c = c) :
    fieldActor (t := TwistTag.D4) σ σ (longElt hf hK σ hσ hγ c hc) =
      longElt hf hK σ hσ hγ c hc := by
  apply Subtype.ext
  rw [coe_fieldActor, coe_longElt]
  have e : Units.map (entrywiseHom σ.toRingHom) (pinnedX TwistTag.D4.tag K γ c) =
      pinnedX TwistTag.D4.tag K γ (σ c) := Units.ext (entrywise_pinnedX σ.toRingHom γ c)
  rw [e, hc]

private theorem jk_longElt_pow_three {γ : Fin TwistTag.D4.tag.rank → ℤ}
    (hγ : γ = rootB ∨ γ = rootC ∨ γ = rootD) (c : K) (hc : σ c = c) :
    longElt hf hK σ hσ hγ c hc ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, coe_longElt, jk_pinnedX_pow_three, Subgroup.coe_one]

theorem exists_twistedConj_kill_C {s r r' r₁ : K} (hs : σ s = s) (hr : σ r = r) (hr' : σ r' = r')
    (hs0 : s ≠ 0) (hr₁ : σ r₁ = r₁) :
    ∃ (w : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (r'' : K) (hr'' : σ r'' = r''),
      w⁻¹ * (longElt hf hK σ hσ (Or.inl rfl) s hs * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr *
          longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr') *
        fieldActor (t := TwistTag.D4) σ σ w =
      longElt hf hK σ hσ (Or.inl rfl) s hs * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r₁ hr₁ *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'' := by
  obtain ⟨ε₀, hε₀, hnest⟩ := exists_nested_commutator_coord (K := K)
  have hε₀0 : ε₀ ≠ 0 := by
    rcases hε₀ with h | h <;> rw [h] <;> norm_num
  have hε₀σ : σ ε₀ = ε₀ := by
    rcases hε₀ with h | h <;> rw [h] <;> simp
  have hc0 : σ ((r₁ - r) / (ε₀ * s)) = (r₁ - r) / (ε₀ * s) := by
    rw [map_div₀, map_mul, map_sub, hε₀σ, hs, hr, hr₁]
  obtain ⟨t, ht⟩ := jk_exists_cube_eq ((r₁ - r) / (ε₀ * s))
  have htσ : σ t = t := by
    apply jk_cube_injective
    show σ t ^ 3 = t ^ 3
    rw [← map_pow σ t 3, ht]
    exact hc0
  have hts : ε₀ * s * t ^ 3 = r₁ - r := by
    rw [ht]
    field_simp
  obtain ⟨m, hm⟩ : ∃ m, m = longElt hf hK σ hσ (Or.inl rfl) s hs := ⟨_, rfl⟩
  obtain ⟨cc, hcc⟩ : ∃ cc, cc = longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr := ⟨_, rfl⟩
  obtain ⟨dd, hdd⟩ : ∃ dd, dd = longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr' := ⟨_, rfl⟩
  rw [← hm, ← hcc, ← hdd]
  obtain ⟨a, ha⟩ : ∃ a, a = shortElt hf hK σ hσ htσ := ⟨_, rfl⟩
  obtain ⟨Mq, hMq⟩ : ∃ x : ModGL TwistTag.D4.tag K, x = pinnedX TwistTag.D4.tag K rootB s :=
    ⟨_, rfl⟩
  obtain ⟨Cq, hCq⟩ : ∃ x : ModGL TwistTag.D4.tag K, x = pinnedX TwistTag.D4.tag K rootC r :=
    ⟨_, rfl⟩
  obtain ⟨Dq, hDq⟩ : ∃ x : ModGL TwistTag.D4.tag K, x = pinnedX TwistTag.D4.tag K rootD r' :=
    ⟨_, rfl⟩
  obtain ⟨Aq, hAq⟩ : ∃ x : ModGL TwistTag.D4.tag K,
      x = pinnedX TwistTag.D4.tag K rootA0 t * pinnedX TwistTag.D4.tag K rootA1 t *
        pinnedX TwistTag.D4.tag K rootA3 t := ⟨_, rfl⟩
  have hmC : (m : ModGL TwistTag.D4.tag K) = Mq := by
    rw [hm, coe_longElt, hMq]
  have hccC : (cc : ModGL TwistTag.D4.tag K) = Cq := by
    rw [hcc, coe_longElt, hCq]
  have hddC : (dd : ModGL TwistTag.D4.tag K) = Dq := by
    rw [hdd, coe_longElt, hDq]
  have haC : (a : ModGL TwistTag.D4.tag K) = Aq := by
    rw [ha, coe_shortElt hf hK σ hσ htσ, hAq]
  have hmU : (m : ModGL TwistTag.D4.tag K) ∈
      graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom := by
    rw [hmC, hMq]
    exact pinnedX_mem_graphFixedPosUnipotent hf hK σ hσ (Or.inl rfl) hs
  have hδm : fieldActor (t := TwistTag.D4) σ σ m = m := by
    rw [hm]
    exact jk_fieldActor_longElt hf hK σ hσ (Or.inl rfl) s hs
  have hδc : fieldActor (t := TwistTag.D4) σ σ cc = cc := by
    rw [hcc]
    exact jk_fieldActor_longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r hr
  have hδd : fieldActor (t := TwistTag.D4) σ σ dd = dd := by
    rw [hdd]
    exact jk_fieldActor_longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r' hr'
  have hδa : fieldActor (t := TwistTag.D4) σ σ a = a := by
    rw [ha]
    exact fieldActor_shortElt hf hK σ hσ htσ
  have hm3 : m ^ 3 = 1 := by
    rw [hm]
    exact jk_longElt_pow_three hf hK σ hσ (Or.inl rfl) s hs
  have hmc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) m = 1 :=
    cocycleProd_eq_one_of_fixed_cube hf hK σ hσ m hδm hm3
  have hy3 : (m * cc * dd) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_mul, hmC, hccC, hddC, Subgroup.coe_one,
      hMq, hCq, hDq]
    exact jk_pow_three_longForm s r r'
  have hδy : fieldActor (t := TwistTag.D4) σ σ (m * cc * dd) = m * cc * dd := by
    rw [map_mul, map_mul, hδm, hδc, hδd]
  have hyc : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) (m * cc * dd) = 1 := by
    simp only [cocycleProd, hδy]
    rw [← pow_three']
    exact hy3
  obtain ⟨y₁, hy₁⟩ : ∃ y₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      y₁ = a⁻¹ * (m * cc * dd) * a := ⟨_, rfl⟩
  have hyc₁ : cocycleProd (fieldActor (t := TwistTag.D4) σ σ) y₁ = 1 := by
    have h := cocycleProd_twistedConj (jk_fa_pow_three hK σ hσ) (m * cc * dd) a
    rw [hδa, hyc, mul_one, inv_mul_cancel] at h
    rw [hy₁]
    exact h
  have hnest' := hnest (-s) (-t)
  have hCD : pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r' ∈
      heightSeries TwistTag.D4.tag K 2 :=
    (heightSeries TwistTag.D4.tag K 2).mul_mem (jk_pinnedX_rootC_mem r) (jk_pinnedX_rootD_mem r')
  have hP2eq : ((m⁻¹ * y₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) =
      ⁅pinnedX TwistTag.D4.tag K rootB (-s), pinnedX TwistTag.D4.tag K rootA0 (-t) *
        pinnedX TwistTag.D4.tag K rootA1 (-t) * pinnedX TwistTag.D4.tag K rootA3 (-t)⁆ *
      (pinnedX TwistTag.D4.tag K rootC r * pinnedX TwistTag.D4.tag K rootD r') := by
    rw [← pinnedX_neg TwistTag.D4.tag K rootB s, ← jk_inv_shortA t]
    simp only [hy₁, Subgroup.coe_mul, Subgroup.coe_inv, hmC, haC, hccC, hddC]
    rw [hMq, hCq, hDq, hAq]
    exact jk_conj_decomp (jk_commute_CD_short r r' t)
  have hP2mem : ((m⁻¹ * y₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K 2 := by
    rw [hP2eq]
    exact (heightSeries TwistTag.D4.tag K 2).mul_mem hnest'.1 hCD
  have hP2coord : coordC ((m⁻¹ * y₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) :
      ModGL TwistTag.D4.tag K) = ε₀ * s * t ^ 3 + r := by
    rw [hP2eq, coordC_mul hnest'.1 hCD, jk_coordC_CD, hnest'.2]
    ring
  have hP2L : m⁻¹ * y₁ ∈ layerN σ 1 :=
    (mem_layerN σ).2 (by rw [show ((1 + 1 : ℕ) : ℤ) = 2 by norm_num]; exact hP2mem)
  obtain ⟨W, hWmem, hkill⟩ := exists_kill_layers_one_two hf hK σ hσ hmU hmc hyc₁ hP2L
  obtain ⟨r₂, r'', hr₂, hr'', hlong⟩ := exists_long_form_of_mem_layerN_three hf hK σ hσ ⟨_, hkill⟩
  have hWq2 : (W : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 2 := by
    have h := (mem_layerN σ).1 hWmem
    rwa [show ((1 + 1 : ℕ) : ℤ) = 2 by norm_num] at h
  have hWq2inv : ((W : ModGL TwistTag.D4.tag K))⁻¹ ∈
      heightSeries TwistTag.D4.tag K 2 := (heightSeries TwistTag.D4.tag K 2).inv_mem hWq2
  have hP3 : (fieldActor (t := TwistTag.D4) σ σ W : ModGL TwistTag.D4.tag K) ∈
      heightSeries TwistTag.D4.tag K 2 := by
    have h := (mem_layerN σ).1 ((cocycleData_delta0 σ).stable 1 W hWmem)
    rwa [show ((1 + 1 : ℕ) : ℤ) = 2 by norm_num] at h
  have hcoordP3 : coordC (fieldActor (t := TwistTag.D4) σ σ W : ModGL TwistTag.D4.tag K) =
      coordC (W : ModGL TwistTag.D4.tag K) :=
    coordC_fieldActor hf hK σ hσ W hWq2
  have hMpos0 : Mq ∈ posUnipotent TwistTag.D4.tag K := by
    rw [← hmC]
    exact (Subgroup.mem_inf.1 hmU).1
  have hP1 : Mq⁻¹ * (W : ModGL TwistTag.D4.tag K)⁻¹ *
      Mq ∈ heightSeries TwistTag.D4.tag K 2 := by
    have hN := heightSeries_normal (τ := TwistTag.D4.tag) K 2
    have hWpos : ((W : ModGL TwistTag.D4.tag K))⁻¹ ∈
        posUnipotent TwistTag.D4.tag K := heightSeries_le_posUnipotent 2 hWq2inv
    have hmem := hN.conj_mem ⟨_, hWpos⟩ (Subgroup.mem_subgroupOf.2 hWq2inv) ⟨Mq⁻¹, inv_mem hMpos0⟩
    have hval := Subgroup.mem_subgroupOf.1 hmem
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hval
  have hcoordP1 : coordC (Mq⁻¹ * (W : ModGL TwistTag.D4.tag K)⁻¹ * Mq) =
      coordC ((W : ModGL TwistTag.D4.tag K)⁻¹) := by
    have h := coordC_conj_rootB (K := K) (-s) hWq2inv
    have e1 : pinnedX TwistTag.D4.tag K rootB (-s) = Mq⁻¹ := by
      rw [hMq, pinnedX_neg]
    have e2 : (pinnedX TwistTag.D4.tag K rootB (-s))⁻¹ = Mq := by
      rw [e1, inv_inv]
    rw [e2, e1] at h
    exact h
  have hZdec : ((m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W) :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
      (Mq⁻¹ * (W : ModGL TwistTag.D4.tag K)⁻¹ * Mq) *
        ((m⁻¹ * y₁ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) *
        (fieldActor (t := TwistTag.D4) σ σ W : ModGL TwistTag.D4.tag K) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hmC]
    group
  have hZcoord : coordC ((m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W) :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) = r₁ := by
    rw [hZdec, coordC_mul ((heightSeries TwistTag.D4.tag K 2).mul_mem hP1 hP2mem) hP3,
      coordC_mul hP1 hP2mem, hcoordP1, jk_coordC_inv hWq2, hP2coord, hcoordP3]
    linear_combination hts
  have hZr₂ : coordC ((m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W) :
      graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) = r₂ := by
    have hZeq : ((m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        pinnedX TwistTag.D4.tag K rootC r₂ * pinnedX TwistTag.D4.tag K rootD r'' := hlong
    rw [hZeq, jk_coordC_CD]
  have hr₂eq : r₂ = r₁ := hZr₂.symm.trans hZcoord
  have hkey : m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W) =
      longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r₁ hr₁ *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'' := by
    apply Subtype.ext
    have e : ((longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r₁ hr₁ *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'' :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        pinnedX TwistTag.D4.tag K rootC r₁ * pinnedX TwistTag.D4.tag K rootD r'' := by
      rw [Subgroup.coe_mul, coe_longElt, coe_longElt]
    rw [e, ← hr₂eq]
    have hZeq : ((m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W) :
        graphFixedRootGroup TwistTag.D4 K σ.toRingHom) : ModGL TwistTag.D4.tag K) =
        pinnedX TwistTag.D4.tag K rootC r₂ * pinnedX TwistTag.D4.tag K rootD r'' := hlong
    exact hZeq
  refine ⟨a * W, r'', hr'', ?_⟩
  rw [map_mul, hδa]
  calc (a * W)⁻¹ * (m * cc * dd) * (a * fieldActor (t := TwistTag.D4) σ σ W)
      = W⁻¹ * (a⁻¹ * (m * cc * dd) * a) * fieldActor (t := TwistTag.D4) σ σ W := by group
    _ = m * (m⁻¹ * (W⁻¹ * y₁ * fieldActor (t := TwistTag.D4) σ σ W)) := by
      rw [hy₁]
      group
    _ = m * (longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r₁ hr₁ *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'') := by rw [hkey]
    _ = m * longElt hf hK σ hσ (Or.inr (Or.inl rfl)) r₁ hr₁ *
        longElt hf hK σ hσ (Or.inr (Or.inr rfl)) r'' hr'' := by rw [mul_assoc]

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
