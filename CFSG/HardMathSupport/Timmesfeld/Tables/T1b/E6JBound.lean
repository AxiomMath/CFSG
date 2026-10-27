module

public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.UpperReduce
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.TorusBound
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6WeylFix
public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.E6TorusLower

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.T1b

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.Open CFSG.SectionRank
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open scoped Matrix

variable {K : Type} [Field K]

section Faithful

theorem weylAct_injective [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {w w' : WeylGroup Tag.E6} (h : ∀ a : Fin Tag.E6.rank → Kˣ, weylAct w a = weylAct w' a) :
    w = w' := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 (by rw [Nat.card_units]; exact h3)
  have hv : ∀ v, e6WeylMat w *ᵥ v = e6WeylMat w' *ᵥ v := fun v => by
    apply cubeTuple_injective hζ
    rw [← weylAct_cubeTuple hζ, ← weylAct_cubeTuple hζ, h]
  apply e6WeylMat_injective
  ext i j
  have := congrFun (hv (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

end Faithful

section Basic


theorem canonicalRep_mem_monomialSubgroup (w : WeylGroup Tag.E6) :
    canonicalRep (coxeterSystem Tag.E6) K w ∈ monomialSubgroup Tag.E6 K :=
  Subgroup.mem_sup_right (canonicalRep_mem_closure (coxeterSystem Tag.E6) K w)

@[expose] noncomputable def nwMono (w : WeylGroup Tag.E6) : monomialSubgroup Tag.E6 K :=
  ⟨canonicalRep (coxeterSystem Tag.E6) K w, canonicalRep_mem_monomialSubgroup w⟩

@[expose] noncomputable def cmHom : monomialSubgroup Tag.E6 K →* adjointGroup Tag.E6 K :=
  Subgroup.inclusion monomialSubgroup_le_adjointGroup'

theorem coe_cmHom (m : monomialSubgroup Tag.E6 K) :
    ((cmHom m : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) = m := rfl

noncomputable abbrev e6TH : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
  (rootDiagAutHom Tag.E6 K).range

@[expose] noncomputable def e6NJ : Subgroup (MulAut (adjointGroup Tag.E6 K)) :=
  (MulAut.conj.comp (cmHom (K := K))).range ⊔ e6TH

theorem e6NJ_le_diagJ : e6NJ (K := K) ≤ diagJ K :=
  sup_le (by rintro _ ⟨m, rfl⟩; exact Subgroup.mem_sup_left ⟨cmHom m, rfl⟩) le_sup_right

theorem e6TH_le_e6NJ : e6TH (K := K) ≤ e6NJ := le_sup_right

theorem conj_nwMono_mem_e6NJ (w : WeylGroup Tag.E6) :
    MulAut.conj (cmHom (nwMono (K := K) w)) ∈ e6NJ (K := K) :=
  Subgroup.mem_sup_left ⟨nwMono w, rfl⟩

end Basic

section Monomial


theorem weylQuotientHom_nwMono (w : WeylGroup Tag.E6) :
    weylQuotientHom Tag.E6 K (nwMono w) = w :=
  weylQuotientHom_eq (mapsRootLines_canonicalRep w)

theorem exists_rootDiagUnit_conj_monomial (a : Fin Tag.E6.rank → Kˣ)
    (m : monomialSubgroup Tag.E6 K) :
    ∃ m' : monomialSubgroup Tag.E6 K, (m' : ModGL Tag.E6 K) =
        rootDiagUnit Tag.E6 a * m * (rootDiagUnit Tag.E6 a)⁻¹ ∧
      weylQuotientHom Tag.E6 K m' = weylQuotientHom Tag.E6 K m := by
  obtain ⟨w, k, hk, hgk⟩ := monomialSubgroup_le_torusWeylCosets m.2
  obtain ⟨t, ht, hnt⟩ := exists_conj_canonicalRep (K := K) a w
  have hmem : k * t * canonicalRep (coxeterSystem Tag.E6) K w ∈ monomialSubgroup Tag.E6 K :=
    mul_mem (mul_mem (torusGroup_le_monomialSubgroup hk) (torusGroup_le_monomialSubgroup ht))
      (canonicalRep_mem_monomialSubgroup w)
  have heq : rootDiagUnit Tag.E6 a * (m : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 a)⁻¹ =
      k * t * canonicalRep (coxeterSystem Tag.E6) K w := by
    rw [hgk]
    calc rootDiagUnit Tag.E6 a * (k * canonicalRep (coxeterSystem Tag.E6) K w) *
          (rootDiagUnit Tag.E6 a)⁻¹ =
        (rootDiagUnit Tag.E6 a * k * (rootDiagUnit Tag.E6 a)⁻¹) *
          (rootDiagUnit Tag.E6 a * canonicalRep (coxeterSystem Tag.E6) K w *
            (rootDiagUnit Tag.E6 a)⁻¹) := by group
      _ = k * t * canonicalRep (coxeterSystem Tag.E6) K w := by
        rw [conj_rootDiagUnit_of_mem_torusGroup a hk, hnt, mul_assoc]
  refine ⟨⟨_, hmem⟩, heq.symm, ?_⟩
  have h1 : MapsRootLines (k * t * canonicalRep (coxeterSystem Tag.E6) K w) w := by
    simpa using ((mapsRootLines_of_mem_torusGroup hk).mul
      (mapsRootLines_of_mem_torusGroup ht)).mul (mapsRootLines_canonicalRep w)
  have h2 : MapsRootLines (m : ModGL Tag.E6 K) w := by
    rw [hgk]
    simpa using (mapsRootLines_of_mem_torusGroup hk).mul (mapsRootLines_canonicalRep w)
  rw [weylQuotientHom_eq (g := ⟨_, hmem⟩) h1, weylQuotientHom_eq h2]

theorem conj_cm_rootDiagAut (m : monomialSubgroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ) :
    MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a * (MulAut.conj (cmHom m))⁻¹ =
      rootDiagAutHom Tag.E6 K (weylAct (weylQuotientHom Tag.E6 K m) a) := by
  have h := monomial_conj_rootDiagUnit m a
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [← map_inv, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply]
  change (m : ModGL Tag.E6 K) * (rootDiagUnit Tag.E6 a * ((m : ModGL Tag.E6 K)⁻¹ * x *
    (m : ModGL Tag.E6 K)⁻¹⁻¹) * (rootDiagUnit Tag.E6 a)⁻¹) * (m : ModGL Tag.E6 K)⁻¹ =
    rootDiagUnit Tag.E6 (weylAct (weylQuotientHom Tag.E6 K m) a) * x *
      (rootDiagUnit Tag.E6 (weylAct (weylQuotientHom Tag.E6 K m) a))⁻¹
  rw [← h]
  group

theorem exists_rootDiagAut_mul_conj (a : Fin Tag.E6.rank → Kˣ) (m : monomialSubgroup Tag.E6 K) :
    ∃ m' : monomialSubgroup Tag.E6 K,
      rootDiagAutHom Tag.E6 K a * MulAut.conj (cmHom m) =
        MulAut.conj (cmHom m') * rootDiagAutHom Tag.E6 K a ∧
      weylQuotientHom Tag.E6 K m' = weylQuotientHom Tag.E6 K m := by
  obtain ⟨m', hm', hρ⟩ := exists_rootDiagUnit_conj_monomial a m
  refine ⟨m', ?_, hρ⟩
  have hβ : rootDiagAutHom Tag.E6 K a (cmHom m) = cmHom m' :=
    Subtype.ext (by rw [coe_cmHom, hm']; rfl)
  rw [mulAut_mul_conj, hβ]

theorem exists_nf_mul (m₁ m₂ : monomialSubgroup Tag.E6 K) (a₁ a₂ : Fin Tag.E6.rank → Kˣ) :
    ∃ m' : monomialSubgroup Tag.E6 K, weylQuotientHom Tag.E6 K m' = weylQuotientHom Tag.E6 K m₂ ∧
      MulAut.conj (cmHom m₁) * rootDiagAutHom Tag.E6 K a₁ *
          (MulAut.conj (cmHom m₂) * rootDiagAutHom Tag.E6 K a₂) =
        MulAut.conj (cmHom (m₁ * m')) * rootDiagAutHom Tag.E6 K (a₁ * a₂) := by
  obtain ⟨m', hm', hρ⟩ := exists_rootDiagAut_mul_conj a₁ m₂
  refine ⟨m', hρ, ?_⟩
  rw [map_mul, map_mul, map_mul]
  calc MulAut.conj (cmHom m₁) * rootDiagAutHom Tag.E6 K a₁ *
        (MulAut.conj (cmHom m₂) * rootDiagAutHom Tag.E6 K a₂) =
      MulAut.conj (cmHom m₁) * (rootDiagAutHom Tag.E6 K a₁ * MulAut.conj (cmHom m₂)) *
        rootDiagAutHom Tag.E6 K a₂ := by group
    _ = _ := by rw [hm']; group

@[expose] noncomputable def e6NJnf : Subgroup (MulAut (adjointGroup Tag.E6 K)) where
  carrier := {x | ∃ (m : monomialSubgroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
    x = MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a}
  mul_mem' := by
    rintro _ _ ⟨m₁, a₁, rfl⟩ ⟨m₂, a₂, rfl⟩
    obtain ⟨m', -, h⟩ := exists_nf_mul m₁ m₂ a₁ a₂
    exact ⟨_, _, h⟩
  one_mem' := ⟨1, 1, by rw [map_one, map_one, map_one, mul_one]⟩
  inv_mem' := by
    rintro _ ⟨m, a, rfl⟩
    obtain ⟨m', hm', -⟩ := exists_rootDiagAut_mul_conj a⁻¹ m⁻¹
    refine ⟨m', a⁻¹, ?_⟩
    rw [mul_inv_rev, ← map_inv, ← map_inv, ← map_inv, hm']

theorem mem_e6NJ_iff {x : MulAut (adjointGroup Tag.E6 K)} :
    x ∈ e6NJ (K := K) ↔ ∃ (m : monomialSubgroup Tag.E6 K) (a : Fin Tag.E6.rank → Kˣ),
      x = MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a := by
  constructor
  · intro hx
    have hle : e6NJ (K := K) ≤ e6NJnf := sup_le
      (by rintro _ ⟨m, rfl⟩; exact ⟨m, 1, by rw [map_one, mul_one]; rfl⟩)
      (by rintro _ ⟨a, rfl⟩; exact ⟨1, a, by rw [map_one, map_one, one_mul]⟩)
    exact hle hx
  · rintro ⟨m, a, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left ⟨m, rfl⟩) (Subgroup.mem_sup_right ⟨a, rfl⟩)

theorem nf_conj_rootDiagAut (m : monomialSubgroup Tag.E6 K) (a c : Fin Tag.E6.rank → Kˣ) :
    MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a * rootDiagAutHom Tag.E6 K c *
        (MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a)⁻¹ =
      rootDiagAutHom Tag.E6 K (weylAct (weylQuotientHom Tag.E6 K m) c) := by
  have hc : rootDiagAutHom Tag.E6 K a * rootDiagAutHom Tag.E6 K c *
      (rootDiagAutHom Tag.E6 K a)⁻¹ = rootDiagAutHom Tag.E6 K c := by
    rw [← map_mul, ← map_inv, ← map_mul, mul_inv_cancel_comm]
  calc _ = MulAut.conj (cmHom m) * (rootDiagAutHom Tag.E6 K a * rootDiagAutHom Tag.E6 K c *
        (rootDiagAutHom Tag.E6 K a)⁻¹) * (MulAut.conj (cmHom m))⁻¹ := by group
    _ = _ := by rw [hc]; exact conj_cm_rootDiagAut m c

theorem weylQuotientHom_eq_of_nf_eq [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    {m m' : monomialSubgroup Tag.E6 K} {a b : Fin Tag.E6.rank → Kˣ}
    (h : MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a =
      MulAut.conj (cmHom m') * rootDiagAutHom Tag.E6 K b) :
    weylQuotientHom Tag.E6 K m = weylQuotientHom Tag.E6 K m' :=
  weylAct_injective h3 fun c => rootDiagAutHom_injective (by
    rw [← nf_conj_rootDiagAut m a c, h, nf_conj_rootDiagAut m' b c])

@[expose] noncomputable def e6NJFun (x : e6NJ (K := K)) : WeylGroup Tag.E6 :=
  weylQuotientHom Tag.E6 K (mem_e6NJ_iff.1 x.2).choose

theorem e6NJFun_eq [Finite K] (h3 : 3 ∣ Nat.card K - 1) (x : e6NJ (K := K))
    {m : monomialSubgroup Tag.E6 K} {a : Fin Tag.E6.rank → Kˣ}
    (hx : (x : MulAut (adjointGroup Tag.E6 K)) =
      MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a) :
    e6NJFun x = weylQuotientHom Tag.E6 K m := by
  obtain ⟨b, hb⟩ := (mem_e6NJ_iff.1 x.2).choose_spec
  exact weylQuotientHom_eq_of_nf_eq h3 (hb.symm.trans hx)

@[expose] noncomputable def e6NJHom [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    e6NJ (K := K) →* WeylGroup Tag.E6 where
  toFun := e6NJFun
  map_one' := by
    rw [e6NJFun_eq h3 1 (m := 1) (a := 1) (by simp), map_one]
  map_mul' x y := by
    obtain ⟨m₁, a₁, h₁⟩ := mem_e6NJ_iff.1 x.2
    obtain ⟨m₂, a₂, h₂⟩ := mem_e6NJ_iff.1 y.2
    obtain ⟨m', hρ, h⟩ := exists_nf_mul m₁ m₂ a₁ a₂
    rw [e6NJFun_eq h3 x h₁, e6NJFun_eq h3 y h₂,
      e6NJFun_eq h3 (x * y) (m := m₁ * m') (a := a₁ * a₂) (by rw [Subgroup.coe_mul, h₁, h₂, h]),
      map_mul, hρ]

theorem e6NJHom_apply [Finite K] (h3 : 3 ∣ Nat.card K - 1) (x : e6NJ (K := K))
    {m : monomialSubgroup Tag.E6 K} {a : Fin Tag.E6.rank → Kˣ}
    (hx : (x : MulAut (adjointGroup Tag.E6 K)) =
      MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a) :
    e6NJHom h3 x = weylQuotientHom Tag.E6 K m :=
  e6NJFun_eq h3 x hx

theorem e6NJHom_eq_one_iff [Finite K] (h3 : 3 ∣ Nat.card K - 1) (x : e6NJ (K := K)) :
    e6NJHom h3 x = 1 ↔ (x : MulAut (adjointGroup Tag.E6 K)) ∈ e6TH := by
  obtain ⟨m, a, hx⟩ := mem_e6NJ_iff.1 x.2
  rw [e6NJHom_apply h3 x hx]
  constructor
  · intro h1
    have hmaps : MapsRootLines (m : ModGL Tag.E6 K) 1 := h1 ▸ mapsRootLines_weylQuotientHom m
    obtain ⟨l, hl⟩ :=
      exists_rootDiagUnit_eq_of_mem_torusGroup (mem_torusGroup_of_mapsRootLines_one m.2 hmaps)
    have hconj : MulAut.conj (cmHom m) = rootDiagAutHom Tag.E6 K l :=
      MulEquiv.ext fun y => Subtype.ext (by
        rw [MulAut.conj_apply]
        change (m : ModGL Tag.E6 K) * y * (m : ModGL Tag.E6 K)⁻¹ =
          rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹
        rw [hl])
    rw [hx, hconj, ← map_mul]
    exact ⟨_, rfl⟩
  · rintro ⟨b, hb⟩
    have h1 : MulAut.conj (cmHom m) * rootDiagAutHom Tag.E6 K a =
        MulAut.conj (cmHom 1) * rootDiagAutHom Tag.E6 K b := by
      rw [← hx, ← hb, map_one, map_one, one_mul]
    exact (weylQuotientHom_eq_of_nf_eq h3 h1).trans (map_one _)

theorem e6NJHom_conj_nwMono [Finite K] (h3 : 3 ∣ Nat.card K - 1) (w : WeylGroup Tag.E6) :
    e6NJHom h3 ⟨_, conj_nwMono_mem_e6NJ (K := K) w⟩ = w := by
  rw [e6NJHom_apply h3 _ (m := nwMono w) (a := 1) (by rw [map_one, mul_one]),
    weylQuotientHom_nwMono]

theorem e6NJHom_surjective [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Function.Surjective (e6NJHom (K := K) h3) := fun w => ⟨_, e6NJHom_conj_nwMono h3 w⟩

theorem card_e6NJ [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    Nat.card (e6NJ (K := K)) = Nat.card (e6TH (K := K)) * 51840 := by
  have h := Subgroup.card_ker_mul_card_range (e6NJHom (K := K) h3)
  rw [MonoidHom.range_eq_top.2 (e6NJHom_surjective h3), Subgroup.card_top,
    card_weylGroup_E6'] at h
  have hker : (e6NJHom (K := K) h3).ker = e6TH.subgroupOf e6NJ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, e6NJHom_eq_one_iff]
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe e6TH_le_e6NJ).toEquiv] at h
  exact h.symm

end Monomial

section Index

open CFSG.Timmesfeld.ExceptionalOrders

@[expose] def e6LenSum (q : ℕ) : ℕ :=
  geomSum 2 1 q * geomSum 3 1 q * geomSum 4 1 q * geomSum 5 1 q *
    (geomSum 2 3 q * geomSum 8 1 q) * (geomSum 9 1 q * geomSum 3 4 q)

theorem e6LenSum_cast (q : ℕ) :
    (e6LenSum q : ZMod 243) = (e6LenSum (q % 243) : ZMod 243) := by
  simp only [e6LenSum, geomSum, Nat.cast_mul, Nat.cast_sum, Nat.cast_pow, ZMod.natCast_mod]

theorem not_dvd_e6LenSum_lt : ∀ r < 243, r % 3 = 1 → ¬ 243 ∣ e6LenSum r := by
  decide +kernel

theorem not_dvd_e6LenSum {q : ℕ} (hq : q % 3 = 1) : ¬ 243 ∣ e6LenSum q := by
  intro h
  have h1 : (e6LenSum q : ZMod 243) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [e6LenSum_cast] at h1
  exact not_dvd_e6LenSum_lt (q % 243) (Nat.mod_lt _ (by norm_num)) (by omega)
    ((ZMod.natCast_eq_zero_iff _ _).1 h1)


theorem card_adjointGroup_E6_eq [Finite K] :
    Nat.card (adjointGroup Tag.E6 K) =
      Nat.card (torusGroup Tag.E6 K) * Nat.card K ^ 36 * e6LenSum (Nat.card K) := by
  classical
  have : Fintype (WeylGroup Tag.E6) := Fintype.ofFinite _
  rw [card_adjointGroup, ncard_posRoots_E6, finsum_eq_sum_of_fintype, sum_length_E6]
  rfl

theorem mulAut_conj_injective_E6 [Finite K] :
    Function.Injective (MulAut.conj : adjointGroup Tag.E6 K →* MulAut (adjointGroup Tag.E6 K)) := by
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hZ := center_adjointGroup_eq_bot (τ := Tag.E6) (K := K)
  rw [injective_iff_map_eq_one]
  intro g hg
  have hc : g ∈ Subgroup.center (adjointGroup Tag.E6 K) := by
    rw [Subgroup.mem_center_iff]
    intro h
    have := congrArg (fun φ : MulAut (adjointGroup Tag.E6 K) => φ h) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact hc

theorem card_inner_E6 [Finite K] :
    Nat.card (inner (adjointGroup Tag.E6 K)) = Nat.card (adjointGroup Tag.E6 K) :=
  Nat.card_congr (MonoidHom.ofInjective mulAut_conj_injective_E6).toEquiv.symm

theorem card_torusGroup_dvd_inf [Finite K] :
    Nat.card (torusGroup Tag.E6 K) ∣
      Nat.card ↥(inner (adjointGroup Tag.E6 K) ⊓ e6TH (K := K)) := by
  set H := (torusGroup Tag.E6 K).subgroupOf (adjointGroup Tag.E6 K)
  have hle : H.map MulAut.conj ≤ inner (adjointGroup Tag.E6 K) ⊓ e6TH := by
    rintro _ ⟨h, hh, rfl⟩
    refine ⟨⟨h, rfl⟩, ?_⟩
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (Subgroup.mem_subgroupOf.1 hh)
    refine ⟨l, MulEquiv.ext fun y => Subtype.ext ?_⟩
    change rootDiagUnit Tag.E6 l * y * (rootDiagUnit Tag.E6 l)⁻¹ =
      (h : ModGL Tag.E6 K) * y * (h : ModGL Tag.E6 K)⁻¹
    rw [hl]
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective mulAut_conj_injective_E6,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe torusGroup_le_adjointGroup').toEquiv] at h1

theorem not_three_dvd_relIndex_e6NJ [Finite K]
    (h3 : 3 ∣ Nat.card K - 1) : ¬ 3 ∣ (e6NJ (K := K)).relIndex (diagJ K) := by
  intro hdvd
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  have hq : Nat.card K % 3 = 1 := by
    have := Finite.one_lt_card (α := K)
    omega
  have hA : (inner (adjointGroup Tag.E6 K)).relIndex (diagJ K) =
      (inner (adjointGroup Tag.E6 K)).relIndex e6TH :=
    Subgroup.relIndex_sup_left _ _
  have hle : inner (adjointGroup Tag.E6 K) ≤ diagJ K := le_sup_left
  have h2 := Subgroup.relIndex_mul_card (inner (adjointGroup Tag.E6 K)) (diagJ K)
  rw [inf_of_le_left hle, hA, card_inner_E6] at h2
  have h3' := Subgroup.relIndex_mul_card (inner (adjointGroup Tag.E6 K)) (e6TH (K := K))
  have h4 := Subgroup.relIndex_mul_card (e6NJ (K := K)) (diagJ K)
  rw [inf_of_le_left e6NJ_le_diagJ, card_e6NJ h3] at h4
  obtain ⟨u, hu⟩ := card_torusGroup_dvd_inf (K := K)
  have hc := card_adjointGroup_E6_eq (K := K)
  have ht : 0 < Nat.card (e6TH (K := K)) := Nat.card_pos
  have hH : 0 < Nat.card (torusGroup Tag.E6 K) := Nat.card_pos
  set i := (e6NJ (K := K)).relIndex (diagJ K)
  set r := (inner (adjointGroup Tag.E6 K)).relIndex (e6TH (K := K))
  set s := Nat.card ↥(inner (adjointGroup Tag.E6 K) ⊓ e6TH (K := K))
  set t := Nat.card (e6TH (K := K))
  set c := Nat.card (adjointGroup Tag.E6 K)
  have e1 : t * (i * 51840 * s) = t * c := by
    calc t * (i * 51840 * s) = i * (t * 51840) * s := by ring
      _ = r * c * s := by rw [h4, h2]
      _ = (r * s) * c := by ring
      _ = t * c := by rw [h3']
  have e2 := Nat.eq_of_mul_eq_mul_left ht e1
  rw [hu, hc] at e2
  have e3 : Nat.card (torusGroup Tag.E6 K) * (i * 51840 * u) =
      Nat.card (torusGroup Tag.E6 K) * (Nat.card K ^ 36 * e6LenSum (Nat.card K)) := by
    rw [← mul_assoc (Nat.card (torusGroup Tag.E6 K)) (Nat.card K ^ 36), ← e2]
    ring
  have e4 := Nat.eq_of_mul_eq_mul_left hH e3
  obtain ⟨i', hi'⟩ := hdvd
  have h243 : 243 ∣ Nat.card K ^ 36 * e6LenSum (Nat.card K) :=
    ⟨i' * 640 * u, by rw [← e4, hi']; ring⟩
  have hcop : Nat.Coprime 243 (Nat.card K ^ 36) :=
    Nat.Coprime.pow 5 36 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega))
  exact not_dvd_e6LenSum hq ((Nat.Coprime.dvd_mul_left hcop).1 h243)

end Index

theorem e6JBoundUntw :
    E6JBoundUntw := by
  intro K _ _ h3
  have : Finite (ModGL Tag.E6 K) := finite_modGL
  rw [pRank_eq_pRank_top_subgroup]
  set J := diagJ K
  set φ : (e6NJ (K := K)).subgroupOf J →* WeylGroup Tag.E6 :=
    (e6NJHom h3).comp (Subgroup.subgroupOfEquivOfLe e6NJ_le_diagJ).toMonoidHom with hφ
  have hφapp : ∀ n : (e6NJ (K := K)).subgroupOf J,
      φ n = e6NJHom h3 ⟨((n : J) : MulAut (adjointGroup Tag.E6 K)), n.2⟩ := fun n => rfl
  refine pRank_le_of_torus_normalizer Nat.prime_three ((e6NJ (K := K)).subgroupOf J)
    ((e6TH (K := K)).subgroupOf J) ?_ (not_three_dvd_relIndex_e6NJ h3) φ ?_ ?_
  · intro a ha b hb
    obtain ⟨x, hx⟩ := Subgroup.mem_subgroupOf.1 ha
    obtain ⟨y, hy⟩ := Subgroup.mem_subgroupOf.1 hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy, ← map_mul, ← map_mul, mul_comm]
  · intro n
    rw [hφapp, e6NJHom_eq_one_iff, Subgroup.mem_subgroupOf]
  · intro F S hF hS hSH hfix
    set f := rootDiagAutHom Tag.E6 K
    have hS₁ : S.map J.subtype ≤ f.range := by
      rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 (hSH hx)
    set S₀ := (S.map J.subtype).comap f
    have hcard : Nat.card S₀ = Nat.card S := by
      rw [← Subgroup.card_map_of_injective (rootDiagAutHom_injective (τ := Tag.E6) (K := K)),
        Subgroup.map_comap_eq_self hS₁,
        Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
    have hS₀ : IsElemAbelian 3 S₀ := by
      refine ⟨⟨⟨fun a b => Subtype.ext (mul_comm _ _)⟩⟩, fun a ha => ?_⟩
      obtain ⟨x, hx, hxa⟩ := ha
      apply rootDiagAutHom_injective (τ := Tag.E6) (K := K)
      rw [map_pow, map_one, ← hxa]
      exact congrArg Subtype.val (hS.2 x hx)
    have hfix₀ : ∀ a ∈ S₀, ∀ w ∈ F, weylAct w a = a := by
      intro a ha w hw
      obtain ⟨x, hx, hxa⟩ := ha
      have hJ : MulAut.conj (cmHom (nwMono (K := K) w)) ∈ J :=
        e6NJ_le_diagJ (conj_nwMono_mem_e6NJ w)
      let e : (e6NJ (K := K)).subgroupOf J := ⟨⟨_, hJ⟩, conj_nwMono_mem_e6NJ w⟩
      have hφe : φ e = w := by
        rw [hφapp]
        exact e6NJHom_conj_nwMono h3 w
      have h := congrArg Subtype.val (hfix x hx e (hφe ▸ hw))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      change MulAut.conj (cmHom (nwMono w)) * (x : MulAut (adjointGroup Tag.E6 K)) *
        (MulAut.conj (cmHom (nwMono w)))⁻¹ = (x : MulAut (adjointGroup Tag.E6 K)) at h
      have hxa' : (x : MulAut (adjointGroup Tag.E6 K)) = f a := hxa
      rw [hxa', conj_cm_rootDiagAut, weylQuotientHom_nwMono] at h
      exact rootDiagAutHom_injective h
    calc Nat.card S * Nat.card F = Nat.card S₀ * Nat.card F := by rw [hcard]
      _ ≤ Nat.card (e6Fix F) * Nat.card F :=
        Nat.mul_le_mul_right _ (card_le_card_e6Fix h3 F S₀ hS₀ hfix₀)
      _ ≤ 3 ^ 6 := card_e6Fix_mul_card_le F hF

end CFSG.HardMathSupport.Timmesfeld.Tables.T1b
