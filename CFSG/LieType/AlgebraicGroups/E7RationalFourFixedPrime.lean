module

public import CFSG.LieType.AlgebraicGroups.IdentityComponentLang

import CFSG.LieType.AlgebraicGroups.E7PairAdditiveCurve
import CFSG.LieType.AlgebraicGroups.FrobeniusFixedPrimeOrder
import CFSG.LieType.AlgebraicGroups.MonomialCentralizerRootCurves
import CFSG.RankThree.PartOne.KE.D4LayerAlgebraic

public noncomputable section

namespace CFSG.LieType.AlgebraicGroups

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem e7_rational_four_fixed_prime
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosure K L]
    (hK : ringChar K ≠ 2) (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (E : Subgroup (ModGL Tag.E7 L)) (hE : CFSG.Open.IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hER : E ≤ adjointGroup Tag.E7 L ⊓
      (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _)) :
    ∃ u : ModGL Tag.E7 L, u ∈ adjointGroup Tag.E7 L ∧ orderOf u = ringChar K ∧
      Units.map (entrywiseHom Fr) u = u ∧ ∀ e ∈ E, Commute u e := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set p := ringChar K with hpdef
  have hCharK : CharP K p := by rw [hpdef]; exact ringChar.charP K
  obtain ⟨e', hpp, hcardK⟩ := FiniteField.card K p
  have : Fact p.Prime := ⟨hpp⟩
  set e := (e' : ℕ) with hedef
  have he1 : 1 ≤ e := e'.pos
  have hcardK' : Nat.card K = p ^ e := by rw [Nat.card_eq_fintype_card, hcardK]
  have hp2 : p ≠ 2 := by rw [hpdef]; exact hK
  have hCharL : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  have hFrIt : iterateFrobenius L p e = Fr := RingHom.ext fun c => by
    rw [iterateFrobenius_def, hFr, hcardK']
  have halg : letI := ZMod.algebra L p; Algebra.IsAlgebraic (ZMod p) L :=
    CFSG.RankThree.PartOne.KE.isAlgebraic_zmod_of_isAlgClosure (ℓ := p) (k := K) (L := L)
  have : Finite E := Nat.finite_of_card_ne_zero (by rw [h4]; norm_num)
  have : Fintype E := Fintype.ofFinite E
  have hcardE : Fintype.card E = 4 := by rw [← Nat.card_eq_fintype_card]; exact h4
  obtain ⟨x₀, hx₀⟩ := Fintype.exists_ne_of_one_lt_card (α := E)
    (by rw [hcardE]; norm_num) (1 : E)
  have hpair : ({1, x₀} : Finset E).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simpa using (Ne.symm hx₀)),
      Finset.card_singleton]
  obtain ⟨y₀, -, hy₀⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, x₀} : Finset E)) (t := Finset.univ) (by
      rw [Finset.card_univ, hcardE, hpair]; norm_num)
  have hy₁ : y₀ ≠ 1 := fun h => hy₀ (by simp [h])
  have hyx : y₀ ≠ x₀ := fun h => hy₀ (by simp [h])
  set x : ModGL Tag.E7 L := (x₀ : ModGL Tag.E7 L) with hxdef
  set y : ModGL Tag.E7 L := (y₀ : ModGL Tag.E7 L) with hydef
  have hxE : x ∈ E := by rw [hxdef]; exact x₀.2
  have hyE : y ∈ E := by rw [hydef]; exact y₀.2
  have hx1 : x ≠ 1 := by
    rw [hxdef]
    exact fun h => hx₀ (Subtype.ext h)
  have hy1 : y ≠ 1 := by
    rw [hydef]
    exact fun h => hy₁ (Subtype.ext h)
  have hyx' : y ≠ x := by
    rw [hydef, hxdef]
    exact fun h => hyx (Subtype.ext h)
  have hx2 : x ^ 2 = 1 := hE.2 x hxE
  have hy2 : y ^ 2 = 1 := hE.2 y hyE
  have hxy : Commute x y := by
    have h := hE.1.is_comm.comm ⟨x, hxE⟩ ⟨y, hyE⟩
    exact congrArg Subtype.val h
  have hxx : x * x = 1 := by rw [← pow_two]; exact hx2
  have hyy : y * y = 1 := by rw [← pow_two]; exact hy2
  have hxy1 : x * y ≠ 1 := by
    intro h
    have h' : x * (x * y) = x * 1 := by rw [h]
    rw [← mul_assoc, hxx, one_mul, mul_one] at h'
    exact hyx' h'
  have hxyx : x * y ≠ x := by
    intro h
    have h' : x * (x * y) = x * x := by rw [h]
    rw [← mul_assoc, hxx, one_mul] at h'
    exact hy1 h'
  have hxyy : x * y ≠ y := by
    intro h
    have h' : (x * y) * y = y * y := by rw [h]
    rw [mul_assoc, hyy, mul_one] at h'
    exact hx1 h'
  have hn1 : (1 : ModGL Tag.E7 L) ∉ ({x, y, x * y} : Finset (ModGL Tag.E7 L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hx1, Ne.symm hy1, Ne.symm hxy1⟩
  have hn2 : x ∉ ({y, x * y} : Finset (ModGL Tag.E7 L)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨Ne.symm hyx', Ne.symm hxyx⟩
  have hn3 : y ∉ ({x * y} : Finset (ModGL Tag.E7 L)) := by
    simp only [Finset.mem_singleton]
    exact Ne.symm hxyy
  have hcard4f : ({1, x, y, x * y} : Finset (ModGL Tag.E7 L)).card = 4 := by
    rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
      Finset.card_insert_of_notMem hn3, Finset.card_singleton]
  have hcard4 : ({1, x, y, x * y} : Set (ModGL Tag.E7 L)).ncard = 4 := by
    have hcoe : (({1, x, y, x * y} : Finset (ModGL Tag.E7 L)) : Set (ModGL Tag.E7 L)) =
        ({1, x, y, x * y} : Set (ModGL Tag.E7 L)) := by simp
    rw [← hcoe, Set.ncard_coe_finset, hcard4f]
  have hsub : ({1, x, y, x * y} : Set (ModGL Tag.E7 L)) ⊆ E := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact E.one_mem
    · exact hxE
    · exact hyE
    · exact E.mul_mem hxE hyE
  have hEncard : (E : Set (ModGL Tag.E7 L)).ncard = 4 := by
    have h : Nat.card (E : Set (ModGL Tag.E7 L)) = 4 := by simpa using h4
    rwa [Nat.card_coe_set_eq] at h
  have hEeq : (E : Set (ModGL Tag.E7 L)) = {1, x, y, x * y} := by
    refine (Set.eq_of_subset_of_ncard_le hsub ?_ ?_).symm
    · rw [hEncard, hcard4]
    · exact Set.finite_coe_iff.1 inferInstance
  have hEelems : ∀ e : ModGL Tag.E7 L, e ∈ E → e = 1 ∨ e = x ∨ e = y ∨ e = x * y := by
    intro e he
    have h : e ∈ (E : Set (ModGL Tag.E7 L)) := he
    rw [hEeq] at h
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  set Z : Subgroup (ModGL Tag.E7 L) :=
    adjointGroup Tag.E7 L ⊓ Subgroup.centralizer ({x, y} : Set (ModGL Tag.E7 L)) with hZdef
  have hGc : IsPointClosed L (transportPoints (modGLPoint Tag.E7 L)
      ((adjointGroup Tag.E7 L : Subgroup (ModGL Tag.E7 L)) : Set (ModGL Tag.E7 L))) := by
    have h := (isConnectedAlgebraicSubgroup_adjointPointSubgroup Tag.E7 L).isPointClosed
    rwa [subgroupPoints_map] at h
  have hZc : IsPointClosed L (transportPoints (modGLPoint Tag.E7 L)
      (Z : Set (ModGL Tag.E7 L))) := by
    rw [hZdef]
    exact isPointClosed_inf hGc
      (isPointClosed_centralizer (T := ({x, y} : Set (ModGL Tag.E7 L))))
  have hxG : x ∈ adjointGroup Tag.E7 L := (hER hxE).1
  have hyG : y ∈ adjointGroup Tag.E7 L := (hER hyE).1
  obtain ⟨c, hc, hc0, hcadd, ⟨t₀, ht₀⟩, hcZ⟩ :=
    e7_exists_additive_curve_commute_pair (L := L) (p := p) hp2 halg hxG hyG hx2 hy2 hxy
  have hcZ' : ∀ t : L, c t ∈ Z := by
    intro t
    rw [hZdef, Subgroup.mem_inf]
    refine ⟨(hcZ t).1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hhx : h = x ∨ h = y := by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
    rcases hhx with rfl | rfl
    · exact ((hcZ t).2.1).symm
    · exact ((hcZ t).2.2).symm
  have hc_nsmul : ∀ (n : ℕ) (t : L), c (n • t) = c t ^ n := by
    intro n
    induction n with
    | zero => intro t; simpa using hc0
    | succ n ih =>
      intro t
      rw [succ_nsmul, hcadd, ih, pow_succ]
  have hc_pow : ∀ t : L, c t ^ p = 1 := by
    intro t
    have h := hc_nsmul p t
    rw [nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, hc0] at h
    exact h.symm
  let φ : Multiplicative L →* ModGL Tag.E7 L :=
    MonoidHom.mk' (fun t => c t.toAdd) (fun s t => hcadd s.toAdd t.toAdd)
  let V : Subgroup (ModGL Tag.E7 L) := φ.range
  have hVrange : (V : Set (ModGL Tag.E7 L)) = Set.range c := by
    ext v
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t.toAdd, rfl⟩
    · rintro ⟨t, rfl⟩
      exact ⟨Multiplicative.ofAdd t, rfl⟩
  have hV : V ≤ closedIdentityComponent Z := by
    intro v hv
    have hv' : v ∈ (V : Set (ModGL Tag.E7 L)) := hv
    rw [hVrange] at hv'
    obtain ⟨t, rfl⟩ := hv'
    exact mem_closedIdentityComponent_of_isPolynomialCurve (Z := Z) hc hcZ' (t₀ := 0) hc0 t
  have hVinf : (V : Set (ModGL Tag.E7 L)).Infinite := by
    rw [hVrange]
    exact infinite_range_of_isPolynomialCurve (k := L) (τ := Tag.E7) hc (s := t₀) (t := 0) (by
      rw [hc0]
      exact ht₀)
  have hVp : IsPGroup p V := by
    intro g
    refine ⟨1, ?_⟩
    have hmem : (g : ModGL Tag.E7 L) ∈ (V : Set (ModGL Tag.E7 L)) := g.2
    rw [hVrange] at hmem
    obtain ⟨t, ht⟩ := hmem
    have hgp : (g : ModGL Tag.E7 L) ^ p = 1 := by
      rw [← ht, hc_pow]
    exact Subtype.ext (by simpa using hgp)
  have hEF : ∀ g : ModGL Tag.E7 L,
      entrywiseFrobGL Tag.E7 L p e g = Units.map (entrywiseHom Fr) g := fun g => by
    show Units.map (entrywiseHom (iterateFrobenius L p e)) g =
      Units.map (entrywiseHom Fr) g
    rw [hFrIt]
  have hxη : entrywiseFrobGL Tag.E7 L p e x = x := by
    rw [hEF x]
    exact (hER hxE).2
  have hyη : entrywiseFrobGL Tag.E7 L p e y = y := by
    rw [hEF y]
    exact (hER hyE).2
  have hFZ : ∀ g ∈ Z, entrywiseFrobGL Tag.E7 L p e g ∈ Z := by
    intro g hg
    have hgG : g ∈ adjointGroup Tag.E7 L := by
      have h := hg
      rw [hZdef, Subgroup.mem_inf] at h
      exact h.1
    have hgc : g ∈ Subgroup.centralizer ({x, y} : Set (ModGL Tag.E7 L)) := by
      have h := hg
      rw [hZdef, Subgroup.mem_inf] at h
      exact h.2
    have hgx : x * g = g * x := Subgroup.mem_centralizer_iff.1 hgc x (by simp)
    have hgy : y * g = g * y := Subgroup.mem_centralizer_iff.1 hgc y (by simp)
    rw [hZdef, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact entrywiseFrobGL_mem (p := p) e hgG
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhx : h = x ∨ h = y := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hh
      rcases hhx with rfl | rfl
      · have h' := congrArg (entrywiseFrobGL Tag.E7 L p e) hgx
        simpa only [map_mul, hxη] using h'
      · have h' := congrArg (entrywiseFrobGL Tag.E7 L p e) hgy
        simpa only [map_mul, hyη] using h'
  obtain ⟨u, huH, huF, huord⟩ :=
    exists_entrywiseFrobGL_fixed_orderOf_eq_prime (τ := Tag.E7) (k := L) p
      halg hZc he1 hFZ hV hVinf hVp
  have huZ : u ∈ Z := closedIdentityComponent_le Z huH
  have huG : u ∈ adjointGroup Tag.E7 L := by
    have h := huZ
    rw [hZdef, Subgroup.mem_inf] at h
    exact h.1
  have huc : u ∈ Subgroup.centralizer ({x, y} : Set (ModGL Tag.E7 L)) := by
    have h := huZ
    rw [hZdef, Subgroup.mem_inf] at h
    exact h.2
  have hux : Commute u x := (Subgroup.mem_centralizer_iff.1 huc x (by simp)).symm
  have huy : Commute u y := (Subgroup.mem_centralizer_iff.1 huc y (by simp)).symm
  refine ⟨u, huG, huord.trans hpdef, ?_, ?_⟩
  · rw [← hEF u]
    exact huF
  · intro e he
    rcases hEelems e he with rfl | rfl | rfl | rfl
    · exact Commute.one_right u
    · exact hux
    · exact huy
    · exact hux.mul_right huy

end CFSG.LieType.AlgebraicGroups
