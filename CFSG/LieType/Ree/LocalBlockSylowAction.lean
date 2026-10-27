module

public import CFSG.LieType.Ree.ReducedWordBorelExtraction
public import CFSG.LieType.Chevalley.ParabolicDegreeIntersection
public import CFSG.LocalAnalysis.ComponentInitial.RootPairRestriction
public import CFSG.LieType.Chevalley.GraphFixedSylowOpposition

public noncomputable section

namespace CFSG.LieType.Ree

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial
open scoped Pointwise

namespace ReeTag

variable (t : ReeTag) (K : Type) [Field K] [Finite K] [CharP K t.prime] (a : ℕ)

@[expose] def reeFixedOrbitNegUnipotent
    (j : Fin t.fixedOrbitCount) : Subgroup (ModGL t.tag K) :=
  rootSpan t.tag K (Neg.neg '' t.fixedOrbitRoots j) ⊓ t.reeGamma K a

@[expose] def reeLocalBlock
    (j : Fin t.fixedOrbitCount) : Subgroup (ModGL t.tag K) :=
  t.reeFixedOrbitUnipotent K a j ⊔ t.reeFixedOrbitNegUnipotent K a j

@[expose] def reeLocalParabolic
    (j : Fin t.fixedOrbitCount) : Subgroup (ModGL t.tag K) :=
  t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j)

@[expose] def reeLocalCosets
    (j : Fin t.fixedOrbitCount) :
    Set (ModGL t.tag K ⧸ t.reeFixedBorel K a) :=
  (fun g : ModGL t.tag K => (g : ModGL t.tag K ⧸ t.reeFixedBorel K a)) ''
    (t.reeLocalParabolic K a j : Set (ModGL t.tag K))

@[expose] def reeLocalBlockStabilizer
    (j : Fin t.fixedOrbitCount) : Subgroup (ModGL t.tag K) :=
  t.reeLocalBlock K a j ⊓ MulAction.stabilizer (ModGL t.tag K)
    (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
      ModGL t.tag K ⧸ t.reeFixedBorel K a)

variable {t K a}

theorem mk_eq_one_iff
    {g : ModGL t.tag K} :
    (g : ModGL t.tag K ⧸ t.reeFixedBorel K a) = ((1 : ModGL t.tag K) : _) ↔
      g ∈ t.reeFixedBorel K a := by
  rw [QuotientGroup.eq, mul_one, inv_mem_iff]

theorem smul_mk
    (g h : ModGL t.tag K) :
    g • (h : ModGL t.tag K ⧸ t.reeFixedBorel K a) = ((g * h : ModGL t.tag K) : _) :=
  rfl

theorem mk_mul_of_mem
    {g b : ModGL t.tag K} (hb : b ∈ t.reeFixedBorel K a) :
    ((g * b : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) = (g : _) := by
  rw [QuotientGroup.eq, mul_inv_rev, inv_mul_cancel_right]
  exact inv_mem hb

theorem image_neg_fixedOrbitRoots
    (j : Fin t.fixedOrbitCount) :
    (fun α => t.fixedOrbitElement j • α) '' (Neg.neg '' t.fixedOrbitRoots j) =
      t.fixedOrbitRoots j := by
  ext β
  constructor
  · rintro ⟨_, ⟨α, hα, rfl⟩, rfl⟩
    show t.fixedOrbitElement j • -α ∈ t.fixedOrbitRoots j
    rw [smul_neg]
    exact neg_smul_mem_fixedOrbitRoots hα
  · intro hβ
    refine ⟨-(-(t.fixedOrbitElement j • β)), ⟨_, neg_smul_mem_fixedOrbitRoots hβ, rfl⟩, ?_⟩
    simp only [neg_neg, fixedOrbitElement_smul_smul]

theorem isRoot_of_mem_neg_fixedOrbitRoots
    {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ} (hα : α ∈ Neg.neg '' t.fixedOrbitRoots j) : IsRoot t.tag α := by
  obtain ⟨β, hβ, rfl⟩ := hα
  exact IsRoot.neg (mem_fixedOrbitRoots_iff.1 hβ).1

theorem map_conj_reeFixedOrbitUnipotent
    (j : Fin t.fixedOrbitCount) :
    (t.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))).toMonoidHom =
      t.reeFixedOrbitNegUnipotent K a j := by
  have hn : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j)).2
  rw [reeFixedOrbitUnipotent, reeFixedOrbitNegUnipotent,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport t.tag K).1 _ _ fun α hα => (mem_fixedOrbitRoots_iff.1 hα).1,
    image_fixedOrbitRoots, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]

theorem map_conj_reeFixedOrbitNegUnipotent
    (j : Fin t.fixedOrbitCount) :
    (t.reeFixedOrbitNegUnipotent K a j).map
        (MulAut.conj (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))).toMonoidHom =
      t.reeFixedOrbitUnipotent K a j := by
  have hn : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeGamma K a :=
    (canonicalRep_mem_reeFixedMonomial t K a (fixedOrbitElement_mem j)).2
  rw [reeFixedOrbitUnipotent, reeFixedOrbitNegUnipotent,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj _).injective,
    (canonical_weyl_root_transport t.tag K).1 _ _ fun α hα => isRoot_of_mem_neg_fixedOrbitRoots hα,
    image_neg_fixedOrbitRoots, map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer hn)]

theorem conj_mem_reeFixedOrbitNegUnipotent
    {j : Fin t.fixedOrbitCount} {x : ModGL t.tag K}
    (hx : x ∈ t.reeFixedOrbitUnipotent K a j) :
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * x *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
        t.reeFixedOrbitNegUnipotent K a j := by
  rw [← map_conj_reeFixedOrbitUnipotent]
  exact ⟨x, hx, rfl⟩

theorem inv_conj_mem_reeFixedOrbitNegUnipotent
    {j : Fin t.fixedOrbitCount} {x : ModGL t.tag K}
    (hx : x ∈ t.reeFixedOrbitUnipotent K a j) :
    (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ * x *
      canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
        t.reeFixedOrbitNegUnipotent K a j := by
  rw [← map_conj_reeFixedOrbitNegUnipotent] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  rw [show (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ *
      (MulAut.conj (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))).toMonoidHom y *
        canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) = y by
    change _ * (_ * y * _) * _ = y
    group]
  exact hy

theorem reeFixedOrbitNegUnipotent_le_reeFixedNegUnipotent
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedOrbitNegUnipotent K a j ≤ t.reeFixedNegUnipotent K a :=
  inf_le_inf_right _ (rootSpan_le_negUnipotent fun α hα => ⟨isRoot_of_mem_neg_fixedOrbitRoots hα,
    by
      obtain ⟨β, hβ, rfl⟩ := hα
      rw [height_neg]
      have := (mem_fixedOrbitRoots_iff.1 hβ).2.1
      omega⟩)

theorem eq_one_of_mem_reeFixedOrbitNegUnipotent_of_mem
    {j : Fin t.fixedOrbitCount}
    {y : ModGL t.tag K} (hy : y ∈ t.reeFixedOrbitNegUnipotent K a j)
    (hyB : y ∈ t.reeFixedBorel K a) : y = 1 := by
  have h : y ∈ t.reeFixedBorel K a ⊓ t.reeFixedNegUnipotent K a :=
    Subgroup.mem_inf.2 ⟨hyB, reeFixedOrbitNegUnipotent_le_reeFixedNegUnipotent j hy⟩
  rwa [reeFixedBorel_inf_reeFixedNegUnipotent, Subgroup.mem_bot] at h

theorem reeFixedOrbitUnipotent_le_reeFixedBorel
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedOrbitUnipotent K a j ≤ t.reeFixedBorel K a :=
  (reeFixedOrbitUnipotent_le_reeFixedPosUnipotent j).trans reeFixedPosUnipotent_le_reeFixedBorel

theorem reeLocalBlock_le
    (j : Fin t.fixedOrbitCount) :
    t.reeLocalBlock K a j ≤ t.reeLocalParabolic K a j := by
  have hnP := canonicalRep_fixedOrbitElement_mem_reeGamma_inf (K := K) (a := a) j
  have hXP : t.reeFixedOrbitUnipotent K a j ≤ t.reeLocalParabolic K a j :=
    (reeFixedOrbitUnipotent_le_reeFixedBorel j).trans
      (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j)
  refine sup_le hXP ?_
  rw [← map_conj_reeFixedOrbitUnipotent]
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hnP (hXP hx)) (inv_mem hnP)

theorem exists_canonicalRep_inv_eq
    (j : Fin t.fixedOrbitCount) :
    ∃ h ∈ t.reeFixedTorus K a,
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ =
        canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * h := by
  obtain ⟨h, hh, e⟩ := exists_canonicalRep_inv_mul_eq (K := K) (a := a)
    (fixedOrbitElement_mem j) (one_mem t.relWeylRee)
  rw [canonicalRep_one, mul_one, mul_one, fixedOrbitElement_inv] at e
  exact ⟨h, hh, e⟩

theorem inversionSet_fixedOrbitElement_subset
    (j : Fin t.fixedOrbitCount) :
    inversionSet (t.fixedOrbitElement j) ⊆ t.fixedOrbitRoots j := by
  rintro α ⟨hr, hp, -, hneg⟩
  by_contra hα
  have hS : α ∈ t.fixedOrbitComplementRoots j := by
    rw [fixedOrbitComplementRoots_eq]
    exact ⟨⟨hr, hp⟩, hα⟩
  have := (mem_fixedOrbitComplementRoots_iff.1 (smul_mem_fixedOrbitComplementRoots hS)).2.1
  omega

theorem exists_eq_mul_canonicalRep_mul
    {j : Fin t.fixedOrbitCount} {g : ModGL t.tag K}
    (hg : g ∈ t.reeLocalParabolic K a j) (hgB : g ∉ t.reeFixedBorel K a) :
    ∃ x ∈ t.reeFixedOrbitUnipotent K a j, ∃ b ∈ t.reeFixedBorel K a,
      g = x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * b := by
  have hg' : g⁻¹ ∈ ((t.reeLocalParabolic K a j : Subgroup (ModGL t.tag K)) :
      Set (ModGL t.tag K)) := inv_mem hg
  change g⁻¹ ∈ ((t.reeGamma K a ⊓ parabolicSubgroup t.tag K (t.fixedOrbitSet j) :
    Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) at hg'
  rw [coe_reeGamma_inf_parabolicSubgroup] at hg'
  rcases hg' with hB | hD
  · exact absurd (inv_mem_iff.1 hB) hgB
  · obtain ⟨-, b, hb, u, hu, hbu⟩ := exists_reeFixed_bruhat_factor
      (reeFixedBruhatCell_subset (fixedOrbitElement_mem j) hD)
      (reeFixedBruhatCell_subset_bruhatCell _ hD)
    have huX : u ∈ t.reeFixedOrbitUnipotent K a j :=
      Subgroup.mem_inf.2 ⟨rootSpan_mono (inversionSet_fixedOrbitElement_subset j)
        (Subgroup.mem_inf.1 hu).1, (Subgroup.mem_inf.1 hu).2⟩
    obtain ⟨h, hh, hinv⟩ := exists_canonicalRep_inv_eq (K := K) (a := a) j
    refine ⟨u⁻¹, inv_mem huX, h * b⁻¹, mul_mem (reeFixedTorus_le_reeFixedBorel hh) (inv_mem hb),
      ?_⟩
    rw [← mul_assoc, mul_assoc u⁻¹, ← hinv, ← inv_inv g, ← hbu]
    group

theorem mk_mul_canonicalRep_inj
    {j : Fin t.fixedOrbitCount} {x x' : ModGL t.tag K}
    (hx : x ∈ t.reeFixedOrbitUnipotent K a j) (hx' : x' ∈ t.reeFixedOrbitUnipotent K a j)
    (h : ((x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
      ModGL t.tag K ⧸ t.reeFixedBorel K a) =
        ((x' * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
          _)) : x = x' := by
  rw [QuotientGroup.eq] at h
  have hY := inv_conj_mem_reeFixedOrbitNegUnipotent (K := K) (a := a) (j := j)
    (mul_mem (inv_mem hx) hx')
  have e : (x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ *
      (x' * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) =
        (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ * (x⁻¹ * x') *
          canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) := by group
  rw [e] at h
  have h1 := eq_one_of_mem_reeFixedOrbitNegUnipotent_of_mem hY h
  have h2 : x⁻¹ * x' = 1 := by
    have := congrArg (fun g => canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * g *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹) h1
    simpa [mul_assoc] using this
  rw [inv_mul_eq_one] at h2
  exact h2

theorem mk_mul_canonicalRep_ne_one
    {j : Fin t.fixedOrbitCount} {x : ModGL t.tag K}
    (hx : x ∈ t.reeFixedOrbitUnipotent K a j) :
    ((x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
      ModGL t.tag K ⧸ t.reeFixedBorel K a) ≠ ((1 : ModGL t.tag K) : _) := by
  rw [Ne, mk_eq_one_iff]
  intro h
  have hn : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈ t.reeFixedBorel K a := by
    have := mul_mem (inv_mem (reeFixedOrbitUnipotent_le_reeFixedBorel j hx)) h
    rwa [inv_mul_cancel_left] at this
  have hD : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) ∈
      t.reeFixedBruhatCell K a (t.fixedOrbitElement j) :=
    mem_reeFixedBruhatCell.2 ⟨1, one_mem _, 1, one_mem _, by rw [one_mul, mul_one]⟩
  exact Set.disjoint_left.1 (disjoint_reeFixedBorel_reeFixedBruhatCell j) hn hD

theorem reeLocalCosets_eq
    (j : Fin t.fixedOrbitCount) :
    t.reeLocalCosets K a j = insert ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a)
      ((fun x : ModGL t.tag K =>
        ((x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
          ModGL t.tag K ⧸ t.reeFixedBorel K a)) ''
        (t.reeFixedOrbitUnipotent K a j : Set (ModGL t.tag K))) := by
  have hnP := canonicalRep_fixedOrbitElement_mem_reeGamma_inf (K := K) (a := a) j
  have hXP : t.reeFixedOrbitUnipotent K a j ≤ t.reeLocalParabolic K a j :=
    (reeFixedOrbitUnipotent_le_reeFixedBorel j).trans
      (reeFixedBorel_le_reeGamma_inf_parabolicSubgroup j)
  ext ω
  constructor
  · rintro ⟨g, hg, rfl⟩
    by_cases hgB : g ∈ t.reeFixedBorel K a
    · exact Or.inl (mk_eq_one_iff.2 hgB)
    · obtain ⟨x, hx, b, hb, rfl⟩ := exists_eq_mul_canonicalRep_mul hg hgB
      exact Or.inr ⟨x, hx, (mk_mul_of_mem hb).symm⟩
  · rintro (rfl | ⟨x, hx, rfl⟩)
    · exact ⟨1, one_mem _, rfl⟩
    · exact ⟨_, mul_mem (hXP hx) hnP, rfl⟩

theorem one_mem_reeLocalCosets
    (j : Fin t.fixedOrbitCount) :
    ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) ∈ t.reeLocalCosets K a j :=
  ⟨1, one_mem _, rfl⟩

theorem one_lt_card_reeFixedOrbitUnipotent
    (j : Fin t.fixedOrbitCount) :
    1 < Nat.card (t.reeFixedOrbitUnipotent K a j) := by
  have := finite_modGL (τ := t.tag) (K := K)
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  refine (Subgroup.one_lt_card_iff_ne_bot _).2 fun h => hu1 ?_
  rw [h] at hu
  exact (Subgroup.mem_bot).1 hu

theorem ncard_reeLocalCosets
    (j : Fin t.fixedOrbitCount) :
    (t.reeLocalCosets K a j).ncard = Nat.card (t.reeFixedOrbitUnipotent K a j) + 1 := by
  have := finite_modGL (τ := t.tag) (K := K)
  have hinj : Set.InjOn (fun x : ModGL t.tag K =>
      ((x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
        ModGL t.tag K ⧸ t.reeFixedBorel K a))
      (t.reeFixedOrbitUnipotent K a j : Set (ModGL t.tag K)) :=
    fun x hx x' hx' h => mk_mul_canonicalRep_inj hx hx' h
  have hnot : ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) ∉
      (fun x : ModGL t.tag K =>
        ((x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
          ModGL t.tag K ⧸ t.reeFixedBorel K a)) ''
        (t.reeFixedOrbitUnipotent K a j : Set (ModGL t.tag K)) := by
    rintro ⟨x, hx, h⟩
    exact mk_mul_canonicalRep_ne_one hx h
  rw [reeLocalCosets_eq, Set.ncard_insert_of_notMem hnot (Set.toFinite _), hinj.ncard_image,
    ← Nat.card_coe_set_eq]
  rfl

theorem exists_mem_reeLocalBlock_mk_eq
    (j : Fin t.fixedOrbitCount) :
    ∃ m ∈ t.reeLocalBlock K a j, (m : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _) := by
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  have hyY := conj_mem_reeFixedOrbitNegUnipotent (K := K) (a := a) hu
  have hyM : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∈
        t.reeLocalBlock K a j := Subgroup.mem_sup_right hyY
  have hyB : canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ ∉ t.reeFixedBorel K a := by
    intro h
    have h1 := eq_one_of_mem_reeFixedOrbitNegUnipotent_of_mem hyY h
    rw [mul_inv_eq_one, mul_eq_left] at h1
    exact hu1 h1
  obtain ⟨x, hx, b, hb, hxe⟩ := exists_eq_mul_canonicalRep_mul (reeLocalBlock_le j hyM) hyB
  refine ⟨x⁻¹ * (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * u *
    (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹),
    mul_mem (Subgroup.mem_sup_left (inv_mem hx)) hyM, ?_⟩
  rw [hxe, show x⁻¹ * (x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * b) =
    canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * b by group, mk_mul_of_mem hb]

theorem exists_mem_reeLocalBlock_smul_one_eq
    {j : Fin t.fixedOrbitCount}
    {ω : ModGL t.tag K ⧸ t.reeFixedBorel K a} (hω : ω ∈ t.reeLocalCosets K a j) :
    ∃ m ∈ t.reeLocalBlock K a j, m • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ _) = ω := by
  rw [reeLocalCosets_eq] at hω
  rcases hω with rfl | ⟨x, hx, rfl⟩
  · exact ⟨1, one_mem _, one_smul _ _⟩
  · obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
    refine ⟨x * m, mul_mem (Subgroup.mem_sup_left hx) hm, ?_⟩
    rw [smul_mk, mul_one]
    rw [QuotientGroup.eq] at hmn ⊢
    rwa [show (x * m)⁻¹ * (x * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) =
      m⁻¹ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) by group]

theorem smul_mem_reeLocalCosets
    {j : Fin t.fixedOrbitCount} {m : ModGL t.tag K}
    (hm : m ∈ t.reeLocalBlock K a j) {ω : ModGL t.tag K ⧸ t.reeFixedBorel K a}
    (hω : ω ∈ t.reeLocalCosets K a j) : m • ω ∈ t.reeLocalCosets K a j := by
  obtain ⟨g, hg, rfl⟩ := hω
  exact ⟨m * g, mul_mem (reeLocalBlock_le j hm) hg, rfl⟩

theorem existsUnique_smul_eq
    {j : Fin t.fixedOrbitCount}
    {ω ω' : ModGL t.tag K ⧸ t.reeFixedBorel K a} (hω : ω ∈ t.reeLocalCosets K a j)
    (hωξ : ω ≠ ((1 : ModGL t.tag K) : _)) (hω' : ω' ∈ t.reeLocalCosets K a j)
    (hω'ξ : ω' ≠ ((1 : ModGL t.tag K) : _)) :
    ∃! x : t.reeFixedOrbitUnipotent K a j, (x : ModGL t.tag K) • ω = ω' := by
  rw [reeLocalCosets_eq] at hω hω'
  rcases hω with rfl | ⟨x₁, hx₁, rfl⟩
  · exact absurd rfl hωξ
  rcases hω' with rfl | ⟨x₂, hx₂, rfl⟩
  · exact absurd rfl hω'ξ
  refine ⟨⟨x₂ * x₁⁻¹, mul_mem hx₂ (inv_mem hx₁)⟩, ?_, ?_⟩
  · change (x₂ * x₁⁻¹) • ((x₁ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
      ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) = ((x₂ *
        canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
          ModGL t.tag K ⧸ t.reeFixedBorel K a)
    rw [smul_mk]
    congr 1
    group
  · rintro ⟨x, hx⟩ hxe
    apply Subtype.ext
    change x • ((x₁ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
      ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) = ((x₂ *
        canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
          ModGL t.tag K ⧸ t.reeFixedBorel K a) at hxe
    rw [smul_mk, ← mul_assoc] at hxe
    have h := mk_mul_canonicalRep_inj (mul_mem hx hx₁) hx₂ hxe
    change x = x₂ * x₁⁻¹
    rw [← h]
    group

theorem smul_one_eq_one_iff
    {g : ModGL t.tag K} :
    g • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) = ((1 : ModGL t.tag K) : _) ↔
      g ∈ t.reeFixedBorel K a := by
  rw [smul_mk, mul_one, mk_eq_one_iff]

theorem reeLocalBlock_le_rootLevi
    (j : Fin t.fixedOrbitCount) :
    t.reeLocalBlock K a j ≤ rootLevi t.tag K (t.fixedOrbitSet j) := by
  refine sup_le (inf_le_left.trans (rootSpan_mono fun _ hα => hα.1))
    (inf_le_left.trans (rootSpan_mono ?_))
  rintro _ ⟨β, hβ, rfl⟩
  exact ⟨IsRoot.neg hβ.1.1, fun i hi => by rw [Pi.neg_apply, hβ.1.2 i hi, neg_zero]⟩

theorem dualRoot_fixedOrbitRootList_check (t : ReeTag) :
    ∀ j : Fin t.fixedOrbitCount, ∀ α ∈ t.fixedOrbitRootList j,
      t.dualRoot α ∈ t.fixedOrbitRootList j := by
  cases t <;> decide +kernel

theorem dualRoot_mem_fixedOrbitRoots {j : Fin t.fixedOrbitCount}
    {α : Fin t.tag.rank → ℤ}
    (hα : α ∈ t.fixedOrbitRoots j) : t.dualRoot α ∈ t.fixedOrbitRoots j := by
  rw [fixedOrbitRoots_eq_list] at hα ⊢
  exact dualRoot_fixedOrbitRootList_check t j α hα

theorem reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedTorus K a ≤
      Subgroup.normalizer (t.reeFixedOrbitUnipotent K a j : Set (ModGL t.tag K)) := fun _ hh =>
  Subgroup.inf_normalizer_le_normalizer_inf (Subgroup.mem_inf.2
    ⟨torusGroup_le_normalizer_rootSpan (fun _ hα => (mem_fixedOrbitRoots_iff.1 hα).1)
      (Subgroup.mem_inf.1 hh).1, Subgroup.le_normalizer (Subgroup.mem_inf.1 hh).2⟩)

theorem exists_mul_of_mem_reeLocalBlock_inf
    {j : Fin t.fixedOrbitCount} {g : ModGL t.tag K}
    (hg : g ∈ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a) :
    ∃ h ∈ t.reeFixedTorus K a, ∃ x ∈ t.reeFixedOrbitUnipotent K a j, g = h * x := by
  obtain ⟨hgM, hgB⟩ := Subgroup.mem_inf.1 hg
  obtain ⟨hgB', hgΓ⟩ := Subgroup.mem_inf.1 hgB
  have hgL : g ∈ rootLevi t.tag K (t.fixedOrbitSet j) ⊓ borelGroup t.tag K :=
    Subgroup.mem_inf.2 ⟨reeLocalBlock_le_rootLevi j hgM, hgB'⟩
  obtain ⟨h, hh, v, hv, rfl⟩ :=
    (large_Ree_parabolic_degree_intersection t.tag K (t.fixedOrbitSet j)).2.1 g hgL
  have hv' : v ∈ rootSpan t.tag K (t.fixedOrbitRoots j) := hv
  have hvU : v ∈ posUnipotent t.tag K := rootSpan_le_posUnipotent (fixedOrbitRoots_subset j) hv'
  have hha := torusGroup_le_adjointGroup t K hh
  have hva := rootSpan_le_adjointGroup _ hv'
  have hF := finiteReeAut_eq_of_mem_reeGamma hgΓ (mul_mem hha hva)
  have e : (⟨h * v, mul_mem hha hva⟩ : adjointGroup t.tag K) = ⟨h, hha⟩ * ⟨v, hva⟩ := rfl
  rw [e, map_mul, Subgroup.coe_mul] at hF
  have hFh := finiteReeAut_mem_torusGroup (a := a) hh hha
  have hFv := finiteReeAut_mem_of_map_le (a := a) (map_finiteReeAut_rootSpan_le fun α hα =>
    ⟨(mem_fixedOrbitRoots_iff.1 hα).1, dualRoot_mem_fixedOrbitRoots hα⟩) hv' hva
  obtain ⟨h1, h2⟩ := (triangular_borel_structure.{0, 0} t.tag K).2.2.2.2.2.2.1 _ hFh _ hh _
    (rootSpan_le_posUnipotent (fixedOrbitRoots_subset j) hFv) _ hvU hF
  exact ⟨h, Subgroup.mem_inf.2 ⟨hh, mem_reeGamma_of_fixed hha h1⟩, v,
    Subgroup.mem_inf.2 ⟨hv', mem_reeGamma_of_fixed hva h2⟩, rfl⟩

theorem conj_mem_of_mem_reeLocalBlock_inf
    {j : Fin t.fixedOrbitCount} {g : ModGL t.tag K}
    (hg : g ∈ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a) {x : ModGL t.tag K}
    (hx : x ∈ t.reeFixedOrbitUnipotent K a j) : g * x * g⁻¹ ∈ t.reeFixedOrbitUnipotent K a j := by
  obtain ⟨h, hh, v, hv, rfl⟩ := exists_mul_of_mem_reeLocalBlock_inf hg
  have hN := reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent j hh
  rw [show h * v * x * (h * v)⁻¹ = h * (v * x * v⁻¹) * h⁻¹ by group]
  exact (Subgroup.mem_normalizer_iff.1 hN _).1 (mul_mem (mul_mem hv hx) (inv_mem hv))

theorem reeFixedOrbitUnipotent_subgroupOf_inf_normal
    (j : Fin t.fixedOrbitCount) :
    ((t.reeFixedOrbitUnipotent K a j).subgroupOf
      (t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a)).Normal :=
  ⟨fun _ hx g => Subgroup.mem_subgroupOf.2
    (conj_mem_of_mem_reeLocalBlock_inf g.2 (Subgroup.mem_subgroupOf.1 hx))⟩

theorem mem_reeFixedBorel_of_mem_normalizer
    {j : Fin t.fixedOrbitCount} {g : ModGL t.tag K}
    (hgM : g ∈ t.reeLocalBlock K a j)
    (hgN : g ∈ Subgroup.normalizer (t.reeFixedOrbitUnipotent K a j : Set (ModGL t.tag K))) :
    g ∈ t.reeFixedBorel K a := by
  by_contra hgB
  obtain ⟨x₁, hx₁, b, hb, rfl⟩ := exists_eq_mul_canonicalRep_mul (reeLocalBlock_le j hgM) hgB
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_mem_reeFixedOrbitUnipotent (K := K) (a := a) j
  set g := x₁ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * b with hgdef
  have h1 : g⁻¹ * u * g ∈ t.reeFixedOrbitUnipotent K a j :=
    (Subgroup.mem_normalizer_iff''.1 hgN u).1 hu
  have h2 : ((u * (x₁ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j)) :
      ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
        ((x₁ * canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : ModGL t.tag K) :
          _) := by
    have e1 : ((u * g : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) = (g : _) := by
      rw [show u * g = g * (g⁻¹ * u * g) by group]
      exact mk_mul_of_mem (reeFixedOrbitUnipotent_le_reeFixedBorel j h1)
    rw [hgdef, ← mul_assoc, mk_mul_of_mem hb, mk_mul_of_mem hb] at e1
    exact e1
  rw [← mul_assoc] at h2
  have h3 := mk_mul_canonicalRep_inj (mul_mem hu hx₁) hx₁ h2
  exact hu1 (mul_eq_right.1 h3)

theorem reeFixedOrbitUnipotent_le_reeLocalBlock
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedOrbitUnipotent K a j ≤ t.reeLocalBlock K a j :=
  le_sup_left

theorem reeFixedOrbitNegUnipotent_le_reeLocalBlock
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedOrbitNegUnipotent K a j ≤ t.reeLocalBlock K a j :=
  le_sup_right

theorem isPGroup_reeFixedOrbitUnipotent
    (j : Fin t.fixedOrbitCount) :
    IsPGroup t.prime (t.reeFixedOrbitUnipotent K a j) :=
  (isPGroup_posUnipotent t.prime t.tag).to_le
    (inf_le_left.trans (rootSpan_le_posUnipotent (fixedOrbitRoots_subset j)))

theorem pow_card_sub_one_mem_reeFixedOrbitUnipotent
    {j : Fin t.fixedOrbitCount}
    {g : ModGL t.tag K} (hg : g ∈ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a) :
    g ^ (Nat.card K - 1) ∈ t.reeFixedOrbitUnipotent K a j := by
  obtain ⟨h, hh, v, hv, rfl⟩ := exists_mul_of_mem_reeLocalBlock_inf hg
  have hN := reeFixedTorus_le_normalizer_reeFixedOrbitUnipotent j hh
  have hv' : h * v * h⁻¹ ∈ t.reeFixedOrbitUnipotent K a j :=
    (Subgroup.mem_normalizer_iff.1 hN v).1 hv
  obtain ⟨u', hu', e⟩ := exists_mul_pow_eq_mul_pow hv' hN (Nat.card K - 1)
  rw [show h * v = h * v * h⁻¹ * h by group, e,
    pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup
      (Subgroup.mem_inf.1 hh).1), mul_one]
  exact hu'

theorem not_dvd_index_reeFixedOrbitUnipotent
    [Fact t.prime.Prime] (j : Fin t.fixedOrbitCount) :
    ¬ t.prime ∣ ((t.reeFixedOrbitUnipotent K a j).subgroupOf (t.reeLocalBlock K a j)).index := by
  have := finite_modGL (τ := t.tag) (K := K)
  have hXM := reeFixedOrbitUnipotent_le_reeLocalBlock (K := K) (a := a) j
  refine not_dvd_index_of_forall_pow_mem
    ((isPGroup_reeFixedOrbitUnipotent j).of_equiv (Subgroup.subgroupOfEquivOfLe hXM).symm)
    (not_dvd_natCard_sub_one (K := K) t.prime) fun x hx => ?_
  rw [Subgroup.mem_subgroupOf]
  have hxB := mem_reeFixedBorel_of_mem_normalizer x.2
    (mem_normalizer_of_mem_normalizer_subgroupOf hXM hx)
  exact pow_card_sub_one_mem_reeFixedOrbitUnipotent (Subgroup.mem_inf.2 ⟨x.2, hxB⟩)

theorem le_of_isPGroup_of_le_normalizer {G : Type*} [Group G] [Finite G] {p : ℕ}
    {M S W : Subgroup G} (hS : IsPGroup p S) (hW : IsPGroup p W) (hSM : S ≤ M) (hWM : W ≤ M)
    (hSW : S ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ Q : Subgroup G, Q ≤ M → IsPGroup p Q → Nat.card Q ≤ Nat.card W) : S ≤ W := by
  have hQ := hS.to_sup_of_normal_right' hW hSW
  have heq := Subgroup.eq_of_le_of_card_ge (le_sup_right : W ≤ S ⊔ W)
    (hmax _ (sup_le hSM hWM) hQ)
  rw [heq]
  exact le_sup_left

theorem card_le_card_reeFixedOrbitUnipotent
    [Fact t.prime.Prime] (j : Fin t.fixedOrbitCount)
    {Q : Subgroup (ModGL t.tag K)} (hQM : Q ≤ t.reeLocalBlock K a j) (hQ : IsPGroup t.prime Q) :
    Nat.card Q ≤ Nat.card (t.reeFixedOrbitUnipotent K a j) := by
  have := finite_modGL (τ := t.tag) (K := K)
  have hXM := reeFixedOrbitUnipotent_le_reeLocalBlock (K := K) (a := a) j
  set PX := ((isPGroup_reeFixedOrbitUnipotent j).of_equiv
    (Subgroup.subgroupOfEquivOfLe hXM).symm).toSylow (not_dvd_index_reeFixedOrbitUnipotent j)
  have hPX : (PX : Subgroup (t.reeLocalBlock K a j)) =
      (t.reeFixedOrbitUnipotent K a j).subgroupOf (t.reeLocalBlock K a j) :=
    IsPGroup.toSylow_coe _ _
  obtain ⟨P, hP⟩ := (hQ.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm).exists_le_sylow
  calc Nat.card Q = Nat.card (Q.subgroupOf (t.reeLocalBlock K a j)) :=
        (card_subgroupOf_of_le hQM).symm
    _ ≤ Nat.card P := Subgroup.card_le_of_le hP
    _ = Nat.card PX := by rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    _ = Nat.card (t.reeFixedOrbitUnipotent K a j) := by rw [hPX, card_subgroupOf_of_le hXM]

theorem mem_normalizer_map_conj
    {j : Fin t.fixedOrbitCount} {w : ModGL t.tag K}
    (hwM : w ∈ t.reeLocalBlock K a j)
    (hw : (w : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _))
    {g : ModGL t.tag K} (hgM : g ∈ t.reeLocalBlock K a j)
    (hg : g • (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
      ModGL t.tag K ⧸ t.reeFixedBorel K a) =
        (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _)) :
    g ∈ Subgroup.normalizer (((t.reeFixedOrbitUnipotent K a j).map
      (MulAut.conj w).toMonoidHom : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) := by
  have hwξ : w • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _) := by
    rw [smul_mk, mul_one, hw]
  have hg' : w⁻¹ * g * w ∈ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hwM) hgM) hwM, ?_⟩
    rw [← smul_one_eq_one_iff, mul_smul, mul_smul, hwξ, hg, ← hwξ, inv_smul_smul]
  have hg'' : (w⁻¹ * g * w)⁻¹ ∈ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a := inv_mem hg'
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨(w⁻¹ * g * w) * x * (w⁻¹ * g * w)⁻¹, conj_mem_of_mem_reeLocalBlock_inf hg' hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨x, hx, hxe⟩
    refine ⟨(w⁻¹ * g * w)⁻¹ * x * (w⁻¹ * g * w)⁻¹⁻¹,
      conj_mem_of_mem_reeLocalBlock_inf hg'' hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hxe ⊢
    rw [show z = g⁻¹ * (w * x * w⁻¹) * g by rw [hxe]; group]
    group

theorem smul_mk_canonicalRep_of_mem
    {j : Fin t.fixedOrbitCount} {y : ModGL t.tag K}
    (hy : y ∈ t.reeFixedOrbitNegUnipotent K a j) :
    y • (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
      ModGL t.tag K ⧸ t.reeFixedBorel K a) =
        (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _) := by
  rw [← map_conj_reeFixedOrbitUnipotent] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [smul_mk]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [show canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * x *
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j))⁻¹ *
        canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) =
      canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) * x by group,
    mk_mul_of_mem (reeFixedOrbitUnipotent_le_reeFixedBorel j hx)]

theorem isPGroup_reeFixedOrbitNegUnipotent
    (j : Fin t.fixedOrbitCount) :
    IsPGroup t.prime (t.reeFixedOrbitNegUnipotent K a j) := by
  rw [← map_conj_reeFixedOrbitUnipotent]
  exact (isPGroup_reeFixedOrbitUnipotent j).map _

theorem reeFixedOrbitNegUnipotent_eq_map_conj
    [Fact t.prime.Prime] {j : Fin t.fixedOrbitCount}
    {w : ModGL t.tag K} (hwM : w ∈ t.reeLocalBlock K a j)
    (hw : (w : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
      (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _)) :
    t.reeFixedOrbitNegUnipotent K a j =
        (t.reeFixedOrbitUnipotent K a j).map (MulAut.conj w).toMonoidHom ∧
      ∀ S : Subgroup (ModGL t.tag K), S ≤ t.reeLocalBlock K a j →
        (∀ s ∈ S, s • (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
          ModGL t.tag K ⧸ t.reeFixedBorel K a) =
            (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _)) →
        IsPGroup t.prime S → S ≤ t.reeFixedOrbitNegUnipotent K a j := by
  have := finite_modGL (τ := t.tag) (K := K)
  have hWM : (t.reeFixedOrbitUnipotent K a j).map (MulAut.conj w).toMonoidHom ≤
      t.reeLocalBlock K a j := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hwM (reeFixedOrbitUnipotent_le_reeLocalBlock j hx)) (inv_mem hwM)
  have hWp : IsPGroup t.prime ((t.reeFixedOrbitUnipotent K a j).map
      (MulAut.conj w).toMonoidHom) := (isPGroup_reeFixedOrbitUnipotent j).map _
  have hWc : Nat.card ((t.reeFixedOrbitUnipotent K a j).map (MulAut.conj w).toMonoidHom) =
      Nat.card (t.reeFixedOrbitUnipotent K a j) :=
    Subgroup.card_map_of_injective (MulAut.conj w).injective
  have hmax : ∀ Q : Subgroup (ModGL t.tag K), Q ≤ t.reeLocalBlock K a j →
      IsPGroup t.prime Q → Nat.card Q ≤ Nat.card ((t.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj w).toMonoidHom) := fun Q hQM hQ =>
    hWc ▸ card_le_card_reeFixedOrbitUnipotent j hQM hQ
  have hstab : ∀ S : Subgroup (ModGL t.tag K), S ≤ t.reeLocalBlock K a j →
      (∀ s ∈ S, s • (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) :
        ModGL t.tag K ⧸ t.reeFixedBorel K a) =
          (canonicalRep (coxeterSystem t.tag) K (t.fixedOrbitElement j) : _)) →
      S ≤ Subgroup.normalizer (((t.reeFixedOrbitUnipotent K a j).map
        (MulAut.conj w).toMonoidHom : Subgroup (ModGL t.tag K)) : Set (ModGL t.tag K)) :=
    fun S hSM hS s hs => mem_normalizer_map_conj hwM hw (hSM hs) (hS s hs)
  have hYM := reeFixedOrbitNegUnipotent_le_reeLocalBlock (K := K) (a := a) j
  have hYc : Nat.card (t.reeFixedOrbitNegUnipotent K a j) =
      Nat.card (t.reeFixedOrbitUnipotent K a j) := by
    rw [← map_conj_reeFixedOrbitUnipotent]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hYW := le_of_isPGroup_of_le_normalizer (isPGroup_reeFixedOrbitNegUnipotent j) hWp hYM hWM
    (hstab _ hYM fun y hy => smul_mk_canonicalRep_of_mem hy) hmax
  have hYeq := Subgroup.eq_of_le_of_card_ge hYW (by rw [hWc, hYc])
  refine ⟨hYeq, fun S hSM hS hSp => ?_⟩
  rw [hYeq]
  exact le_of_isPGroup_of_le_normalizer hSp hWp hSM hWM (hstab S hSM hS) hmax

theorem reeFixedOrbitNegUnipotent_le_reeLocalBlockStabilizer
    (j : Fin t.fixedOrbitCount) :
    t.reeFixedOrbitNegUnipotent K a j ≤ t.reeLocalBlockStabilizer K a j := fun _ hy =>
  Subgroup.mem_inf.2 ⟨reeFixedOrbitNegUnipotent_le_reeLocalBlock j hy,
    MulAction.mem_stabilizer_iff.2 (smul_mk_canonicalRep_of_mem hy)⟩

theorem coe_sylow_reeLocalBlockStabilizer
    [Fact t.prime.Prime] {j : Fin t.fixedOrbitCount}
    (S : Sylow t.prime (t.reeLocalBlockStabilizer K a j)) :
    (S : Subgroup (t.reeLocalBlockStabilizer K a j)) =
      (t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlockStabilizer K a j) := by
  have := finite_modGL (τ := t.tag) (K := K)
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
  obtain ⟨-, hYuniq⟩ := reeFixedOrbitNegUnipotent_eq_map_conj hm hmn
  have hYp : IsPGroup t.prime
      ((t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlockStabilizer K a j)) :=
    (isPGroup_reeFixedOrbitNegUnipotent j).of_equiv
      (Subgroup.subgroupOfEquivOfLe (reeFixedOrbitNegUnipotent_le_reeLocalBlockStabilizer j)).symm
  have hmapS : (S : Subgroup (t.reeLocalBlockStabilizer K a j)).map
      (t.reeLocalBlockStabilizer K a j).subtype ≤ t.reeFixedOrbitNegUnipotent K a j := by
    refine hYuniq _ ((Subgroup.map_subtype_le _).trans inf_le_left) (fun s hs => ?_) (S.2.map _)
    obtain ⟨y, -, rfl⟩ := hs
    exact MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 y.2).2
  refine (S.3 hYp fun s hs => ?_).symm
  rw [Subgroup.mem_subgroupOf]
  exact hmapS ⟨s, hs, rfl⟩

theorem injective_pairAutRestrict_reeLocalBlock
    [Fact t.prime.Prime] (j : Fin t.fixedOrbitCount) :
    Function.Injective (pairAutRestrict
      ((t.reeFixedOrbitUnipotent K a j).subgroupOf (t.reeLocalBlock K a j))
      ((t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlock K a j))) := by
  have := finite_modGL (τ := t.tag) (K := K)
  have hXM := reeFixedOrbitUnipotent_le_reeLocalBlock (K := K) (a := a) j
  have hYM := reeFixedOrbitNegUnipotent_le_reeLocalBlock (K := K) (a := a) j
  set PX := ((isPGroup_reeFixedOrbitUnipotent j).of_equiv
    (Subgroup.subgroupOfEquivOfLe hXM).symm).toSylow (not_dvd_index_reeFixedOrbitUnipotent j)
  have hPX : (PX : Subgroup (t.reeLocalBlock K a j)) =
      (t.reeFixedOrbitUnipotent K a j).subgroupOf (t.reeLocalBlock K a j) :=
    IsPGroup.toSylow_coe _ _
  set ξ : ModGL t.tag K ⧸ t.reeFixedBorel K a :=
    ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) with hξ
  have hΩo : (MulAction.orbit (t.reeLocalBlock K a j) ξ : Set (ModGL t.tag K ⧸ _)) =
      t.reeLocalCosets K a j := by
    ext ω
    constructor
    · rintro ⟨m, rfl⟩
      exact smul_mem_reeLocalCosets m.2 (one_mem_reeLocalCosets j)
    · intro hω
      obtain ⟨m, hm, rfl⟩ := exists_mem_reeLocalBlock_smul_one_eq hω
      exact ⟨⟨m, hm⟩, rfl⟩
  set ξo : MulAction.orbit (t.reeLocalBlock K a j) ξ := ⟨ξ, MulAction.mem_orbit_self ξ⟩
  have hΩ : 3 ≤ Nat.card (MulAction.orbit (t.reeLocalBlock K a j) ξ) := by
    rw [Nat.card_coe_set_eq, hΩo, ncard_reeLocalCosets]
    have := one_lt_card_reeFixedOrbitUnipotent (K := K) (a := a) j
    omega
  have hmemU : ∀ x : t.reeLocalBlock K a j, x ∈ (PX : Subgroup (t.reeLocalBlock K a j)) ↔
      (x : ModGL t.tag K) ∈ t.reeFixedOrbitUnipotent K a j := fun x => by
    rw [hPX, Subgroup.mem_subgroupOf]
  have hUξ : (PX : Subgroup (t.reeLocalBlock K a j)) ≤
      MulAction.stabilizer (t.reeLocalBlock K a j) ξo := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    refine Subtype.ext ?_
    change (x : ModGL t.tag K) • ξ = ξ
    exact smul_one_eq_one_iff.2 (reeFixedOrbitUnipotent_le_reeFixedBorel j ((hmemU x).1 hx))
  have hstab : ∀ g : t.reeLocalBlock K a j, g ∈ MulAction.stabilizer (t.reeLocalBlock K a j) ξo →
      (g : ModGL t.tag K) ∈ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a := fun g hg => by
    rw [MulAction.mem_stabilizer_iff] at hg
    have hg' : (g : ModGL t.tag K) • ξ = ξ := congrArg Subtype.val hg
    exact Subgroup.mem_inf.2 ⟨g.2, smul_one_eq_one_iff.1 hg'⟩
  have hUn : ((PX : Subgroup (t.reeLocalBlock K a j)).subgroupOf
      (MulAction.stabilizer (t.reeLocalBlock K a j) ξo)).Normal := by
    refine ⟨fun u hu g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    rw [hmemU] at hu ⊢
    exact conj_mem_of_mem_reeLocalBlock_inf (hstab g g.2) hu
  have hreg : ∀ ω ω' : MulAction.orbit (t.reeLocalBlock K a j) ξ, ω ≠ ξo → ω' ≠ ξo →
      ∃! u : (PX : Subgroup (t.reeLocalBlock K a j)), (u : t.reeLocalBlock K a j) • ω = ω' := by
    intro ω ω' hω hω'
    have h1 : (ω : ModGL t.tag K ⧸ t.reeFixedBorel K a) ∈ t.reeLocalCosets K a j :=
      hΩo ▸ ω.2
    have h2 : (ω' : ModGL t.tag K ⧸ t.reeFixedBorel K a) ∈ t.reeLocalCosets K a j :=
      hΩo ▸ ω'.2
    have hne : (ω : ModGL t.tag K ⧸ t.reeFixedBorel K a) ≠ ξ := fun h => hω (Subtype.ext h)
    have hne' : (ω' : ModGL t.tag K ⧸ t.reeFixedBorel K a) ≠ ξ := fun h => hω' (Subtype.ext h)
    obtain ⟨x, hx, huniq⟩ := existsUnique_smul_eq h1 hne h2 hne'
    have hxU : (⟨x, hXM x.2⟩ : t.reeLocalBlock K a j) ∈ (PX : Subgroup _) := (hmemU _).2 x.2
    refine ⟨⟨⟨x, hXM x.2⟩, hxU⟩, Subtype.ext hx, ?_⟩
    rintro ⟨⟨y, hyM⟩, hyU⟩ hy
    have hyX : y ∈ t.reeFixedOrbitUnipotent K a j := (hmemU ⟨y, hyM⟩).1 hyU
    have h := huniq ⟨y, hyX⟩ (congrArg Subtype.val hy)
    have h' : y = (x : ModGL t.tag K) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
  set w : t.reeLocalBlock K a j := ⟨m, hm⟩
  have hw : w • ξo ≠ ξo := by
    intro h
    have h' : m • ξ = ξ := congrArg Subtype.val h
    rw [smul_mk, mul_one, hmn] at h'
    have := mk_mul_canonicalRep_ne_one (K := K) (a := a) (j := j)
      (one_mem (t.reeFixedOrbitUnipotent K a j))
    rw [one_mul] at this
    exact this h'
  obtain ⟨hYeq, -⟩ := reeFixedOrbitNegUnipotent_eq_map_conj hm hmn
  have hmapU : (PX : Subgroup (t.reeLocalBlock K a j)).map (MulAut.conj w).toMonoidHom =
      (t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlock K a j) := by
    rw [hPX, map_conj_subgroupOf hXM, hYeq]
  have hgen : (PX : Subgroup (t.reeLocalBlock K a j)) ⊔
      (PX : Subgroup (t.reeLocalBlock K a j)).map (MulAut.conj w).toMonoidHom = ⊤ := by
    rw [hmapU, hPX, ← subgroupOf_sup_of_le hXM hYM]
    exact Subgroup.subgroupOf_self _
  have h := (large_Ree_root_pair_restriction (Ω := MulAction.orbit (t.reeLocalBlock K a j) ξ)
    (ξ := ξo) (U := PX) hΩ hUξ hUn hreg w hw hgen).1
  rw [hmapU, hPX] at h
  exact h

theorem large_Ree_local_block_Sylow_action
    (t : ReeTag) (a : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K t.prime] (j : Fin t.fixedOrbitCount) :
    t.reeLocalBlock K a j ≤ t.reeLocalParabolic K a j ∧
    (∀ m ∈ t.reeLocalBlock K a j, ∀ ω ∈ t.reeLocalCosets K a j,
      m • ω ∈ t.reeLocalCosets K a j) ∧
    (∀ ω ∈ t.reeLocalCosets K a j, ∀ ω' ∈ t.reeLocalCosets K a j,
      ∃ m ∈ t.reeLocalBlock K a j, m • ω = ω') ∧
    (∀ ω ∈ t.reeLocalCosets K a j,
      ω ≠ ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) →
      ∀ ω' ∈ t.reeLocalCosets K a j, ω' ≠ ((1 : ModGL t.tag K) : _) →
        ∃! x : t.reeFixedOrbitUnipotent K a j, (x : ModGL t.tag K) • ω = ω') ∧
    (t.reeLocalCosets K a j).ncard = Nat.card (t.reeFixedOrbitUnipotent K a j) + 1 ∧
    3 ≤ (t.reeLocalCosets K a j).ncard ∧
    t.reeFixedOrbitUnipotent K a j ≤ t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a ∧
    (∃ S : Sylow t.prime (t.reeLocalBlock K a j), (S : Subgroup (t.reeLocalBlock K a j)) =
      (t.reeFixedOrbitUnipotent K a j).subgroupOf (t.reeLocalBlock K a j)) ∧
    (∀ m ∈ t.reeLocalBlock K a j,
      m • ((1 : ModGL t.tag K) : ModGL t.tag K ⧸ t.reeFixedBorel K a) =
        ((1 : ModGL t.tag K) : _) ↔ m ∈ t.reeFixedBorel K a) ∧
    ((t.reeFixedOrbitUnipotent K a j).subgroupOf
      (t.reeLocalBlock K a j ⊓ t.reeFixedBorel K a)).Normal ∧
    (∃ w ∈ t.reeLocalBlock K a j, t.reeFixedOrbitNegUnipotent K a j =
      (t.reeFixedOrbitUnipotent K a j).map (MulAut.conj w).toMonoidHom) ∧
    t.reeFixedOrbitNegUnipotent K a j ≤ t.reeLocalBlockStabilizer K a j ∧
    (∃ S : Sylow t.prime (t.reeLocalBlockStabilizer K a j),
      (S : Subgroup (t.reeLocalBlockStabilizer K a j)) =
        (t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlockStabilizer K a j)) ∧
    (∀ S : Sylow t.prime (t.reeLocalBlockStabilizer K a j),
      (S : Subgroup (t.reeLocalBlockStabilizer K a j)) =
        (t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlockStabilizer K a j)) ∧
    Function.Injective (pairAutRestrict
      ((t.reeFixedOrbitUnipotent K a j).subgroupOf (t.reeLocalBlock K a j))
      ((t.reeFixedOrbitNegUnipotent K a j).subgroupOf (t.reeLocalBlock K a j))) := by
  have : Fact t.prime.Prime := ⟨by cases t <;> decide⟩
  have hXM := reeFixedOrbitUnipotent_le_reeLocalBlock (K := K) (a := a) j
  have hSyl := IsPGroup.toSylow_coe ((isPGroup_reeFixedOrbitUnipotent j).of_equiv
    (Subgroup.subgroupOfEquivOfLe hXM).symm) (not_dvd_index_reeFixedOrbitUnipotent j)
  obtain ⟨m, hm, hmn⟩ := exists_mem_reeLocalBlock_mk_eq (K := K) (a := a) j
  refine ⟨reeLocalBlock_le j, fun m hm ω hω => smul_mem_reeLocalCosets hm hω,
    fun ω hω ω' hω' => ?_, fun ω hω hωξ ω' hω' hω'ξ => existsUnique_smul_eq hω hωξ hω' hω'ξ,
    ncard_reeLocalCosets j, ?_, le_inf hXM (reeFixedOrbitUnipotent_le_reeFixedBorel j),
    ⟨_, hSyl⟩, fun m _ => smul_one_eq_one_iff, reeFixedOrbitUnipotent_subgroupOf_inf_normal j,
    ⟨m, hm, (reeFixedOrbitNegUnipotent_eq_map_conj hm hmn).1⟩,
    reeFixedOrbitNegUnipotent_le_reeLocalBlockStabilizer j,
    ⟨default, coe_sylow_reeLocalBlockStabilizer _⟩, coe_sylow_reeLocalBlockStabilizer,
    injective_pairAutRestrict_reeLocalBlock j⟩
  · obtain ⟨g, hg, rfl⟩ := exists_mem_reeLocalBlock_smul_one_eq hω
    obtain ⟨g', hg', rfl⟩ := exists_mem_reeLocalBlock_smul_one_eq hω'
    exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), by rw [mul_smul, inv_smul_smul]⟩
  · rw [ncard_reeLocalCosets]
    have := one_lt_card_reeFixedOrbitUnipotent (K := K) (a := a) j
    omega

end ReeTag

end CFSG.LieType.Ree
