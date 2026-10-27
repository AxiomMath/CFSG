module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L2012Y
public import CFSG.GH74.GLS.Stage2.Final.Thm6.SL2BoundBar
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Inst
public import CFSG.GH74.GLS.Stage2.Final.Thm6.L20_14

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L2012

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final
  CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2 CFSG.GH74.GLS.Stage2.Final.Thm6.SL2Bound

section Pairs

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

theorem pair₁_of_stage1 (hP : Stage1Pair G z S q L₁ L₂) : Pair L₁ L₂ q q where
  odd := hP.odd
  gt := hP.gt3
  odd' := hP.odd
  hm := hP.sl₁
  hm' := hP.sl₂
  comm := hP.prod.2.1
  inf := hP.prod.2.2

theorem pair₂_of_stage1 (hP : Stage1Pair G z S q L₁ L₂) : Pair L₂ L₁ q q where
  odd := hP.odd
  gt := hP.gt3
  odd' := hP.odd
  hm := hP.sl₂
  hm' := hP.sl₁
  comm := fun a ha b hb => (hP.prod.2.1 b hb a ha).symm
  inf := by rw [inf_comm]; exact hP.prod.2.2

theorem isComponent_L₁ (hP : Stage1Pair G z S q L₁ L₂) : IsComponent L₁ := by
  have : L₁ ∈ {K : Subgroup (CentralizerBar z) | IsComponent K} := by
    rw [hP.comps]; exact Set.mem_insert _ _
  exact this

theorem cj_L₁_cases (hP : Stage1Pair G z S q L₁ L₂) (y : CentralizerBar z) :
    cj y L₁ = L₁ ∨ cj y L₁ = L₂ := by
  have h1 : IsComponent (cj y L₁) := isComponent_cj y (isComponent_L₁ hP)
  have h2 : cj y L₁ ∈ ({L₁, L₂} : Set (Subgroup (CentralizerBar z))) := by
    rw [← hP.comps]; exact h1
  simpa using h2

end Pairs

section Nrm

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {q : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

abbrev Nrm (L₁ : Subgroup (CentralizerBar z)) : Subgroup (CentralizerBar z) :=
  normalizer (L₁ : Set (CentralizerBar z))

omit [Finite G] in
theorem nrm_le₁ : L₁ ≤ Nrm L₁ := Subgroup.le_normalizer

theorem nrm_le₂ (hP : Stage1Pair G z S q L₁ L₂) : L₂ ≤ Nrm L₁ :=
  (bar_le_centralizer_of_comm hP.prod.2.1).trans (Subgroup.centralizer_le_normalizer _)

theorem nrm_normalizes₂ (hP : Stage1Pair G z S q L₁ L₂) {n : CentralizerBar z} (hn : n ∈ Nrm L₁) :
    n ∈ normalizer (L₂ : Set (CentralizerBar z)) :=
  bar_mem_normalizer_other hP.ne hP.comps hn

theorem cj_eq_of_not_mem (hP : Stage1Pair G z S q L₁ L₂) {y : CentralizerBar z} (hy : y ∉ Nrm L₁) :
    cj y L₁ = L₂ :=
  (cj_L₁_cases hP y).resolve_left (fun h => hy (cj_eq_iff.1 h))

omit [Finite G] in
theorem inv_mul_mem_nrm {y₁ y₂ : CentralizerBar z}
    (h₁ : cj y₁ L₁ = L₂) (h₂ : cj y₂ L₁ = L₂) : y₁⁻¹ * y₂ ∈ Nrm L₁ := by
  rw [← cj_eq_iff, cj_mul, h₂, ← h₁, cj_inv_cj]

theorem exists_swap_bar (hP : Stage1Pair G z S q L₁ L₂) :
    ∃ (s : G) (_ : s ∈ S) (hsC : s ∈ Cen z), cj (toBar z ⟨s, hsC⟩) L₁ = L₂ := by
  obtain ⟨s, hsS, hsw⟩ := hP.swap
  obtain ⟨hsC, hcj⟩ := L20.swaps_cj hsw
  exact ⟨s, hsS, hsC, hcj⟩

theorem nrm_index (hP : Stage1Pair G z S q L₁ L₂) : (Nrm L₁).index = 2 := by
  obtain ⟨s, -, hsC, hs⟩ := exists_swap_bar hP
  have hy₀ : toBar z ⟨s, hsC⟩ ∉ Nrm L₁ := by
    intro h
    have h1 : cj (toBar z ⟨s, hsC⟩) L₁ = L₁ := cj_eq_iff.2 h
    exact hP.ne (h1.symm.trans hs)
  rw [Subgroup.index_eq_two_iff]
  refine ⟨toBar z ⟨s, hsC⟩, fun b => ?_⟩
  by_cases hb : b ∈ Nrm L₁
  · have : b * toBar z ⟨s, hsC⟩ ∉ Nrm L₁ := fun h => hy₀ (by
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
      simpa using this)
    exact Or.inr ⟨hb, this⟩
  · have : b * toBar z ⟨s, hsC⟩ ∈ Nrm L₁ := by
      by_contra h
      apply hy₀
      have := inv_mul_mem_nrm (cj_eq_of_not_mem hP hb) (cj_eq_of_not_mem hP h)
      simpa using this
    exact Or.inl ⟨this, hb⟩

theorem nrm_normal (hP : Stage1Pair G z S q L₁ L₂) : (Nrm L₁).Normal :=
  Subgroup.normal_of_index_eq_two (nrm_index hP)

theorem barS1_eq (hP : Stage1Pair G z S q L₁ L₂) : barOf z (S1 S z) = barOf z S ⊓ Nrm L₁ := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, hsC, hsS1, rfl⟩ := bar_mem_barOf_iff.1 hx
    obtain ⟨hsS, hsC', hK⟩ := bar_mem_S1_iff.1 hsS1
    refine ⟨bar_mem_barOf_iff.2 ⟨s, hsC, hsS, rfl⟩, ?_⟩
    have hLle : L₁ ≤ LBar z := hP.prod.1 ▸ le_sup_left
    exact hK L₁ (isComponent_L₁ hP) hLle
  · rintro ⟨hxS, hxN⟩
    obtain ⟨s, hsC, hsS, rfl⟩ := bar_mem_barOf_iff.1 hxS
    refine bar_mem_barOf_iff.2 ⟨s, hsC, ?_, rfl⟩
    rw [bar_mem_S1_iff]
    exact ⟨hsS, hsC, fun K hK _ => bar_mem_normalizer_comp hP.comps hxN (nrm_normalizes₂ hP hxN) hK⟩

theorem nrm_sup_barS (hP : Stage1Pair G z S q L₁ L₂) : Nrm L₁ ⊔ barOf z S = ⊤ := by
  obtain ⟨s, hsS, hsC, hs⟩ := exists_swap_bar hP
  rw [eq_top_iff]
  intro x _
  by_cases hx : x ∈ Nrm L₁
  · exact Subgroup.mem_sup_left hx
  · have h1 := inv_mul_mem_nrm hs (cj_eq_of_not_mem hP hx)
    have hsb : toBar z ⟨s, hsC⟩ ∈ barOf z S := bar_mem_barOf_iff.2 ⟨s, hsC, hsS, rfl⟩
    have : x = toBar z ⟨s, hsC⟩ * ((toBar z ⟨s, hsC⟩)⁻¹ * x) := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hsb) (Subgroup.mem_sup_left h1)

theorem isSylow_bar_S1 (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (hP : Stage1Pair G z S q L₁ L₂) :
    CFSG.ABGLocalTools.IsSylowOf 2 (barOf z (S1 S z)) (Nrm L₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSb := isSylowOf_barOf hS
  obtain ⟨-, hpS, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hSb
  rw [Subgroup.relIndex_top_right] at hidx
  have hNn := nrm_normal hP
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  refine ⟨?_, ?_, ?_⟩
  · rw [barS1_eq hP]; exact inf_le_right
  · rw [barS1_eq hP]; exact hpS.to_le inf_le_left
  · rw [barS1_eq hP, Subgroup.inf_relIndex_right, ← CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal (Nrm L₁) (barOf z S),
      nrm_sup_barS hP, Subgroup.relIndex_top_right]
    exact hidx

theorem rc_le_S1 (hSC : S ≤ Cen z) (hP : Stage1Pair G z S q L₁ L₂) : RC S z ≤ S1 S z := by
  intro s hs
  have hs' : s ∈ S ⊓ LC z := hs
  have hsC : s ∈ Cen z := hSC hs'.1
  have hsL : toBar z ⟨s, hsC⟩ ∈ LBar z := bar_mem_barOf_iff.2 ⟨s, hsC, hs'.2, rfl⟩
  rw [← hP.prod.1] at hsL
  have hsN := bar_sup_le_normalizer_inf hP.prod.2.1 hsL
  rw [bar_mem_S1_iff]
  exact ⟨hs'.1, hsC, fun K hK _ => bar_mem_normalizer_comp hP.comps hsN.1 hsN.2 hK⟩

theorem not_S_le_S1 (hP : Stage1Pair G z S q L₁ L₂) : ¬ S ≤ S1 S z := by
  intro hle
  obtain ⟨s, hsS, hsC, hs⟩ := exists_swap_bar hP
  have hmem : toBar z ⟨s, hsC⟩ ∈ barOf z (S1 S z) := bar_mem_barOf_iff.2 ⟨s, hsC, hle hsS, rfl⟩
  rw [barS1_eq hP] at hmem
  exact hP.ne ((cj_eq_iff.2 hmem.2).symm.trans hs)

theorem relIndex_R_S1_le_two (hSC : S ≤ Cen z) (hP : Stage1Pair G z S q L₁ L₂)
    (hidx : (RC S z).relIndex S ≤ 4) : (RC S z).relIndex (S1 S z) ≤ 2 := by
  have hRS1 := rc_le_S1 hSC hP
  have e2 := Subgroup.relIndex_mul_relIndex (RC S z) (S1 S z) S hRS1 bar_S1_le_S
  have hc : 2 ≤ (S1 S z).relIndex S := by
    have h0 : (S1 S z).relIndex S ≠ 0 := bar_relIndex_ne_zero _ _
    have h1 : (S1 S z).relIndex S ≠ 1 := fun h => not_S_le_S1 hP (Subgroup.relIndex_eq_one.1 h)
    omega
  by_contra hgt
  push Not at hgt
  have : 3 * 2 ≤ (RC S z).relIndex S := by rw [← e2]; exact Nat.mul_le_mul hgt hc
  omega

theorem Rb_idx_S1 (hSC : S ≤ Cen z) (hP : Stage1Pair G z S q L₁ L₂) (hidx : (RC S z).relIndex S ≤ 4) :
    ∀ y ∈ barOf z (S1 S z), y ∉ barOf z (RC S z) → ∀ s ∈ barOf z (S1 S z),
      s ∈ barOf z (RC S z) ∨ y⁻¹ * s ∈ barOf z (RC S z) := by
  have hle2 := relIndex_R_S1_le_two hSC hP hidx
  rintro y ⟨⟨y', hy'C⟩, hy'S, rfl⟩ hyR s ⟨⟨s', hs'C⟩, hs'S, rfl⟩
  have hy'S' : y' ∈ S1 S z := Subgroup.mem_subgroupOf.mp hy'S
  have hs'S' : s' ∈ S1 S z := Subgroup.mem_subgroupOf.mp hs'S
  by_cases hsR : s' ∈ RC S z
  · left
    exact ⟨⟨s', hs'C⟩, Subgroup.mem_subgroupOf.mpr hsR, rfl⟩
  · right
    have hyR' : y' ∉ RC S z := fun h => hyR ⟨⟨y', hy'C⟩, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    have hidx2 : ((RC S z).subgroupOf (S1 S z)).index = 2 := by
      have h0 : (RC S z).relIndex (S1 S z) ≠ 0 := bar_relIndex_ne_zero _ _
      have h1 : (RC S z).relIndex (S1 S z) ≠ 1 := fun h => hyR' (Subgroup.relIndex_eq_one.1 h hy'S')
      show (RC S z).relIndex (S1 S z) = 2
      omega
    have h2 : (⟨y', hy'S'⟩ : ↥(S1 S z))⁻¹ ∉ (RC S z).subgroupOf (S1 S z) := by
      rw [inv_mem_iff]
      exact fun h => hyR' (Subgroup.mem_subgroupOf.mp h)
    have h3 : (⟨s', hs'S'⟩ : ↥(S1 S z)) ∉ (RC S z).subgroupOf (S1 S z) := fun h =>
      hsR (Subgroup.mem_subgroupOf.mp h)
    have h1 : (⟨y', hy'S'⟩ : ↥(S1 S z))⁻¹ * ⟨s', hs'S'⟩ ∈ (RC S z).subgroupOf (S1 S z) := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx2]
      exact ⟨fun h => absurd h h2, fun h => absurd h h3⟩
    have h1' : y'⁻¹ * s' ∈ RC S z := Subgroup.mem_subgroupOf.mp h1
    refine ⟨⟨y'⁻¹ * s', (Cen z).mul_mem ((Cen z).inv_mem hy'C) hs'C⟩,
      Subgroup.mem_subgroupOf.mpr h1', ?_⟩
    rw [← map_inv, ← map_mul]
    rfl

theorem centralizer_sup_le (hP : Stage1Pair G z S q L₁ L₂) :
    ∀ x : CentralizerBar z, (∀ y ∈ L₁ ⊔ L₂, x * y = y * x) → x ∈ L₁ ⊔ L₂ := by
  intro x hx
  have hF : generalizedFitting (CentralizerBar z) = L₁ ⊔ L₂ := hP.fitting.trans hP.prod.1.symm
  have hcen : x ∈ Subgroup.centralizer ((generalizedFitting (CentralizerBar z) : Subgroup (CentralizerBar z)) :
      Set (CentralizerBar z)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hF] at hh
    exact (hx h hh).symm
  have := CFSG.centralizer_generalizedFitting_le (CentralizerBar z) hcen
  rwa [hF] at this

theorem ykey_l4 {ε : Bool} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (Cen z)) (hSC : S ≤ Cen z)
    (hL4 : Stage1L4 G z S ε q L₁ L₂)
    {t e : CentralizerBar z} (ht : t ∈ L₁ ⊔ L₂) (ht2 : t * t = 1) (htI : t ∉ L₁ ⊓ L₂)
    (heN : e ∈ Nrm L₁) (he2 : e * e = 1) (het : e * t = t * e) (heI : e ∉ L₁ ⊓ L₂)
    (hetI : e * t ∉ L₁ ⊓ L₂)
    {Bb : Subgroup (CentralizerBar z)} (hBN : Bb ≤ Nrm L₁) (hBodd : Odd (Nat.card ↥Bb))
    (hBt : ∀ b ∈ Bb, b * t = t * b)
    (hBn : ∀ m ∈ Nrm L₁, m * t = t * m → ∀ b ∈ Bb, m * b * m⁻¹ ∈ Bb)
    (hBe : ∀ b ∈ Bb, e * b = b * e) : Bb = ⊥ := by
  have hP := hL4.pair
  have hS1N : barOf z (S1 S z) ≤ Nrm L₁ := by
    rw [barS1_eq hP]; exact inf_le_right
  have htN : t ∈ Nrm L₁ := (sup_le nrm_le₁ (nrm_le₂ hP)) ht
  refine ykey_sub (N := Nrm L₁) (Sb := barOf z (S1 S z)) (Rb := barOf z (RC S z)) nrm_le₁ (nrm_le₂ hP) hS1N
    (pair₁_of_stage1 hP) (pair₂_of_stage1 hP)
    (fun n hn x hx => (Subgroup.mem_normalizer_iff.1 hn x).1 hx)
    (fun n hn x hx => (Subgroup.mem_normalizer_iff.1 (nrm_normalizes₂ hP hn) x).1 hx)
    (isSylow_bar_S1 hS hP) hL4.pgl.1 hL4.pgl.2 ?_ (Rb_idx_S1 hSC hP hL4.index_le)
    (fun x _ hx => centralizer_sup_le hP x hx) htN heN ht ht2 htI he2 het heI hetI hBN hBodd hBt hBn hBe
  rw [hP.prod.1]
  exact barOf_le_LBar (inf_le_right : S ⊓ LC z ≤ LC z)

end Nrm

end CFSG.GH74.GLS.Stage2.Final.Thm6.L2012
