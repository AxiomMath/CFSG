module

public import CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2Bar
public import CFSG.GH74.GLS.Stage2.Final.ClassicalLib
public import CFSG.GH74.GLS.Stage2.Final.L26.G2Three

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Stage2.Final

section Abstract

variable {Y : Type} [Group Y]

@[expose] def cj (y : Y) (H : Subgroup Y) : Subgroup Y := H.map (MulAut.conj y).toMonoidHom

theorem mem_cj_iff {y x : Y} {H : Subgroup Y} : x ∈ cj y H ↔ y⁻¹ * x * y ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    have e : y⁻¹ * ((MulAut.conj y).toMonoidHom h) * y = h := by
      show y⁻¹ * (y * h * y⁻¹) * y = h
      group
    rw [e]
    exact hh
  · intro h
    refine ⟨y⁻¹ * x * y, h, ?_⟩
    show y * (y⁻¹ * x * y) * y⁻¹ = x
    group

theorem cj_mul (y y' : Y) (H : Subgroup Y) : cj (y * y') H = cj y (cj y' H) := by
  ext x
  simp only [mem_cj_iff, mul_inv_rev, mul_assoc]

theorem cj_one (H : Subgroup Y) : cj 1 H = H := by
  ext x
  simp [mem_cj_iff]

theorem cj_inv_cj (y : Y) (H : Subgroup Y) : cj y⁻¹ (cj y H) = H := by
  rw [← cj_mul, inv_mul_cancel, cj_one]

theorem cj_eq_iff {y : Y} {Lk : Subgroup Y} : cj y Lk = Lk ↔ y ∈ normalizer (Lk : Set Y) := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    constructor
    · intro hx
      have h2 : y * x * y⁻¹ ∈ cj y Lk := by
        rw [mem_cj_iff]
        have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
        rw [e]
        exact hx
      rwa [h] at h2
    · intro hx
      rw [← h, mem_cj_iff] at hx
      have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
      rwa [e] at hx
  · intro h
    ext x
    rw [mem_cj_iff]
    have h1 := h (y⁻¹ * x * y)
    have e : y * (y⁻¹ * x * y) * y⁻¹ = x := by group
    rw [e] at h1
    exact h1

end Abstract

section Normal

variable {Y : Type} [Group Y] [Finite Y]

theorem normal_of_two_conj {Sb Lk Lk' : Subgroup Y} (hS : CFSG.ABGLocalTools.IsSylowOf 2 Sb ⊤)
    (hconj : ∀ y : Y, cj y Lk = Lk ∨ cj y Lk = Lk') (hSb : Sb ≤ normalizer (Lk : Set Y)) :
    Lk.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : normalizer (Lk : Set Y) = ⊤ := by
    by_contra hne
    obtain ⟨y₀, hy₀⟩ : ∃ y₀ : Y, y₀ ∉ normalizer (Lk : Set Y) := by
      by_contra hall
      push Not at hall
      exact hne (eq_top_iff.2 fun y _ => hall y)
    have hout : ∀ y : Y, y ∉ normalizer (Lk : Set Y) → cj y Lk = Lk' := fun y hy =>
      (hconj y).resolve_left (fun h => hy (cj_eq_iff.1 h))
    have hy₀' : cj y₀ Lk = Lk' := hout y₀ hy₀
    have hB : ∀ y₁ y₂ : Y, cj y₁ Lk = Lk' → cj y₂ Lk = Lk' → y₁⁻¹ * y₂ ∈ normalizer (Lk : Set Y) := by
      intro y₁ y₂ h₁ h₂
      rw [← cj_eq_iff, cj_mul, h₂, ← h₁, cj_inv_cj]
    have hidx : (normalizer (Lk : Set Y)).index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨y₀, fun b => ?_⟩
      by_cases hb : b ∈ normalizer (Lk : Set Y)
      · have : b * y₀ ∉ normalizer (Lk : Set Y) := fun h => hy₀ (by
          have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) h
          simpa using this)
        exact Or.inr ⟨hb, this⟩
      · have : b * y₀ ∈ normalizer (Lk : Set Y) := by
          by_contra h
          apply hy₀
          have := hB b (b * y₀) (hout b hb) (hout _ h)
          simpa using this
        exact Or.inl ⟨this, hb⟩
    obtain ⟨-, -, hidxS⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hS
    rw [Subgroup.relIndex_top_right] at hidxS
    exact hidxS (hidx ▸ Subgroup.index_dvd_of_le hSb)
  exact Subgroup.normalizer_eq_top_iff.1 hN

omit [Finite Y] in
theorem not_comm_of_isComponent {J : Subgroup Y} (hJ : IsComponent J) :
    ¬ ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := by
  intro hc
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  have hnt : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  have hsol : Group.IsSolvable ↥J :=
    Group.isSolvable_of_comm (fun a b => Subtype.ext (hc a a.2 b b.2))
  exact Group.IsPerfect.not_isSolvable ↥J hsol

end Normal

section Shape

variable {G : Type} [Group G] [Finite G] {z : G} {S : Subgroup G} {r₁ r₂ : ℕ}
  {L₁ L₂ : Subgroup (CentralizerBar z)}

omit [Finite G] in
theorem three_le_r₂ (hsh : G2Shape z S r₁ r₂ L₁ L₂) : 3 ≤ r₂ := by
  obtain ⟨-, hodd₂, -, -, -, hm₂, -⟩ := hsh
  obtain ⟨F, hF, hFin, hq, -⟩ := hm₂
  have h1 : 1 < Nat.card F := Finite.one_lt_card
  have h2 : Nat.card F = r₂ := hq
  obtain ⟨m, hm⟩ := hodd₂
  omega

omit [Finite G] in
theorem pair₁ (hsh : G2Shape z S r₁ r₂ L₁ L₂) : Pair L₁ L₂ r₁ r₂ := by
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, -, -, -, -, -⟩ := hsh
  obtain ⟨-, hcomm, hcard⟩ := hprod
  exact ⟨hodd₁, hg₁, hodd₂, hm₁, hm₂, hcomm, hcard⟩

omit [Finite G] in
theorem pair₂ (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h : 3 < r₂) : Pair L₂ L₁ r₂ r₁ := by
  obtain ⟨hodd₁, hodd₂, hg₁, hprod, hm₁, hm₂, -, -, -, -, -, -⟩ := hsh
  obtain ⟨-, hcomm, hcard⟩ := hprod
  exact ⟨hodd₂, h, hodd₁, hm₂, hm₁, fun a ha b hb => (hcomm b hb a ha).symm, by rwa [inf_comm]⟩

omit [Finite G] in
theorem sup_eq (hsh : G2Shape z S r₁ r₂ L₁ L₂) : L₁ ⊔ L₂ = LBar z := by
  obtain ⟨-, -, -, ⟨hsup, -, -⟩, -⟩ := hsh
  exact hsup

theorem isComponent₁ (hsh : G2Shape z S r₁ r₂ L₁ L₂) : IsComponent L₁ := by
  have p := pair₁ hsh
  exact L26.isComponent_of_sl2_pair (sup_eq hsh) p.comm (LBar_normal z) p.odd (by have := p.gt; omega)
    p.hm

theorem isComponent₂ (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h : 3 < r₂) : IsComponent L₂ := by
  have p := pair₂ hsh h
  exact L26.isComponent_of_sl2_pair (by rw [sup_comm]; exact sup_eq hsh) p.comm (LBar_normal z)
    p.odd (by omega) p.hm

theorem comp_eq_big (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) {J : Subgroup (CentralizerBar z)}
    (hJ : IsComponent J) : J = L₁ ∨ J = L₂ := by
  have p₁ := pair₁ hsh
  have p₂ := pair₂ hsh h3
  have hFLB : generalizedFitting (CentralizerBar z) = LBar z := by
    obtain ⟨-, -, -, -, -, -, -, -, h4, -⟩ := hsh
    exact (h4 h3).2
  have hJle : J ≤ L₁ ⊔ L₂ := by
    rw [sup_eq hsh]
    calc J ≤ layer (CentralizerBar z) := le_sSup hJ
      _ ≤ generalizedFitting (CentralizerBar z) := le_sup_right
      _ = LBar z := hFLB
  by_contra hne
  push Not at hne
  have hJ₁ := (CFSG.LocalCores.distinct_components_commute hJ (isComponent₁ hsh)).resolve_left hne.1
  have hJ₂ := (CFSG.LocalCores.distinct_components_commute hJ (isComponent₂ hsh h3)).resolve_left hne.2
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hJ₁ hJ₂
  have hmem : ∀ j ∈ J, j ∈ L₁ ⊓ L₂ := by
    intro j hj
    have h1 : j ∈ L₂ := p₁.mem_of_cen (hJle hj) (fun c hc => (Subgroup.mem_centralizer_iff.mp (hJ₁ hj) c hc).symm)
    have h2 : j ∈ L₁ := p₂.mem_of_cen (by rw [sup_comm]; exact hJle hj)
      (fun c hc => (Subgroup.mem_centralizer_iff.mp (hJ₂ hj) c hc).symm)
    exact ⟨h2, h1⟩
  exact not_comm_of_isComponent hJ fun a ha b hb => p₁.comm a (hmem a ha).1 b (hmem b hb).2

theorem comp_eq_three (hsh : G2Shape z S r₁ 3 L₁ L₂) {J : Subgroup (CentralizerBar z)}
    (hJ : IsComponent J) : J = L₁ := by
  have p₁ := pair₁ hsh
  have hsup := sup_eq hsh
  have hc₁ := isComponent₁ hsh
  obtain ⟨-, -, -, -, -, hm₂, -, h3, -⟩ := hsh
  have hJle : J ≤ L₁ ⊔ L₂ := by
    have hF : generalizedFitting (CentralizerBar z) ≤ L₁ ⊔ L₂ := by
      rw [(h3 rfl).2, hsup]
      exact Subgroup.map_subtype_le _
    exact (le_sSup hJ : J ≤ layer (CentralizerBar z)).trans (le_sup_right.trans hF)
  by_contra hne
  have hJ₁ := (CFSG.LocalCores.distinct_components_commute hJ hc₁).resolve_left hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hJ₁
  have hJL₂ : J ≤ L₂ := fun j hj =>
    p₁.mem_of_cen (hJle hj) (fun c hc => (Subgroup.mem_centralizer_iff.mp (hJ₁ hj) c hc).symm)
  have hsol₂ : Group.IsSolvable ↥L₂ := L26.isSolvable_of_hasSL2Model_three' hm₂
  have hsolJ : Group.IsSolvable ↥J :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hJL₂)
  have hperf : Group.IsPerfect ↥J := hJ.1.1
  have hnt : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hJ.1
  exact Group.IsPerfect.not_isSolvable ↥J hsolJ

theorem isComponent_cj {Y : Type} [Group Y] {J : Subgroup Y} (y : Y) (hJ : IsComponent J) :
    IsComponent (cj y J) :=
  CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj y) hJ

theorem normal₁_three (hsh : G2Shape z S r₁ 3 L₁ L₂) : L₁.Normal := by
  have hc₁ := isComponent₁ hsh
  have : normalizer (L₁ : Set (CentralizerBar z)) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [← cj_eq_iff]
    exact comp_eq_three hsh (isComponent_cj y hc₁)
  exact Subgroup.normalizer_eq_top_iff.1 this

theorem sbar_le_normalizer (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) :
    SBar S z ≤ normalizer (L₁ : Set (CentralizerBar z)) := by
  intro s hs
  by_contra hns
  have hc₁ := isComponent₁ hsh
  have hcs : cj s L₁ = L₂ := by
    rcases comp_eq_big hsh h3 (isComponent_cj s hc₁) with h | h
    · exact absurd (cj_eq_iff.1 h) hns
    · exact h
  have p₁ := pair₁ hsh
  obtain ⟨-, -, -, -, -, -, -, -, -, -, ⟨hnT, -⟩, -⟩ := hsh
  have hsT : s ∈ L₁ ⊔ SBar S z := Subgroup.mem_sup_right hs
  have hcomm : ∀ x ∈ L₁, ∀ c ∈ L₁, c * x = x * c := by
    intro x hx c hc
    have hxT : x ∈ L₁ ⊔ SBar S z := Subgroup.mem_sup_left hx
    have h1 : ∀ l ∈ L₁, (s⁻¹ * x * s) * l = l * (s⁻¹ * x * s) := by
      intro l hl
      have hl' : s * l * s⁻¹ ∈ L₂ := by
        rw [← hcs, mem_cj_iff]
        have e : s⁻¹ * (s * l * s⁻¹) * s = l := by group
        rw [e]
        exact hl
      have := p₁.comm x hx _ hl'
      calc (s⁻¹ * x * s) * l = s⁻¹ * (x * (s * l * s⁻¹)) * s := by group
        _ = s⁻¹ * ((s * l * s⁻¹) * x) * s := by rw [this]
        _ = l * (s⁻¹ * x * s) := by group
    have hmem : s⁻¹ * x * s ∈ L₁ ⊔ SBar S z :=
      mul_mem (mul_mem (inv_mem hsT) hxT) hsT
    have hN : (⟨s⁻¹ * x * s, hmem⟩ : ↥(L₁ ⊔ SBar S z)) ∈
        (centralizer (L₁ : Set (CentralizerBar z))).subgroupOf (L₁ ⊔ SBar S z) := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro l hl
      exact (h1 l hl).symm
    have h3' := hnT.conj_mem _ hN ⟨s, hsT⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h3'
    have := h3' c hc
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [e] at this
    exact this
  exact p₁.not_comm fun a ha b hb => hcomm b hb a ha

theorem normal₁_big (hctx : Stage2Ctx G z Kind.g2 S) (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) :
    L₁.Normal :=
  normal_of_two_conj (Lk' := L₂) (isSylowOf_barOf hctx.sylow)
    (fun y => comp_eq_big hsh h3 (isComponent_cj y (isComponent₁ hsh))) (sbar_le_normalizer hsh h3)

theorem normal₁ (hctx : Stage2Ctx G z Kind.g2 S) (hsh : G2Shape z S r₁ r₂ L₁ L₂) : L₁.Normal := by
  have h3 := three_le_r₂ hsh
  rcases Nat.lt_or_ge 3 r₂ with h | h
  · exact normal₁_big hctx hsh h
  · obtain rfl : r₂ = 3 := by omega
    exact normal₁_three hsh

theorem normal₂ (hctx : Stage2Ctx G z Kind.g2 S) (hsh : G2Shape z S r₁ r₂ L₁ L₂) : L₂.Normal := by
  have hn₁ := normal₁ hctx hsh
  have p₁ := pair₁ hsh
  have hsup := sup_eq hsh
  refine ⟨fun x hx y => ?_⟩
  have hLb : y * x * y⁻¹ ∈ L₁ ⊔ L₂ := by
    rw [hsup]
    exact (LBar_normal z).conj_mem x (by rw [← hsup]; exact Subgroup.mem_sup_right hx) y
  refine p₁.mem_of_cen hLb (fun c hc => ?_)
  have hc' : y⁻¹ * c * y ∈ L₁ := by simpa using hn₁.conj_mem c hc y⁻¹
  have := p₁.comm _ hc' x hx
  calc y * x * y⁻¹ * c = y * (x * (y⁻¹ * c * y)) * y⁻¹ := by group
    _ = y * ((y⁻¹ * c * y) * x) * y⁻¹ := by rw [this]
    _ = c * (y * x * y⁻¹) := by group

omit [Finite G] in
theorem Rb_idx_of (hidx : (RC S z).relIndex S = 2) :
    ∀ y ∈ SBar S z, y ∉ barOf z (RC S z) → ∀ s ∈ SBar S z,
      s ∈ barOf z (RC S z) ∨ y⁻¹ * s ∈ barOf z (RC S z) := by
  rintro y ⟨⟨y', hy'C⟩, hy'S, rfl⟩ hyR s ⟨⟨s', hs'C⟩, hs'S, rfl⟩
  have hy'S' : y' ∈ S := Subgroup.mem_subgroupOf.mp hy'S
  have hs'S' : s' ∈ S := Subgroup.mem_subgroupOf.mp hs'S
  by_cases hsR : s' ∈ RC S z
  · left
    exact ⟨⟨s', hs'C⟩, Subgroup.mem_subgroupOf.mpr hsR, rfl⟩
  · right
    have hyR' : y' ∉ RC S z := fun h => hyR ⟨⟨y', hy'C⟩, Subgroup.mem_subgroupOf.mpr h, rfl⟩
    have hidx' : ((RC S z).subgroupOf S).index = 2 := hidx
    have h2 : (⟨y', hy'S'⟩ : ↥S)⁻¹ ∉ (RC S z).subgroupOf S := by
      rw [inv_mem_iff]
      exact fun h => hyR' (Subgroup.mem_subgroupOf.mp h)
    have h3 : (⟨s', hs'S'⟩ : ↥S) ∉ (RC S z).subgroupOf S := fun h =>
      hsR (Subgroup.mem_subgroupOf.mp h)
    have h1 : (⟨y', hy'S'⟩ : ↥S)⁻¹ * ⟨s', hs'S'⟩ ∈ (RC S z).subgroupOf S := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx']
      exact ⟨fun h => absurd h h2, fun h => absurd h h3⟩
    have h1' : y'⁻¹ * s' ∈ RC S z := Subgroup.mem_subgroupOf.mp h1
    refine ⟨⟨y'⁻¹ * s', (Cen z).mul_mem ((Cen z).inv_mem hy'C) hs'C⟩,
      Subgroup.mem_subgroupOf.mpr h1', ?_⟩
    rw [← map_inv, ← map_mul]
    rfl

theorem factor₁ (hctx : Stage2Ctx G z Kind.g2 S) (hsh : G2Shape z S r₁ r₂ L₁ L₂) :
    Factor (SBar S z) (barOf z (RC S z)) L₁ L₂ r₁ r₂ := by
  have p := pair₁ hsh
  have hn := normal₁ hctx hsh
  have hsup := sup_eq hsh
  obtain ⟨-, -, -, -, -, -, -, -, -, hidx, hind₁, -⟩ := hsh
  exact
    { toPair := p
      normal := hn
      syl := isSylowOf_barOf hctx.sylow
      ind := hind₁
      Rb_le := by
        rw [hsup]
        exact barOf_le_LBar (inf_le_right : S ⊓ LC z ≤ LC z)
      Rb_idx := Rb_idx_of hidx }

theorem factor₂ (hctx : Stage2Ctx G z Kind.g2 S) (hsh : G2Shape z S r₁ r₂ L₁ L₂) (h3 : 3 < r₂) :
    Factor (SBar S z) (barOf z (RC S z)) L₂ L₁ r₂ r₁ := by
  have p := pair₂ hsh h3
  have hn := normal₂ hctx hsh
  have hsup := sup_eq hsh
  obtain ⟨-, -, -, -, -, -, -, -, -, hidx, -, hind₂⟩ := hsh
  exact
    { toPair := p
      normal := hn
      syl := isSylowOf_barOf hctx.sylow
      ind := hind₂
      Rb_le := by
        rw [sup_comm, hsup]
        exact barOf_le_LBar (inf_le_right : S ⊓ LC z ≤ LC z)
      Rb_idx := Rb_idx_of hidx }

end Shape

end CFSG.GH74.GLS.Stage2.Final.Thm6.L208g2
