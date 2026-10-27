module

public import CFSG.GH74.Generic.S1.Exo.Glue

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic CFSG.GH74.GLS
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem proj_injective_of_odd_free {v : G} {B : Subgroup G} (hBv : B ≤ centralizer ({v} : Set G))
    (hodd : ∀ N : Subgroup ↥B, N.Normal → Odd (Nat.card N) → N = ⊥) :
    Function.Injective ((proj v).comp (Subgroup.inclusion hBv)) := by
  set φ₀ : ↥B →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hBv) with hφ₀
  rw [← MonoidHom.ker_eq_bot_iff]
  refine hodd _ (MonoidHom.normal_ker φ₀) ?_
  by_contra hne
  rw [Nat.not_odd_iff_even] at hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := ↥φ₀.ker) 2 (even_iff_two_dvd.1 hne)
  have hk1 : φ₀ (k : ↥B) = 1 := k.2
  have hmem : (⟨((k : ↥B) : G), hBv (k : ↥B).2⟩ : ↥(centralizer ({v} : Set G))) ∈
      pPrimeCore 2 ↥(centralizer ({v} : Set G)) := (QuotientGroup.eq_one_iff _).1 hk1
  have hodd2 := orderOf_odd_of_mem_pPrimeCore hmem
  have hord : orderOf (⟨((k : ↥B) : G), hBv (k : ↥B).2⟩ : ↥(centralizer ({v} : Set G))) = 2 := by
    have h1 : orderOf (Subgroup.inclusion hBv (k : ↥B)) = orderOf (k : ↥B) :=
      orderOf_injective (Subgroup.inclusion hBv) (Subgroup.inclusion_injective hBv) _
    have h2 : orderOf (k : ↥B) = 2 := (Subgroup.orderOf_coe k).trans hk
    exact h1.trans h2
  rw [hord] at hodd2
  exact absurd hodd2 (by decide)

omit [Finite G] in
theorem exists_mulEquiv_barSub_of_inj {v : G} {B : Subgroup G} (hBv : B ≤ centralizer ({v} : Set G))
    (hinj : Function.Injective ((proj v).comp (Subgroup.inclusion hBv))) :
    ∃ φ : ↥B ≃* ↥(S45.barSub v B),
      ∀ b : ↥B, ((φ b : ↥(S45.barSub v B)) : CentralizerBar v) = proj v ⟨(b : G), hBv b.2⟩ := by
  set φ₀ : ↥B →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hBv) with hφ₀
  have hrange : φ₀.range = S45.barSub v B := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact S45.proj_mem_barSub (hBv j.2) j.2
    · intro hy
      obtain ⟨g, hg, hgJ, rfl⟩ := S45.mem_barSub.1 hy
      exact ⟨⟨g, hgJ⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun b => rfl⟩

omit [Finite G] in
theorem barSub_cent_of_inj {c : G} {B : Subgroup G} (hBv : B ≤ centralizer ({c} : Set G))
    (hinj : Function.Injective ((proj c).comp (Subgroup.inclusion hBv)))
    {e : G} (heB : e ∈ B) (he2 : e * e = 1) (he1 : e ≠ 1)
    (hcen : center ↥B = Subgroup.zpowers (⟨e, heB⟩ : ↥B)) :
    ∀ a ∈ S45.barSub c B, (∀ b ∈ S45.barSub c B, a * b = b * a) →
      a = 1 ∨ a = proj c ⟨e, hBv heB⟩ := by
  have he2' : (⟨e, heB⟩ : ↥B) * ⟨e, heB⟩ = 1 := Subtype.ext he2
  have he1' : (⟨e, heB⟩ : ↥B) ≠ 1 := fun h => he1 (congrArg Subtype.val h)
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_barSub_of_inj hBv hinj
  intro a ha hcomm
  set a₀ : ↥B := φ.symm ⟨a, ha⟩ with ha₀
  have haφ : (φ a₀ : CentralizerBar c) = a := by
    rw [ha₀, MulEquiv.apply_symm_apply]
  have ha₀c : a₀ ∈ center ↥B := by
    rw [Subgroup.mem_center_iff]
    intro b₀
    apply φ.injective
    rw [map_mul, map_mul]
    apply Subtype.ext
    change (φ b₀ : CentralizerBar c) * (φ a₀ : CentralizerBar c) =
      (φ a₀ : CentralizerBar c) * (φ b₀ : CentralizerBar c)
    rw [haφ]
    exact (hcomm _ (φ b₀).2).symm
  rw [hcen] at ha₀c
  rcases eq_one_or_of_mem_zpowers_of_sq he2' he1' ha₀c with h | h
  · left
    rw [← haφ, h, map_one]
    rfl
  · right
    rw [← haφ, h, hφ]

omit [Finite G] in
theorem barSub_hasSL2Model_of_inj {c : G} {B : Subgroup G} (hBv : B ≤ centralizer ({c} : Set G))
    (hinj : Function.Injective ((proj c).comp (Subgroup.inclusion hBv)))
    {q : ℕ} {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = q)
    (e : SL(2, F₀) ≃* ↥B) : HasSL2Model ↥(S45.barSub c B) (fun r => r = q) := by
  obtain ⟨φ, -⟩ := exists_mulEquiv_barSub_of_inj hBv hinj
  exact ⟨F₀, inferInstance, inferInstance, hF₀,
    ⟨(e.trans φ).symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F₀).symm.symm⟩⟩

theorem isSubnormal_subgroupOf_of_two_step {X : Type*} [Group X] {J R T : Subgroup X} (hJR : J ≤ R)
    (h1 : ∀ r ∈ R, ∀ j ∈ J, r * j * r⁻¹ ∈ J)
    (h2 : ∀ t ∈ T, ∀ r ∈ R, t * r * t⁻¹ ∈ R) : (J.subgroupOf T).IsSubnormal := by
  have hRn : (R.subgroupOf T).Normal := by
    constructor
    intro n hn g
    have hn' : (n : X) ∈ R := hn
    show ((g * n * g⁻¹ : ↥T) : X) ∈ R
    exact h2 g g.2 n hn'
  refine Subgroup.IsSubnormal.step (J.subgroupOf T) (R.subgroupOf T)
    (fun x hx => hJR hx) hRn.isSubnormal ?_
  constructor
  intro n hn g
  have hn' : (((n : ↥(R.subgroupOf T)) : ↥T) : X) ∈ J := hn
  have hg' : (((g : ↥(R.subgroupOf T)) : ↥T) : X) ∈ R := g.2
  show ((((g * n * g⁻¹ : ↥(R.subgroupOf T)) : ↥T)) : X) ∈ J
  exact h1 _ hg' _ hn'

end CFSG.GH74.Generic.S1.Exo
