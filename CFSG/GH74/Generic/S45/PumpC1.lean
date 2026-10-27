module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GH74.Generic.Front.Transfer
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.GH74.Generic.S45

open CFSG CFSG.GH74 CFSG.GH74.Generic CFSG.GH74.L5U5 CFSG.ABGLocalTools Subgroup

section Bar

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def barSub (v : G) (J : Subgroup G) : Subgroup (CentralizerBar v) :=
  (J.subgroupOf (centralizer ({v} : Set G))).map (proj v)

omit [Finite G] in
theorem mem_barSub {v : G} {J : Subgroup G} {y : CentralizerBar v} :
    y ∈ barSub v J ↔ ∃ (g : G) (hg : g ∈ centralizer ({v} : Set G)), g ∈ J ∧ proj v ⟨g, hg⟩ = y := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, u.2, hu, rfl⟩
  · rintro ⟨g, hg, hgJ, rfl⟩
    exact ⟨⟨g, hg⟩, hgJ, rfl⟩

omit [Finite G] in
theorem proj_mem_barSub {v : G} {J : Subgroup G} {g : G} (hg : g ∈ centralizer ({v} : Set G))
    (hgJ : g ∈ J) : proj v ⟨g, hg⟩ ∈ barSub v J :=
  mem_barSub.2 ⟨g, hg, hgJ, rfl⟩

omit [Finite G] in
theorem barSub_mono {v : G} {J J' : Subgroup G} (h : J ≤ J') : barSub v J ≤ barSub v J' := by
  rintro y hy
  obtain ⟨g, hg, hgJ, rfl⟩ := mem_barSub.1 hy
  exact proj_mem_barSub hg (h hgJ)

theorem eq_one_of_proj_eq_one_of_sq {v g : G} (hg : g ∈ centralizer ({v} : Set G))
    (h1 : proj v ⟨g, hg⟩ = 1) (hsq : g * g = 1) : g = 1 := by
  have hodd := proj_odd v ⟨g, hg⟩ h1
  have h2 : orderOf (⟨g, hg⟩ : ↥(centralizer ({v} : Set G))) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact Subtype.ext hsq)
  have h3 : orderOf (⟨g, hg⟩ : ↥(centralizer ({v} : Set G))) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h | h
    · exact h
    · exact absurd (h ▸ hodd) (by decide)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h3)

theorem exists_noncomm_of_isQuasisimple {Q : Type*} [Group Q] (hQ : IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, hab⟩ := hQ.2.2
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcon a' b']

theorem barSub_mulEquiv {v : G} {W : Subgroup G} (hWH : W ≤ centralizer ({v} : Set G))
    (hWs : IsSimpleGroup ↥W) {e : G} (heW : e ∈ W) (he2 : e * e = 1) (he1 : e ≠ 1) :
    ∃ φ : ↥W ≃* ↥(barSub v W),
      ∀ w : ↥W, ((φ w : ↥(barSub v W)) : CentralizerBar v) = proj v ⟨(w : G), hWH w.2⟩ := by
  let φ₀ : ↥W →* CentralizerBar v := (proj v).comp (Subgroup.inclusion hWH)
  have hker : φ₀.ker = ⊥ := by
    have := hWs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ₀.ker with h | h
    · exact h
    · exfalso
      have h1 : φ₀ ⟨e, heW⟩ = 1 := by
        have : (⟨e, heW⟩ : ↥W) ∈ φ₀.ker := by rw [h]; trivial
        exact this
      exact he1 (eq_one_of_proj_eq_one_of_sq (hWH heW) h1 he2)
  have hinj : Function.Injective φ₀ := (MonoidHom.ker_eq_bot_iff _).1 hker
  have hrange : φ₀.range = barSub v W := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩
      exact proj_mem_barSub (hWH j.2) j.2
    · intro hy
      obtain ⟨g, hg, hgJ, rfl⟩ := mem_barSub.1 hy
      exact ⟨⟨g, hgJ⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange), fun w => rfl⟩

end Bar

end CFSG.GH74.Generic.S45
