module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieFam
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCoreX
public import CFSG.LocalAnalysis.ComponentClassification.Foote5OddLieCore

public section

namespace CFSG.ComponentClassification.Foote5.OddLieCore.Exc

open CFSG Subgroup CFSG.Blueprint CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {S : Type} [Group S]

@[expose] def OuterCoreAt (i : MulAut S) : Prop :=
  ∀ R : Subgroup (MulAut S), Odd (Nat.card R) → (∀ r ∈ R, r * i = i * r) →
    (∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) →
    ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ * r₂ = r₂ * r₁

@[expose] def OuterCoreTrivAt (i : MulAut S) : Prop :=
  ∀ R : Subgroup (MulAut S), Odd (Nat.card R) → (∀ r ∈ R, r * i = i * r) →
    (∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R) → ∀ r ∈ R, r = 1

theorem OuterCoreTrivAt.outerCoreAt {i : MulAut S} (h : OuterCoreTrivAt i) :
    OuterCoreAt i := by
  intro R hRodd hRi hRc r₁ h₁ r₂ h₂
  rw [h R hRodd hRi hRc r₁ h₁, h R hRodd hRi hRc r₂ h₂]

theorem congr_conj' {T : Type} [Group T] (e : S ≃* T) (s : S) :
    MulAut.congr e (MulAut.conj s) = MulAut.conj (e s) := by
  ext x
  simp [MulAut.congr_apply]

theorem outerCoreAt_of_congr {T : Type} [Group T] (e : S ≃* T) {i : MulAut S}
    (h : OuterCoreAt (MulAut.congr e i)) : OuterCoreAt i := by
  intro R hRodd hRi hRc r₁ h₁ r₂ h₂
  set φ : MulAut S →* MulAut T := (MulAut.congr e).toMonoidHom with hφ
  have hinj : Function.Injective φ := (MulAut.congr e).injective
  have hφapp : ∀ x, φ x = MulAut.congr e x := fun x => rfl
  set R' := R.map φ with hR'
  have hR'odd : Odd (Nat.card R') := by
    rw [hR', Subgroup.card_map_of_injective hinj]
    exact hRodd
  have hR'i : ∀ r ∈ R', r * MulAut.congr e i = MulAut.congr e i * r := by
    rintro _ ⟨r, hr, rfl⟩
    rw [hφapp, ← map_mul, ← map_mul, hRi r hr]
  have hR'c : ∀ s : T, MulAut.congr e i s = s → Odd (orderOf s) → ∀ r ∈ R',
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R' := by
    rintro s hs hso _ ⟨r, hr, rfl⟩
    have hs' : i (e.symm s) = e.symm s := by
      have := congrArg e.symm hs
      simpa [MulAut.congr_apply] using this
    have hso' : Odd (orderOf (e.symm s)) := by rwa [MulEquiv.orderOf_eq]
    refine ⟨_, hRc _ hs' hso' r hr, ?_⟩
    rw [hφapp, map_mul, map_mul, map_inv, congr_conj', MulEquiv.apply_symm_apply, hφapp]
  apply hinj
  have := h R' hR'odd hR'i hR'c (φ r₁) ⟨r₁, h₁, rfl⟩ (φ r₂) ⟨r₂, h₂, rfl⟩
  rw [map_mul, map_mul]
  exact this

theorem outerCoreAt_of_conj {i i₀ ψ : MulAut S} (hψ : ψ * i * ψ⁻¹ = i₀) (h : OuterCoreAt i₀) :
    OuterCoreAt i :=
  outerCoreAt_of_congr ψ (by
    rw [show MulAut.congr ψ i = ψ * i * ψ⁻¹ from rfl, hψ]
    exact h)

theorem oddLieCoreFamilyInput_of_outerCoreAt {τ : StatedLieTag}
    (h : ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
      ∀ n p f : ℕ, p.Prime → p ≠ 2 → StatedLieAdmissible τ n p f → LieModel S τ n p f →
      ∀ i : MulAut S, orderOf i = 2 → OuterCoreAt i) :
    OddLieCoreFamilyInput τ :=
  fun S _ _ _ hna n p f hp hp2 hadm hm _ i hi R hRodd hRi hRc =>
    h S hna n p f hp hp2 hadm hm i hi R hRodd hRi hRc

theorem sq_eq_one_of_orderOf {i : MulAut S} (hi : orderOf i = 2) : i ^ 2 = 1 := by
  rw [← hi]
  exact pow_orderOf_eq_one i

theorem center_eq_bot_of_simple' {J : Type*} [Group J] [IsSimpleGroup J]
    (hna : ∃ a b : J, a * b ≠ b * a) : center J = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center J) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ center J := h ▸ mem_top b
    exact hab (mem_center_iff.mp hb a)

theorem commutator_eq_top_of_simple' {J : Type*} [Group J] [IsSimpleGroup J]
    (hna : ∃ a b : J, a * b ≠ b * a) : _root_.commutator J = ⊤ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator J) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    apply hab
    have h1 : ⁅a, b⁆ ∈ _root_.commutator J := by
      rw [_root_.commutator_def]
      exact commutator_mem_commutator (mem_top a) (mem_top b)
    rw [h, mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  · exact h

theorem gw_isQuasisimple_of_simple {J : Type*} [Group J] [hs : IsSimpleGroup J]
    (hna : ∃ a b : J, a * b ≠ b * a) : GorensteinWalter.IsQuasisimple J := by
  refine ⟨hs.toNontrivial, commutator_eq_top_of_simple' hna, ?_⟩
  exact (MulEquiv.isSimpleGroup_congr ((QuotientGroup.quotientMulEquivOfEq
    (center_eq_bot_of_simple' hna)).trans QuotientGroup.quotientBot)).2 hs

theorem fix_of_fixed_simple [Finite S] (hZ : center S = ⊥) {i : MulAut S}
    {R : Subgroup (MulAut S)} (hRodd : Odd (Nat.card R)) (hRi : ∀ r ∈ R, r * i = i * r)
    (hRc : ∀ s : S, i s = s → Odd (orderOf s) → ∀ r ∈ R,
      MulAut.conj s * r * (MulAut.conj s)⁻¹ ∈ R)
    {J : Subgroup S} (hJ : ∀ s, i s = s ↔ s ∈ J) (hJs : IsSimpleGroup J)
    (hJna : ∃ a b : J, a * b ≠ b * a) {r : MulAut S} (hr : r ∈ R) {j : S} (hj : j ∈ J) :
    r j = j := by
  have hperf : _root_.commutator J = ⊤ := commutator_eq_top_of_simple' hJna
  have hJT : J ≤ oddFixed i := by
    refine (le_oddClosure_of_perfect le_rfl hperf).trans (closure_mono ?_)
    rintro g ⟨hgJ, hgo⟩
    exact ⟨(hJ g).2 hgJ, hgo⟩
  have hTJ : oddFixed i ≤ J := by
    rw [oddFixed, closure_le]
    rintro s ⟨hs, -⟩
    exact (hJ s).1 hs
  have hcomp : GorensteinWalter.IsComponentOf J (oddFixed i) := by
    refine ⟨hJT, ?_, gw_isQuasisimple_of_simple hJna⟩
    rw [(Subgroup.subgroupOf_eq_top).2 hTJ]
    exact Subgroup.IsSubnormal.top
  exact fix_of_isComponentOf hRi hRc hZ hRodd hr hcomp hj

theorem eq_one_of_odd_of_mem_zpowers {G : Type*} [Group G] {x y : G} (hx : x ^ 2 = 1)
    (hy : y ∈ zpowers x) (hyo : Odd (orderOf y)) : y = 1 := by
  have h1 : orderOf y ∣ 2 :=
    (orderOf_dvd_of_mem_zpowers hy).trans (orderOf_dvd_of_pow_eq_one hx)
  have h2 : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact h
    · rw [h] at hyo
      exact absurd hyo (by decide)
  exact orderOf_eq_one_iff.1 h2

theorem odd_orderOf_of_mem {G : Type*} [Group G] {R : Subgroup G}
    (hRodd : Odd (Nat.card R)) {r : G} (hr : r ∈ R) : Odd (orderOf r) := by
  have h := orderOf_dvd_natCard (⟨r, hr⟩ : R)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hRodd h

end CFSG.ComponentClassification.Foote5.OddLieCore.Exc
