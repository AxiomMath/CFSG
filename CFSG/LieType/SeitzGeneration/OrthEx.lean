module

public import CFSG.LieType.SeitzGeneration.OrthFamily
public import CFSG.LieType.SeitzGeneration.OrthThree

public section

namespace CFSG.LieType.SeitzGeneration.OrthBlk

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical
  CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal CFSG.Open
open CFSG.RankThree.Classical2 (orthDerived)

section Plane

theorem exists_plane_of_two {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {e₁ e₂ : G}
    (h12 : Commute e₁ e₂) (h₁ : e₁ ^ p = 1) (h₂ : e₂ ^ p = 1)
    (hi : ∀ i j : ℤ, e₁ ^ i * e₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) :
    ∃ E : Subgroup G, (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧
      Nat.card E = p ^ 2 ∧ ∀ x ∈ E, ∃ i j : ℤ, x = e₁ ^ i * e₂ ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  have hne1 : e₁ ≠ 1 := fun h => by
    have := (hi 1 0 (by rw [h]; simp)).1
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have hne2 : e₂ ≠ 1 := fun h => by
    have := (hi 0 1 (by rw [h]; simp)).2
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by exact_mod_cast this))
  have ho₁ : orderOf e₁ = p := orderOf_eq_prime h₁ hne1
  have ho₂ : orderOf e₂ = p := orderOf_eq_prime h₂ hne2
  have hc12 : ∀ (a : ↥(Subgroup.zpowers e₁)) (b : ↥(Subgroup.zpowers e₂)),
      Commute ((Subgroup.zpowers e₁).subtype a) ((Subgroup.zpowers e₂).subtype b) := by
    intro a b
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change Commute (a : G) (b : G)
    rw [← hk, ← hl]
    exact h12.zpow_zpow k l
  let f : ↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂) →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers e₁).subtype (Subgroup.zpowers e₂).subtype hc12
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨a, b⟩ hab
    have hab' : (a : G) * b = 1 := hab
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
    rw [← hk, ← hl] at hab'
    obtain ⟨hpk, hpl⟩ := hi k l hab'
    have ha : a = 1 := by
      apply Subtype.ext
      rw [← hk]
      obtain ⟨n, rfl⟩ := hpk
      rw [zpow_mul, zpow_natCast, h₁, one_zpow]
      rfl
    have hb : b = 1 := by
      apply Subtype.ext
      rw [← hl]
      obtain ⟨n, rfl⟩ := hpl
      rw [zpow_mul, zpow_natCast, h₂, one_zpow]
      rfl
    rw [ha, hb]
    rfl
  have hcard : Nat.card (↥(Subgroup.zpowers e₁) × ↥(Subgroup.zpowers e₂)) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, ho₁, ho₂]
    ring
  refine ⟨f.range, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext (mul_comm' x.1 y.1) (mul_comm' x.2 y.2)
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have hpow : ∀ (e : G) (he : e ^ p = 1) (a : ↥(Subgroup.zpowers e)), a ^ p = 1 := by
      intro e he a
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      apply Subtype.ext
      change (a : G) ^ p = 1
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
    have : x ^ p = 1 := Prod.ext (hpow e₁ h₁ x.1) (hpow e₂ h₂ x.2)
    rw [this, map_one]
  · exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm.trans hcard
  · rintro _ ⟨x, rfl⟩
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp x.1.2
    obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp x.2.2
    exact ⟨k, l, by
      change (x.1 : G) * x.2 = _
      rw [← hk, ← hl]⟩

end Plane

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

omit [Finite K] [FiniteDimensional K V] in
theorem OrthSep.disjoint {S T : Submodule K V} (hS : PolarNondegOn Q S) (h : OrthSep Q S T) :
    Disjoint S T := by
  rw [Submodule.disjoint_def]
  intro x hxS hxT
  exact hS x hxS fun y hy => by rw [polar_comm]; exact h y hy x hxT

omit [Finite K] [FiniteDimensional K V] in
theorem polarNondegOn_sup {S T : Submodule K V} (hS : PolarNondegOn Q S) (hT : PolarNondegOn Q T)
    (h : OrthSep Q S T) : PolarNondegOn Q (S ⊔ T) := by
  intro x hx hxy
  obtain ⟨s, hs, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  have hs0 : s = 0 := hS s hs fun y hy => by
    have := hxy y (Submodule.mem_sup_left hy)
    rwa [polar_add_left, h.symm t ht y hy, add_zero] at this
  have ht0 : t = 0 := hT t ht fun y hy => by
    have := hxy y (Submodule.mem_sup_right hy)
    rwa [polar_add_left, h s hs y hy, zero_add] at this
  rw [hs0, ht0, add_zero]

omit [Finite K] [FiniteDimensional K V] in
theorem le_perp_sup {S₁ S₂ S₃ : Submodule K V} (h13 : OrthSep Q S₁ S₃) (h23 : OrthSep Q S₂ S₃) :
    S₃ ≤ perp Q (S₁ ⊔ S₂) := fun x hx => by
  rw [mem_perp]
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hs
  rw [polar_add_left, h13 a ha x hx, h23 b hb x hx, add_zero]

omit [Finite K] in
theorem exists_good_pair {S₀ S₁ S₂ : Submodule K V} (hdim : 7 ≤ finrank K V)
    (h₀ : PolarNondegOn Q S₀) (h₁ : PolarNondegOn Q S₁) (h₂ : PolarNondegOn Q S₂)
    (h01 : OrthSep Q S₀ S₁) (h02 : OrthSep Q S₀ S₂) (h12 : OrthSep Q S₁ S₂) :
    3 ≤ finrank K (perp Q (S₀ ⊔ S₁)) ∨ 3 ≤ finrank K (perp Q (S₀ ⊔ S₂)) ∨
      3 ≤ finrank K (perp Q (S₁ ⊔ S₂)) := by
  have e01 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp (polarNondegOn_sup h₀ h₁ h01))
  have e02 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp (polarNondegOn_sup h₀ h₂ h02))
  have e12 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp (polarNondegOn_sup h₁ h₂ h12))
  rw [finrank_sup_of_disjoint (h01.disjoint h₀)] at e01
  rw [finrank_sup_of_disjoint (h02.disjoint h₀)] at e02
  rw [finrank_sup_of_disjoint (h12.disjoint h₁)] at e12
  have hle : finrank K S₂ ≤ finrank K (perp Q (S₀ ⊔ S₁)) :=
    Submodule.finrank_mono (le_perp_sup h02 h12)
  omega

omit [Finite K] [FiniteDimensional K V] in
theorem zpow_apply_of_fixed {g : V ≃ₗ[K] V} {e : V} (h : g e = e) (i : ℤ) : (g ^ i) e = e := by
  have := (MulAction.stabilizer (V ≃ₗ[K] V) e).zpow_mem (MulAction.mem_stabilizer_iff.mpr h) i
  exact MulAction.mem_stabilizer_iff.mp this

theorem exists_plane_of_blocks (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hp : p.Prime) (hp2 : p ≠ 2)
    {S₁ S₂ : Submodule K V} {g₁ g₂ : V ≃ₗ[K] V} (h₁ : PolarNondegOn Q S₁)
    (b₁ : IsBlock Q p S₁ g₁) (b₂ : IsBlock Q p S₂ g₂) (hsep : OrthSep Q S₁ S₂)
    {e : V} (he₁ : ∀ s ∈ S₁, polar Q s e = 0) (he₂ : ∀ s ∈ S₂, polar Q s e = 0) :
    ∃ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧
      Nat.card E = p ^ 2 ∧ e ∈ planeFixSpace E := by
  have : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hg₁ : g₁ ∈ orthDerived Q := mem_orthDerived_of_odd_pow hQ hT hodd b₁.mem b₁.pow
  have hg₂ : g₂ ∈ orthDerived Q := mem_orthDerived_of_odd_pow hQ hT hodd b₂.mem b₂.pow
  have hO₁ := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup b₁.mem
  have hO₂ := TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup b₂.mem
  have F1 : ∀ u ∈ S₁, g₂ u = u := fun u hu => b₂.fix u fun s hs => hsep.symm s hs u hu
  have F2 : ∀ u ∈ S₂, g₁ u = u := fun u hu => b₁.fix u fun s hs => hsep s hs u hu
  have hcomm : g₁ * g₂ = g₂ * g₁ := by
    refine LinearEquiv.ext fun v => ?_
    obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp ((isCompl_perp h₁).sup_eq_top ▸
      Submodule.mem_top (x := v))
    have hw' := mem_perp.mp hw
    have h1 : g₁ w = w := b₁.fix w hw'
    have h2 : g₁ (g₂ w) = g₂ w := b₁.fix _ fun s hs => by
      have := hO₂ s w
      rw [F1 s hs] at this
      rw [this]
      exact hw' s hs
    have h3 : g₂ (g₁ u) = g₁ u := b₂.fix _ fun s hs => by
      have := hO₁ s u
      rw [F2 s hs] at this
      rw [this]
      exact hsep.symm s hs u hu
    have h4 : g₂ u = u := F1 u hu
    simp only [LinearEquiv.mul_apply, map_add, h1, h2, h3, h4]
  have hi : ∀ i j : ℤ, (⟨g₁, hg₁⟩ : orthDerived Q) ^ i * (⟨g₂, hg₂⟩ : orthDerived Q) ^ j = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j h
    have h' : g₁ ^ i * g₂ ^ j = 1 := by
      have := congrArg Subtype.val h
      simpa using this
    have hS₁ : g₂ ^ j ∈ stabPW S₁ := (stabPW S₁).zpow_mem (fun u hu => F1 u hu) j
    have hP : g₁ ^ i ∈ stabPW (perp Q S₁) :=
      (stabPW (perp Q S₁)).zpow_mem (fun w hw => b₁.fix w (mem_perp.mp hw)) i
    have hP' : g₁ ^ i ∈ stabPW S₁ := fun u hu => by
      have := congrArg (fun f : V ≃ₗ[K] V => f u) h'
      simp only [LinearEquiv.mul_apply, hS₁ u hu] at this
      exact this
    have h1 : g₁ ^ i = 1 := by
      have : g₁ ^ i ∈ stabPW (S₁ ⊔ perp Q S₁) := by rw [stabPW_sup]; exact ⟨hP', hP⟩
      rw [(isCompl_perp h₁).sup_eq_top, stabPW_top] at this
      exact Subgroup.mem_bot.mp this
    have h2 : g₂ ^ j = 1 := by rw [h1, one_mul] at h'; exact h'
    have ho₁ : orderOf g₁ = p := orderOf_eq_prime b₁.pow b₁.ne
    have ho₂ : orderOf g₂ = p := orderOf_eq_prime b₂.pow b₂.ne
    refine ⟨?_, ?_⟩
    · have := orderOf_dvd_iff_zpow_eq_one.mpr h1
      rwa [ho₁] at this
    · have := orderOf_dvd_iff_zpow_eq_one.mpr h2
      rwa [ho₂] at this
  obtain ⟨E, hEc, hEp, hEcard, hEform⟩ := exists_plane_of_two hp
    (e₁ := (⟨g₁, hg₁⟩ : orthDerived Q)) (e₂ := (⟨g₂, hg₂⟩ : orthDerived Q))
    (Subtype.ext hcomm) (Subtype.ext b₁.pow) (Subtype.ext b₂.pow) hi
  refine ⟨E, hEc, hEp, hEcard, ?_⟩
  rw [planeFixSpace, mem_fixSpace]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨i, j, rfl⟩ := hEform x hx
  have hfe₁ : g₁ e = e := b₁.fix e he₁
  have hfe₂ : g₂ e = e := b₂.fix e he₂
  change ((g₁ ^ i * g₂ ^ j : V ≃ₗ[K] V)) e = e
  rw [LinearEquiv.mul_apply, zpow_apply_of_fixed hfe₂ j, zpow_apply_of_fixed hfe₁ i]

end Geometry

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem natCast_ne_zero_of_ne_ringChar {p : ℕ} (hp : p.Prime) (h : p ≠ ringChar K) :
    (p : K) ≠ 0 := by
  intro h0
  have hℓ : (ringChar K).Prime := by
    have := Fintype.ofFinite K
    exact CharP.char_is_prime K _
  have : ringChar K ∣ p := (CharP.cast_eq_zero_iff K (ringChar K) p).mp h0
  exact h ((Nat.prime_dvd_prime_iff_eq hℓ hp).mp this).symm

@[expose] def OrthHighGen (Q : QuadraticForm K V) (p : ℕ) : Prop :=
  ¬ RankLE2 p (orthDerived Q) → ∃ E : Subgroup (orthDerived Q),
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
      Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

theorem orthHighGen (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) : OrthHighGen Q p := by
  intro hrank
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_ne_ringChar hp hpl
  have key : ∀ (S₁ S₂ : Submodule K V) (g₁ g₂ : V ≃ₗ[K] V), PolarNondegOn Q S₁ →
      PolarNondegOn Q S₂ → IsBlock Q p S₁ g₁ → IsBlock Q p S₂ g₂ → OrthSep Q S₁ S₂ →
      3 ≤ finrank K (perp Q (S₁ ⊔ S₂)) → ∃ E : Subgroup (orthDerived Q),
        (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x ^ p = 1) ∧ Nat.card E = p ^ 2 ∧
          Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤ := by
    intro S₁ S₂ g₁ g₂ h₁ h₂ b₁ b₂ hsep h3
    have hreg : PolarNondegOn Q (perp Q (S₁ ⊔ S₂)) :=
      polarNondegOn_perp hQ (polarNondegOn_sup h₁ h₂ hsep)
    obtain ⟨e, he, he0, heQ⟩ := exists_singular_of_three_le_general hreg h3
    have he' := mem_perp.mp he
    obtain ⟨E, hEc, hEp, hEcard, hEe⟩ := exists_plane_of_blocks hQ hT hp hp2 h₁ b₁ b₂ hsep
      (fun s hs => he' s (Submodule.mem_sup_left hs))
      (fun s hs => he' s (Submodule.mem_sup_right hs))
    refine ⟨E, hEc, hEp, hEcard, ?_⟩
    have : Nontrivial V := nontrivial_of_three_singular hT
    exact closure_eq_top_of_singular_fixed hQ hT hp hp2 hpl E hEc hEp hEcard hEe he0 heQ
  obtain ⟨F₀, hF₀, hcard⟩ : ∃ F₀ : Subgroup (orthDerived Q), IsElemAbelian p F₀ ∧
      p ^ 2 < Nat.card F₀ := by
    by_contra h
    push Not at h
    exact hrank fun F hF => h F hF
  let F : Subgroup (V ≃ₗ[K] V) := F₀.map (orthDerived Q).subtype
  have hFcard : Nat.card F = Nat.card F₀ :=
    Subgroup.card_map_of_injective (orthDerived Q).subtype_injective
  have hcommF₀ : ∀ x ∈ F₀, ∀ y ∈ F₀, x * y = y * x := by
    have : IsMulCommutative F₀ := hF₀.1
    exact fun x hx y hy =>
      congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : F₀) ⟨y, hy⟩)
  have hF : ElemAbOrth Q p F := by
    refine ⟨?_, ?_, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact orthDerived_mem_orthogonalGroup
    · rintro _ ⟨x, hx, rfl⟩
      have := hF₀.2 x hx
      exact congrArg Subtype.val this
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hcommF₀ x hx y hy)
  obtain ⟨L, hL, hlen⟩ := exists_blockFamily_top hQ hp hpK hF
  have hL3 : 3 ≤ L.length := by
    by_contra h
    push Not at h
    have : p ^ L.length ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (by omega)
    omega
  rcases L with _ | ⟨x₀, _ | ⟨x₁, _ | ⟨x₂, rest⟩⟩⟩
  · simp at hL3
  · simp at hL3
  · simp at hL3
  · have hpw := hL.orth
    rw [List.pairwise_cons] at hpw
    obtain ⟨hall, hpw'⟩ := hpw
    rw [List.pairwise_cons] at hpw'
    have h01 := hall x₁ (by simp)
    have h02 := hall x₂ (by simp)
    have h12 := hpw'.1 x₂ (by simp)
    have r0 := hL.reg x₀ (by simp)
    have r1 := hL.reg x₁ (by simp)
    have r2 := hL.reg x₂ (by simp)
    have b0 := hL.block x₀ (by simp)
    have b1 := hL.block x₁ (by simp)
    have b2 := hL.block x₂ (by simp)
    rcases exists_good_pair hdim r0 r1 r2 h01 h02 h12 with h | h | h
    · exact key _ _ _ _ r0 r1 b0 b1 h01 h
    · exact key _ _ _ _ r0 r2 b0 b2 h02 h
    · exact key _ _ _ _ r1 r2 b1 b2 h12 h

end Model

end CFSG.LieType.SeitzGeneration.OrthBlk
