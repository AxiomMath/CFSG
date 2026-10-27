module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims136b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136c

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.MovingAround
open scoped commutatorElement

section Diag

variable {Z Y : Type*} [Group Z] [Group Y]

theorem comm_eq_map (E : Z →* Y) (τ : Y) (ψ : Z →* Z) (hτ : ∀ u, τ * E u * τ⁻¹ = E (ψ u)) (u : Z) :
    ⁅E u, τ⁆ = E (u * (ψ u)⁻¹) := by
  have h1 : τ * (E u)⁻¹ * τ⁻¹ = E (ψ u⁻¹) := by rw [← hτ, map_inv]
  rw [commutatorElement_def, map_mul, ← map_inv ψ, ← h1]
  group

theorem comm_comm_eq_map (E : Z →* Y) (τ : Y) (ψ : Z →* Z) (hτ : ∀ u, τ * E u * τ⁻¹ = E (ψ u))
    (u : Z) : ⁅⁅E u, τ⁆, τ⁆ = E (u * (ψ u)⁻¹ * (ψ (u * (ψ u)⁻¹))⁻¹) := by
  rw [comm_eq_map E τ ψ hτ u, comm_eq_map E τ ψ hτ]

@[expose] def diagFun (e : Z →* Y) (c : Y →* Y) (u : Z) : Y := e u * c (e u) * c (c (e u))

section DiagFacts

variable (e : Z →* Y) (c : Y →* Y) (hc3 : ∀ y, c (c (c y)) = y)
  (hcomm : ∀ u v, e u * c (e v) = c (e v) * e u)
include hc3 hcomm

theorem diag_comm13 (u v : Z) : e u * c (c (e v)) = c (c (e v)) * e u := by
  have h := congrArg (fun y => c (c y)) (hcomm v u)
  simp only [map_mul, hc3] at h
  exact h.symm

omit hc3 in
theorem diag_comm23 (u v : Z) : c (e u) * c (c (e v)) = c (c (e v)) * c (e u) := by
  have h := congrArg c (hcomm u v)
  simp only [map_mul] at h
  exact h

theorem diagFun_mul (u v : Z) : diagFun e c (u * v) = diagFun e c u * diagFun e c v := by
  have h12 := hcomm v u
  have h13 := diag_comm13 e c hc3 hcomm v u
  have h23 := diag_comm23 e c hcomm v u
  simp only [diagFun, map_mul]
  calc e u * e v * (c (e u) * c (e v)) * (c (c (e u)) * c (c (e v)))
      = e u * (e v * c (e u)) * c (e v) * c (c (e u)) * c (c (e v)) := by simp only [mul_assoc]
    _ = e u * (c (e u) * e v) * c (e v) * c (c (e u)) * c (c (e v)) := by rw [h12]
    _ = e u * c (e u) * e v * (c (e v) * c (c (e u))) * c (c (e v)) := by simp only [mul_assoc]
    _ = e u * c (e u) * e v * (c (c (e u)) * c (e v)) * c (c (e v)) := by rw [h23]
    _ = e u * c (e u) * (e v * c (c (e u))) * c (e v) * c (c (e v)) := by simp only [mul_assoc]
    _ = e u * c (e u) * (c (c (e u)) * e v) * c (e v) * c (c (e v)) := by rw [h13]
    _ = e u * c (e u) * c (c (e u)) * (e v * c (e v) * c (c (e v))) := by simp only [mul_assoc]

@[expose] noncomputable def diagHom : Z →* Y :=
  MonoidHom.mk' (diagFun e c) (diagFun_mul e c hc3 hcomm)

theorem diagHom_apply (u : Z) : diagHom e c hc3 hcomm u = e u * c (e u) * c (c (e u)) := rfl

theorem c_diagHom (u : Z) : c (diagHom e c hc3 hcomm u) = diagHom e c hc3 hcomm u := by
  have h12 := hcomm u u
  have h13 := diag_comm13 e c hc3 hcomm u u
  rw [diagHom_apply, map_mul, map_mul, hc3]
  calc c (e u) * c (c (e u)) * e u = c (e u) * (c (c (e u)) * e u) := by rw [mul_assoc]
    _ = c (e u) * (e u * c (c (e u))) := by rw [h13]
    _ = (c (e u) * e u) * c (c (e u)) := by rw [mul_assoc]
    _ = (e u * c (e u)) * c (c (e u)) := by rw [h12]

theorem tau_diagHom (τ : Y →* Y) (hτc : ∀ y, τ (c y) = c (τ y)) {u u' : Z} (hu : τ (e u) = e u') :
    τ (diagHom e c hc3 hcomm u) = diagHom e c hc3 hcomm u' := by
  rw [diagHom_apply, diagHom_apply, map_mul, map_mul, hτc, hτc, hτc, hu]

theorem comm_of_diagHom_eq_one {u : Z} (h1 : diagHom e c hc3 hcomm u = 1) (v : Z) :
    e u * e v = e v * e u := by
  have h12 : Commute (e v) (c (e u)) := hcomm v u
  have h13 : Commute (e v) (c (c (e u))) := diag_comm13 e c hc3 hcomm v u
  rw [diagHom_apply] at h1
  have he : e u = (c (c (e u)))⁻¹ * (c (e u))⁻¹ := by
    have h2 : e u * c (e u) = (c (c (e u)))⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [← h2]
    group
  have hc : Commute (e v) ((c (c (e u)))⁻¹ * (c (e u))⁻¹) := h13.inv_right.mul_right h12.inv_right
  rw [he]
  exact hc.eq.symm

end DiagFacts

end Diag

section Perm

open Equiv

variable {α : Type} [Fintype α] [DecidableEq α]

theorem perm_inv_apply_self (f : Perm α) (x : α) : f⁻¹ (f x) = x := Perm.inv_eq_iff_eq.2 rfl

theorem zpow_apply_eq_self {P : Subgroup (Perm α)} {ω : α} {π₁ : Perm α} (hπ3 : π₁ ^ 3 = 1)
    (hπP : ∀ g ∈ P, π₁ * g = g * π₁) (hπω : π₁ ω = ω ∨ ∀ g ∈ P, π₁ ω ≠ g ω) (j : ℤ)
    {g : Perm α} (hg : g ∈ P) (hj : (π₁ ^ j) ω = g ω) : (π₁ ^ j) ω = ω := by
  rcases hπω with h | h
  · have hst : π₁ ∈ MulAction.stabilizer (Perm α) ω := h
    exact (MulAction.stabilizer (Perm α) ω).zpow_mem hst j
  · have hmod : π₁ ^ j = π₁ ^ (j % 3) := by
      have := zpow_eq_zpow_emod' j hπ3
      rwa [Nat.cast_ofNat] at this
    rw [hmod] at hj ⊢
    have h0 : 0 ≤ j % 3 := Int.emod_nonneg _ (by norm_num)
    have h3 : j % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
    rcases (show j % 3 = 0 ∨ j % 3 = 1 ∨ j % 3 = 2 by omega) with he | he | he
    · rw [he, zpow_zero]
      rfl
    · rw [he, zpow_one] at hj
      exact absurd hj (h g hg)
    · exfalso
      rw [he, zpow_two, Perm.mul_apply] at hj
      apply h g⁻¹ (P.inv_mem hg)
      have h3' : π₁ (π₁ (π₁ ω)) = ω := by
        have := congrArg (fun π : Perm α => π ω) hπ3
        simpa [pow_three, Perm.mul_apply] using this
      have e1 : g (π₁ ω) = ω := by
        rw [← Perm.mul_apply, ← hπP g hg, Perm.mul_apply, ← hj, h3']
      calc π₁ ω = g⁻¹ (g (π₁ ω)) := (perm_inv_apply_self g (π₁ ω)).symm
        _ = g⁻¹ ω := by rw [e1]

theorem perm_core {P : Subgroup (Perm α)} (hPab : ∀ g ∈ P, ∀ h ∈ P, g * h = h * g) {ω : α}
    (hreg : ∀ g ∈ P, g ω = ω → g = 1) {β γ π₁ : Perm α} (hβ : β ∈ P) (hγ : γ ∈ P)
    (hβγ : β ∉ Subgroup.zpowers γ) (hγ1 : γ ≠ 1) (hβ3 : β ^ 3 = 1) (hγ3 : γ ^ 3 = 1)
    (hπ3 : π₁ ^ 3 = 1) (hπP : ∀ g ∈ P, π₁ * g = g * π₁)
    (hπω : π₁ ω = ω ∨ ∀ g ∈ P, π₁ ω ≠ g ω) :
    (∀ h ∈ Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁,
        ∀ h' ∈ Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁, h * h' = h' * h) ∧
      (∀ h ∈ Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁, h ^ 3 = 1) ∧
      (∀ h ∈ Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁, β * h = h * β) ∧
      ∃ x ∈ Claims136b.orbSubH (Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁), ⁅⁅x, β⁆, β⁆ ≠ 1 := by
  set H := Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁ with hH
  have hγπ : Commute γ π₁ := (hπP γ hγ).symm
  have hcomm : ∀ i j : ℤ, Commute (γ ^ i) (π₁ ^ j) := fun i j => hγπ.zpow_zpow i j
  have hc : Subgroup.zpowers γ ≤
      Subgroup.centralizer ((Subgroup.zpowers π₁ : Subgroup (Perm α)) : Set (Perm α)) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact ((hcomm i j).eq).symm
  have hdec : ∀ h ∈ H, ∃ i j : ℤ, h = γ ^ i * π₁ ^ j := by
    intro h hh
    obtain ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, hu⟩ := exists_mul_of_mem_sup hc hh
    exact ⟨i, j, hu⟩
  have hβγc : Commute β γ := hPab β hβ γ hγ
  have hβπ : Commute β π₁ := (hπP β hβ).symm
  have hHab : ∀ h ∈ H, ∀ h' ∈ H, h * h' = h' * h := by
    intro h hh h' hh'
    obtain ⟨i, j, rfl⟩ := hdec h hh
    obtain ⟨k, l, rfl⟩ := hdec h' hh'
    exact (Commute.mul_right (Commute.mul_left (Commute.zpow_zpow_self γ i k) (hcomm k j).symm)
      (Commute.mul_left (hcomm i l) (Commute.zpow_zpow_self π₁ j l))).eq
  refine ⟨hHab, ?_, ?_, ?_⟩
  · intro h hh
    obtain ⟨i, j, rfl⟩ := hdec h hh
    rw [(hcomm i j).mul_pow]
    have h1 : (γ ^ i) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hγ3, one_zpow]
    have h2 : (π₁ ^ j) ^ 3 = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hπ3, one_zpow]
    rw [h1, h2, one_mul]
  · intro h hh
    obtain ⟨i, j, rfl⟩ := hdec h hh
    exact ((hβγc.zpow_right i).mul_right (hβπ.zpow_right j)).eq
  · have hγH : γ ∈ H := Subgroup.mem_sup_left (Subgroup.mem_zpowers γ)
    have hγω : γ ω ≠ ω := fun h0 => hγ1 (hreg γ hγ h0)
    have hγi : ∀ i : ℤ, γ ^ i ∈ P := fun i => P.zpow_mem hγ i
    have hβω : ∀ h ∈ H, h ω ≠ β ω := by
      intro h hh hhω
      obtain ⟨i, j, rfl⟩ := hdec h hh
      rw [Perm.mul_apply] at hhω
      have hgP : (γ ^ i)⁻¹ * β ∈ P := P.mul_mem (P.inv_mem (hγi i)) hβ
      have hj : (π₁ ^ j) ω = ((γ ^ i)⁻¹ * β) ω := by
        rw [Perm.mul_apply, ← hhω, perm_inv_apply_self]
      have hj' := zpow_apply_eq_self hπ3 hπP hπω j hgP hj
      rw [hj'] at hj
      have h1 := hreg _ hgP hj.symm
      exact hβγ (Subgroup.mem_zpowers_iff.2 ⟨i, inv_mul_eq_one.1 h1⟩)
    have hβω' : ∀ h ∈ H, h ω ≠ β⁻¹ ω := by
      intro h hh hhω
      obtain ⟨i, j, rfl⟩ := hdec h hh
      rw [Perm.mul_apply] at hhω
      have hgP : (γ ^ i)⁻¹ * β⁻¹ ∈ P := P.mul_mem (P.inv_mem (hγi i)) (P.inv_mem hβ)
      have hj : (π₁ ^ j) ω = ((γ ^ i)⁻¹ * β⁻¹) ω := by
        rw [Perm.mul_apply, ← hhω, perm_inv_apply_self]
      have hj' := zpow_apply_eq_self hπ3 hπP hπω j hgP hj
      rw [hj'] at hj
      have h1 := inv_mul_eq_one.1 (hreg _ hgP hj.symm)
      exact hβγ (Subgroup.mem_zpowers_iff.2 ⟨-i, by rw [zpow_neg, h1, inv_inv]⟩)
    exact Claims136b.exists_mem_orbSubH_comm_ne hHab hγH hβ3 hγω hβω hβω'

end Perm

section Bar

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

theorem card_plane {B : Subgroup G} (hB : IsElemAbelian 3 B) {x y : G} (hxB : x ∈ B) (hyB : y ∈ B)
    (hx1 : x ≠ 1) (hyx : y ∉ Subgroup.zpowers x) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 ↥B := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hB.2 g.1 g.2)⟩
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ B :=
    sup_le ((Subgroup.zpowers_le).2 hxB) ((Subgroup.zpowers_le).2 hyB)
  have hxy : x * y = y * x := congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hxB⟩ ⟨y, hyB⟩)
  have h9 := Claims136b.card_sup_zpowers_le hxy (hB.2 x hxB) (hB.2 y hyB)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (hBp.to_le hle)
  have hlt : Subgroup.zpowers x < Subgroup.zpowers x ⊔ Subgroup.zpowers y :=
    lt_of_le_of_ne le_sup_left fun h => hyx (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have h1 := card_lt_of_lt' hlt
  have hx3 : Nat.card ↥(Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hB.2 x hxB) hx1
  rw [hk] at h9 h1 ⊢
  rw [hx3] at h1
  have hk2 : k ≤ 2 := by
    by_contra h3
    push Not at h3
    have : 3 ^ 3 ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h3
    omega
  interval_cases k <;> simp_all

@[expose] noncomputable def embBar {C K : Subgroup G} (hK : GLAPComponent 3 C K) :
    barOf 3 K →* (↥C ⧸ GLAPPrimeCore 3 ↥C) :=
  (barX 3 C K).subtype.comp (quotEquivBarX Nat.prime_three hK.1 hK.2.1).toMonoidHom

theorem embBar_injective {C K : Subgroup G} (hK : GLAPComponent 3 C K) :
    Function.Injective (embBar hK) :=
  (barX 3 C K).subtype_injective.comp (quotEquivBarX Nat.prime_three hK.1 hK.2.1).injective

theorem embBar_mk {C K : Subgroup G} (hK : GLAPComponent 3 C K) (t : ↥K) :
    embBar hK (QuotientGroup.mk t) = QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨t, hK.1 t.2⟩ := rfl

theorem embBar_mem {C K : Subgroup G} (hK : GLAPComponent 3 C K) (u : barOf 3 K) :
    embBar hK u ∈ barX 3 C K :=
  (quotEquivBarX Nat.prime_three hK.1 hK.2.1 u).2

theorem embBar_barAut {C K : Subgroup G} (hK : GLAPComponent 3 C K) {g : G} (hgC : g ∈ C)
    (hgK : g ∈ Subgroup.normalizer (K : Set G)) (u : barOf 3 K) :
    QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨g, hgC⟩ * embBar hK u *
        (QuotientGroup.mk' (GLAPPrimeCore 3 ↥C) ⟨g, hgC⟩)⁻¹ =
      embBar hK (barAut 3 K ⟨g, hgK⟩ u) := by
  induction u using QuotientGroup.induction_on with
  | H t =>
    rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, embBar_mk, embBar_mk, ← map_inv,
      ← map_mul, ← map_mul]
    rfl

end Bar

section Final

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)

theorem final_step (hP95 : Prop95) (h111 : Prop111Statement) (h121 : Prop121_of_cexStatement)
    (hcomp : Sec13_compStatement) (h133 : Lemma133Statement)
    {m : ℕ} {B M E A D T L : Subgroup G} (h : Cex134 G m 3 B M E A D T L)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    {c₀ a₁ : G} (hc₀B : c₀ ∈ B) (ha₁B : a₁ ∈ B) (hc₀C : c₀ ∈ Cg d) (ha₁C : a₁ ∈ Cg d)
    (hc₀1 : c₀ ≠ 1) (ha₁c₀ : a₁ ∉ Subgroup.zpowers c₀)
    {b : G} (hbB : b ∈ B) (hbL : b ∈ L) (hbC : b ∈ Cg d)
    {Z : Type} [Group Z] (Eh : Z →* (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d))) {U : Subgroup Z}
    (hUel : IsElemAbelian 3 U) (ψ : Z →* Z) (hψU : ∀ u ∈ U, ψ u ∈ U)
    (hEb : ∀ u, QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b, hbC⟩ * Eh u *
      (QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨b, hbC⟩)⁻¹ = Eh (ψ u))
    (hEc : ∀ u ∈ U, QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨c₀, hc₀C⟩ * Eh u =
      Eh u * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨c₀, hc₀C⟩)
    (hEa : ∀ u ∈ U, QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨a₁, ha₁C⟩ * Eh u =
      Eh u * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨a₁, ha₁C⟩)
    {x : Z} (hx : x ∈ U) (hne : Eh (x * (ψ x)⁻¹ * (ψ (x * (ψ x)⁻¹))⁻¹) ≠ 1) : False := by
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set mk := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) with hmk
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hBM : B ≤ M := h.uniq.le
  set A₀ := Subgroup.zpowers c₀ ⊔ Subgroup.zpowers a₁ with hA₀
  have hA₀B : A₀ ≤ B := sup_le ((Subgroup.zpowers_le).2 hc₀B) ((Subgroup.zpowers_le).2 ha₁B)
  have hA₀X : A₀ ≤ Cg d := sup_le ((Subgroup.zpowers_le).2 hc₀C) ((Subgroup.zpowers_le).2 ha₁C)
  have hA₀c : Nat.card ↥A₀ = 9 := card_plane hBel hc₀B ha₁B hc₀1 ha₁c₀
  have hA₀el : IsElemAbelian 3 A₀ := CFSG.Open.IsElemAbelian.mono hBel hA₀B
  have hA₀p : IsPGroup 3 ↥A₀ := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hA₀el.2 g.1 g.2)⟩
  have hA₀rk : 2 ≤ CFSG.Open.pRank 3 A₀ :=
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl hA₀el (by rw [hA₀c]; norm_num)
  have hNA₀ : Subgroup.normalizer (A₀ : Set G) ≤ M := by
    have h1 : Subgroup.normalizer (A₀ : Set G) ≤ GLBCore 3 2 B := le_sSup ⟨A₀, hA₀B, hA₀rk, rfl⟩
    exact h1.trans h.uniq.clause_d
  have hCA₀ : Subgroup.centralizer (A₀ : Set G) ≤ M :=
    (Subgroup.centralizer_le_normalizer _).trans hNA₀
  have hXqM : GLAPPrimeCoreOf 3 (Cg d) ≤ M := h111 h.toSec11 hdA hd1
  set Ut : Subgroup (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) := U.map Eh with hUt
  have hUtel : IsElemAbelian 3 Ut := CFSG.SectionRank.isElemAbelian_map hUel Eh
  set bb := mk ⟨b, hbC⟩ with hbb
  have hb3 : b ^ 3 = 1 := hBel.2 b hbB
  have hbb3 : bb ^ 3 = 1 := by
    rw [hbb, ← map_pow]
    have : (⟨b, hbC⟩ : ↥(Cg d)) ^ 3 = 1 := Subtype.ext (by simpa using hb3)
    rw [this, map_one]
  have hUtb : ∀ k ∈ Ut, bb * k * bb⁻¹ ∈ Ut := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hEb u]
    exact ⟨ψ u, hψU u hu, rfl⟩
  have hUtbi : ∀ k ∈ Ut, bb⁻¹ * k * bb ∈ Ut := by
    intro k hk
    have h3 : bb * bb * bb = 1 := by rw [mul_assoc, ← pow_three]; exact hbb3
    have e1 : bb * bb = bb⁻¹ := eq_inv_of_mul_eq_one_left h3
    have e2 : bb * (bb * k * bb⁻¹) * bb⁻¹ = bb⁻¹ * k * bb := by
      calc bb * (bb * k * bb⁻¹) * bb⁻¹ = (bb * bb) * k * (bb * bb)⁻¹ := by group
        _ = bb⁻¹ * k * bb := by rw [e1, inv_inv]
    rw [← e2]
    exact hUtb _ (hUtb k hk)
  set Q : Subgroup G :=
    ((Subgroup.centralizer (Ut : Set (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)))).comap mk).map (Cg d).subtype with hQ
  have hgenQ : ∀ (g : G) (hg : g ∈ Cg d), (∀ u ∈ U, mk ⟨g, hg⟩ * Eh u = Eh u * mk ⟨g, hg⟩) → g ∈ Q := by
    intro g hg hgU
    refine ⟨⟨g, hg⟩, ?_, rfl⟩
    show mk ⟨g, hg⟩ ∈ Subgroup.centralizer _
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    exact (hgU u hu).symm
  have hA₀Q : A₀ ≤ Q := sup_le ((Subgroup.zpowers_le).2 (hgenQ c₀ hc₀C hEc))
    ((Subgroup.zpowers_le).2 (hgenQ a₁ ha₁C hEa))
  have hUtA : ∀ a (ha : a ∈ A₀), ∀ k ∈ Ut, mk ⟨a, hA₀X ha⟩ * k = k * mk ⟨a, hA₀X ha⟩ := by
    intro a ha k hk
    obtain ⟨a', ha', rfl⟩ := hA₀Q ha
    exact ((Subgroup.mem_centralizer_iff.1 ha') k hk).symm
  set Ut' : Subgroup G := (Ut.comap mk).map (Cg d).subtype with hUt'
  have hmemUt' : ∀ z, z ∈ Ut' ↔ ∃ hz : z ∈ Cg d, mk ⟨z, hz⟩ ∈ Ut := by
    intro z
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k.2, hk⟩
    · rintro ⟨hz, hz'⟩
      exact ⟨⟨z, hz⟩, hz', rfl⟩
  have hUt'X : Ut' ≤ Cg d := Subgroup.map_subtype_le _
  have hAN : A₀ ≤ Subgroup.normalizer (Cg d : Set G) := fun a ha => Subgroup.le_normalizer (hA₀X ha)
  have hUt'M : Ut' ≤ M := by
    intro z hz
    obtain ⟨hzX, hzU⟩ := (hmemUt' z).1 hz
    obtain ⟨v, hvO, hv⟩ := Claims136b.exists_lift_centralizer hA₀p hAN ⟨z, hzX⟩ (fun a ha => by
      rw [Claims136.barAut_eq_conj (hA₀X ha) (hAN ha), MulAut.conj_apply]
      show mk ⟨a, hA₀X ha⟩ * mk ⟨z, hzX⟩ * (mk ⟨a, hA₀X ha⟩)⁻¹ = mk ⟨z, hzX⟩
      rw [hUtA a ha _ hzU, mul_inv_cancel_right])
    have hzvC : z * v ∈ Subgroup.centralizer (A₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have := hv a ha
      calc a * (z * v) = (a * (z * v) * a⁻¹) * a := by group
        _ = (z * v) * a := by rw [this]
    have e : z = (z * v) * v⁻¹ := by group
    rw [e]
    exact M.mul_mem (hCA₀ hzvC) (M.inv_mem (hXqM hvO))
  have hbX : b ∈ Cg d := hbC
  have hbUt' : b ∈ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨hzX, hzU⟩ := (hmemUt' z).1 hz
      have hbz : b * z * b⁻¹ ∈ Cg d := (Cg d).mul_mem ((Cg d).mul_mem hbX hzX) ((Cg d).inv_mem hbX)
      refine (hmemUt' _).2 ⟨hbz, ?_⟩
      have e : mk ⟨b * z * b⁻¹, hbz⟩ = bb * mk ⟨z, hzX⟩ * bb⁻¹ := by
        rw [hbb, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact hUtb _ hzU
    · intro hz
      obtain ⟨hbzX, hbzU⟩ := (hmemUt' _).1 hz
      have hzX : z ∈ Cg d := by
        have := (Cg d).mul_mem ((Cg d).mul_mem ((Cg d).inv_mem hbX) hbzX) hbX
        simpa [mul_assoc] using this
      refine (hmemUt' z).2 ⟨hzX, ?_⟩
      have e : mk ⟨z, hzX⟩ = bb⁻¹ * mk ⟨b * z * b⁻¹, hbzX⟩ * bb := by
        rw [hbb, ← map_inv, ← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show z = b⁻¹ * (b * z * b⁻¹) * b
        group
      rw [e]
      exact hUtbi _ hbzU
  set W : Subgroup G := Ut' ⊔ Subgroup.zpowers b with hW
  have hWM : W ≤ M := sup_le hUt'M ((Subgroup.zpowers_le).2 (hBM hbB))
  have hWX : W ≤ Cg d := sup_le hUt'X ((Subgroup.zpowers_le).2 hbX)
  have hWN : W ≤ Subgroup.normalizer ((Ut' : Subgroup G) : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hbUt')
  obtain ⟨S0, hS0el, hS0map, -⟩ := exists_elemAbelian_lift (GLAPPrimeCore 3 ↥(Cg d))
    ((Nat.Prime.coprime_iff_not_dvd hp).1 CFSG.pPrimeCore_coprime_card) hUtel
  set R : Subgroup G := S0.map (Cg d).subtype with hR
  have hRU : R ≤ Ut' := by
    rintro _ ⟨s, hs, rfl⟩
    refine (hmemUt' _).2 ⟨s.2, ?_⟩
    rw [← hS0map]
    exact ⟨s, hs, rfl⟩
  have hRp : IsPGroup 3 ↥R := by
    have hel := CFSG.SectionRank.isElemAbelian_map hS0el (Cg d).subtype
    exact fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hel.2 g.1 g.2)⟩
  have hbp : IsPGroup 3 ↥(Subgroup.zpowers b) := l119_isPGroup_zpowers hb3
  obtain ⟨w, hwW, S, hSp, hSW, hbS, hRS⟩ := exists_conj_le_pGroup' (K := W)
    ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers b))) hbp
    (hRU.trans le_sup_left) hRp
  obtain ⟨x₁, hx₁⟩ := QuotientGroup.mk_surjective (Eh x)
  have hx₁' : mk x₁ = Eh x := hx₁
  have hx₁U : (x₁ : G) ∈ Ut' := (hmemUt' _).2 ⟨x₁.2, by
    show mk x₁ ∈ Ut
    rw [hx₁']
    exact ⟨x, hx, rfl⟩⟩
  have hwX : w ∈ Cg d := hWX hwW
  have hwN := hWN hwW
  have hwx₁ : w * x₁ * w⁻¹ ∈ Ut' := (Subgroup.mem_normalizer_iff.1 hwN _).1 hx₁U
  obtain ⟨hwx₁X, hwx₁U⟩ := (hmemUt' _).1 hwx₁
  rw [← hS0map] at hwx₁U
  obtain ⟨s, hs, hsx⟩ := hwx₁U
  have hx'X : w⁻¹ * (s : G) * w ∈ Cg d := (Cg d).mul_mem ((Cg d).mul_mem ((Cg d).inv_mem hwX) s.2) hwX
  have hx'S : w⁻¹ * (s : G) * w ∈ S := hRS (mem_gLBConj.2 (by
    have : w * (w⁻¹ * (s : G) * w) * w⁻¹ = s := by group
    rw [this]
    exact ⟨s, hs, rfl⟩))
  have hx'img : mk ⟨w⁻¹ * (s : G) * w, hx'X⟩ = Eh x := by
    have e1 : (⟨w⁻¹ * (s : G) * w, hx'X⟩ : ↥(Cg d)) = (⟨w, hwX⟩ : ↥(Cg d))⁻¹ * s * ⟨w, hwX⟩ := Subtype.ext rfl
    have e2 : mk s = mk ⟨w, hwX⟩ * mk x₁ * (mk ⟨w, hwX⟩)⁻¹ := by
      rw [hsx, ← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e1, map_mul, map_mul, map_inv, e2, ← hx₁']
    group
  have hbS' : b ∈ S := hbS (Subgroup.mem_zpowers b)
  have hbN' : b ∈ Lstarsub M L := Lemma136.l136_le_lstar hbL
  have hcc := Claims136b.comm_comm_eq_one hP95 h111 h121 hcomp h133 h (hSW.trans hWM) hSp hx'S
    hbS' hbN'
  have hx'' : ⁅⁅(⟨w⁻¹ * (s : G) * w, hx'X⟩ : ↥(Cg d)), (⟨b, hbC⟩ : ↥(Cg d))⁆, (⟨b, hbC⟩ : ↥(Cg d))⁆ = 1 := by
    apply Subtype.ext
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at hcc ⊢
    exact hcc
  apply hne
  rw [← comm_comm_eq_map Eh bb ψ hEb x, ← hx'img, hbb, ← map_commutatorElement,
    ← map_commutatorElement, hx'', map_one]

end Final

section Main

open Equiv
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut autBar barOf)

theorem iiHardCaseAltMainTwo_of_inputs (hP95 : Prop95) (h111 : Prop111Statement)
    (h121 : Prop121_of_cexStatement) (hcomp : Sec13_compStatement) (h133 : Lemma133Statement) :
    Claims136b.IIHardCaseAltMainTwo := by
  intro G _ _ m B M E A D T L h hN d hd hd1 hfix b _B1 hP _hS hEk K hK _hnot hBsN hcent _hnb halt
  classical
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set Bs := Lemma136c.bStarOf B L D b with hBs
  obtain ⟨hLc, -⟩ := hcomp h.toSec13 h.hL
  have hLM : L ≤ M := hLc.1
  have hLsn : IsSubnormal L M := hLc.2.1
  have hdA : d ∈ A := h.hD.1 hd
  have hBel : IsElemAbelian 3 B := h.uniq.elemAbelian
  have hBcomm : ∀ y ∈ B, ∀ y' ∈ B, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hBel.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  obtain ⟨hbBL, hσb, -, -, -⟩ := hP
  have hBsB : Bs ≤ B := sup_le ((Subgroup.zpowers_le).2 hbBL.1) (inf_le_left.trans inf_le_right)
  have hbBs : b ∈ Bs := Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  have hb3 : b ^ 3 = 1 := hBel.2 b hbBL.1
  obtain ⟨-, eM, -⟩ := Lemma136.l136_gamma hP95 h111 h121 hcomp h
  have eL : barOf 3 L ≃* alternatingGroup (Fin 7) := (quotEquivBarX hp hLM hLsn).trans eM
  have hd3 : d ^ 3 = 1 := h.hD.2.1.2 d hd
  have hσ3 : barAut 3 L ⟨d, hN hd⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨d, hN hd⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ 3 = 1 := Subtype.ext (by simp [hd3])
    rw [this, map_one]
  obtain ⟨hσd1, -⟩ := Claims136.exists_klein eL _ hσ3 hfix
  have hb1 : b ≠ 1 := by
    intro h1
    apply hσd1
    rw [← hσb (Subgroup.le_normalizer hbBL.2)]
    have : (⟨b, Subgroup.le_normalizer hbBL.2⟩ : ↥(Subgroup.normalizer (L : Set G))) = 1 :=
      Subtype.ext h1
    rw [this, map_one]
  obtain ⟨hBsC, -, hBsc⟩ := hEk
  have hbC : b ∈ Cg d := hBsC hbBs
  have hcard3 : ∀ y : G, y ^ 3 = 1 → Nat.card ↥(Subgroup.zpowers y) ≤ 3 := fun y hy => by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hy)
  obtain ⟨-, hcgI⟩ := Claims136b.conj_comp hcomp h M.one_mem
  rw [gLBConj_one] at hcgI
  obtain ⟨-, -, -, hBLc, hrk⟩ := (h133 h.toSec13).2 L hcgI
  have h9 : 9 ≤ Nat.card ↥(B ⊓ L) := by
    have h2 := Claims136.two_le_pRank_of_alt7 eL
    have hBLel : IsElemAbelian 3 (B ⊓ L) := CFSG.Open.IsElemAbelian.mono hBel inf_le_left
    rw [Claims136.card_eq_pow_pRank3 hBLel, hrk]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 L := Nat.pow_le_pow_right (by norm_num) h2
  obtain ⟨b₁, hb₁BL, hb₁b⟩ : ∃ b₁ ∈ B ⊓ L, b₁ ∉ Subgroup.zpowers b := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show B ⊓ L ≤ Subgroup.zpowers b from hcon)
    have := hcard3 b hb3
    omega
  have hb₁B : b₁ ∈ B := hb₁BL.1
  have hb₁3 : b₁ ^ 3 = 1 := hBel.2 b₁ hb₁B
  have hb₁d : b₁ ∈ Cg d := by
    have hb₁N : b₁ ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hb₁BL.2
    have hbN : b ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hbBL.2
    have hzL : b₁ * d * b₁⁻¹ * d⁻¹ ∈ L := by
      have h1 : d * b₁⁻¹ * d⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hN hd) _).1 (L.inv_mem hb₁BL.2)
      have e : b₁ * d * b₁⁻¹ * d⁻¹ = b₁ * (d * b₁⁻¹ * d⁻¹) := by group
      rw [e]
      exact L.mul_mem hb₁BL.2 h1
    have hzP : b₁ * d * b₁⁻¹ * d⁻¹ ∈ A ⊔ B := by
      have hb₁P : b₁ ∈ A ⊔ B := Subgroup.mem_sup_right hb₁B
      have hdP : d ∈ A ⊔ B := Subgroup.mem_sup_left hdA
      exact (A ⊔ B).mul_mem ((A ⊔ B).mul_mem ((A ⊔ B).mul_mem hb₁P hdP) ((A ⊔ B).inv_mem hb₁P))
        ((A ⊔ B).inv_mem hdP)
    have hz1 : barAut 3 L ⟨b₁ * d * b₁⁻¹ * d⁻¹, Subgroup.le_normalizer hzL⟩ = 1 := by
      have e : (⟨b₁ * d * b₁⁻¹ * d⁻¹, Subgroup.le_normalizer hzL⟩ :
          ↥(Subgroup.normalizer (L : Set G))) =
          ⟨b₁, hb₁N⟩ * ⟨d, hN hd⟩ * (⟨b₁, hb₁N⟩)⁻¹ * (⟨d, hN hd⟩)⁻¹ := Subtype.ext rfl
      have hcb : barAut 3 L ⟨b₁, hb₁N⟩ * barAut 3 L ⟨b, hbN⟩ =
          barAut 3 L ⟨b, hbN⟩ * barAut 3 L ⟨b₁, hb₁N⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hBcomm b₁ hb₁B b hbBL.1)
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hσb hbN, hcb]
      group
    have h1 := Claims136.eq_one_of_barAut_eq_one eL h.hAB hzL hzP _ hz1
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc b₁ * d = (b₁ * d * b₁⁻¹ * d⁻¹) * (d * b₁) := by group
      _ = d * b₁ := by rw [h1, one_mul]
  have hb₁Bs : b₁ ∉ Bs := by
    intro hmem
    have hc : Subgroup.zpowers b ≤ Subgroup.centralizer
        ((centBar 3 B L ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact hBcomm z hz.1.2 y ((Subgroup.zpowers_le.2 hbBL.1) hy)
    obtain ⟨y, hy, z, hz, hyz⟩ := exists_mul_of_mem_sup hc hmem
    have hzL : z ∈ L := by
      have e : z = y⁻¹ * b₁ := by rw [hyz]; group
      rw [e]
      exact L.mul_mem (L.inv_mem ((Subgroup.zpowers_le.2 hbBL.2) hy)) hb₁BL.2
    have hz1 : z = 1 := by
      have hz' : z ∈ (B ⊓ L) ⊓ centBar 3 B L := ⟨⟨hz.1.2, hzL⟩, hz.1⟩
      rw [hBLc] at hz'
      exact Subgroup.mem_bot.1 hz'
    apply hb₁b
    rw [hyz, hz1, mul_one]
    exact hy
  obtain ⟨c₀, hc₀Bs, hc₀b⟩ : ∃ c₀ ∈ Bs, c₀ ∉ Subgroup.zpowers b := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (show Bs ≤ Subgroup.zpowers b from hcon)
    rw [hBsc, Nat.card_zpowers] at h1
    have h2 : orderOf b ≤ 3 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hb3)
    have h3 : (3 : ℕ) ^ 2 = 9 := by norm_num
    omega
  have hc₀B : c₀ ∈ B := hBsB hc₀Bs
  have hc₀C : c₀ ∈ Cg d := hBsC hc₀Bs
  have hc₀1 : c₀ ≠ 1 := fun h1 => hc₀b (h1 ▸ Subgroup.one_mem _)
  have hc₀3 : c₀ ^ 3 = 1 := hBel.2 c₀ hc₀B
  have hbc₀ : b ∉ Subgroup.zpowers c₀ := by
    intro hbm
    apply hc₀b
    have hle : Subgroup.zpowers b ≤ Subgroup.zpowers c₀ := (Subgroup.zpowers_le).2 hbm
    have hcb : Nat.card ↥(Subgroup.zpowers c₀) ≤ Nat.card ↥(Subgroup.zpowers b) := by
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hb3 hb1, orderOf_eq_prime hc₀3 hc₀1]
    rw [Subgroup.eq_of_le_of_card_ge hle hcb]
    exact Subgroup.mem_zpowers c₀
  obtain ⟨m', δ, hm', hδ, φ, ρ, Ω₀, hact, hΩ, hsemi⟩ := halt
  have hn9 : 9 ≤ m' * 3 ^ 2 := by
    have : m' * 3 ^ 2 = 9 * m' := by ring
    omega
  have h5 : 5 ≤ m' * 3 ^ 2 + δ := by omega
  have h6 : m' * 3 ^ 2 + δ ≠ 6 := by omega
  set σ := AltWeakBalance.autPerm φ h5 h6 with hσ
  set ι : barOf 3 K →* Perm (Fin (m' * 3 ^ 2 + δ)) :=
    (alternatingGroup (Fin (m' * 3 ^ 2 + δ))).subtype.comp φ.toMonoidHom with hι
  have hιi : Function.Injective ι := fun u v huv => φ.injective (Subtype.ext huv)
  have hισ : ∀ (ψ : MulAut (barOf 3 K)) (u : barOf 3 K), ι (ψ u) = σ ψ * ι u * (σ ψ)⁻¹ :=
    fun ψ u => AltWeakBalance.autPerm_spec φ h5 h6 ψ u
  have hmemAb : ∀ y (hy : y ∈ Bs), barAut 3 K ⟨y, hBsN hy⟩ ∈ autBar 3 Bs K := fun y hy =>
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ⟨hy, hBsN hy⟩)
  have hAbcases : ∀ g ∈ autBar 3 Bs K, ∃ y, ∃ hy : y ∈ Bs, g = barAut 3 K ⟨y, hBsN hy⟩ := by
    rintro _ ⟨⟨y, hyN⟩, hy, rfl⟩
    exact ⟨y, (Subgroup.mem_subgroupOf.1 hy).1, rfl⟩
  have hinjBs : ∀ y (hy : y ∈ Bs), barAut 3 K ⟨y, hBsN hy⟩ = 1 → y = 1 := by
    intro y hy h1
    have hmem : y ∈ centBar 3 Bs K := ⟨⟨⟨y, hBsN hy⟩, h1, rfl⟩, hy⟩
    rw [hcent] at hmem
    exact Subgroup.mem_bot.1 hmem
  set πN : ↥(Subgroup.normalizer (K : Set G)) →* Perm (Fin (m' * 3 ^ 2 + δ)) :=
    σ.toMonoidHom.comp (barAut 3 K) with hπN
  have hπNapp : ∀ g, πN g = σ (barAut 3 K g) := fun g => rfl
  have hinjN : ∀ g : ↥(Subgroup.normalizer (K : Set G)), (g : G) ∈ Bs → πN g = 1 → (g : G) = 1 := by
    intro g hg h1
    have h2 : barAut 3 K g = 1 := σ.injective (by rw [← hπNapp, h1, map_one])
    exact hinjBs (g : G) hg h2
  have hπN3 : ∀ y (hy : y ∈ Subgroup.normalizer (K : Set G)), y ^ 3 = 1 → πN ⟨y, hy⟩ ^ 3 = 1 := by
    intro y hy hy3
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  set P : Subgroup (Perm (Fin (m' * 3 ^ 2 + δ))) := (autBar 3 Bs K).map σ.toMonoidHom with hP
  have hPmem : ∀ y (hy : y ∈ Bs), πN ⟨y, hBsN hy⟩ ∈ P := fun y hy =>
    Subgroup.mem_map_of_mem _ (hmemAb y hy)
  have hPcases : ∀ g ∈ P, ∃ y, ∃ hy : y ∈ Bs, g = πN ⟨y, hBsN hy⟩ := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨y, hy, rfl⟩ := hAbcases g hg
    exact ⟨y, hy, rfl⟩
  have hPab : ∀ g ∈ P, ∀ g' ∈ P, g * g' = g' * g := by
    intro g hg g' hg'
    obtain ⟨y, hy, rfl⟩ := hPcases g hg
    obtain ⟨y', hy', rfl⟩ := hPcases g' hg'
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBcomm y (hBsB hy) y' (hBsB hy'))
  obtain ⟨ω, hω⟩ : ∃ ω, ω ∉ Ω₀ := by
    by_contra hcon
    push Not at hcon
    have huniv : Ω₀ = Set.univ := Set.eq_univ_of_forall hcon
    rw [huniv, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin] at hΩ
    omega
  have hreg : ∀ g ∈ P, g ω = ω → g = 1 := by
    intro g hg hgω
    obtain ⟨y, hy, rfl⟩ := hPcases g hg
    by_contra hne
    have hσρ : σ (barAut 3 K ⟨y, hBsN hy⟩) = ρ ⟨_, hmemAb y hy⟩ :=
      AltWeakBalance.autPerm_eq φ h5 h6 (hact ⟨_, hmemAb y hy⟩)
    have hg1 : (⟨_, hmemAb y hy⟩ : ↥(autBar 3 Bs K)) ≠ 1 := by
      intro h1
      apply hne
      rw [hπNapp, show barAut 3 K ⟨y, hBsN hy⟩ = 1 from congrArg Subtype.val h1, map_one]
    exact hsemi.2 _ hg1 ω hω (by rw [← hσρ]; exact hgω)
  set β := πN ⟨b, hBsN hbBs⟩ with hβdef
  set γ := πN ⟨c₀, hBsN hc₀Bs⟩ with hγdef
  have hβP : β ∈ P := hPmem b hbBs
  have hγP : γ ∈ P := hPmem c₀ hc₀Bs
  have hβ3 : β ^ 3 = 1 := hπN3 b _ hb3
  have hγ3 : γ ^ 3 = 1 := hπN3 c₀ _ hc₀3
  have hγ1 : γ ≠ 1 := fun h1 => hc₀1 (hinjN _ hc₀Bs h1)
  have hβγ : β ∉ Subgroup.zpowers γ := by
    intro hmem
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 hmem
    set g : ↥(Subgroup.normalizer (K : Set G)) :=
      ((⟨c₀, hBsN hc₀Bs⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ i)⁻¹ * ⟨b, hBsN hbBs⟩ with hg
    have hgG : (g : G) = (c₀ ^ i)⁻¹ * b := by simp [hg]
    have hgBs : (g : G) ∈ Bs := by
      rw [hgG]
      exact Bs.mul_mem (Bs.inv_mem (Bs.zpow_mem hc₀Bs i)) hbBs
    have h1 : πN g = 1 := by
      rw [hg, map_mul, map_inv, map_zpow, ← hγdef, hi, ← hβdef, inv_mul_cancel]
    have h2 := hinjN g hgBs h1
    rw [hgG] at h2
    exact hbc₀ (Subgroup.mem_zpowers_iff.2 ⟨i, inv_mul_eq_one.1 h2⟩)
  set ψ : barOf 3 K →* barOf 3 K := (barAut 3 K ⟨b, hBsN hbBs⟩).toMonoidHom with hψ
  have hιψ : ∀ u, β * ι u * β⁻¹ = ι (ψ u) := fun u => (hισ _ u).symm
  have common : ∀ π₁ : Perm (Fin (m' * 3 ^ 2 + δ)), π₁ ^ 3 = 1 → (∀ g ∈ P, π₁ * g = g * π₁) →
      (π₁ ω = ω ∨ ∀ g ∈ P, π₁ ω ≠ g ω) →
      ∃ U : Subgroup (barOf 3 K), IsElemAbelian 3 U ∧ (∀ u ∈ U, ψ u ∈ U) ∧
        (∀ u ∈ U, barAut 3 K ⟨c₀, hBsN hc₀Bs⟩ u = u) ∧ (∀ u ∈ U, ι u * π₁ = π₁ * ι u) ∧
        ∃ x ∈ U, x * (ψ x)⁻¹ * (ψ (x * (ψ x)⁻¹))⁻¹ ≠ 1 := by
    intro π₁ hπ3 hπP hπω
    obtain ⟨hHab, hH3, hβH, x, hxU, hxne⟩ :=
      perm_core hPab hreg hβP hγP hβγ hγ1 hβ3 hγ3 hπ3 hπP hπω
    set H := Subgroup.zpowers γ ⊔ Subgroup.zpowers π₁ with hH
    have hUprops := Claims136b.orbSubH_props hHab hH3
    have hmemU : ∀ u, u ∈ (Claims136b.orbSubH H).comap ι ↔ ι u ∈ Claims136b.orbSubH H :=
      fun u => Iff.rfl
    refine ⟨(Claims136b.orbSubH H).comap ι, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨⟨⟨fun u v => Subtype.ext (hιi ?_)⟩⟩, fun u hu => hιi ?_⟩
      · show ι ((u : barOf 3 K) * v) = ι ((v : barOf 3 K) * u)
        rw [map_mul, map_mul]
        exact hUprops.2 _ u.2 _ v.2
      · rw [map_pow, map_one]
        exact hUprops.1 _ hu
    · intro u hu
      rw [hmemU, ← hιψ]
      exact Claims136b.conj_mem_orbSubH hβH ((hmemU u).1 hu)
    · intro u hu
      apply hιi
      rw [hισ]
      have h1 := (Claims136b.mem_orbSubH.1 ((hmemU u).1 hu)).1 γ
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers γ))
      show γ * ι u * γ⁻¹ = ι u
      rw [← h1, mul_inv_cancel_right]
    · intro u hu
      exact (Claims136b.mem_orbSubH.1 ((hmemU u).1 hu)).1 π₁
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers π₁))
    · have hx3 : x ^ 3 = 1 := hUprops.1 x hxU
      have hxA : x ∈ alternatingGroup (Fin (m' * 3 ^ 2 + δ)) :=
        Perm.mem_alternatingGroup.2 (AltWeakBalance.sign_eq_one_of_pow_prime hp (by norm_num) hx3)
      set xt : barOf 3 K := φ.symm ⟨x, hxA⟩ with hxt
      have hιxt : ι xt = x := by
        show ((φ (φ.symm ⟨x, hxA⟩) : alternatingGroup (Fin _)) : Perm _) = x
        rw [MulEquiv.apply_symm_apply]
      refine ⟨xt, ?_, ?_⟩
      · rw [hmemU, hιxt]
        exact hxU
      · intro h0
        apply hxne
        rw [← hιxt, comm_comm_eq_map ι β ψ hιψ, h0, map_one]
  by_cases hb₁K : b₁ ∈ Subgroup.normalizer (K : Set G)
  ·
    have case1 : ∀ (a₁ : G) (ha₁B : a₁ ∈ B) (ha₁C : a₁ ∈ Cg d)
        (ha₁K : a₁ ∈ Subgroup.normalizer (K : Set G)), a₁ ∉ Bs →
        (πN ⟨a₁, ha₁K⟩ ω = ω ∨ ∀ g ∈ P, πN ⟨a₁, ha₁K⟩ ω ≠ g ω) → False := by
      intro a₁ ha₁B ha₁C ha₁K ha₁Bs hπω
      have hπ3 : πN ⟨a₁, ha₁K⟩ ^ 3 = 1 := hπN3 a₁ ha₁K (hBel.2 a₁ ha₁B)
      have hπP : ∀ g ∈ P, πN ⟨a₁, ha₁K⟩ * g = g * πN ⟨a₁, ha₁K⟩ := by
        intro g hg
        obtain ⟨y, hy, rfl⟩ := hPcases g hg
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (hBcomm a₁ ha₁B y (hBsB hy))
      obtain ⟨U, hUel, hψU, hUc, hUa, x, hxU, hxne⟩ := common _ hπ3 hπP hπω
      have hUa' : ∀ u ∈ U, barAut 3 K ⟨a₁, ha₁K⟩ u = u := by
        intro u hu
        apply hιi
        rw [hισ]
        show πN ⟨a₁, ha₁K⟩ * ι u * (πN ⟨a₁, ha₁K⟩)⁻¹ = ι u
        rw [← hUa u hu, mul_inv_cancel_right]
      have hfix : ∀ (g : G) (hgC : g ∈ Cg d) (hgK : g ∈ Subgroup.normalizer (K : Set G)),
          (∀ u ∈ U, barAut 3 K ⟨g, hgK⟩ u = u) → ∀ u ∈ U,
          QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨g, hgC⟩ * embBar hK u =
            embBar hK u * QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) ⟨g, hgC⟩ := by
        intro g hgC hgK hgU u hu
        have h1 := embBar_barAut hK hgC hgK u
        rw [hgU u hu] at h1
        exact mul_inv_eq_iff_eq_mul.1 h1
      exact final_step hP95 h111 h121 hcomp h133 h hdA hd1 hc₀B ha₁B hc₀C ha₁C hc₀1
        (fun hm => ha₁Bs ((Subgroup.zpowers_le.2 hc₀Bs) hm)) hbBL.1 hbBL.2 hbC (embBar hK) hUel ψ
        hψU (fun u => embBar_barAut hK hbC (hBsN hbBs) u) (hfix c₀ hc₀C (hBsN hc₀Bs) hUc)
        (hfix a₁ ha₁C ha₁K hUa') hxU
        (fun h0 => hxne (embBar_injective hK (h0.trans (map_one _).symm)))
    by_cases hT : ∃ g ∈ P, πN ⟨b₁, hb₁K⟩ ω = g ω
    · obtain ⟨g, hg, hgω⟩ := hT
      obtain ⟨y₀, hy₀, rfl⟩ := hPcases g hg
      have ha₁K : y₀⁻¹ * b₁ ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).mul_mem
          ((Subgroup.normalizer (K : Set G)).inv_mem (hBsN hy₀)) hb₁K
      refine case1 (y₀⁻¹ * b₁) (B.mul_mem (B.inv_mem (hBsB hy₀)) hb₁B)
        ((Cg d).mul_mem ((Cg d).inv_mem (hBsC hy₀)) hb₁d) ha₁K ?_ (Or.inl ?_)
      · intro hmem
        apply hb₁Bs
        have e : b₁ = y₀ * (y₀⁻¹ * b₁) := by group
        rw [e]
        exact Bs.mul_mem hy₀ hmem
      · have e : (⟨y₀⁻¹ * b₁, ha₁K⟩ : ↥(Subgroup.normalizer (K : Set G))) =
            (⟨y₀, hBsN hy₀⟩ : ↥(Subgroup.normalizer (K : Set G)))⁻¹ * ⟨b₁, hb₁K⟩ := Subtype.ext rfl
        rw [e, map_mul, map_inv, Perm.mul_apply, hgω, perm_inv_apply_self]
    · push Not at hT
      exact case1 b₁ hb₁B hb₁d hb₁K hb₁Bs (Or.inr hT)
  ·
    obtain ⟨U, hUel, hψU, hUc, -, x, hxU, hxne⟩ :=
      common 1 (one_pow 3) (fun g _ => by rw [one_mul, mul_one]) (Or.inl rfl)
    set mk := QuotientGroup.mk' (GLAPPrimeCore 3 ↥(Cg d)) with hmk
    set ν := mk ⟨b₁, hb₁d⟩ with hν
    have hν3 : ν ^ 3 = 1 := by
      rw [hν, ← map_pow]
      have : (⟨b₁, hb₁d⟩ : ↥(Cg d)) ^ 3 = 1 := Subtype.ext (by simpa using hb₁3)
      rw [this, map_one]
    set c : (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) →* (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) :=
      (MulAut.conj ν⁻¹).toMonoidHom with hc
    have hcapp : ∀ y, c y = ν⁻¹ * y * ν := fun y => by
      show MulAut.conj ν⁻¹ y = ν⁻¹ * y * ν
      rw [MulAut.conj_apply, inv_inv]
    have hc3 : ∀ y, c (c (c y)) = y := by
      intro y
      rw [hcapp, hcapp, hcapp]
      have h1 : ν * ν * ν = 1 := by rw [mul_assoc, ← pow_three]; exact hν3
      calc ν⁻¹ * (ν⁻¹ * (ν⁻¹ * y * ν) * ν) * ν = (ν * ν * ν)⁻¹ * y * (ν * ν * ν) := by group
        _ = y := by rw [h1, inv_one, one_mul, mul_one]
    have hKbar : IsComponentOf (barX 3 (Cg d) K) ⊤ := hK.2.2.1
    have hneK : barX 3 (Cg d) K ≠ GLBConj ν (barX 3 (Cg d) K) := by
      intro heq
      apply hb₁K
      exact Lemma136.l136_mem_normalizer_of_bar hK ⟨b₁, hb₁d⟩
        (mem_normalizer_iff_gLBConj_eq.2 heq.symm)
    have hcomm : ∀ u v, embBar hK u * c (embBar hK v) = c (embBar hK v) * embBar hK u := by
      intro u v
      rw [hcapp]
      refine CFSG.ComponentClassification.AschbacherTheorem5.SectionSix.components_commute hKbar
        (isComponentOf_gLBConj hKbar ν) hneK _ (embBar_mem hK u) _ ?_
      rw [mem_gLBConj]
      have e : ν * (ν⁻¹ * embBar hK v * ν) * ν⁻¹ = embBar hK v := by group
      rw [e]
      exact embBar_mem hK v
    set Δ := diagHom (embBar hK) c hc3 hcomm with hΔ
    have hcΔ : ∀ u, c (Δ u) = Δ u := c_diagHom (embBar hK) c hc3 hcomm
    have hτΔ : ∀ (τ : (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d)) →* (↥(Cg d) ⧸ GLAPPrimeCore 3 ↥(Cg d))),
        (∀ y, τ (c y) = c (τ y)) → ∀ {u u' : barOf 3 K}, τ (embBar hK u) = embBar hK u' →
          τ (Δ u) = Δ u' :=
      fun τ hτc u u' hu => tau_diagHom (embBar hK) c hc3 hcomm τ hτc hu
    have hΔ1 : ∀ w, Δ w = 1 → w = 1 := by
      intro w hw
      have hcw := comm_of_diagHom_eq_one (embBar hK) c hc3 hcomm hw
      have hz : φ w ∈ Subgroup.center (alternatingGroup (Fin (m' * 3 ^ 2 + δ))) := by
        rw [Subgroup.mem_center_iff]
        intro g
        obtain ⟨v, rfl⟩ := φ.surjective g
        rw [← map_mul, ← map_mul]
        congr 1
        have h2 : w * v = v * w := embBar_injective hK (by rw [map_mul, map_mul]; exact hcw v)
        exact h2.symm
      rw [alternatingGroup.center_eq_bot (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega),
        Subgroup.mem_bot] at hz
      exact φ.injective (hz.trans (map_one φ).symm)
    have hconjΔ : ∀ (g : G) (hgC : g ∈ Cg d) (hgK : g ∈ Subgroup.normalizer (K : Set G)),
        g * b₁ = b₁ * g → ∀ u, mk ⟨g, hgC⟩ * Δ u * (mk ⟨g, hgC⟩)⁻¹ = Δ (barAut 3 K ⟨g, hgK⟩ u) := by
      intro g hgC hgK hg u
      have hgν : Commute (mk ⟨g, hgC⟩) ν := by
        show mk ⟨g, hgC⟩ * ν = ν * mk ⟨g, hgC⟩
        rw [hν, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hg
      have hτc : ∀ y, (MulAut.conj (mk ⟨g, hgC⟩)).toMonoidHom (c y) =
          c ((MulAut.conj (mk ⟨g, hgC⟩)).toMonoidHom y) := by
        intro y
        show MulAut.conj (mk ⟨g, hgC⟩) (c y) = c (MulAut.conj (mk ⟨g, hgC⟩) y)
        rw [hcapp, hcapp, MulAut.conj_apply, MulAut.conj_apply]
        calc mk ⟨g, hgC⟩ * (ν⁻¹ * y * ν) * (mk ⟨g, hgC⟩)⁻¹ =
            (mk ⟨g, hgC⟩ * ν⁻¹) * y * (ν * (mk ⟨g, hgC⟩)⁻¹) := by group
          _ = (ν⁻¹ * mk ⟨g, hgC⟩) * y * ((mk ⟨g, hgC⟩)⁻¹ * ν) := by
            rw [hgν.inv_right.eq, ← hgν.inv_left.eq]
          _ = ν⁻¹ * (mk ⟨g, hgC⟩ * y * (mk ⟨g, hgC⟩)⁻¹) * ν := by group
      have h1 := hτΔ (MulAut.conj (mk ⟨g, hgC⟩)).toMonoidHom hτc (u := u)
        (u' := barAut 3 K ⟨g, hgK⟩ u) (by
          show MulAut.conj (mk ⟨g, hgC⟩) (embBar hK u) = _
          rw [MulAut.conj_apply]
          exact embBar_barAut hK hgC hgK u)
      rw [← h1]
      show _ = MulAut.conj (mk ⟨g, hgC⟩) (Δ u)
      rw [MulAut.conj_apply]
    have hEc : ∀ u ∈ U, mk ⟨c₀, hc₀C⟩ * Δ u = Δ u * mk ⟨c₀, hc₀C⟩ := by
      intro u hu
      have h1 := hconjΔ c₀ hc₀C (hBsN hc₀Bs) (hBcomm c₀ hc₀B b₁ hb₁B) u
      rw [hUc u hu] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    have hEa : ∀ u ∈ U, mk ⟨b₁, hb₁d⟩ * Δ u = Δ u * mk ⟨b₁, hb₁d⟩ := by
      intro u hu
      have h1 := hcΔ u
      rw [hcapp] at h1
      rw [← hν]
      calc ν * Δ u = ν * (ν⁻¹ * Δ u * ν) := by rw [h1]
        _ = Δ u * ν := by group
    exact final_step hP95 h111 h121 hcomp h133 h hdA hd1 hc₀B hb₁B hc₀C hb₁d hc₀1
      (fun hm => hb₁Bs ((Subgroup.zpowers_le.2 hc₀Bs) hm)) hbBL.1 hbBL.2 hbC Δ hUel ψ hψU
      (hconjΔ b hbC (hBsN hbBs) (hBcomm b hbBL.1 b₁ hb₁B)) hEc hEa hxU (fun h0 => hxne (hΔ1 _ h0))

end Main

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims136c

end
