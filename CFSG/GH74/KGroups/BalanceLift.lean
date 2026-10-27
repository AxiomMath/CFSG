module

public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X5bGroup

public section

namespace CFSG.GH74.KGroups.Bal

open Subgroup CFSG CFSG.QuasithinUnique.Setup.X5
open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

theorem commutator_induction {A B : Subgroup G} {C : G → Prop} {x : G} (hx : x ∈ ⁅A, B⁆)
    (hgen : ∀ a ∈ A, ∀ b ∈ B, C ⁅a, b⁆) (h1 : C 1) (hmul : ∀ x y, C x → C y → C (x * y))
    (hinv : ∀ x, C x → C x⁻¹) : C x := by
  rw [Subgroup.commutator_def] at hx
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hz
    exact hgen a ha b hb
  | one => exact h1
  | mul x y _ _ hx hy => exact hmul x y hx hy
  | inv x _ hx => exact hinv x hx

theorem commutator_mul_mul_of_commute {y₁ y₂ τ₁ τ₂ : G} (h₁₁ : Commute y₁ τ₁) (h₁₂ : Commute y₁ τ₂)
    (h₂₁ : Commute y₂ τ₁) (h₂₂ : Commute y₂ τ₂) : ⁅y₁ * τ₁, y₂ * τ₂⁆ = ⁅y₁, y₂⁆ * ⁅τ₁, τ₂⁆ := by
  let P := Subgroup.closure ({y₁, y₂} : Set G)
  let T := Subgroup.closure ({τ₁, τ₂} : Set G)
  have hc : ∀ m : P, ∀ n : T, Commute (P.subtype m) (T.subtype n) := by
    intro m n
    have : ∀ a ∈ P, ∀ b ∈ T, Commute a b := by
      intro a ha b hb
      induction ha using Subgroup.closure_induction with
      | mem a ha =>
        induction hb using Subgroup.closure_induction with
        | mem b hb =>
          rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> assumption
        | one => exact Commute.one_right _
        | mul b b' _ _ h h' => exact h.mul_right h'
        | inv b _ h => exact h.inv_right
      | one => exact Commute.one_left _
      | mul a a' _ _ h h' => exact h.mul_left h'
      | inv a _ h => exact h.inv_left
    exact this m m.2 n n.2
  let ψ : P × T →* G := MonoidHom.noncommCoprod P.subtype T.subtype hc
  have hy₁ : y₁ ∈ P := Subgroup.subset_closure (by simp)
  have hy₂ : y₂ ∈ P := Subgroup.subset_closure (by simp)
  have ht₁ : τ₁ ∈ T := Subgroup.subset_closure (by simp)
  have ht₂ : τ₂ ∈ T := Subgroup.subset_closure (by simp)
  have key : ⁅ψ (⟨y₁, hy₁⟩, ⟨τ₁, ht₁⟩), ψ (⟨y₂, hy₂⟩, ⟨τ₂, ht₂⟩)⁆ =
      ψ (⁅(⟨y₁, hy₁⟩ : P), ⟨y₂, hy₂⟩⁆, ⁅(⟨τ₁, ht₁⟩ : T), ⟨τ₂, ht₂⟩⁆) := by
    rw [← map_commutatorElement]
    congr 1
  simpa [ψ, MonoidHom.noncommCoprod_apply, commutatorElement_def] using key


theorem perfect_le_of_solvable_commute {D P T : Subgroup G} (hD : ⁅D, D⁆ = D)
    (hdec : ∀ x ∈ D, ∃ y ∈ P, ∃ τ ∈ T, y * τ = x) (hPT : ∀ y ∈ P, ∀ τ ∈ T, y * τ = τ * y)
    (hP : Group.IsSolvable ↥P) : D ≤ T := by
  obtain ⟨m, hm⟩ := (Group.isSolvable_def ↥P).1 hP
  have key : ∀ n : ℕ, ∀ x ∈ D, ∃ y ∈ (derivedSeries ↥P n).map P.subtype, ∃ τ ∈ T, y * τ = x := by
    intro n
    induction n with
    | zero =>
      intro x hx
      obtain ⟨y, hy, τ, hτ, h⟩ := hdec x hx
      exact ⟨y, ⟨⟨y, hy⟩, by simp, rfl⟩, τ, hτ, h⟩
    | succ n ih =>
      intro x hx
      have hx' : x ∈ ⁅D, D⁆ := by rw [hD]; exact hx
      refine commutator_induction (C := fun x => ∃ y ∈ (derivedSeries ↥P (n + 1)).map P.subtype,
        ∃ τ ∈ T, y * τ = x) hx' ?_ ⟨1, one_mem _, 1, one_mem _, by simp⟩ ?_ ?_
      · intro a ha b hb
        obtain ⟨y₁, ⟨ŷ₁, hŷ₁, rfl⟩, τ₁, hτ₁, rfl⟩ := ih a ha
        obtain ⟨y₂, ⟨ŷ₂, hŷ₂, rfl⟩, τ₂, hτ₂, rfl⟩ := ih b hb
        simp only [Subgroup.coe_subtype]
        have hcm : ∀ (ŷ : ↥P) (τ : G), τ ∈ T → Commute (ŷ : G) τ := fun ŷ τ hτ => hPT _ ŷ.2 τ hτ
        rw [commutator_mul_mul_of_commute (hcm ŷ₁ τ₁ hτ₁) (hcm ŷ₁ τ₂ hτ₂) (hcm ŷ₂ τ₁ hτ₁)
          (hcm ŷ₂ τ₂ hτ₂)]
        refine ⟨⁅(ŷ₁ : G), ŷ₂⁆, ⟨⁅ŷ₁, ŷ₂⁆, ?_, rfl⟩, ⁅τ₁, τ₂⁆, ?_, rfl⟩
        · rw [derivedSeries_succ]
          exact Subgroup.commutator_mem_commutator hŷ₁ hŷ₂
        · rw [commutatorElement_def]
          exact mul_mem (mul_mem (mul_mem hτ₁ hτ₂) (inv_mem hτ₁)) (inv_mem hτ₂)
      · rintro x₁ x₂ ⟨y₁, ⟨ŷ₁, hŷ₁, rfl⟩, τ₁, hτ₁, rfl⟩ ⟨y₂, ⟨ŷ₂, hŷ₂, rfl⟩, τ₂, hτ₂, rfl⟩
        refine ⟨(ŷ₁ : G) * ŷ₂, ⟨ŷ₁ * ŷ₂, mul_mem hŷ₁ hŷ₂, rfl⟩, τ₁ * τ₂, mul_mem hτ₁ hτ₂, ?_⟩
        have := hPT _ ŷ₂.2 τ₁ hτ₁
        calc (ŷ₁ : G) * ŷ₂ * (τ₁ * τ₂) = ŷ₁ * (ŷ₂ * τ₁) * τ₂ := by simp only [mul_assoc]
          _ = ŷ₁ * (τ₁ * ŷ₂) * τ₂ := by rw [this]
          _ = (ŷ₁ * τ₁) * (ŷ₂ * τ₂) := by simp only [mul_assoc]
      · rintro x₁ ⟨y₁, ⟨ŷ₁, hŷ₁, rfl⟩, τ₁, hτ₁, rfl⟩
        refine ⟨((ŷ₁ : G))⁻¹, ⟨ŷ₁⁻¹, inv_mem hŷ₁, rfl⟩, τ₁⁻¹, inv_mem hτ₁, ?_⟩
        have := hPT _ ŷ₁.2 τ₁ hτ₁
        simp only [Subgroup.coe_subtype, mul_inv_rev]
        exact (Commute.inv_inv this).eq
  intro x hx
  obtain ⟨y, hy, τ, hτ, rfl⟩ := key m x hx
  rw [hm] at hy
  obtain ⟨y', hy', rfl⟩ := hy
  have hy1 : y' = 1 := hy'
  rw [hy1, map_one, one_mul]
  exact hτ

theorem centralizes_of_central_commutator {H : Subgroup G} (hH : ⁅H, H⁆ = H) {a : G}
    (h : ∀ x ∈ H, ⁅a, x⁆ ∈ H ∧ ∀ y ∈ H, ⁅a, x⁆ * y = y * ⁅a, x⁆) : ∀ x ∈ H, a * x = x * a := by
  let H₀ : Subgroup G :=
    { carrier := {x | x ∈ H ∧ a * x = x * a}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
        calc a * (x * y) = (a * x) * y := by rw [mul_assoc]
          _ = (x * a) * y := by rw [hx.2]
          _ = x * (a * y) := by rw [mul_assoc]
          _ = x * (y * a) := by rw [hy.2]
          _ = x * y * a := by rw [mul_assoc]⟩
      inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
        calc a * x⁻¹ = x⁻¹ * (x * a) * x⁻¹ := by group
          _ = x⁻¹ * (a * x) * x⁻¹ := by rw [hx.2]
          _ = x⁻¹ * a := by group⟩ }
  have hle : H ≤ H₀ := by
    rw [← hH, Subgroup.commutator_le]
    intro x hx y hy
    obtain ⟨hcx, hcx'⟩ := h x hx
    obtain ⟨hcy, hcy'⟩ := h y hy
    refine ⟨?_, ?_⟩
    · have := Subgroup.commutator_mem_commutator hx hy
      rwa [hH] at this
    · have hxa : a * x * a⁻¹ = ⁅a, x⁆ * x := by simp only [commutatorElement_def]; group
      have hya : a * y * a⁻¹ = ⁅a, y⁆ * y := by simp only [commutatorElement_def]; group
      have hconj : a * ⁅x, y⁆ * a⁻¹ = ⁅a * x * a⁻¹, a * y * a⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      have hcy : ⁅a, y⁆ ∈ H := hcy
      have hcomm : ⁅a * x * a⁻¹, a * y * a⁻¹⁆ = ⁅x, y⁆ := by
        rw [hxa, hya, commutator_mul_mul_of_commute (hcx' x hx) (hcx' y hy) (hcy' x hx) (hcy' y hy),
          commutatorElement_eq_one_iff_mul_comm.2 (hcx' _ hcy), one_mul]
      have := hconj.trans hcomm
      calc a * ⁅x, y⁆ = (a * ⁅x, y⁆ * a⁻¹) * a := by group
        _ = ⁅x, y⁆ * a := by rw [this]
  intro x hx
  exact (hle (hH ▸ hx)).2


theorem exists_fixed_involution [Finite G] {a : G} (ha : a * a = 1) {J : Subgroup G}
    (hJa : ∀ x ∈ J, a * x * a⁻¹ ∈ J) (hJ : Even (Nat.card J)) :
    ∃ j ∈ J, j * j = 1 ∧ j ≠ 1 ∧ a * j = j * a := by
  classical
  have : Fintype J := Fintype.ofFinite J
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have haa : ∀ x : G, a * (a * x) = x := fun x => by rw [← mul_assoc, ha, one_mul]
  let σ : Equiv.Perm J :=
    { toFun := fun x => ⟨a * x * a⁻¹, hJa x x.2⟩
      invFun := fun x => ⟨a * x * a⁻¹, hJa x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc, haa, hainv, ha])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc, haa, hainv, ha]) }
  have hσ2 : σ ^ 2 ^ 1 = 1 := by
    ext x
    simp [σ, pow_two, mul_assoc, haa, hainv, ha]
  have h1 := Equiv.Perm.card_compl_support_modEq (p := 2) (n := 1) hσ2
  set C : Subgroup G := J ⊓ Subgroup.centralizer ({a} : Set G) with hCdef
  have hfixset : (Equiv.Perm.support σ)ᶜ = Finset.univ.filter (fun x : J => σ x = x) := by
    ext x
    simp [Equiv.Perm.mem_support]
  have hσfix : ∀ x : J, σ x = x ↔ (x : G) * a = a * x := by
    intro x
    constructor
    · intro h
      have := congrArg Subtype.val h
      simp only [σ, Equiv.coe_fn_mk] at this
      calc (x : G) * a = (a * x * a⁻¹) * a := by rw [this]
        _ = a * x := by group
    · intro h
      apply Subtype.ext
      simp only [σ, Equiv.coe_fn_mk]
      calc a * (x : G) * a⁻¹ = (x * a) * a⁻¹ := by rw [← h]
        _ = x := by group
  have hCcard : Nat.card C = (Equiv.Perm.support σ)ᶜ.card := by
    rw [hfixset, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_congr ⟨fun c => ⟨⟨c.1, c.2.1⟩, (hσfix _).2 (mem_centralizer_singleton_iff.1 c.2.2)⟩,
      fun x => ⟨x.1.1, x.1.2, mem_centralizer_singleton_iff.2 ((hσfix _).1 x.2)⟩, ?_, ?_⟩
    · intro c; rfl
    · intro x; rfl
  have hCeven : Even (Nat.card C) := by
    rw [hCcard]
    have h2 : Even (Fintype.card J) := by rw [Nat.card_eq_fintype_card] at hJ; exact hJ
    rw [Nat.even_iff] at h2 ⊢
    have h1' : _ % 2 = _ % 2 := h1
    omega
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hCeven)
  refine ⟨(c : G), c.2.1, ?_, ?_, ?_⟩
  · have := pow_orderOf_eq_one c
    rw [hc, pow_two] at this
    simpa using congrArg Subtype.val this
  · intro h
    have : c = 1 := Subtype.ext h
    rw [this, orderOf_one] at hc
    omega
  · exact (mem_centralizer_singleton_iff.1 c.2.2).symm

end Helpers

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

theorem layer_decomposition {I : Subgroup Y} (hI : IsComponent I) :
    ∀ x ∈ layer Y, ∃ y ∈ I, ∃ τ ∈ layer Y ⊓ Subgroup.centralizer (I : Set Y), y * τ = x := by
  let M : Subgroup Y :=
    { carrier := {x | ∃ y ∈ I, ∃ τ ∈ layer Y ⊓ Subgroup.centralizer (I : Set Y), y * τ = x}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨y₁, hy₁, τ₁, hτ₁, rfl⟩ ⟨y₂, hy₂, τ₂, hτ₂, rfl⟩
        refine ⟨y₁ * y₂, mul_mem hy₁ hy₂, τ₁ * τ₂, mul_mem hτ₁ hτ₂, ?_⟩
        have : y₂ * τ₁ = τ₁ * y₂ := (Subgroup.mem_centralizer_iff.1 hτ₁.2 y₂ hy₂)
        calc y₁ * y₂ * (τ₁ * τ₂) = y₁ * (y₂ * τ₁) * τ₂ := by simp only [mul_assoc]
          _ = y₁ * (τ₁ * y₂) * τ₂ := by rw [this]
          _ = y₁ * τ₁ * (y₂ * τ₂) := by simp only [mul_assoc]
      inv_mem' := by
        rintro _ ⟨y, hy, τ, hτ, rfl⟩
        refine ⟨y⁻¹, inv_mem hy, τ⁻¹, inv_mem hτ, ?_⟩
        have : y * τ = τ * y := (Subgroup.mem_centralizer_iff.1 hτ.2 y hy)
        have h2 : y⁻¹ * τ⁻¹ = τ⁻¹ * y⁻¹ := (Commute.inv_inv this).eq
        rw [mul_inv_rev]
        exact h2 }
  have hle : layer Y ≤ M := by
    refine sSup_le fun L hL => ?_
    rcases CFSG.LocalCores.distinct_components_commute hL hI with h | h
    · rw [h]
      intro x hx
      exact ⟨x, hx, 1, one_mem _, by simp⟩
    · intro x hx
      have hxc : x ∈ Subgroup.centralizer (I : Set Y) := by
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        have := Subgroup.commutator_mem_commutator hx hg
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
        exact this.symm
      exact ⟨1, one_mem _, x, ⟨le_sSup hL hx, hxc⟩, by simp⟩
  exact fun x hx => hle hx

end Layer

section Exact

variable {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem commutator_self_of_quasisimple {I : Subgroup X} (hI : CFSG.IsQuasisimple ↥I) : ⁅I, I⁆ = I := by
  have h := congrArg (Subgroup.map I.subtype) (Group.isPerfect_def.mp hI.1)
  rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h

omit [Finite X] in
theorem component_inf_normal_central {I N : Subgroup X} (hI : IsComponent I) [N.Normal] (hIN : ¬ I ≤ N) :
    ∀ e ∈ I ⊓ N, ∀ i ∈ I, e * i = i * e := by
  intro e he i hi
  have hn : (N.subgroupOf I).Normal := Subgroup.normal_subgroupOf
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hI.1 hn with h | h
  · exact absurd (fun x hx => (Subgroup.mem_subgroupOf.1
      (h ▸ Subgroup.mem_top (⟨x, hx⟩ : I) : (⟨x, hx⟩ : I) ∈ N.subgroupOf I))) hIN
  · have : (⟨e, he.1⟩ : I) ∈ Subgroup.center I := h (Subgroup.mem_subgroupOf.2 he.2)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 this ⟨i, hi⟩).symm

theorem commute_of_commutator_mem_solvable {I O : Subgroup X} (hI : IsComponent I) [hOn : O.Normal]
    (hOs : Group.IsSolvable ↥O) {j : X} (hj : ∀ i ∈ I, ⁅j, i⁆ ∈ O) : ∀ i ∈ I, j * i = i * j := by
  have hIO : ¬ I ≤ O := CFSG.LocalAnalysis.ComponentInitial.not_le_of_isComponent_of_isSolvable hI hOs
  have hIq : ⁅I, I⁆ = I := commutator_self_of_quasisimple hI.1
  have hcO : ⁅I, O⁆ = ⊥ := (CFSG.LocalCores.component_solvable_centralizer hOs hOn.isSubnormal).1 I hI
  have hcomm : ∀ o ∈ O, ∀ i ∈ I, o * i = i * o := by
    intro o ho i hi
    have := Subgroup.commutator_mem_commutator hi ho
    rw [hcO, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  have hjI : ∀ i ∈ I, j * i * j⁻¹ ∈ I := by
    have hD : I.map (MulAut.conj j).toMonoidHom ≤ I := by
      refine perfect_le_of_solvable_commute (P := O) (T := I) ?_ ?_ ?_ hOs
      · rw [← Subgroup.map_commutator, hIq]
      · rintro _ ⟨i, hi, rfl⟩
        refine ⟨⁅j, i⁆, hj i hi, i, hi, ?_⟩
        simp [commutatorElement_def, MulAut.conj_apply]
      · exact hcomm
    intro i hi
    exact hD ⟨i, hi, by simp [MulAut.conj_apply]⟩
  refine centralizes_of_central_commutator hIq ?_
  intro x hx
  have hxO : ⁅j, x⁆ ∈ O := hj x hx
  have hxI : ⁅j, x⁆ ∈ I := by
    have h1 : j * x * j⁻¹ ∈ I := hjI x hx
    rw [commutatorElement_def]
    exact mul_mem h1 (inv_mem hx)
  refine ⟨hxI, ?_⟩
  exact component_inf_normal_central hI hIO ⁅j, x⁆ ⟨hxI, hxO⟩

end Exact

section BC

open CFSG.ClassicalInvolution CFSG.LocalAnalysis.ComponentInitial

theorem balance_commute {X : Type} [Group X] [Finite X] {a : X} (ha : a * a = 1) {I J : Subgroup X}
    (hI : IsComponent I) (hJq : IsQuasisimple ↥J) (hJC : J ≤ Subgroup.centralizer ({a} : Set X))
    (hJs : (J.subgroupOf (Subgroup.centralizer ({a} : Set X))).IsSubnormal)
    (haI : ∀ i ∈ I, a * i * a⁻¹ ∈ I)
    (hsolv : ∀ P : Subgroup X, P ≤ I →
      (∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ I ⊓ Subgroup.centralizer (I : Set X)) → Group.IsSolvable ↥P) :
    J ≤ Subgroup.centralizer (I : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup X := pPrimeCore 2 X with hO
  have hOn : O.Normal := pPrimeCore_normal
  have hOsolv : Group.IsSolvable ↥O := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have := pPrimeCore_coprime_card (p := 2) (G := X)
    exact (Nat.coprime_two_left.1 this)
  have hCz : Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) =
      Subgroup.centralizer ({a} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [← hCz] at hJC hJs
  set C : Subgroup X := Subgroup.centralizer ((Subgroup.zpowers a : Subgroup X) : Set X) with hC
  set π : X →* X ⧸ O := QuotientGroup.mk' O with hπ
  have hIO : ¬ I ≤ O := not_le_of_isComponent_of_isSolvable hI hOsolv
  have hIq : ⁅I, I⁆ = I := commutator_self_of_quasisimple hI.1
  have hJp : ⁅J, J⁆ = J := commutator_self_of_quasisimple hJq
  have hJcomp : IsComponent (J.subgroupOf C) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hJq, hJs⟩
  have hCO : Group.IsSolvable (pPrimeCore 2 ↥C) := by
    apply CFSG.FeitThompson.isSolvable_of_odd_natCard _
    have := pPrimeCore_coprime_card (p := 2) (G := ↥C)
    exact (Nat.coprime_two_left.1 this)
  have hJP : IsPComponent 2 (J.subgroupOf C) :=
    isPComponent_of_isComponent_of_not_le 2 hJcomp (not_le_of_isComponent_of_isSolvable hJcomp hCO)
  have hA : IsPGroup 2 (Subgroup.zpowers a) := by
    have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ha)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  have hJL : J ≤ pLayer X 2 := by
    have h1 := (Subgroup.map_mono (le_sSup hJP : J.subgroupOf C ≤ pLayer C 2)).trans
      (l2PrimeBalance X (Subgroup.zpowers a) hA)
    rwa [Subgroup.map_subgroupOf_eq_of_le hJC] at h1
  have hJE : J.map π ≤ layer (X ⧸ O) := by
    rw [← ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient (H := X) (p := 2)]
    exact Subgroup.map_mono hJL
  have hIc : IsComponent (I.map π) := component_quotient_image hI hIO
  set Ĩ : Subgroup (X ⧸ O) := I.map π with hĨdef
  set E : Subgroup (X ⧸ O) := layer (X ⧸ O) with hEdef
  set T : Subgroup (X ⧸ O) := E ⊓ Subgroup.centralizer (Ĩ : Set (X ⧸ O)) with hTdef
  have hdec : ∀ x ∈ E, ∃ y ∈ Ĩ, ∃ τ ∈ T, y * τ = x := layer_decomposition hIc
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  set ā : X ⧸ O := π a with hādef
  have hāĨ : ∀ y ∈ Ĩ, ā * y * ā⁻¹ ∈ Ĩ := by
    rintro _ ⟨i, hi, rfl⟩
    refine ⟨a * i * a⁻¹, haI i hi, ?_⟩
    simp [ā, map_mul, map_inv]
  have hEn : E.Normal := by
    have : E.Characteristic := CFSG.LocalCores.layer_characteristic (G := X ⧸ O)
    infer_instance
  have hāT : ∀ τ ∈ T, ā * τ * ā⁻¹ ∈ T := by
    intro τ hτ
    refine ⟨hEn.conj_mem τ hτ.1 ā, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro y hy
    have h1 : ā⁻¹ * y * ā ∈ Ĩ := by
      have := hāĨ y hy
      have hā2 : ā⁻¹ = ā := by simp [ā, ← map_inv, hainv]
      rw [hā2]
      simpa [hā2] using this
    have h2 := Subgroup.mem_centralizer_iff.1 hτ.2 _ h1
    calc y * (ā * τ * ā⁻¹) = ā * ((ā⁻¹ * y * ā) * τ) * ā⁻¹ := by group
      _ = ā * (τ * (ā⁻¹ * y * ā)) * ā⁻¹ := by rw [h2]
      _ = ā * τ * ā⁻¹ * y := by group
  have hTc : ∀ τ ∈ T, ∀ y ∈ Ĩ, y * τ = τ * y :=
    fun τ hτ y hy => Subgroup.mem_centralizer_iff.1 hτ.2 y hy
  let Pt : Subgroup (X ⧸ O) :=
    { carrier := {y | y ∈ Ĩ ∧ ∃ τ ∈ T, y * τ ∈ J.map π}
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, τ₁, hτ₁, h₁⟩ ⟨hy₂, τ₂, hτ₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, τ₁ * τ₂, mul_mem hτ₁ hτ₂, ?_⟩
        have : y₁ * y₂ * (τ₁ * τ₂) = (y₁ * τ₁) * (y₂ * τ₂) := by
          calc y₁ * y₂ * (τ₁ * τ₂) = y₁ * (y₂ * τ₁) * τ₂ := by simp only [mul_assoc]
            _ = y₁ * (τ₁ * y₂) * τ₂ := by rw [hTc τ₁ hτ₁ y₂ hy₂]
            _ = (y₁ * τ₁) * (y₂ * τ₂) := by simp only [mul_assoc]
        rw [this]
        exact mul_mem h₁ h₂
      inv_mem' := by
        rintro y ⟨hy, τ, hτ, h⟩
        refine ⟨inv_mem hy, τ⁻¹, inv_mem hτ, ?_⟩
        have : y⁻¹ * τ⁻¹ = (y * τ)⁻¹ := by
          rw [mul_inv_rev]
          exact (Commute.inv_inv (hTc τ hτ y hy)).eq
        rw [this]
        exact inv_mem h }
  set Ph : Subgroup X := Pt.comap π ⊓ I with hPhdef
  have hPhI : Ph ≤ I := inf_le_right
  have hPh : ∀ p ∈ Ph, a * p * a⁻¹ * p⁻¹ ∈ I ⊓ Subgroup.centralizer (I : Set X) := by
    intro p hp
    obtain ⟨hpPt, hpI⟩ := hp
    obtain ⟨hy, τ, hτ, j, hj, hjeq⟩ := hpPt
    have hmemI : a * p * a⁻¹ * p⁻¹ ∈ I := mul_mem (haI p hpI) (inv_mem hpI)
    refine ⟨hmemI, ?_⟩
    have hjC : a * j = j * a := Subgroup.mem_centralizer_iff.1 (hJC hj) a (Subgroup.mem_zpowers a)
    have hfix : ā * (π p * τ) * ā⁻¹ = π p * τ := by
      rw [← hjeq]
      calc ā * π j * ā⁻¹ = π (a * j * a⁻¹) := by simp [ā, map_mul, map_inv]
        _ = π j := by rw [hjC]; simp
    have hπe : π (a * p * a⁻¹ * p⁻¹) ∈ Subgroup.centralizer (Ĩ : Set (X ⧸ O)) := by
      set y := π p with hydef
      set u := ā * y * ā⁻¹ with hudef
      set τ' := ā * τ * ā⁻¹ with hτ'def
      have hτ'T : τ' ∈ T := hāT τ hτ
      have huτ : u * τ' = y * τ := by
        calc u * τ' = ā * (y * τ) * ā⁻¹ := by simp only [hudef, hτ'def]; group
          _ = y * τ := hfix
      have hζ : y⁻¹ * u = τ * τ'⁻¹ := by
        calc y⁻¹ * u = y⁻¹ * (u * τ') * τ'⁻¹ := by group
          _ = y⁻¹ * (y * τ) * τ'⁻¹ := by rw [huτ]
          _ = τ * τ'⁻¹ := by group
      have hζT : y⁻¹ * u ∈ T := by rw [hζ]; exact mul_mem hτ (inv_mem hτ'T)
      have hyζ : y * (y⁻¹ * u) = (y⁻¹ * u) * y := Subgroup.mem_centralizer_iff.1 hζT.2 y hy
      have : π (a * p * a⁻¹ * p⁻¹) = y⁻¹ * u := by
        calc π (a * p * a⁻¹ * p⁻¹) = u * y⁻¹ := by simp [hudef, ā, hydef, map_mul, map_inv]
          _ = y * (y⁻¹ * u) * y⁻¹ := by group
          _ = (y⁻¹ * u) * y * y⁻¹ := by rw [hyζ]
          _ = y⁻¹ * u := by group
      rw [this]
      exact hζT.2
    have hall : ∀ i ∈ I, ⁅a * p * a⁻¹ * p⁻¹, i⁆ ∈ I ⊓ O := by
      intro i hi
      rw [Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact mul_mem (mul_mem (mul_mem hmemI hi) (inv_mem hmemI)) (inv_mem hi)
      · have h1 := Subgroup.mem_centralizer_iff.1 hπe (π i) ⟨i, hi, rfl⟩
        have h2 : π ⁅a * p * a⁻¹ * p⁻¹, i⁆ = 1 := by
          rw [map_commutatorElement]
          exact commutatorElement_eq_one_iff_mul_comm.2 h1.symm
        exact (QuotientGroup.eq_one_iff _).1 h2
    have hcent := centralizes_of_central_commutator hIq (a := a * p * a⁻¹ * p⁻¹)
      (fun x hx => ⟨(Subgroup.mem_inf.1 (hall x hx)).1,
        fun y hy => component_inf_normal_central hI hIO _ (hall x hx) y hy⟩)
    exact Subgroup.mem_centralizer_iff.2 fun i hi => (hcent i hi).symm
  have hPsolv : Group.IsSolvable ↥Ph := hsolv Ph hPhI hPh
  have hPtsolv : Group.IsSolvable ↥Pt := by
    let φ : ↥Ph →* ↥Pt := (π.comp Ph.subtype).codRestrict Pt (fun p => p.2.1)
    have hφ : Function.Surjective φ := by
      rintro ⟨y, hy⟩
      obtain ⟨i, hi, rfl⟩ := hy.1
      exact ⟨⟨i, ⟨hy, hi⟩⟩, rfl⟩
    exact Group.isSolvable_of_surjective hφ
  have hD : ⁅J.map π, J.map π⁆ = J.map π := by rw [← Subgroup.map_commutator, hJp]
  have hdecJ : ∀ x ∈ J.map π, ∃ y ∈ Pt, ∃ τ ∈ T, y * τ = x := by
    intro x hx
    obtain ⟨y, hy, τ, hτ, rfl⟩ := hdec x (hJE hx)
    exact ⟨y, ⟨hy, τ, hτ, hx⟩, τ, hτ, rfl⟩
  have hle : J.map π ≤ T :=
    perfect_le_of_solvable_commute hD hdecJ (fun y hy τ hτ => hTc τ hτ y hy.1) hPtsolv
  have hcentJ : ∀ j ∈ J, ∀ i ∈ I, ⁅j, i⁆ ∈ O := by
    intro j hj i hi
    have hjT := hle ⟨j, hj, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hjT.2 (π i) ⟨i, hi, rfl⟩
    have h2 : π ⁅j, i⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 h1.symm
    exact (QuotientGroup.eq_one_iff _).1 h2
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  exact (commute_of_commutator_mem_solvable hI hOsolv (hcentJ j hj) i hi).symm

end BC


section Lift

variable {G : Type*} [Group G]

theorem lift_fixed {L : Subgroup G} (hodd : Odd (Nat.card (center ↥L))) {a : G} (ha : a * a = 1)
    (haN : a ∈ normalizer (L : Set G)) {xb : ↥L ⧸ center ↥L}
    (hfix : normalizerAct L ⟨a, haN⟩ xb = xb) :
    ∃ x : ↥L, a * (x : G) * a⁻¹ = x ∧ (QuotientGroup.mk x : ↥L ⧸ center ↥L) = xb := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective xb
  rw [normalizerAct_apply_mk] at hfix
  have hz : y⁻¹ * conjOn L ⟨a, haN⟩ y ∈ center ↥L := by
    rw [← QuotientGroup.eq]
    exact hfix.symm
  set α := conjOn L ⟨a, haN⟩ with hα
  set z : ↥L := y⁻¹ * α y with hzdef
  have hαy : α y = y * z := by rw [hzdef]; group
  have hα2 : ∀ x : ↥L, α (α x) = x := fun x => Subtype.ext (by
    simp only [hα, coe_conjOn]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a⁻¹ * a⁻¹) := by group
      _ = x := by
        have : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
        rw [ha, this, ha]; simp)
  have hαz : α z = z⁻¹ := by
    have h1 : α (α y) = y := hα2 y
    rw [hαy, map_mul, hαy] at h1
    have : y * z * α z = y := h1
    have h2 : z * α z = 1 := by
      calc z * α z = y⁻¹ * (y * z * α z) := by group
        _ = 1 := by rw [this]; group
    exact eq_inv_of_mul_eq_one_right h2
  obtain ⟨m, hm⟩ := hodd
  let zc : center ↥L := ⟨z, hz⟩
  have hzn : zc ^ Nat.card (center ↥L) = 1 := pow_card_eq_one'
  have hzn' : z ^ (2 * m + 1) = 1 := by
    have := congrArg (fun t : center ↥L => (t : ↥L)) hzn
    rw [hm] at this
    simpa using this
  set u : ↥L := z ^ (m + 1) with hu
  have hu2 : u * u = z := by
    rw [hu, ← pow_add]
    calc z ^ (m + 1 + (m + 1)) = z ^ (2 * m + 1) * z := by rw [← pow_succ]; congr 1; ring
      _ = z := by rw [hzn', one_mul]
  have hαu : α u = u⁻¹ := by
    rw [hu, map_pow, hαz, inv_pow]
  have huc : u ∈ center ↥L := Subgroup.pow_mem _ hz _
  refine ⟨y * u, ?_, ?_⟩
  · have h1 : α (y * u) = y * u := by
      rw [map_mul, hαy, hαu, mul_assoc, ← hu2]
      group
    have := congrArg Subtype.val h1
    simpa [hα, coe_conjOn] using this
  · exact (QuotientGroup.eq.2 (by simpa using inv_mem huc : (y * u)⁻¹ * y ∈ center ↥L)).symm ▸ rfl

end Lift



section LiftComp

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem perfect_le_of_central_coset {A B H Z : Subgroup G} (hB : ⁅B, B⁆ = B)
    (hAH : A ≤ H) (hZH : Z ≤ H) (hZ : ∀ z ∈ Z, ∀ h ∈ H, z * h = h * z)
    (hdec : ∀ b ∈ B, ∃ x ∈ A, ∃ z ∈ Z, x * z = b) : B ≤ A := by
  rw [← hB, Subgroup.commutator_le]
  intro b₁ hb₁ b₂ hb₂
  obtain ⟨x₁, hx₁, z₁, hz₁, rfl⟩ := hdec b₁ hb₁
  obtain ⟨x₂, hx₂, z₂, hz₂, rfl⟩ := hdec b₂ hb₂
  have c11 : Commute x₁ z₁ := (hZ z₁ hz₁ x₁ (hAH hx₁)).symm
  have c12 : Commute x₁ z₂ := (hZ z₂ hz₂ x₁ (hAH hx₁)).symm
  have c21 : Commute x₂ z₁ := (hZ z₁ hz₁ x₂ (hAH hx₂)).symm
  have c22 : Commute x₂ z₂ := (hZ z₂ hz₂ x₂ (hAH hx₂)).symm
  rw [commutator_mul_mul_of_commute c11 c12 c21 c22]
  have : ⁅z₁, z₂⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact hZ z₁ hz₁ z₂ (hZH hz₂)
  rw [this, mul_one, commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem hx₁ hx₂) (inv_mem hx₁)) (inv_mem hx₂)


omit [Finite G] in
theorem exists_lift_component {L : Subgroup G} (hodd : Odd (Nat.card (center ↥L))) {a : G} (ha : a * a = 1)
    (haN : a ∈ normalizer (L : Set G)) {N : Subgroup (↥L ⧸ center ↥L)} (hNq : CFSG.IsQuasisimple ↥N)
    (hNfix : ∀ n ∈ N, normalizerAct L ⟨a, haN⟩ n = n)
    (hNnorm : ∀ x, normalizerAct L ⟨a, haN⟩ x = x → ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    ∃ J : Subgroup G, J ≤ L ⊓ Subgroup.centralizer ({a} : Set G) ∧ CFSG.IsQuasisimple ↥J ∧
      ∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ y ∈ J, x * y * x⁻¹ ∈ J := by
  classical
  set π : ↥L →* ↥L ⧸ center ↥L := QuotientGroup.mk' (center ↥L) with hπ
  set Ñ : Subgroup G := (N.comap π).map L.subtype with hÑ
  set E : Subgroup G := Ñ ⊓ Subgroup.centralizer ({a} : Set G) with hE
  have hÑL : Ñ ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hEL : E ≤ L := inf_le_left.trans hÑL
  have hmemÑ : ∀ x : ↥L, (x : G) ∈ Ñ ↔ π x ∈ N := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
    · intro h
      exact ⟨x, h, rfl⟩
  have hfixπ : ∀ x : ↥L, a * x = x * a → normalizerAct L ⟨a, haN⟩ (π x) = π x := by
    intro x hx
    have h1 : normalizerAct L ⟨a, haN⟩ (QuotientGroup.mk x) = QuotientGroup.mk (conjOn L ⟨a, haN⟩ x) :=
      normalizerAct_apply_mk L ⟨a, haN⟩ x
    have h2 : conjOn L ⟨a, haN⟩ x = x := Subtype.ext (by
      rw [coe_conjOn]
      calc a * (x : G) * a⁻¹ = (x * a) * a⁻¹ := by rw [← hx]
        _ = x := by group)
    exact h1.trans (by rw [h2]; rfl)
  have hconjE : ∀ x ∈ L ⊓ Subgroup.centralizer ({a} : Set G), ∀ e ∈ E, x * e * x⁻¹ ∈ E := by
    intro x hx e he
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxL, hxc⟩ := hx
    have hxa : x * a = a * x := mem_centralizer_singleton_iff.1 hxc
    have heL : e ∈ L := hEL he
    refine ⟨?_, ?_⟩
    · have hfx := hfixπ ⟨x, hxL⟩ hxa.symm
      have hen : π ⟨e, heL⟩ ∈ N := (hmemÑ ⟨e, heL⟩).1 he.1
      have := hNnorm _ hfx _ hen
      have hmem : x * e * x⁻¹ ∈ L := mul_mem (mul_mem hxL heL) (inv_mem hxL)
      refine (hmemÑ ⟨x * e * x⁻¹, hmem⟩).2 ?_
      have hsub : (⟨x * e * x⁻¹, hmem⟩ : ↥L) = ⟨x, hxL⟩ * ⟨e, heL⟩ * ⟨x, hxL⟩⁻¹ := rfl
      rw [hsub, map_mul, map_mul, map_inv]
      exact this
    · have hea : e * a = a * e := mem_centralizer_singleton_iff.1 he.2
      refine mem_centralizer_singleton_iff.2 ?_
      calc x * e * x⁻¹ * a = x * e * (x⁻¹ * a) := by rw [mul_assoc]
        _ = x * e * (a * x⁻¹) := by
            congr 1
            calc x⁻¹ * a = x⁻¹ * (a * x) * x⁻¹ := by group
              _ = x⁻¹ * (x * a) * x⁻¹ := by rw [hxa]
              _ = a * x⁻¹ := by group
        _ = x * (e * a) * x⁻¹ := by group
        _ = x * (a * e) * x⁻¹ := by rw [hea]
        _ = a * (x * e * x⁻¹) := by
            calc x * (a * e) * x⁻¹ = (x * a) * e * x⁻¹ := by group
              _ = (a * x) * e * x⁻¹ := by rw [hxa]
              _ = a * (x * e * x⁻¹) := by group
  have hJE : ⁅E, E⁆ ≤ E := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hx hy) (inv_mem hx)) (inv_mem hy)
  refine ⟨⁅E, E⁆, ?_, ?_, ?_⟩
  · intro x hx
    exact ⟨hEL (hJE hx), (hJE hx).2⟩
  · let fE : ↥E →* ↥N := (π.comp (Subgroup.inclusion hEL)).codRestrict N
      (fun e => (hmemÑ ⟨e, hEL e.2⟩).1 e.2.1)
    have hsurj : Function.Surjective fE := by
      intro n
      obtain ⟨x, hx, hπx⟩ := lift_fixed hodd ha haN (hNfix n n.2)
      have hxN : π x ∈ N := by
        show (QuotientGroup.mk x : ↥L ⧸ center ↥L) ∈ N
        rw [hπx]
        exact n.2
      have hxE : (x : G) ∈ E := ⟨(hmemÑ x).2 hxN, mem_centralizer_singleton_iff.2 (by
        calc (x : G) * a = (a * x * a⁻¹) * a := by rw [hx]
          _ = a * x := by group)⟩
      refine ⟨⟨x, hxE⟩, Subtype.ext ?_⟩
      exact hπx
    have hker : fE.ker ≤ center ↥E := by
      intro e he
      have h1 : π ⟨e, hEL e.2⟩ = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 he)
      have hcL : (⟨e, hEL e.2⟩ : ↥L) ∈ center ↥L := (QuotientGroup.eq_one_iff _).1 h1
      rw [Subgroup.mem_center_iff]
      intro g
      have h := Subgroup.mem_center_iff.1 hcL ⟨g, hEL g.2⟩
      have h' : (g : G) * e = e * g := congrArg Subtype.val h
      exact Subtype.ext h'
    have hq := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective fE hsurj hker hNq
    have hcomm : (commutator ↥E).map E.subtype = ⁅E, E⁆ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype]
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((Subgroup.equivMapOfInjective _ E.subtype E.subtype_injective).trans
        (MulEquiv.subgroupCongr hcomm)) hq
  · intro x hx y hy
    refine commutator_induction (C := fun y => x * y * x⁻¹ ∈ ⁅E, E⁆) hy ?_ (by simp) ?_ ?_
    · intro e₁ he₁ e₂ he₂
      have := Subgroup.commutator_mem_commutator (hconjE x hx e₁ he₁) (hconjE x hx e₂ he₂)
      have heq : x * ⁅e₁, e₂⁆ * x⁻¹ = ⁅x * e₁ * x⁻¹, x * e₂ * x⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [heq]
      exact this
    · intro y₁ y₂ h₁ h₂
      have : x * (y₁ * y₂) * x⁻¹ = (x * y₁ * x⁻¹) * (x * y₂ * x⁻¹) := by group
      rw [this]
      exact mul_mem h₁ h₂
    · intro y₁ h₁
      have : x * y₁⁻¹ * x⁻¹ = (x * y₁ * x⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem h₁

end LiftComp



section Sub

theorem isSubnormal_of_chain {G : Type*} [Group G] {J M₁ M₂ : Subgroup G} (hJM : J ≤ M₁)
    (hJ : ∀ x ∈ M₁, ∀ y ∈ J, x * y * x⁻¹ ∈ J) (hM : ∀ x ∈ M₂, ∀ y ∈ M₁, x * y * x⁻¹ ∈ M₁) :
    (J.subgroupOf M₂).IsSubnormal := by
  refine Subgroup.IsSubnormal.step (J.subgroupOf M₂) (M₁.subgroupOf M₂) ?_ ?_ ?_
  · intro x hx
    exact hJM hx
  · refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    exact hM g g.2 n hn
  · refine ⟨fun n hn g => ?_⟩
    exact hJ g g.2 n hn

theorem balance_commute_sub {G : Type} [Group G] [Finite G] {Cv : Subgroup G} {a : G} (haC : a ∈ Cv)
    (ha : a * a = 1) {I J M : Subgroup G} (hIC : I ≤ Cv) (hI : IsComponent (I.subgroupOf Cv))
    (hJq : IsQuasisimple ↥J) (hJM : J ≤ M) (hMC : M ≤ Cv ⊓ Subgroup.centralizer ({a} : Set G))
    (hJnorm : ∀ x ∈ M, ∀ y ∈ J, x * y * x⁻¹ ∈ J)
    (hMnorm : ∀ x ∈ Cv ⊓ Subgroup.centralizer ({a} : Set G), ∀ y ∈ M, x * y * x⁻¹ ∈ M)
    (haI : ∀ i ∈ I, a * i * a⁻¹ ∈ I)
    (hsolv : ∀ P : Subgroup G, P ≤ I →
      (∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ I ⊓ Subgroup.centralizer (I : Set G)) → Group.IsSolvable ↥P) :
    J ≤ Subgroup.centralizer (I : Set G) := by
  have hJC : J ≤ Cv := fun x hx => (hMC (hJM hx)).1
  let a' : ↥Cv := ⟨a, haC⟩
  have ha' : a' * a' = 1 := Subtype.ext ha
  have hcen : (Cv ⊓ Subgroup.centralizer ({a} : Set G)).subgroupOf Cv =
      Subgroup.centralizer ({a'} : Set ↥Cv) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, h⟩
      exact Subtype.ext h
    · intro h
      exact ⟨x.2, congrArg Subtype.val h⟩
  have hJs : ((J.subgroupOf Cv).subgroupOf (Subgroup.centralizer ({a'} : Set ↥Cv))).IsSubnormal := by
    refine isSubnormal_of_chain (J := J.subgroupOf Cv) (M₁ := M.subgroupOf Cv)
      (M₂ := Subgroup.centralizer ({a'} : Set ↥Cv)) (fun x hx => hJM hx) ?_ ?_
    · intro x hx y hy
      exact hJnorm x hx y hy
    · intro x hx y hy
      have hx' : (x : G) ∈ Subgroup.centralizer ({a} : Set G) := by
        have := Subgroup.mem_centralizer_singleton_iff.1 hx
        exact mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
      exact hMnorm x ⟨x.2, hx'⟩ y hy
  have hJq' : IsQuasisimple ↥(J.subgroupOf Cv) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJC).symm hJq
  have hJC' : J.subgroupOf Cv ≤ Subgroup.centralizer ({a'} : Set ↥Cv) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (mem_centralizer_singleton_iff.1 (hMC (hJM hx)).2)
  have haI' : ∀ i ∈ I.subgroupOf Cv, a' * i * a'⁻¹ ∈ I.subgroupOf Cv := fun i hi => haI i hi
  have hsolv' : ∀ P' : Subgroup ↥Cv, P' ≤ I.subgroupOf Cv →
      (∀ p ∈ P', a' * p * a'⁻¹ * p⁻¹ ∈ (I.subgroupOf Cv) ⊓
        Subgroup.centralizer ((I.subgroupOf Cv : Subgroup ↥Cv) : Set ↥Cv)) → Group.IsSolvable ↥P' := by
    intro P' hP'I hP'
    have hP : (P'.map Cv.subtype) ≤ I := by
      rintro _ ⟨x, hx, rfl⟩
      exact hP'I hx
    have hPcond : ∀ p ∈ P'.map Cv.subtype, a * p * a⁻¹ * p⁻¹ ∈ I ⊓ Subgroup.centralizer (I : Set G) := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨h1, h2⟩ := hP' x hx
      refine ⟨h1, Subgroup.mem_centralizer_iff.2 fun i hi => ?_⟩
      have := Subgroup.mem_centralizer_iff.1 h2 ⟨i, hIC hi⟩ hi
      exact congrArg Subtype.val this
    have hsol := hsolv _ hP hPcond
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective P' Cv.subtype Cv.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective P' Cv.subtype Cv.subtype_injective).injective
  have key := balance_commute (X := ↥Cv) (a := a') ha' hI hJq' hJC' hJs haI' hsolv'
  intro j hj
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  have hjx : (⟨j, hJC hj⟩ : ↥Cv) ∈ J.subgroupOf Cv := hj
  have hix : (⟨i, hIC hi⟩ : ↥Cv) ∈ (I.subgroupOf Cv : Subgroup ↥Cv) := hi
  have := Subgroup.mem_centralizer_iff.1 (key hjx) ⟨i, hIC hi⟩ hix
  exact congrArg Subtype.val this

end Sub


end CFSG.GH74.KGroups.Bal
