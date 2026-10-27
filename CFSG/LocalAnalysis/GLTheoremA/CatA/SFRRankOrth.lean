module

public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoTv
public import CFSG.LocalAnalysis.GLTheoremA.CatA.SFRRankLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.SFRRank

open scoped commutatorElement
open Module QuadraticMap CFSG.Open
open CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two
open CFSG.RankThree.OrthogonalInvolutions (polar_self_eq_zero)

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private def perpPair (Q : QuadraticForm K V) (S : Submodule K V) (u v : V) : Submodule K V :=
  S ⊓ LinearMap.ker (polarBilin Q u) ⊓ LinearMap.ker (polarBilin Q v)

private theorem mem_perpPair {S : Submodule K V} {u v x : V} :
    x ∈ perpPair Q S u v ↔ x ∈ S ∧ polar Q u x = 0 ∧ polar Q v x = 0 := by
  simp only [perpPair, Submodule.mem_inf, LinearMap.mem_ker, polarBilin_apply_apply, and_assoc]

private theorem perpPair_le (S : Submodule K V) (u v : V) : perpPair Q S u v ≤ S :=
  fun _ hx => (mem_perpPair.1 hx).1

private def PolarNondeg (Q : QuadraticForm K V) (S : Submodule K V) : Prop :=
  ∀ y ∈ S, y ≠ 0 → ∃ z ∈ S, polar Q y z = 1

private theorem finrank_le_inf_ker [FiniteDimensional K V] (S : Submodule K V) (g : V →ₗ[K] K) :
    finrank K S ≤ finrank K ↥(S ⊓ LinearMap.ker g) + 1 := by
  have h1 := Submodule.finrank_sup_add_finrank_inf_eq S (LinearMap.ker g)
  have h2 := LinearMap.finrank_range_add_finrank_ker g
  have h3 : finrank K ↥(LinearMap.range g) ≤ 1 :=
    (Submodule.finrank_le _).trans (Module.finrank_self K).le
  have h4 : finrank K ↥(S ⊔ LinearMap.ker g) ≤ finrank K V := Submodule.finrank_le _
  omega

private theorem finrank_perpPair [FiniteDimensional K V] (S : Submodule K V) (u v : V) :
    finrank K S ≤ finrank K (perpPair Q S u v) + 2 := by
  have h1 := finrank_le_inf_ker S (polarBilin Q u)
  have h2 := finrank_le_inf_ker (S ⊓ LinearMap.ker (polarBilin Q u)) (polarBilin Q v)
  change finrank K S ≤ finrank K
    ↥(S ⊓ LinearMap.ker (polarBilin Q u) ⊓ LinearMap.ker (polarBilin Q v)) + 2
  omega

private theorem exists_ne_zero_of_finrank_pos {S : Submodule K V} (h : 0 < finrank K S) :
    ∃ y ∈ S, y ≠ 0 := by
  have hS : S ≠ ⊥ := by
    rintro rfl
    simp at h
  exact Submodule.exists_mem_ne_zero_of_ne_bot hS

private theorem exists_quad_one (hK : Nat.card K = 2) {S : Submodule K V} (hS : PolarNondeg Q S)
    {y : V} (hy : y ∈ S) (hy0 : y ≠ 0) : ∃ d ∈ S, Q d = 1 := by
  obtain ⟨z, hzS, hyz⟩ := hS y hy hy0
  rcases card_two_cases' hK (Q y) with h1 | h1
  · rcases card_two_cases' hK (Q z) with h2 | h2
    · refine ⟨y + z, S.add_mem hy hzS, ?_⟩
      rw [QuadraticMap.map_add Q y z, h1, h2, hyz, zero_add, zero_add]
    · exact ⟨z, hzS, h2⟩
  · exact ⟨y, hy, h1⟩

private theorem derived_le_orth :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ≤
      TauCeti.QuadraticMap.orthogonalGroup Q :=
  Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

variable [CharP K 2]

private theorem polarNondeg_perpPair {S : Submodule K V} (hS : PolarNondeg Q S) {u v : V}
    (hu : u ∈ S) (hv : v ∈ S) (huv : polar Q u v = 1) : PolarNondeg Q (perpPair Q S u v) := by
  have hvu : polar Q v u = 1 := by rw [polar_comm]; exact huv
  intro y hy hy0
  obtain ⟨hyS, hyu, hyv⟩ := mem_perpPair.1 hy
  have hyu' : polar Q y u = 0 := by rw [polar_comm]; exact hyu
  have hyv' : polar Q y v = 0 := by rw [polar_comm]; exact hyv
  obtain ⟨z, hzS, hyz⟩ := hS y hyS hy0
  refine ⟨z + polar Q v z • u + polar Q u z • v, mem_perpPair.2 ⟨?_, ?_, ?_⟩, ?_⟩
  · exact S.add_mem (S.add_mem hzS (S.smul_mem _ hu)) (S.smul_mem _ hv)
  · simp only [polar_add_right, polar_smul_right, polar_self_eq_zero, huv, smul_eq_mul, mul_zero,
      add_zero, mul_one, CharTwo.add_self_eq_zero]
  · simp only [polar_add_right, polar_smul_right, polar_self_eq_zero, hvu, smul_eq_mul, mul_zero,
      add_zero, mul_one, CharTwo.add_self_eq_zero]
  · simp only [polar_add_right, polar_smul_right, hyu', hyv', smul_eq_mul, mul_zero, add_zero, hyz]

private theorem exists_pair (hK : Nat.card K = 2) [FiniteDimensional K V] {a : V ≃ₗ[K] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h3 : ∀ x, a (a (a x)) = x)
    {S : Submodule K V} (hSa : ∀ x ∈ S, a x ∈ S) (hS : PolarNondeg Q S) (h4 : 4 ≤ finrank K S) :
    ∃ u ∈ S, ∃ v ∈ S, Q u = 1 ∧ Q v = 1 ∧ polar Q u v = 1 ∧
      ((a u = u ∧ a v = v) ∨ (a u = v ∧ a v = u + v)) := by
  have hQa : ∀ x, Q (a x) = Q x := fun x =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup ha x
  have hpa : ∀ x y, polar Q (a x) (a y) = polar Q x y :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ha
  have hadd : ∀ x y, Q (x + y) = Q x + Q y + polar Q x y := fun x y => QuadraticMap.map_add Q x y
  by_cases hfix : ∀ x ∈ S, a x = x
  ·
    obtain ⟨y, hy, hy0⟩ := exists_ne_zero_of_finrank_pos (S := S) (by omega)
    obtain ⟨d, hdS, hd⟩ := exists_quad_one hK hS hy hy0
    have hd0 : d ≠ 0 := by
      rintro rfl
      simp at hd
    obtain ⟨z, hzS, hdz⟩ := hS d hdS hd0
    rcases card_two_cases' hK (Q z) with hz | hz
    · have hP := polarNondeg_perpPair hS hdS hzS hdz
      have hdim := finrank_perpPair (Q := Q) S d z
      obtain ⟨w0, hw0, hw00⟩ := exists_ne_zero_of_finrank_pos (S := perpPair Q S d z) (by omega)
      obtain ⟨w, hwP, hw⟩ := exists_quad_one hK hP hw0 hw00
      obtain ⟨hwS, hdw, hzw⟩ := mem_perpPair.1 hwP
      refine ⟨d, hdS, z + w, S.add_mem hzS hwS, hd, ?_, ?_,
        Or.inl ⟨hfix d hdS, hfix _ (S.add_mem hzS hwS)⟩⟩
      · rw [hadd, hz, hw, hzw, zero_add, add_zero]
      · rw [polar_add_right, hdz, hdw, add_zero]
    · exact ⟨d, hdS, z, hzS, hd, hz, hdz, Or.inl ⟨hfix d hdS, hfix z hzS⟩⟩
  ·
    have finish : ∀ w ∈ S, a (a w) = a w + w → Q w = 1 →
        ∃ u ∈ S, ∃ v ∈ S, Q u = 1 ∧ Q v = 1 ∧ polar Q u v = 1 ∧
          ((a u = u ∧ a v = v) ∨ (a u = v ∧ a v = u + v)) := by
      intro w hwS hw hQw
      refine ⟨w, hwS, a w, hSa w hwS, hQw, by rw [hQa, hQw], ?_, Or.inr ⟨rfl, by rw [hw, add_comm]⟩⟩
      have h1 : Q (a (a w)) = Q w := by rw [hQa, hQa]
      rw [hw, hadd, hQa, hQw, CharTwo.add_self_eq_zero, zero_add] at h1
      rw [polar_comm]
      exact h1
    push Not at hfix
    obtain ⟨x, hxS, hx⟩ := hfix
    obtain ⟨y, hydef⟩ : ∃ y, y = a x + x := ⟨_, rfl⟩
    have hyS : y ∈ S := by rw [hydef]; exact S.add_mem (hSa x hxS) hxS
    have hy0 : y ≠ 0 := by
      rintro h
      apply hx
      rw [hydef] at h
      calc a x = a x + (x + x) := by rw [add_self_vec K x, add_zero]
        _ = (a x + x) + x := by abel
        _ = x := by rw [h, zero_add]
    have haay : a (a y) = a y + y := by
      rw [hydef]
      simp only [map_add, h3]
      rw [show a (a x) + a x + (a x + x) = x + a (a x) + (a x + a x) by abel,
        add_self_vec K (a x), add_zero]
    rcases card_two_cases' hK (Q y) with hQy | hQy
    · obtain ⟨z, hzS, hyz⟩ := hS y hyS hy0
      obtain ⟨z₁, hz₁⟩ : ∃ z₁, z₁ = a z + a (a z) := ⟨_, rfl⟩
      have hz₁S : z₁ ∈ S := by rw [hz₁]; exact S.add_mem (hSa z hzS) (hSa _ (hSa z hzS))
      have haaz : a (a z₁) = a z₁ + z₁ := by
        rw [hz₁]
        simp only [map_add, h3]
        rw [show a (a z) + z + (a z + a (a z)) = z + a z + (a (a z) + a (a z)) by abel,
          add_self_vec K (a (a z)), add_zero]
      have e1 : polar Q y (a z) = polar Q (a (a y)) z := by
        calc polar Q y (a z) = polar Q (a (a y)) (a (a (a z))) := by rw [hpa, hpa]
          _ = polar Q (a (a y)) z := by rw [h3]
      have e2 : polar Q y (a (a z)) = polar Q (a y) z := by
        calc polar Q y (a (a z)) = polar Q (a y) (a (a (a z))) := by rw [hpa]
          _ = polar Q (a y) z := by rw [h3]
      have hyz₁ : polar Q y z₁ = 1 := by
        rw [hz₁, polar_add_right, e1, e2, ← polar_add_left, haay,
          show a y + y + a y = y by rw [add_comm (a y) y, add_assoc, add_self_vec K (a y), add_zero],
          hyz]
      rcases card_two_cases' hK (Q z₁) with hQz | hQz
      · refine finish (y + z₁) (S.add_mem hyS hz₁S) ?_ ?_
        · rw [map_add, map_add, haay, haaz]
          abel
        · rw [hadd, hQy, hQz, hyz₁, zero_add, zero_add]
      · exact finish z₁ hz₁S haaz hQz
    · exact finish y hyS haay hQy

private theorem perpPair_inv {a : V ≃ₗ[K] V} (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {S : Submodule K V} (hSa : ∀ x ∈ S, a x ∈ S) {u v : V}
    (hD : (a u = u ∧ a v = v) ∨ (a u = v ∧ a v = u + v)) :
    ∀ x ∈ perpPair Q S u v, a x ∈ perpPair Q S u v := by
  have hpa : ∀ x y, polar Q (a x) (a y) = polar Q x y :=
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup ha
  intro x hx
  obtain ⟨hxS, hux, hvx⟩ := mem_perpPair.1 hx
  refine mem_perpPair.2 ⟨hSa x hxS, ?_, ?_⟩
  · rcases hD with ⟨hu, -⟩ | ⟨hu, hv⟩
    · rw [← hu, hpa, hux]
    · have h1 : a (u + v) = u := by
        rw [map_add, hu, hv, add_left_comm, add_self_vec K v, add_zero]
      rw [← h1, hpa, polar_add_left, hux, hvx, add_zero]
  · rcases hD with ⟨-, hv⟩ | ⟨hu, -⟩
    · rw [← hv, hpa, hvx]
    · rw [← hu, hpa, hux]

private theorem rot_mem_derived {u v : V} (hQu : Q u = 1) (hQv : Q v = 1)
    (huv : polar Q u v = 1) :
    rot Q u v ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have h1 : ⁅tv Q u, tv Q v⁆ = rot Q u v ^ 2 := by
    simp only [commutatorElement_def, tv_inv, rot_eq_mul, pow_two, mul_assoc]
  have h2 : (rot Q u v ^ 2) ^ 2 = rot Q u v := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_succ, rot_cube huv, one_mul]
  rw [← h2, ← h1]
  exact Subgroup.pow_mem _ (Subgroup.commutator_mem_commutator (tv_mem hQu) (tv_mem hQv)) 2

private theorem rot_comm_a {a : V ≃ₗ[K] V} (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {u v : V} (hQu : Q u = 1) (huv : polar Q u v = 1)
    (hD : (a u = u ∧ a v = v) ∨ (a u = v ∧ a v = u + v)) : a * rot Q u v = rot Q u v * a := by
  rcases hD with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact rot_comm_of_fixed ha hu hv
  · have h1 := rot_conj ha u v
    rw [hu, hv, (rot_cyc hQu huv).1] at h1
    calc a * rot Q u v = a * rot Q u v * a⁻¹ * a := by group
      _ = rot Q u v * a := by rw [h1]

private theorem exists_elemAb_orth_aux (hK : Nat.card K = 2) [FiniteDimensional K V]
    {a : V ≃ₗ[K] V} (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (h3 : ∀ x, a (a (a x)) = x) (j : ℕ) :
    ∀ S : Submodule K V, (∀ x ∈ S, a x ∈ S) → PolarNondeg Q S → 2 * j + 2 ≤ finrank K S →
      ∃ T : Subgroup (V ≃ₗ[K] V),
        T ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
        (∀ t ∈ T, t * a = a * t) ∧ IsElemAbelian 3 T ∧ Nat.card T = 3 ^ j ∧
        ∀ t ∈ T, ∀ x : V, (∀ s ∈ S, polar Q s x = 0) → t x = x := by
  induction j with
  | zero =>
    intro S _ _ _
    refine ⟨⊥, bot_le, ?_, isElemAbelian_of_forall _ ?_ ?_, by simp, ?_⟩
    · intro t ht
      rw [Subgroup.mem_bot.1 ht, one_mul, mul_one]
    · intro x hx y hy
      rw [Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]
    · intro x hx
      rw [Subgroup.mem_bot.1 hx, one_pow]
    · intro t ht x _
      obtain rfl := Subgroup.mem_bot.1 ht
      rfl
  | succ j ih =>
    intro S hSa hS hdim
    obtain ⟨u, hu, v, hv, hQu, hQv, huv, hD⟩ := exists_pair hK ha h3 hSa hS (by omega)
    have hS'd := finrank_perpPair (Q := Q) S u v
    obtain ⟨T', hT'Ω, hT'a, hT'e, hT'c, hT'f⟩ :=
      ih (perpPair Q S u v) (perpPair_inv ha hSa hD) (polarNondeg_perpPair hS hu hv huv)
        (by omega)
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    set e := rot Q u v with he
    have he3 : e ^ 3 = 1 := rot_cube huv
    have heΩ : e ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
      rot_mem_derived hQu hQv huv
    have hea : Commute e a := (rot_comm_a ha hQu huv hD).symm
    have hT'u : ∀ t ∈ T', t u = u := fun t ht => hT'f t ht u fun s hs => by
      rw [polar_comm]; exact (mem_perpPair.1 hs).2.1
    have hT'v : ∀ t ∈ T', t v = v := fun t ht => hT'f t ht v fun s hs => by
      rw [polar_comm]; exact (mem_perpPair.1 hs).2.2
    have hcomm : ∀ t ∈ T', Commute t e := fun t ht =>
      rot_comm_of_fixed (derived_le_orth (hT'Ω ht)) (hT'u t ht) (hT'v t ht)
    have hT'comm : ∀ x ∈ T', ∀ y ∈ T', Commute x y := fun x hx y hy =>
      congrArg Subtype.val (hT'e.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hfin : IsOfFinOrder e := isOfFinOrder_iff_pow_eq_one.2 ⟨3, by norm_num, he3⟩
    have hzp : ∀ s ∈ Subgroup.zpowers e, ∃ n : ℕ, e ^ n = s := fun s hs =>
      (Submonoid.mem_powers_iff _ _).1 (hfin.mem_powers_iff_mem_zpowers.2 hs)
    have he1 : e ≠ 1 := by
      intro h
      have h1 : e u = v := rot_a huv
      rw [h] at h1
      have h2 : u = v := h1
      rw [← h2, polar_self_eq_zero] at huv
      exact zero_ne_one huv
    have horder : orderOf e = 3 := orderOf_eq_prime he3 he1
    have hpair : ∀ (t : T') (s : Subgroup.zpowers e),
        Commute (T'.subtype t) ((Subgroup.zpowers e).subtype s) := by
      rintro ⟨t, ht⟩ ⟨s, hs⟩
      obtain ⟨n, rfl⟩ := hzp s hs
      exact (hcomm t ht).pow_right n
    set ψ := MonoidHom.noncommCoprod T'.subtype (Subgroup.zpowers e).subtype hpair with hψ
    have hψapp : ∀ (t : T') (s : Subgroup.zpowers e), ψ (t, s) = (t : V ≃ₗ[K] V) * s :=
      fun _ _ => rfl
    have hinj : Function.Injective ψ := by
      refine (injective_iff_map_eq_one ψ).2 ?_
      rintro ⟨⟨t, ht⟩, ⟨s, hs⟩⟩ hp
      have hp' : t * s = 1 := hp
      obtain ⟨n, rfl⟩ := hzp s hs
      have hnu : (e ^ n) u = u := by
        have h2 : e ^ n * t = 1 := by rw [← ((hcomm t ht).pow_right n).eq]; exact hp'
        have h1 := congrArg (fun f : V ≃ₗ[K] V => f u) h2
        simp only [LinearEquiv.mul_apply, hT'u t ht] at h1
        exact h1
      have hen : e ^ n = 1 := by
        obtain ⟨k, rfl⟩ := three_dvd_of_rot_pow_apply_eq huv hnu
        rw [pow_mul, he3, one_pow]
      rw [hen, mul_one] at hp'
      exact Prod.ext (Subtype.ext hp') (Subtype.ext hen)
    have hmem : ∀ y ∈ ψ.range, ∃ t ∈ T', ∃ n : ℕ, y = t * e ^ n := by
      intro y hy
      obtain ⟨⟨⟨t, ht⟩, ⟨s, hs⟩⟩, rfl⟩ := MonoidHom.mem_range.1 hy
      obtain ⟨n, rfl⟩ := hzp s hs
      exact ⟨t, ht, n, hψapp _ _⟩
    have hefix : ∀ x : V, (∀ s ∈ S, polar Q s x = 0) → ∀ n : ℕ, (e ^ n) x = x := by
      intro x hx n
      have h1 : e x = x := by
        rw [he, rot_apply huv, hx u hu, hx v hv, zero_smul, zero_smul, add_zero, add_zero]
      induction n with
      | zero => rw [pow_zero]; rfl
      | succ n ihn => rw [pow_succ, LinearEquiv.mul_apply, h1, ihn]
    refine ⟨ψ.range, ?_, ?_, isElemAbelian_of_forall _ ?_ ?_, ?_, ?_⟩
    · intro y hy
      obtain ⟨t, ht, n, rfl⟩ := hmem y hy
      exact mul_mem (hT'Ω ht) (Subgroup.pow_mem _ heΩ n)
    · intro y hy
      obtain ⟨t, ht, n, rfl⟩ := hmem y hy
      have hta : Commute t a := hT'a t ht
      exact (hta.mul_left (hea.pow_left n)).eq
    · intro y₁ hy₁ y₂ hy₂
      obtain ⟨t₁, ht₁, n₁, rfl⟩ := hmem y₁ hy₁
      obtain ⟨t₂, ht₂, n₂, rfl⟩ := hmem y₂ hy₂
      have hc : Commute (t₁ * e ^ n₁) (t₂ * e ^ n₂) :=
        Commute.mul_left (Commute.mul_right (hT'comm t₁ ht₁ t₂ ht₂) ((hcomm t₁ ht₁).pow_right n₂))
          (Commute.mul_right ((hcomm t₂ ht₂).pow_right n₁).symm (Commute.pow_pow_self e n₁ n₂))
      exact hc.eq
    · intro y hy
      obtain ⟨t, ht, n, rfl⟩ := hmem y hy
      rw [((hcomm t ht).pow_right n).mul_pow, hT'e.2 t ht, one_mul, ← pow_mul, mul_comm, pow_mul,
        he3, one_pow]
    · rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hT'c,
        Nat.card_zpowers, horder, pow_succ]
    · intro y hy x hx
      obtain ⟨t, ht, n, rfl⟩ := hmem y hy
      rw [LinearEquiv.mul_apply, hefix x hx n]
      exact hT'f t ht x fun s hs => hx s (perpPair_le S u v hs)

theorem exists_elemAb81_orth (hK : Nat.card K = 2) [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 10 ≤ finrank K V) {a : V ≃ₗ[K] V}
    (ha : a ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (h3 : a ^ 3 = 1) :
    ∃ E : Subgroup (V ≃ₗ[K] V),
      E ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
      E ≤ Subgroup.centralizer {a} ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have h3' : ∀ x, a (a (a x)) = x := fun x => by
    have h1 : (a ^ 3) x = x := by rw [h3]; rfl
    simpa [pow_succ, LinearEquiv.mul_apply] using h1
  have hnd : PolarNondeg Q ⊤ := by
    intro y _ hy0
    obtain ⟨z, hz⟩ : ∃ z, polar Q y z ≠ 0 := by
      by_contra h
      push Not at h
      exact hy0 (hQ.1 y fun z => by rw [polarBilin_apply_apply]; exact h z)
    exact ⟨z, Submodule.mem_top, (card_two_cases' hK _).resolve_left hz⟩
  obtain ⟨T, hTΩ, hTa, hTe, hTc, -⟩ := exists_elemAb_orth_aux hK ha h3' 4 ⊤
    (fun _ _ => Submodule.mem_top) hnd (by rw [finrank_top]; omega)
  exact ⟨T, hTΩ, fun t ht => Subgroup.mem_centralizer_singleton_iff.2 (hTa t ht), hTe, hTc⟩

theorem coreThree_orth (hK : Nat.card K = 2) [FiniteDimensional K V]
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 10 ≤ finrank K V) :
    CoreThree
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  intro y hy
  have hy3 : (y : V ≃ₗ[K] V) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hy, Subgroup.coe_one]
  obtain ⟨E, hEΩ, hEc, hEe, hEn⟩ := exists_elemAb81_orth hK hQ hdim (derived_le_orth y.2) hy3
  refine ⟨E.subgroupOf _, ?_, isElemAbelian_of_forall _ ?_ ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 (hEc (Subgroup.mem_subgroupOf.1 hx)))
  · intro x hx z hz
    have h := congrArg Subtype.val (hEe.1.is_comm.comm
      ⟨_, Subgroup.mem_subgroupOf.1 hx⟩ ⟨_, Subgroup.mem_subgroupOf.1 hz⟩)
    exact Subtype.ext h
  · intro x hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hEe.2 _ (Subgroup.mem_subgroupOf.1 hx)
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEΩ).toEquiv, hEn]

end CFSG.LocalAnalysis.GLTheoremA.SFRRank

end
