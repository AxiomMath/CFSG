module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.GroupTheory.PGroup
import CFSG.Mathlib.GroupTheory.PermCommute

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Equiv Subgroup

@[expose] def normTriple {A : Type*} [Group A] (θ : A ≃* A) (x : A) : A := x * θ x * θ (θ x)

theorem normTriple_mul_core {A : Type*} [CommGroup A] (α β γ δ : A ≃* A)
    (hβ : ∀ x, β (β (β x)) = x) (hc : ∀ x, α (β x) = β (α x))
    (hγ : ∀ x, γ x = α (β x)) (hδ : ∀ x, δ x = α (β (β x))) (x : A) :
    normTriple α x * normTriple β x * normTriple γ x * normTriple δ x =
      x ^ 3 * normTriple α (normTriple β x) := by
  have e1 : γ (γ x) = α (α (β (β x))) := by rw [hγ, hγ, ← hc (β x)]
  have c1 : β (α (β (β x))) = α x := by rw [← hc (β (β x)), hβ]
  have e2 : δ (δ x) = α (α (β x)) := by rw [hδ, hδ, c1, ← hc x]
  unfold normTriple
  rw [e1, e2, hγ, hδ]
  simp only [map_mul, pow_succ, pow_zero, one_mul]
  ac_rfl

variable {Y : Type*} [Group Y]

@[expose] def normalizerConjAut (M : Subgroup Y) (g : Y) (hg : g ∈ normalizer (M : Set Y)) :
    M ≃* M where
  toFun x := ⟨g * x * g⁻¹, (mem_set_normalizer_iff.1 hg x).1 x.2⟩
  invFun x := ⟨g⁻¹ * x * g, (mem_set_normalizer_iff''.1 hg x).1 x.2⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_normalizerConjAut (M : Subgroup Y) (g : Y) (hg : g ∈ normalizer (M : Set Y)) (x : M) :
    ((normalizerConjAut M g hg x : M) : Y) = g * x * g⁻¹ := rfl

@[expose, instance_reducible] def commGroupOfAbelian (M : Subgroup Y)
    (h : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) : CommGroup M :=
  { (inferInstance : Group M) with
    mul_comm := fun x y => Subtype.ext (h _ x.2 _ y.2) }

theorem normalizerConjAut_cube (M : Subgroup Y) (g : Y) (hg : g ∈ normalizer (M : Set Y))
    (hg3 : g ^ 3 = 1) (x : M) :
    normalizerConjAut M g hg (normalizerConjAut M g hg (normalizerConjAut M g hg x)) = x := by
  refine Subtype.ext ?_
  simp only [coe_normalizerConjAut]
  have hg3' : g * (g * g) = 1 := by simpa [pow_succ, mul_assoc] using hg3
  calc g * (g * (g * (x : Y) * g⁻¹) * g⁻¹) * g⁻¹
      = (g * (g * g)) * x * (g * (g * g))⁻¹ := by group
    _ = x := by rw [hg3']; simp

theorem normTriple_mem_centralizer (M : Subgroup Y) (hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (g : Y) (hg : g ∈ normalizer (M : Set Y)) (hg3 : g ^ 3 = 1) (n : M) :
    ((normTriple (normalizerConjAut M g hg) n : M) : Y) ∈ centralizer ({g} : Set Y) := by
  let _ : CommGroup M := commGroupOfAbelian M hMab
  set θ := normalizerConjAut M g hg with hθ
  have h3 : ∀ x, θ (θ (θ x)) = x := normalizerConjAut_cube M g hg hg3
  have hfix : θ (normTriple θ n) = normTriple θ n := by
    unfold normTriple
    simp only [map_mul, h3]
    ac_rfl
  rw [mem_centralizer_singleton_iff]
  have := congrArg Subtype.val hfix
  simp only [hθ, coe_normalizerConjAut] at this
  exact (mul_inv_eq_iff_eq_mul.1 this).symm

theorem exists_independent {Y : Type*} [Group Y] [Finite Y] (P : Subgroup Y)
    (hP3 : ∀ a ∈ P, a ^ 3 = 1) (hP9 : Nat.card P = 9) :
    ∃ a ∈ P, ∃ b ∈ P, a ≠ 1 ∧ b ∉ zpowers a := by
  have : Nontrivial P := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : P)
  have ha1 : (a : Y) ≠ 1 := fun h => ha (Subtype.ext h)
  obtain ⟨b, hbP, hb⟩ : ∃ b ∈ P, b ∉ zpowers (a : Y) := by
    by_contra hcon
    have hle : P ≤ zpowers (a : Y) := fun b hb => by
      by_contra h
      exact hcon ⟨b, hb, h⟩
    have h1 := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hP9] at h1
    have h2 : orderOf (a : Y) ∣ 3 := orderOf_dvd_of_pow_eq_one (hP3 a a.2)
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  exact ⟨a, a.2, b, hbP, ha1, hb⟩

theorem pow_three_eq_one_of_mem_zpowers {Y : Type*} [Group Y] {a z : Y} (ha3 : a ^ 3 = 1)
    (hz : z ∈ zpowers a) : z ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := hz
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
  simp [ha3]

theorem zpowers_eq_of_mem_of_ne_one {Y : Type*} [Group Y] [Finite Y] {a z : Y} (ha3 : a ^ 3 = 1)
    (ha1 : a ≠ 1) (hz : z ∈ zpowers a) (hz1 : z ≠ 1) : zpowers z = zpowers a := by
  have hz3 := pow_three_eq_one_of_mem_zpowers ha3 hz
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have h2 : orderOf a = 3 := orderOf_eq_prime ha3 ha1
  exact Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hz) (by
    rw [Nat.card_zpowers, Nat.card_zpowers, h1, h2])

theorem mem_closure_centralizers_of_E9 {Y : Type*} [Group Y] [Finite Y] (P : Subgroup Y)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP3 : ∀ a ∈ P, a ^ 3 = 1) (hP9 : Nat.card P = 9)
    (M : Subgroup Y) (hM : P ≤ normalizer (M : Set Y)) (hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x)
    (hM3 : Nat.Coprime (Nat.card M) 3) :
    M = ⨆ (a : P) (_ : a ≠ 1), M ⊓ centralizer ({(a : Y)} : Set Y) := by
  let _ : CommGroup M := commGroupOfAbelian M hMab
  refine le_antisymm ?_ (iSup₂_le fun g _ => inf_le_left)
  obtain ⟨a, haP, b, hbP, ha1, hb⟩ := exists_independent P hP3 hP9
  have hab : a * b = b * a := hPab a haP b hbP
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hb
    rw [eq_inv_of_mul_eq_one_right h]
    exact inv_mem (mem_zpowers a)
  have hb3 : b * (b * b) = 1 := by simpa [pow_succ, mul_assoc] using hP3 b hbP
  have habb1 : a * b * b ≠ 1 := by
    intro h
    apply hb
    have h' : b * b = a⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [mul_assoc] at h)
    have : b = a⁻¹ * a⁻¹ := by
      rw [← h']
      calc b = (b * (b * b)) * b := by rw [hb3, one_mul]
        _ = b * b * (b * b) := by simp [mul_assoc]
    rw [this]
    exact mul_mem (inv_mem (mem_zpowers a)) (inv_mem (mem_zpowers a))
  have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
  set J : Subgroup Y := ⨆ (a : P) (_ : a ≠ 1), M ⊓ centralizer ({(a : Y)} : Set Y) with hJ
  have hK : ∀ g (hg : g ∈ P), g ≠ 1 → ∀ n : M,
      ((normTriple (normalizerConjAut M g (hM hg)) n : M) : Y) ∈ J := by
    intro g hg hg1 n
    have hmem : ((normTriple (normalizerConjAut M g (hM hg)) n : M) : Y) ∈
        M ⊓ centralizer ({g} : Set Y) :=
      ⟨(normTriple (normalizerConjAut M g (hM hg)) n).2,
        normTriple_mem_centralizer M hMab g (hM hg) (hP3 g hg) n⟩
    exact le_iSup₂_of_le (f := fun (a : P) (_ : a ≠ 1) =>
      M ⊓ centralizer ({(a : Y)} : Set Y)) ⟨g, hg⟩ (fun h => hg1 (congrArg Subtype.val h))
      le_rfl hmem
  have habP : a * b ∈ P := mul_mem haP hbP
  have habbP : a * b * b ∈ P := mul_mem habP hbP
  have hcube : ∀ x : M, ((x : Y)) ^ 3 ∈ J := by
    intro x
    set α := normalizerConjAut M a (hM haP) with hα
    set β := normalizerConjAut M b (hM hbP) with hβ
    set γ := normalizerConjAut M (a * b) (hM habP) with hγ
    set δ := normalizerConjAut M (a * b * b) (hM habbP) with hδ
    have key := normTriple_mul_core α β γ δ
      (normalizerConjAut_cube M b (hM hbP) (hP3 b hbP))
      (fun y => Subtype.ext (by
        simp only [hα, hβ, coe_normalizerConjAut]
        calc a * (b * (y : Y) * b⁻¹) * a⁻¹ = (a * b) * y * (a * b)⁻¹ := by group
          _ = (b * a) * y * (b * a)⁻¹ := by rw [hab]
          _ = b * (a * (y : Y) * a⁻¹) * b⁻¹ := by group))
      (fun y => Subtype.ext (by simp only [hα, hβ, hγ, coe_normalizerConjAut]; group))
      (fun y => Subtype.ext (by simp only [hα, hβ, hδ, coe_normalizerConjAut]; group)) x
    have hx : x ^ 3 = (normTriple α x * normTriple β x * normTriple γ x * normTriple δ x) *
        (normTriple α (normTriple β x))⁻¹ := eq_mul_inv_of_mul_eq key.symm
    have := congrArg Subtype.val hx
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at this
    rw [this]
    exact mul_mem (mul_mem (mul_mem (mul_mem (hK a haP ha1 x) (hK b hbP hb1 x))
      (hK _ habP hab1 x)) (hK _ habbP habb1 x)) (inv_mem (hK a haP ha1 _))
  intro m hm
  obtain ⟨y, hy⟩ := (powCoprime hM3).surjective ⟨m, hm⟩
  have := hcube y
  rw [powCoprime_apply] at hy
  have := congrArg Subtype.val hy
  simp only [Subgroup.coe_pow] at this
  rw [← this]
  exact hcube y

theorem eq_bot_of_normal_of_commute {Y : Type*} [Group Y] [Finite Y] (P : Subgroup Y)
    (hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP3 : ∀ a ∈ P, a ^ 3 = 1) (hP9 : Nat.card P = 9)
    (hC : ∀ a ∈ P, a ≠ 1 → ∀ Q : Subgroup Y, Q ≤ centralizer ({a} : Set Y) →
      (∀ g ∈ centralizer ({a} : Set Y), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q) →
      (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) → Q ≤ zpowers a)
    (A : Subgroup Y) (hA : A.Normal) (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) : A = ⊥ := by
  by_contra hne
  obtain ⟨x, hxA, hx1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hne (eq_bot_iff.2 fun y hy => h y hy)
  have hcardA : Nat.card A ≠ 1 := by
    intro h
    have : Subsingleton A := Finite.card_le_one_iff_subsingleton.1 h.le
    exact hx1 (congrArg Subtype.val (Subsingleton.elim (⟨x, hxA⟩ : A) 1))
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hcardA
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := A) p hpd
  let M : Subgroup Y :=
    { carrier := {x | x ∈ A ∧ ∃ k : ℕ, x ^ p ^ k = 1}
      one_mem' := ⟨one_mem _, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxA, k, hk⟩ ⟨hyA, l, hl⟩
        refine ⟨mul_mem hxA hyA, k + l, ?_⟩
        rw [(show Commute x y from hAab x hxA y hyA).mul_pow, pow_add, pow_mul, hk,
          mul_comm (p ^ k), pow_mul, hl]
        simp
      inv_mem' := by
        rintro x ⟨hxA, k, hk⟩
        exact ⟨inv_mem hxA, k, by rw [inv_pow, hk, inv_one]⟩ }
  have hMA : ∀ y, y ∈ M ↔ y ∈ A ∧ ∃ k : ℕ, y ^ p ^ k = 1 := fun y => Iff.rfl
  have hMn : M.Normal := ⟨fun y hy g => by
    obtain ⟨hyA, k, hk⟩ := (hMA y).1 hy
    exact (hMA _).2 ⟨hA.conj_mem y hyA g, k, by rw [conj_pow, hk]; simp⟩⟩
  have hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := fun x hx y hy =>
    hAab x ((hMA x).1 hx).1 y ((hMA y).1 hy).1
  have hxM : (u : Y) ∈ M := (hMA _).2 ⟨u.2, 1, by
    have h1 := congrArg Subtype.val (pow_orderOf_eq_one u)
    rw [hu] at h1
    simpa using h1⟩
  have hu1 : (u : Y) ≠ 1 := by
    intro h
    have : orderOf (u : Y) = 1 := by rw [h]; exact orderOf_one
    have h' : orderOf u = 1 := by rwa [Subgroup.orderOf_coe] at this
    exact hp.one_lt.ne' (hu ▸ h')
  have hQle : ∀ g ∈ P, g ≠ 1 → M ⊓ centralizer ({g} : Set Y) ≤ zpowers g := by
    intro g hg hg1
    refine hC g hg hg1 (M ⊓ centralizer ({g} : Set Y)) inf_le_right
      (fun h hh q hq => ⟨hMn.conj_mem q hq.1 h, ?_⟩) (fun x hx y hy => hMab x hx.1 y hy.1)
    exact (Subgroup.centralizer ({g} : Set Y)).mul_mem
      ((Subgroup.centralizer ({g} : Set Y)).mul_mem hh hq.2)
      ((Subgroup.centralizer ({g} : Set Y)).inv_mem hh)
  have := hMn
  by_cases hp3 : p = 3
  · subst hp3
    let ρ : P →* MulAut M := (MulAut.conjNormal : Y →* MulAut M).comp P.subtype
    let _ : MulAction P M := MulAction.compHom M ρ
    have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
    have hMp : IsPGroup 3 M := fun g => by
      obtain ⟨_, k, hk⟩ := g.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    have hMnt : Nontrivial M := ⟨⟨u, hxM⟩, 1, fun h => hu1 (congrArg Subtype.val h)⟩
    have hdvd : 3 ∣ Nat.card M := by
      obtain ⟨n, hn0, hn⟩ := hMp.nontrivial_iff_card.mp hMnt
      exact hn ▸ dvd_pow_self 3 hn0.ne'
    have hfix1 : (1 : M) ∈ MulAction.fixedPoints P M :=
      MulAction.mem_fixedPoints.2 fun g => by
        change ρ g 1 = 1
        exact map_one _
    obtain ⟨z, hz, hz1⟩ := hPp.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hdvd hfix1
    have hzc : ∀ g ∈ P, g * (z : Y) * g⁻¹ = z := fun g hg => by
      have := congrArg Subtype.val (MulAction.mem_fixedPoints.1 hz ⟨g, hg⟩)
      exact this
    have hzmem : ∀ g ∈ P, g ≠ 1 → (z : Y) ∈ zpowers g := fun g hg hg1 =>
      hQle g hg hg1 ⟨z.2, mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 (hzc g hg)).symm⟩
    obtain ⟨a, haP, b, hbP, ha1, hb⟩ := exists_independent P hP3 hP9
    have hb1 : b ≠ 1 := fun h => hb (h ▸ one_mem _)
    have hz1' : (z : Y) ≠ 1 := fun h => hz1 (Subtype.ext h.symm)
    have h1 := zpowers_eq_of_mem_of_ne_one (hP3 a haP) ha1 (hzmem a haP ha1) hz1'
    have h2 := zpowers_eq_of_mem_of_ne_one (hP3 b hbP) hb1 (hzmem b hbP hb1) hz1'
    exact hb (h1 ▸ h2 ▸ mem_zpowers b)
  · have hMp : IsPGroup p M := fun g => by
      obtain ⟨_, k, hk⟩ := g.2
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hMp
    have hcop : Nat.Coprime (Nat.card M) 3 := by
      rw [hn]
      exact Nat.Coprime.pow_left n ((Nat.coprime_primes hp Nat.prime_three).2 hp3)
    have hgen := mem_closure_centralizers_of_E9 P hPab hP3 hP9 M
      (by rw [normalizer_eq_top]; exact le_top) hMab hcop
    have hbot : M ≤ ⊥ := hgen.le.trans (iSup₂_le fun g hg q hq => by
      have hz := hQle g g.2 (fun h => hg (Subtype.ext h)) hq
      have h3 := pow_three_eq_one_of_mem_zpowers (hP3 g g.2) hz
      obtain ⟨_, j, hj⟩ := (hMA q).1 hq.1
      have hd3 : orderOf q ∣ 3 := orderOf_dvd_of_pow_eq_one h3
      have hdp : orderOf q ∣ p ^ j := orderOf_dvd_of_pow_eq_one hj
      have hcop' : Nat.Coprime 3 (p ^ j) :=
        ((Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)).pow_right j
      have := Nat.dvd_gcd hd3 hdp
      rw [hcop'] at this
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 this))
    exact hu1 (hbot hxM)


theorem perm5_normal_abelian_eq_bot (S : Subgroup (Perm (Fin 5))) (hS : S.Normal)
    (hab : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : S = ⊥ := by
  have hA : ∀ x ∈ S, x ∈ alternatingGroup (Fin 5) → x = 1 := by
    have := hS
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (S.subgroupOf (alternatingGroup (Fin 5))) with
      h | h
    · intro x hx hxA
      have : (⟨x, hxA⟩ : alternatingGroup (Fin 5)) ∈ S.subgroupOf (alternatingGroup (Fin 5)) := hx
      rw [h] at this
      simpa using this
    · exfalso
      have hcomm : IsMulCommutative (alternatingGroup (Fin 5)) := by
        refine ⟨⟨fun x y => ?_⟩⟩
        have hx : x ∈ S.subgroupOf (alternatingGroup (Fin 5)) := by rw [h]; trivial
        have hy : y ∈ S.subgroupOf (alternatingGroup (Fin 5)) := by rw [h]; trivial
        exact Subtype.ext (hab _ hx _ hy)
      have := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 5)).1 hcomm
      simp at this
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  apply CFSG.perm_eq_one_of_forall_commute (by simp)
  intro g
  have hc : n * g * n⁻¹ * g⁻¹ ∈ S := by
    have := S.mul_mem hn (hS.conj_mem _ (S.inv_mem hn) g)
    simpa [mul_assoc] using this
  have := hA _ hc (by
    rw [Perm.mem_alternatingGroup]
    simp only [map_mul, map_inv, Int.units_inv_eq_self]
    generalize Perm.sign n = u
    generalize Perm.sign g = v
    rcases Int.units_eq_one_or u with rfl | rfl <;> rcases Int.units_eq_one_or v with rfl | rfl <;>
      simp)
  calc n * g = (n * g * n⁻¹ * g⁻¹) * (g * n) := by group
    _ = g * n := by rw [this, one_mul]

theorem le_zpowers_of_centralizer_equiv {Y : Type*} [Group Y] [Finite Y] {a : Y} (ha : a ≠ 1)
    (_ha3 : a ^ 3 = 1)
    (e : ↥(centralizer ({a} : Set Y)) ≃* Multiplicative (ZMod 3) × Equiv.Perm (Fin 5))
    (Q : Subgroup Y) (hQ : Q ≤ centralizer ({a} : Set Y))
    (hQn : ∀ g ∈ centralizer ({a} : Set Y), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) : Q ≤ zpowers a := by
  have haC : a ∈ centralizer ({a} : Set Y) := by
    rw [mem_centralizer_iff]; intro h hh; rw [Set.mem_singleton_iff.1 hh]
  let ac : centralizer ({a} : Set Y) := ⟨a, haC⟩
  let φ : centralizer ({a} : Set Y) →* Equiv.Perm (Fin 5) :=
    (MonoidHom.snd _ _).comp e.toMonoidHom
  have hφs : Function.Surjective φ := fun t => ⟨e.symm (1, t), by simp [φ]⟩
  let Q' : Subgroup (centralizer ({a} : Set Y)) := Q.subgroupOf (centralizer ({a} : Set Y))
  have hQ'n : Q'.Normal := ⟨fun n hn g => hQn g g.2 n hn⟩
  have hSn : (Q'.map φ).Normal := hQ'n.map φ hφs
  have hS : Q'.map φ = ⊥ := by
    refine perm5_normal_abelian_eq_bot _ hSn ?_
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hQab _ hx _ hy)
  have hφa : φ ac = 1 := by
    apply CFSG.perm_eq_one_of_forall_commute (by simp)
    intro t
    obtain ⟨c, rfl⟩ := hφs t
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    have := c.2
    rw [mem_centralizer_iff] at this
    exact this a (Set.mem_singleton a)
  have hw : (e ac).1 ≠ 1 := by
    intro h
    have : e ac = 1 := Prod.ext h hφa
    exact ha (congrArg Subtype.val (e.injective (this.trans (map_one e).symm)))
  intro q hq
  have hqC := hQ hq
  let c : centralizer ({a} : Set Y) := ⟨q, hqC⟩
  have hc1 : φ c = 1 := by
    have : φ c ∈ Q'.map φ := ⟨c, hq, rfl⟩
    rw [hS] at this
    simpa using this
  have key : ∀ z w : Multiplicative (ZMod 3), w ≠ 1 → ∃ k : Fin 3, w ^ (k : ℕ) = z := by decide
  obtain ⟨k, hk⟩ := key (e c).1 _ hw
  have : c = ac ^ (k : ℕ) := by
    apply e.injective
    refine Prod.ext ?_ ?_
    · simp [hk]
    · have h1 : (e c).2 = 1 := hc1
      have h2 : (e ac).2 = 1 := hφa
      simp [h1, h2]
  exact ⟨k, by simpa using (congrArg Subtype.val this).symm⟩

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
