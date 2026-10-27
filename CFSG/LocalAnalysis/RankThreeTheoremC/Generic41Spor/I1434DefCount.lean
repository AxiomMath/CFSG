module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434General

public section

open CFSG.Open

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434

@[expose] def FiveExpLe (G : Type*) [Group G] (k : ℕ) : Prop :=
  ∀ g : G, (∃ m : ℕ, g ^ (5 ^ m) = 1) → g ^ (5 ^ k) = 1

namespace FiveExpLe

variable {G H : Type*} [Group G] [Group H] {k l : ℕ}

theorem subgroup (S : Subgroup G) (h : FiveExpLe G k) : FiveExpLe S k := by
  intro g ⟨m, hm⟩
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h g (⟨m, by simpa using congrArg Subtype.val hm⟩)

theorem of_mulEquiv (e : G ≃* H) (h : FiveExpLe G k) : FiveExpLe H k := by
  intro g ⟨m, hm⟩
  have h1 : (e.symm g) ^ (5 ^ m) = 1 := by rw [← map_pow, hm, map_one]
  have h2 := h _ ⟨m, h1⟩
  have h3 : g ^ (5 ^ k) = e ((e.symm g) ^ (5 ^ k)) := by rw [map_pow, MulEquiv.apply_symm_apply]
  rw [h3, h2, map_one]

theorem of_surjective [Finite G] {f : G →* H} (hf : Function.Surjective f) (h : FiveExpLe G k) :
    FiveExpLe H k := by
  intro g ⟨m, hm⟩
  obtain ⟨x, rfl⟩ := hf g
  have ho : orderOf x ≠ 0 := (orderOf_pos x).ne'
  obtain ⟨a, s, hs, hos⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho 5 (by norm_num)
  have hcop : Nat.Coprime (5 ^ m) s :=
    Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).2 hs)
  obtain ⟨u, hu1, hu2⟩ := Nat.chineseRemainder hcop 1 0
  have hxu : (x ^ u) ^ (5 ^ a) = 1 := by
    obtain ⟨c, hc⟩ := (Nat.modEq_zero_iff_dvd).1 hu2
    have hu5 : u * 5 ^ a = orderOf x * c := by rw [hos, hc]; ring
    rw [← pow_mul, hu5, pow_mul, pow_orderOf_eq_one, one_pow]
  have h1 := h (x ^ u) ⟨a, hxu⟩
  have hgu : (f x) ^ u = f x := by
    have hg5 : (f x) ^ (5 ^ m) = 1 := hm
    rw [pow_eq_pow_mod u hg5]
    have : u % 5 ^ m = 1 % 5 ^ m := hu1
    rw [this]
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp at hg5
      simp [hg5]
    · rw [Nat.mod_eq_of_lt (by
        calc 1 < 5 := by norm_num
          _ = 5 ^ 1 := by norm_num
          _ ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm0), pow_one]
  calc (f x) ^ (5 ^ k) = (f x ^ u) ^ (5 ^ k) := by rw [hgu]
    _ = f ((x ^ u) ^ (5 ^ k)) := by rw [map_pow, map_pow]
    _ = 1 := by rw [h1, map_one]

end FiveExpLe

section Unipotent

variable {F V : Type*} [Field F] [CharP F 5] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem five_eq_zero_end : ((5 : ℕ) : Module.End F V) = 0 := by
  ext v
  have h5 : ((5 : ℕ) : F) = 0 := CharP.cast_eq_zero F 5
  rw [Module.End.natCast_apply, Nat.cast_smul_eq_nsmul F 5 v |>.symm, h5, zero_smul]
  rfl

theorem fiveExpLe_units_end {k : ℕ} (hk : Module.finrank F V ≤ 5 ^ k) :
    FiveExpLe (Module.End F V)ˣ k := by
  intro g ⟨m, hg⟩
  set N : Module.End F V := (g : Module.End F V) - 1 with hN
  have hgN : (g : Module.End F V) = N + 1 := by simp [hN]
  have hcomm : Commute N 1 := Commute.one_right N
  have hpow : ∀ n : ℕ, ((N + 1) ^ (5 ^ n) : Module.End F V) = N ^ (5 ^ n) + 1 := by
    intro n
    obtain ⟨r, hr⟩ := hcomm.exists_add_pow_prime_pow_eq Nat.prime_five n
    rw [hr, five_eq_zero_end]
    simp
  have h1 : N ^ (5 ^ m) = 0 := by
    have h2 := hpow m
    rw [← hgN, ← Units.val_pow_eq_pow_val, hg, Units.val_one] at h2
    have h3 : N ^ (5 ^ m) + 1 = 0 + 1 := by rw [← h2]; simp
    exact add_right_cancel h3
  have hnil : IsNilpotent N := ⟨5 ^ m, h1⟩
  have hcp := (LinearMap.isNilpotent_iff_charpoly N).1 hnil
  have hCH := LinearMap.aeval_self_charpoly N
  rw [hcp] at hCH
  simp only [map_pow, Polynomial.aeval_X] at hCH
  have h4 : N ^ (5 ^ k) = 0 := pow_eq_zero_of_le hk hCH
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, hgN, hpow k, h4]
  simp

theorem fiveExpLe_GL {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (hk : Fintype.card ι ≤ 5 ^ k) : FiveExpLe (Matrix.GeneralLinearGroup ι F) k := by
  have h : FiveExpLe (LinearMap.GeneralLinearGroup F (ι → F)) k :=
    fiveExpLe_units_end (by rw [Module.finrank_fintype_fun_eq_card]; exact hk)
  exact FiveExpLe.of_mulEquiv (Matrix.GeneralLinearGroup.toLin).symm h

end Unipotent

section Abelian

theorem card_le_pow_of_abelian :
    ∀ (k : ℕ) (A : Type) [CommGroup A] [Finite A], (∀ g : A, g ^ (5 ^ k) = 1) →
      (∀ E : Subgroup A, (∀ g ∈ E, g ^ 5 = 1) → Nat.card E ≤ 5 ^ 3) →
        Nat.card A ≤ 5 ^ (3 * k) := by
  intro k
  induction k with
  | zero =>
    intro A _ _ hexp _
    have : Subsingleton A := ⟨fun a b => by
      have ha := hexp a
      have hb := hexp b
      simp only [pow_zero, pow_one] at ha hb
      rw [ha, hb]⟩
    have := Nat.card_unique (α := A)
    simp
  | succ k ih =>
    intro A _ _ hexp hrank
    let φ : A →* A := powMonoidHom 5
    have hker : Nat.card φ.ker ≤ 5 ^ 3 := by
      refine hrank φ.ker fun g hg => ?_
      simpa [φ] using hg
    have hB : Nat.card φ.range ≤ 5 ^ (3 * k) := by
      refine ih φ.range ?_ ?_
      · intro g
        obtain ⟨a, ha⟩ := g.2
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, ← ha]
        have : φ a = a ^ 5 := rfl
        rw [this, ← pow_mul, ← pow_succ']
        exact hexp a
      · intro E hE
        have h1 : Nat.card (E.map φ.range.subtype) ≤ 5 ^ 3 := by
          refine hrank _ ?_
          rintro _ ⟨g, hg, rfl⟩
          have := hE g hg
          simpa using congrArg Subtype.val this
        rwa [Subgroup.card_map_of_injective φ.range.subtype_injective] at h1
    have := Subgroup.card_ker_mul_card_range φ
    calc Nat.card A = Nat.card φ.ker * Nat.card φ.range := this.symm
      _ ≤ 5 ^ 3 * 5 ^ (3 * k) := Nat.mul_le_mul hker hB
      _ = 5 ^ (3 * (k + 1)) := by ring

end Abelian

theorem Data.le_of_fiveExpLe {K : Type} [Group K] [Finite K] {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂) {k : ℕ} (hk : FiveExpLe K k) :
    (Nat.card K).factorization 5 ≤ 3 * k := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI := hD.abelian
  letI : CommGroup (Q : Subgroup K) :=
    { (inferInstance : Group (Q : Subgroup K)) with mul_comm := fun a b => mul_comm' a b }
  have hexp : ∀ g : (Q : Subgroup K), g ^ (5 ^ k) = 1 := by
    intro g
    obtain ⟨m, hm⟩ := Q.isPGroup' g
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hk (g : K) ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hrank : ∀ E : Subgroup (Q : Subgroup K), (∀ g ∈ E, g ^ 5 = 1) → Nat.card E ≤ 5 ^ 3 := by
    intro E hE
    have hEK : IsElemAbelian 5 (E.map (Q : Subgroup K).subtype) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
      · obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.1 a.2
        obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.1 b.2
        apply Subtype.ext
        change (a : K) * b = b * a
        rw [← ha, ← hb]
        exact congrArg Subtype.val (mul_comm' a' b')
      · rintro _ hg
        obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
        have := hE g' hg'
        simpa using congrArg Subtype.val this
    have := card_le_of_isElemAbelian hD.rank hEK
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at this
  have hcard := card_le_pow_of_abelian k (Q : Subgroup K) hexp hrank
  rw [Sylow.card_eq_multiplicity] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 5)).1 hcard

theorem Data.false_of_fiveExpLe {K : Type} [Group K] [Finite K] {Q : Sylow 5 K} {x : K}
    {J₁ J₂ : Subgroup K} (hD : Data K Q x J₁ J₂) {k : ℕ} (hk : FiveExpLe K k)
    (hv : 3 * k < (Nat.card K).factorization 5) : False :=
  absurd (hD.le_of_fiveExpLe hk) (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.I1434
