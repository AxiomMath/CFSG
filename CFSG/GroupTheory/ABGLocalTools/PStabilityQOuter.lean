module

public import CFSG.GroupTheory.ABGLocalTools.PStabilityCoreOdd

public section

open Subgroup

namespace CFSG.ABGLocalTools

theorem mem_of_pow_two_pow_mem {M : Type*} [Group M] {J : Subgroup M} {y : M} {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hyp : y ^ p = 1) (hyk : y ^ 2 ^ k ∈ J) : y ∈ J := by
  have hdvd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
  have hcop : Nat.Coprime (2 ^ k) (orderOf y) := by
    apply Nat.Coprime.coprime_dvd_right hdvd
    exact Nat.Coprime.pow_left k ((Nat.coprime_primes Nat.prime_two hp).mpr hp2.symm)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact pow_mem hyk m

theorem mem_of_mem_sup_zpowers_of_pow_two_pow {M : Type*} [Group M] {B : Subgroup M} {z : M}
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hzp : z ^ p = 1)
    (hzN : z ∈ normalizer (B : Set M)) {t : M} (ht : t ∈ B ⊔ zpowers z) {k : ℕ}
    (htk : t ^ 2 ^ k = 1) : t ∈ B := by
  have hle : zpowers z ≤ normalizer (B : Set M) := zpowers_le.mpr hzN
  have ht' : t ∈ ((B ⊔ zpowers z : Subgroup M) : Set M) := ht
  rw [coe_mul_of_right_le_normalizer_left B (zpowers z) hle] at ht'
  obtain ⟨b, hb, w, hw, rfl⟩ := ht'
  have hwN : w ∈ normalizer (B : Set M) := hle hw
  have hpow : ∀ n : ℕ, ∃ c ∈ B, (b * w) ^ n = c * w ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨c, hc, hcn⟩ := ih
      have hwn : w ^ n ∈ normalizer (B : Set M) := pow_mem hwN n
      have hconj : w ^ n * b * (w ^ n)⁻¹ ∈ B := (mem_normalizer_iff.mp hwn b).mp hb
      refine ⟨c * (w ^ n * b * (w ^ n)⁻¹), mul_mem hc hconj, ?_⟩
      rw [pow_succ, hcn, pow_succ]
      group
  obtain ⟨c, hc, hck⟩ := hpow (2 ^ k)
  have hwk : w ^ 2 ^ k ∈ B := by
    have : w ^ 2 ^ k = c⁻¹ * (b * w) ^ 2 ^ k := by rw [hck]; group
    rw [this, htk, mul_one]
    exact inv_mem hc
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hw
  have hwp : (z ^ i) ^ p = 1 := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hzp, one_zpow]
  exact mul_mem hb (mem_of_pow_two_pow_mem hp hp2 hwp hwk)

theorem mem_of_quadratic_of_pow_eq_one {G M : Type*} [Group G] [Finite G] [Group M] {p : ℕ}
    [Fact p.Prime] (hp : p ≠ 2) (π : G →* M) (hπ : Function.Surjective π)
    (hker : Odd (Nat.card π.ker)) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    [FiniteDimensional (ZMod p) V] (ρ : G →* LinearMap.GeneralLinearGroup (ZMod p) V)
    (hρ : Function.Injective ρ) {x : G} (hx : ((ρ x : V →ₗ[ZMod p] V) - 1) ^ 2 = 0)
    (J : Subgroup M) [J.Normal] {F : Type} [Field F] [Finite F] (hF : Odd (Nat.card F))
    (hpF : ¬ p ∣ Nat.card F) (e : J ≃* Matrix.SpecialLinearGroup (Fin 2) F)
    (hC : IsPGroup 2 (centralizer (J : Set M))) (hfa : SL2FieldAutomorphism)
    (hxp : π x ^ p = 1) : π x ∈ J := by
  classical
  have hpp : p.Prime := Fact.out
  have : Finite M := Finite.of_surjective π hπ
  set y := π x with hy
  by_contra hyJ
  let α : MulAut (Matrix.SpecialLinearGroup (Fin 2) F) := MulAut.congr e (MulAut.conjNormal y)
  have hαapp : ∀ j : J, α (e j) = e (MulAut.conjNormal y j) := by
    intro j
    change e ((MulAut.conjNormal y) (e.symm (e j))) = _
    rw [MulEquiv.symm_apply_apply]
  have hαp : α ^ p = 1 := by
    change (MulAut.congr e (MulAut.conjNormal y)) ^ p = 1
    rw [← map_pow, ← map_pow, hxp, map_one, map_one]
  by_cases hinner : ∃ g, α = MulAut.conj g
  ·
    obtain ⟨g, hg⟩ := hinner
    set j₀ : J := e.symm g with hj₀
    have hconj : ∀ j : J, y * (j : M) * y⁻¹ = (j₀ : M) * j * (j₀ : M)⁻¹ := by
      intro j
      have h1 : α (e j) = g * e j * g⁻¹ := by rw [hg]; rfl
      rw [hαapp, show g = e j₀ by rw [hj₀, MulEquiv.apply_symm_apply], ← map_mul, ← map_inv,
        ← map_mul] at h1
      have h2 := congrArg Subtype.val (e.injective h1)
      simpa using h2
    set c : M := (j₀ : M)⁻¹ * y with hc
    have hcC : c ∈ centralizer (J : Set M) := by
      rw [mem_centralizer_iff]
      intro h hh
      have := hconj ⟨h, hh⟩
      simp only at this
      calc h * c = (j₀ : M)⁻¹ * ((j₀ : M) * h * (j₀ : M)⁻¹) * y := by rw [hc]; group
        _ = (j₀ : M)⁻¹ * (y * h * y⁻¹) * y := by rw [this]
        _ = c * h := by rw [hc]; group
    obtain ⟨k, hk⟩ := hC ⟨c, hcC⟩
    have hck : c ^ 2 ^ k = 1 := by
      have := congrArg Subtype.val hk
      simpa using this
    have hcomm : Commute (j₀ : M) c := by
      have := (mem_centralizer_iff.mp hcC) (j₀ : M) j₀.2
      exact this
    have hyjc : y = (j₀ : M) * c := by rw [hc]; group
    have hyk : y ^ 2 ^ k ∈ J := by
      rw [hyjc, hcomm.mul_pow, hck, mul_one]
      exact pow_mem j₀.2 _
    exact hyJ (mem_of_pow_two_pow_mem hpp hp hxp hyk)
  ·
    push Not at hinner
    obtain ⟨B, hBα, hB2, hBp, b₀, hb₀B, hαb₀⟩ := hfa F p hp hF hpF α hαp hinner
    let ι : Matrix.SpecialLinearGroup (Fin 2) F →* M := J.subtype.comp e.symm.toMonoidHom
    have hι : Function.Injective ι := (subtype_injective J).comp e.symm.injective
    have hια : ∀ b, ι (α b) = y * ι b * y⁻¹ := by
      intro b
      have h1 : α b = e (MulAut.conjNormal y (e.symm b)) := by
        rw [← hαapp, MulEquiv.apply_symm_apply]
      change ((e.symm (α b) : J) : M) = y * ((e.symm b : J) : M) * y⁻¹
      rw [h1, MulEquiv.symm_apply_apply, MulAut.conjNormal_apply]
    set Bb := B.map ι with hBb
    have hαB : ∀ b ∈ B, α b ∈ B := by
      intro b hb
      rw [← hBα]
      exact ⟨b, hb, rfl⟩
    have hyN : y ∈ normalizer (Bb : Set M) := by
      rw [mem_normalizer_iff]
      intro h
      constructor
      · rintro ⟨b, hb, rfl⟩
        exact ⟨α b, hαB b hb, hια b⟩
      · rintro ⟨b, hb, hbh⟩
        rw [← hBα] at hb
        obtain ⟨b', hb', rfl⟩ := hb
        refine ⟨b', hb', ?_⟩
        have : y * ι b' * y⁻¹ = y * h * y⁻¹ := by rw [← hια]; exact hbh
        exact mul_left_cancel (mul_right_cancel this)
    set W := Bb ⊔ zpowers y with hW
    have hB2b : TwoSubgroupsCyclic Bb := hB2.map_of_injective ι hι
    have hW2 : TwoSubgroupsCyclic W := by
      intro T hTW hT
      have hTB : T ≤ Bb := by
        intro t ht
        obtain ⟨k, hk⟩ := hT ⟨t, ht⟩
        have htk : t ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        exact mem_of_mem_sup_zpowers_of_pow_two_pow hpp hp hxp hyN (hTW ht) htk
      exact hB2b T hTB hT
    have hyW : y ∈ W := mem_sup_right (mem_zpowers y)
    have hcore := mem_pCore_of_twoSubgroupsCyclic hp π hπ hker ρ hρ hx hW2 hyW
    set PW : Subgroup M := (pCore p W).map W.subtype with hPW
    have hPWp : IsPGroup p PW := (pCore_isPGroup (G := W)).map _
    have hPWn : ∀ w ∈ W, ∀ h ∈ PW, w * h * w⁻¹ ∈ PW := by
      rintro w hw _ ⟨q, hq, rfl⟩
      refine ⟨⟨w, hw⟩ * q * ⟨w, hw⟩⁻¹, (pCore_normal (G := W)).conj_mem q hq _, ?_⟩
      simp
    have hcommB : ∀ b ∈ B, y * ι b * y⁻¹ * (ι b)⁻¹ = 1 := by
      intro b hb
      have hbW : ι b ∈ W := mem_sup_left ⟨b, hb, rfl⟩
      set c := y * ι b * y⁻¹ * (ι b)⁻¹ with hc
      have hcPW : c ∈ PW := by
        have hy' : y ∈ PW := ⟨⟨y, hyW⟩, hcore, rfl⟩
        have h1 : ι b * y⁻¹ * (ι b)⁻¹ ∈ PW := hPWn (ι b) hbW y⁻¹ (inv_mem hy')
        rw [hc, show y * ι b * y⁻¹ * (ι b)⁻¹ = y * (ι b * y⁻¹ * (ι b)⁻¹) by group]
        exact mul_mem hy' h1
      have hcB : c = ι (α b * b⁻¹) := by rw [map_mul, map_inv, hια]
      let D : Subgroup B := (PW.comap ι).subgroupOf B
      have hDn : D.Normal := by
        constructor
        intro d hd g
        change ι ((g * d * g⁻¹ : B) : Matrix.SpecialLinearGroup (Fin 2) F) ∈ PW
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_mul, map_inv]
        exact hPWn (ι g) (mem_sup_left ⟨g, g.2, rfl⟩) _ hd
      have hDp : IsPGroup p D := by
        have hinj : Function.Injective (fun d : D => (⟨ι d, d.2⟩ : PW)) := by
          intro a b hab
          have h1 := congrArg (fun z : PW => (z : M)) hab
          simp only at h1
          exact Subtype.ext (Subtype.ext (hι h1))
        exact IsPGroup.of_injective hPWp (MonoidHom.mk' (fun d : D => (⟨ι d, d.2⟩ : PW))
          (fun a b => by apply Subtype.ext; simp)) hinj
      have hDbot : D = ⊥ := by
        have : D ≤ pCore p B := le_sSup ⟨hDn, hDp⟩
        rw [hBp] at this
        exact le_bot_iff.mp this
      have hmem : (⟨α b * b⁻¹, mul_mem (hαB b hb) (inv_mem hb)⟩ : B) ∈ D := by
        change ι (α b * b⁻¹) ∈ PW
        rw [← hcB]
        exact hcPW
      rw [hDbot, mem_bot] at hmem
      have : α b * b⁻¹ = 1 := congrArg Subtype.val hmem
      rw [hcB, this, map_one]
    apply hαb₀
    apply hι
    have := hcommB b₀ hb₀B
    rw [hια]
    calc y * ι b₀ * y⁻¹ = y * ι b₀ * y⁻¹ * (ι b₀)⁻¹ * ι b₀ := by group
      _ = ι b₀ := by rw [this, one_mul]

end CFSG.ABGLocalTools
