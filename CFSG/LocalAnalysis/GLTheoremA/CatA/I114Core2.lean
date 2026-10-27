module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Core1
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I114Cent

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I114

open CFSG.Open

variable {Y : Type} [Group Y]

theorem cj_inf (g : Y) (A C : Subgroup Y) : cj g (A ⊓ C) = cj g A ⊓ cj g C :=
  Subgroup.map_inf _ _ _ (MulAut.conj g).injective

theorem pow_mul_mem_of_normalizes {t p : Y} {P : Subgroup Y}
    (ht : t ∈ Subgroup.normalizer (P : Set Y)) (hp : p ∈ P) (n : ℕ) :
    ∃ q ∈ P, (t * p) ^ n = t ^ n * q := by
  induction n with
  | zero => exact ⟨1, P.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨q, hq, hqe⟩ := ih
    have ht' : t⁻¹ ∈ Subgroup.normalizer (P : Set Y) := (Subgroup.normalizer _).inv_mem ht
    have hc : t⁻¹ * q * t ∈ P := by
      have h1 := (Subgroup.mem_normalizer_iff.1 ht' q).1 hq
      simpa [inv_inv] using h1
    refine ⟨t⁻¹ * q * t * p, P.mul_mem hc hp, ?_⟩
    rw [pow_succ, hqe, pow_succ]
    group

theorem eq_one_of_cube_and_two_pow {x : Y} (h3 : x ^ 3 = 1) {J : ℕ} (hJ : x ^ 2 ^ J = 1) :
    x = 1 := by
  have hg : x ^ Nat.gcd 3 (2 ^ J) = 1 := (pow_gcd_eq_one (a := x)).2 ⟨h3, hJ⟩
  have hcop : Nat.gcd 3 (2 ^ J) = 1 :=
    Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right J (by norm_num))
  rw [hcop, pow_one] at hg
  exact hg

theorem exists_normal_two_subgroup {Y : Type} [Group Y] [Finite Y] {B K P T : Subgroup Y} {t : Y}
    (hKP : ElemCommute K P) (hZ : Nat.card (Subgroup.center ↥K) = 3)
    (hPn : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Y) → cj b P = P)
    (hTn : ∀ b ∈ B, cj b T = T)
    (hTK : T ≤ K ⊔ P) (hTp : IsPGroup 2 T) (htT : t ∈ T) (htP : t ∉ P) :
    ∃ P₀ : Subgroup Y, P₀ ≤ K ∧ P₀ ≠ ⊥ ∧ IsPGroup 2 P₀ ∧
      ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Y) → cj b P₀ = P₀ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKN : K ≤ Subgroup.normalizer (P : Set Y) := commutes_normalizer (commutes_symm hKP)
  have hTN : ∀ s ∈ T, s ∈ Subgroup.normalizer (P : Set Y) := fun s hs =>
    (sup_le hKN Subgroup.le_normalizer) (hTK hs)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hTp
  have hTpow : ∀ s ∈ T, s ^ 2 ^ k = 1 := by
    intro s hs
    have h1 : (⟨s, hs⟩ : ↥T) ^ Nat.card ↥T = 1 := pow_card_eq_one'
    rw [hk] at h1
    have := congrArg Subtype.val h1
    simpa using this
  set Z : Subgroup Y := K ⊓ P with hZdef
  set S : Subgroup Y := K ⊓ (T ⊔ P) with hSdef
  have hZS : Z ≤ S := inf_le_inf_left _ le_sup_right
  have hSK : S ≤ K := inf_le_left
  have hZK : Z ≤ K := inf_le_left
  have hZP : Z ≤ P := inf_le_right
  have hKZ : ∀ l ∈ K, ∀ z ∈ Z, l * z = z * l := fun l hl z hz => hKP l hl z hz.2
  have hZ3 : ∀ z ∈ Z, z ^ 3 = 1 := fun z hz =>
    cube_one_of_center hZ (hZK hz) (fun l hl => hKZ l hl z hz)
  have hA : ∀ s ∈ S, s ^ 2 ^ k ∈ Z := by
    intro s hs
    obtain ⟨t', ht', p, hp, rfl⟩ := mem_sup_of_normalizes hTN _ hs.2
    obtain ⟨q, hq, hqe⟩ := pow_mul_mem_of_normalizes (hTN t' ht') hp (2 ^ k)
    have hK' : (t' * p) ^ 2 ^ k ∈ K := K.pow_mem hs.1 _
    have hP' : (t' * p) ^ 2 ^ k ∈ P := by
      rw [hqe, hTpow t' ht', one_mul]
      exact hq
    exact ⟨hK', hP'⟩
  have hNeq : ∀ l : Y, l ∈ S → ∀ z ∈ Z, l * z = z * l := fun l hl z hz => hKZ l (hSK hl) z hz
  have hZcard : Nat.card Z ∣ 3 := by
    have hle : Z.subgroupOf K ≤ Subgroup.center ↥K := by
      intro l hl
      rw [Subgroup.mem_subgroupOf] at hl
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hKZ g.1 g.2 l hl)
    have h1 := Subgroup.card_dvd_of_le hle
    rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZK).toEquiv] at h1
    exact h1
  have hNcard_dvd : Nat.card (Z.subgroupOf S) ∣ 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv]
    exact hZcard
  haveI hNn : (Z.subgroupOf S).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hc : (g : Y) * (n : Y) * (g : Y)⁻¹ = n := by
      rw [hNeq (g : Y) g.2 n hn]
      group
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hc]
    exact hn
  have hcop : Nat.Coprime (Nat.card (Z.subgroupOf S)) (Z.subgroupOf S).index := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hNcard_dvd with h1 | h3
    · rw [h1]
      exact Nat.coprime_one_left _
    · rw [h3]
      rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
      intro hdiv
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥S ⧸ Z.subgroupOf S) 3 hdiv
      obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective g
      have h2 : (QuotientGroup.mk s : ↥S ⧸ Z.subgroupOf S) ^ 2 ^ k = 1 := by
        rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
          Subgroup.coe_pow]
        exact hA _ s.2
      have h4 := orderOf_dvd_of_pow_eq_one h2
      rw [hg] at h4
      have h5 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h4
      norm_num at h5
  obtain ⟨P', hP'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  set P₀ : Subgroup Y := P'.map S.subtype with hP₀def
  have hP₀S : ∀ x ∈ P₀, x ∈ S := by
    intro x hx
    obtain ⟨p', -, rfl⟩ := hx
    exact p'.2
  have hP₀K : P₀ ≤ K := fun x hx => hSK (hP₀S x hx)
  have hcommPN : ElemCommute P' (Z.subgroupOf S) := by
    intro p hp n hn
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact hKZ p.1 (hSK p.2) n.1 (Subgroup.mem_subgroupOf.1 hn)
  have hdisj : P' ⊓ (Z.subgroupOf S) = ⊥ := (inf_comm _ _).trans hP'.disjoint.eq_bot
  have hP₀exp : ∀ x ∈ P₀, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨p', hp', rfl⟩ := hx
    have hmem : p' ^ 2 ^ k ∈ P' ⊓ (Z.subgroupOf S) := by
      refine ⟨P'.pow_mem hp' _, Subgroup.mem_subgroupOf.2 ?_⟩
      rw [Subgroup.coe_pow]
      exact hA _ p'.2
    rw [hdisj, Subgroup.mem_bot] at hmem
    have := congrArg Subtype.val hmem
    simpa using this
  have hP₀ne : P₀ ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, c, hc, hEq⟩ := mem_sup_of_commutes hKP t (hTK htT)
    have haP : a ∉ P := by
      intro haP
      apply htP
      rw [hEq]
      exact P.mul_mem haP hc
    have haS : a ∈ S := by
      refine ⟨ha, ?_⟩
      have key : t * c⁻¹ ∈ T ⊔ P := (T ⊔ P).mul_mem (le_sup_left (a := T) (b := P) htT)
        (le_sup_right (a := T) (b := P) (P.inv_mem hc))
      have e : t * c⁻¹ = a := by rw [hEq]; group
      rw [e] at key
      exact key
    have htop : (⟨a, haS⟩ : ↥S) ∈ P' ⊔ (Z.subgroupOf S) := by
      rw [sup_comm, hP'.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨p'', hp'', n'', hn'', heq⟩ := mem_sup_of_commutes hcommPN _ htop
    have hp1 : p''.1 = 1 := by
      have hmem : p''.1 ∈ P₀ := ⟨p'', hp'', rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have ha_eq : a = n''.1 := by
      have := congrArg Subtype.val heq
      simp only [Subgroup.coe_mk, Subgroup.coe_mul, hp1, one_mul] at this
      exact this
    apply haP
    rw [ha_eq]
    exact (Subgroup.mem_subgroupOf.1 hn'').2
  have hKey : ∀ g : Y, g ∈ S → ∀ j : ℕ, g ^ 2 ^ j = 1 → g ∈ P₀ := by
    intro g hg j hj
    have hgS : (⟨g, hg⟩ : ↥S) ∈ P' ⊔ (Z.subgroupOf S) := by
      rw [sup_comm, hP'.sup_eq_top]
      exact Subgroup.mem_top _
    obtain ⟨p'', hp'', n'', hn'', heq⟩ := mem_sup_of_commutes hcommPN _ hgS
    have hJ : g ^ 2 ^ (j + k) = 1 := by rw [pow_add, pow_mul, hj, one_pow]
    have hpow : (⟨g, hg⟩ : ↥S) ^ 2 ^ (j + k) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hJ
    rw [heq] at hpow
    have hcm : Commute p'' n'' := hcommPN p'' hp'' n'' hn''
    rw [hcm.mul_pow] at hpow
    have hnN : n'' ^ 2 ^ (j + k) ∈ P' ⊓ (Z.subgroupOf S) := by
      refine ⟨?_, (Z.subgroupOf S).pow_mem hn'' _⟩
      have hinv : n'' ^ 2 ^ (j + k) = (p'' ^ 2 ^ (j + k))⁻¹ := (mul_eq_one_iff_inv_eq.1 hpow).symm
      rw [hinv]
      exact P'.inv_mem (P'.pow_mem hp'' _)
    rw [hdisj, Subgroup.mem_bot] at hnN
    have hv : (n'' : Y) ^ 2 ^ (j + k) = 1 := by
      have := congrArg Subtype.val hnN
      simpa using this
    have hv1 : (n'' : Y) = 1 :=
      eq_one_of_cube_and_two_pow (hZ3 _ (Subgroup.mem_subgroupOf.1 hn'')) hv
    have hgp : g = p''.1 := by
      have := congrArg Subtype.val heq
      simp only [Subgroup.coe_mk, Subgroup.coe_mul] at this
      rw [this, hv1, mul_one]
    rw [hgp]
    exact ⟨p'', hp'', rfl⟩
  have hPp : IsPGroup 2 ↥P₀ := fun x => ⟨k, Subtype.ext (by simpa using hP₀exp x.1 x.2)⟩
  have hle : ∀ b ∈ B, b ∈ Subgroup.normalizer (K : Set Y) → cj b P₀ ≤ P₀ := by
    intro b hb hbN x hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hcjK : cj b K = K := mem_normalizer_iff_cj.1 hbN
    have hcjS : cj b S = S := by
      rw [hSdef, cj_inf, cj_sup, hcjK, hTn b hb, hPn b hb hbN]
    have hyS : y ∈ S := hP₀S y hy
    have hxS : (MulAut.conj b).toMonoidHom y ∈ S := by
      rw [← hcjS]
      exact ⟨y, hyS, rfl⟩
    have hy2 : y ^ 2 ^ k = 1 := hP₀exp y hy
    have hxpow : ((MulAut.conj b).toMonoidHom y) ^ 2 ^ k = 1 := by
      rw [← map_pow, hy2, map_one]
    exact hKey _ hxS k hxpow
  refine ⟨P₀, hP₀K, hP₀ne, hPp, fun b hb hbN => le_antisymm (hle b hb hbN) ?_⟩
  intro y hy
  rw [mem_cj]
  have hb' := hle b⁻¹ (B.inv_mem hb) ((Subgroup.normalizer _).inv_mem hbN)
  apply hb'
  exact ⟨y, hy, by simp [MulAut.conj_apply]⟩

end CFSG.LocalAnalysis.GLTheoremA.I114
