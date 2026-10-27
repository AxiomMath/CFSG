module

public import Mathlib.GroupTheory.Sylow
import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.CoprimeOmega
import TauCeti.GroupTheory.OrderOfElement.PPart

public section

namespace CFSG.GroupTheory

open Subgroup

variable {K : Type*} [Group K] [Finite K] {p : ℕ} [Fact p.Prime]

omit [Finite K] [Fact (Nat.Prime p)] in
private theorem ocNormAux_zpow_conj_eq_of_fix (S : Subgroup K) {c : K}
    (hc : c ∈ normalizer (S : Set K))
    (hfix : ∀ w ∈ S, w ^ p = 1 → c * w * c⁻¹ = w) (z : ℤ) :
    ∀ w ∈ S, w ^ p = 1 → c ^ z * w * (c ^ z)⁻¹ = w := by
  classical
  let α : MulAut ↥S := S.normalizerMonoidHom ⟨c, hc⟩
  have hαfix : ∀ x : ↥S, ((x : K)) ^ p = 1 → α x = x := by
    intro x hx
    apply Subtype.ext
    rw [show (α x : K) = c * (x : K) * c⁻¹ from
      Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨c, hc⟩ x]
    exact hfix x x.2 hx
  have hαz : α ^ z = S.normalizerMonoidHom ⟨c ^ z, zpow_mem hc z⟩ := by
    rw [show α = S.normalizerMonoidHom ⟨c, hc⟩ from rfl, ← map_zpow]
    exact congrArg S.normalizerMonoidHom (Subtype.ext rfl)
  have hkey : ∀ x : ↥S, ((x : K)) ^ p = 1 → (α ^ z) x = x := by
    intro x hx
    have hαx : α x = x := hαfix x hx
    have hnat : ∀ n : ℕ, (α ^ n) x = x := by
      intro n
      induction n with
      | zero => rw [pow_zero]; rfl
      | succ n ih =>
        rw [pow_succ']
        show α ((α ^ n) x) = x
        rw [ih, hαx]
    obtain ⟨n, hz | hz⟩ := Int.eq_nat_or_neg z
    · subst hz
      simpa using hnat n
    · subst hz
      rw [zpow_neg, zpow_natCast]
      have hinv : ((α ^ n)⁻¹) x = x := by
        have h := congrArg (fun y => ((α ^ n)⁻¹) y) (hnat n)
        rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h
        exact h.symm
      exact hinv
  intro w hw hwp
  have hval : ((α ^ z) ⟨w, hw⟩ : K) = c ^ z * w * (c ^ z)⁻¹ := by
    rw [hαz, Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [← hval]
  exact congrArg Subtype.val (hkey ⟨w, hw⟩ hwp)

theorem mem_sylow_mul_centralizer_of_fix_omega (hp2 : p ≠ 2) (S : Sylow p K) {c : K}
    (hc : c ∈ normalizer ((S : Subgroup K) : Set K))
    (hfix : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c * w * c⁻¹ = w) :
    ∃ s ∈ (S : Subgroup K), ∃ z ∈ centralizer ((S : Subgroup K) : Set K), c = s * z := by
  classical
  set u : K := TauCeti.pPart p c with hu_def
  set v : K := TauCeti.pFreePart p c with hv_def
  have huv : u * v = c := by
    rw [hu_def, hv_def]
    exact TauCeti.pPart_mul_pFreePart p c
  have huz : u ∈ Subgroup.zpowers c := by
    rw [hu_def]; exact TauCeti.pPart_mem_zpowers p c
  have hvz : v ∈ Subgroup.zpowers c := by
    rw [hv_def]; exact TauCeti.pFreePart_mem_zpowers p c
  have huN : u ∈ normalizer ((S : Subgroup K) : Set K) :=
    Subgroup.zpowers_le.mpr hc huz
  have hvN : v ∈ normalizer ((S : Subgroup K) : Set K) :=
    Subgroup.zpowers_le.mpr hc hvz
  have hfixv : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → v * w * v⁻¹ = w := by
    obtain ⟨kv, hkv⟩ := Subgroup.mem_zpowers_iff.mp hvz
    intro w hw hwp
    rw [← hkv]
    exact ocNormAux_zpow_conj_eq_of_fix (S : Subgroup K) hc hfix kv w hw hwp
  have hvAut : (S : Subgroup K).normalizerMonoidHom ⟨v, hvN⟩ = 1 := by
    refine CFSG.HardMathSupport.Timmesfeld.ComponentBalance.mulAut_eq_one_of_coprime_of_fix_omega
      hp2 S.isPGroup' ?_ ?_
    · rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Fact.out]
      intro hdvd
      have hdvd' : p ∣ orderOf v :=
        dvd_trans hdvd (by
          rw [← Subgroup.orderOf_mk v hvN]
          exact orderOf_map_dvd ((S : Subgroup K).normalizerMonoidHom) ⟨v, hvN⟩)
      have hdvd'' : p ∣ orderOf (TauCeti.pFreePart p c) := by
        rwa [hv_def] at hdvd'
      exact TauCeti.not_dvd_orderOf_pFreePart Fact.out (orderOf_pos c).ne' hdvd''
    · intro x hx
      apply Subtype.ext
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
      have hx' : ((x : K)) ^ p = 1 := by
        have hc := congrArg Subtype.val hx
        simpa using hc
      exact hfixv x x.2 hx'
  have hvC : v ∈ centralizer ((S : Subgroup K) : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 : ((S : Subgroup K).normalizerMonoidHom ⟨v, hvN⟩) ⟨w, hw⟩ = ⟨w, hw⟩ := by
      rw [hvAut]; rfl
    have h2 : v * w * v⁻¹ = w := by
      have h := congrArg Subtype.val h1
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
      simpa using h
    have h3 : v * w = w * v := by
      calc v * w = (v * w * v⁻¹) * v := by group
        _ = w * v := by rw [h2]
    exact h3.symm
  have hupow : IsPGroup p ↥(Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := (orderOf c).factorization p) ?_
    rw [Nat.card_zpowers, show u = TauCeti.pPart p c from hu_def,
      TauCeti.orderOf_pPart Fact.out (orderOf_pos c).ne']
  have hsup : IsPGroup p ↥((S : Subgroup K) ⊔ Subgroup.zpowers u) :=
    IsPGroup.to_sup_of_normal_left' S.isPGroup' hupow (Subgroup.zpowers_le.mpr huN)
  have hSeq : (S : Subgroup K) ⊔ Subgroup.zpowers u = (S : Subgroup K) :=
    Sylow.is_maximal' S hsup le_sup_left
  have huS : u ∈ (S : Subgroup K) := by
    rw [← hSeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers u)
  exact ⟨u, huS, v, hvC, huv.symm⟩

theorem exists_normalizer_involution_of_omega (hp2 : p ≠ 2) (S : Sylow p K)
    (hact : ∀ c₁ ∈ normalizer ((S : Subgroup K) : Set K),
      ∀ c₂ ∈ normalizer ((S : Subgroup K) : Set K),
      (∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₁ * w * c₁⁻¹ = w) ∨
      (∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₂ * w * c₂⁻¹ = w) ∨
      ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c₁ * w * c₁⁻¹ = c₂ * w * c₂⁻¹)
    {c : K} (hc : c ∈ normalizer ((S : Subgroup K) : Set K))
    (hnc : ¬ ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c * w * c⁻¹ = w) :
    ∃ n ∈ normalizer ((S : Subgroup K) : Set K),
      (∀ w ∈ (S : Subgroup K), w ^ p = 1 → n * w * n⁻¹ = c * w * c⁻¹) ∧
      ∀ y ∈ (S : Subgroup K), n * (n * y * n⁻¹) * n⁻¹ = y := by
  classical
  have hc2N : c ^ 2 ∈ normalizer ((S : Subgroup K) : Set K) := pow_mem hc 2
  have hfix2 : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → c ^ 2 * w * (c ^ 2)⁻¹ = w := by
    intro w hw hwp
    rcases hact (c ^ 2) hc2N c hc with h1 | h2 | h3
    · exact h1 w hw hwp
    · exact absurd h2 hnc
    · exfalso
      apply hnc
      intro w hw hwp
      have h := h3 w hw hwp
      calc c * w * c⁻¹ = c⁻¹ * (c ^ 2 * w * (c ^ 2)⁻¹) * c := by group
        _ = c⁻¹ * (c * w * c⁻¹) * c := by rw [h]
        _ = w := by group
  obtain ⟨a, b, hbodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c).ne'
  let n : K := c ^ b
  have hnN : n ∈ normalizer ((S : Subgroup K) : Set K) := by
    rw [show n = c ^ b from rfl]
    exact pow_mem hc b
  have hn2 : n ^ 2 = c ^ (2 * b) := by
    rw [show n = c ^ b from rfl, pow_two, ← pow_add]
    congr 1
    ring
  have hn2N : n ^ 2 ∈ normalizer ((S : Subgroup K) : Set K) := pow_mem hnN 2
  have hfixn2 : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → n ^ 2 * w * (n ^ 2)⁻¹ = w := by
    intro w hw hwp
    have h := ocNormAux_zpow_conj_eq_of_fix (S : Subgroup K) hc2N hfix2 (b : ℤ) w hw hwp
    have hz : (c ^ 2) ^ b = c ^ (2 * b) := (pow_mul c 2 b).symm
    rw [zpow_natCast] at h
    rw [hn2, ← hz]
    exact h
  obtain ⟨s, hsS, z, hzC, hsz⟩ :=
    mem_sylow_mul_centralizer_of_fix_omega hp2 S hn2N hfixn2
  have hnact : ∀ w ∈ (S : Subgroup K), w ^ p = 1 → n * w * n⁻¹ = c * w * c⁻¹ := by
    intro w hw hwp
    obtain ⟨k, hk⟩ : ∃ k, b = 2 * k + 1 := hbodd
    have hw' : c * w * c⁻¹ ∈ (S : Subgroup K) := (Subgroup.mem_normalizer_iff.mp hc w).mp hw
    have hwp' : (c * w * c⁻¹) ^ p = 1 := by
      have h : c * w ^ p * c⁻¹ = (c * w * c⁻¹) ^ p := by
        simpa only [MulAut.conj_apply] using map_pow (MulAut.conj c) w p
      rw [← h, hwp]
      simp
    have hfix2w : c ^ (2 * k) * (c * w * c⁻¹) * (c ^ (2 * k))⁻¹ = c * w * c⁻¹ := by
      have h := ocNormAux_zpow_conj_eq_of_fix (S : Subgroup K) hc2N hfix2 (k : ℤ)
        (c * w * c⁻¹) hw' hwp'
      have hz : (c ^ 2) ^ k = c ^ (2 * k) := (pow_mul c 2 k).symm
      rw [zpow_natCast] at h
      rw [← hz]
      exact h
    rw [show n = c ^ b from rfl, hk, pow_succ]
    calc c ^ (2 * k) * c * w * (c ^ (2 * k) * c)⁻¹
        = c ^ (2 * k) * (c * w * c⁻¹) * (c ^ (2 * k))⁻¹ := by group
      _ = c * w * c⁻¹ := hfix2w
  have hzN : z ∈ normalizer ((S : Subgroup K) : Set K) :=
    Subgroup.centralizer_le_normalizer ((S : Subgroup K) : Set K) hzC
  have hz1 : (S : Subgroup K).normalizerMonoidHom ⟨z, hzN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, Subgroup.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf]
    exact hzC
  have hαeq : (S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩ =
      (S : Subgroup K).normalizerMonoidHom ⟨s, Subgroup.le_normalizer hsS⟩ := by
    have helem : (⟨n ^ 2, hn2N⟩ : ↥(normalizer ((S : Subgroup K) : Set K))) =
        ⟨s, Subgroup.le_normalizer hsS⟩ * ⟨z, hzN⟩ := by
      apply Subtype.ext
      show n ^ 2 = s * z
      exact hsz
    calc (S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩
        = (S : Subgroup K).normalizerMonoidHom
            (⟨s, Subgroup.le_normalizer hsS⟩ * ⟨z, hzN⟩) := by rw [helem]
      _ = (S : Subgroup K).normalizerMonoidHom ⟨s, Subgroup.le_normalizer hsS⟩ *
          (S : Subgroup K).normalizerMonoidHom ⟨z, hzN⟩ := map_mul _ _ _
      _ = (S : Subgroup K).normalizerMonoidHom ⟨s, Subgroup.le_normalizer hsS⟩ := by
          rw [hz1, mul_one]
  have hα2 : orderOf ((S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩) ∣ 2 ^ a := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow]
    have hpow : (⟨n ^ 2, hn2N⟩ : ↥(normalizer ((S : Subgroup K) : Set K))) ^ (2 ^ a) = 1 := by
      apply Subtype.ext
      show (n ^ 2) ^ (2 ^ a) = 1
      rw [hn2, ← pow_mul]
      have hexp : 2 * b * 2 ^ a = 2 ^ a * b * 2 := by ring
      rw [hexp, pow_mul]
      rw [show c ^ (2 ^ a * b) = 1 by rw [← hord, pow_orderOf_eq_one]]
      rw [one_pow]
    rw [hpow, map_one]
  have hspow : ∃ k, orderOf s = p ^ k := by
    have h := (IsPGroup.iff_orderOf (G := ↥(S : Subgroup K))).mp S.isPGroup' ⟨s, hsS⟩
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩
  obtain ⟨k, hk⟩ := hspow
  have hcop : Nat.Coprime (orderOf s) (2 ^ a) := by
    rw [hk]
    have hpodd : Odd p := Nat.Prime.odd_of_ne_two Fact.out hp2
    have hp2' : p.Coprime 2 := Nat.coprime_two_right.mpr hpodd
    exact Nat.Coprime.pow k a hp2'
  have hαs : orderOf ((S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩) ∣ orderOf s := by
    rw [hαeq]
    calc orderOf ((S : Subgroup K).normalizerMonoidHom ⟨s, Subgroup.le_normalizer hsS⟩)
        ∣ orderOf (⟨s, Subgroup.le_normalizer hsS⟩ :
            ↥(normalizer ((S : Subgroup K) : Set K))) := orderOf_map_dvd _ _
      _ = orderOf s := Subgroup.orderOf_mk s _
  have hα1 : orderOf ((S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hαs hα2
  refine ⟨n, hnN, hnact, ?_⟩
  intro y hy
  have hα1' : (S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩ = 1 :=
    orderOf_eq_one_iff.mp hα1
  have hαy : ((S : Subgroup K).normalizerMonoidHom ⟨n ^ 2, hn2N⟩) ⟨y, hy⟩ = ⟨y, hy⟩ := by
    rw [hα1']; rfl
  have hval : n ^ 2 * y * (n ^ 2)⁻¹ = y := by
    have h := congrArg Subtype.val hαy
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
    simpa using h
  calc n * (n * y * n⁻¹) * n⁻¹ = n ^ 2 * y * (n ^ 2)⁻¹ := by
        rw [pow_two, mul_inv_rev]; group
    _ = y := hval

end CFSG.GroupTheory

end
