module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13h
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma137b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltInputs
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims137

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

section Abstract

variable {Y : Type*} [Group Y]

theorem conj_mem_centralizer_of {K : Subgroup Y} {c w : Y}
    (h : ∀ k ∈ K, (c⁻¹ * k * c) * w = w * (c⁻¹ * k * c)) :
    c * w * c⁻¹ ∈ Subgroup.centralizer (K : Set Y) := by
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  calc k * (c * w * c⁻¹) = c * ((c⁻¹ * k * c) * w) * c⁻¹ := by group
    _ = c * (w * (c⁻¹ * k * c)) * c⁻¹ := by rw [h k hk]
    _ = c * w * c⁻¹ * k := by group

theorem eq_one_of_pow_two_of_pow_p {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {z : Y} {a b : ℕ}
    (ha : z ^ (2 ^ a) = 1) (hb : z ^ (p ^ b) = 1) : z = 1 := by
  have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
    Nat.Coprime.pow a b ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h1 : orderOf z ∣ 2 ^ a := orderOf_dvd_of_pow_eq_one ha
  have h2 : orderOf z ∣ p ^ b := orderOf_dvd_of_pow_eq_one hb
  have h3 : orderOf z ∣ Nat.gcd (2 ^ a) (p ^ b) := Nat.dvd_gcd h1 h2
  rw [hcop] at h3
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)

theorem commute_of_mem_centralizer {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hcore : GLAPPrimeCore p Y = ⊥) (S W : Subgroup Y) [hSn : S.Normal]
    (hW2 : IsPGroup 2 W)
    (hWF : W ≤ Subgroup.centralizer (CFSG.Open.pCore p Y : Set Y))
    (hWK : ∀ K : Subgroup Y, IsComponentOf K ⊤ → ¬ K ≤ S →
      W ≤ Subgroup.centralizer (K : Set Y))
    {c : Y} (hc : c ∈ Subgroup.centralizer (S : Set Y)) {w : Y} (hw : w ∈ W) :
    c * w = w * c := by
  haveI : Fact p.Prime := ⟨hp⟩
  set z : Y := c * w * c⁻¹ * w⁻¹ with hz
  have hz' : z = (c * w * c⁻¹) * w⁻¹ := rfl
  have hPn : (CFSG.Open.pCore p Y).Normal := inferInstance
  have hzS : z ∈ Subgroup.centralizer (S : Set Y) := by
    have h1 : w * c⁻¹ * w⁻¹ ∈ Subgroup.centralizer (S : Set Y) := by
      refine conj_mem_centralizer_of (fun s hs => ?_)
      have hs' : w⁻¹ * s * w⁻¹⁻¹ ∈ S := hSn.conj_mem s hs w⁻¹
      rw [inv_inv] at hs'
      exact Subgroup.mem_centralizer_iff.1 ((Subgroup.centralizer (S : Set Y)).inv_mem hc) _ hs'
    have : z = c * (w * c⁻¹ * w⁻¹) := by rw [hz]; group
    rw [this]
    exact (Subgroup.centralizer (S : Set Y)).mul_mem hc h1
  have hzF : z ∈ Subgroup.centralizer (CFSG.Open.pCore p Y : Set Y) := by
    have h1 : c * w * c⁻¹ ∈ Subgroup.centralizer (CFSG.Open.pCore p Y : Set Y) := by
      refine conj_mem_centralizer_of (fun k hk => ?_)
      have hk' : c⁻¹ * k * c⁻¹⁻¹ ∈ CFSG.Open.pCore p Y := hPn.conj_mem k hk c⁻¹
      rw [inv_inv] at hk'
      exact Subgroup.mem_centralizer_iff.1 (hWF hw) _ hk'
    rw [hz']
    exact (Subgroup.centralizer _).mul_mem h1 ((Subgroup.centralizer _).inv_mem (hWF hw))
  have hzK : ∀ K : Subgroup Y, IsComponentOf K ⊤ → z ∈ Subgroup.centralizer (K : Set Y) := by
    intro K hK
    by_cases hKS : K ≤ S
    · exact Subgroup.centralizer_le hKS hzS
    ·
      have hK' : IsComponentOf (GLBConj c K) ⊤ := isComponentOf_gLBConj hK c
      have hK'S : ¬ GLBConj c K ≤ S := by
        intro hle
        apply hKS
        intro k hk
        have h1 : c⁻¹ * k * c ∈ GLBConj c K := by
          rw [mem_gLBConj]
          simpa [mul_assoc] using hk
        have h2 := hSn.conj_mem _ (hle h1) c
        simpa [mul_assoc] using h2
      have h1 : c * w * c⁻¹ ∈ Subgroup.centralizer (K : Set Y) := by
        refine conj_mem_centralizer_of (fun k hk => ?_)
        have hk' : c⁻¹ * k * c ∈ GLBConj c K := by
          rw [mem_gLBConj]
          simpa [mul_assoc] using hk
        exact Subgroup.mem_centralizer_iff.1 (hWK _ hK' hK'S hw) _ hk'
      rw [hz']
      exact (Subgroup.centralizer _).mul_mem h1 ((Subgroup.centralizer _).inv_mem (hWK K hK hKS hw))
  have hzP : z ∈ CFSG.Open.pCore p Y := mem_pCore_of_centralizes hp hcore hzF hzK
  have hwz : Commute z w := Subgroup.mem_centralizer_iff.1 (hWF hw) z hzP
  have hcw : c * w * c⁻¹ = z * w := by rw [hz]; group
  have hpow : ∀ n : ℕ, c * w ^ n * c⁻¹ = z ^ n * w ^ n := by
    intro n
    have h1 : c * w ^ n * c⁻¹ = (c * w * c⁻¹) ^ n := by
      rw [← conj_pow]
    rw [h1, hcw, hwz.mul_pow]
  obtain ⟨a, ha⟩ := hW2 ⟨w, hw⟩
  have ha' : w ^ (2 ^ a) = 1 := by
    have := congrArg Subtype.val ha
    simpa using this
  have hza : z ^ (2 ^ a) = 1 := by
    have h1 := hpow (2 ^ a)
    rw [ha', mul_one, mul_one, mul_inv_cancel] at h1
    exact h1.symm
  obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := Y) p) ⟨z, hzP⟩
  have hzb : z ^ (p ^ b) = 1 := by
    have := congrArg Subtype.val hb
    simpa using this
  have hz1 : z = 1 := eq_one_of_pow_two_of_pow_p hp hp2 hza hzb
  rw [hz] at hz1
  calc c * w = (c * w * c⁻¹ * w⁻¹) * (w * c) := by group
    _ = w * c := by rw [hz1, one_mul]

theorem commutator_mem_pCore_two {X : Type*} [Group X] [Finite X] (Q : Subgroup X)
    [hQn : Q.Normal] {g c : X} (hg2 : ∃ a : ℕ, g ^ (2 ^ a) = 1)
    (hgQ : ∀ q ∈ Q, g * q * g⁻¹ * q⁻¹ ∈ CFSG.pCore 2 X)
    (hcg : c * g * c⁻¹ * g⁻¹ ∈ Q) : c * g * c⁻¹ * g⁻¹ ∈ CFSG.pCore 2 X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup X := CFSG.pCore 2 X with hN
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  set w : X := c * g * c⁻¹ * g⁻¹ with hw
  have hgcomm : ∀ q ∈ Q, π g * π q = π q * π g := by
    intro q hq
    have h1 : π (g * q * g⁻¹ * q⁻¹) = 1 := (QuotientGroup.eq_one_iff _).2 (hgQ q hq)
    simp only [map_mul, map_inv] at h1
    calc π g * π q = (π g * π q * (π g)⁻¹ * (π q)⁻¹) * (π q * π g) := by group
      _ = π q * π g := by rw [h1, one_mul]
  have hcg' : π c * π g * (π c)⁻¹ = π w * π g := by
    rw [hw]; simp only [map_mul, map_inv]; group
  have hwcomm : ∀ q ∈ Q, π w * π q = π q * π w := by
    intro q hq
    have hq₁ : c⁻¹ * q * c ∈ Q := by
      have := hQn.conj_mem q hq c⁻¹
      simpa using this
    have h1 := hgcomm _ hq₁
    have hq' : π c * π (c⁻¹ * q * c) * (π c)⁻¹ = π q := by
      simp only [map_mul, map_inv]; group
    have h2 : (π c * π g * (π c)⁻¹) * (π c * π (c⁻¹ * q * c) * (π c)⁻¹) =
        (π c * π (c⁻¹ * q * c) * (π c)⁻¹) * (π c * π g * (π c)⁻¹) := by
      calc (π c * π g * (π c)⁻¹) * (π c * π (c⁻¹ * q * c) * (π c)⁻¹)
          = π c * (π g * π (c⁻¹ * q * c)) * (π c)⁻¹ := by group
        _ = π c * (π (c⁻¹ * q * c) * π g) * (π c)⁻¹ := by rw [h1]
        _ = (π c * π (c⁻¹ * q * c) * (π c)⁻¹) * (π c * π g * (π c)⁻¹) := by group
    rw [hcg', hq'] at h2
    have h3 := hgcomm q hq
    have h4 : π w * π q * π g = π q * π w * π g := by
      calc π w * π q * π g = π w * (π q * π g) := by group
        _ = π w * (π g * π q) := by rw [h3]
        _ = π w * π g * π q := by group
        _ = π q * (π w * π g) := h2
        _ = π q * π w * π g := by group
    exact mul_right_cancel h4
  have hwg : Commute (π w) (π g) := (hgcomm w hcg).symm
  obtain ⟨a, ha⟩ := hg2
  have hwa : π w ^ (2 ^ a) = 1 := by
    have h1 : π c * π g ^ (2 ^ a) * (π c)⁻¹ = (π c * π g * (π c)⁻¹) ^ (2 ^ a) := by
      rw [← conj_pow]
    rw [hcg', hwg.mul_pow, ← map_pow, ha, map_one, mul_one, mul_one, mul_inv_cancel] at h1
    exact h1.symm
  set Qb : Subgroup (X ⧸ N) := Q.map π with hQb
  have hQbn : Qb.Normal := Subgroup.Normal.map hQn π (QuotientGroup.mk'_surjective N)
  let Rb : Subgroup (X ⧸ N) :=
    { carrier := {y | y ∈ Qb ∧ (∀ q ∈ Qb, y * q = q * y) ∧ ∃ n : ℕ, y ^ (2 ^ n) = 1}
      one_mem' := ⟨Qb.one_mem, fun q _ => by simp, ⟨0, by simp⟩⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨h₁Q, h₁c, n₁, h₁n⟩ ⟨h₂Q, h₂c, n₂, h₂n⟩
        refine ⟨Qb.mul_mem h₁Q h₂Q, fun q hq => ?_, n₁ + n₂, ?_⟩
        · calc y₁ * y₂ * q = y₁ * (q * y₂) := by rw [mul_assoc, h₂c q hq]
            _ = (y₁ * q) * y₂ := by rw [mul_assoc]
            _ = (q * y₁) * y₂ := by rw [h₁c q hq]
            _ = q * (y₁ * y₂) := by rw [mul_assoc]
        · have hcomm : Commute y₁ y₂ := h₁c y₂ h₂Q
          rw [hcomm.mul_pow, pow_add, pow_mul, h₁n, one_pow, one_mul, mul_comm (2 ^ n₁),
            pow_mul, h₂n, one_pow]
      inv_mem' := by
        rintro y ⟨hQ, hc, n, hn⟩
        refine ⟨Qb.inv_mem hQ, fun q hq => ?_, n, by rw [inv_pow, hn, inv_one]⟩
        have := hc q hq
        calc y⁻¹ * q = y⁻¹ * (q * y) * y⁻¹ := by group
          _ = y⁻¹ * (y * q) * y⁻¹ := by rw [this]
          _ = q * y⁻¹ := by group }
  have hRbn : Rb.Normal := by
    refine ⟨fun y hy x => ?_⟩
    obtain ⟨hQ, hc, n, hn⟩ := hy
    refine ⟨hQbn.conj_mem y hQ x, fun q hq => ?_, n, ?_⟩
    · have hq' : x⁻¹ * q * x ∈ Qb := by
        have := hQbn.conj_mem q hq x⁻¹
        rwa [inv_inv] at this
      have h1 := hc _ hq'
      calc x * y * x⁻¹ * q = x * (y * (x⁻¹ * q * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * q * x) * y) * x⁻¹ := by rw [h1]
        _ = q * (x * y * x⁻¹) := by group
    · rw [conj_pow, hn, mul_one, mul_inv_cancel]
  set R : Subgroup X := Rb.comap π with hR
  have hRn : R.Normal := Subgroup.Normal.comap hRbn π
  have hR2 : IsPGroup 2 R := by
    intro r
    obtain ⟨-, -, n, hn⟩ := r.2
    have h1 : (r : X) ^ (2 ^ n) ∈ N := by
      have h2 : π ((r : X) ^ (2 ^ n)) = 1 := by rw [map_pow]; exact hn
      exact (QuotientGroup.eq_one_iff _).1 h2
    obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup (G := X) 2) ⟨_, h1⟩
    refine ⟨n + m, Subtype.ext ?_⟩
    have hm' : ((r : X) ^ (2 ^ n)) ^ (2 ^ m) = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    simp only [Subgroup.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hm']
  have hRN : R ≤ N := CFSG.LieType.BorelTits.le_pCore 2 hRn hR2
  have hwR : w ∈ R := by
    refine ⟨Subgroup.mem_map_of_mem π hcg, fun q hq => ?_, a, hwa⟩
    obtain ⟨q', hq', rfl⟩ := Subgroup.mem_map.1 hq
    exact hwcomm q' hq'
  exact hRN hwR

end Abstract

section Joins

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) : x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA y, hB y]

theorem card_eq_pow_of_dvd' {p : ℕ} [hp : Fact p.Prime] {Y S : Subgroup G}
    (hS : IsPGroup p ↥S) (hSY : S ≤ Y)
    (hdvd : p ^ (Nat.card ↥Y).factorization p ∣ Nat.card ↥S) :
    Nat.card ↥S = p ^ (Nat.card ↥Y).factorization p := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hS
  have hY0 : Nat.card ↥Y ≠ 0 := Nat.card_pos.ne'
  have hkY : p ^ k ∣ Nat.card ↥Y := by
    rw [← hk]
    exact Subgroup.card_dvd_of_le hSY
  have hk' : k ≤ (Nat.card ↥Y).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp.out hY0).1 hkY
  have hv : (Nat.card ↥Y).factorization p ≤ k := by
    rw [hk] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.out.one_lt).1 hdvd
  rw [hk]
  congr 1
  omega

theorem factorization_card_sup {p : ℕ} [hp : Fact p.Prime] {H L : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hint : ¬ p ∣ Nat.card ↥(H ⊓ L)) :
    (Nat.card ↥(H ⊔ L)).factorization p =
      (Nat.card ↥H).factorization p + (Nat.card ↥L).factorization p := by
  have h1 := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hHL
  have h0a : Nat.card ↥(H ⊔ L) ≠ 0 := Nat.card_pos.ne'
  have h0b : Nat.card ↥(H ⊓ L) ≠ 0 := Nat.card_pos.ne'
  have h0c : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have h0d : Nat.card ↥L ≠ 0 := Nat.card_pos.ne'
  have h2 := congrArg (fun n => n.factorization p) h1
  simp only [Nat.factorization_mul h0a h0b, Nat.factorization_mul h0c h0d, Finsupp.add_apply] at h2
  have h3 : (Nat.card ↥(H ⊓ L)).factorization p = 0 :=
    Nat.factorization_eq_zero_of_not_dvd hint
  omega

theorem exists_sylow_join {p : ℕ} [hp : Fact p.Prime] (C : Subgroup G) (𝓛 : Finset (Subgroup G))
    (hnorm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L' ≤ Subgroup.normalizer (L : Set G))
    (hint : ∀ L ∈ 𝓛, ∀ S : Finset (Subgroup G), S ⊆ 𝓛 → L ∉ S →
      ¬ p ∣ Nat.card ↥((⨆ L' ∈ S, L') ⊓ L))
    (hC : ∀ L ∈ 𝓛, p ^ (Nat.card ↥L).factorization p ∣ Nat.card ↥(L ⊓ C)) :
    ∃ P : Subgroup G, P ≤ (⨆ L ∈ 𝓛, L) ⊓ C ∧ IsPGroup p ↥P ∧
      Nat.card ↥P = p ^ (Nat.card ↥(⨆ L ∈ 𝓛, L)).factorization p := by
  classical
  suffices key : ∀ S : Finset (Subgroup G), S ⊆ 𝓛 → ∃ P : Subgroup G, P ≤ (⨆ L ∈ S, L) ⊓ C ∧
      IsPGroup p ↥P ∧ Nat.card ↥P = p ^ (Nat.card ↥(⨆ L ∈ S, L)).factorization p from
    key 𝓛 subset_rfl
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨⊥, bot_le, IsPGroup.of_bot, ?_⟩
    simp
  | insert L S hLS ih =>
    intro hsub
    have hL𝓛 : L ∈ 𝓛 := hsub (Finset.mem_insert_self L S)
    have hS𝓛 : S ⊆ 𝓛 := (Finset.subset_insert L S).trans hsub
    obtain ⟨PH, hPH, hPHp, hPHc⟩ := ih hS𝓛
    set H : Subgroup G := ⨆ L' ∈ S, L' with hH
    rw [Finset.iSup_insert, sup_comm]
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      iSup₂_le fun L' hL' => hnorm L hL𝓛 L' (hS𝓛 hL')
    set CL : Subgroup G := L ⊓ C with hCL
    have hPHN : PH ≤ Subgroup.normalizer (CL : Set G) := fun x hx =>
      mem_normalizer_inf (hHL (hPH hx).1) (Subgroup.le_normalizer (hPH hx).2)
    set K : Subgroup G := CL ⊔ PH with hK
    have hKN : K ≤ Subgroup.normalizer (CL : Set G) := sup_le Subgroup.le_normalizer hPHN
    obtain ⟨T, hTK, hPHT, hTp, hTd⟩ := Sec13h.sylow_inf_normal_dvd (G := G) K CL PH le_sup_left
      (fun k hk c hc => (Subgroup.mem_normalizer_iff.1 (hKN hk) c).1 hc) le_sup_right hPHp
    have hL0 : Nat.card ↥CL ≠ 0 := Nat.card_pos.ne'
    have hvL : (Nat.card ↥L).factorization p ≤ (Nat.card ↥CL).factorization p :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp.out hL0).1 (hC L hL𝓛)
    have hTd' : p ^ (Nat.card ↥L).factorization p ∣ Nat.card ↥(T ⊓ CL) :=
      (pow_dvd_pow p hvL).trans hTd
    set X : Subgroup G := T ⊓ CL with hX
    have hPHX : PH ≤ Subgroup.normalizer (X : Set G) := fun x hx =>
      mem_normalizer_inf (Subgroup.le_normalizer (hPHT hx)) (hPHN hx)
    have hbot : PH ⊓ X = ⊥ := by
      have h1 : PH ⊓ (H ⊓ L) = ⊥ :=
        isPGroup_inf_eq_bot_of_not_dvd hp.out hPHp (hint L hL𝓛 S hS𝓛 hLS)
      exact le_bot_iff.1 (h1 ▸ le_inf inf_le_left
        (le_inf (inf_le_left.trans (hPH.trans inf_le_left)) (inf_le_right.trans
          (inf_le_right.trans inf_le_left))))
    have hcard := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hPHX
    rw [hbot, Subgroup.card_bot, mul_one] at hcard
    have hTsup : PH ⊔ X ≤ T := sup_le hPHT inf_le_left
    have hdvdT : p ^ ((Nat.card ↥H).factorization p + (Nat.card ↥L).factorization p) ∣
        Nat.card ↥T := by
      rw [pow_add, ← hPHc]
      refine dvd_trans ?_ (Subgroup.card_dvd_of_le hTsup)
      rw [hcard]
      exact mul_dvd_mul_left _ hTd'
    have hTle : T ≤ H ⊔ L := hTK.trans (sup_le (inf_le_left.trans le_sup_right)
      (hPH.trans (inf_le_left.trans le_sup_left)))
    have hTC : T ≤ C := hTK.trans (sup_le inf_le_right (hPH.trans inf_le_right))
    have hv := factorization_card_sup hHL (hint L hL𝓛 S hS𝓛 hLS)
    refine ⟨T, le_inf hTle hTC, hTp, card_eq_pow_of_dvd' hTp hTle ?_⟩
    rw [hv]
    exact hdvdT

theorem isElemAbelian_sup {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : IsElemAbelian p (A ⊔ B) := by
  have hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hCA : A ⊔ B ≤ Subgroup.centralizer (A : Set G) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hAc y hy x hx)
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hc y hy x hx)
  have hCB : A ⊔ B ≤ Subgroup.centralizer (B : Set G) := sup_le
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => (hc x hx y hy).symm)
    (fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy => hBc y hy x hx)
  have hAB : A ⊔ B ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.1 hCA) (Subgroup.le_centralizer_iff.1 hCB)
  refine isElemAbelian_of_comm_pow (fun x hx y hy => ?_) (fun x hx => ?_)
  · exact Subgroup.mem_centralizer_iff.1 (hAB hy) x hx
  · obtain ⟨a, ha, b, hb, rfl⟩ := Lemma137.mem_sup_of_comm hc x hx
    rw [(show Commute a b from hc a ha b hb).mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem card_sup_of_comm {A B : Subgroup G} (hc : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x)
    (hbot : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card ↥A * Nat.card ↥B := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).1
  rwa [hbot, Subgroup.card_bot, mul_one] at h

theorem mod_comm_pow {p : ℕ} {E H : Subgroup G} (hE : IsElemAbelian p E)
    (hEH : E ≤ Subgroup.normalizer (H : Set G)) {x y : G} (hx : x ∈ E ⊔ H) (hy : y ∈ E ⊔ H) :
    x * y * x⁻¹ * y⁻¹ ∈ H ∧ x ^ p ∈ H := by
  set K : Subgroup G := E ⊔ H with hK
  have hHK : H ≤ K := le_sup_right
  have hEK : E ≤ K := le_sup_left
  haveI hn : (H.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHK).2 (sup_le hEH Subgroup.le_normalizer)
  set π := QuotientGroup.mk' (H.subgroupOf K) with hπ
  have hdec : ∀ (z : G) (hz : z ∈ K), ∃ (e : G) (he : e ∈ E), π ⟨z, hz⟩ = π ⟨e, hEK he⟩ := by
    intro z hz
    have h1 : z ∈ ((E : Set G) * (H : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right E H hEH]
      exact hz
    obtain ⟨e, he, h, hh, rfl⟩ := h1
    refine ⟨e, he, ?_⟩
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have : (e * h)⁻¹ * e = h⁻¹ := by group
    rw [this]
    exact H.inv_mem hh
  obtain ⟨e, he, hxe⟩ := hdec x hx
  obtain ⟨e', he', hye⟩ := hdec y hy
  have hee' : e * e' = e' * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
  constructor
  · have h1 : π ((⟨x, hx⟩ : ↥K) * ⟨y, hy⟩ * (⟨x, hx⟩ : ↥K)⁻¹ * (⟨y, hy⟩ : ↥K)⁻¹) = 1 := by
      simp only [map_mul, map_inv, hxe, hye]
      have hc : π ⟨e, hEK he⟩ * π ⟨e', hEK he'⟩ = π ⟨e', hEK he'⟩ * π ⟨e, hEK he⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hee'
      rw [hc]
      group
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2
  · have h1 : π ((⟨x, hx⟩ : ↥K) ^ p) = 1 := by
      rw [map_pow, hxe, ← map_pow]
      have : (⟨e, hEK he⟩ : ↥K) ^ p = 1 := Subtype.ext (by simpa using hE.2 e he)
      rw [this, map_one]
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    rw [Subgroup.mem_subgroupOf] at h2
    simpa using h2

theorem two_factor_card {p : ℕ} [hp : Fact p.Prime] {H L : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hLH : L ≤ Subgroup.normalizer (H : Set G))
    (hN : ¬ p ∣ Nat.card ↥(H ⊓ L)) {E : Subgroup G} (hE : IsElemAbelian p E) (hEle : E ≤ H ⊔ L) :
    ∃ F : Subgroup G, F ≤ L ∧ IsElemAbelian p F ∧
      Nat.card ↥E = Nat.card ↥(E ⊓ H) * Nat.card ↥F := by
  have hEH : E ≤ Subgroup.normalizer (H : Set G) := hEle.trans (sup_le Subgroup.le_normalizer hLH)
  set X : Subgroup G := (E ⊔ H) ⊓ L with hX
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := fun h hh =>
    mem_normalizer_inf (Subgroup.le_normalizer (Subgroup.mem_sup_right hh)) (hHL hh)
  have hEHeq : E ⊔ H = H ⊔ X := by
    apply le_antisymm
    · intro y hy
      have hyHL : y ∈ ((H : Set G) * (L : Set G)) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right H L hHL]
        exact (sup_le hEle le_sup_left) hy
      obtain ⟨h, hh, ℓ, hℓ, rfl⟩ := hyHL
      have hℓE : ℓ ∈ E ⊔ H := by
        have : ℓ = h⁻¹ * (h * ℓ) := by group
        rw [this]
        exact (E ⊔ H).mul_mem ((E ⊔ H).inv_mem (Subgroup.mem_sup_right hh)) hy
      exact (H ⊔ X).mul_mem (Subgroup.mem_sup_left hh) (Subgroup.mem_sup_right (show ℓ ∈ X from ⟨hℓE, hℓ⟩))
    · exact sup_le le_sup_right inf_le_left
  have hHXinf : H ⊓ X = H ⊓ L := by
    rw [hX, ← inf_assoc, inf_of_le_left (le_sup_right : H ≤ E ⊔ H)]
  have c1 := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hEH
  have c2 := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hHX
  rw [← hEHeq, hHXinf] at c2
  have c3 : Nat.card ↥E * Nat.card ↥(H ⊓ L) = Nat.card ↥X * Nat.card ↥(E ⊓ H) := by
    have hH0 : 0 < Nat.card ↥H := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hH0
    calc Nat.card ↥H * (Nat.card ↥E * Nat.card ↥(H ⊓ L))
        = (Nat.card ↥E * Nat.card ↥H) * Nat.card ↥(H ⊓ L) := by ring
      _ = Nat.card ↥(E ⊔ H) * Nat.card ↥(E ⊓ H) * Nat.card ↥(H ⊓ L) := by rw [c1]
      _ = (Nat.card ↥(E ⊔ H) * Nat.card ↥(H ⊓ L)) * Nat.card ↥(E ⊓ H) := by ring
      _ = Nat.card ↥H * Nat.card ↥X * Nat.card ↥(E ⊓ H) := by rw [c2]
      _ = Nat.card ↥H * (Nat.card ↥X * Nat.card ↥(E ⊓ H)) := by ring
  obtain ⟨P⟩ : Nonempty (Sylow p ↥X) := inferInstance
  set F : Subgroup G := (P : Subgroup ↥X).map X.subtype with hF
  have hFX : F ≤ X := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hFc : Nat.card ↥F = p ^ (Nat.card ↥X).factorization p := by
    rw [hF, Subgroup.card_map_of_injective X.subtype_injective]
    exact Sylow.card_eq_multiplicity P
  have hFp : IsPGroup p ↥F := IsPGroup.of_card hFc
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 (Sec13h.isPGroup_of_isElemAbelian' hE)
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.1 ((Sec13h.isPGroup_of_isElemAbelian' hE).to_le (inf_le_left : E ⊓ H ≤ E))
  have hv : (Nat.card ↥X).factorization p + b = a := by
    have h0X : Nat.card ↥X ≠ 0 := Nat.card_pos.ne'
    have h0N : Nat.card ↥(H ⊓ L) ≠ 0 := Nat.card_pos.ne'
    have h1 : (Nat.card ↥E * Nat.card ↥(H ⊓ L)).factorization p =
        (Nat.card ↥X * Nat.card ↥(E ⊓ H)).factorization p := by rw [c3]
    rw [ha, hb] at h1
    rw [Nat.factorization_mul (pow_ne_zero _ hp.out.ne_zero) h0N,
      Nat.factorization_mul h0X (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hN, Nat.factorization_pow,
      Nat.factorization_pow, Finsupp.smul_apply, Finsupp.smul_apply,
      Nat.Prime.factorization_self hp.out] at h1
    simp only [smul_eq_mul, mul_one, add_zero] at h1
    omega
  have hFbot : F ⊓ (H ⊓ L) = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out hFp hN
  have hFea : IsElemAbelian p F := by
    refine isElemAbelian_of_comm_pow (fun x hx y hy => ?_) (fun x hx => ?_)
    · obtain ⟨h1, -⟩ := mod_comm_pow hE hEH (hFX hx).1 (hFX hy).1
      have hcL : x * y * x⁻¹ * y⁻¹ ∈ L :=
        L.mul_mem (L.mul_mem (L.mul_mem (hFX hx).2 (hFX hy).2) (L.inv_mem (hFX hx).2))
          (L.inv_mem (hFX hy).2)
      have hcF : x * y * x⁻¹ * y⁻¹ ∈ F :=
        F.mul_mem (F.mul_mem (F.mul_mem hx hy) (F.inv_mem hx)) (F.inv_mem hy)
      have h2 : x * y * x⁻¹ * y⁻¹ ∈ F ⊓ (H ⊓ L) := ⟨hcF, h1, hcL⟩
      rw [hFbot, Subgroup.mem_bot] at h2
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [h2, one_mul]
    · obtain ⟨-, h2⟩ := mod_comm_pow hE hEH (hFX hx).1 (hFX hx).1
      have h3 : x ^ p ∈ F ⊓ (H ⊓ L) := ⟨F.pow_mem hx p, h2, L.pow_mem (hFX hx).2 p⟩
      rwa [hFbot, Subgroup.mem_bot] at h3
  refine ⟨F, hFX.trans inf_le_right, hFea, ?_⟩
  rw [ha, hb, hFc, ← hv, pow_add, mul_comm]

theorem factorization_pow_mul {p : ℕ} (hp : p.Prime) (k v : ℕ) (hv : ¬ p ∣ v) :
    (p ^ k * v).factorization p = k := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ dvd_zero p)
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hv0, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self hp,
    Nat.factorization_eq_zero_of_not_dvd hv, smul_eq_mul, mul_one, add_zero]

theorem isElemAbelian_of_le {p : ℕ} {E F : Subgroup G} (hE : IsElemAbelian p E) (hFE : F ≤ E) :
    IsElemAbelian p F :=
  isElemAbelian_of_comm_pow
    (fun x hx y hy => congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hFE hx⟩ ⟨y, hFE hy⟩))
    (fun x hx => hE.2 x (hFE hx))

theorem gLBConj_le_sup_inf {H L K : Subgroup G} (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hLH : L ≤ Subgroup.normalizer (H : Set G)) (hKL : K ≤ L) {h : G} (hh : h ∈ H) :
    GLBConj h K ≤ K ⊔ (H ⊓ L) := by
  intro z hz
  rw [mem_gLBConj] at hz
  set y := h * z * h⁻¹ with hy
  have hyL : y ∈ L := hKL hz
  have hz' : z = y * (y⁻¹ * (h⁻¹ * y * h)) := by rw [hy]; group
  have hn : y⁻¹ * (h⁻¹ * y * h) ∈ H ⊓ L := by
    constructor
    · have h1 : y⁻¹ * h⁻¹ * y⁻¹⁻¹ ∈ H :=
        (Subgroup.mem_normalizer_iff.1 (hLH (L.inv_mem hyL)) h⁻¹).1 (H.inv_mem hh)
      rw [inv_inv] at h1
      have : y⁻¹ * (h⁻¹ * y * h) = (y⁻¹ * h⁻¹ * y) * h := by group
      rw [this]
      exact H.mul_mem h1 hh
    · have h1 : h⁻¹ * y * h⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hHL (H.inv_mem hh)) y).1 hyL
      rw [inv_inv] at h1
      exact L.mul_mem (L.inv_mem hyL) h1
  rw [hz']
  exact (K ⊔ (H ⊓ L)).mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hn)

theorem eq_of_mul_eq_mul_of_le {a b A B : ℕ} (ha : a ≤ A) (hb : b ≤ B) (hA : 0 < A) (hB : 0 < B)
    (h : a * b = A * B) : a = A ∧ b = B := by
  have h1 : a = A := by
    by_contra hne
    have hlt : a < A := lt_of_le_of_ne ha hne
    have h2 : a * b ≤ a * B := Nat.mul_le_mul_left a hb
    have h3 : a * B < A * B := Nat.mul_lt_mul_of_pos_right hlt hB
    omega
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hA h⟩

theorem two_factor_conj {p : ℕ} [hp : Fact p.Prime] {H L : Subgroup G}
    (hHL : H ≤ Subgroup.normalizer (L : Set G)) (hLH : L ≤ Subgroup.normalizer (H : Set G))
    (hN : ¬ p ∣ Nat.card ↥(H ⊓ L)) {mH mL : ℕ}
    (haH : ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → Nat.card ↥E ≤ mH)
    (haL : ∀ E : Subgroup G, E ≤ L → IsElemAbelian p E → Nat.card ↥E ≤ mL)
    (hcH : ∀ E₁ E₂ : Subgroup G, E₁ ≤ H → E₂ ≤ H → IsElemAbelian p E₁ → IsElemAbelian p E₂ →
      Nat.card ↥E₁ = mH → Nat.card ↥E₂ = mH → ∃ g ∈ H, GLBConj g E₁ = E₂)
    (hcL : ∀ E₁ E₂ : Subgroup G, E₁ ≤ L → E₂ ≤ L → IsElemAbelian p E₁ → IsElemAbelian p E₂ →
      Nat.card ↥E₁ = mL → Nat.card ↥E₂ = mL → ∃ g ∈ L, GLBConj g E₁ = E₂)
    {E₁ E₂ : Subgroup G} (h₁ : E₁ ≤ H ⊔ L) (h₂ : E₂ ≤ H ⊔ L) (he₁ : IsElemAbelian p E₁)
    (he₂ : IsElemAbelian p E₂) (hc₁ : Nat.card ↥E₁ = mH * mL) (hc₂ : Nat.card ↥E₂ = mH * mL) :
    ∃ g ∈ H ⊔ L, GLBConj g E₁ = E₂ := by
  have hbotea : IsElemAbelian p (⊥ : Subgroup G) :=
    isElemAbelian_of_comm_pow (fun x hx y hy => by
      rw [Subgroup.mem_bot] at hx hy; rw [hx, hy]) (fun x hx => by
      rw [Subgroup.mem_bot] at hx; rw [hx, one_pow])
  have hmH : 0 < mH := lt_of_lt_of_le Nat.card_pos (haH ⊥ bot_le hbotea)
  have hmL : 0 < mL := lt_of_lt_of_le Nat.card_pos (haL ⊥ bot_le hbotea)
  have hN' : ¬ p ∣ Nat.card ↥(L ⊓ H) := by rw [inf_comm]; exact hN
  have hsplit : ∀ E : Subgroup G, E ≤ H ⊔ L → IsElemAbelian p E → Nat.card ↥E = mH * mL →
      Nat.card ↥(E ⊓ H) = mH ∧ Nat.card ↥(E ⊓ L) = mL ∧ E = (E ⊓ H) ⊔ (E ⊓ L) := by
    intro E hEle hE hEc
    obtain ⟨F, hFL, hFea, hFc⟩ := two_factor_card hHL hLH hN hE hEle
    obtain ⟨F', hF'H, hF'ea, hF'c⟩ := two_factor_card hLH hHL hN' hE (by rwa [sup_comm])
    have hEH : Nat.card ↥(E ⊓ H) = mH := (eq_of_mul_eq_mul_of_le
      (haH _ inf_le_right (isElemAbelian_of_le hE inf_le_left)) (haL F hFL hFea) hmH hmL
      (hFc.symm.trans hEc)).1
    have hEL : Nat.card ↥(E ⊓ L) = mL := (eq_of_mul_eq_mul_of_le
      (haL _ inf_le_right (isElemAbelian_of_le hE inf_le_left)) (haH F' hF'H hF'ea) hmL hmH
      (by rw [← hF'c, hEc, mul_comm])).1
    refine ⟨hEH, hEL, ?_⟩
    have hcomm : ∀ x ∈ E ⊓ H, ∀ y ∈ E ⊓ L, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)
    have hbot : (E ⊓ H) ⊓ (E ⊓ L) = ⊥ := by
      have h1 : (E ⊓ H) ⊓ (E ⊓ L) ≤ E ⊓ (H ⊓ L) := le_inf (inf_le_left.trans inf_le_left)
        (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right))
      have h2 : E ⊓ (H ⊓ L) = ⊥ :=
        isPGroup_inf_eq_bot_of_not_dvd hp.out (Sec13h.isPGroup_of_isElemAbelian' hE) hN
      exact le_bot_iff.1 (h2 ▸ h1)
    have hle : (E ⊓ H) ⊔ (E ⊓ L) ≤ E := sup_le inf_le_left inf_le_left
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [card_sup_of_comm hcomm hbot, hEH, hEL, hEc]
  obtain ⟨hE₁H, hE₁L, hE₁eq⟩ := hsplit E₁ h₁ he₁ hc₁
  obtain ⟨hE₂H, hE₂L, hE₂eq⟩ := hsplit E₂ h₂ he₂ hc₂
  obtain ⟨h, hh, hhc⟩ := hcH (E₁ ⊓ H) (E₂ ⊓ H) inf_le_right inf_le_right
    (isElemAbelian_of_le he₁ inf_le_left) (isElemAbelian_of_le he₂ inf_le_left) hE₁H hE₂H
  obtain ⟨ℓ, hℓ, hℓc⟩ := hcL (E₁ ⊓ L) (E₂ ⊓ L) inf_le_right inf_le_right
    (isElemAbelian_of_le he₁ inf_le_left) (isElemAbelian_of_le he₂ inf_le_left) hE₁L hE₂L
  set N : Subgroup G := H ⊓ L with hNdef
  have hNn : H ⊔ L ≤ Subgroup.normalizer (N : Set G) := sup_le
    (fun x hx => mem_normalizer_inf (Subgroup.le_normalizer hx) (hHL hx))
    (fun x hx => mem_normalizer_inf (hLH hx) (Subgroup.le_normalizer hx))
  have hsup : ∀ (g : G) (A B : Subgroup G), GLBConj g (A ⊔ B) = GLBConj g A ⊔ GLBConj g B :=
    fun g A B => Subgroup.map_sup A B _
  set E₁' : Subgroup G := GLBConj ℓ (GLBConj h E₁) with hE₁'
  have hstep1 : GLBConj h E₁ ≤ (E₂ ⊓ H) ⊔ ((E₁ ⊓ L) ⊔ N) := by
    conv_lhs => rw [hE₁eq]
    rw [hsup, hhc]
    exact sup_le_sup_left (gLBConj_le_sup_inf hHL hLH inf_le_right hh) _
  have hℓN : GLBConj ℓ N ≤ N := by
    intro z hz
    rw [mem_gLBConj] at hz
    have h1 := (Subgroup.mem_normalizer_iff.1 (hNn (Subgroup.mem_sup_right (L.inv_mem hℓ))) _).1 hz
    simpa [mul_assoc] using h1
  have hE₁'le : E₁' ≤ E₂ ⊔ N := by
    have h1 : E₁' ≤ GLBConj ℓ ((E₂ ⊓ H) ⊔ ((E₁ ⊓ L) ⊔ N)) := gLBConj_mono ℓ hstep1
    rw [hsup, hsup, hℓc] at h1
    refine h1.trans (sup_le ?_ (sup_le ?_ ?_))
    · have h2 := gLBConj_le_sup_inf hLH hHL (inf_le_right : E₂ ⊓ H ≤ H) hℓ
      rw [inf_comm L H] at h2
      exact h2.trans (sup_le_sup_right inf_le_left _)
    · exact (inf_le_left : E₂ ⊓ L ≤ E₂).trans le_sup_left
    · exact hℓN.trans le_sup_right
  have hE₁'p : IsPGroup p ↥E₁' := Sec13h.isPGroup_of_isElemAbelian'
    (sec9_isElemAbelian_gLBConj ℓ (sec9_isElemAbelian_gLBConj h he₁))
  have hE₁'c : Nat.card ↥E₁' = Nat.card ↥E₂ := by rw [hE₁', sec9_card_gLBConj, sec9_card_gLBConj, hc₁, hc₂]
  have hE₂p := Sec13h.isPGroup_of_isElemAbelian' he₂
  have hE₂N : E₂ ⊓ N = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out hE₂p hN
  have hcardW := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer (h₂.trans hNn)
  rw [hE₂N, Subgroup.card_bot, mul_one] at hcardW
  obtain ⟨c, hcc⟩ := IsPGroup.iff_card.1 hE₂p
  have hE₂c : Nat.card ↥E₂ = p ^ (Nat.card ↥(E₂ ⊔ N)).factorization p := by
    rw [hcardW, hcc, factorization_pow_mul hp.out c _ hN]
  obtain ⟨z, hz, hzc⟩ := Sec13h.exists_conj_le_of_sylow (E₂ ⊔ N) E₂ E₁' le_sup_left hE₂c hE₁'le hE₁'p
  refine ⟨h * ℓ * z, (H ⊔ L).mul_mem ((H ⊔ L).mul_mem (Subgroup.mem_sup_left hh)
    (Subgroup.mem_sup_right hℓ)) ((sup_le h₂ (inf_le_left.trans le_sup_left)) hz), ?_⟩
  have h3 : GLBConj (h * ℓ * z) E₁ = GLBConj z E₁' := by
    rw [hE₁', gLBConj_gLBConj, gLBConj_gLBConj, mul_assoc]
  rw [h3]
  refine Subgroup.eq_of_le_of_card_ge hzc ?_
  rw [sec9_card_gLBConj, hE₁'c]

theorem le_normalizer_iSup_finset {K : Subgroup G} (S : Finset (Subgroup G))
    (h : ∀ L' ∈ S, K ≤ Subgroup.normalizer (L' : Set G)) :
    K ≤ Subgroup.normalizer ((⨆ L' ∈ S, L' : Subgroup G) : Set G) := by
  intro x hx
  refine Subgroup.iInf_normalizer_le_normalizer_iSup _ (Subgroup.mem_iInf.2 fun L' => ?_)
  refine Subgroup.iInf_normalizer_le_normalizer_iSup _ (Subgroup.mem_iInf.2 fun hL' => ?_)
  exact h L' hL' hx

theorem conj_join {p : ℕ} [hp : Fact p.Prime] (𝓛 : Finset (Subgroup G))
    (hnorm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L' ≤ Subgroup.normalizer (L : Set G))
    (hint : ∀ L ∈ 𝓛, ∀ S : Finset (Subgroup G), S ⊆ 𝓛 → L ∉ S →
      ¬ p ∣ Nat.card ↥((⨆ L' ∈ S, L') ⊓ L))
    (F : Subgroup G → Subgroup G) (hF : ∀ L ∈ 𝓛, Sec13h.IsMaxEA p L (F L))
    (hFc : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, ∀ x ∈ F L, ∀ y ∈ F L', x * y = y * x)
    (hconj : ∀ L ∈ 𝓛, ∀ E₁ E₂ : Subgroup G, Sec13h.IsMaxEA p L E₁ → Sec13h.IsMaxEA p L E₂ →
      ∃ g ∈ L, GLBConj g E₁ = E₂) :
    (⨆ L ∈ 𝓛, F L) ≤ (⨆ L ∈ 𝓛, L) ∧ IsElemAbelian p (⨆ L ∈ 𝓛, F L) ∧
    (∀ E : Subgroup G, E ≤ ⨆ L ∈ 𝓛, L → IsElemAbelian p E →
      Nat.card ↥E ≤ Nat.card ↥(⨆ L ∈ 𝓛, F L)) ∧
    (∀ E₁ E₂ : Subgroup G, E₁ ≤ ⨆ L ∈ 𝓛, L → E₂ ≤ ⨆ L ∈ 𝓛, L → IsElemAbelian p E₁ →
      IsElemAbelian p E₂ → Nat.card ↥E₁ = Nat.card ↥(⨆ L ∈ 𝓛, F L) →
      Nat.card ↥E₂ = Nat.card ↥(⨆ L ∈ 𝓛, F L) → ∃ g ∈ ⨆ L ∈ 𝓛, L, GLBConj g E₁ = E₂) := by
  classical
  have hbotea : IsElemAbelian p (⊥ : Subgroup G) :=
    isElemAbelian_of_comm_pow (fun x hx y hy => by
      rw [Subgroup.mem_bot] at hx hy; rw [hx, hy]) (fun x hx => by
      rw [Subgroup.mem_bot] at hx; rw [hx, one_pow])
  suffices key : ∀ S : Finset (Subgroup G), S ⊆ 𝓛 →
      (⨆ L ∈ S, F L) ≤ (⨆ L ∈ S, L) ∧ IsElemAbelian p (⨆ L ∈ S, F L) ∧
      (∀ E : Subgroup G, E ≤ ⨆ L ∈ S, L → IsElemAbelian p E →
        Nat.card ↥E ≤ Nat.card ↥(⨆ L ∈ S, F L)) ∧
      (∀ E₁ E₂ : Subgroup G, E₁ ≤ ⨆ L ∈ S, L → E₂ ≤ ⨆ L ∈ S, L → IsElemAbelian p E₁ →
        IsElemAbelian p E₂ → Nat.card ↥E₁ = Nat.card ↥(⨆ L ∈ S, F L) →
        Nat.card ↥E₂ = Nat.card ↥(⨆ L ∈ S, F L) → ∃ g ∈ ⨆ L ∈ S, L, GLBConj g E₁ = E₂) from
    key 𝓛 subset_rfl
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot]
    refine ⟨le_rfl, hbotea, fun E hE _ => Subgroup.card_le_of_le hE, ?_⟩
    intro E₁ E₂ h₁ h₂ _ _ _ _
    refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [gLBConj_one, le_bot_iff.1 h₁, le_bot_iff.1 h₂]
  | insert L S hLS ih =>
    intro hsub
    have hL𝓛 : L ∈ 𝓛 := hsub (Finset.mem_insert_self L S)
    have hS𝓛 : S ⊆ 𝓛 := (Finset.subset_insert L S).trans hsub
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih hS𝓛
    rw [Finset.iSup_insert, Finset.iSup_insert]
    set H : Subgroup G := ⨆ L' ∈ S, L' with hH
    set ES : Subgroup G := ⨆ L' ∈ S, F L' with hES
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      iSup₂_le fun L' hL' => hnorm L hL𝓛 L' (hS𝓛 hL')
    have hLH : L ≤ Subgroup.normalizer (H : Set G) :=
      le_normalizer_iSup_finset S fun L' hL' => hnorm L' (hS𝓛 hL') L hL𝓛
    have hN : ¬ p ∣ Nat.card ↥(H ⊓ L) := hint L hL𝓛 S hS𝓛 hLS
    obtain ⟨hFLle, hFLea, hFLmax⟩ := hF L hL𝓛
    have hcomm : ∀ x ∈ F L, ∀ y ∈ ES, x * y = y * x := by
      have h1 : ES ≤ Subgroup.centralizer ((F L : Subgroup G) : Set G) :=
        iSup₂_le fun L' hL' y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
          hFc L hL𝓛 L' (hS𝓛 hL') x hx y hy
      exact fun x hx y hy => Subgroup.mem_centralizer_iff.1 (h1 hy) x hx
    have hbot : F L ⊓ ES = ⊥ := by
      have h1 : F L ⊓ (H ⊓ L) = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out
        (Sec13h.isPGroup_of_isElemAbelian' hFLea) hN
      exact le_bot_iff.1 (h1 ▸ le_inf inf_le_left (le_inf (inf_le_right.trans ih1)
        (inf_le_left.trans hFLle)))
    have hcard : Nat.card ↥(F L ⊔ ES) = Nat.card ↥(F L) * Nat.card ↥ES := card_sup_of_comm hcomm hbot
    have haL : ∀ E : Subgroup G, E ≤ L → IsElemAbelian p E → Nat.card ↥E ≤ Nat.card ↥(F L) :=
      fun E hE hEe => hFLmax E hE hEe
    have hcL : ∀ E₁ E₂ : Subgroup G, E₁ ≤ L → E₂ ≤ L → IsElemAbelian p E₁ → IsElemAbelian p E₂ →
        Nat.card ↥E₁ = Nat.card ↥(F L) → Nat.card ↥E₂ = Nat.card ↥(F L) →
        ∃ g ∈ L, GLBConj g E₁ = E₂ := by
      intro E₁ E₂ h₁ h₂ he₁ he₂ hc₁ hc₂
      exact hconj L hL𝓛 E₁ E₂ ⟨h₁, he₁, fun F' hF' hF'e => (hFLmax F' hF' hF'e).trans hc₁.ge⟩
        ⟨h₂, he₂, fun F' hF' hF'e => (hFLmax F' hF' hF'e).trans hc₂.ge⟩
    refine ⟨sup_le_sup hFLle ih1, isElemAbelian_sup hFLea ih2 hcomm, ?_, ?_⟩
    · intro E hE hEe
      obtain ⟨F', hF'L, hF'e, hEc⟩ := two_factor_card hHL hLH hN hEe (by rwa [sup_comm])
      rw [hEc, hcard, mul_comm (Nat.card ↥(F L))]
      exact Nat.mul_le_mul (ih3 _ inf_le_right (isElemAbelian_of_le hEe inf_le_left))
        (haL F' hF'L hF'e)
    · intro E₁ E₂ h₁ h₂ he₁ he₂ hc₁ hc₂
      rw [hcard, mul_comm] at hc₁ hc₂
      obtain ⟨g, hg, hgc⟩ := two_factor_conj hHL hLH hN ih3 haL ih4 hcL (by rwa [sup_comm])
        (by rwa [sup_comm]) he₁ he₂ hc₁ hc₂
      exact ⟨g, by rwa [sup_comm], hgc⟩

theorem bound_join {p : ℕ} [hp : Fact p.Prime] (𝓛 : Finset (Subgroup G))
    (hnorm : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L' ≤ Subgroup.normalizer (L : Set G))
    (hint : ∀ L ∈ 𝓛, ∀ S : Finset (Subgroup G), S ⊆ 𝓛 → L ∉ S →
      ¬ p ∣ Nat.card ↥((⨆ L' ∈ S, L') ⊓ L))
    (F : Subgroup G → Subgroup G) (hF : ∀ L ∈ 𝓛, Sec13h.IsMaxEA p L (F L))
    (hFc : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, ∀ x ∈ F L, ∀ y ∈ F L', x * y = y * x) :
    (⨆ L ∈ 𝓛, F L) ≤ (⨆ L ∈ 𝓛, L) ∧ IsElemAbelian p (⨆ L ∈ 𝓛, F L) ∧
    (∀ E : Subgroup G, E ≤ ⨆ L ∈ 𝓛, L → IsElemAbelian p E →
      Nat.card ↥E ≤ Nat.card ↥(⨆ L ∈ 𝓛, F L)) := by
  classical
  have hbotea : IsElemAbelian p (⊥ : Subgroup G) :=
    isElemAbelian_of_comm_pow (fun x hx y hy => by
      rw [Subgroup.mem_bot] at hx hy; rw [hx, hy]) (fun x hx => by
      rw [Subgroup.mem_bot] at hx; rw [hx, one_pow])
  suffices key : ∀ S : Finset (Subgroup G), S ⊆ 𝓛 →
      (⨆ L ∈ S, F L) ≤ (⨆ L ∈ S, L) ∧ IsElemAbelian p (⨆ L ∈ S, F L) ∧
      (∀ E : Subgroup G, E ≤ ⨆ L ∈ S, L → IsElemAbelian p E →
        Nat.card ↥E ≤ Nat.card ↥(⨆ L ∈ S, F L)) from key 𝓛 subset_rfl
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp only [Finset.notMem_empty, iSup_false, iSup_bot]
    exact ⟨le_rfl, hbotea, fun E hE _ => Subgroup.card_le_of_le hE⟩
  | insert L S hLS ih =>
    intro hsub
    have hL𝓛 : L ∈ 𝓛 := hsub (Finset.mem_insert_self L S)
    have hS𝓛 : S ⊆ 𝓛 := (Finset.subset_insert L S).trans hsub
    obtain ⟨ih1, ih2, ih3⟩ := ih hS𝓛
    rw [Finset.iSup_insert, Finset.iSup_insert]
    set H : Subgroup G := ⨆ L' ∈ S, L' with hH
    set ES : Subgroup G := ⨆ L' ∈ S, F L' with hES
    have hHL : H ≤ Subgroup.normalizer (L : Set G) :=
      iSup₂_le fun L' hL' => hnorm L hL𝓛 L' (hS𝓛 hL')
    have hLH : L ≤ Subgroup.normalizer (H : Set G) :=
      le_normalizer_iSup_finset S fun L' hL' => hnorm L' (hS𝓛 hL') L hL𝓛
    have hN : ¬ p ∣ Nat.card ↥(H ⊓ L) := hint L hL𝓛 S hS𝓛 hLS
    obtain ⟨hFLle, hFLea, hFLmax⟩ := hF L hL𝓛
    have hcomm : ∀ x ∈ F L, ∀ y ∈ ES, x * y = y * x := by
      have h1 : ES ≤ Subgroup.centralizer ((F L : Subgroup G) : Set G) :=
        iSup₂_le fun L' hL' y hy => Subgroup.mem_centralizer_iff.2 fun x hx =>
          hFc L hL𝓛 L' (hS𝓛 hL') x hx y hy
      exact fun x hx y hy => Subgroup.mem_centralizer_iff.1 (h1 hy) x hx
    have hbot : F L ⊓ ES = ⊥ := by
      have h1 : F L ⊓ (H ⊓ L) = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out
        (Sec13h.isPGroup_of_isElemAbelian' hFLea) hN
      exact le_bot_iff.1 (h1 ▸ le_inf inf_le_left (le_inf (inf_le_right.trans ih1)
        (inf_le_left.trans hFLle)))
    have hcard : Nat.card ↥(F L ⊔ ES) = Nat.card ↥(F L) * Nat.card ↥ES := card_sup_of_comm hcomm hbot
    refine ⟨sup_le_sup hFLle ih1, isElemAbelian_sup hFLea ih2 hcomm, ?_⟩
    intro E hE hEe
    obtain ⟨F', hF'L, hF'e, hEc⟩ := two_factor_card hHL hLH hN hEe (by rwa [sup_comm])
    rw [hEc, hcard, mul_comm (Nat.card ↥(F L))]
    exact Nat.mul_le_mul (ih3 _ inf_le_right (isElemAbelian_of_le hEe inf_le_left))
      (hFLmax F' hF'L hF'e)

theorem sup_inf_of_comm {A Y Z : Subgroup G} (hAZ : A ≤ Z) (hc : ∀ x ∈ A, ∀ y ∈ Y, x * y = y * x) :
    (A ⊔ Y) ⊓ Z = A ⊔ (Y ⊓ Z) := by
  apply le_antisymm
  · rintro x ⟨hx, hxZ⟩
    obtain ⟨a, ha, y, hy, rfl⟩ := Lemma137.mem_sup_of_comm hc x hx
    have hyZ : y ∈ Z := by
      have : y = a⁻¹ * (a * y) := by group
      rw [this]
      exact Z.mul_mem (Z.inv_mem (hAZ ha)) hxZ
    exact (A ⊔ (Y ⊓ Z)).mul_mem (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right ⟨hy, hyZ⟩)
  · exact le_inf (sup_le_sup_left inf_le_left _) (sup_le hAZ (inf_le_right))

theorem decomp_join {B : Subgroup G} (hB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (𝓛 : Finset (Subgroup G)) (C : Subgroup G → Subgroup G) (hCB : ∀ L ∈ 𝓛, C L ≤ B)
    (hdec : ∀ L ∈ 𝓛, B = (B ⊓ L) ⊔ C L)
    (hcross : ∀ L ∈ 𝓛, ∀ L' ∈ 𝓛, L ≠ L' → B ⊓ L' ≤ C L) :
    B = (⨆ L ∈ 𝓛, B ⊓ L) ⊔ (B ⊓ ⨅ L ∈ 𝓛, C L) := by
  classical
  suffices key : ∀ S : Finset (Subgroup G), S ⊆ 𝓛 →
      B = (⨆ L ∈ S, B ⊓ L) ⊔ (B ⊓ ⨅ L ∈ S, C L) from key 𝓛 subset_rfl
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert L S hLS ih =>
    intro hsub
    have hL𝓛 : L ∈ 𝓛 := hsub (Finset.mem_insert_self L S)
    have hS𝓛 : S ⊆ 𝓛 := (Finset.subset_insert L S).trans hsub
    have h1 := ih hS𝓛
    rw [Finset.iSup_insert, Finset.iInf_insert]
    set X : Subgroup G := ⨆ L' ∈ S, B ⊓ L' with hX
    set Y : Subgroup G := B ⊓ ⨅ L' ∈ S, C L' with hY
    have hAY : B ⊓ L ≤ Y := le_inf inf_le_left (le_iInf₂ fun L' hL' =>
      hcross L' (hS𝓛 hL') L hL𝓛 (fun h => hLS (h ▸ hL')))
    have hc : ∀ x ∈ B ⊓ L, ∀ y ∈ C L, x * y = y * x := fun x hx y hy =>
      hB x hx.1 y (hCB L hL𝓛 hy)
    have hYeq : Y = (B ⊓ L) ⊔ (C L ⊓ Y) := by
      have h2 : Y = ((B ⊓ L) ⊔ C L) ⊓ Y := by rw [← hdec L hL𝓛]; exact (inf_of_le_right inf_le_left).symm
      rw [sup_inf_of_comm hAY hc] at h2
      exact h2
    have hY' : C L ⊓ Y = B ⊓ (C L ⊓ ⨅ L' ∈ S, C L') := by
      rw [hY, inf_left_comm]
    conv_lhs => rw [h1, hYeq, hY']
    rw [← sup_assoc, sup_comm X (B ⊓ L)]

end Joins

section StepA

variable {G : Type} [Group G] [Finite G]

theorem iof_le_istar (p : ℕ) (M D : Subgroup G) : Iof p M D ≤ Istar p M D :=
  le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g (Iof p M D)) 1 M.one_mem
    (by rw [gLBConj_one])

theorem conj_mem_istar (p : ℕ) {M D : Subgroup G} {g : G} (hg : g ∈ M) {x : G}
    (hx : x ∈ Istar p M D) : g * x * g⁻¹ ∈ Istar p M D := by
  have h1 : x ∈ GLBConj g (Istar p M D) := by rw [istar_conj_eq p hg]; exact hx
  exact mem_gLBConj.1 h1

theorem barX_istar_normal (p : ℕ) (M D : Subgroup G) : (barX p M (Istar p M D)).Normal := by
  refine ⟨fun y hy x => ?_⟩
  obtain ⟨i, hi, rfl⟩ := (mem_barX_iff p y).1 hy
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (GLAPPrimeCore p ↥M) x
  refine (mem_barX_iff p _).2 ⟨m * i * m⁻¹, ?_, by simp [map_mul, map_inv]⟩
  exact conj_mem_istar p m.2 hi

theorem centB_core (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h97 : Prop95Parts.Lemma97) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) {c : G} (hcM : c ∈ M)
    (hc : ∀ x ∈ Istar p M D, c * x * c⁻¹ * x⁻¹ ∈ GLAPPrimeCoreOf p M)
    {g : G} (hg : g ∈ gammaStar p D) : c * g * c⁻¹ * g⁻¹ ∈ pCoreOf 2 M := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hPH := prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD
  obtain ⟨-, hcent, -⟩ := hP95 G m p hS M D hPH
  have hΓM : gammaStar p D ≤ M :=
    (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h.toSec11 h.hD).2
  have hgM : g ∈ M := hΓM hg
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hπ
  haveI hSn := barX_istar_normal p M D
  have hW2 : IsPGroup 2 ↥(barX p M (gammaStar p D)) := isPGroup_barX (isPGroup_gammaStar p D)
  have hWF : barX p M (gammaStar p D) ≤
      Subgroup.centralizer (CFSG.Open.pCore p (↥M ⧸ GLAPPrimeCore p ↥M) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    (barX_mono p (gammaStar_le_gammaD p D)).trans hcent
  have hWK : ∀ K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M), IsComponentOf K ⊤ →
      ¬ K ≤ barX p M (Istar p M D) →
        barX p M (gammaStar p D) ≤ Subgroup.centralizer (K : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    intro K hK hKS
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq M hK
    by_contra hnc
    apply hKS
    have hLI : L ≤ Iof p M D := le_iSup₂_of_le L ⟨hL, hnc⟩ le_rfl
    exact barX_mono p (hLI.trans (iof_le_istar p M D))
  have hcY : π ⟨c, hcM⟩ ∈ Subgroup.centralizer
      ((barX p M (Istar p M D) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    obtain ⟨x, hx, rfl⟩ := (mem_barX_iff p s).1 hs
    have h1 := hc x hx
    obtain ⟨hxM', hxQ⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff
      p M _).1 h1
    have h2 : π (⟨c, hcM⟩ * x * ⟨c, hcM⟩⁻¹ * x⁻¹) = 1 := by
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      convert hxQ using 1
    simp only [map_mul, map_inv] at h2
    calc π x * π ⟨c, hcM⟩ = (π ⟨c, hcM⟩ * π x * (π ⟨c, hcM⟩)⁻¹ * (π x)⁻¹)⁻¹ *
        (π ⟨c, hcM⟩ * π x) := by group
      _ = π ⟨c, hcM⟩ * π x := by rw [h2, inv_one, one_mul]
  have hstep1 := commute_of_mem_centralizer hp hp2 (glaPPrimeCore_quotient_eq_bot hp)
    (barX p M (Istar p M D)) (barX p M (gammaStar p D)) hW2 hWF hWK hcY
    (Lemma137.mk_mem_barX' hΓM hg)
  have hcgQ : (⟨c, hcM⟩ : ↥M) * ⟨g, hgM⟩ * (⟨c, hcM⟩ : ↥M)⁻¹ * (⟨g, hgM⟩ : ↥M)⁻¹ ∈
      GLAPPrimeCore p ↥M := by
    rw [← QuotientGroup.eq_one_iff]
    change π (⟨c, hcM⟩ * ⟨g, hgM⟩ * (⟨c, hcM⟩ : ↥M)⁻¹ * (⟨g, hgM⟩ : ↥M)⁻¹) = 1
    simp only [map_mul, map_inv]
    have e : π ⟨c, hcM⟩ * π ⟨g, hgM⟩ = π ⟨g, hgM⟩ * π ⟨c, hcM⟩ := hstep1
    rw [e]
    group
  have hg2 : ∃ a : ℕ, (⟨g, hgM⟩ : ↥M) ^ (2 ^ a) = 1 := by
    obtain ⟨a, ha⟩ := isPGroup_gammaStar p D ⟨g, hg⟩
    refine ⟨a, Subtype.ext ?_⟩
    have := congrArg Subtype.val ha
    simpa using this
  have hgQ : ∀ q ∈ GLAPPrimeCore p ↥M, (⟨g, hgM⟩ : ↥M) * q * (⟨g, hgM⟩ : ↥M)⁻¹ * q⁻¹ ∈
      CFSG.pCore 2 ↥M := by
    intro q hq
    have hqG : (q : G) ∈ GLAPPrimeCoreOf p M :=
      (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff p M _).2
        ⟨q.2, hq⟩
    have h1 : g * (q : G) * g⁻¹ * (q : G)⁻¹ ∈ pCoreOf 2 M :=
      h97 G m p hS M D hPH (Subgroup.commutator_mem_commutator (gammaStar_le_gammaD p D hg) hqG)
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 h1
    have : y = (⟨g, hgM⟩ : ↥M) * q * (⟨g, hgM⟩ : ↥M)⁻¹ * q⁻¹ := Subtype.ext hyeq
    rw [← this]
    exact hy
  have h2 := commutator_mem_pCore_two (GLAPPrimeCore p ↥M) hg2 hgQ hcgQ
  exact Subgroup.mem_map_of_mem M.subtype h2

end StepA

section Components

variable {G : Type} [Group G] [Finite G]

noncomputable def compSet (p : ℕ) (M D : Subgroup G) : Finset (Subgroup G) :=
  (Set.toFinite {L : Subgroup G | GLAPComponent p (Istar p M D) L}).toFinset

theorem mem_compSet {p : ℕ} {M D L : Subgroup G} :
    L ∈ compSet p M D ↔ GLAPComponent p (Istar p M D) L := by
  unfold compSet
  rw [Set.Finite.mem_toFinset]
  rfl

theorem istar_eq_iSup_compSet {p : ℕ} (hp : p.Prime) (M D : Subgroup G) :
    Istar p M D = ⨆ L ∈ compSet p M D, L := by
  refine le_antisymm ?_ (iSup₂_le fun L hL => (mem_compSet.1 hL).1)
  refine iSup₂_le fun g hg => ?_
  have h1 : Iof p M D ≤ GLBConj g⁻¹ (⨆ L ∈ compSet p M D, L) := by
    refine iSup₂_le fun L0 hL0 => ?_
    have hc : GLAPComponent p M (GLBConj g L0) := glaPComponent_conj_mem hL0.1 hg
    have hle : GLBConj g L0 ≤ Istar p M D :=
      le_iSup₂_of_le (f := fun g (_ : g ∈ M) => GLBConj g (Iof p M D)) g hg
        (gLBConj_mono g (le_iSup₂_of_le (f := fun L (_ : GLAPComponent p M L ∧ ¬ barX p M (gammaStar p D) ≤
          Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
            Set (↥M ⧸ GLAPPrimeCore p ↥M))) => L) L0 hL0 le_rfl))
    have hmem : GLBConj g L0 ∈ compSet p M D :=
      mem_compSet.2 (glaPComponent_of_le hp hc hle (istar_le_M p M D))
    have h2 : GLBConj g L0 ≤ ⨆ L ∈ compSet p M D, L := le_iSup₂_of_le _ hmem le_rfl
    have h3 := gLBConj_mono g⁻¹ h2
    rwa [gLBConj_inv_gLBConj] at h3
  have h4 := gLBConj_mono g h1
  rwa [gLBConj_gLBConj_inv] at h4

theorem istar_comp_facts {m p : ℕ} {M D : Subgroup G} (hP95 : Prop95) (hS : GLStanding G m p)
    (hPH : Prop95Hyp p M D) {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L) :
    GLAPComponent p M L ∧ IsGLBlock M L := by
  obtain ⟨g, hg, L0, hL0, rfl⟩ := Lemma137b.istar_component' hS.prime hL
  have hnc : ¬ barX p M (gammaD D) ≤ Subgroup.centralizer
      ((barX p M L0 : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) :=
    fun hle => hL0.2 ((barX_mono p (gammaStar_le_gammaD p D)).trans hle)
  obtain ⟨hcomp, hbl, -⟩ := block_of_conj_iv hS hP95 hPH hg hL0.1 hnc
  exact ⟨hcomp, hbl⟩

theorem barX_le_centralizer_of_ne {p : ℕ} {M L L' : Subgroup G} (hL : GLAPComponent p M L)
    (hL' : GLAPComponent p M L') (hne : L ≠ L') :
    barX p M L' ≤ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hne' : barX p M L ≠ barX p M L' := fun h => hne (glaPComponent_unique hL hL' h)
  rcases CFSG.LocalCores.distinct_components_commute ((CFSG.isComponent_iff_open _).2 hL.2.2.1)
      ((CFSG.isComponent_iff_open _).2 hL'.2.2.1) with h | h
  · exact absurd h hne'
  · rw [Subgroup.commutator_comm] at h
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h

theorem mem_normalizer_of_centralizes {p : ℕ} (hp : p.Prime) {M L : Subgroup G}
    (hL : GLAPComponent p M L) {x : G} (hxM : x ∈ M)
    (hx : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ ∈ Subgroup.centralizer
      ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  refine mem_normalizer_of_barX_normalizes hp le_rfl hL hxM (Subgroup.le_normalizer hxM) ?_
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hc := Subgroup.mem_centralizer_iff.1 hx
  constructor
  · intro hy
    rw [← hc y hy]
    simpa [mul_assoc] using hy
  · intro hy
    set x' := QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩
    have hy' : x' * y * x'⁻¹ ∈ barX p M L := hy
    have h1 : x'⁻¹ * (x' * y * x'⁻¹) = (x' * y * x'⁻¹) * x'⁻¹ := by
      have h2 := hc _ hy'
      calc x'⁻¹ * (x' * y * x'⁻¹) = x'⁻¹ * ((x' * y * x'⁻¹) * x') * x'⁻¹ := by group
        _ = x'⁻¹ * (x' * (x' * y * x'⁻¹)) * x'⁻¹ := by rw [h2]
        _ = (x' * y * x'⁻¹) * x'⁻¹ := by group
    have h3 : y = x' * y * x'⁻¹ := by
      calc y = x'⁻¹ * (x' * y * x'⁻¹) * x' := by group
        _ = (x' * y * x'⁻¹) * x'⁻¹ * x' := by rw [h1]
        _ = x' * y * x'⁻¹ := by group
    rw [h3]
    exact hy'

theorem le_normalizer_of_comp {p : ℕ} (hp : p.Prime) {M L L' : Subgroup G}
    (hL : GLAPComponent p M L) (hL' : GLAPComponent p M L') :
    L' ≤ Subgroup.normalizer (L : Set G) := by
  by_cases hne : L = L'
  · subst hne
    exact Subgroup.le_normalizer
  · intro x hx
    exact mem_normalizer_of_centralizes hp hL (hL'.1 hx)
      (barX_le_centralizer_of_ne hL hL' hne (Lemma137.mk_mem_barX' hL'.1 hx))

theorem iSup_inf_le_core {p : ℕ} {M L : Subgroup G} (hL : GLAPComponent p M L)
    (hZ : Subgroup.center ↥(barX p M L) = ⊥) (S : Finset (Subgroup G))
    (hS : ∀ L' ∈ S, GLAPComponent p M L') (hLS : L ∉ S) :
    (⨆ L' ∈ S, L') ⊓ L ≤ GLAPPrimeCoreOf p M := by
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥M) with hπ
  set Z : Subgroup G := ((Subgroup.centralizer ((barX p M L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
    Set (↥M ⧸ GLAPPrimeCore p ↥M))).comap π).map M.subtype with hZdef
  have hSZ : (⨆ L' ∈ S, L') ≤ Z := by
    refine iSup₂_le fun L' hL' => ?_
    intro x hx
    have hxM : x ∈ M := (hS L' hL').1 hx
    refine ⟨⟨x, hxM⟩, ?_, rfl⟩
    have hne : L ≠ L' := fun h => hLS (h ▸ hL')
    exact barX_le_centralizer_of_ne hL (hS L' hL') hne (Lemma137.mk_mem_barX' (hS L' hL').1 hx)
  intro x hx
  obtain ⟨hxS, hxL⟩ := Subgroup.mem_inf.1 hx
  obtain ⟨y, hy, rfl⟩ := hSZ hxS
  have hyL : π y ∈ barX p M L := ⟨y, Subgroup.mem_subgroupOf.2 hxL, rfl⟩
  have hc : (⟨π y, hyL⟩ : ↥(barX p M L)) ∈ Subgroup.center ↥(barX p M L) := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hy w.1 w.2)
  rw [hZ, Subgroup.mem_bot] at hc
  have h1 : π y = 1 := congrArg Subtype.val hc
  exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff p M _).2
    ⟨y.2, (QuotientGroup.eq_one_iff _).1 h1⟩

theorem not_dvd_card_of_isPGroup_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Subgroup G}
    (hX : IsPGroup 2 ↥X) : ¬ p ∣ Nat.card ↥X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hX
  rw [hk]
  intro hd
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))

theorem not_dvd_card_iSup_inf {m p : ℕ} {M D : Subgroup G} (hP95 : Prop95) (hS : GLStanding G m p)
    (hPH : Prop95Hyp p M D) {L : Subgroup G} (hL : L ∈ compSet p M D) (S : Finset (Subgroup G))
    (hSsub : S ⊆ compSet p M D) (hLS : L ∉ S) : ¬ p ∣ Nat.card ↥((⨆ L' ∈ S, L') ⊓ L) := by
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  obtain ⟨hLcomp, hbl⟩ := istar_comp_facts hP95 hS hPH (mem_compSet.1 hL)
  have hZ : Subgroup.center ↥(barX p M L) = ⊥ :=
    Prop139.center_bot_of_mulEquiv (quotEquivBarX hp hLcomp.1 hLcomp.2.1).symm
      (center_quotient_eq_bot_of_block hp hp2 hLcomp hbl)
  have hle : (⨆ L' ∈ S, L') ⊓ L ≤ L ⊓ GLAPPrimeCoreOf p M :=
    le_inf inf_le_right (iSup_inf_le_core hLcomp hZ S
      (fun L' hL' => (istar_comp_facts hP95 hS hPH (mem_compSet.1 (hSsub hL'))).1) hLS)
  exact not_dvd_card_of_isPGroup_two hp hp2
    ((isPGroup_two_inf_glaPPrimeCoreOf hp hp2 hLcomp hbl).to_le hle)
end Components

section Numerics

theorem pow_dvd_card_of_not_dvd_index {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (H : Subgroup X) (h : ¬ p ∣ H.index) : p ^ (Nat.card X).factorization p ∣ Nat.card ↥H := by
  have h1 := H.index_mul_card
  have h0a : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h0b : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have h2 : (Nat.card X).factorization p = H.index.factorization p + (Nat.card ↥H).factorization p := by
    rw [← h1, Nat.factorization_mul h0a h0b, Finsupp.add_apply]
  rw [h2, Nat.factorization_eq_zero_of_not_dvd h, zero_add]
  exact Nat.ordProj_dvd _ _

theorem not_dvd_index_of_pow_dvd_card {p : ℕ} [hp : Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (H : Subgroup X) (h : p ^ (Nat.card X).factorization p ∣ Nat.card ↥H) : ¬ p ∣ H.index := by
  intro hd
  have h1 := H.index_mul_card
  have h0a : H.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h0b : Nat.card ↥H ≠ 0 := Nat.card_pos.ne'
  have h2 : (Nat.card X).factorization p = H.index.factorization p + (Nat.card ↥H).factorization p := by
    rw [← h1, Nat.factorization_mul h0a h0b, Finsupp.add_apply]
  have h3 : (Nat.card X).factorization p ≤ (Nat.card ↥H).factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp.out h0b).1 h
  have h4 : 1 ≤ H.index.factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp.out h0a).1 hd
  omega

theorem not_dvd_index_alt {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {X : Type*} [Group X] [Finite X]
    (H : Subgroup X) (hX : Nat.card X = Nat.card (alternatingGroup (Fin (k * p + 2))))
    (hH : Nat.card ↥H = (k * p).factorial) : ¬ p ∣ H.index := by
  intro hd
  have h1 := H.index_mul_card
  have h2 : 2 * Nat.card (alternatingGroup (Fin (k * p + 2))) = (k * p + 2).factorial := by
    rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]
  have h3 : 2 * H.index * (k * p).factorial = (k * p + 2) * (k * p + 1) * (k * p).factorial := by
    calc 2 * H.index * (k * p).factorial = 2 * (H.index * Nat.card ↥H) := by rw [hH]; ring
      _ = 2 * Nat.card (alternatingGroup (Fin (k * p + 2))) := by rw [h1, hX]
      _ = (k * p + 2).factorial := h2
      _ = (k * p + 2) * (k * p + 1) * (k * p).factorial := by
        rw [Nat.factorial_succ, Nat.factorial_succ]; ring
  have h4 : 2 * H.index = (k * p + 2) * (k * p + 1) :=
    Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) h3
  have h5 : p ∣ (k * p + 2) * (k * p + 1) := h4 ▸ dvd_mul_of_dvd_right hd 2
  rcases (Nat.Prime.dvd_mul hp).1 h5 with h6 | h6
  · have h7 : p ∣ 2 := (Nat.dvd_add_right (dvd_mul_left p k)).1 h6
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h7)
  · have h7 : p ∣ 1 := (Nat.dvd_add_right (dvd_mul_left p k)).1 h6
    exact hp.one_lt.ne' (Nat.dvd_one.1 h7)

end Numerics

section ConjMax

@[expose] def ConjMaxEA (p : ℕ) (X : Type) [Group X] : Prop :=
  ∀ F₁ F₂ : Subgroup X, IsElemAbelian p F₁ → IsElemAbelian p F₂ →
    (∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥F₁) →
    (∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥F₂) →
      ∃ x : X, GLBConj x F₁ = F₂

variable {X : Type} [Group X] [Finite X]

theorem isPGroup_of_ea {p : ℕ} {E : Subgroup X} (hE : IsElemAbelian p E) : IsPGroup p ↥E :=
  Sec13h.isPGroup_of_isElemAbelian' hE

theorem card_comap_mk (V : Subgroup X) [V.Normal] (F : Subgroup (X ⧸ V)) :
    Nat.card ↥(F.comap (QuotientGroup.mk' V)) = Nat.card ↥F * Nat.card ↥V := by
  have h1 := (F.comap (QuotientGroup.mk' V)).index_mul_card
  have h2 := F.index_mul_card
  have h3 : (F.comap (QuotientGroup.mk' V)).index = F.index :=
    Subgroup.index_comap_of_surjective F (QuotientGroup.mk'_surjective V)
  have h4 : Nat.card X = Nat.card (X ⧸ V) * Nat.card ↥V :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup V
  have h0 : F.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rw [h3] at h1
  apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h0)
  rw [h1, h4, ← h2, mul_assoc]

theorem card_map_mk_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (V : Subgroup X) [V.Normal]
    (hV : ¬ p ∣ Nat.card ↥V) {E : Subgroup X} (hE : IsPGroup p ↥E) :
    Nat.card ↥(E.map (QuotientGroup.mk' V)) = Nat.card ↥E := by
  have hinj : Function.Injective ((QuotientGroup.mk' V).comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 : (x : X) ∈ E ⊓ V := ⟨x.2, hx⟩
    rw [isPGroup_inf_eq_bot_of_not_dvd hp.out hE hV, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hrange : ((QuotientGroup.mk' V).comp E.subtype).range = E.map (QuotientGroup.mk' V) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

theorem map_gLBConj {Y : Type} [Group Y] (f : X →* Y) (x : X) (E : Subgroup X) :
    (GLBConj x E).map f = GLBConj (f x) (E.map f) := by
  unfold GLBConj
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply]

theorem conjMaxEA_of_quotient {p : ℕ} [hp : Fact p.Prime] (V : Subgroup X) [hVn : V.Normal]
    (hV : ¬ p ∣ Nat.card ↥V) (hY : ConjMaxEA p (X ⧸ V)) : ConjMaxEA p X := by
  intro E₁ E₂ hE₁ hE₂ hm₁ hm₂
  set π := QuotientGroup.mk' V with hπ
  have hp₁ := isPGroup_of_ea hE₁
  have hp₂ := isPGroup_of_ea hE₂
  have hc₁ := card_map_mk_of_isPGroup V hV hp₁
  have hc₂ := card_map_mk_of_isPGroup V hV hp₂
  have hlift : ∀ F : Subgroup (X ⧸ V), IsElemAbelian p F →
      ∃ P : Subgroup X, IsElemAbelian p P ∧ Nat.card ↥P = Nat.card ↥F := by
    intro F hF
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_ea hF)
    set Ft := F.comap π with hFt
    obtain ⟨P⟩ : Nonempty (Sylow p ↥Ft) := inferInstance
    set P' : Subgroup X := (P : Subgroup ↥Ft).map Ft.subtype with hP'
    have hP'Ft : P' ≤ Ft := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hFtc : Nat.card ↥Ft = p ^ k * Nat.card ↥V := by rw [hFt, card_comap_mk, hk]
    have hP'c : Nat.card ↥P' = p ^ k := by
      rw [hP', Subgroup.card_map_of_injective Ft.subtype_injective, Sylow.card_eq_multiplicity P,
        hFtc, factorization_pow_mul hp.out k _ hV]
    have hP'p : IsPGroup p ↥P' := IsPGroup.of_card hP'c
    have hP'V : P' ⊓ V = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out hP'p hV
    have hkerP : ∀ z ∈ P', π z = 1 → z = 1 := by
      intro z hz hz1
      have h1 : z ∈ P' ⊓ V := ⟨hz, (QuotientGroup.eq_one_iff _).1 hz1⟩
      rw [hP'V, Subgroup.mem_bot] at h1
      exact h1
    have hmapF : ∀ z ∈ P', π z ∈ F := fun z hz => hP'Ft hz
    refine ⟨P', ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩, ?_⟩
    · have hab : (a : X) * b * (a : X)⁻¹ * (b : X)⁻¹ = 1 := by
        refine hkerP _ (P'.mul_mem (P'.mul_mem (P'.mul_mem a.2 b.2) (P'.inv_mem a.2))
          (P'.inv_mem b.2)) ?_
        simp only [map_mul, map_inv]
        have hc : π a * π b = π b * π a := by
          have := hF.1.is_comm.comm ⟨π a, hmapF _ a.2⟩ ⟨π b, hmapF _ b.2⟩
          exact congrArg Subtype.val this
        rw [hc]
        group
      calc ((a * b : ↥P') : X) = ((a : X) * b * (a : X)⁻¹ * (b : X)⁻¹) * ((b : X) * a) := by
            simp only [Subgroup.coe_mul]; group
        _ = ((b * a : ↥P') : X) := by rw [hab, one_mul]; rfl
    · refine hkerP _ (P'.pow_mem hz p) ?_
      rw [map_pow]
      exact hF.2 _ (hmapF z hz)
    · rw [hP'c, hk]
  have hmax : ∀ E : Subgroup X, IsElemAbelian p E →
      (∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E) →
      ∀ F : Subgroup (X ⧸ V), IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥(E.map π) := by
    intro E hE hm F hF
    obtain ⟨P, hPe, hPc⟩ := hlift F hF
    rw [card_map_mk_of_isPGroup V hV (isPGroup_of_ea hE), ← hPc]
    exact hm P hPe
  obtain ⟨y, hy⟩ := hY (E₁.map π) (E₂.map π) (CFSG.SectionRank.isElemAbelian_map hE₁ π)
    (CFSG.SectionRank.isElemAbelian_map hE₂ π) (hmax E₁ hE₁ hm₁) (hmax E₂ hE₂ hm₂)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V y
  set E₁' : Subgroup X := GLBConj x E₁ with hE₁'
  have hE₁'map : E₁'.map π = E₂.map π := by rw [hE₁', map_gLBConj]; exact hy
  have hE₁'p : IsPGroup p ↥E₁' := isPGroup_of_ea (sec9_isElemAbelian_gLBConj x hE₁)
  have hcard12 : Nat.card ↥E₁ = Nat.card ↥E₂ := le_antisymm (hm₂ E₁ hE₁) (hm₁ E₂ hE₂)
  have hE₁'c : Nat.card ↥E₁' = Nat.card ↥E₂ := by rw [hE₁', sec9_card_gLBConj, hcard12]
  set W : Subgroup X := (E₂.map π).comap π with hW
  have hE₂W : E₂ ≤ W := Subgroup.le_comap_map π E₂
  have hE₁'W : E₁' ≤ W := by
    rw [hW, ← hE₁'map]
    exact Subgroup.le_comap_map π E₁'
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hp₂
  have hWc : Nat.card ↥W = p ^ j * Nat.card ↥V := by rw [hW, card_comap_mk, hc₂, hj]
  have hE₂c : Nat.card ↥E₂ = p ^ (Nat.card ↥W).factorization p := by
    rw [hWc, factorization_pow_mul hp.out j _ hV, hj]
  obtain ⟨z, -, hz⟩ := Sec13h.exists_conj_le_of_sylow W E₂ E₁' hE₂W hE₂c hE₁'W hE₁'p
  refine ⟨x * z, ?_⟩
  rw [← gLBConj_gLBConj]
  refine Subgroup.eq_of_le_of_card_ge hz ?_
  rw [sec9_card_gLBConj, hE₁'c]

theorem ConjMaxEA.of_mulEquiv {p : ℕ} {Y : Type} [Group Y] (e : X ≃* Y) (h : ConjMaxEA p X) :
    ConjMaxEA p Y := by
  intro F₁ F₂ hF₁ hF₂ hm₁ hm₂
  have hcard : ∀ F : Subgroup Y, Nat.card ↥(F.map e.symm.toMonoidHom) = Nat.card ↥F := fun F =>
    Subgroup.card_map_of_injective e.symm.injective
  have hmax : ∀ F' : Subgroup Y,
      (∀ F : Subgroup Y, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥F') →
      ∀ F : Subgroup X, IsElemAbelian p F →
        Nat.card ↥F ≤ Nat.card ↥(F'.map e.symm.toMonoidHom) := by
    intro F' hm F hF
    rw [hcard]
    have h1 := hm (F.map e.toMonoidHom) (CFSG.SectionRank.isElemAbelian_map hF _)
    rwa [Subgroup.card_map_of_injective e.injective] at h1
  obtain ⟨x, hx⟩ := h _ _ (CFSG.SectionRank.isElemAbelian_map hF₁ _)
    (CFSG.SectionRank.isElemAbelian_map hF₂ _) (hmax F₁ hm₁) (hmax F₂ hm₂)
  refine ⟨e x, ?_⟩
  have h2 := congrArg (Subgroup.map e.toMonoidHom) hx
  rw [map_gLBConj, Subgroup.map_map, Subgroup.map_map] at h2
  have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id Y := by ext; simp
  rw [hid, Subgroup.map_id, Subgroup.map_id] at h2
  have hex : e.toMonoidHom (e.symm.toMonoidHom (e x)) = e x := by simp
  simpa [hex] using h2

theorem conjMaxEA_alt {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hn : 5 ≤ n) :
    ConjMaxEA p ↥(alternatingGroup (Fin n)) := by
  intro F₁ F₂ hF₁ hF₂ hm₁ hm₂
  have hK : IsAltType n ↥(⊤ : Subgroup ↥(alternatingGroup (Fin n))) := ⟨Subgroup.topEquiv⟩
  obtain ⟨hle, E₀, -, hE₀, hE₀c⟩ := Lemma118R.Input10_6AltRank_holds n p _ ⊤ hn hp hp2 hK
  have hc₁ : Nat.card ↥F₁ = p ^ (n / p) := le_antisymm (hle F₁ le_top hF₁) (hE₀c ▸ hm₁ E₀ hE₀)
  have hc₂ : Nat.card ↥F₂ = p ^ (n / p) := le_antisymm (hle F₂ le_top hF₂) (hE₀c ▸ hm₂ E₀ hE₀)
  obtain ⟨g, -, hg⟩ := (Lemma118R.Input10_5AltMax_holds n p _ ⊤ hn hp hp2 hK).1 F₁ F₂ le_top le_top
    hF₁ hF₂ hc₁ hc₂
  refine ⟨g⁻¹, ?_⟩
  rw [hg]
  unfold GLBConj
  rw [inv_inv]

end ConjMax

@[expose] def Input10_13Omega : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ), 1 ≤ n → HasFixedPointFreeOrder ε n p →
    ∀ (K : Type) [Group K] [Finite K] (L : Subgroup K), IsOmegaTwo ε (n + 1) K →
      Nonempty (↥L ≃* ↥(StatedSp n (ZMod 2))) → p ^ (Nat.card K).factorization p ∣ Nat.card ↥L

@[expose] def Input10_2Omega : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (ε : Bool) (n : ℕ), 1 ≤ n → HasFixedPointFreeOrder ε n p →
    ∀ (X : Type) [Group X] [Finite X], IsOmegaTwo ε (n + 1) X →
      ∀ E₁ E₂ : Subgroup X, IsElemAbelian p E₁ → IsElemAbelian p E₂ →
        (∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₁) →
        (∀ F : Subgroup X, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E₂) →
          ∃ x : X, E₂ = E₁.map (MulAut.conj x).toMonoidHom

section OneCompConj

variable {G : Type} [Group G] [Finite G]

theorem conjMaxEA_of_input102 (hI : Input10_2Omega) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ε : Bool} {n : ℕ} (hn : 1 ≤ n) (hfp : HasFixedPointFreeOrder ε n p) {X : Type} [Group X]
    [Finite X] (hX : IsOmegaTwo ε (n + 1) X) : ConjMaxEA p X := by
  intro F₁ F₂ hF₁ hF₂ hm₁ hm₂
  obtain ⟨x, hx⟩ := hI p hp hp2 ε n hn hfp X hX F₁ F₂ hF₁ hF₂ hm₁ hm₂
  refine ⟨x⁻¹, ?_⟩
  rw [hx]
  unfold GLBConj
  rw [inv_inv]

theorem conj_of_conjMaxEA {p : ℕ} {L : Subgroup G} (h : ConjMaxEA p ↥L) {E₁ E₂ : Subgroup G}
    (h₁ : Sec13h.IsMaxEA p L E₁) (h₂ : Sec13h.IsMaxEA p L E₂) : ∃ g ∈ L, GLBConj g E₁ = E₂ := by
  obtain ⟨hE₁L, hE₁, hm₁⟩ := h₁
  obtain ⟨hE₂L, hE₂, hm₂⟩ := h₂
  have hcard : ∀ E : Subgroup G, E ≤ L → Nat.card ↥(E.subgroupOf L) = Nat.card ↥E := fun E hE =>
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE).toEquiv
  have hmax : ∀ E : Subgroup G, E ≤ L →
      (∀ F : Subgroup G, F ≤ L → IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥E) →
      ∀ F : Subgroup ↥L, IsElemAbelian p F → Nat.card ↥F ≤ Nat.card ↥(E.subgroupOf L) := by
    intro E hE hm F hF
    rw [hcard E hE]
    have h1 := hm (F.map L.subtype) (Subgroup.map_subtype_le F)
      (CFSG.SectionRank.isElemAbelian_map hF _)
    rwa [Subgroup.card_map_of_injective L.subtype_injective] at h1
  obtain ⟨x, hx⟩ := h (E₁.subgroupOf L) (E₂.subgroupOf L)
    (CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hE₁ L)
    (CFSG.LocalAnalysis.GLTheoremB.isElemAbelian_subgroupOf hE₂ L) (hmax E₁ hE₁L hm₁)
    (hmax E₂ hE₂L hm₂)
  refine ⟨x, x.2, ?_⟩
  have h2 := congrArg (Subgroup.map L.subtype) hx
  rw [map_gLBConj] at h2
  rwa [Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hE₁L,
    inf_of_le_left hE₂L] at h2

theorem conjMaxEA_comp {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hI102 : Input10_2Omega)
    {L : Subgroup G} (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hpi : IsPiGroup p (↥L ⧸ CFSG.pCore 2 ↥L)) : ConjMaxEA p ↥L := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine conjMaxEA_of_quotient (CFSG.pCore 2 ↥L)
    (not_dvd_card_of_isPGroup_two hp hp2 (CFSG.pCore_isPGroup : IsPGroup 2 ↥(CFSG.pCore 2 ↥L))) ?_
  set Y := ↥L ⧸ CFSG.pCore 2 ↥L with hY
  have hZ : Subgroup.center Y = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
    · exact h
    · exfalso
      have hcomm : IsMulCommutative Y := Subgroup.center_eq_top_iff.1 h
      have hperf : Group.IsPerfect Y := ⟨hpi.1.1⟩
      have : Subsingleton Y := Group.IsPerfect.subsingleton_of_isMulCommutative
      exact not_subsingleton Y this
  let eZ : (Y ⧸ Subgroup.center Y) ≃* Y :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨-, -, htype⟩ := hpi
  rcases htype with ⟨k, ⟨f⟩⟩ | ⟨n, ε, hn, hΩ, hfp⟩ | ⟨-, ⟨f⟩⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exfalso
      have h1 : Nat.card (alternatingGroup (Fin (0 * p + 2))) = 1 := by
        have h2 := two_mul_nat_card_alternatingGroup (α := Fin (0 * p + 2))
        rw [Nat.card_perm, Nat.card_fin] at h2
        simp only [zero_mul, zero_add, Nat.factorial_two] at h2
        omega
      have h3 : Nat.card Y = 1 := by
        rw [← Nat.card_congr eZ.toEquiv, Nat.card_congr f.toEquiv, h1]
      haveI : Nontrivial Y := hsimple.toNontrivial
      have h4 := Finite.one_lt_card (α := Y)
      omega
    · exact ConjMaxEA.of_mulEquiv (f.symm.trans eZ) (conjMaxEA_alt hp hp2 (by nlinarith))
  · exact ConjMaxEA.of_mulEquiv eZ (conjMaxEA_of_input102 hI102 hp hp2 hn hfp hΩ)
  · exact ConjMaxEA.of_mulEquiv (f.symm.trans eZ) (conjMaxEA_alt hp hp2 (by norm_num))

end OneCompConj

section OneComp

variable {G : Type} [Group G] [Finite G]

theorem subgroupOf_cm_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L Γ : Subgroup G}
    (hO : ∀ a ∈ M, ∀ o ∈ pCoreOf 2 M, a * o * a⁻¹ ∈ pCoreOf 2 M)
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) (hΓM : Γ ≤ M)
    (hΓL : Γ ≤ Subgroup.normalizer (L : Set G)) :
    (L ⊓ Sec13h.cmSubgroup M Γ (pCoreOf 2 M) hO).subgroupOf L =
      ((barX p M L ⊓ Subgroup.centralizer ((barX p M Γ : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M))).subgroupOf (barX p M L)).comap (barMap p hL.1) := by
  have hLM : L ≤ M := hL.1
  have hsn : IsSubnormal L M := hL.2.1
  have hcoreL : L ⊓ GLAPPrimeCoreOf p M ≤ pCoreOf 2 M := by
    rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hsn]
    have h1 : GLAPPrimeCoreOf p L = pCoreOf 2 L := by
      unfold GLAPPrimeCoreOf pCoreOf
      rw [glaPPrimeCore_eq_pCore_two_of_block hp hp2 hL hbl]
    rw [h1]
    exact Lemma137b.pCoreTwo_le_of_isSubnormal hsn
  have hOQ : pCoreOf 2 M ≤ GLAPPrimeCoreOf p M := p131_pCore_le_glaPPrime hp hp2 M
  ext x
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf]
  constructor
  · rintro ⟨-, hxM, hxc⟩
    refine ⟨(barMap p hLM x).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨g, hg, rfl⟩ := (mem_barX_iff p t).1 ht
    have h1 : (x : G) * (g : G) * (x : G)⁻¹ * (g : G)⁻¹ ∈ GLAPPrimeCoreOf p M := hOQ (hxc g hg)
    obtain ⟨hm, h2⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff
      p M _).1 h1
    have h3 : QuotientGroup.mk' (GLAPPrimeCore p ↥M)
        ((⟨x, hLM x.2⟩ : ↥M) * g * (⟨x, hLM x.2⟩ : ↥M)⁻¹ * g⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).2 h2
    simp only [map_mul, map_inv] at h3
    change QuotientGroup.mk' (GLAPPrimeCore p ↥M) g * QuotientGroup.mk' (GLAPPrimeCore p ↥M)
      ⟨x, hLM x.2⟩ = QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hLM x.2⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥M) g
    set a := QuotientGroup.mk' (GLAPPrimeCore p ↥M) (⟨x, hLM x.2⟩ : ↥M)
    set b := QuotientGroup.mk' (GLAPPrimeCore p ↥M) g
    calc b * a = (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b) := by group
      _ = a * b := by rw [h3, inv_one, one_mul]
  · rintro ⟨-, hxc⟩
    refine ⟨x.2, hLM x.2, fun g hg => ?_⟩
    have hgM : g ∈ M := hΓM hg
    have hc := Subgroup.mem_centralizer_iff.1 hxc _ (Lemma137.mk_mem_barX' hΓM hg)
    have hcQ : (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈ GLAPPrimeCoreOf p M := by
      refine (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff
        p M _).2 ⟨M.mul_mem (M.mul_mem (M.mul_mem (hLM x.2) hgM) (M.inv_mem (hLM x.2)))
          (M.inv_mem hgM), ?_⟩
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' (GLAPPrimeCore p ↥M)
        ((⟨x, hLM x.2⟩ : ↥M) * ⟨g, hgM⟩ * (⟨x, hLM x.2⟩ : ↥M)⁻¹ * (⟨g, hgM⟩ : ↥M)⁻¹) = 1
      simp only [map_mul, map_inv]
      have hc' : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hLM x.2⟩ =
          QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hLM x.2⟩ *
            QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ := hc
      rw [← hc']
      group
    have hcL : (x : G) * g * (x : G)⁻¹ * g⁻¹ ∈ L := by
      have h1 : g * (x : G)⁻¹ * g⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hΓL hg) _).1 (L.inv_mem x.2)
      have : (x : G) * g * (x : G)⁻¹ * g⁻¹ = (x : G) * (g * (x : G)⁻¹ * g⁻¹) := by group
      rw [this]
      exact L.mul_mem x.2 h1
    exact hcoreL ⟨hcL, hcQ⟩

theorem not_dvd_index_comp (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h134 : Prop134_of_cexStatement) (hOmT : Lemma137b.Input9_6OmegaTransv)
    (hI1013 : Input10_13Omega) {m p : ℕ} {B M E A D T : Subgroup G}
    (h : Sec13 G m p B M E A D T) (hO : ∀ a ∈ M, ∀ o ∈ pCoreOf 2 M, a * o * a⁻¹ ∈ pCoreOf 2 M)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L) :
    ¬ p ∣ ((L ⊓ Sec13h.cmSubgroup M (gammaStar p D) (pCoreOf 2 M) hO).subgroupOf L).index := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hPH := prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD
  obtain ⟨-, -, hcomp95⟩ := hP95 G m p hS M D hPH
  have hΓM : gammaStar p D ≤ M :=
    (prop131_of_inputs h111 h1117 (prop121_cor_of h121) h127 h.toSec11 h.hD).2
  obtain ⟨hLcomp, hbl⟩ := istar_comp_facts hP95 hS hPH hL
  have hLM : L ≤ M := hLcomp.1
  have hsn : IsSubnormal L M := hLcomp.2.1
  obtain ⟨hWN, -⟩ := hcomp95 L hLcomp
  have hTW : barX p M (gammaStar p D) ≤ barX p M (gammaD D) := barX_mono p (gammaStar_le_gammaD p D)
  have hΓL : gammaStar p D ≤ Subgroup.normalizer (L : Set G) := fun g hg =>
    mem_normalizer_of_barX_normalizes hp le_rfl hLcomp (hΓM hg) (Subgroup.le_normalizer (hΓM hg))
      (hWN (hTW (Lemma137.mk_mem_barX' hΓM hg)))
  rw [subgroupOf_cm_eq hp hp2 hO hLcomp hbl hΓM hΓL,
    Subgroup.index_comap_of_surjective _ (barMap_surjective hLM)]
  set Ab : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) := barX p M L with hAb
  set Tb : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) := barX p M (gammaStar p D) with hTb
  by_cases hcen : Tb ≤ Subgroup.centralizer (Ab : Set (↥M ⧸ GLAPPrimeCore p ↥M))
  · have htop : (Ab ⊓ Subgroup.centralizer (Tb : Set (↥M ⧸ GLAPPrimeCore p ↥M))).subgroupOf Ab = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_subgroupOf]
      refine ⟨x.2, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
      exact (Subgroup.mem_centralizer_iff.1 (hcen ht) x x.2).symm
    rw [htop, Subgroup.index_top]
    exact hp.not_dvd_one
  ·
    have hLIof : L ≤ Iof p M D := le_iSup₂_of_le L ⟨hLcomp, hcen⟩ le_rfl
    have hLI : GLAPComponent p (Iof p M D) L := glaPComponent_of_le hp hLcomp hLIof (Iof_le_M p M D)
    have hαβ : Prop95Alpha p M D L ∨ Prop95Beta p M D L := by
      by_contra hn
      exact h134 (⟨h, hLI, hn⟩ : Cex134 G m p B M E A D T L)
    have hZ : Subgroup.center ↥Ab = ⊥ :=
      Prop139.center_bot_of_mulEquiv (quotEquivBarX hp hLM hsn).symm
        (center_quotient_eq_bot_of_block hp hp2 hLcomp hbl)
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    rcases hαβ with ⟨k, hk, -, e, τ, hτ, hcard, hAct, -⟩ | ⟨n, hn, hβ'⟩
    · obtain ⟨-, ⟨φ⟩⟩ := Lemma137b.caseII_abstract Ab (barX p M (gammaD D)) Tb hTW hWN e
        (MulAut.conjNormal τ) hAct hcard
        (fun a => Lemma137b.conj_ne_conjNormal (by nlinarith) hτ a) hZ hcen
      obtain ⟨ψ⟩ := Lemma137b.alt_centralizer_equiv (r := k * p) hτ
      refine not_dvd_index_alt hp hp2 _ (Nat.card_congr e.toEquiv) ?_
      rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe inf_le_left).trans (φ.trans ψ)).toEquiv,
        Nat.card_perm, Nat.card_fin]
    · rcases hβ' with ⟨hfp, hbw⟩ | ⟨hfp, hbw⟩
      · obtain ⟨-, e, hcard, ⟨t, ht, hQt, hTv, hAct⟩, -⟩ := hbw
        obtain ⟨hout, ⟨hsp⟩⟩ := hOmT.1 n hn t ht hQt hTv
        obtain ⟨-, ⟨φ⟩⟩ := Lemma137b.caseII_abstract Ab (barX p M (gammaD D)) Tb hTW hWN e _
          hAct hcard hout hZ hcen
        refine not_dvd_index_of_pow_dvd_card _ ?_
        exact hI1013 p hp hp2 true n hn hfp ↥Ab _ ⟨e⟩
          ⟨(Subgroup.subgroupOfEquivOfLe inf_le_left).trans (φ.trans hsp)⟩
      · obtain ⟨-, e, hcard, ⟨t, ht, hQt, hTv, hAct⟩, -⟩ := hbw
        obtain ⟨hout, ⟨hsp⟩⟩ := hOmT.2 n hn t ht hQt hTv
        obtain ⟨-, ⟨φ⟩⟩ := Lemma137b.caseII_abstract Ab (barX p M (gammaD D)) Tb hTW hWN e _
          hAct hcard hout hZ hcen
        refine not_dvd_index_of_pow_dvd_card _ ?_
        exact hI1013 p hp hp2 false n hn hfp ↥Ab _ ⟨e⟩
          ⟨(Subgroup.subgroupOfEquivOfLe inf_le_left).trans (φ.trans hsp)⟩
end OneComp

section B133

variable {G : Type} [Group G] [Finite G]

open CFSG.HardMathSupport.Solomon.LocalBalance (barAut)

theorem mem_centBar_iff' {p : ℕ} {X L : Subgroup G} {b : G} :
    b ∈ centBar p X L ↔ b ∈ X ∧ b ∈ Subgroup.normalizer (L : Set G) ∧
      ∀ x ∈ L, x⁻¹ * (b * x * b⁻¹) ∈ GLAPPrimeCoreOf p L := by
  constructor
  · rintro ⟨hb, hbX⟩
    obtain ⟨hbN, h1⟩ := mem_centK_iff.1 hb
    refine ⟨hbX, hbN, fun x hx => ?_⟩
    have h2 := CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk p L ⟨b, hbN⟩ ⟨x, hx⟩
    rw [h1, MulAut.one_apply, QuotientGroup.eq] at h2
    have hmem : x⁻¹ * (b * x * b⁻¹) ∈ L := L.mul_mem (L.inv_mem hx) ((Subgroup.mem_normalizer_iff.1 hbN x).1 hx)
    have e : (⟨x⁻¹ * (b * x * b⁻¹), hmem⟩ : ↥L) =
        (⟨x, hx⟩ : ↥L)⁻¹ * L.normalizerMonoidHom ⟨b, hbN⟩ ⟨x, hx⟩ := rfl
    exact (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff p L _).2
      ⟨hmem, e ▸ h2⟩
  · rintro ⟨hbX, hbN, hx⟩
    refine ⟨mem_centK_iff.2 ⟨hbN, ?_⟩, hbX⟩
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply, eq_comm,
        QuotientGroup.eq]
      obtain ⟨hm, h⟩ := (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff
        p L _).1 (hx x x.2)
      exact h

theorem commutator_mem_of_ne {p : ℕ} (hp : p.Prime) {M L L' : Subgroup G} (hL : GLAPComponent p M L)
    (hL' : GLAPComponent p M L') (hne : L ≠ L') {b : G} (hb : b ∈ L') {x : G} (hx : x ∈ L) :
    b * x * b⁻¹ * x⁻¹ ∈ L ⊓ GLAPPrimeCoreOf p M := by
  have hbM : b ∈ M := hL'.1 hb
  have hxM : x ∈ M := hL.1 hx
  have hbN : b ∈ Subgroup.normalizer (L : Set G) := le_normalizer_of_comp hp hL hL' hb
  refine ⟨?_, ?_⟩
  · have h1 : b * x * b⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hbN x).1 hx
    exact L.mul_mem h1 (L.inv_mem hx)
  · have hc := Subgroup.mem_centralizer_iff.1 (barX_le_centralizer_of_ne hL hL' hne
      (Lemma137.mk_mem_barX' hL'.1 hb)) _ (Lemma137.mk_mem_barX' hL.1 hx)
    refine (CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns.mem_gLAPPrimeCoreOf_iff p M _).2
      ⟨M.mul_mem (M.mul_mem (M.mul_mem hbM hxM) (M.inv_mem hbM)) (M.inv_mem hxM), ?_⟩
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (GLAPPrimeCore p ↥M)
      ((⟨b, hbM⟩ : ↥M) * ⟨x, hxM⟩ * (⟨b, hbM⟩ : ↥M)⁻¹ * (⟨x, hxM⟩ : ↥M)⁻¹) = 1
    simp only [map_mul, map_inv]
    have hc' : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ *
        QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hbM⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hbM⟩ *
          QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ := hc
    rw [← hc']
    group

theorem core_le_pCore_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {M L : Subgroup G}
    (hL : GLAPComponent p M L) (hbl : IsGLBlock M L) : GLAPPrimeCoreOf p L ≤ pCoreOf 2 M := by
  have h1 : GLAPPrimeCoreOf p L = pCoreOf 2 L := by
    unfold GLAPPrimeCoreOf pCoreOf
    rw [glaPPrimeCore_eq_pCore_two_of_block hp hp2 hL hbl]
  rw [h1]
  exact Lemma137b.pCoreTwo_le_of_isSubnormal hL.2.1

@[expose] def commO (M O : Subgroup G) (hO : ∀ a ∈ M, ∀ o ∈ O, a * o * a⁻¹ ∈ O) (b : G) :
    Subgroup G where
  carrier := {g | g ∈ M ∧ b * g * b⁻¹ * g⁻¹ ∈ O}
  one_mem' := ⟨M.one_mem, by simp [O.one_mem]⟩
  mul_mem' := by
    rintro g h ⟨hg, hgO⟩ ⟨hh, hhO⟩
    refine ⟨M.mul_mem hg hh, ?_⟩
    have e : b * (g * h) * b⁻¹ * (g * h)⁻¹ = (b * g * b⁻¹ * g⁻¹) * (g * (b * h * b⁻¹ * h⁻¹) * g⁻¹) := by
      group
    rw [e]
    exact O.mul_mem hgO (hO g hg _ hhO)
  inv_mem' := by
    rintro g ⟨hg, hgO⟩
    refine ⟨M.inv_mem hg, ?_⟩
    have e : b * g⁻¹ * b⁻¹ * g⁻¹⁻¹ = g⁻¹ * (b * g * b⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
    rw [e]
    exact hO g⁻¹ (M.inv_mem hg) _ (O.inv_mem hgO)

theorem b_decomp_of {m p : ℕ} {B M E A D T : Subgroup G} (hP95 : Prop95)
    (hPH : Prop95Hyp p M D) (h133 : Lemma133Statement) (h : Sec13 G m p B M E A D T)
    (C : Subgroup G → Subgroup G) (hCB : ∀ L ∈ compSet p M D, C L ≤ B)
    (hCbar : ∀ L ∈ compSet p M D, centBar p B L ≤ C L)
    (hcross : ∀ L ∈ compSet p M D, ∀ L' ∈ compSet p M D, L ≠ L' → B ⊓ L' ≤ C L) :
    B = (⨆ L ∈ compSet p M D, B ⊓ L) ⊔ (B ⊓ ⨅ L ∈ compSet p M D, C L) := by
  have hBel : IsElemAbelian p B := h.bOne.1.1
  refine decomp_join (fun x hx y hy => congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
    (compSet p M D) C hCB (fun L hL => ?_) hcross
  obtain ⟨-, -, hdec, -, -⟩ := (h133 h).2 L (mem_compSet.1 hL)
  refine le_antisymm ?_ (sup_le inf_le_left (hCB L hL))
  conv_lhs => rw [hdec]
  exact sup_le_sup_left (hCbar L hL) _

theorem istar_join_data (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h133 : Lemma133Statement) {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T) :
    (∀ L ∈ compSet p M D, ∀ L' ∈ compSet p M D, L' ≤ Subgroup.normalizer (L : Set G)) ∧
    (∀ L ∈ compSet p M D, ∀ S : Finset (Subgroup G), S ⊆ compSet p M D → L ∉ S →
      ¬ p ∣ Nat.card ↥((⨆ L' ∈ S, L') ⊓ L)) ∧
    (∀ L ∈ compSet p M D, Sec13h.IsMaxEA p L (B ⊓ L)) ∧
    (∀ L ∈ compSet p M D, ∀ L' ∈ compSet p M D, ∀ x ∈ B ⊓ L, ∀ y ∈ B ⊓ L', x * y = y * x) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hPH := prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD
  have hBel : IsElemAbelian p B := h.bOne.1.1
  refine ⟨fun L hL L' hL' => le_normalizer_of_comp hp
      (istar_comp_facts hP95 hS hPH (mem_compSet.1 hL)).1
      (istar_comp_facts hP95 hS hPH (mem_compSet.1 hL')).1,
    fun L hL S hS' hLS => not_dvd_card_iSup_inf hP95 hS hPH hL S hS' hLS, ?_,
    fun L _ L' _ x hx y hy => congrArg Subtype.val (hBel.1.is_comm.comm ⟨x, hx.1⟩ ⟨y, hy.1⟩)⟩
  intro L hL
  obtain ⟨-, -, -, -, hrk⟩ := (h133 h).2 L (mem_compSet.1 hL)
  have hBLea : IsElemAbelian p (B ⊓ L) := isElemAbelian_of_le hBel inf_le_left
  obtain ⟨k, hk⟩ := Lemma118R.card_eq_pow_of_elemAb hBLea
  have hk' : CFSG.Open.pRank p (B ⊓ L) = k := Lemma118T.pRank_eq_of_isElemAbelian_card hBLea hk
  refine ⟨inf_le_right, hBLea, fun F hFL hFe => ?_⟩
  rw [hk, ← hk', hrk]
  exact Lemma118R.card_le_pow_pRank hFL hFe

theorem isMaxEA_inf_istar (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h133 : Lemma133Statement) {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T) :
    Sec13h.IsMaxEA p (Istar p M D) (B ⊓ Istar p M D) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hBel : IsElemAbelian p B := h.bOne.1.1
  obtain ⟨hnorm, hint, hF, hFc⟩ := istar_join_data h111 h1117 h121 h127 hP95 h133 h
  obtain ⟨hJle, -, hJbound⟩ := bound_join (compSet p M D) hnorm hint (fun L => B ⊓ L) hF hFc
  rw [← istar_eq_iSup_compSet hp M D] at hJle hJbound
  have hJB : (⨆ L ∈ compSet p M D, B ⊓ L) ≤ B ⊓ Istar p M D :=
    le_inf (iSup₂_le fun L _ => inf_le_left) hJle
  refine ⟨inf_le_right, isElemAbelian_of_le hBel inf_le_left, fun F hF hFe => ?_⟩
  exact (hJbound F hF hFe).trans (Subgroup.card_le_of_le hJB)

@[expose] def hatCent (M B I : Subgroup G) : Subgroup G :=
  B ⊓ Sec13h.cmSubgroup M I (pCoreOf 2 M) (fun a ha o ho =>
    ((Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M ha)) o).1 ho)

theorem mem_hatCent {M B I : Subgroup G} {b : G} :
    b ∈ hatCent M B I ↔ b ∈ B ∧ b ∈ M ∧ ∀ x ∈ I, b * x * b⁻¹ * x⁻¹ ∈ pCoreOf 2 M := Iff.rfl

theorem b_eq_inf_sup_hatCent (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h133 : Lemma133Statement) {m p : ℕ} {B M E A D T : Subgroup G} (h : Sec13 G m p B M E A D T) :
    B = (B ⊓ Istar p M D) ⊔ hatCent M B (Istar p M D) := by
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  have hPH := prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS h.bOne h.pre
  have hO : ∀ a ∈ M, ∀ o ∈ pCoreOf 2 M, a * o * a⁻¹ ∈ pCoreOf 2 M := fun a ha o ho =>
    ((Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M ha)) o).1 ho
  have hdec := b_decomp_of hP95 hPH h133 h (fun L => hatCent M B L) (fun L _ => inf_le_left)
    (fun L hL b hb => by
      obtain ⟨hLcomp, hbl⟩ := istar_comp_facts hP95 hS hPH (mem_compSet.1 hL)
      obtain ⟨hbB, hbN, hx⟩ := mem_centBar_iff'.1 hb
      refine ⟨hbB, hBM hbB, fun x hxL => ?_⟩
      have h1 := core_le_pCore_two hp hp2 hLcomp hbl (hx x hxL)
      have e : b * x * b⁻¹ * x⁻¹ = x * (x⁻¹ * (b * x * b⁻¹)) * x⁻¹ := by group
      rw [e]
      exact hO x (hLcomp.1 hxL) _ h1)
    (fun L hL L' hL' hne b hb => by
      obtain ⟨hLcomp, hbl⟩ := istar_comp_facts hP95 hS hPH (mem_compSet.1 hL)
      obtain ⟨hL'comp, -⟩ := istar_comp_facts hP95 hS hPH (mem_compSet.1 hL')
      refine ⟨hb.1, hBM hb.1, fun x hxL => ?_⟩
      have h1 := commutator_mem_of_ne hp hLcomp hL'comp hne hb.2 hxL
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hLcomp.2.1] at h1
      exact core_le_pCore_two hp hp2 hLcomp hbl h1)
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  conv_lhs => rw [hdec]
  refine sup_le_sup (iSup₂_le fun L hL => le_inf inf_le_left
    (inf_le_right.trans ((mem_compSet.1 hL).1.trans le_rfl))) ?_
  · intro b hb
    obtain ⟨hbB, hbI⟩ := hb
    refine ⟨hbB, hBM hbB, fun x hx => ?_⟩
    have hle : Istar p M D ≤ commO M (pCoreOf 2 M) hO b := by
      rw [istar_eq_iSup_compSet hp M D]
      refine iSup₂_le fun L hL y hy => ?_
      have hbL := Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hbI L) hL
      exact ⟨(mem_compSet.1 hL).1.trans (istar_le_M p M D) hy, hbL.2.2 y hy⟩
    exact (hle hx).2

@[expose] def InputB133IstarHat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T : Subgroup G) (_ : Sec13 G m p B M E A D T),
    B = (B ⊓ Istar p M D) ⊔ hatCent M B (Istar p M D) ∧
      Sec13h.IsMaxEA p (Istar p M D) (B ⊓ Istar p M D)

@[expose] def InputCentBHat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (m p : ℕ) (B M E A D T : Subgroup G) (_ : Sec13 G m p B M E A D T),
    ∀ c ∈ hatCent M B (Istar p M D), ∀ g ∈ gammaStar p D, c * g * c⁻¹ * g⁻¹ ∈ pCoreOf 2 M

end B133

section CoreHat

variable {G : Type} [Group G] [Finite G]

theorem core_hat {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    (M I Γ O A B : Subgroup G) (hO : ∀ a ∈ M, ∀ o ∈ O, a * o * a⁻¹ ∈ O) (hO2 : IsPGroup 2 ↥O)
    (hΓM : Γ ≤ M) (hIM : I ≤ M) (hIn : ∀ a ∈ M, GLBConj a I = I) (hAM : A ≤ M) (hBM : B ≤ M)
    (hAΓ : A ≤ Subgroup.normalizer (Γ : Set G)) (hABp : IsPGroup p ↥(A ⊔ B))
    (hPsyl : ∃ P : Subgroup G, P ≤ I ∧ IsPGroup p ↥P ∧
      Nat.card ↥P = p ^ (Nat.card ↥I).factorization p ∧ ∀ x ∈ P, ∀ g ∈ Γ, x * g * x⁻¹ * g⁻¹ ∈ O)
    (hConjI : ∀ E₁ E₂ : Subgroup G, Sec13h.IsMaxEA p I E₁ → Sec13h.IsMaxEA p I E₂ →
      ∃ g ∈ I, GLBConj g E₁ = E₂)
    (Ch : Subgroup G) (hChB : Ch ≤ B) (hChI : ∀ c ∈ Ch, ∀ x ∈ I, c * x * c⁻¹ * x⁻¹ ∈ O)
    (hBdec : B = (B ⊓ I) ⊔ Ch) (hBmax : Sec13h.IsMaxEA p I (B ⊓ I))
    (hCentB : ∀ c ∈ Ch, ∀ g ∈ Γ, c * g * c⁻¹ * g⁻¹ ∈ O) :
    ∃ y ∈ M, IsPGroup p ↥(A ⊔ GLBConj y B) ∧
      ∀ x ∈ GLBConj y B, ∀ g ∈ Γ, x * g * x⁻¹ * g⁻¹ ∈ O := by
  let cm : Subgroup G := Sec13h.cmSubgroup M Γ O hO
  let C : Subgroup G := I ⊓ cm
  have hCI : C ≤ I := inf_le_left
  have hCcm : C ≤ cm := inf_le_right
  have hcmmem : ∀ x : G, x ∈ cm ↔ x ∈ M ∧ ∀ g ∈ Γ, x * g * x⁻¹ * g⁻¹ ∈ O := fun x => Iff.rfl
  have hChM : Ch ≤ M := hChB.trans hBM
  have hconjI : ∀ u ∈ M, ∀ x ∈ I, u * x * u⁻¹ ∈ I := fun u hu x hx => by
    have hx' : x ∈ GLBConj u I := by rw [hIn u hu]; exact hx
    exact mem_gLBConj.1 hx'
  have hconjC : ∀ u ∈ M, (∀ g ∈ Γ, u⁻¹ * g * u ∈ Γ) → ∀ x ∈ C, u * x * u⁻¹ ∈ C := by
    intro u hu hug x hx
    obtain ⟨hxI, hxcm⟩ := hx
    obtain ⟨hxM, hxg⟩ := (hcmmem x).1 hxcm
    refine ⟨hconjI u hu x hxI, (hcmmem _).2 ⟨M.mul_mem (M.mul_mem hu hxM) (M.inv_mem hu),
      fun g hg => ?_⟩⟩
    have key : u * (x * (u⁻¹ * g * u) * x⁻¹ * (u⁻¹ * g * u)⁻¹) * u⁻¹ =
        (u * x * u⁻¹) * g * (u * x * u⁻¹)⁻¹ * g⁻¹ := by group
    have h1 := hO u hu _ (hxg _ (hug g hg))
    rwa [key] at h1
  have hconjC' : ∀ c ∈ M, (∀ x ∈ I, c * x * c⁻¹ * x⁻¹ ∈ O) → ∀ x ∈ C, c * x * c⁻¹ ∈ C := by
    intro c hcM hcI x hx
    obtain ⟨hxI, hxcm⟩ := hx
    obtain ⟨hxM, hxg⟩ := (hcmmem x).1 hxcm
    refine ⟨hconjI c hcM x hxI, (hcmmem _).2 ⟨M.mul_mem (M.mul_mem hcM hxM) (M.inv_mem hcM),
      fun g hg => ?_⟩⟩
    have ho : c * x * c⁻¹ * x⁻¹ ∈ O := hcI x hxI
    have e : (c * x * c⁻¹) * g * (c * x * c⁻¹)⁻¹ * g⁻¹ =
        (c * x * c⁻¹ * x⁻¹) * (x * g * x⁻¹ * g⁻¹) * (g * (c * x * c⁻¹ * x⁻¹)⁻¹ * g⁻¹) := by group
    rw [e]
    exact O.mul_mem (O.mul_mem ho (hxg g hg)) (hO g (hΓM hg) _ (O.inv_mem ho))
  have hAnorm : ∀ a ∈ A, a ∈ Subgroup.normalizer (C : Set G) := by
    intro a ha
    have haM : a ∈ M := hAM ha
    have hconj_a : ∀ g ∈ Γ, a⁻¹ * g * a ∈ Γ := fun g hg => by
      have h1 := (Subgroup.mem_normalizer_iff.1 (hAΓ ha) (a⁻¹ * g * a)).2
      exact h1 (by rwa [show a * (a⁻¹ * g * a) * a⁻¹ = g by group])
    have hconj_ainv : ∀ g ∈ Γ, (a⁻¹)⁻¹ * g * a⁻¹ ∈ Γ := fun g hg => by
      rw [inv_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hAΓ ha) g).1 hg
    refine Subgroup.mem_normalizer_iff.2 (fun y => ⟨fun hy => hconjC a haM hconj_a y hy, fun hy => ?_⟩)
    have h2 := hconjC a⁻¹ (M.inv_mem haM) hconj_ainv _ hy
    rwa [show a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y by group] at h2
  have hChnorm : ∀ c ∈ Ch, c ∈ Subgroup.normalizer (C : Set G) := by
    intro c hc
    refine Subgroup.mem_normalizer_iff.2 (fun y =>
      ⟨fun hy => hconjC' c (hChM hc) (hChI c hc) y hy, fun hy => ?_⟩)
    have h2 := hconjC' c⁻¹ (M.inv_mem (hChM hc)) (hChI c⁻¹ (Ch.inv_mem hc)) _ hy
    rwa [show c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y by group] at h2
  let K : Subgroup G := C ⊔ (A ⊔ Ch)
  have hKnorm : K ≤ Subgroup.normalizer (C : Set G) :=
    sup_le Subgroup.le_normalizer (sup_le (fun a ha => hAnorm a ha) (fun c hc => hChnorm c hc))
  have hCn : ∀ k ∈ K, ∀ c ∈ C, k * c * k⁻¹ ∈ C := fun k hk c hc =>
    (Subgroup.mem_normalizer_iff.1 (hKnorm hk) c).1 hc
  have hXp : IsPGroup p ↥(A ⊔ Ch) := hABp.to_le (sup_le_sup_left hChB A)
  obtain ⟨Q, -, hXQ, hQp, hQd⟩ := Sec13h.sylow_inf_normal_dvd K C (A ⊔ Ch) le_sup_left hCn
    le_sup_right hXp
  have hSp : IsPGroup p ↥(Q ⊓ C) := hQp.to_le inf_le_left
  have hSI : Q ⊓ C ≤ I := inf_le_right.trans hCI
  obtain ⟨P, hPI, hPp, hPc, hPcomm⟩ := hPsyl
  have hPC : P ≤ C := fun x hx =>
    ⟨hPI hx, (hcmmem x).2 ⟨hIM (hPI hx), fun g hg => hPcomm x hx g hg⟩⟩
  have hC0 : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have hvIC : (Nat.card ↥I).factorization p ≤ (Nat.card ↥C).factorization p := by
    have h1 : p ^ (Nat.card ↥I).factorization p ∣ Nat.card ↥C := by
      rw [← hPc]
      exact Subgroup.card_dvd_of_le hPC
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp.out hC0).1 h1
  have hSc : Nat.card ↥(Q ⊓ C) = p ^ (Nat.card ↥I).factorization p :=
    Sec13h.card_eq_pow_of_dvd hSp hSI ((pow_dvd_pow p hvIC).trans hQd)
  obtain ⟨E₀, hE₀I, hE₀ea, hE₀max⟩ := Sec13h.exists_max_ea (G := G) p I
  obtain ⟨g, hgI, hgS⟩ := Sec13h.exists_conj_le_of_sylow I (Q ⊓ C) E₀ hSI hSc hE₀I
    (Sec13h.isPGroup_of_isElemAbelian' hE₀ea)
  set E : Subgroup G := GLBConj g E₀ with hE
  have hEmax : Sec13h.IsMaxEA p I E := by
    refine ⟨?_, sec9_isElemAbelian_gLBConj g hE₀ea, fun F hFI hFea => ?_⟩
    · have h1 := gLBConj_mono g hE₀I
      rwa [hIn g (hIM hgI)] at h1
    · rw [hE, sec9_card_gLBConj]
      exact hE₀max F hFI hFea
  obtain ⟨y₀, hy₀I, hy₀⟩ := hConjI (B ⊓ I) E hBmax hEmax
  have hOp : ¬ p ∣ Nat.card ↥O := not_dvd_card_of_isPGroup_two hp.out hp2 hO2
  have hQO : Q ⊓ O = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out hQp hOp
  have hECh : ∀ e ∈ E, ∀ c ∈ Ch, e * c = c * e := by
    intro e he c hc
    have heQ : e ∈ Q := (hgS he).1
    have hcQ : c ∈ Q := hXQ (Subgroup.mem_sup_right hc)
    have h1 : c * e * c⁻¹ * e⁻¹ ∈ Q ⊓ O :=
      ⟨Q.mul_mem (Q.mul_mem (Q.mul_mem hcQ heQ) (Q.inv_mem hcQ)) (Q.inv_mem heQ),
        hChI c hc e (hSI (hgS he))⟩
    rw [hQO, Subgroup.mem_bot] at h1
    calc e * c = (c * e * c⁻¹ * e⁻¹)⁻¹ * (c * e) := by group
      _ = c * e := by rw [h1, inv_one, one_mul]
  set F : Subgroup G := E ⊔ Ch with hF
  have hFQ : F ≤ Q := sup_le (hgS.trans inf_le_left) (le_sup_right.trans hXQ)
  have hFp : IsPGroup p ↥F := hQp.to_le hFQ
  set N₀ : Subgroup G := I ⊓ O with hN₀
  have hN₀p : ¬ p ∣ Nat.card ↥N₀ := not_dvd_card_of_isPGroup_two hp.out hp2 (hO2.to_le inf_le_right)
  have hFM : F ≤ M := sup_le (hgS.trans (inf_le_right.trans (hCI.trans hIM))) hChM
  have hFN : F ≤ Subgroup.normalizer (N₀ : Set G) := fun x hx => by
    refine mem_normalizer_inf ?_ ?_
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact fun hy => hconjI x (hFM hx) y hy
      · intro hy
        have h1 := hconjI x⁻¹ (M.inv_mem (hFM hx)) _ hy
        rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact fun hy => hO x (hFM hx) y hy
      · intro hy
        have h1 := hO x⁻¹ (M.inv_mem (hFM hx)) _ hy
        rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at h1
  have hFN₀ : F ⊓ N₀ = ⊥ := isPGroup_inf_eq_bot_of_not_dvd hp.out hFp hN₀p
  have hW := CFSG.GH74.GLS.Th2.HY.card_sup_mul_card_inf_of_le_normalizer hFN
  rw [hFN₀, Subgroup.card_bot, mul_one] at hW
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hFp
  have hFc : Nat.card ↥F = p ^ (Nat.card ↥(F ⊔ N₀)).factorization p := by
    rw [hW, ha, factorization_pow_mul hp.out a _ hN₀p]
  have hChy : GLBConj y₀ Ch ≤ Ch ⊔ N₀ := by
    intro z hz
    rw [mem_gLBConj] at hz
    set c := y₀ * z * y₀⁻¹ with hc
    have hzc : z = c * (c⁻¹ * y₀⁻¹ * c * y₀) := by rw [hc]; group
    have hn : c⁻¹ * y₀⁻¹ * c * y₀ ∈ N₀ := by
      refine ⟨?_, ?_⟩
      · have h1 := hconjI c⁻¹ (M.inv_mem (hChM hz)) y₀⁻¹ (I.inv_mem hy₀I)
        rw [inv_inv] at h1
        exact I.mul_mem h1 hy₀I
      · have h1 := hChI c⁻¹ (Ch.inv_mem hz) y₀⁻¹ (I.inv_mem hy₀I)
        rwa [inv_inv, inv_inv] at h1
    rw [hzc]
    exact (Ch ⊔ N₀).mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hn)
  have hBy₀ : GLBConj y₀ B ≤ F ⊔ N₀ := by
    have h1 : GLBConj y₀ B = GLBConj y₀ (B ⊓ I) ⊔ GLBConj y₀ Ch := by
      conv_lhs => rw [hBdec]
      exact Subgroup.map_sup _ _ _
    rw [h1, hy₀, hF, sup_assoc]
    exact sup_le_sup_left hChy E
  have hBp : IsPGroup p ↥B := hABp.to_le le_sup_right
  have hBy₀p : IsPGroup p ↥(GLBConj y₀ B) := hBp.map _
  obtain ⟨z, hzW, hz⟩ := Sec13h.exists_conj_le_of_sylow (F ⊔ N₀) F (GLBConj y₀ B) le_sup_left hFc
    hBy₀ hBy₀p
  have hWM : F ⊔ N₀ ≤ M := sup_le hFM (inf_le_left.trans hIM)
  have hyB : GLBConj (y₀ * z) B ≤ F := by rw [← gLBConj_gLBConj]; exact hz
  refine ⟨y₀ * z, M.mul_mem (hIM hy₀I) (hWM hzW), ?_, ?_⟩
  · exact hQp.to_le (sup_le (le_sup_left.trans hXQ) (hyB.trans hFQ))
  · intro x hx t ht
    have hFcm : F ≤ cm := sup_le (hgS.trans (inf_le_right.trans hCcm))
      (fun c hc => (hcmmem c).2 ⟨hChM hc, fun g' hg' => hCentB c hc g' hg'⟩)
    exact ((hcmmem x).1 (hFcm (hyB hx))).2 t ht

end CoreHat

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims137

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

theorem Claims137.inputSylowCentIstar_of_inputs (h111 : Prop111Statement)
    (h1117 : Prop1117Statement) (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement)
    (hP95 : Prop95) (h134 : Prop134_of_cexStatement) (hOmT : Lemma137b.Input9_6OmegaTransv)
    (hI1013 : Claims137.Input10_13Omega) : Sec13h.InputSylowCentIstar := by
  intro G _ _ m p B M E A D T h
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hp⟩
  have hPH := prop95Hyp_of h111 h1117 h121 h127 h.toSec11 h.hD
  have hO : ∀ a ∈ M, ∀ o ∈ pCoreOf 2 M, a * o * a⁻¹ ∈ pCoreOf 2 M := fun a ha o ho =>
    ((Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M ha)) o).1 ho
  set cm := Sec13h.cmSubgroup M (gammaStar p D) (pCoreOf 2 M) hO with hcm
  have hnorm : ∀ L ∈ Claims137.compSet p M D, ∀ L' ∈ Claims137.compSet p M D,
      L' ≤ Subgroup.normalizer (L : Set G) := fun L hL L' hL' =>
    Claims137.le_normalizer_of_comp hp
      (Claims137.istar_comp_facts hP95 hS hPH (Claims137.mem_compSet.1 hL)).1
      (Claims137.istar_comp_facts hP95 hS hPH (Claims137.mem_compSet.1 hL')).1
  have hC : ∀ L ∈ Claims137.compSet p M D,
      p ^ (Nat.card ↥L).factorization p ∣ Nat.card ↥(L ⊓ cm) := by
    intro L hL
    have h1 := Claims137.not_dvd_index_comp h111 h1117 h121 h127 hP95 h134 hOmT hI1013 h hO
      (Claims137.mem_compSet.1 hL)
    have h2 := Claims137.pow_dvd_card_of_not_dvd_index _ h1
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : L ⊓ cm ≤ L)).toEquiv] at h2
  obtain ⟨P, hP, hPp, hPc⟩ := Claims137.exists_sylow_join cm (Claims137.compSet p M D) hnorm
    (fun L hL S hS' hLS => Claims137.not_dvd_card_iSup_inf hP95 hS hPH hL S hS' hLS) hC
  rw [← Claims137.istar_eq_iSup_compSet hp M D] at hP hPc
  exact ⟨P, hP.trans inf_le_left, hPp, hPc, fun x hx g hg => (hP hx).2.2 g hg⟩

theorem Claims137.inputConjIstar_of_inputs (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h133 : Lemma133Statement) (hI102 : Claims137.Input10_2Omega) : Sec13h.InputConjIstar := by
  intro G _ _ m p B M E A D T h E₁ E₂ h₁ h₂
  have hS : GLStanding G m p := h.standing
  have hp : p.Prime := hS.prime
  have hp2 : p ≠ 2 := hS.ne_two
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hnorm, hint, hF, hFc⟩ := Claims137.istar_join_data h111 h1117 h121 h127 hP95 h133 h
  have hconj : ∀ L ∈ Claims137.compSet p M D, ∀ F₁ F₂ : Subgroup G, Sec13h.IsMaxEA p L F₁ →
      Sec13h.IsMaxEA p L F₂ → ∃ g ∈ L, GLBConj g F₁ = F₂ := by
    intro L hL F₁ F₂ hF₁ hF₂
    obtain ⟨⟨hbl, hpi, -⟩, -⟩ := (h133 h).2 L (Claims137.mem_compSet.1 hL)
    exact Claims137.conj_of_conjMaxEA (Claims137.conjMaxEA_comp hp hp2 hI102 hbl.simple hpi) hF₁ hF₂
  obtain ⟨hJle, hJea, hJbound, hJconj⟩ :=
    Claims137.conj_join (Claims137.compSet p M D) hnorm hint (fun L => B ⊓ L) hF hFc hconj
  rw [← Claims137.istar_eq_iSup_compSet hp M D] at hJle hJbound hJconj
  obtain ⟨h₁le, h₁ea, h₁m⟩ := h₁
  obtain ⟨h₂le, h₂ea, h₂m⟩ := h₂
  have hc₁ := le_antisymm (hJbound E₁ h₁le h₁ea) (h₁m _ hJle hJea)
  have hc₂ := le_antisymm (hJbound E₂ h₂le h₂ea) (h₂m _ hJle hJea)
  exact hJconj E₁ E₂ h₁le h₂le h₁ea h₂ea hc₁ hc₂

theorem Claims137.inputB133IstarHat_of_inputs (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h133 : Lemma133Statement) : Claims137.InputB133IstarHat := fun _ _ _ _ _ _ _ _ _ _ _ h =>
  ⟨Claims137.b_eq_inf_sup_hatCent h111 h1117 h121 h127 hP95 h133 h,
    Claims137.isMaxEA_inf_istar h111 h1117 h121 h127 hP95 h133 h⟩

theorem Claims137.inputCentBHat_of_inputs (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h97 : Prop95Parts.Lemma97) : Claims137.InputCentBHat := by
  intro G _ _ m p B M E A D T h c hc g hg
  have hS : GLStanding G m p := h.standing
  obtain ⟨-, hcM, hcI⟩ := Claims137.mem_hatCent.1 hc
  exact Claims137.centB_core h111 h1117 h121 h127 hP95 h97 h hcM
    (fun x hx => p131_pCore_le_glaPPrime hS.prime hS.ne_two M (hcI x hx)) hg

theorem Claims137.bstar137_of_inputs_hat (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_corStatement) (h127 : Prop127_of_cexStatement)
    (hSyl : Sec13h.InputSylowCentIstar) (hConj : Sec13h.InputConjIstar)
    (hGlob : Claims137.InputB133IstarHat) (hCent : Claims137.InputCentBHat) : BStar137Statement := by
  intro G _ _ m p B M E A D T h
  have hS : GLStanding G m p := h.standing
  haveI : Fact p.Prime := ⟨hS.prime⟩
  have hΓM : gammaStar p D ≤ M := (prop131_of_inputs h111 h1117 h121 h127 h.toSec11 h.hD).2
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hS h.bOne h.pre
  have hO : ∀ a ∈ M, ∀ o ∈ pCoreOf 2 M, a * o * a⁻¹ ∈ pCoreOf 2 M := fun a ha o ho =>
    ((Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M ha)) o).1 ho
  have hO2 : IsPGroup 2 ↥(pCoreOf 2 M) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  obtain ⟨hdec, hmax⟩ := hGlob G m p B M E A D T h
  exact Claims137.core_hat hS.ne_two M (Istar p M D) (gammaStar p D) (pCoreOf 2 M) A B hO hO2 hΓM
    (istar_le_M p M D) (fun a ha => istar_conj_eq p ha) hAM hBM
    (Sec13h.inputANormGamma_holds G m p B M E A D T h) h.hAB (hSyl G m p B M E A D T h)
    (fun E₁ E₂ h₁ h₂ => hConj G m p B M E A D T h E₁ E₂ h₁ h₂)
    (Claims137.hatCent M B (Istar p M D)) inf_le_left
    (fun c hc x hx => (Claims137.mem_hatCent.1 hc).2.2 x hx) hdec hmax
    (fun c hc g hg => hCent G m p B M E A D T h c hc g hg)

theorem Claims137.bstar137_of_partI (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h97 : Prop95Parts.Lemma97) (h133 : Lemma133Statement) (h134 : Prop134_of_cexStatement)
    (hOmT : Lemma137b.Input9_6OmegaTransv) (hI1013 : Claims137.Input10_13Omega)
    (hI102 : Claims137.Input10_2Omega) : BStar137Statement :=
  Claims137.bstar137_of_inputs_hat h111 h1117 (prop121_cor_of h121) h127
    (Claims137.inputSylowCentIstar_of_inputs h111 h1117 h121 h127 hP95 h134 hOmT hI1013)
    (Claims137.inputConjIstar_of_inputs h111 h1117 h121 h127 hP95 h133 hI102)
    (Claims137.inputB133IstarHat_of_inputs h111 h1117 h121 h127 hP95 h133)
    (Claims137.inputCentBHat_of_inputs h111 h1117 h121 h127 hP95 h97)

theorem Claims137.lemma137_i_of_partI (h111 : Prop111Statement) (h1117 : Prop1117Statement)
    (h121 : Prop121_of_cexStatement) (h127 : Prop127_of_cexStatement) (hP95 : Prop95)
    (h97 : Prop95Parts.Lemma97) (h133 : Lemma133Statement) (h134 : Prop134_of_cexStatement)
    (hOmT : Lemma137b.Input9_6OmegaTransv) (hI1013 : Claims137.Input10_13Omega)
    (hI102 : Claims137.Input10_2Omega) : Lemma137_iStatement :=
  lemma137_i_of_bstar
    (Claims137.bstar137_of_partI h111 h1117 h121 h127 hP95 h97 h133 h134 hOmT hI1013 hI102)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
