module

public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.HSAux

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {M : Type*} [Group M] [Finite M] {P R : Subgroup M}

theorem core_inf_eq_bot_of_ambient (hPR : P ≤ R) {d : M}
    (hd : GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set M) ⊓ P) = ⊥) :
    GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set M) ⊓ R) ⊓ P = ⊥ := by
  rw [eq_bot_iff, ← hd]
  refine le_GLAPPrimeCoreOf_of_normal
    (C := Subgroup.centralizer ({d} : Set M) ⊓ P)
    (S := GLAPPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set M) ⊓ R) ⊓ P) ?_ ?_ ?_
  · intro x hx
    exact ⟨(GLAPPrimeCoreOf_le _ hx.1).1, hx.2⟩
  · intro g hg x hx
    have hgR : g ∈ Subgroup.centralizer ({d} : Set M) ⊓ R := ⟨hg.1, hPR hg.2⟩
    exact ⟨GLAPPrimeCoreOf_conj_mem g hgR x hx.1,
      P.mul_mem (P.mul_mem hg.2 hx.2) (P.inv_mem hg.2)⟩
  · exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left)
      (coprime_card_GLAPPrimeCoreOf Nat.prime_three _)

theorem plane_delta_bot (hPR : P ≤ R) (hRn : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P)
    (hidx : ∀ a ∈ R, ∀ b ∈ R, a ∉ P → b ∉ P → a * b ∈ P)
    (hA : ∀ x ∈ P, orderOf x = 3 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set M) ⊓ P) = ⊥)
    {nP nY : ℕ} (hnP : Nat.card P = nP)
    (hinv : ∀ t ∈ R, t ∉ P → t * t = 1 →
      9 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set M)) →
        Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set M)) = nY)
    (hmod : ¬ nP ≡ nY [MOD 3 ^ (2 + 1)])
    (E : Subgroup ↥P) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hEc : Nat.card E = 3 ^ 2) :
    (⨅ (d : ↥P) (_ : d ∈ E) (_ : d ≠ 1),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R)) = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  by_contra hy1
  have hyK : ∀ d : ↥P, d ∈ E → d ≠ 1 →
      y ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R) := fun d hd hd1 => by
    have h1 := (Subgroup.mem_iInf.1 hy) d
    have h2 := (Subgroup.mem_iInf.1 h1) hd
    exact (Subgroup.mem_iInf.1 h2) hd1
  obtain ⟨d₀, hd₀E, hd₀1⟩ : ∃ d₀ ∈ E, d₀ ≠ 1 := by
    by_contra hall
    have hall' : ∀ d ∈ E, d = 1 := fun d hd => by
      by_contra hd1
      exact hall ⟨d, hd, hd1⟩
    have h1 : Nat.card E = 1 := Subgroup.card_eq_one.2 ((Subgroup.eq_bot_iff_forall E).2 hall')
    rw [hEc] at h1
    norm_num at h1
  have hord : ∀ d : ↥P, d ∈ E → d ≠ 1 → orderOf (d : M) = 3 := fun d hd hd1 => by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (hE3 d hd) hd1
  have hKP : ∀ d : ↥P, d ∈ E → d ≠ 1 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R) ⊓ P = ⊥ :=
    fun d hd hd1 => core_inf_eq_bot_of_ambient hPR (hA (d : M) d.2 (hord d hd hd1))
  have hyR : y ∈ R := (GLAPPrimeCoreOf_le _ (hyK d₀ hd₀E hd₀1)).2
  have hyP : y ∉ P := fun hyP => hy1 (by
    have h1 : y ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d₀ : M)} : Set M) ⊓ R) ⊓ P :=
      ⟨hyK d₀ hd₀E hd₀1, hyP⟩
    rw [hKP d₀ hd₀E hd₀1] at h1
    exact Subgroup.mem_bot.1 h1)
  have hyy : y * y = 1 := by
    have h1 : y * y ∈ GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d₀ : M)} : Set M) ⊓ R) ⊓ P :=
      ⟨Subgroup.mul_mem _ (hyK d₀ hd₀E hd₀1) (hyK d₀ hd₀E hd₀1), hidx y hyR y hyR hyP hyP⟩
    rw [hKP d₀ hd₀E hd₀1] at h1
    exact Subgroup.mem_bot.1 h1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hcomm : ∀ d : ↥P, d ∈ E → d ≠ 1 →
      ∀ c ∈ Subgroup.centralizer ({(d : M)} : Set M) ⊓ R, c * y = y * c := by
    intro d hd hd1 c hc
    have hcK := GLAPPrimeCoreOf_conj_mem c hc y (hyK d hd hd1)
    have hcR : c ∈ R := hc.2
    have hcyR : c * y * c⁻¹ ∈ R := R.mul_mem (R.mul_mem hcR hyR) (R.inv_mem hcR)
    have hcyP : c * y * c⁻¹ ∉ P := fun hmem => hyP (by
      have h1 := hRn c⁻¹ (R.inv_mem hcR) _ hmem
      have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
      rwa [e] at h1)
    have hprod : y * (c * y * c⁻¹) ∈
        GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ R) ⊓ P :=
      ⟨Subgroup.mul_mem _ (hyK d hd hd1) hcK, hidx y hyR _ hcyR hyP hcyP⟩
    rw [hKP d hd hd1, Subgroup.mem_bot] at hprod
    have h2 : c * y * c⁻¹ = y := by
      have h3 : c * y * c⁻¹ = y⁻¹ := eq_inv_of_mul_eq_one_right hprod
      rw [h3, hyinv]
    calc c * y = c * y * c⁻¹ * c := by group
      _ = y * c := by rw [h2]
  have hyd : ∀ d : ↥P, d ∈ E → y * (d : M) = (d : M) * y := by
    intro d hd
    by_cases hd1 : d = 1
    · rw [hd1]
      simp
    · exact Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ (hyK d hd hd1)).1
  have hnorm : ∀ n : ↥P, n ∈ Subgroup.normalizer (E : Set ↥P) → (n : M) * y = y * (n : M) := by
    intro n hn
    have hnR : (n : M) ∈ R := hPR n.2
    have hd₁E : n⁻¹ * d₀ * n ∈ E := ((Subgroup.mem_normalizer_iff''.1 hn) d₀).1 hd₀E
    have hd₁1 : n⁻¹ * d₀ * n ≠ 1 := by
      intro h1
      apply hd₀1
      have h2 : d₀ = n * (n⁻¹ * d₀ * n) * n⁻¹ := by group
      rw [h2, h1]
      group
    obtain ⟨y', hy'⟩ : ∃ y' : M, y' = (n : M) * y * (n : M)⁻¹ := ⟨_, rfl⟩
    have hy'R : y' ∈ R := by
      rw [hy']
      exact R.mul_mem (R.mul_mem hnR hyR) (R.inv_mem hnR)
    have hy'P : y' ∉ P := fun hmem => hyP (by
      have h1 := hRn _ (R.inv_mem hnR) _ hmem
      have e : (n : M)⁻¹ * y' * (n : M)⁻¹⁻¹ = y := by rw [hy']; group
      rwa [e] at h1)
    have hy'y' : y' * y' = 1 := by
      calc y' * y' = (n : M) * (y * y) * (n : M)⁻¹ := by rw [hy']; group
        _ = 1 := by rw [hyy]; group
    have hy'comm : ∀ c ∈ Subgroup.centralizer ({(d₀ : M)} : Set M) ⊓ P, c * y' = y' * c := by
      intro c hc
      have hcd : c * (d₀ : M) = (d₀ : M) * c := Subgroup.mem_centralizer_singleton_iff.1 hc.1
      have hcent : (n : M)⁻¹ * c * (n : M) * ((n⁻¹ * d₀ * n : ↥P) : M) =
          ((n⁻¹ * d₀ * n : ↥P) : M) * ((n : M)⁻¹ * c * (n : M)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        calc (n : M)⁻¹ * c * (n : M) * ((n : M)⁻¹ * (d₀ : M) * (n : M))
            = (n : M)⁻¹ * (c * (d₀ : M)) * (n : M) := by group
          _ = (n : M)⁻¹ * ((d₀ : M) * c) * (n : M) := by rw [hcd]
          _ = (n : M)⁻¹ * (d₀ : M) * (n : M) * ((n : M)⁻¹ * c * (n : M)) := by group
      have hc' : (n : M)⁻¹ * c * (n : M) ∈
          Subgroup.centralizer ({((n⁻¹ * d₀ * n : ↥P) : M)} : Set M) ⊓ R :=
        ⟨Subgroup.mem_centralizer_singleton_iff.2 hcent,
          R.mul_mem (R.mul_mem (R.inv_mem hnR) (hPR hc.2)) hnR⟩
      have h1 := hcomm _ hd₁E hd₁1 _ hc'
      calc c * y' = (n : M) * ((n : M)⁻¹ * c * (n : M) * y) * (n : M)⁻¹ := by rw [hy']; group
        _ = (n : M) * (y * ((n : M)⁻¹ * c * (n : M))) * (n : M)⁻¹ := by rw [h1]
        _ = y' * c := by rw [hy']; group
    obtain ⟨z, hz⟩ : ∃ z : M, z = y * y' := ⟨_, rfl⟩
    have hzP : z ∈ P := by
      rw [hz]
      exact hidx y hyR y' hy'R hyP hy'P
    have hd₀y' : (d₀ : M) * y' = y' * (d₀ : M) :=
      hy'comm (d₀ : M) ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, d₀.2⟩
    have hzd₀ : (d₀ : M) * z = z * (d₀ : M) := by
      rw [hz]
      calc (d₀ : M) * (y * y') = ((d₀ : M) * y) * y' := by rw [mul_assoc]
        _ = (y * (d₀ : M)) * y' := by rw [← hyd d₀ hd₀E]
        _ = y * ((d₀ : M) * y') := by rw [mul_assoc]
        _ = y * (y' * (d₀ : M)) := by rw [hd₀y']
        _ = (y * y') * (d₀ : M) := by rw [mul_assoc]
    have hzc : ∀ c ∈ Subgroup.centralizer ({(d₀ : M)} : Set M) ⊓ P, c * z = z * c := by
      intro c hc
      have hcy : c * y = y * c := hcomm d₀ hd₀E hd₀1 c ⟨hc.1, hPR hc.2⟩
      have hcy' : c * y' = y' * c := hy'comm c hc
      rw [hz]
      calc c * (y * y') = (c * y) * y' := by rw [mul_assoc]
        _ = (y * c) * y' := by rw [hcy]
        _ = y * (c * y') := by rw [mul_assoc]
        _ = y * (y' * c) := by rw [hcy']
        _ = (y * y') * c := by rw [mul_assoc]
    have hzy : z * y = y * z :=
      hcomm d₀ hd₀E hd₀1 z ⟨Subgroup.mem_centralizer_singleton_iff.2 hzd₀.symm, hPR hzP⟩
    have hy'z : y' = y * z := by
      rw [hz]
      calc y' = (y * y) * y' := by rw [hyy, one_mul]
        _ = y * (y * y') := by rw [mul_assoc]
    have hzz : z * z = 1 := by
      calc z * z = (y * y) * (z * z) := by rw [hyy, one_mul]
        _ = y * (y * z) * z := by group
        _ = y * (z * y) * z := by rw [hzy]
        _ = (y * z) * (y * z) := by group
        _ = y' * y' := by rw [← hy'z]
        _ = 1 := hy'y'
    have hz1 : z = 1 := by
      have hzle : Subgroup.zpowers z ≤
          GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d₀ : M)} : Set M) ⊓ P) := by
        refine le_GLAPPrimeCoreOf_of_normal (S := Subgroup.zpowers z) ?_ ?_ ?_
        · exact (Subgroup.zpowers_le).2
            ⟨Subgroup.mem_centralizer_singleton_iff.2 hzd₀.symm, hzP⟩
        · intro g hg x hx
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
          have hgz : Commute g z := hzc g hg
          have hk : g * z ^ k = z ^ k * g := (Commute.zpow_right hgz k).eq
          rw [hk, mul_assoc, mul_inv_cancel, mul_one]
          exact Subgroup.zpow_mem_zpowers z k
        · have hdvd : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hzz)
          rw [Nat.card_zpowers]
          exact Nat.Coprime.coprime_dvd_right hdvd (by norm_num)
      rw [hA (d₀ : M) d₀.2 (hord d₀ hd₀E hd₀1)] at hzle
      exact Subgroup.mem_bot.1 (hzle (Subgroup.mem_zpowers z))
    have hy'y : y' = y := by rw [hy'z, hz1, mul_one]
    calc (n : M) * y = (n : M) * y * (n : M)⁻¹ * (n : M) := by group
      _ = y' * (n : M) := by rw [hy']
      _ = y * (n : M) := by rw [hy'y]
  set Y' : Subgroup ↥P := (Subgroup.centralizer ({y} : Set M)).subgroupOf P with hY'
  have hEY : E ≤ Y' := fun d hd => by
    rw [hY', Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact (hyd d hd).symm
  have hNY : Subgroup.normalizer (E : Set ↥P) ≤ Y' := fun n hn => by
    rw [hY', Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    exact hnorm n hn
  have hY'card : Nat.card Y' = Nat.card ↥(P ⊓ Subgroup.centralizer ({y} : Set M)) := by
    rw [hY', ← Subgroup.inf_subgroupOf_left (Subgroup.centralizer ({y} : Set M)) P]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hdvd9 : 9 ∣ Nat.card Y' := by
    have h1 : Nat.card E ∣ Nat.card Y' := Subgroup.card_dvd_of_le hEY
    rwa [hEc, show (3 : ℕ) ^ 2 = 9 by norm_num] at h1
  have hYcard : Nat.card Y' = nY := by
    rw [hY'card]
    exact hinv y hyR hyP hyy (by rwa [hY'card] at hdvd9)
  have h1 : Nat.card (Subgroup.normalizer (E : Set ↥P)) ≡ Nat.card ↥P [MOD 3 ^ (2 + 1)] :=
    Sylow.card_normalizer_modEq_card hEc
  have hEc' : Nat.card (E.subgroupOf Y') = 3 ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEY).toEquiv, hEc]
  have h2 : Nat.card (Subgroup.normalizer ((E.subgroupOf Y' : Subgroup ↥Y') : Set ↥Y')) ≡
      Nat.card ↥Y' [MOD 3 ^ (2 + 1)] := Sylow.card_normalizer_modEq_card hEc'
  rw [← Subgroup.subgroupOf_normalizer_eq hEY] at h2
  have h3 : Nat.card ((Subgroup.normalizer (E : Set ↥P)).subgroupOf Y') =
      Nat.card (Subgroup.normalizer (E : Set ↥P)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNY).toEquiv
  rw [h3] at h2
  have h4 := h1.symm.trans h2
  rw [hYcard, hnP] at h4
  exact hmod h4

theorem eq_one_of_mem_cores (hPR : P ≤ R) (hRn : ∀ r ∈ R, ∀ q ∈ P, r * q * r⁻¹ ∈ P)
    (hidx : ∀ a ∈ R, ∀ b ∈ R, a ∉ P → b ∉ P → a * b ∈ P)
    (hA : ∀ x ∈ P, orderOf x = 3 →
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({x} : Set M) ⊓ P) = ⊥)
    {nP nY : ℕ} (hnP : Nat.card P = nP)
    (hinv : ∀ t ∈ R, t ∉ P → t * t = 1 →
      9 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set M)) →
        Nat.card ↥(P ⊓ Subgroup.centralizer ({t} : Set M)) = nY)
    (hmod : ¬ nP ≡ nY [MOD 3 ^ (2 + 1)])
    {E : Subgroup M} (hEP : E ≤ P) (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hEc : Nat.card E = 3 ^ 2)
    {H' : Subgroup M} (hPH' : P ≤ H') (hH'R : H' ≤ R) {y : M}
    (hy : ∀ d ∈ E, d ≠ 1 →
      y ∈ GLAPPrimeCoreOf 3 (H' ⊓ Subgroup.centralizer ({d} : Set M))) : y = 1 := by
  have h0 := plane_delta_bot (R := H') hPH' (fun r hr q hq => hRn r (hH'R hr) q hq)
    (fun a ha b hb => hidx a (hH'R ha) b (hH'R hb)) hA hnP (fun t ht => hinv t (hH'R ht)) hmod
    (E.subgroupOf P)
    (fun x hx => Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 _ (Subgroup.mem_subgroupOf.1 hx)))
    (by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEP).toEquiv]; exact hEc)
  have hmem : y ∈ ⨅ (d : ↥P) (_ : d ∈ E.subgroupOf P) (_ : d ≠ 1),
      GLAPPrimeCoreOf 3 (Subgroup.centralizer ({(d : M)} : Set M) ⊓ H') := by
    refine Subgroup.mem_iInf.2 fun d => Subgroup.mem_iInf.2 fun hd => Subgroup.mem_iInf.2
      fun hd1 => ?_
    rw [inf_comm]
    exact hy d (Subgroup.mem_subgroupOf.1 hd) (fun h => hd1 (Subtype.ext h))
  rw [h0] at hmem
  exact Subgroup.mem_bot.1 hmem

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.HSAux
