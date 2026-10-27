module

public import CFSG.Walter.Bender1970.S4.Control
public import CFSG.Walter.ReeOrder.JT.Section7G
public import CFSG.GH74.GLS.C3.Prop121.Coord
public import CFSG.GH74.GLS.C3.Prop121.MooreBasic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm CFSG.GH74.GLS

section Config

variable {G : Type} [Group G] [Finite G] {n : ℕ} {x : G} {K T Q S : Subgroup G} {a : G}

theorem centralizer_le_normalizer_Q (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) (hP : PatternFacts G n) :
    ∀ u ∈ Q, u ≠ 1 → ∀ c : G, c * u = u * c → ∀ r ∈ Q, c * r * c⁻¹ ∈ Q := by
  intro u hu hu1 c hc r hr
  obtain ⟨m, hm, hmx⟩ := transitive hn hG4 h hF hP u hu hu1
  have hm' := Coord.conj_mem_inv hm
  have hux : m⁻¹ * u * m = x := by rw [← hmx]; group
  have hc'x : m⁻¹ * c * m * x = x * (m⁻¹ * c * m) := by
    calc m⁻¹ * c * m * x = m⁻¹ * c * (m * x * m⁻¹) * m := by group
      _ = m⁻¹ * (c * u) * m := by rw [hmx]; group
      _ = m⁻¹ * (u * c) * m := by rw [hc]
      _ = (m⁻¹ * u * m) * (m⁻¹ * c * m) := by group
      _ = x * (m⁻¹ * c * m) := by rw [hux]
  have hc'C : m⁻¹ * c * m ∈ centralizer ({x} : Set G) :=
    mem_centralizer_singleton_iff.2 hc'x
  have h1 := h.Q_normal (m⁻¹ * c * m) hc'C (m⁻¹ * r * m) (hm' r hr)
  have h2 := hm _ h1
  have : m * ((m⁻¹ * c * m) * (m⁻¹ * r * m) * (m⁻¹ * c * m)⁻¹) * m⁻¹ = c * r * c⁻¹ := by group
  rwa [this] at h2

theorem odd_normal_comm_Qg (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) (hP : PatternFacts G n) {t u g : G}
    (hS : Stage3Loc n x K Q t u g) (R : Subgroup G) (hRodd : Odd (Nat.card R))
    (hRn : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) :
    ∀ q ∈ Q, ∀ r ∈ R, (g * q * g⁻¹) * r = r * (g * q * g⁻¹) := by
  classical
  have hginv : g⁻¹ = g := sq_eq_one_inv hS.g_sq
  have hg2 : g * g = 1 := by rw [← sq]; exact hS.g_sq
  have hQ4 : IsKleinFour ↥Q :=
    CFSG.Walter.JT.isKleinFour_of_card_four hS.Q_card (fun q => Subtype.ext (by
      have := hS.Q_sq q.1 q.2
      simpa [sq] using this))
  let D : Subgroup G := R.map (MulAut.conj g).toMonoidHom
  have hDmem : ∀ ρ : G, ρ ∈ D ↔ g * ρ * g⁻¹ ∈ R := by
    intro ρ
    constructor
    · rintro ⟨r, hr, rfl⟩
      show g * (g * r * g⁻¹) * g⁻¹ ∈ R
      have : g * (g * r * g⁻¹) * g⁻¹ = (g * g) * r * (g⁻¹ * g⁻¹) := by group
      rw [this, hg2, show g⁻¹ * g⁻¹ = 1 by rw [hginv]; exact hg2]
      simpa using hr
    · intro hρ
      refine ⟨g * ρ * g⁻¹, hρ, ?_⟩
      show g * (g * ρ * g⁻¹) * g⁻¹ = ρ
      have : g * (g * ρ * g⁻¹) * g⁻¹ = (g * g) * ρ * (g⁻¹ * g⁻¹) := by group
      rw [this, hg2, show g⁻¹ * g⁻¹ = 1 by rw [hginv]; exact hg2]
      simp
  have hDodd : Odd (Nat.card D) := by
    have : Nat.card D = Nat.card R :=
      Nat.card_congr (Subgroup.equivMapOfInjective R _ (MulAut.conj g).injective).toEquiv.symm
    rw [this]; exact hRodd
  have hQD : ∀ q ∈ Q, ∀ ρ ∈ D, q * ρ * q⁻¹ ∈ D := by
    intro q hq ρ hρ
    rw [hDmem] at hρ ⊢
    have hqK : g * q * g⁻¹ ∈ K := hS.g_Q q hq
    have h1 := hRn _ hqK _ hρ
    have : g * (q * ρ * q⁻¹) * g⁻¹ = (g * q * g⁻¹) * (g * ρ * g⁻¹) * (g * q * g⁻¹)⁻¹ := by group
    rw [this]
    exact h1
  have hQnorm : Q ≤ Subgroup.normalizer (D : Set G) := by
    intro q hq
    rw [Subgroup.mem_normalizer_iff]
    intro ρ
    constructor
    · exact hQD q hq ρ
    · intro hρ
      have := hQD q⁻¹ (Q.inv_mem hq) _ hρ
      rwa [show q⁻¹ * (q * ρ * q⁻¹) * q⁻¹⁻¹ = ρ by group] at this
  have hDle : D ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.Walter.le_of_forall_centralizer_le_of_odd (U₀ := Q) (D := D)
      (H := Subgroup.normalizer (Q : Set G)) hQ4 hQnorm hDodd (fun u hu hu1 c hc => by
        rw [Subgroup.mem_normalizer_iff]
        intro r
        have hc' : c * u = u * c := mem_centralizer_singleton_iff.1 hc
        constructor
        · intro hr
          exact centralizer_le_normalizer_Q hn hG4 h hF hP u hu hu1 c hc' r hr
        · intro hr
          have hcinv : c⁻¹ * u = u * c⁻¹ := by
            calc c⁻¹ * u = c⁻¹ * (u * c) * c⁻¹ := by group
              _ = c⁻¹ * (c * u) * c⁻¹ := by rw [hc']
              _ = u * c⁻¹ := by group
          have := centralizer_le_normalizer_Q hn hG4 h hF hP u hu hu1 c⁻¹ hcinv _ hr
          rwa [show c⁻¹ * (c * r * c⁻¹) * c⁻¹⁻¹ = r by group] at this)
  have hcomm : ∀ ρ ∈ D, ∀ q ∈ Q, ρ * q = q * ρ := by
    intro ρ hρ q hq
    have hρN := hDle hρ
    rw [Subgroup.mem_normalizer_iff] at hρN
    have h1 : ρ * q * ρ⁻¹ ∈ Q := (hρN q).1 hq
    set c : G := ρ * q * ρ⁻¹ * q⁻¹ with hc
    have hcQ : c ∈ Q := Q.mul_mem h1 (Q.inv_mem hq)
    have hcD : c ∈ D := by
      have h2 := hQD q hq ρ⁻¹ (D.inv_mem hρ)
      have : c = ρ * (q * ρ⁻¹ * q⁻¹) := by rw [hc]; group
      rw [this]
      exact D.mul_mem hρ h2
    have hc2 : c ^ 2 = 1 := hS.Q_sq c hcQ
    have hdvd1 : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one hc2
    have hdvd2 : orderOf c ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hcD
    have hc1 : c = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd1 with h1 | h1
      · exact orderOf_eq_one_iff.1 h1
      · exfalso
        rw [h1] at hdvd2
        exact (Nat.not_even_iff_odd.2 hDodd) (even_iff_two_dvd.2 hdvd2)
    have : ρ * q * ρ⁻¹ = q := by
      have h3 : ρ * q * ρ⁻¹ * q⁻¹ = 1 := hc1
      calc ρ * q * ρ⁻¹ = (ρ * q * ρ⁻¹ * q⁻¹) * q := by group
        _ = q := by rw [h3]; group
    calc ρ * q = (ρ * q * ρ⁻¹) * ρ := by group
      _ = q * ρ := by rw [this]
  intro q hq r hr
  have hρD : g * r * g⁻¹ ∈ D := by
    rw [hDmem]
    have : g * (g * r * g⁻¹) * g⁻¹ = r := by
      have e : g * (g * r * g⁻¹) * g⁻¹ = (g * g) * r * (g⁻¹ * g⁻¹) := by group
      rw [e, hg2, show g⁻¹ * g⁻¹ = 1 by rw [hginv]; exact hg2]
      simp
    rw [this]; exact hr
  have h1 := hcomm _ hρD q hq
  have h2 : r * (g⁻¹ * q * g) = (g⁻¹ * q * g) * r := by
    calc r * (g⁻¹ * q * g) = g⁻¹ * ((g * r * g⁻¹) * q) * g := by group
      _ = g⁻¹ * (q * (g * r * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * q * g) * r := by group
  have h3 : g⁻¹ * q * g = g * q * g⁻¹ := by rw [hginv]
  rw [h3] at h2
  exact h2.symm

theorem odd_normal_comm_K (hn : n = 5 ∨ n = 6 ∨ n = 7) (hG4 : pRank 2 G ≤ 4)
    (h : IsAConfig n x K T Q S a) (hF : FnFacts n) (hP : PatternFacts G n) {t u g : G}
    (hS : Stage3Loc n x K Q t u g) (R : Subgroup G) (hRodd : Odd (Nat.card R))
    (hRn : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ ∈ R) :
    ∀ r ∈ R, ∀ k ∈ K, r * k = k * r := by
  classical
  have hn5 : 5 ≤ n := by omega
  obtain ⟨eK⟩ := hS.K_alt
  have : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn5)
  have : IsSimpleGroup ↥K := eK.isSimpleGroup
  have hQg := odd_normal_comm_Qg hn hG4 h hF hP hS R hRodd hRn
  let N : Subgroup K := (K ⊓ centralizer (R : Set G)).subgroupOf K
  have hNmem : ∀ k : K, k ∈ N ↔ ∀ r ∈ R, (k : G) * r = r * k := by
    intro k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨-, hk⟩ r hr
      exact (hk r hr).symm
    · intro hk
      exact ⟨k.2, fun r hr => (hk r hr).symm⟩
  have hNnorm : N.Normal := by
    refine ⟨fun n' hn' k => ?_⟩
    rw [hNmem] at hn' ⊢
    intro r hr
    have hk1 : (k : G)⁻¹ * r * (k : G) ∈ R := by
      have := hRn (k⁻¹ : K) (k⁻¹).2 r hr
      simpa using this
    have h2 := hn' _ hk1
    show (k : G) * n' * (k : G)⁻¹ * r = r * ((k : G) * n' * (k : G)⁻¹)
    calc (k : G) * n' * (k : G)⁻¹ * r = (k : G) * (n' * ((k : G)⁻¹ * r * k)) * (k : G)⁻¹ := by group
      _ = (k : G) * (((k : G)⁻¹ * r * k) * n') * (k : G)⁻¹ := by rw [h2]
      _ = r * ((k : G) * n' * (k : G)⁻¹) := by group
  have hN1 : N ≠ ⊥ := by
    intro hbot
    have hx1 : g * x * g⁻¹ ∈ K := hS.g_Q x hS.x_mem
    have hmem : (⟨g * x * g⁻¹, hx1⟩ : K) ∈ N := by
      rw [hNmem]
      intro r hr
      exact hQg x hS.x_mem r hr
    rw [hbot, Subgroup.mem_bot] at hmem
    have : g * x * g⁻¹ = 1 := congrArg Subtype.val hmem
    apply hS.x_ne
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = 1 := by rw [this]; group
  have : N.Normal := hNnorm
  have hNtop : N = ⊤ := (IsSimpleGroup.eq_bot_or_eq_top_of_normal N).resolve_left hN1
  intro r hr k hk
  have : (⟨k, hk⟩ : K) ∈ N := by rw [hNtop]; trivial
  exact ((hNmem _).1 this r hr).symm

end Config

end CFSG.GH74.GLS.C3.Prop121
