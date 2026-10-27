module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Set

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup CFSG.OddStandard.SmallF3.HarrisU33

namespace Fz410Set

variable {G : Type} [Group G] [Finite G] {t : G} {L S T : Subgroup G}
  {x₁ x₂ lam rho tau s : G} {Z E W Q R P : Subgroup G}
  (D : Fz410Set t L S T x₁ x₂ lam rho tau s Z E W Q R P)

include D

theorem nrmP {n : G} (hn : n ∈ normalizer (R : Set G)) (a : G) : n * a * n⁻¹ ∈ P ↔ a ∈ P := by
  constructor
  · intro h
    have := D.facts.charP n⁻¹ (Subgroup.inv_mem _ hn) _ h
    simpa [mul_assoc] using this
  · exact D.facts.charP n hn a

private theorem exists_Q_not_W : ∃ n ∈ Q, n ∉ W := by
  by_contra hcon
  have hle : Q ≤ W := fun a ha => by_contra (fun h => hcon ⟨a, ha, h⟩)
  have := Subgroup.card_le_of_le hle
  rw [D.str.card_Q, D.str.card_W] at this
  omega

private theorem sq_of_comm_s {e : G} (he : e ∈ E) (hcomm : e * s = s * e) : e ^ 2 = 1 := by
  have h := D.s_inv_E e he
  have h1 : s * e * s⁻¹ = e := by rw [← hcomm]; group
  have h2 : e = e⁻¹ := h1.symm.trans h
  calc e ^ 2 = e * e := pow_two e
    _ = e * e⁻¹ := by rw [← h2]
    _ = 1 := mul_inv_cancel e

theorem Z_eq_center (x : G) : x ∈ Z ↔ x ∈ R ∧ ∀ r ∈ R, x * r = r * x := by
  constructor
  · intro hx
    have hxR : x ∈ R := D.str.QR (D.str.WQ (D.str.EW (D.str.ZE hx)))
    refine ⟨hxR, fun r hr => ?_⟩
    have h := D.str.R_Z r hr x hx
    calc x * r = r * x * r⁻¹ * r := by rw [h]
      _ = r * x := by group
  · rintro ⟨hxR, hxc⟩
    have hxQ : x ∈ Q :=
      (D.facts.qc x hxR).mp (fun e he => hxc e (D.str.QR (D.str.WQ (D.str.EW he))))
    have hxt : x * t = t * x := hxc t D.t_mem_R
    have hxs : x * s = s * x := hxc s D.s_mem_R
    have hst : s * t = t * s := D.s_comm_t
    have hxW : x ∈ W := by
      by_contra hxW
      apply D.str.Q_t x hxQ hxW
      calc x * t * x⁻¹ = t * x * x⁻¹ := by rw [hxt]
        _ = t := by group
    rcases D.str.W_split x hxW with hxE | htxE
    · exact D.str.E_invol x hxE (D.sq_of_comm_s hxE hxs)
    · exfalso
      have hec : (t * x) * s = s * (t * x) := by
        calc t * x * s = t * (x * s) := by group
          _ = t * (s * x) := by rw [hxs]
          _ = (t * s) * x := by group
          _ = (s * t) * x := by rw [hst]
          _ = s * (t * x) := by group
      have heZ : t * x ∈ Z := D.str.E_invol _ htxE (D.sq_of_comm_s htxE hec)
      obtain ⟨n, hnQ, hnW⟩ := D.exists_Q_not_W
      have hnR : n ∈ R := D.str.QR hnQ
      have hne : n * (t * x) * n⁻¹ = t * x := D.str.R_Z n hnR _ heZ
      have hnx : n * x * n⁻¹ = x := by
        rw [← hxc n hnR]
        group
      apply D.str.Q_t n hnQ hnW
      have h1 : t = (t * x) * x⁻¹ := by group
      calc n * t * n⁻¹ = n * ((t * x) * x⁻¹) * n⁻¹ := by rw [← h1]
        _ = (n * (t * x) * n⁻¹) * (n * x * n⁻¹)⁻¹ := by group
        _ = (t * x) * x⁻¹ := by rw [hne, hnx]
        _ = t := by rw [← h1]

theorem nrmZ {n : G} (hn : n ∈ normalizer (R : Set G)) (z : G) : n * z * n⁻¹ ∈ Z ↔ z ∈ Z := by
  have key : ∀ m ∈ normalizer (R : Set G), ∀ z ∈ Z, m * z * m⁻¹ ∈ Z := by
    intro m hm z hz
    obtain ⟨hzR, hzc⟩ := (D.Z_eq_center z).mp hz
    refine (D.Z_eq_center _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hm z).mp hzR, fun r hr => ?_⟩
    have hr' : m⁻¹ * r * m ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm) r).mp hr
      simpa using this
    have h := hzc _ hr'
    calc m * z * m⁻¹ * r = m * (z * (m⁻¹ * r * m)) * m⁻¹ := by group
      _ = m * ((m⁻¹ * r * m) * z) * m⁻¹ := by rw [h]
      _ = r * (m * z * m⁻¹) := by group
  constructor
  · intro h
    have := key n⁻¹ (Subgroup.inv_mem _ hn) _ h
    simpa [mul_assoc] using this
  · exact key n hn z

theorem conjE {n : G} (hn : n ∈ normalizer (R : Set G)) :
    (∀ a : G, n⁻¹ * a * n ∈ E ↔ a ∈ E) ∨
      (∀ a : G, n⁻¹ * a * n ∈ E ↔ a ∈ fz410F P t s) := by
  have hn' : n⁻¹ ∈ normalizer (R : Set G) := Subgroup.inv_mem _ hn
  have hiR : n * t * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn t).mp D.t_mem_R
  have hiP : n * t * n⁻¹ ∉ P := fun h => D.t_notin_P ((D.nrmP hn t).mp h)
  have hPn : ∀ a : G, n⁻¹ * a * n ∈ P ↔ a ∈ P := fun a => by simpa using D.nrmP hn' a
  have key : ∀ a : G, n⁻¹ * a * n ∈ E ↔ (a ∈ P ∧ (n * t * n⁻¹) * a = a * (n * t * n⁻¹)) := by
    intro a
    constructor
    · intro h
      have hP : n⁻¹ * a * n ∈ P := D.pf.EP h
      have hc : (n⁻¹ * a * n) * t = t * (n⁻¹ * a * n) := (D.E_cent _ hP).mpr h
      refine ⟨(hPn a).mp hP, ?_⟩
      calc n * t * n⁻¹ * a = n * (t * (n⁻¹ * a * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * a * n) * t) * n⁻¹ := by rw [← hc]
        _ = a * (n * t * n⁻¹) := by group
    · rintro ⟨haP, hcomm⟩
      refine (D.E_cent _ ((hPn a).mpr haP)).mp ?_
      calc n⁻¹ * a * n * t = n⁻¹ * (a * (n * t * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * t * n⁻¹) * a) * n := by rw [hcomm]
        _ = t * (n⁻¹ * a * n) := by group
  rcases D.facts.centP _ hiR hiP with h1 | h2 | h3
  · left
    intro a
    rw [key a]
    constructor
    · rintro ⟨haP, hia⟩
      exact (h1 a haP).mp hia
    · intro haE
      have haP : a ∈ P := D.pf.EP haE
      exact ⟨haP, (h1 a haP).mpr haE⟩
  · right
    intro a
    rw [key a]
    constructor
    · rintro ⟨haP, hia⟩
      exact (h2 a haP).mp hia
    · intro haF
      have haP : a ∈ P := (Subgroup.mem_inf.mp haF).1
      exact ⟨haP, (h2 a haP).mpr haF⟩
  · exfalso
    obtain ⟨e, he, he2⟩ := D.exists_E_sq_ne_one
    have heP : e ∈ P := D.pf.EP he
    have hnP : n * e * n⁻¹ ∈ P := (D.nrmP hn e).mpr heP
    have het : e * t = t * e := (D.E_cent e heP).mpr he
    have hcomm : (n * t * n⁻¹) * (n * e * n⁻¹) = (n * e * n⁻¹) * (n * t * n⁻¹) := by
      calc (n * t * n⁻¹) * (n * e * n⁻¹) = n * (t * e) * n⁻¹ := by group
        _ = n * (e * t) * n⁻¹ := by rw [het]
        _ = (n * e * n⁻¹) * (n * t * n⁻¹) := by group
    have h4 := h3 _ hnP hcomm
    apply he2
    have h5 : n * e ^ 2 * n⁻¹ = 1 := by
      calc n * e ^ 2 * n⁻¹ = n * (e * e) * n⁻¹ := by rw [pow_two]
        _ = (n * e * n⁻¹) * (n * e * n⁻¹) := by group
        _ = (n * e * n⁻¹) ^ 2 := (pow_two _).symm
        _ = 1 := h4
    calc e ^ 2 = n⁻¹ * (n * e ^ 2 * n⁻¹) * n := by group
      _ = 1 := by rw [h5]; group

theorem R_le_M : R ≤ fz410M R E := by
  have hRE : ∀ r ∈ R, ∀ e ∈ E, r * e * r⁻¹ ∈ E := by
    intro r hr e he
    have h := D.facts.rq r hr e (D.str.WQ (D.str.EW he))
    have := E.mul_mem h he
    simpa using this
  intro r hr
  refine Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hr, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact hRE r hr h
  · intro hrh
    have := hRE r⁻¹ (R.inv_mem hr) _ hrh
    simpa [mul_assoc] using this

theorem M_le_N3 : fz410M R E ≤ normalizer (R : Set G) :=
  fun _ hx => (Subgroup.mem_inf.mp hx).1

theorem relIndex_M : (fz410M R E).relIndex (normalizer (R : Set G)) ≤ 2 := by
  by_cases hall : ∀ n ∈ normalizer (R : Set G), n ∈ fz410M R E
  · have h1 : (fz410M R E).relIndex (normalizer (R : Set G)) = 1 := by
      rw [Subgroup.relIndex_eq_one]
      exact hall
    omega
  · obtain ⟨u, huN, huM⟩ : ∃ u, u ∈ normalizer (R : Set G) ∧ u ∉ fz410M R E :=
      by_contra (fun h => hall (fun n hn => by_contra (fun hnM => h ⟨n, hn, hnM⟩)))
    have hF : ∀ n ∈ normalizer (R : Set G), n ∉ fz410M R E →
        ∀ a : G, n⁻¹ * a * n ∈ E ↔ a ∈ fz410F P t s := by
      intro n hn hnM
      rcases D.conjE hn with h1 | h2
      · exfalso
        apply hnM
        refine Subgroup.mem_inf.mpr ⟨hn, ?_⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        have h3 : n⁻¹ * (n * y * n⁻¹) * n = y := by group
        have := h1 (n * y * n⁻¹)
        rwa [h3] at this
      · exact h2
    have hmain : (fz410M R E).relIndex (normalizer (R : Set G)) = 2 := by
      rw [Subgroup.relIndex_eq_two_iff_exists_notMem_and']
      refine ⟨u⁻¹, Subgroup.inv_mem _ huN, ?_, ?_⟩
      · intro h
        exact huM (by simpa using (Subgroup.inv_mem _ h))
      · intro b hb
        by_cases hbM : b ∈ fz410M R E
        · exact Or.inr hbM
        · left
          refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ huN) hb, ?_⟩
          rw [Subgroup.mem_normalizer_iff]
          intro y
          have hu2 := hF u huN huM (b * y * b⁻¹)
          have hb2 := hF b hb hbM (b * y * b⁻¹)
          have e1 : b⁻¹ * (b * y * b⁻¹) * b = y := by group
          have e2 : u⁻¹ * b * y * (u⁻¹ * b)⁻¹ = u⁻¹ * (b * y * b⁻¹) * u := by group
          rw [e2]
          rw [e1] at hb2
          exact hb2.trans hu2.symm
    omega

end Fz410Set

end CFSG.OddStandard.SmallF3.FritzII
