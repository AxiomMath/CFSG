module

public import CFSG.GH74.Uniqueness.Section14Lem49

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] {Z : Set X} {M : Subgroup X} {t : X} {n r : ℕ}
  {L K J Mo P U T S2 : Subgroup X}

namespace Sec14F

variable (F : Facts14 Z M t n r L K J Mo P U T S2)
include F

theorem inv_commutator_mem {g u : X} (hgM : g ∈ M) (hgu : g * u * g⁻¹ * u⁻¹ ∈ Mo) :
    g⁻¹ * u * g⁻¹⁻¹ * u⁻¹ ∈ Mo := by
  have e : g⁻¹ * u * g⁻¹⁻¹ * u⁻¹ = g⁻¹ * (g * u * g⁻¹ * u⁻¹)⁻¹ * g⁻¹⁻¹ := by group
  rw [e]
  exact F.Mo_normal g⁻¹ (M.inv_mem hgM) _ (inv_mem hgu)

theorem conj_T {u : X} (hu : u ∈ U) (hu1 : u ≠ 1) {g : X} (hgM : g ∈ M)
    (hgu : g * u * g⁻¹ * u⁻¹ ∈ Mo) : ∀ x ∈ T, g * x * g⁻¹ ∈ T := by
  intro x hx
  rw [← F.cent_Mo_u u hu hu1] at hx ⊢
  obtain ⟨hxC, hxu⟩ := mem_inf.mp hx
  refine mem_inf.mpr ⟨?_, ?_⟩
  · rw [mem_centralizer_iff]
    intro m hm
    have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ Mo := F.Mo_normal g⁻¹ (M.inv_mem hgM) m hm
    rw [inv_inv] at hm'
    have h1 := (mem_centralizer_iff.mp hxC) _ hm'
    calc m * (g * x * g⁻¹) = g * ((g⁻¹ * m * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * m * g)) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * m := by group
  · rw [mem_centralizer_singleton_iff]
    set c := g * u * g⁻¹ * u⁻¹ with hc
    have hc' : g⁻¹ * u * g = (g⁻¹ * c * g)⁻¹ * u := by rw [hc]; group
    have hc'Mo : (g⁻¹ * c * g)⁻¹ ∈ Mo := by
      have := F.Mo_normal g⁻¹ (M.inv_mem hgM) c hgu
      rw [inv_inv] at this
      exact inv_mem this
    have hxc : x * (g⁻¹ * c * g)⁻¹ = (g⁻¹ * c * g)⁻¹ * x :=
      ((mem_centralizer_iff.mp hxC) _ hc'Mo).symm
    have hxu' : x * u = u * x := mem_centralizer_singleton_iff.mp hxu
    have h1 : x * (g⁻¹ * u * g) = (g⁻¹ * u * g) * x := by
      have hc1 : Commute x (g⁻¹ * c * g)⁻¹ := hxc
      have hc2 : Commute x u := hxu'
      rw [hc']
      exact (hc1.mul_right hc2).eq
    calc g * x * g⁻¹ * u = g * (x * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * x) * g⁻¹ := by rw [h1]
      _ = u * (g * x * g⁻¹) := by group

theorem mem_normalizer_T {u : X} (hu : u ∈ U) (hu1 : u ≠ 1) {g : X} (hgM : g ∈ M)
    (hgu : g * u * g⁻¹ * u⁻¹ ∈ Mo) : g ∈ normalizer (T : Set X) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨conj_T F hu hu1 hgM hgu x, fun hx => ?_⟩
  have := conj_T F hu hu1 (M.inv_mem hgM) (inv_commutator_mem F hgM hgu) _ hx
  simpa [mul_assoc] using this

theorem ND_le_NT : dGrp M t ⊓ normalizer (U : Set X) ≤ normalizer (T : Set X) := by
  intro d hd
  obtain ⟨hdD, hdU⟩ := mem_inf.mp hd
  have hdP := F.D_norm_P hdD
  have key : ∀ d, d ∈ normalizer (P : Set X) → d ∈ normalizer (U : Set X) →
      ∀ x ∈ T, d * x * d⁻¹ ∈ T := by
    intro d hdP hdU x hx
    obtain ⟨p, hp, u, hu, rfl⟩ := (Sec146.mem_T_iff F).mp hx
    have e : d * (p * u) * d⁻¹ = (d * p * d⁻¹) * (d * u * d⁻¹) := by group
    rw [e]
    exact mul_mem (Sec146.P_le_T F ((mem_normalizer_iff.mp hdP p).mp hp))
      (Sec146.U_le_T F ((mem_normalizer_iff.mp hdU u).mp hu))
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key d hdP hdU x, fun hx => ?_⟩
  have := key d⁻¹ (inv_mem hdP) (inv_mem hdU) _ hx
  simpa [mul_assoc] using this

theorem not_dvd_orderOf [Finite X] (h146 : Concl146 M t n K Mo U T S2) {g : X}
    (hg : g ∈ normalizer (T : Set X)) : ¬ r ∣ orderOf g := by
  set ND := dGrp M t ⊓ normalizer (U : Set X) with hND
  have hNDS : ND ≤ normalizer (S2 : Set X) := (ND_le_NT F).trans h146.normal
  have hprod := card_sup_mul_card_inf' hNDS
  have hgmem : g ∈ ND ⊔ S2 := by
    obtain ⟨s, hs, d, hd, hdU, rfl⟩ := h146.normalizer_T g hg
    exact mul_mem (mem_sup_right hs) (mem_sup_left (mem_inf.mpr ⟨hd, hdU⟩))
  have h1 : orderOf g ∣ Nat.card ↥(ND ⊔ S2) := by
    have := orderOf_dvd_natCard (⟨g, hgmem⟩ : ↥(ND ⊔ S2))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : Nat.card ↥(ND ⊔ S2) ∣ Nat.card S2 * Nat.card ND := ⟨_, hprod.symm⟩
  intro hr
  have h3 := (hr.trans h1).trans h2
  rcases (Nat.Prime.dvd_mul F.r_prime).mp h3 with h4 | h4
  · obtain ⟨k, hk⟩ := F.S2_sylow.isPGroup.exists_card_eq
    rw [hk] at h4
    exact F.r_ne_two ((Nat.prime_dvd_prime_iff_eq F.r_prime Nat.prime_two).mp
      (F.r_prime.dvd_of_dvd_pow h4))
  · exact F.r_not_dvd_D (h4.trans (Subgroup.card_dvd_of_le inf_le_left))

theorem false_of_lemmas [Finite X] (h146 : Concl146 M t n K Mo U T S2)
    (h149 : ∀ u ∈ U, ∀ g ∈ M, g * u * g⁻¹ ∈ S2 → g * u * g⁻¹ * u⁻¹ ∈ Mo)
    (hZ : ZStar14Stmt) : False := by
  have : Fact r.Prime := ⟨F.r_prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ U, u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact F.U_ne_bot (eq_bot_iff.mpr fun x hx => mem_bot.mpr (hcon x hx))
  have huMo : u ∉ Mo := by
    intro h
    have : u ∈ Mo ⊓ U := mem_inf.mpr ⟨h, hu⟩
    rw [Sec146.Mo_inf_U F, mem_bot] at this
    exact hu1 this
  have hMo2 : IsPGroup 2 Mo := IsPGroup.of_card F.card_Mo
  obtain ⟨R, hR, hRn⟩ := hZ M Mo S2 u r F.Mo_le_M F.Mo_normal hMo2 (Sec149.S2_sylow_M F h146)
    ((Sec146.Mo_le_T F).trans F.T_le_S2) (F.T_le_S2 (Sec146.U_le_T F hu)) huMo
    (by rw [F.U_sq u hu]; exact one_mem _)
    (fun s hs => h146.quot_center s hs u (mem_sup_right hu)) (h149 u hu)
    (fun g hgM hgu => h146.normal (mem_normalizer_T F hu hu1 hgM hgu))
    (fun _ _ hodd _ hwS => Sec149.odd_centralizes_T F hodd fun x hx => hwS x (F.T_le_S2 hx))
    F.r_prime F.r_ne_two
    (fun g hgM hgu => not_dvd_orderOf F h146 (mem_normalizer_T F hu hu1 hgM hgu))
  have hKH : K ≤ normalizer ((R ⊔ Mo : Subgroup X) : Set X) := by
    intro k hk
    have hkM := Sec146.K_le_M F hk
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hRn k hkM x, fun hx => ?_⟩
    have := hRn k⁻¹ (M.inv_mem hkM) _ hx
    simpa [mul_assoc] using this
  have hRMo : R ≤ normalizer (Mo : Set X) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro m
    have hxM := hR.le hx
    refine ⟨F.Mo_normal x hxM m, fun hm => ?_⟩
    have := F.Mo_normal x⁻¹ (M.inv_mem hxM) _ hm
    simpa [mul_assoc] using this
  have hprod := card_sup_mul_card_inf' hRMo
  have hHdvd : Nat.card ↥(R ⊔ Mo) ∣ Nat.card R * Nat.card Mo :=
    ⟨Nat.card ↥(Mo ⊓ R), by rw [hprod]; ring⟩
  have hrK : ¬ r ∣ Nat.card K :=
    fun h => F.r_not_dvd_D (h.trans (Subgroup.card_dvd_of_le (Sec146.K_le_D F)))
  have hcop : Nat.Coprime (Nat.card K) (Nat.card ↥(R ⊔ Mo)) := by
    apply Nat.Coprime.coprime_dvd_right hHdvd
    apply Nat.Coprime.mul_right
    · obtain ⟨k, hk⟩ := hR.isPGroup.exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right _ ((Nat.coprime_comm.mp
        ((Nat.Prime.coprime_iff_not_dvd F.r_prime).mpr hrK)))
    · rw [F.card_Mo]
      exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (Sec149.odd_card_K F))
  have hKsolv : Group.IsSolvable ↥K :=
    Group.isSolvable_of_comm fun a b => Subtype.ext (F.K_comm a a.2 b b.2)
  obtain ⟨R', hR', hKR'⟩ := exists_sylow_normalized_of_coprime hKH hcop r
  have hHM : R ⊔ Mo ≤ M := sup_le hR.le F.Mo_le_M
  have hR'M : ABGLocalTools.IsSylowOf r R' M := by
    apply ABGLocalTools.isSylowOf_of_card (hR'.le.trans hHM)
    rw [hR'.card_eq]
    congr 1
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le hHM) r
    · have h1 : Nat.card R ∣ Nat.card ↥(R ⊔ Mo) := Subgroup.card_dvd_of_le le_sup_left
      rw [hR.card_eq] at h1
      exact (F.r_prime.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
  exact F.not_norm_sylow R' hR'M hKR'

end Sec14F

end CFSG.GH74.Uniqueness
