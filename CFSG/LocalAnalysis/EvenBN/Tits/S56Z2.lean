module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Z1

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem s56_M_le_normalizer_C (d : Data G) :
    d.M ≤ normalizer (centralizer (d.A : Set G) : Set G) := by
  have key : ∀ g ∈ d.M, ∀ c ∈ centralizer (d.A : Set G),
      g * c * g⁻¹ ∈ centralizer (d.A : Set G) := by
    intro g hg c hc
    rw [mem_centralizer_iff]
    intro a ha
    have hga : g⁻¹ * a * g ∈ d.A := by
      have := (mem_normalizer_iff.1 (inv_mem hg) a).1 ha
      simpa using this
    have h := mem_centralizer_iff.1 hc _ hga
    calc a * (g * c * g⁻¹) = g * ((g⁻¹ * a * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * a * g)) * g⁻¹ := by rw [h]
      _ = g * c * g⁻¹ * a := by group
  intro g hg
  rw [mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem Hyp.s56_E_le_C (hd : d.Hyp) : d.E ≤ centralizer (d.A : Set G) := fun e he => by
  rw [mem_centralizer_iff]
  intro a ha
  exact congrArg Subtype.val (hd.A_facts.2.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨e, s56_E_le_A d he⟩)

theorem Hyp.s56_relIndex_E_C_le (hd : d.Hyp) :
    d.E.relIndex (centralizer (d.A : Set G)) ≤ 4 := by
  have hEC := hd.s56_E_le_C
  have h := Subgroup.relIndex_mul_card (H := d.E) (K := centralizer (d.A : Set G))
  rw [inf_of_le_left hEC, hd.A_facts.1] at h
  obtain ⟨-, hc⟩ := hd.s56_centralizer_A
  have hcard : Nat.card (centralizer (d.A : Set G)) ≤ 128 := by
    rcases hc with ⟨-, h6⟩ | ⟨-, h7⟩
    · rw [h6]; norm_num
    · calc Nat.card (centralizer (d.A : Set G)) ≤ 2 ^ 7 := h7
        _ = 128 := by norm_num
  omega

theorem Hyp.s56_conj_z1_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {z₁ : G}
    (hz₁ : z₁ ∈ d.s56Q2) (hε : d.s56Eps z₁ = d.z) {g : G} (hg : g ∈ zpowers d.x₅) :
    z₁⁻¹ * (g * z₁ * g⁻¹) ∈ d.E := by
  have hxM := hd.s56_x5_mem_M
  have hxt := hd.s56_x5_comm_t
  have hxz := hd.s56_x5_comm_z
  let T : Subgroup G :=
    { carrier := {g | g ∈ d.M ∧ z₁⁻¹ * (g * z₁ * g⁻¹) ∈ d.E}
      one_mem' := ⟨one_mem _, by simp [one_mem]⟩
      mul_mem' := by
        rintro g h ⟨hgM, hg⟩ ⟨hhM, hh⟩
        refine ⟨mul_mem hgM hhM, ?_⟩
        have hcen : ∀ e ∈ d.E, z₁ * e = e * z₁ := fun e he =>
          (((s56_mem_Q2_iff).1 hz₁).2 e he).symm
        have he₁ : g * (z₁⁻¹ * (h * z₁ * h⁻¹)) * g⁻¹ ∈ d.E :=
          (mem_normalizer_iff.1 (hd.s56_ME hgM) _).1 hh
        have e : z₁⁻¹ * (g * h * z₁ * (g * h)⁻¹) =
            (z₁⁻¹ * (g * z₁ * g⁻¹)) * (g * (z₁⁻¹ * (h * z₁ * h⁻¹)) * g⁻¹) := by group
        rw [e]
        exact mul_mem hg he₁
      inv_mem' := by
        rintro g ⟨hgM, hg⟩
        refine ⟨inv_mem hgM, ?_⟩
        have he₁ : g⁻¹ * (z₁⁻¹ * (g * z₁ * g⁻¹)) * g⁻¹⁻¹ ∈ d.E :=
          (mem_normalizer_iff.1 (hd.s56_ME (inv_mem hgM)) _).1 hg
        have e : z₁⁻¹ * (g⁻¹ * z₁ * g⁻¹⁻¹) =
            (g⁻¹ * (z₁⁻¹ * (g * z₁ * g⁻¹)) * g⁻¹⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem he₁ }
  have hxT : d.x₅ ∈ T := by
    refine ⟨hxM, ?_⟩
    set w := d.x₅ * z₁ * d.x₅⁻¹ with hw
    have hwQ2 : w ∈ d.s56Q2 := hd.s56_Q2_conj_mem hxM hz₁
    have hεw : d.s56Eps w = d.z := by
      rw [hw, hd.s56_eps_conj hxt, hε]
      calc d.x₅ * d.z * d.x₅⁻¹ = d.z * d.x₅ * d.x₅⁻¹ := by rw [hxz]
        _ = d.z := by group
    have hu : z₁⁻¹ * w ∈ d.s56Q2 := mul_mem (inv_mem hz₁) hwQ2
    have hεu : d.s56Eps (z₁⁻¹ * w) = 1 := by
      rw [hd.s56_eps_mul_Q2' (inv_mem hz₁) hwQ2, hd.s56_eps_inv_Q2 hz₁, hεw, hε]
      exact hd.s56_z_sq
    have huC : z₁⁻¹ * w ∈ centralizer (d.A : Set G) := by
      rw [hd.s56_mem_centralizer_A_iff]
      refine ⟨((s56_mem_Q2_iff).1 hu).2, ?_⟩
      have h1 := hd.s56_conj_t (z₁⁻¹ * w)
      rw [hεu, mul_one] at h1
      calc (z₁⁻¹ * w) * d.t = (z₁⁻¹ * w) * d.t * (z₁⁻¹ * w)⁻¹ * (z₁⁻¹ * w) := by group
        _ = d.t * (z₁⁻¹ * w) := by rw [h1]
    exact S56.conj_mem_of_index_le_four hd.s56_orderOf_x5 hd.s56_E_le_C
      (hd.s56_ME hxM) (s56_M_le_normalizer_C d hxM) hd.s56_relIndex_E_C_le huC
  exact (zpowers_le.2 hxT) hg |>.2

theorem Hyp.s56_eq_J_of_mem (hd : d.Hyp) {H : Subgroup G} (hEH : d.E ≤ H)
    (hHJ : H ≤ d.s56J) (hx : d.x₅ ∈ normalizer (H : Set G)) (hv : d.pv 7 ∈ H) :
    H = d.s56J := by
  have hxM := hd.s56_x5_mem_M
  have hmod := S56.card_modEq_of_centralizer_le hd.s56_orderOf_x5 hEH hHJ
    (hd.s56_ME hxM) hx
    (fun c hc hcx => hd.s56_zpowers_le_E (hd.s56_J_cent_x5 hc hcx.symm))
  rw [hd.A_facts.1] at hmod
  have hdvd : Nat.card H ∣ 2 ^ 9 := by
    have := Subgroup.card_dvd_of_le hHJ
    rwa [hd.s56_card_J] at this
  obtain ⟨k, hk9, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h32 : 32 ∣ Nat.card H := by
    have := Subgroup.card_dvd_of_le hEH
    rwa [hd.A_facts.1] at this
  rw [hk] at hmod h32
  have hk5 : 5 ≤ k := by
    rcases Nat.lt_or_ge k 5 with hlt | hge
    · exfalso
      interval_cases k <;> norm_num at h32
    · exact hge
  have hkc : k = 5 ∨ k = 9 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  rcases hkc with rfl | rfl
  · exfalso
    have hEH' : d.E = H := Subgroup.eq_of_le_of_card_ge hEH (by rw [hk, hd.A_facts.1]; norm_num)
    apply hd.s56_pv7_not_mem_E
    rw [hEH']; exact hv
  · exact (Subgroup.eq_of_le_of_card_ge hHJ (by rw [hd.s56_card_J, hk]))

theorem Hyp.s56_J_comm_z1_mem_E (h49 : d.Thm49Statement) (hd : d.Hyp) {z₁ : G}
    (hz₁ : z₁ ∈ d.s56Q2) (hε : d.s56Eps z₁ = d.z) {j : G} (hj : j ∈ d.s56J) :
    j * z₁ * j⁻¹ * z₁⁻¹ ∈ d.E := by
  have hxM := hd.s56_x5_mem_M
  have hcen : ∀ e ∈ d.E, z₁ * e = e * z₁ := fun e he => (((s56_mem_Q2_iff).1 hz₁).2 e he).symm
  let H₁ : Subgroup G :=
    { carrier := {j | j ∈ d.s56J ∧ j * z₁ * j⁻¹ * z₁⁻¹ ∈ d.E}
      one_mem' := ⟨one_mem _, by simpa using one_mem d.E⟩
      mul_mem' := by
        rintro j j' ⟨hj, hjE⟩ ⟨hj', hj'E⟩
        refine ⟨mul_mem hj hj', ?_⟩
        have e : j * j' * z₁ * (j * j')⁻¹ * z₁⁻¹ =
            (j * (j' * z₁ * j'⁻¹ * z₁⁻¹) * j⁻¹) * (j * z₁ * j⁻¹ * z₁⁻¹) := by group
        rw [e]
        exact mul_mem ((mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M hj)) _).1 hj'E) hjE
      inv_mem' := by
        rintro j ⟨hj, hjE⟩
        refine ⟨inv_mem hj, ?_⟩
        have e : j⁻¹ * z₁ * j⁻¹⁻¹ * z₁⁻¹ = j⁻¹ * (j * z₁ * j⁻¹ * z₁⁻¹)⁻¹ * j⁻¹⁻¹ := by group
        rw [e]
        exact (mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M (inv_mem hj))) _).1 (inv_mem hjE) }
  have hEH : d.E ≤ H₁ := fun e he => ⟨s56_E_le_J d he, by
    have h := hcen e he
    have e1 : e * z₁ * e⁻¹ * z₁⁻¹ = 1 := by rw [← h]; group
    rw [e1]; exact one_mem _⟩
  have hcon : ∀ g ∈ zpowers d.x₅, ∀ j ∈ H₁, g * j * g⁻¹ ∈ H₁ := by
    intro g hg j ⟨hj, hjE⟩
    have hgM : g ∈ d.M := (zpowers_le.2 hxM) hg
    refine ⟨(mem_normalizer_iff.1 ((zpowers_le.2 hd.s56_x5_normalizes_J) hg) j).1 hj, ?_⟩
    have hw := hd.s56_conj_z1_mem h49 hz₁ hε (inv_mem hg)
    set e := z₁⁻¹ * (g⁻¹ * z₁ * g⁻¹⁻¹) with hedef
    have hwe : g⁻¹ * z₁ * g = z₁ * e := by rw [hedef]; group
    have hjw : j * (z₁ * e) * j⁻¹ * (z₁ * e)⁻¹ ∈ d.E := by
      have hje := hd.s56_J_comm_E hj hw
      have hjeE : j * e * j⁻¹ * e⁻¹ ∈ d.E := hd.s56_zpowers_le_E hje
      have e1 : j * (z₁ * e) * j⁻¹ * (z₁ * e)⁻¹ =
          (j * z₁ * j⁻¹ * z₁⁻¹) * (z₁ * (j * e * j⁻¹ * e⁻¹) * z₁⁻¹) := by group
      rw [e1]
      refine mul_mem hjE ?_
      have h3 : z₁ * (j * e * j⁻¹ * e⁻¹) * z₁⁻¹ = j * e * j⁻¹ * e⁻¹ := by
        have := hcen _ hjeE
        calc z₁ * (j * e * j⁻¹ * e⁻¹) * z₁⁻¹ = (j * e * j⁻¹ * e⁻¹) * z₁ * z₁⁻¹ := by rw [this]
          _ = j * e * j⁻¹ * e⁻¹ := by group
      rw [h3]; exact hjeE
    have e2 : g * j * g⁻¹ * z₁ * (g * j * g⁻¹)⁻¹ * z₁⁻¹ =
        g * (j * (z₁ * e) * j⁻¹ * (z₁ * e)⁻¹) * g⁻¹ := by
      rw [← hwe]; group
    show (g * j * g⁻¹) * z₁ * (g * j * g⁻¹)⁻¹ * z₁⁻¹ ∈ d.E
    rw [e2]
    exact (mem_normalizer_iff.1 (hd.s56_ME hgM) _).1 hjw
  have hx : d.x₅ ∈ normalizer (H₁ : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hcon _ (mem_zpowers _) h hh, fun hh => ?_⟩
    have := hcon d.x₅⁻¹ (inv_mem (mem_zpowers _)) _ hh
    simpa [mul_assoc] using this
  have hv : d.pv 7 ∈ H₁ := by
    refine ⟨s56_pv7_mem_J d, ?_⟩
    have hN : z₁ ∈ d.N := (hd.s56_mem_N_iff_eps h49 (hd.s56_Q2_le_Q0 h49 hz₁)).2
      (hε ▸ hd.s56_z_mem_F)
    exact hd.s56_cm_mem_E h49 hz₁ hN
  have hJ := hd.s56_eq_J_of_mem hEH (fun j hj => hj.1) hx hv
  have : j ∈ H₁ := by rw [hJ]; exact hj
  exact this.2

theorem Hyp.s56_J_conj_S (h49 : d.Thm49Statement) (hd : d.Hyp) {z₁ : G}
    (hz₁ : z₁ ∈ d.s56Q2) (hε : d.s56Eps z₁ = d.z) (hz₁sq : z₁ * z₁ ∈ d.E) {j : G}
    (hj : j ∈ d.s56J) {s : G} (hs : s ∈ d.E ⊔ zpowers z₁) : j * s * j⁻¹ ∈ d.E ⊔ zpowers z₁ := by
  have hcen : ∀ e ∈ d.E, z₁ * e = e * z₁ := fun e he => (((s56_mem_Q2_iff).1 hz₁).2 e he).symm
  have hES : d.E ≤ d.E ⊔ zpowers z₁ := le_sup_left
  have hz₁S : z₁ ∈ d.E ⊔ zpowers z₁ := mem_sup_right (mem_zpowers _)
  have hjE : ∀ e ∈ d.E, j * e * j⁻¹ ∈ d.E := fun e he =>
    (mem_normalizer_iff.1 (hd.s56_ME (hd.s56_J_le_M hj)) e).1 he
  rcases s56y_mem_sup_zpowers (A := d.E) hcen hz₁sq hs with h | ⟨e, he, rfl⟩
  · exact hES (hjE s h)
  · have hjz := hd.s56_J_comm_z1_mem_E h49 hz₁ hε hj
    have e1 : j * (z₁ * e) * j⁻¹ = (j * z₁ * j⁻¹ * z₁⁻¹) * z₁ * (j * e * j⁻¹) := by group
    rw [e1]
    exact mul_mem (mul_mem (hES hjz) hz₁S) (hES (hjE e he))

theorem Hyp.s56_J_comm_Q2_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {z₁ : G}
    (hz₁ : z₁ ∈ d.s56Q2) (hε : d.s56Eps z₁ = d.z)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₁ * e)
    {j : G} (hj : j ∈ d.s56J) {q : G} (hq : q ∈ d.s56Q2) :
    j * q * j⁻¹ * q⁻¹ ∈ d.E ⊔ zpowers z₁ := by
  have hxM := hd.s56_x5_mem_M
  have hcen : ∀ e ∈ d.E, z₁ * e = e * z₁ := fun e he => (((s56_mem_Q2_iff).1 hz₁).2 e he).symm
  have hz₁sq := hd.s56_Q2_sq_mem_E_all h49 z₁ hz₁
  set S : Subgroup G := d.E ⊔ zpowers z₁ with hS
  have hES : d.E ≤ S := le_sup_left
  have hz₁S : z₁ ∈ S := mem_sup_right (mem_zpowers _)
  have hSmem : ∀ s ∈ S, s ∈ d.E ∨ ∃ e ∈ d.E, s = z₁ * e := fun s hs =>
    s56y_mem_sup_zpowers (A := d.E) hcen hz₁sq hs
  have hJS : ∀ j ∈ d.s56J, ∀ s ∈ S, j * s * j⁻¹ ∈ S := fun j hj s hs =>
    hd.s56_J_conj_S h49 hz₁ hε hz₁sq hj hs
  let H₂ : Subgroup G :=
    { carrier := {j | j ∈ d.s56J ∧ ∀ q ∈ d.s56Q2, j * q * j⁻¹ * q⁻¹ ∈ S}
      one_mem' := ⟨one_mem _, fun q hq => by simpa using one_mem S⟩
      mul_mem' := by
        rintro j j' ⟨hj, hjS⟩ ⟨hj', hj'S⟩
        refine ⟨mul_mem hj hj', fun q hq => ?_⟩
        have e : j * j' * q * (j * j')⁻¹ * q⁻¹ =
            (j * (j' * q * j'⁻¹ * q⁻¹) * j⁻¹) * (j * q * j⁻¹ * q⁻¹) := by group
        rw [e]
        exact mul_mem (hJS j hj _ (hj'S q hq)) (hjS q hq)
      inv_mem' := by
        rintro j ⟨hj, hjS⟩
        refine ⟨inv_mem hj, fun q hq => ?_⟩
        have e : j⁻¹ * q * j⁻¹⁻¹ * q⁻¹ = j⁻¹ * (j * q * j⁻¹ * q⁻¹)⁻¹ * j⁻¹⁻¹ := by group
        rw [e]
        exact hJS j⁻¹ (inv_mem hj) _ (inv_mem (hjS q hq)) }
  have hEH : d.E ≤ H₂ := fun e he => ⟨s56_E_le_J d he, fun q hq => by
    have h := ((s56_mem_Q2_iff).1 hq).2 e he
    have e1 : e * q * e⁻¹ * q⁻¹ = 1 := by rw [h]; group
    rw [e1]; exact one_mem _⟩
  have hgS : ∀ g ∈ zpowers d.x₅, ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have hgM : g ∈ d.M := (zpowers_le.2 hxM) hg
    have hgE : ∀ e ∈ d.E, g * e * g⁻¹ ∈ d.E := fun e he =>
      (mem_normalizer_iff.1 (hd.s56_ME hgM) e).1 he
    rcases hSmem s hs with h | ⟨e, he, rfl⟩
    · exact hES (hgE s h)
    · have h1 := hd.s56_conj_z1_mem h49 hz₁ hε hg
      have e1 : g * (z₁ * e) * g⁻¹ = z₁ * (z₁⁻¹ * (g * z₁ * g⁻¹)) * (g * e * g⁻¹) := by group
      rw [e1]
      exact mul_mem (mul_mem hz₁S (hES h1)) (hES (hgE e he))
  have hcon : ∀ g ∈ zpowers d.x₅, ∀ j ∈ H₂, g * j * g⁻¹ ∈ H₂ := by
    intro g hg j ⟨hj, hjS⟩
    have hgM : g ∈ d.M := (zpowers_le.2 hxM) hg
    refine ⟨(mem_normalizer_iff.1 ((zpowers_le.2 hd.s56_x5_normalizes_J) hg) j).1 hj,
      fun q hq => ?_⟩
    have hq' : g⁻¹ * q * g⁻¹⁻¹ ∈ d.s56Q2 := hd.s56_Q2_conj_mem (inv_mem hgM) hq
    have h := hjS _ hq'
    have e : g * j * g⁻¹ * q * (g * j * g⁻¹)⁻¹ * q⁻¹ =
        g * (j * (g⁻¹ * q * g⁻¹⁻¹) * j⁻¹ * (g⁻¹ * q * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
    rw [e]
    exact hgS g hg _ h
  have hx : d.x₅ ∈ normalizer (H₂ : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hcon _ (mem_zpowers _) h hh, fun hh => ?_⟩
    have := hcon d.x₅⁻¹ (inv_mem (mem_zpowers _)) _ hh
    simpa [mul_assoc] using this
  have hv : d.pv 7 ∈ H₂ := by
    refine ⟨s56_pv7_mem_J d, fun q hq => ?_⟩
    rcases hdich q hq with h | ⟨e, he, h⟩
    · exact hES h
    · have : d.pv 7 * q * (d.pv 7)⁻¹ * q⁻¹ = d.s56Cm q := rfl
      rw [this, h]
      exact mul_mem hz₁S (hES he)
  have hJ := hd.s56_eq_J_of_mem hEH (fun j hj => hj.1) hx hv
  have : j ∈ H₂ := by rw [hJ]; exact hj
  exact this.2 q hq

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
