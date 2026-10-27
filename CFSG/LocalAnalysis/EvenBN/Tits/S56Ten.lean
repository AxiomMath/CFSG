module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Nine

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped commutatorElement

namespace S56

theorem centralizes_of_comm_mem {G : Type*} [Group G] {P X Zc : Subgroup G} {z₀ : G}
    (hZ : ∀ w ∈ Zc, ∀ g ∈ P ⊔ X, g * w = w * g) (hZc : ∀ a ∈ Zc, ∀ b ∈ Zc, a * b = b * a)
    (hX : ∀ g ∈ X, g * z₀ = z₀ * g) (hPX : ⁅P, X⁆ = P)
    (hxP : ∀ g ∈ X, ∀ p ∈ P, g * p * g⁻¹ ∈ P)
    (hψ : ∀ p ∈ P, p * z₀ * p⁻¹ * z₀⁻¹ ∈ Zc) {p : G} (hp : p ∈ P) : p * z₀ = z₀ * p := by
  obtain ⟨ψ, hψd⟩ : ∃ ψ : G → G, ∀ p, ψ p = p * z₀ * p⁻¹ * z₀⁻¹ := ⟨_, fun _ => rfl⟩
  have hψZ : ∀ p ∈ P, ψ p ∈ Zc := fun p hp => by rw [hψd]; exact hψ p hp
  have hZP : ∀ w ∈ Zc, ∀ p ∈ P, p * w = w * p := fun w hw p hp => hZ w hw p (mem_sup_left hp)
  have hZX : ∀ w ∈ Zc, ∀ g ∈ X, g * w = w * g := fun w hw g hg => hZ w hw g (mem_sup_right hg)
  have hmul : ∀ p ∈ P, ∀ p' ∈ P, ψ (p * p') = ψ p * ψ p' := by
    intro p hp p' hp'
    have h1 : p * ψ p' * p⁻¹ = ψ p' := by
      rw [hZP _ (hψZ p' hp') p hp]; group
    have e : ψ (p * p') = (p * ψ p' * p⁻¹) * ψ p := by
      simp only [hψd]; group
    rw [e, h1]
    exact hZc _ (hψZ p' hp') _ (hψZ p hp)
  have hone : ψ 1 = 1 := by rw [hψd]; group
  have hinv : ∀ p ∈ P, ψ p⁻¹ = (ψ p)⁻¹ := by
    intro p hp
    have h := hmul p hp p⁻¹ (inv_mem hp)
    rw [mul_inv_cancel, hone] at h
    exact eq_inv_of_mul_eq_one_right h.symm
  have hconj : ∀ g ∈ X, ∀ p ∈ P, ψ (g * p * g⁻¹) = ψ p := by
    intro g hg p hp
    have h1 : g⁻¹ * z₀ * g = z₀ := by
      calc g⁻¹ * z₀ * g = g⁻¹ * (z₀ * g) := by group
        _ = g⁻¹ * (g * z₀) := by rw [hX g hg]
        _ = z₀ := by group
    have e : ψ (g * p * g⁻¹) = g * ψ p * g⁻¹ := by
      simp only [hψd]
      calc g * p * g⁻¹ * z₀ * (g * p * g⁻¹)⁻¹ * z₀⁻¹
          = g * (p * (g⁻¹ * z₀ * g) * p⁻¹ * (g⁻¹ * z₀ * g)⁻¹) * g⁻¹ := by group
        _ = g * (p * z₀ * p⁻¹ * z₀⁻¹) * g⁻¹ := by rw [h1]
    rw [e, hZX _ (hψZ p hp) g hg]; group
  have key : ∀ u : G, ψ u = 1 → u * z₀ = z₀ * u := by
    intro u h
    rw [hψd] at h
    calc u * z₀ = (u * z₀ * u⁻¹ * z₀⁻¹) * (z₀ * u) := by group
      _ = z₀ * u := by rw [h, one_mul]
  have hle : ⁅P, X⁆ ≤ P ⊓ centralizer ({z₀} : Set G) := by
    refine Subgroup.commutator_le.2 fun p hp g hg => ?_
    have hu : g * p⁻¹ * g⁻¹ ∈ P := hxP g hg p⁻¹ (inv_mem hp)
    have hc : ⁅p, g⁆ = p * (g * p⁻¹ * g⁻¹) := by
      rw [commutatorElement_def]; group
    have hPm : ⁅p, g⁆ ∈ P := by rw [hc]; exact mul_mem hp hu
    refine mem_inf.2 ⟨hPm, ?_⟩
    have h1 : ψ ⁅p, g⁆ = 1 := by
      rw [hc, hmul p hp _ hu, hconj g hg p⁻¹ (inv_mem hp), hinv p hp, mul_inv_cancel]
    rw [mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    exact (key _ h1).symm
  have hp' : p ∈ ⁅P, X⁆ := by rw [hPX]; exact hp
  exact (mem_centralizer_iff.1 (mem_inf.1 (hle hp')).2 z₀ (Set.mem_singleton _)).symm

theorem conj_mem_centralizer {G : Type*} [Group G] {X : Subgroup G} {n u : G}
    (hn : n ∈ normalizer (X : Set G)) (hu : u ∈ centralizer (X : Set G)) :
    n * u * n⁻¹ ∈ centralizer (X : Set G) := by
  rw [mem_centralizer_iff]
  intro g hg
  have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ X := (mem_normalizer_iff.1 (inv_mem hn) g).1 hg
  have h := mem_centralizer_iff.1 hu _ hg'
  calc g * (n * u * n⁻¹) = n * ((n⁻¹ * g * n⁻¹⁻¹) * u) * n⁻¹ := by group
    _ = n * (u * (n⁻¹ * g * n⁻¹⁻¹)) * n⁻¹ := by rw [h]
    _ = n * u * n⁻¹ * g := by group

end S56

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}



theorem Hyp.s56_M_conj_zpowers (hd : d.Hyp) {g : G} (hg : g ∈ d.M) {w : G}
    (hw : w ∈ zpowers d.z) : g * w * g⁻¹ = w := by
  rw [hd.s56_M_comm_zpowers hg hw]; group

theorem s56_X_comm_of_comm (d : Data G) {z₀ : G} (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅) (g : G)
    (hg : g ∈ zpowers d.x₅) : g * z₀ = z₀ * g := by
  obtain ⟨k, rfl⟩ := hg
  exact (Commute.zpow_left (show Commute d.x₅ z₀ from hxz₀) k).eq

theorem Hyp.s56_J_comm_z0_mem (hd : d.Hyp) {z₀ : G} (hz₀ : z₀ ∈ d.s56Q2)
    (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅) (hvz₀ : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z)
    {j : G} (hj : j ∈ d.s56J) : j * z₀ * j⁻¹ * z₀⁻¹ ∈ zpowers d.z := by
  have hxM := hd.s56_x5_mem_M
  have hcen : ∀ e ∈ d.E, z₀ * e = e * z₀ := fun e he => (((s56_mem_Q2_iff).1 hz₀).2 e he).symm
  let H₃ : Subgroup G :=
    { carrier := {j | j ∈ d.s56J ∧ j * z₀ * j⁻¹ * z₀⁻¹ ∈ zpowers d.z}
      one_mem' := ⟨one_mem _, by simpa using one_mem (zpowers d.z)⟩
      mul_mem' := by
        rintro j j' ⟨hj, hjz⟩ ⟨hj', hj'z⟩
        refine ⟨mul_mem hj hj', ?_⟩
        have e : j * j' * z₀ * (j * j')⁻¹ * z₀⁻¹ =
            (j * (j' * z₀ * j'⁻¹ * z₀⁻¹) * j⁻¹) * (j * z₀ * j⁻¹ * z₀⁻¹) := by group
        rw [e, hd.s56_M_conj_zpowers (hd.s56_J_le_M hj) hj'z]
        exact mul_mem hj'z hjz
      inv_mem' := by
        rintro j ⟨hj, hjz⟩
        refine ⟨inv_mem hj, ?_⟩
        have e : j⁻¹ * z₀ * j⁻¹⁻¹ * z₀⁻¹ = j⁻¹ * (j * z₀ * j⁻¹ * z₀⁻¹)⁻¹ * j⁻¹⁻¹ := by group
        rw [e, hd.s56_M_conj_zpowers (hd.s56_J_le_M (inv_mem hj)) (inv_mem hjz)]
        exact inv_mem hjz }
  have hEH : d.E ≤ H₃ := fun e he => ⟨s56_E_le_J d he, by
    have h := hcen e he
    have e1 : e * z₀ * e⁻¹ * z₀⁻¹ = 1 := by rw [← h]; group
    rw [e1]; exact one_mem _⟩
  have hgz := s56_X_comm_of_comm d hxz₀
  have hcon : ∀ g ∈ zpowers d.x₅, ∀ j ∈ H₃, g * j * g⁻¹ ∈ H₃ := by
    intro g hg j ⟨hj, hjz⟩
    have hgM : g ∈ d.M := (zpowers_le.2 hxM) hg
    refine ⟨(mem_normalizer_iff.1 ((zpowers_le.2 hd.s56_x5_normalizes_J) hg) j).1 hj, ?_⟩
    have h1 : g⁻¹ * z₀ * g = z₀ := by
      calc g⁻¹ * z₀ * g = g⁻¹ * (z₀ * g) := by group
        _ = g⁻¹ * (g * z₀) := by rw [hgz g hg]
        _ = z₀ := by group
    have e : g * j * g⁻¹ * z₀ * (g * j * g⁻¹)⁻¹ * z₀⁻¹ =
        g * (j * z₀ * j⁻¹ * z₀⁻¹) * g⁻¹ := by
      calc g * j * g⁻¹ * z₀ * (g * j * g⁻¹)⁻¹ * z₀⁻¹
          = g * (j * (g⁻¹ * z₀ * g) * j⁻¹ * (g⁻¹ * z₀ * g)⁻¹) * g⁻¹ := by group
        _ = g * (j * z₀ * j⁻¹ * z₀⁻¹) * g⁻¹ := by rw [h1]
    show (g * j * g⁻¹) * z₀ * (g * j * g⁻¹)⁻¹ * z₀⁻¹ ∈ zpowers d.z
    rw [e, hd.s56_M_conj_zpowers hgM hjz]
    exact hjz
  have hx : d.x₅ ∈ normalizer (H₃ : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hcon _ (mem_zpowers _) h hh, fun hh => ?_⟩
    have := hcon d.x₅⁻¹ (inv_mem (mem_zpowers _)) _ hh
    simpa [mul_assoc] using this
  have hv : d.pv 7 ∈ H₃ := ⟨s56_pv7_mem_J d, hvz₀⟩
  have hJ := hd.s56_eq_J_of_mem hEH (fun j hj => hj.1) hx hv
  have : j ∈ H₃ := by rw [hJ]; exact hj
  exact this.2

theorem Hyp.s56_J_comm_z0 (hd : d.Hyp) {z₀ : G} (hz₀ : z₀ ∈ d.s56Q2)
    (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅) (hvz₀ : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z)
    {j : G} (hj : j ∈ d.s56J) : j * z₀ = z₀ * j :=
  S56.centralizes_of_comm_mem (P := d.s56J) (X := zpowers d.x₅) (Zc := zpowers d.z)
    (fun w hw g hg => hd.s56_M_comm_zpowers (sup_le hd.s56_J_le_M hd.s56_X_le_M hg) hw)
    (fun a ha b hb => hd.s56_zpowers_comm ha hb) (s56_X_comm_of_comm d hxz₀)
    hd.s56_J_eq_comm
    (fun g hg p hp => (mem_normalizer_iff.1 ((zpowers_le.2 hd.s56_x5_normalizes_J) hg) p).1 hp)
    (fun p hp => hd.s56_J_comm_z0_mem hz₀ hxz₀ hvz₀ hp) hj

theorem Hyp.s56_E_inf_centralizer_J (hd : d.Hyp) :
    d.E ⊓ centralizer (d.s56J : Set G) = zpowers d.z := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxM := hd.s56_x5_mem_M
  have hKE : d.E ⊓ centralizer (d.s56J : Set G) ≤ d.E := inf_le_left
  have hzK : zpowers d.z ≤ d.E ⊓ centralizer (d.s56J : Set G) := by
    refine zpowers_le.2 (mem_inf.2 ⟨hd.s56_z_mem_E, ?_⟩)
    rw [mem_centralizer_iff]
    intro j hj
    exact hd.s56_M_comm_zpowers (hd.s56_J_le_M hj) (mem_zpowers _)
  have hcon : ∀ g ∈ zpowers d.x₅, ∀ k ∈ d.E ⊓ centralizer (d.s56J : Set G),
      g * k * g⁻¹ ∈ d.E ⊓ centralizer (d.s56J : Set G) := by
    intro g hg k hk
    obtain ⟨hkE, hkC⟩ := mem_inf.1 hk
    have hgM : g ∈ d.M := (zpowers_le.2 hxM) hg
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 (hd.s56_ME hgM) k).1 hkE, ?_⟩
    rw [mem_centralizer_iff]
    intro j hj
    have hj' : g⁻¹ * j * g⁻¹⁻¹ ∈ d.s56J :=
      (mem_normalizer_iff.1 ((zpowers_le.2 hd.s56_x5_normalizes_J) (inv_mem hg)) j).1 hj
    have h := mem_centralizer_iff.1 hkC _ hj'
    calc j * (g * k * g⁻¹) = g * ((g⁻¹ * j * g⁻¹⁻¹) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * j * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
      _ = g * k * g⁻¹ * j := by group
  have hx : d.x₅ ∈ normalizer ((d.E ⊓ centralizer (d.s56J : Set G) : Subgroup G) : Set G) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hcon _ (mem_zpowers _) h hh, fun hh => ?_⟩
    have := hcon d.x₅⁻¹ (inv_mem (mem_zpowers _)) _ hh
    simpa [mul_assoc] using this
  have hxz : d.x₅ ∈ normalizer ((zpowers d.z : Subgroup G) : Set G) := by
    apply Subgroup.centralizer_le_normalizer ((zpowers d.z : Subgroup G) : Set G)
    rw [mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := hw
    exact (Commute.zpow_left (show Commute d.z d.x₅ from hd.s56_x5_comm_z.symm) k).eq
  have hmod := S56.card_modEq_of_centralizer_le hd.s56_orderOf_x5 hzK hKE hxz hx
    (fun c hc hcx => hd.s56_E_cent_x5 hc hcx.symm)
  have hzcard : Nat.card (zpowers d.z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact hd.s56_z_sq) hd.s56_z_ne_one
  have hdvd : Nat.card ((d.E ⊓ centralizer (d.s56J : Set G) : Subgroup G)) ∣ 2 ^ 5 := by
    have := Subgroup.card_dvd_of_le hKE
    rw [hd.A_facts.1] at this
    simpa using this
  obtain ⟨k, hk5, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hk, hzcard] at hmod
  have hk' : k = 1 ∨ k = 5 := by
    interval_cases k <;> first | (left; rfl) | (right; rfl) | (exfalso; revert hmod; decide)
  rcases hk' with rfl | rfl
  · exact (Subgroup.eq_of_le_of_card_ge hzK (by rw [hk, hzcard]; norm_num)).symm
  · exfalso
    have hEK : d.E = d.E ⊓ centralizer (d.s56J : Set G) :=
      (Subgroup.eq_of_le_of_card_ge hKE (by rw [hk, hd.A_facts.1]; norm_num)).symm
    have hv7E : ∀ e ∈ d.E, d.pv 7 * e = e * d.pv 7 := fun e he => by
      have h : e ∈ d.E ⊓ centralizer (d.s56J : Set G) := by rw [← hEK]; exact he
      exact mem_centralizer_iff.1 (mem_inf.1 h).2 _ (s56_pv7_mem_J d)
    have hc := hv7E _ (s56_pv8_mem_E d)
    have h1 := s56_pv7_conj_pv8 d
    rw [hc, mul_assoc, mul_inv_cancel, mul_one] at h1
    exact hd.s56_z_ne_one (mul_eq_left.1 h1.symm)

theorem Hyp.s56_Q2_comm_z0_mem (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz₀ : z₀ ∈ d.s56Q2) (hε : d.s56Eps z₀ = d.z) (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅)
    (hvz₀ : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e)
    {w : G} (hw : w ∈ d.s56Q2) : w * z₀ * w⁻¹ * z₀⁻¹ ∈ zpowers d.z := by
  have hcen : ∀ e ∈ d.E, z₀ * e = e * z₀ := fun e he => (((s56_mem_Q2_iff).1 hz₀).2 e he).symm
  have hz₀sq := hd.s56_Q2_sq_mem_E_all h49 z₀ hz₀
  have hψE : w * z₀ * w⁻¹ * z₀⁻¹ ∈ d.E := hd.s56_Q2_comm_mem_E h49 hw hz₀
  have hmem : w * z₀ * w⁻¹ * z₀⁻¹ ∈ d.E ⊓ centralizer (d.s56J : Set G) := by
    refine mem_inf.2 ⟨hψE, ?_⟩
    rw [mem_centralizer_iff]
    intro j hj
    have hjz := hd.s56_J_comm_z0 hz₀ hxz₀ hvz₀ hj
    have hjz' : j * z₀⁻¹ = z₀⁻¹ * j := by
      calc j * z₀⁻¹ = z₀⁻¹ * (z₀ * j) * z₀⁻¹ := by group
        _ = z₀⁻¹ * (j * z₀) * z₀⁻¹ := by rw [hjz]
        _ = z₀⁻¹ * j := by group
    obtain ⟨s, hsdef⟩ : ∃ s, s = j⁻¹ * w⁻¹ * j⁻¹⁻¹ * w⁻¹⁻¹ := ⟨_, rfl⟩
    have hs : s ∈ d.E ⊔ zpowers z₀ := by
      rw [hsdef]; exact hd.s56_J_comm_Q2_mem h49 hz₀ hε hdich (inv_mem hj) (inv_mem hw)
    have hsz : s * z₀ = z₀ * s := by
      rcases s56y_mem_sup_zpowers (A := d.E) hcen hz₀sq hs with h | ⟨e, he, h⟩
      · exact (hcen s h).symm
      · rw [h]
        calc z₀ * e * z₀ = z₀ * (e * z₀) := by group
          _ = z₀ * (z₀ * e) := by rw [hcen e he]
    have hwjw : w⁻¹ * j * w = j * s := by rw [hsdef]; group
    have h1 : (w⁻¹ * j * w) * z₀ = z₀ * (w⁻¹ * j * w) := by
      rw [hwjw]
      calc j * s * z₀ = j * (s * z₀) := by group
        _ = j * (z₀ * s) := by rw [hsz]
        _ = (j * z₀) * s := by group
        _ = (z₀ * j) * s := by rw [hjz]
        _ = z₀ * (j * s) := by group
    have hc1 : j * (w * z₀ * w⁻¹) = (w * z₀ * w⁻¹) * j := by
      calc j * (w * z₀ * w⁻¹) = w * ((w⁻¹ * j * w) * z₀) * w⁻¹ := by group
        _ = w * (z₀ * (w⁻¹ * j * w)) * w⁻¹ := by rw [h1]
        _ = (w * z₀ * w⁻¹) * j := by group
    calc j * (w * z₀ * w⁻¹ * z₀⁻¹) = (j * (w * z₀ * w⁻¹)) * z₀⁻¹ := by group
      _ = ((w * z₀ * w⁻¹) * j) * z₀⁻¹ := by rw [hc1]
      _ = (w * z₀ * w⁻¹) * (j * z₀⁻¹) := by group
      _ = (w * z₀ * w⁻¹) * (z₀⁻¹ * j) := by rw [hjz']
      _ = (w * z₀ * w⁻¹ * z₀⁻¹) * j := by group
  rwa [hd.s56_E_inf_centralizer_J] at hmem

theorem Hyp.s56_Q_comm_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz₀ : z₀ ∈ d.s56Q2) (hε : d.s56Eps z₀ = d.z) (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅)
    (hvz₀ : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e)
    {q : G} (hq : q ∈ d.s56Q) : q * z₀ = z₀ * q := by
  have hQM : d.s56Q ≤ d.M := hd.s56_Q_le_Q0.trans (hd.s56_Q0_le_M h49)
  refine S56.centralizes_of_comm_mem (P := d.s56Q) (X := zpowers d.x₅) (Zc := zpowers d.z)
    (fun w hw g hg => hd.s56_M_comm_zpowers (sup_le hQM hd.s56_X_le_M hg) hw)
    (fun a ha b hb => hd.s56_zpowers_comm ha hb) (s56_X_comm_of_comm d hxz₀)
    hd.s56_Q_comm_X (fun g hg p hp => ?_) (fun p hp => ?_) hq
  · exact (mem_normalizer_iff.1 (hd.s56_M_le_normalizer_Q h49 (hd.s56_X_le_M hg)) p).1 hp
  · obtain ⟨j, hj, w, hw, rfl⟩ := hd.s56_Q0_eq_J_mul_Q2 h49 (hd.s56_Q_le_Q0 hp)
    have hjz := hd.s56_J_comm_z0 hz₀ hxz₀ hvz₀ hj
    have hwz := hd.s56_Q2_comm_z0_mem h49 hz₀ hε hxz₀ hvz₀ hdich hw
    have e : j * w * z₀ * (j * w)⁻¹ * z₀⁻¹ =
        (j * (w * z₀ * w⁻¹ * z₀⁻¹) * j⁻¹) * (j * z₀ * j⁻¹ * z₀⁻¹) := by group
    have h1 : j * z₀ * j⁻¹ * z₀⁻¹ = 1 := by rw [hjz]; group
    rw [e, h1, mul_one, hd.s56_M_conj_zpowers (hd.s56_J_le_M hj) hwz]
    exact hwz

theorem Hyp.s56_M_le_normalizer_Z (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz₀Q : z₀ ∈ d.s56Q) (hz₀Q2 : z₀ ∈ d.s56Q2) (hε : d.s56Eps z₀ = d.z)
    (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅) (hvz₀ : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e) :
    d.M ≤ normalizer ((zpowers d.z ⊔ zpowers z₀ : Subgroup G) : Set G) := by
  have hZ := hd.s56_CQX_eq h49 hz₀Q hz₀Q2 hε hxz₀ hdich
  have hQZ : ∀ c ∈ d.s56Q, ∀ u ∈ zpowers d.z ⊔ zpowers z₀, c * u * c⁻¹ = u := by
    intro c hc u hu
    have hcM : c ∈ d.M := (hd.s56_Q_le_Q0.trans (hd.s56_Q0_le_M h49)) hc
    have hzc : d.z ∈ centralizer ({c} : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hd.s56_M_comm_zpowers hcM (mem_zpowers _)
    have hz₀c : z₀ ∈ centralizer ({c} : Set G) := by
      rw [mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact hd.s56_Q_comm_z0 h49 hz₀Q2 hε hxz₀ hvz₀ hdich hc
    have hZc : zpowers d.z ⊔ zpowers z₀ ≤ centralizer ({c} : Set G) :=
      sup_le (zpowers_le.2 hzc) (zpowers_le.2 hz₀c)
    have h := mem_centralizer_iff.1 (hZc hu) c (Set.mem_singleton _)
    rw [h]; group
  have hnZ : ∀ n ∈ d.M, n ∈ normalizer ((zpowers d.x₅ : Subgroup G) : Set G) →
      ∀ u ∈ zpowers d.z ⊔ zpowers z₀, n * u * n⁻¹ ∈ zpowers d.z ⊔ zpowers z₀ := by
    intro n hn hnX u hu
    rw [← hZ] at hu ⊢
    obtain ⟨huQ, huX⟩ := mem_inf.1 hu
    exact mem_inf.2 ⟨(mem_normalizer_iff.1 (hd.s56_M_le_normalizer_Q h49 hn) u).1 huQ,
      S56.conj_mem_centralizer hnX huX⟩
  have hM : ∀ m ∈ d.M, ∀ u ∈ zpowers d.z ⊔ zpowers z₀,
      m * u * m⁻¹ ∈ zpowers d.z ⊔ zpowers z₀ := by
    intro m hm u hu
    obtain ⟨hQ0, hN⟩ := (⟨hd.s56_Q0_le_M h49, s56_M_le_normalizer_Q0 d⟩ :
      d.s56Q0 ≤ d.M ∧ d.M ≤ normalizer (d.s56Q0 : Set G))
    obtain ⟨-, -, -, -, -, h20, -⟩ := hd.s56_structure_M h49
    obtain ⟨q, hq, n, hnM, hnX, rfl⟩ := S56.exists_mul_normalizer_of_index_twenty hQ0 hN
      (s56_Q0_isPGroup d) hd.s56_x5_mem_M hd.s56_orderOf_x5 h20 hm
    obtain ⟨c, hc, k, hk, rfl⟩ := hd.s56_Q0_decomp hq
    obtain ⟨hkQ0, hkX⟩ := mem_inf.1 hk
    have hkM : k ∈ d.M := hQ0 hkQ0
    have hkN : k ∈ normalizer ((zpowers d.x₅ : Subgroup G) : Set G) :=
      Subgroup.centralizer_le_normalizer ((zpowers d.x₅ : Subgroup G) : Set G) hkX
    have hmem := hnZ (k * n) (mul_mem hkM hnM) (mul_mem hkN hnX) u hu
    have e : c * k * n * u * (c * k * n)⁻¹ = c * ((k * n) * u * (k * n)⁻¹) * c⁻¹ := by group
    rw [e, hQZ c hc _ hmem]
    exact hmem
  intro m hm
  rw [mem_normalizer_iff]
  intro s
  refine ⟨fun hs => hM m hm s hs, fun hs => ?_⟩
  have := hM m⁻¹ (inv_mem hm) _ hs
  simpa [mul_assoc] using this

theorem Hyp.s56_exists_z0_full (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∃ z₀ : G, z₀ ∈ d.s56Q ∧ z₀ ∈ d.s56Q2 ∧ d.s56Eps z₀ = d.z ∧ d.x₅ * z₀ = z₀ * d.x₅ ∧
      z₀ * z₀ ∈ zpowers d.z ∧ d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z ∧
      (∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e) ∧
      (∀ q ∈ d.s56Q, q * z₀ = z₀ * q) ∧
      d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) = zpowers d.z ⊔ zpowers z₀ ∧
      d.M ≤ normalizer ((zpowers d.z ⊔ zpowers z₀ : Subgroup G) : Set G) ∧
      d.M ≤ normalizer ((d.E ⊔ zpowers z₀ : Subgroup G) : Set G) := by
  obtain ⟨z₀, hQ, hQ2, hε, hxz, hsq, hvz, hdich⟩ := hd.s56_exists_z0 h49
  exact ⟨z₀, hQ, hQ2, hε, hxz, hsq, hvz, hdich,
    fun q hq => hd.s56_Q_comm_z0 h49 hQ2 hε hxz hvz hdich hq,
    hd.s56_CQX_eq h49 hQ hQ2 hε hxz hdich,
    hd.s56_M_le_normalizer_Z h49 hQ hQ2 hε hxz hvz hdich,
    hd.s56_M_le_normalizer_S h49 hQ hQ2 hε hxz hdich⟩

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
