module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Eight
public import CFSG.LocalAnalysis.EvenBN.Tits.S56Fix

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_exists_z0 (h49 : d.Thm49Statement) (hd : d.Hyp) :
    ∃ z₀ : G, z₀ ∈ d.s56Q ∧ z₀ ∈ d.s56Q2 ∧ d.s56Eps z₀ = d.z ∧ d.x₅ * z₀ = z₀ * d.x₅ ∧
      z₀ * z₀ ∈ zpowers d.z ∧ d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ ∈ zpowers d.z ∧
      ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e := by
  obtain ⟨z₁, hz₁Q2, hz₁Q, hεz, hvz₁, hdich⟩ := hd.s56_exists_z1 h49
  have hxM := hd.s56_x5_mem_M
  have hcard5 : ¬ 5 ∣ Nat.card d.E := by rw [hd.A_facts.1]; norm_num
  have hz₁x := hd.s56_conj_z1_mem h49 hz₁Q2 hεz (mem_zpowers d.x₅)
  obtain ⟨e₀, he₀, hfix⟩ := S56.exists_fixed_point_of_conj_stable_coset hd.s56_orderOf_x5
    (hd.s56_ME hxM) hz₁x hcard5
  have hEQ := hd.s56_E_le_Q h49
  have hE2 := hd.s56_E_le_Q2
  have hcen : ∀ e ∈ d.E, z₁ * e = e * z₁ := fun e he =>
    (((s56_mem_Q2_iff).1 hz₁Q2).2 e he).symm
  set z₀ := z₁ * e₀ with hz₀
  have hz₀Q2 : z₀ ∈ d.s56Q2 := mul_mem hz₁Q2 (hE2 he₀)
  have hxz₀ : d.x₅ * z₀ = z₀ * d.x₅ := by
    have : d.x₅ * z₀ * d.x₅⁻¹ = z₀ := hfix
    calc d.x₅ * z₀ = d.x₅ * z₀ * d.x₅⁻¹ * d.x₅ := by group
      _ = z₀ * d.x₅ := by rw [this]
  have hz₀sq : z₀ * z₀ ∈ zpowers d.z := by
    have hE : z₀ * z₀ ∈ d.E := hd.s56_Q2_sq_mem_E_all h49 z₀ hz₀Q2
    refine hd.s56_E_cent_x5 hE ?_
    calc z₀ * z₀ * d.x₅ = z₀ * (z₀ * d.x₅) := by group
      _ = z₀ * (d.x₅ * z₀) := by rw [hxz₀]
      _ = d.x₅ * (z₀ * z₀) := by rw [← mul_assoc, ← hxz₀]; group
      _ = d.x₅ * (z₀ * z₀) := rfl
  refine ⟨z₀, mul_mem hz₁Q (hEQ he₀), hz₀Q2, ?_, hxz₀, hz₀sq, ?_, ?_⟩
  · rw [hz₀, hd.s56_eps_mul_Q2' hz₁Q2 (hE2 he₀), hεz,
      hd.s56_eps_of_comm (hd.L_comm_t (s56_E_le_L d he₀)), mul_one]
  ·
    have hw₀ := hd.s56_pv7_conj_E he₀
    set w₀ := d.pv 7 * e₀ * (d.pv 7)⁻¹ * e₀⁻¹ with hw₀def
    have hw₀E : w₀ ∈ d.E := hd.s56_zpowers_le_E hw₀
    have hee := hd.s56_E_sq he₀
    have e1 : d.pv 7 * z₀ * (d.pv 7)⁻¹ * z₀⁻¹ = w₀ * (z₀ * z₀)⁻¹ := by
      have h1 : d.pv 7 * (z₁ * e₀) * (d.pv 7)⁻¹ * (z₁ * e₀)⁻¹ =
          (d.pv 7 * z₁ * (d.pv 7)⁻¹) * w₀ * z₁⁻¹ := by rw [hw₀def]; group
      have h2 : z₀ * z₀ = z₁ * z₁ := by
        rw [hz₀]
        calc z₁ * e₀ * (z₁ * e₀) = z₁ * (e₀ * z₁) * e₀ := by group
          _ = z₁ * (z₁ * e₀) * e₀ := by rw [← hcen e₀ he₀]
          _ = z₁ * z₁ * (e₀ * e₀) := by group
          _ = z₁ * z₁ := by rw [hee, mul_one]
      rw [hz₀, h1, hvz₁, ← hz₀, h2]
      have h3 : z₁⁻¹ * w₀ = w₀ * z₁⁻¹ := by
        have := hcen w₀ hw₀E
        calc z₁⁻¹ * w₀ = z₁⁻¹ * w₀ * z₁ * z₁⁻¹ := by group
          _ = z₁⁻¹ * (z₁ * w₀) * z₁⁻¹ := by rw [this]; group
          _ = w₀ * z₁⁻¹ := by group
      calc z₁⁻¹ * w₀ * z₁⁻¹ = w₀ * z₁⁻¹ * z₁⁻¹ := by rw [h3]
        _ = w₀ * (z₁ * z₁)⁻¹ := by group
    rw [e1]
    exact mul_mem hw₀ (inv_mem hz₀sq)
  · intro q hq
    rcases hdich q hq with h | ⟨e, he, h⟩
    · exact Or.inl h
    · right
      refine ⟨e₀⁻¹ * e, mul_mem (inv_mem he₀) he, ?_⟩
      rw [h, hz₀]; group

theorem Hyp.s56_CQX_eq (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G} (hz₀Q : z₀ ∈ d.s56Q)
    (hz₀Q2 : z₀ ∈ d.s56Q2) (hε : d.s56Eps z₀ = d.z) (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e) :
    d.s56Q ⊓ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) = zpowers d.z ⊔ zpowers z₀ := by
  have hcen : ∀ e ∈ d.E, z₀ * e = e * z₀ := fun e he =>
    (((s56_mem_Q2_iff).1 hz₀Q2).2 e he).symm
  have hz₀sq := hd.s56_Q2_sq_mem_E_all h49 z₀ hz₀Q2
  have hEQ := hd.s56_E_le_Q h49
  apply le_antisymm
  · intro w hw
    obtain ⟨hwQ, hwX⟩ := mem_inf.1 hw
    have hwx : d.x₅ * w = w * d.x₅ := mem_centralizer_iff.1 hwX d.x₅ (mem_zpowers _)
    have hwS := hd.s56_CQX_le_S h49 hz₀Q2 hε hdich hw
    rcases s56y_mem_sup_zpowers (A := d.E) hcen hz₀sq hwS with h | ⟨e, he, rfl⟩
    · exact mem_sup_left (hd.s56_E_cent_x5 h hwx.symm)
    · have hex : e * d.x₅ = d.x₅ * e := by
        have h1 : z₀ * (d.x₅ * e) = z₀ * (e * d.x₅) := by
          calc z₀ * (d.x₅ * e) = (z₀ * d.x₅) * e := by group
            _ = (d.x₅ * z₀) * e := by rw [hxz₀]
            _ = d.x₅ * (z₀ * e) := by group
            _ = z₀ * e * d.x₅ := hwx
            _ = z₀ * (e * d.x₅) := by group
        exact (mul_left_cancel h1).symm
      have he' := hd.s56_E_cent_x5 he hex
      exact mul_mem (mem_sup_right (mem_zpowers _)) (mem_sup_left he')
  · refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
    · refine mem_inf.2 ⟨hEQ hd.s56_z_mem_E, ?_⟩
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := hg
      exact (Commute.zpow_left (show Commute d.x₅ d.z from hd.s56_x5_comm_z) k).eq
    · refine mem_inf.2 ⟨hz₀Q, ?_⟩
      rw [mem_centralizer_iff]
      intro g hg
      obtain ⟨k, rfl⟩ := hg
      exact (Commute.zpow_left (show Commute d.x₅ z₀ from hxz₀) k).eq

theorem Hyp.s56_M_le_normalizer_S (h49 : d.Thm49Statement) (hd : d.Hyp) {z₀ : G}
    (hz₀Q : z₀ ∈ d.s56Q) (hz₀Q2 : z₀ ∈ d.s56Q2) (hε : d.s56Eps z₀ = d.z)
    (hxz₀ : d.x₅ * z₀ = z₀ * d.x₅)
    (hdich : ∀ q ∈ d.s56Q2, d.s56Cm q ∈ d.E ∨ ∃ e ∈ d.E, d.s56Cm q = z₀ * e) :
    d.M ≤ normalizer ((d.E ⊔ zpowers z₀ : Subgroup G) : Set G) := by
  have hcen : ∀ e ∈ d.E, z₀ * e = e * z₀ := fun e he =>
    (((s56_mem_Q2_iff).1 hz₀Q2).2 e he).symm
  have hz₀sq := hd.s56_Q2_sq_mem_E_all h49 z₀ hz₀Q2
  have hEQ := hd.s56_E_le_Q h49
  set S : Subgroup G := d.E ⊔ zpowers z₀ with hS
  have hES : d.E ≤ S := le_sup_left
  have hz₀S : z₀ ∈ S := mem_sup_right (mem_zpowers _)
  have hSmem : ∀ s ∈ S, s ∈ d.E ∨ ∃ e ∈ d.E, s = z₀ * e := fun s hs =>
    s56y_mem_sup_zpowers (A := d.E) hcen hz₀sq hs
  have hSQ : S ≤ d.s56Q := sup_le hEQ (zpowers_le.2 hz₀Q)
  have hSS := hd.s56_Q_comm_le_S h49 hz₀Q2 hε hdich
  have hQS : ∀ c ∈ d.s56Q, ∀ s ∈ S, c * s * c⁻¹ ∈ S := by
    intro c hc s hs
    have h := hSS (Subgroup.commutator_mem_commutator hc (hSQ hs))
    rw [commutatorElement_def] at h
    have e : c * s * c⁻¹ = (c * s * c⁻¹ * s⁻¹) * s := by group
    rw [e]
    exact mul_mem h hs
  have hNS : ∀ n ∈ d.M, n ∈ normalizer ((zpowers d.x₅ : Subgroup G) : Set G) →
      ∀ s ∈ S, n * s * n⁻¹ ∈ S := by
    intro n hnM hnX s hs
    have hnE : ∀ e ∈ d.E, n * e * n⁻¹ ∈ d.E := fun e he =>
      (mem_normalizer_iff.1 (hd.s56_ME hnM) e).1 he
    have hz₀n : n * z₀ * n⁻¹ ∈ S := by
      have hQn : n * z₀ * n⁻¹ ∈ d.s56Q :=
        (mem_normalizer_iff.1 (hd.s56_M_le_normalizer_Q h49 hnM) z₀).1 hz₀Q
      have hX : n * z₀ * n⁻¹ ∈ centralizer ((zpowers d.x₅ : Subgroup G) : Set G) := by
        rw [mem_centralizer_iff]
        intro g hg
        have hg' : n⁻¹ * g * n⁻¹⁻¹ ∈ zpowers d.x₅ :=
          (mem_normalizer_iff.1 (inv_mem hnX) g).1 hg
        obtain ⟨k, hk⟩ := hg'
        have hz₀g : z₀ * (n⁻¹ * g * n⁻¹⁻¹) = (n⁻¹ * g * n⁻¹⁻¹) * z₀ := by
          rw [← hk]
          exact (Commute.zpow_right (show Commute z₀ d.x₅ from hxz₀.symm) k).eq
        calc g * (n * z₀ * n⁻¹) = n * ((n⁻¹ * g * n⁻¹⁻¹) * z₀) * n⁻¹ := by group
          _ = n * (z₀ * (n⁻¹ * g * n⁻¹⁻¹)) * n⁻¹ := by rw [hz₀g]
          _ = (n * z₀ * n⁻¹) * g := by group
      exact hd.s56_CQX_le_S h49 hz₀Q2 hε hdich (mem_inf.2 ⟨hQn, hX⟩)
    rcases hSmem s hs with h | ⟨e, he, rfl⟩
    · exact hES (hnE s h)
    · have e1 : n * (z₀ * e) * n⁻¹ = (n * z₀ * n⁻¹) * (n * e * n⁻¹) := by group
      rw [e1]
      exact mul_mem hz₀n (hES (hnE e he))
  have hM : ∀ m ∈ d.M, ∀ s ∈ S, m * s * m⁻¹ ∈ S := by
    intro m hm s hs
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
    have e : c * k * n * s * (c * k * n)⁻¹ = c * ((k * n) * s * (k * n)⁻¹) * c⁻¹ := by group
    rw [e]
    exact hQS c hc _ (hNS (k * n) (mul_mem hkM hnM) (mul_mem hkN hnX) s hs)
  intro m hm
  rw [mem_normalizer_iff]
  intro s
  refine ⟨fun hs => hM m hm s hs, fun hs => ?_⟩
  have := hM m⁻¹ (inv_mem hm) _ hs
  simpa [mul_assoc] using this

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
