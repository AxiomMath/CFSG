module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Irreducible
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.HNSideFacts.F4Extraspecial

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t z : G}

theorem phi2_le (R : Subgroup G) : Phi2 R ≤ R := by
  rw [Phi2]
  refine sup_le ?_ ?_
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)
  · refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨y, hy, rfl⟩
    exact R.pow_mem hy 2

theorem map_Phi2_le {R : Subgroup G} {f : G →* G} (h : R.map f ≤ R) :
    (Phi2 R).map f ≤ Phi2 R := by
  rw [Phi2, Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw [Subgroup.map_commutator]
    exact (Subgroup.commutator_mono (H₁ := R.map f) (H₂ := R.map f) (K₁ := R) (K₂ := R)
      h h).trans le_sup_left
  · rw [MonoidHom.map_closure]
    exact (Subgroup.closure_mono (by
      rintro x ⟨s, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨f y, h (Subgroup.mem_map_of_mem f hy), map_pow f y 2⟩)).trans le_sup_right

structure RExtra (t z : G) : Prop where
  phi_eq : Phi2 (Rg t z) = zpowers z
  extraspecial : CFSG.IsExtraspecial 2 ↥(Rg t z)

theorem rExtra (c : Core3 E t z) : RExtra t z := by
  have hPhi_le_R : Phi2 (Rg t z) ≤ Rg t z := phi2_le (Rg t z)
  have hPhi_le_P : Phi2 (Rg t z) ≤ Pg E z := hPhi_le_R.trans c.rp.R_le_P
  have hInvPhi : InvUnder (CNz E z) (Phi2 (Rg t z)) := by
    intro n hn w hw
    have hRmap : (Rg t z).map (MulAut.conj n : G →* G) ≤ Rg t z := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
      change n * u * n⁻¹ ∈ Rg t z
      exact c.rnorm n hn u hu
    have hmem : (MulAut.conj n : G →* G) w ∈ Phi2 (Rg t z) :=
      map_Phi2_le hRmap (Subgroup.mem_map_of_mem (MulAut.conj n : G →* G) hw)
    change n * w * n⁻¹ ∈ Phi2 (Rg t z)
    exact hmem
  have hInvE : InvUnder (CNz E z) E := by
    intro n hn e he
    exact (mem_normalizer_iff.mp ((CNz_le_Nrm E z) hn) e).mp he
  have hInvS : InvUnder (CNz E z) (Phi2 (Rg t z) ⊔ E) := hInvPhi.sup hInvE
  have hS_le_P : Phi2 (Rg t z) ⊔ E ≤ Pg E z := sup_le hPhi_le_P c.rp.E_le_P
  have hcardS_le : Nat.card ↥(Phi2 (Rg t z) ⊔ E) ≤ 2 ^ 15 := by
    have hB : Phi2 (Rg t z) ≤ normalizer (E : Set G) :=
      hPhi_le_R.trans (c.rp.R_le_P.trans ((Pg_le_CNz E z).trans (CNz_le_Nrm E z)))
    have hprod := card_sup_mul_card_inf_of_le_normalizer (A := E) (B := Phi2 (Rg t z)) hB
    rw [sup_comm, inf_comm] at hprod
    have h1 : Nat.card ↥(Phi2 (Rg t z) ⊔ E) * Nat.card ↥(Phi2 (Rg t z) ⊓ E) ≤ 2 ^ 15 := by
      rw [hprod]
      calc Nat.card ↥E * Nat.card ↥(Phi2 (Rg t z)) ≤ 2 ^ 11 * 16 :=
            Nat.mul_le_mul (le_of_eq c.m24.card_E) c.jr.phi_card
        _ ≤ 2 ^ 15 := by norm_num
    have hge : 0 < Nat.card ↥(Phi2 (Rg t z) ⊓ E) := by
      haveI : Nonempty ↥(Phi2 (Rg t z) ⊓ E) := ⟨1, Subgroup.one_mem _⟩
      exact Nat.card_pos
    exact (Nat.le_mul_of_pos_right _ hge).trans h1
  have hS_ne_P : Phi2 (Rg t z) ⊔ E ≠ Pg E z := by
    intro hSP
    have hcard : Nat.card ↥(Phi2 (Rg t z) ⊔ E) = 2 ^ 17 := by
      rw [hSP, c.cocode.card_P]
    rw [hcard] at hcardS_le
    norm_num at hcardS_le
  have hPhi_le_E : Phi2 (Rg t z) ≤ E := by
    rcases c.cocode.P_irred (Phi2 (Rg t z) ⊔ E) le_sup_right hS_le_P hInvS with h | h
    · exact h ▸ (le_sup_left : Phi2 (Rg t z) ≤ Phi2 (Rg t z) ⊔ E)
    · exact absurd h hS_ne_P
  have hR_nabel : ¬ (∀ x ∈ Rg t z, ∀ y ∈ Rg t z, x * y = y * x) := by
    intro habel
    have hR_le_z : Rg t z ≤ zpowers z :=
      fun x hx => (c.jr.center_R x hx).mp (fun y hy => habel x hx y hy)
    have hcardR_le : Nat.card ↥(Rg t z) ≤ Nat.card ↥(zpowers z) :=
      Subgroup.card_le_of_le hR_le_z
    have hcardz : Nat.card ↥(zpowers z) = 2 := by
      rw [Nat.card_zpowers, orderOf_eq_prime c.klein.z_sq c.klein.z_ne]
    rw [hcardz, c.jr.card_R] at hcardR_le
    norm_num at hcardR_le
  have hPhi_ne_bot : Phi2 (Rg t z) ≠ ⊥ := by
    intro hbot
    apply hR_nabel
    intro x hx y hy
    have hcomm' : ⁅x, y⁆ ∈ Phi2 (Rg t z) :=
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hcomm'
    exact hcomm'
  have hPhi_z : Phi2 (Rg t z) = zpowers z := by
    rcases c.cocode.lattice (Phi2 (Rg t z)) hPhi_le_E hInvPhi with hbot | hz | hcard | hE
    · exact absurd hbot hPhi_ne_bot
    · exact hz
    · exfalso
      have hle := c.jr.phi_card
      rw [hcard] at hle
      norm_num at hle
    · exfalso
      have hcardPhi : Nat.card ↥(Phi2 (Rg t z)) = 2 ^ 11 := by rw [hE, c.m24.card_E]
      have hle := c.jr.phi_card
      rw [hcardPhi] at hle
      norm_num at hle
  have hzR : z ∈ Rg t z := c.jr.V_le_R z_mem_Vtz
  have hzc : ∀ y ∈ Rg t z, z * y = y * z :=
    fun y hy => ((c.jr.center_R z hzR).mpr (Subgroup.mem_zpowers z)) y hy
  have hcomm : ∀ x ∈ Rg t z, ∀ y ∈ Rg t z, x * y * x⁻¹ * y⁻¹ ∈ zpowers z := by
    intro x hx y hy
    rw [← hPhi_z, Phi2]
    simpa only [commutatorElement_def] using
      Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hx hy)
  have hsq : ∀ x ∈ Rg t z, x ^ 2 ∈ zpowers z := by
    intro x hx
    rw [← hPhi_z, Phi2]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨x, hx, rfl⟩)
  have hcentre : ∀ x ∈ Rg t z, (∀ y ∈ Rg t z, x * y = y * x) → x ∈ zpowers z :=
    fun x hx h => (c.jr.center_R x hx).mp h
  have hnc : ∃ x ∈ Rg t z, ∃ y ∈ Rg t z, x * y ≠ y * x := by
    by_contra h
    apply hR_nabel
    intro x hx y hy
    by_contra hxy
    exact h ⟨x, hx, ⟨y, hy, hxy⟩⟩
  have hext : CFSG.IsExtraspecial 2 ↥(Rg t z) :=
    CFSG.EvenSporadicStandard.HNRecog.SideF4.isExtraspecial_two_of_central_involution
      hzR c.klein.z_sq c.klein.z_ne hzc hcomm hsq hcentre hnc
  exact ⟨hPhi_z, hext⟩

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
