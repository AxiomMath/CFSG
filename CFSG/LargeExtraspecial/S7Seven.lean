module

public import CFSG.LargeExtraspecial.S7Sigma
public import CFSG.LargeExtraspecial.S5Five
public import CFSG.LargeExtraspecial.S7Four

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S7

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions Equiv
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6 CFSG.Open

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G}

variable (S) in
@[expose] noncomputable def Obar : Subgroup S.O := (timmesfeldOddCore S.Mbar).map S.Mbar.subtype

variable (S) in
@[expose] noncomputable def Cbar (t : S.O) : Subgroup S.O :=
  S.Mbar ⊓ centralizer ((Obar S ⊔ zpowers t : Subgroup S.O) : Set S.O)

theorem Obar_le_Mbar : Obar S ≤ S.Mbar := map_subtype_le _

theorem conj_mem_Obar {x y : S.O} (hx : x ∈ S.Mbar) (hy : y ∈ Obar S) :
    x * y * x⁻¹ ∈ Obar S := by
  obtain ⟨y', hy', rfl⟩ := hy
  exact ⟨⟨x, hx⟩ * y' * ⟨x, hx⟩⁻¹,
    (S5.timmesfeldOddCore_normal S.Mbar).conj_mem y' hy' ⟨x, hx⟩, rfl⟩

theorem card_Obar : Nat.card (Obar S) = Nat.card (timmesfeldOddCore S.Mbar) :=
  card_map_of_injective S.Mbar.subtype_injective

theorem Cbar_le_Mbar {t : S.O} : Cbar S t ≤ S.Mbar := inf_le_left

theorem comm_of_mem_Cbar {t c : S.O} (hc : c ∈ Cbar S t) : c * t = t * c :=
  (mem_centralizer_iff.mp hc.2 t (mem_sup_right (mem_zpowers t))).symm

theorem exists_conj_ne (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) :
    ∃ x ∈ S.Mbar, x * t * x⁻¹ ≠ t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  have hP := Setting.s12_noNormalTwo_Mbar S (zpowers t) (zpowers_le.mpr (S.Lbar_le_Mbar g ht))
    (IsPGroup.of_card (n := 1) (by rw [card_zpowers_eq_two H ht ht1, pow_one]))
    (fun m hm => S4.mem_normalizer_of_conj_le fun p hp => by
      rcases (mem_zpowers_iff_of_mem_Lbar H ht).mp hp with hp1 | hp1
      · rw [hp1, mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [hp1, hcon m hm]
        exact mem_zpowers t)
  apply ht1
  have : t ∈ zpowers t := mem_zpowers t
  rwa [hP, mem_bot] at this

theorem apply_mem_orbit_of_comm (H : Hyp4 S g) {t : S.O} (ht : t ∈ S.Lbar g)
    (hD : DtEqConj S g t) {x : S.O} (hx : x ∈ S.Mbar) (hxt : x * t = t * x) {v : S.Qt}
    (hv : v ∈ orbit S g t) : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ orbit S g t := by
  obtain ⟨κ, rfl⟩ := MonoidHom.mem_range.mp hx
  obtain ⟨r, hr, rfl⟩ := hv
  have htκ : t ∈ S.Lbar ((κ : G) * g) := by
    have h1 := conj_mem_Lbar_mul S κ ht
    rwa [hxt, mul_assoc, mul_inv_cancel, mul_one] at h1
  obtain ⟨k, hk, hLk⟩ := hD κ htκ
  have hcl := cl_eq_of_Lbar_eq H hLk
  refine ⟨S.ρ κ * r * (S.ρ κ)⁻¹ * S.ρ k, mul_mem (conj_mem_Rbar hxt hr) hk, ?_⟩
  simp only [coe_mul_apply]
  rw [ρ_cl_conj_z S k H.conj_mem, ← hcl, ← ρ_cl_conj_z S κ H.conj_mem, inv_apply_apply_O]

section Seven

variable (hCE : CentralExtInput.{u}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h8 : 8 ≤ finrank (ZMod 2) (Vt S g t))
include hCE H hNo C ht ht1 hVQ hΩ hN h8

theorem card_Obar_eq_three : Nat.card (Obar S) = 3 := by
  have hw := width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ
  have h3 := S5.card_oddCore_dvd_three H hNo C (by omega : 4 < S.width)
  obtain ⟨-, hO⟩ := timmesfeld_7_4 hCE H hNo C ht ht1 hVQ hΩ hN h8
  rw [card_Obar]
  rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h | h
  · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hO
  · exact h

theorem comm_mem_Obar {x : S.O} (hx : x ∈ S.Mbar) : x * t * x⁻¹ * t⁻¹ ∈ Obar S := by
  obtain ⟨hZ, -⟩ := timmesfeld_7_4 hCE H hNo C ht ht1 hVQ hΩ hN h8
  exact ⟨_, hZ ⟨x, hx⟩, rfl⟩

theorem nonempty_mulEquiv_Mbar : Nonempty (S.Mbar ≃* Perm (Fin 3) × Cbar S t) :=
  nonempty_mulEquiv_sigma_prod Obar_le_Mbar (card_Obar_eq_three hCE H hNo C ht ht1 hVQ hΩ hN h8)
    (fun _ hx _ hy => conj_mem_Obar hx hy) (S.Lbar_le_Mbar g ht)
    (mul_self_of_mem_Lbar S H.conj_mem ht) ht1
    (fun _ hx => comm_mem_Obar hCE H hNo C ht ht1 hVQ hΩ hN h8 hx) (exists_conj_ne H ht ht1)

theorem exists_mul_Cbar {x : S.O} (hx : x ∈ S.Mbar) :
    ∃ s ∈ Obar S ⊔ zpowers t, ∃ c ∈ Cbar S t, x = s * c :=
  exists_sigma_mul_cent Obar_le_Mbar (card_Obar_eq_three hCE H hNo C ht ht1 hVQ hΩ hN h8)
    (fun _ hx _ hy => conj_mem_Obar hx hy) (S.Lbar_le_Mbar g ht)
    (mul_self_of_mem_Lbar S H.conj_mem ht) ht1
    (fun _ hx => comm_mem_Obar hCE H hNo C ht ht1 hVQ hΩ hN h8 hx) (exists_conj_ne H ht ht1) hx

theorem mem_Cbar_of_comm {x : S.O} (hx : x ∈ S.Mbar) (hxt : x * t = t * x) :
    x ∈ Cbar S t ∨ t * x ∈ Cbar S t :=
  mem_cent_of_comm_t Obar_le_Mbar (card_Obar_eq_three hCE H hNo C ht ht1 hVQ hΩ hN h8)
    (fun _ hx _ hy => conj_mem_Obar hx hy) (S.Lbar_le_Mbar g ht)
    (mul_self_of_mem_Lbar S H.conj_mem ht) ht1
    (fun _ hx => comm_mem_Obar hCE H hNo C ht ht1 hVQ hΩ hN h8 hx) (exists_conj_ne H ht ht1)
    hx hxt

end Seven

end CFSG.LargeExtraspecial.S7
