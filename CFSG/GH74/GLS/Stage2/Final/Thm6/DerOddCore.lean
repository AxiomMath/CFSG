module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Final.Thm6

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Final.Thm4
open scoped commutatorElement

section Abstract

variable {X : Type} [Group X] [Finite X]

theorem eq_bot_of_normal_odd_of_fitting_sq {B N : Subgroup X} (hNB : N ≤ B)
    (hnorm : ∀ b ∈ B, ∀ n ∈ N, b * n * b⁻¹ ∈ N) (hodd : Odd (Nat.card ↥N))
    (hsq : ∀ x ∈ Fm B, x ^ 2 = 1) : N = ⊥ := by
  by_contra hNne
  set N' : Subgroup ↥B := N.subgroupOf B with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn⟩
  have hcard : Nat.card ↥N' = Nat.card ↥N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNB).toEquiv
  have hsolv : Group.IsSolvable ↥N' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ (hcard ▸ hodd)
  have hFne : fittingSubgroup ↥N' ≠ ⊥ := by
    intro h
    have h1 := (fitting_eq_bot_iff_card_eq_one_of_solvable ↥N').mp h
    exact hNne (Subgroup.eq_bot_of_card_eq N (hcard ▸ h1))
  set K : Subgroup ↥B := (fittingSubgroup ↥N').map N'.subtype with hK
  have hKn : K.Normal := inferInstance
  have hKnil : Group.IsNilpotent ↥K :=
    Group.nilpotent_of_mulEquiv (Subgroup.equivMapOfInjective _ N'.subtype N'.subtype_injective)
  have hKle : K ≤ fittingSubgroup ↥B := le_sSup ⟨hKn, hKnil⟩
  have hK1 : ∀ x ∈ K, x = 1 := by
    intro x hx
    have hxF : (x : X) ∈ Fm B := ⟨x, hKle hx, rfl⟩
    have hx2 : (x : X) ^ 2 = 1 := hsq _ hxF
    obtain ⟨y, -, rfl⟩ := hx
    have hyN : ((y : ↥B) : X) ∈ N := Subgroup.mem_subgroupOf.mp y.2
    set w : ↥N := ⟨((y : ↥B) : X), hyN⟩ with hw
    have hd2 : orderOf (w : X) ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
    have hdN : orderOf (w : X) ∣ Nat.card ↥N := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_dvd_natCard w
    rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with h1 | h2
    · have : ((y : ↥B) : X) = 1 := orderOf_eq_one_iff.mp h1
      exact Subtype.ext this
    · rw [h2] at hdN
      exact absurd (even_iff_two_dvd.mpr hdN) (Nat.not_even_iff_odd.mpr hodd)
  apply hFne
  rw [eq_bot_iff]
  intro y hy
  have h1 := hK1 (N'.subtype y) ⟨y, hy, rfl⟩
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

end Abstract

section Bar

variable {G : Type} [Group G]

theorem barIn_mono {H X Y : Subgroup G} (h : X ≤ Y) : barIn H X ≤ barIn H Y :=
  Subgroup.map_mono (Subgroup.comap_mono h)

variable [Finite G]

theorem oddCore_le_pPrimeCoreOf_of_fitting {z : G} {M : Subgroup G} (hCM : Cen z ≤ M) (hz : z ^ 2 = 1)
    (hF : Fm (barIn M (Cen z)) = barIn M (zpowers z)) : OddCore z ≤ pPrimeCoreOf 2 M := by
  have hAC : OddCore z ≤ Cen z := Subgroup.map_subtype_le _
  have hAM : OddCore z ≤ M := hAC.trans hCM
  have hnormA : Cen z ≤ normalizer ((OddCore z : Subgroup G) : Set G) :=
    le_normalizer_map_subtype (Cen z) (pPrimeCore 2 ↥(Cen z))
  have hbot : barIn M (OddCore z) = ⊥ := by
    refine eq_bot_of_normal_odd_of_fitting_sq (B := barIn M (Cen z)) (barIn_mono hAC) ?_ ?_ ?_
    · rintro b ⟨⟨c, hcM⟩, hc, rfl⟩ n ⟨⟨a, haM⟩, ha, rfl⟩
      have hc' : c ∈ Cen z := Subgroup.mem_subgroupOf.mp hc
      have ha' : a ∈ OddCore z := Subgroup.mem_subgroupOf.mp ha
      have hmem : c * a * c⁻¹ ∈ M := M.mul_mem (M.mul_mem hcM haM) (M.inv_mem hcM)
      have hmemA : c * a * c⁻¹ ∈ OddCore z := (Subgroup.mem_normalizer_iff.mp (hnormA hc') a).mp ha'
      refine ⟨⟨c * a * c⁻¹, hmem⟩, Subgroup.mem_subgroupOf.mpr hmemA, ?_⟩
      have e : (⟨c * a * c⁻¹, hmem⟩ : ↥M) = ⟨c, hcM⟩ * ⟨a, haM⟩ * (⟨c, hcM⟩ : ↥M)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_inv]
    · have h1 : Nat.card ↥(barIn M (OddCore z)) ∣ Nat.card ↥((OddCore z).subgroupOf M) :=
        Subgroup.card_map_dvd _ _
      have h2 : Nat.card ↥((OddCore z).subgroupOf M) = Nat.card ↥(OddCore z) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAM).toEquiv
      have h3 : Nat.card ↥(OddCore z) = Nat.card ↥(pPrimeCore 2 ↥(Cen z)) :=
        Subgroup.card_map_of_injective (Cen z).subtype_injective
      have h4 : Odd (Nat.card ↥(pPrimeCore 2 ↥(Cen z))) :=
        Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥(Cen z)))
      rw [h2, h3] at h1
      exact Odd.of_dvd_nat h4 h1
    · intro x hx
      rw [hF] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hu)
      rw [← map_pow]
      have hu2 : u ^ 2 = 1 := by
        apply Subtype.ext
        change (u : G) ^ 2 = 1
        rw [← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
        simp [hz]
      rw [hu2, map_one]
  intro a ha
  have haM : a ∈ M := hAM ha
  have hmem : (QuotientGroup.mk' (pPrimeCore 2 ↥M)) ⟨a, haM⟩ ∈ barIn M (OddCore z) :=
    ⟨⟨a, haM⟩, ha, rfl⟩
  rw [hbot] at hmem
  have h1 : (⟨a, haM⟩ : ↥M) ∈ pPrimeCore 2 ↥M :=
    (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hmem)
  exact ⟨⟨a, haM⟩, h1, rfl⟩

end Bar

theorem oddCoreLeM_of (h34 : Leaf_Prop34) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (k : Kind) (S M : Subgroup G), Ctx20 G z k S M →
      Cen z < M → OddCore z ≤ pPrimeCoreOf 2 M := by
  intro G _ _ z k S M h20 hlt
  have h := h20.ctx17
  rcases h34 G z k S h.ctx M h.cen_le h.ne_top with hc | hd | ⟨ε, q, L₁, L₂, hk, hL4, -, hq3, hF, hcoat, -, -, -, hFm⟩
  · exact absurd (h.eq_of_oddCover hc) hlt.ne'
  · exact absurd hd (not_isDihedral_S h.ctx)
  · have hz : z ^ 2 = 1 := by
      rw [← h.ctx.orderOf_z]
      exact pow_orderOf_eq_one z
    exact oddCore_le_pPrimeCoreOf_of_fitting h.cen_le hz hFm

end CFSG.GH74.GLS.Stage2.Final.Thm6
