module

public import CFSG.GH74.Uniqueness.SU.SU13TC6GNorm
public import CFSG.GH74.Uniqueness.SU.SU13TC6C

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

namespace Ctx9

variable (X : Ctx9 G z)

theorem z_ne_one (X : Ctx9 G z) : z ≠ 1 := fun h => by
  have := X.hz
  rw [h, orderOf_one] at this
  omega

theorem t_ne_one : X.L.e.t ≠ 1 := fun h => by
  have := X.L.e.t_ord
  rw [h, orderOf_one] at this
  omega

theorem t_mem_C : X.L.e.t ∈ X.C := mem_centralizer_singleton_iff.mpr X.L.e.t_s₂

theorem kfour_le_C : (kfour X.hz X.L.e : Subgroup G) ≤ X.C := by
  intro x hx
  rcases kfour_mem X.hz X.L.e hx with rfl | rfl | rfl | rfl
  · exact X.C.mul_mem X.t_mem_C X.z_mem_C
  · exact X.t_mem_C
  · exact X.z_mem_C
  · exact X.C.one_mem

theorem kfour_sq {x : G} (hx : x ∈ kfour X.hz X.L.e) : x * x = 1 := by
  have : IsKleinFour (kfour X.hz X.L.e) := isKleinFour_kfour X.hz X.L.e
  exact CFSG.ABGLocalTools.kleinFour_mul_self hx

theorem kfour_odd_eq_one {x : G} (hx : x ∈ kfour X.hz X.L.e) (hodd : Odd (orderOf x)) : x = 1 := by
  by_contra h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact X.kfour_sq hx) h1
  rw [h2] at hodd
  exact absurd hodd (by decide)

theorem Y_inf_kfour : X.Y ⊓ kfour X.hz X.L.e = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxY, hxR⟩ := mem_inf.mp hx
  exact mem_bot.mpr (X.kfour_odd_eq_one hxR (X.odd_orderOf hxY (odd_card_oc _)))

theorem Y'_cent_R_eq_one {s : G} (hs : s ∈ ⁅X.Y, X.Y⁆) (hst : s * X.L.e.t = X.L.e.t * s)
    (hsz : s * z = z * s) : s = 1 := by
  have : IsKleinFour (kfour X.hz X.L.e) := isKleinFour_kfour X.hz X.L.e
  exact eq_one_of_mem_commutator_of_centralizes (Y := X.Y) (T := kfour X.hz X.L.e)
    (odd_card_oc _) (fun x hx => le_normalizer_oc X.C (X.kfour_le_C hx)) (t_mem_kfour X.hz X.L.e)
    (z_mem_kfour X.hz X.L.e) X.t_ne_one X.z_ne_one X.L.e.t_ne
    (fun a ha b hb c hc => (X.Zy_comm (X.class_two ha hb) hc).symm)
    (fun a ha hall b hb => X.cent_Y_R_central ha (hall _ (t_mem_kfour X.hz X.L.e))
      (hall _ (z_mem_kfour X.hz X.L.e)) hb)
    (fun r hr hr1 a ha b hb har hbr => X.cent_Y_abelian hr hr1 ha hb har hbr) hs hst hsz

theorem s₂_not_mem_Y' : X.L.e.s₂ ∉ ⁅X.Y, X.Y⁆ := fun h => by
  have h1 := X.Y'_cent_R_eq_one h X.L.e.t_s₂.symm X.L.e.s₂_comm
  have h2 := X.L.e.s₂_ord
  rw [h1, orderOf_one] at h2
  omega

theorem card_Mbar : Nat.card (Mbar X.C) = 12 := by
  have hCq := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥X.C)
  have hoc : Nat.card (oc X.C) = Nat.card (pPrimeCore 2 ↥X.C) :=
    Subgroup.card_map_of_injective X.C.subtype_injective
  rw [← hoc, X.Y_card, X.card_C_twelve] at hCq
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 3 ^ 7) (by linarith [hCq])

theorem exists_V1 : ∃ V₁ : Subgroup G, V₁ ≤ X.C ∧ X.Y ≤ V₁ ∧
    (∀ c ∈ X.C, ∀ v ∈ V₁, c * v * c⁻¹ ∈ V₁) ∧ Nat.card V₁ = 3 ^ 7 * 4 ∧
    (∀ x ∈ X.C, x * x = 1 → x ∈ V₁) := by
  obtain ⟨V, hVn, hV4⟩ := X.l3.cbar.four X.card_Mbar
  have : V.Normal := hVn
  have hidx : V.index = 3 := by
    have h2 := Subgroup.card_mul_index V
    rw [hV4, X.card_Mbar] at h2
    omega
  let V₁ : Subgroup G := (V.comap (proj X.C)).map X.C.subtype
  have hmem : ∀ x : G, x ∈ V₁ ↔ ∃ hx : x ∈ X.C, proj X.C ⟨x, hx⟩ ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hx, h⟩
      exact ⟨⟨x, hx⟩, h, rfl⟩
  refine ⟨V₁, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨hyC, hyc⟩ := mem_oc.mp hy
    refine (hmem y).mpr ⟨hyC, ?_⟩
    have : proj X.C ⟨y, hyC⟩ = 1 := by
      rw [← MonoidHom.mem_ker, ker_proj]
      exact hyc
    rw [this]
    exact V.one_mem
  · intro c hc v hv
    obtain ⟨hvC, hvV⟩ := (hmem v).mp hv
    refine (hmem _).mpr ⟨X.C.mul_mem (X.C.mul_mem hc hvC) (X.C.inv_mem hc), ?_⟩
    have : proj X.C ⟨c * v * c⁻¹, X.C.mul_mem (X.C.mul_mem hc hvC) (X.C.inv_mem hc)⟩ =
        proj X.C ⟨c, hc⟩ * proj X.C ⟨v, hvC⟩ * (proj X.C ⟨c, hc⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact hVn.conj_mem _ hvV _
  · have hsub : Nat.card V₁ = Nat.card (V.comap (proj X.C)) :=
      Subgroup.card_map_of_injective X.C.subtype_injective
    have h1 := Subgroup.card_mul_index (V.comap (proj X.C))
    rw [Subgroup.index_comap_of_surjective V (proj_surjective X.C)] at h1
    rw [hidx, X.card_C_twelve] at h1
    rw [hsub]
    omega
  · intro x hx hxx
    let q : ↥X.C →* Mbar X.C ⧸ V := (QuotientGroup.mk' V).comp (proj X.C)
    have hq3 : Nat.card (Mbar X.C ⧸ V) = 3 := by
      rw [← Subgroup.index_eq_card]
      exact hidx
    have hsq : (q ⟨x, hx⟩) ^ 2 = 1 := by
      rw [← map_pow]
      have : (⟨x, hx⟩ : ↥X.C) ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hxx)
      rw [this, map_one]
    have hdvd2 : orderOf (q ⟨x, hx⟩) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    have hdvd3 : orderOf (q ⟨x, hx⟩) ∣ 3 := hq3 ▸ orderOf_dvd_natCard _
    have h1 : orderOf (q ⟨x, hx⟩) = 1 := Nat.eq_one_of_dvd_coprimes (by norm_num) hdvd2 hdvd3
    have h2 : q ⟨x, hx⟩ = 1 := orderOf_eq_one_iff.mp h1
    exact (hmem x).mpr ⟨hx, (QuotientGroup.eq_one_iff _).mp h2⟩

theorem kfour_le_V1 {V₁ : Subgroup G} (hinv : ∀ x ∈ X.C, x * x = 1 → x ∈ V₁) :
    kfour X.hz X.L.e ≤ V₁ := fun _ hx => hinv _ (X.kfour_le_C hx) (X.kfour_sq hx)

theorem V1_form {V₁ : Subgroup G} (hYV : X.Y ≤ V₁) (hcard : Nat.card V₁ = 3 ^ 7 * 4)
    (hRV : kfour X.hz X.L.e ≤ V₁) : ∀ v ∈ V₁, ∃ y ∈ X.Y, ∃ r ∈ kfour X.hz X.L.e, v = y * r := by
  have hD : ∀ d ∈ kfour X.hz X.L.e, ∀ w ∈ X.Y, d * w * d⁻¹ ∈ X.Y :=
    fun d hd w hw => X.conj_Y (X.kfour_le_C hd) hw
  have hle : TT X.Y (kfour X.hz X.L.e) hD ≤ V₁ := by
    rintro _ ⟨w, hw, d, hd, rfl⟩
    exact V₁.mul_mem (hYV hw) (hRV hd)
  have : IsKleinFour (kfour X.hz X.L.e) := isKleinFour_kfour X.hz X.L.e
  have hTT : Nat.card (TT X.Y (kfour X.hz X.L.e) hD) = 3 ^ 7 * 4 := by
    rw [card_TT_eq hD X.Y_inf_kfour, X.Y_card, IsKleinFour.card_four]
  have heq : TT X.Y (kfour X.hz X.L.e) hD = V₁ :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hTT])
  intro v hv
  rw [← heq] at hv
  obtain ⟨w, hw, d, hd, rfl⟩ := hv
  exact ⟨w, hw, d, hd, rfl⟩

end Ctx9

end CFSG.GH74.Uniqueness.SU.SU13
