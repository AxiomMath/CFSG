module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SylowEndExt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.NormalCentralA

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

omit [Finite G] in
theorem map_conj_inf_centralizer {T : Subgroup G} {y : G} (hy : y ∈ normalizer (T : Set G))
    (t : G) : (T ⊓ centralizer ({t} : Set G)).map (MulAut.conj y).toMonoidHom =
      T ⊓ centralizer ({y * t * y⁻¹} : Set G) := by
  ext z
  constructor
  · rintro ⟨x, ⟨hxT, hxc⟩, rfl⟩
    refine ⟨(mem_normalizer_iff.1 hy x).1 hxT, mem_centralizer_singleton_iff.2 ?_⟩
    have h : x * t = t * x := mem_centralizer_singleton_iff.1 hxc
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc y * x * y⁻¹ * (y * t * y⁻¹) = y * (x * t) * y⁻¹ := by group
      _ = y * (t * x) * y⁻¹ := by rw [h]
      _ = y * t * y⁻¹ * (y * x * y⁻¹) := by group
  · rintro ⟨hzT, hzc⟩
    have hz : z * (y * t * y⁻¹) = (y * t * y⁻¹) * z := mem_centralizer_singleton_iff.1 hzc
    have hx : y⁻¹ * z * y ∈ T := by
      have := (mem_normalizer_iff.1 (inv_mem hy) z).1 hzT
      simpa using this
    refine ⟨y⁻¹ * z * y, ⟨hx, mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    swap
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    calc y⁻¹ * z * y * t = y⁻¹ * (z * (y * t * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * t * y⁻¹) * z) * y := by rw [hz]
      _ = t * (y⁻¹ * z * y) := by group

section

variable (H : ThCyc G L R t) (W : ThLocalIn L S A B z)

include H W

theorem ThCyc.exists_conj_mul_t_of_invol {f : G} (hfL : f ∈ L) (hf2 : f ^ 2 = 1) (hf1 : f ≠ 1) :
    ∃ c : G, c⁻¹ * t * c = f * t := by
  obtain ⟨-, g, -, -, -, -, hgt⟩ := H.exists_fusing_z W
  have hzL : z ∈ L := W.S_le W.z_mem
  have hfo : orderOf (⟨f, hfL⟩ : L) = 2 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using hf2)) fun h => hf1 ?_
    simpa using congrArg Subtype.val h
  have hzo : orderOf (⟨z, hzL⟩ : L) = 2 := by
    refine orderOf_eq_prime (Subtype.ext (by simpa using W.z_sq)) fun h => W.z_ne_one ?_
    simpa using congrArg Subtype.val h
  obtain ⟨c, hc⟩ := isConj_iff.1 (H.data.invConj _ _ hfo hzo)
  have hcf : (c : G) * f * (c : G)⁻¹ = z := by simpa using congrArg Subtype.val hc
  have hct : t * (c : G) = (c : G) * t := H.comm_of_mem_L c.2
  have h1 : (c : G)⁻¹ * z * c = f := by
    calc (c : G)⁻¹ * z * c = (c : G)⁻¹ * ((c : G) * f * (c : G)⁻¹) * c := by rw [hcf]
      _ = f := by group
  have h2 : (c : G)⁻¹ * t * c = t := by
    calc (c : G)⁻¹ * t * c = (c : G)⁻¹ * (t * c) := by group
      _ = (c : G)⁻¹ * (c * t) := by rw [hct]
      _ = t := by group
  refine ⟨g⁻¹ * c, ?_⟩
  calc (g⁻¹ * (c : G))⁻¹ * t * (g⁻¹ * c) = (c : G)⁻¹ * (g * t * g⁻¹) * c := by group
    _ = (c : G)⁻¹ * (z * t) * c := by rw [hgt]
    _ = ((c : G)⁻¹ * z * c) * ((c : G)⁻¹ * t * c) := by group
    _ = f * t := by rw [h1, h2]

theorem ThCyc.sup_Bp_inf_L : (S ⊔ Bp A t) ⊓ L = S := by
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_left W.S_le)
  exact W.maximal ((S ⊔ Bp A t) ⊓ L) inf_le_right
    ((H.isPGroup_S_sup_Bp W).to_le inf_le_left) (le_inf le_sup_left W.S_le) hx

theorem ThCyc.sup_Bp_inf_centralizer_t (W2 : ThLocalIn2 B A Aa b) :
    (S ⊔ Bp A t) ⊓ centralizer ({t} : Set G) = S ⊔ zpowers t := by
  have htT : t ∈ S ⊔ Bp A t := mem_sup_right (H.t_mem_Bp W W2)
  refine le_antisymm (fun x ⟨hxT, hxc⟩ => ?_) (le_inf (sup_le le_sup_left
    (zpowers_le.2 htT)) (sup_le (fun s hs => mem_centralizer_singleton_iff.2
      (H.comm_of_mem_L (W.S_le hs)).symm) (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))))
  have hxC : x ∈ L ⊔ zpowers t := by rw [← H.centralizer_eq_zpowers]; exact hxc
  have hcomm : zpowers t ≤ centralizer (L : Set G) := by
    rw [zpowers_le]
    exact mem_centralizer_iff.2 fun l hl => (H.comm_of_mem_L hl).symm
  obtain ⟨l, hl, r, hr, rfl⟩ := exists_mul_of_mem_sup hcomm hxC
  have hrT : r ∈ S ⊔ Bp A t := (zpowers_le.2 htT) hr
  have hlT : l ∈ S ⊔ Bp A t := by
    have := (S ⊔ Bp A t).mul_mem hxT ((S ⊔ Bp A t).inv_mem hrT)
    simpa using this
  have hlS : l ∈ S := by
    have h1 : l ∈ (S ⊔ Bp A t) ⊓ L := ⟨hlT, hl⟩
    rwa [H.sup_Bp_inf_L W] at h1
  exact mul_mem_sup hlS hr

variable (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D)

include W2 hD

theorem ThCyc.normalizer_Tprime_le_normalizer_A
    (hAb : ∀ g : G, ∀ Y : Subgroup G, Y ≤ L.map (MulAut.conj g).toMonoidHom → IsPGroup 2 Y →
      (∀ x ∈ Y, ∀ y ∈ Y, x * y = y * x) → Nat.card Y ≤ 2 ^ 8)
    (hZ : ∀ s ∈ S, (∀ x ∈ S, s * x * s⁻¹ * x⁻¹ ∈ Aa) → s ∈ B)
    {y : G} (hy : y ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G)) :
    y ∈ normalizer (A : Set G) := by
  have hT2 : IsPGroup 2 ↥(S ⊔ Bp A t) := H.isPGroup_S_sup_Bp W
  have hTN := H.S_sup_Bp_le_normalizer W
  have htT : t ∈ S ⊔ Bp A t := mem_sup_right (H.t_mem_Bp W W2)
  have hSP : S ⊔ zpowers t ≤ S ⊔ Bp A t := sup_le le_sup_left (zpowers_le.2 htT)
  have hAL : A ≤ L := le_trans (fun x hx => ((W.mem_A_iff x).1 hx).1) W.S_le
  have hAT : A ≤ S ⊔ Bp A t := by
    intro x hx
    have hxB : x ∈ B := (W.mem_B_iff x (hAL hx)).2 fun a ha => W.A_comm x hx a ha
    exact mem_sup_right (H.B_le_Bp W hxB)
  have huT : y * t * y⁻¹ ∈ S ⊔ Bp A t := (mem_normalizer_iff.1 hy t).1 htT
  have hcardT : Nat.card ↥((S ⊔ Bp A t) ⊓ centralizer ({y * t * y⁻¹} : Set G)) =
      2 * Nat.card S := by
    rw [← map_conj_inf_centralizer hy t, Subgroup.card_map_of_injective (MulAut.conj y).injective,
      H.sup_Bp_inf_centralizer_t W W2, H.card_sup_zpowers W]
  have hext := H.ext_extremal_of_card W W2 hD hAb hZ hT2 hSP le_sup_right hTN (g := y⁻¹)
    (by simpa only [inv_inv] using hcardT.ge) (by simpa only [inv_inv] using huT)
  simp only [inv_inv] at hext
  obtain ⟨-, -, -, -, d₁, hd₁, hu⟩ := hext
  have huBp : y * t * y⁻¹ ∈ Bp A t := by
    rcases hu with h | h | h <;> rw [h]
    · exact mul_mem (H.D_le_Bp W W2 hD hd₁) (H.t_mem_Bp W W2)
    · exact mul_mem (H.D_le_Bp W W2 hD hd₁) (H.b_mem_Bp W W2)
    · exact mul_mem (H.D_le_Bp W W2 hD hd₁) (mul_mem (H.b_mem_Bp W W2) (H.t_mem_Bp W W2))
  have hAu : ∀ a ∈ A, a * (y * t * y⁻¹) = (y * t * y⁻¹) * a := fun a ha =>
    mem_centralizer_iff.1 huBp.1 a ha
  have hAL' : ∀ a ∈ A, y⁻¹ * a * y ∈ L := by
    intro a ha
    have ha't : (y⁻¹ * a * y) * t = t * (y⁻¹ * a * y) := by
      calc (y⁻¹ * a * y) * t = y⁻¹ * (a * (y * t * y⁻¹)) * y := by group
        _ = y⁻¹ * ((y * t * y⁻¹) * a) * y := by rw [hAu a ha]
        _ = t * (y⁻¹ * a * y) := by group
    have hC : y⁻¹ * a * y ∈ L ⊔ zpowers t := by
      rw [← H.centralizer_eq_zpowers]
      exact mem_centralizer_singleton_iff.2 ha't
    have hcomm : zpowers t ≤ centralizer (L : Set G) := by
      rw [zpowers_le]
      exact mem_centralizer_iff.2 fun l hl => (H.comm_of_mem_L hl).symm
    obtain ⟨l, hl, r, hr, hlr⟩ := exists_mul_of_mem_sup hcomm hC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
    rcases zpow_eq_one_or_self H.sq_t k with hk | hk
    · rw [hlr, hk, mul_one]
      exact hl
    · exfalso
      rw [hk] at hlr
      have ha2 : (y⁻¹ * a * y) ^ 2 = 1 := by
        calc (y⁻¹ * a * y) ^ 2 = y⁻¹ * a ^ 2 * y := by simp only [sq]; group
          _ = 1 := by rw [W.A_sq a ha]; group
      have hl2 : l ^ 2 = 1 := by
        have h1 : (l * t) ^ 2 = l ^ 2 * t ^ 2 :=
          (show Commute l t from (H.comm_of_mem_L hl).symm).mul_pow 2
        rw [← hlr, ha2, H.sq_t, mul_one] at h1
        exact h1.symm
      by_cases hl1 : l = 1
      · rw [hl1, one_mul] at hlr
        refine H.not_conj_mem y⁻¹ ?_
        have : (y⁻¹)⁻¹ * t * y⁻¹ = a := by
          rw [← hlr]
          group
        rw [this]
        exact hAL ha
      · obtain ⟨c, hc⟩ := H.exists_conj_mul_t_of_invol W hl hl2 hl1
        refine H.not_conj_mem (c * y⁻¹) ?_
        have : (c * y⁻¹)⁻¹ * t * (c * y⁻¹) = a := by
          calc (c * y⁻¹)⁻¹ * t * (c * y⁻¹) = y * (c⁻¹ * t * c) * y⁻¹ := by group
            _ = y * (y⁻¹ * a * y) * y⁻¹ := by rw [hc, ← hlr]
            _ = a := by group
        rw [this]
        exact hAL ha
  have hy' : y⁻¹ ∈ normalizer ((S ⊔ Bp A t : Subgroup G) : Set G) := inv_mem hy
  have hXS : A.map (MulAut.conj y⁻¹).toMonoidHom ≤ S := by
    rintro _ ⟨a, ha, rfl⟩
    have haT : y⁻¹ * a * y ∈ S ⊔ Bp A t := by
      have := (mem_normalizer_iff.1 hy' a).1 (hAT ha)
      simpa using this
    have hmem : (MulAut.conj y⁻¹).toMonoidHom a ∈ (S ⊔ Bp A t) ⊓ L := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      exact ⟨haT, hAL' a ha⟩
    rwa [H.sup_Bp_inf_L W] at hmem
  have hXn : ∀ s ∈ S, ∀ x ∈ A.map (MulAut.conj y⁻¹).toMonoidHom,
      s * x * s⁻¹ ∈ A.map (MulAut.conj y⁻¹).toMonoidHom := by
    rintro s hs _ ⟨a, ha, rfl⟩
    have hn : y * s * y⁻¹ ∈ S ⊔ Bp A t := (mem_normalizer_iff.1 hy s).1 (mem_sup_left hs)
    have hna : (y * s * y⁻¹) * a * (y * s * y⁻¹)⁻¹ ∈ A :=
      H.normalizer_W5_conj_mem W (hTN hn) ha
    refine ⟨(y * s * y⁻¹) * a * (y * s * y⁻¹)⁻¹, hna, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group
  have hcard : Nat.card ↥(A.map (MulAut.conj y⁻¹).toMonoidHom) ≤ 16 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective, W.A_card]
  have hXA := W.le_A_of_normal hXS hXn hcard
  have hconj : ∀ a ∈ A, y⁻¹ * a * y ∈ A := fun a ha => hXA ⟨a, ha, by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]⟩
  exact mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := y) hconj)

end

end CFSG.EvenSporadicStandard.ThStd
