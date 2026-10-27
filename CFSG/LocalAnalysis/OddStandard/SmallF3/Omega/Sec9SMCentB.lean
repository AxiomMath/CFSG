module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SMLift
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SME1
import CFSG.GroupTheory.ElemAbelianClosure

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t t₀ z g : G} {L S B E1 : Subgroup G}

private abbrev sec9mN (t t₀ : G) (B : Subgroup G) : Subgroup G :=
  centMod (Asub9 t t₀ B) B

private abbrev sec9mO (t t₀ : G) (B : Subgroup G) : Subgroup G :=
  oddCoreIn (sec9mN t t₀ B)

theorem sec9m_O_cent_B (hT : Asc82Tab9M) (h6 : Asc82Tab6M)
    (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∀ o ∈ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ b ∈ B, o * b = b * o := by
  have hctxC : Sec9Ctx G t L S z g B t₀ := hctx.choice.toSec9Ctx
  have hOleN : sec9mO t t₀ B ≤ sec9mN t t₀ B := (oddCoreIn_normal (sec9mN t t₀ B)).1
  have hNnorm : sec9mN t t₀ B ≤ normalizer (B : Set G) := fun x hx => hx.1
  have hKH : autIn L B ≤ autIn (sec9mN t t₀ B) B := sec9m_autIn_le hT h6 hctxC
  have hRH : autIn (sec9mO t t₀ B) B ≤ autIn (sec9mN t t₀ B) B :=
    sec9m_autIn_mono hOleN
  have hKiso : Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) :=
    (sec9m_autL h6 hctxC).1
  have htrans : ∀ b b' : ↥B, b ≠ 1 → b' ≠ 1 →
      ∃ h ∈ autIn (sec9mN t t₀ B) B, h b = b' := by
    intro b b' hb hb'
    obtain ⟨k, hkK, hk⟩ := (sec9m_autL h6 hctxC).2 b b' hb hb'
    exact ⟨k, hKH hkK, hk⟩
  have hnormO : ∀ y ∈ sec9mN t t₀ B, ∀ x ∈ sec9mO t t₀ B,
      y * x * y⁻¹ ∈ sec9mO t t₀ B := by
    intro y hy x hx
    have hle : sec9mN t t₀ B ≤ normalizer (sec9mO t t₀ B : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hOleN).mp
        (oddCoreIn_normal (sec9mN t t₀ B)).2
    exact (Subgroup.mem_normalizer_iff.mp (hle hy) x).mp hx
  have hnormR := sec9m_autIn_conj (X := sec9mO t t₀ B) (Y := sec9mN t t₀ B)
    (B := B) hOleN hNnorm hnormO
  have hnotKR : ¬ autIn L B ≤ autIn (sec9mO t t₀ B) B := by
    intro hKR
    have hcardK : Nat.card ↥(autIn L B) = 360 := sec9m_card_A6 hKiso
    have hdvd1 : Nat.card ↥(autIn L B) ∣ Nat.card ↥(autIn (sec9mO t t₀ B) B) :=
      Subgroup.card_dvd_of_le hKR
    have hdvd2 : Nat.card ↥(autIn (sec9mO t t₀ B) B) ∣ Nat.card ↥(sec9mO t t₀ B) :=
      sec9m_card_autIn_dvd (hOleN.trans hNnorm)
    have h2 : 2 ∣ Nat.card ↥(sec9mO t t₀ B) := by
      have h2K : 2 ∣ Nat.card ↥(autIn L B) := by rw [hcardK]; norm_num
      exact dvd_trans (dvd_trans h2K hdvd1) hdvd2
    exact (odd_card_oddCoreIn (sec9mN t t₀ B)).not_two_dvd_nat h2
  have hV : Nat.card ↥B = 16 := by
    have h16 := hctx.choice.B_e16.2
    norm_num at h16
    exact h16
  have hAut : Nat.card (MulAut ↥B) = 20160 := sec9m_card_mulAut hctx.choice.B_e16
  have htriv := sec9m_normal_trivial (V := ↥B) hV hAut
    (H := autIn (sec9mN t t₀ B) B) (K := autIn L B) (R := autIn (sec9mO t t₀ B) B)
    hKH hKiso htrans hRH hnormR hnotKR
  intro o ho b hb
  have hoN : o ∈ sec9mN t t₀ B := hOleN ho
  have hnormB : o ∈ normalizer (B : Set G) := hNnorm hoN
  let r : MulAut ↥B := B.normalizerMonoidHom ⟨o, hnormB⟩
  have hrR : r ∈ autIn (sec9mO t t₀ B) B := by
    rw [autIn, Subgroup.mem_map]
    refine ⟨⟨o, hnormB⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact ho
  have hfix : r ⟨b, hb⟩ = ⟨b, hb⟩ := htriv r hrR ⟨b, hb⟩
  have hconj : o * b * o⁻¹ = b := by
    have h := congrArg (fun x : ↥B => (x : G)) hfix
    simpa [r, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  calc o * b = (o * b * o⁻¹) * o := by group
    _ = b * o := by rw [hconj]

private theorem sec9m_rho_M_eq_E1 (hT : Asc82Tab9M) (h6 : Asc82Tab6M)
    (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∀ m ∈ E1 ⊔ sec9mO t t₀ B,
      ∃ e ∈ E1, ∀ b ∈ B, m * b * m⁻¹ = e * b * e⁻¹ := by
  intro m hm
  rw [Subgroup.sup_eq_closure] at hm
  refine Subgroup.closure_induction (p := fun x _ =>
      ∃ e ∈ E1, ∀ b ∈ B, x * b * x⁻¹ = e * b * e⁻¹) ?_ ?_ ?_ ?_ hm
  · rintro x (hx | hx)
    · exact ⟨x, hx, fun b _ => rfl⟩
    · refine ⟨1, E1.one_mem, fun b hb => ?_⟩
      rw [sec9m_O_cent_B hT h6 hctx x hx b hb]
      group
  · exact ⟨1, E1.one_mem, fun b _ => by group⟩
  · rintro x y hx hy ⟨ex, hex, hx'⟩ ⟨ey, hey, hy'⟩
    refine ⟨ex * ey, E1.mul_mem hex hey, fun b hb => ?_⟩
    have hmem : ey * b * ey⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hctx.le_N hey).1 b).mp hb
    calc x * y * b * (x * y)⁻¹
        = x * (y * b * y⁻¹) * x⁻¹ := by group
      _ = x * (ey * b * ey⁻¹) * x⁻¹ := by rw [hy' b hb]
      _ = ex * (ey * b * ey⁻¹) * ex⁻¹ := hx' (ey * b * ey⁻¹) hmem
      _ = ex * ey * b * (ex * ey)⁻¹ := by group
  · rintro x hx ⟨e, he, hx'⟩
    refine ⟨e⁻¹, E1.inv_mem he, fun b hb => ?_⟩
    have hmem : e⁻¹ * b * e ∈ B := by
      have h := (Subgroup.mem_normalizer_iff.mp (inv_mem (hctx.le_N he).1) b).mp hb
      simpa [inv_inv] using h
    have h1 : x * (e⁻¹ * b * e) * x⁻¹ = e * (e⁻¹ * b * e) * e⁻¹ :=
      hx' (e⁻¹ * b * e) hmem
    have h2 : e * (e⁻¹ * b * e) * e⁻¹ = b := by group
    have h3 : x * (e⁻¹ * b * e) * x⁻¹ = b := by rw [h1, h2]
    calc x⁻¹ * b * (x⁻¹)⁻¹
        = x⁻¹ * (x * (e⁻¹ * b * e) * x⁻¹) * (x⁻¹)⁻¹ := by rw [h3]
      _ = e⁻¹ * b * (e⁻¹)⁻¹ := by group

theorem sec9m_M_cent_B (hT : Asc82Tab9M) (h6 : Asc82Tab6M)
    (hctx : Sec9E1 G t L S z g B t₀ E1) :
    ∀ m ∈ E1 ⊔ oddCoreIn (centMod (Asub9 t t₀ B) B), ∀ b ∈ B, m * b = b * m := by
  have hctxC : Sec9Ctx G t L S z g B t₀ := hctx.choice.toSec9Ctx
  have hOleN : sec9mO t t₀ B ≤ sec9mN t t₀ B := (oddCoreIn_normal (sec9mN t t₀ B)).1
  have hNnorm : sec9mN t t₀ B ≤ normalizer (B : Set G) := fun x hx => hx.1
  have hMleN : E1 ⊔ sec9mO t t₀ B ≤ sec9mN t t₀ B := sup_le hctx.le_N hOleN
  have hKH : autIn L B ≤ autIn (sec9mN t t₀ B) B := sec9m_autIn_le hT h6 hctxC
  have hRH : autIn (E1 ⊔ sec9mO t t₀ B) B ≤ autIn (sec9mN t t₀ B) B :=
    sec9m_autIn_mono hMleN
  have hKiso : Nonempty (↥(autIn L B) ≃* alternatingGroup (Fin 6)) :=
    (sec9m_autL h6 hctxC).1
  have htrans : ∀ b b' : ↥B, b ≠ 1 → b' ≠ 1 →
      ∃ h ∈ autIn (sec9mN t t₀ B) B, h b = b' := by
    intro b b' hb hb'
    obtain ⟨k, hkK, hk⟩ := (sec9m_autL h6 hctxC).2 b b' hb hb'
    exact ⟨k, hKH hkK, hk⟩
  have hMnorm : ∀ y ∈ sec9mN t t₀ B, ∀ x ∈ E1 ⊔ sec9mO t t₀ B,
      y * x * y⁻¹ ∈ E1 ⊔ sec9mO t t₀ B := by
    intro y hy x hx
    have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hMleN).mp hctx.normal
    exact (Subgroup.mem_normalizer_iff.mp (hle hy) x).mp hx
  have hnormR := sec9m_autIn_conj (X := E1 ⊔ sec9mO t t₀ B) (Y := sec9mN t t₀ B)
    (B := B) hMleN hNnorm hMnorm
  have hRcomm : ∀ φ ∈ autIn (E1 ⊔ sec9mO t t₀ B) B,
      ∀ ψ ∈ autIn (E1 ⊔ sec9mO t t₀ B) B, φ * ψ = ψ * φ := by
    apply sec9m_autIn_comm
    intro x hx x' hx' b hb
    obtain ⟨e, he, hxe⟩ := sec9m_rho_M_eq_E1 hT h6 hctx x hx
    obtain ⟨e', he', hx'e⟩ := sec9m_rho_M_eq_E1 hT h6 hctx x' hx'
    have hmem' : e' * b * e'⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hctx.le_N he').1 b).mp hb
    have hmem : e * b * e⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hctx.le_N he).1 b).mp hb
    have hL : x * (x' * b * x'⁻¹) * x⁻¹ = e * (e' * b * e'⁻¹) * e⁻¹ := by
      rw [hx'e b hb]
      exact hxe (e' * b * e'⁻¹) hmem'
    have hR : x' * (x * b * x⁻¹) * x'⁻¹ = e' * (e * b * e⁻¹) * e'⁻¹ := by
      rw [hxe b hb]
      exact hx'e (e * b * e⁻¹) hmem
    rw [hL, hR]
    let c : G := e * e' * e⁻¹ * e'⁻¹
    have hcA : c ∈ Asub9 t t₀ B := sec9m_E1_comm_mem_A hctx he he'
    have hX : (e' * e) * b * (e' * e)⁻¹ ∈ B :=
      (Subgroup.mem_normalizer_iff.mp (hctx.le_N (E1.mul_mem he' he)).1 b).mp hb
    have hXA : (e' * e) * b * (e' * e)⁻¹ ∈ Asub9 t t₀ B :=
      Subgroup.mem_sup_right hX
    have hcomm_cX : c * ((e' * e) * b * (e' * e)⁻¹) =
        ((e' * e) * b * (e' * e)⁻¹) * c :=
      CFSG.Open.IsElemAbelian.comm (sec9n_A_elem hctxC) hcA hXA
    have hce : e * e' = c * (e' * e) := by
      show e * e' = (e * e' * e⁻¹ * e'⁻¹) * (e' * e)
      group
    calc e * (e' * b * e'⁻¹) * e⁻¹
        = (e * e') * b * (e * e')⁻¹ := by group
      _ = c * ((e' * e) * b * (e' * e)⁻¹) * c⁻¹ := by
            rw [hce]; group
      _ = (e' * e) * b * (e' * e)⁻¹ := by rw [hcomm_cX]; group
      _ = e' * (e * b * e⁻¹) * e'⁻¹ := by group
  have hnotKR : ¬ autIn L B ≤ autIn (E1 ⊔ sec9mO t t₀ B) B := by
    intro hKR
    obtain ⟨a, b, hab⟩ := sec9m_not_comm hKiso
    have hcomm := hRcomm a.1 (hKR a.2) b.1 (hKR b.2)
    exact hab (Subtype.ext hcomm)
  have hV : Nat.card ↥B = 16 := by
    have h16 := hctx.choice.B_e16.2
    norm_num at h16
    exact h16
  have hAut : Nat.card (MulAut ↥B) = 20160 := sec9m_card_mulAut hctx.choice.B_e16
  have htriv := sec9m_normal_trivial (V := ↥B) hV hAut
    (H := autIn (sec9mN t t₀ B) B) (K := autIn L B)
    (R := autIn (E1 ⊔ sec9mO t t₀ B) B) hKH hKiso htrans hRH hnormR hnotKR
  intro m hm b hb
  have hmN : m ∈ sec9mN t t₀ B := hMleN hm
  have hnormB : m ∈ normalizer (B : Set G) := hNnorm hmN
  let r : MulAut ↥B := B.normalizerMonoidHom ⟨m, hnormB⟩
  have hrR : r ∈ autIn (E1 ⊔ sec9mO t t₀ B) B := by
    rw [autIn, Subgroup.mem_map]
    refine ⟨⟨m, hnormB⟩, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact hm
  have hfix : r ⟨b, hb⟩ = ⟨b, hb⟩ := htriv r hrR ⟨b, hb⟩
  have hconj : m * b * m⁻¹ = b := by
    have h := congrArg (fun x : ↥B => (x : G)) hfix
    simpa [r, Subgroup.normalizerMonoidHom_apply_apply_coe] using h
  calc m * b = (m * b * m⁻¹) * m := by group
    _ = b * m := by rw [hconj]

end CFSG.OddStandard.SmallF3.Omega
