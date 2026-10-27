module

public import CFSG.LocalAnalysis.OddStandard.GH71.L102Five
public import CFSG.LocalAnalysis.OddStandard.GH71.L102Idx
public import CFSG.LocalAnalysis.OddStandard.GH71.L102Case
public import CFSG.LocalAnalysis.OddStandard.GH71.Bar3

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71


theorem le_of_isMaxAbelianIn (h : Ctx71 G z S U u) (hB0 : SpecB0) (hB4 : SpecB4)
    (h812 : IVK_8_12_ly) {H P Q : Subgroup G} (hH : H ≠ ⊤) (hSH : S ≤ H)
    (hcov : Covers H (Cen z) (pPrimeCoreOf 2 (Cen z)))
    (hbar : IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly)
    (hP : MaxSInv 3 S H P) (hQ : P ⊓ pPrimeCoreOf 2 H = Q) (hHQ : H ≤ normalizer (Q : Set G))
    (hL : H ⊓ centralizer (zIn Q : Set G) ≤ pPrimeCoreOf 2 H ⊔ zpowers z)
    {D : Subgroup G} (hD : IsMaxAbelianIn P D) : D ≤ Q := by
  by_contra hDQ
  have hzH : z ∈ H := hSH h.ctx.z_mem
  have hDP : D ≤ P := hD.1
  have hDH : D ≤ H := hDP.trans hP.1
  have hQP : Q ≤ P := by rw [← hQ]; exact inf_le_left
  have hDO : ¬ D ≤ pPrimeCoreOf 2 H := fun hle => hDQ (by rw [← hQ]; exact le_inf hDP hle)
  have hPO : ¬ P ≤ pPrimeCoreOf 2 H := fun hle => hDO (hDP.trans hle)
  have hcardP : Nat.card (barIn H P) = 3 := h.card_barIn_of_ivk h812 hH hSH hP hPO
  have hDbar : barIn H D = barIn H P := by
    have hle : barIn H D ≤ barIn H P := map_mono (fun x hx => hDP hx)
    have hne : barIn H D ≠ ⊥ := fun hb => hDO ((IVK812.barIn_eq_bot_iff hDH).mp hb)
    have hdvd : Nat.card (barIn H D) ∣ 3 := hcardP ▸ card_dvd_of_le hle
    have h3 : Nat.card (barIn H D) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with e | e
      · exact absurd (card_eq_one.mp e) hne
      · exact e
    exact eq_of_le_of_card_ge hle (by rw [h3, hcardP])
  set D₀ := D ⊓ pPrimeCoreOf 2 H with hD₀
  have hidxD : D₀.relIndex D = 3 := by
    rw [hD₀, IVK812.relIndex_eq_card_barIn hDH, hDbar, hcardP]
  have hD₀Q : D₀ ≤ Q := by rw [← hQ]; exact inf_le_inf_right _ hDP
  have hEQ : zIn Q ≤ Q := zIn_le Q
  have hE3 : IsPGroup 3 ↥(zIn Q) := hP.2.1.to_le (hEQ.trans hQP)
  have hHE : H ≤ normalizer (zIn Q : Set G) := hHQ.trans (normalizer_le_normalizer_zIn Q)
  have hEab : ∀ a ∈ zIn Q, ∀ b ∈ zIn Q, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp ha.2 b hb.1).symm
  have hED₀ : ∀ e ∈ zIn Q, ∀ d ∈ D₀, e * d = d * e := fun e he d hd =>
    (mem_centralizer_iff.mp he.2 d (hD₀Q hd)).symm
  have hidx1 : D₀.relIndex (zIn Q) ≤ 3 :=
    relIndex_le_three hD inf_le_left hidxD (hEQ.trans hQP) hEab hED₀
  obtain ⟨x, hxP, hx3, -, hSx, hUx⟩ := h.exists_gen_bar hB0 hSH hP.2.2.1 hcardP
  have hxz : x ∈ centralizer ({zBar H hzH} : Set (HBar H)) :=
    mem_centralizer_singleton_iff.mpr (mem_centralizer_singleton_iff.mp (hUx z h.z_mem hzH)).symm
  obtain ⟨g, -, y, hy, hy5⟩ := h.exists_five hB4 hSH hcov hbar hx3 hxz hSx
  obtain ⟨g', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H) g
  have hkH : (g' : G) ∈ H := g'.2
  have hkE : (g' : G) ∈ normalizer (zIn Q : Set G) := hHE hkH
  obtain ⟨d', hd', hd'x⟩ : x ∈ barIn H D := hDbar ▸ hxP
  set c := (MulAut.conj (g' : G)).toMonoidHom with hc
  have hDcH : D.map c ≤ H := by
    rintro _ ⟨w, hw, rfl⟩
    exact H.mul_mem (H.mul_mem hkH (hDH hw)) (H.inv_mem hkH)
  have hclos : closure ({x, QuotientGroup.mk' (pPrimeCore 2 ↥H) g' * x *
      (QuotientGroup.mk' (pPrimeCore 2 ↥H) g')⁻¹} : Set (HBar H)) ≤ barIn H (D ⊔ D.map c) := by
    rw [closure_le]
    refine Set.insert_subset_iff.mpr ⟨?_, Set.singleton_subset_iff.mpr ?_⟩
    · have hxD : x ∈ barIn H D := ⟨d', hd', hd'x⟩
      exact (map_mono (fun w hw => (le_sup_left : D ≤ D ⊔ D.map c) hw) :
        barIn H D ≤ barIn H (D ⊔ D.map c)) hxD
    · refine ⟨g' * d' * g'⁻¹, ?_, by rw [map_mul, map_mul, map_inv, hd'x]⟩
      exact (le_sup_right : D.map c ≤ D ⊔ D.map c) ⟨(d' : G), hd', rfl⟩
  obtain ⟨y', hy', hy'e⟩ := hclos hy
  have hn0 : orderOf y' ≠ 0 := (orderOf_pos y').ne'
  obtain ⟨a, b, hb5, hab⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 5 (by norm_num)
  obtain ⟨y₅, hy₅⟩ : ∃ y₅, y₅ = y' ^ (orderOf y' / 5 ^ a) := ⟨_, rfl⟩
  have hy₅ord : orderOf y₅ = 5 ^ a := by rw [hy₅]; exact orderOf_pow_orderOf_div hn0 ⟨b, hab⟩
  have hdiv : orderOf y' / 5 ^ a = b := by
    rw [hab, Nat.mul_div_cancel_left _ (pow_pos (by norm_num) a)]
  have hy₅bar : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) y₅) = 5 := by
    have hcop : (orderOf y).Coprime b := by
      rw [hy5]; exact (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr hb5
    have e : QuotientGroup.mk' (pPrimeCore 2 ↥H) y₅ = y ^ b := by
      rw [hy₅, map_pow, hy'e, hdiv]
    rw [e, Nat.Coprime.orderOf_pow hcop, hy5]
  have hy₅Y : (y₅ : G) ∈ D ⊔ D.map c := by
    have : y₅ ∈ (D ⊔ D.map c).subgroupOf H := by rw [hy₅]; exact Subgroup.pow_mem _ hy' _
    exact this
  have hidx : ((D₀ ⊓ D₀.map c) ⊓ zIn Q).relIndex (zIn Q) ≤ 9 := by
    rw [inf_relIndex_right]
    exact relIndex_inf_le.trans (Nat.mul_le_mul hidx1 ((relIndex_map_conj hkE).trans_le hidx1))
  have hDab := comm_of_isMulCommutative hD.2.1
  have hYE₀ : D ⊔ D.map c ≤ centralizer (((D₀ ⊓ D₀.map c) ⊓ zIn Q : Subgroup G) : Set G) := by
    refine sup_le (fun w hw => mem_centralizer_iff.mpr fun e he => hDab e he.1.1.1 w hw) ?_
    rintro _ ⟨w, hw, rfl⟩
    rw [mem_centralizer_iff]
    intro e he
    obtain ⟨e', he', rfl⟩ := he.1.2
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have := hDab e' he'.1 w hw
    calc (g' : G) * e' * (g' : G)⁻¹ * ((g' : G) * w * (g' : G)⁻¹)
        = (g' : G) * (e' * w) * (g' : G)⁻¹ := by group
      _ = (g' : G) * (w * e') * (g' : G)⁻¹ := by rw [this]
      _ = (g' : G) * w * (g' : G)⁻¹ * ((g' : G) * e' * (g' : G)⁻¹) := by group
  have hy₅ordG : orderOf (y₅ : G) = 5 ^ a := by rw [Subgroup.orderOf_coe]; exact hy₅ord
  have hEy : zIn Q ≤ centralizer ({(y₅ : G)} : Set G) :=
    centralizes_of_five hy₅ordG (hHE y₅.2) hE3 inf_le_right
      (fun e he => mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hYE₀ hy₅Y) e he))
      hidx
  have hy₅L : (y₅ : G) ∈ H ⊓ centralizer (zIn Q : Set G) :=
    ⟨y₅.2, mem_centralizer_iff.mpr fun e he => mem_centralizer_singleton_iff.mp (hEy he)⟩
  have hmem := bar_mem_zpowers hzH (hL hy₅L) y₅.2
  have hdvd := orderOf_dvd_of_mem_zpowers hmem
  have h2 : orderOf (QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨z, hzH⟩) = 2 := h.orderOf_zBar hzH
  have e : (⟨(y₅ : G), y₅.2⟩ : ↥H) = y₅ := rfl
  rw [h2, e, hy₅bar] at hdvd
  norm_num at hdvd

end Ctx71

end CFSG.OddStandard.GH71
