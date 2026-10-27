module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S9b
public import CFSG.LocalAnalysis.ComponentClassification.TBLitComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81S8
public import CFSG.GH74.GLS.Bg.Local.Transfer1515

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

theorem X11.commutator_le_of_isCyclic {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    (hN : IsCyclic (H ⧸ N)) : commutator H ≤ N := by
  rw [_root_.commutator_def, commutator_le]
  intro g₁ _ g₂ _
  have hcomm : (QuotientGroup.mk' N g₁) * QuotientGroup.mk' N g₂ =
      QuotientGroup.mk' N g₂ * QuotientGroup.mk' N g₁ :=
    (IsCyclic.commGroup (α := H ⧸ N)).mul_comm _ _
  have h1 : QuotientGroup.mk' N ⁅g₁, g₂⁆ = 1 := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  exact (QuotientGroup.eq_one_iff _).mp h1

theorem X11.centralizer_le_coreActionKernel {H : Type*} [Group H] (K : Subgroup H) :
    centralizer (K : Set H) ≤ coreActionKernel K := by
  intro g hg
  refine ⟨centralizer_le_normalizer _ hg, fun j hj => ?_⟩
  have h1 : j * g = g * j := mem_centralizer_iff.mp hg j hj
  rw [show j⁻¹ * g⁻¹ * j * g = 1 by
    calc j⁻¹ * g⁻¹ * j * g = j⁻¹ * g⁻¹ * (j * g) := by group
      _ = j⁻¹ * g⁻¹ * (g * j) := by rw [h1]
      _ = 1 := by group]
  exact one_mem _

theorem X11.exists_sylowIn_ge {H : Type*} [Group H] [Finite H] {K C : Subgroup H} (hKC : K ≤ C)
    (hK : IsPGroup 2 K) :
    ∃ T : Subgroup H, K ≤ T ∧ T ≤ C ∧ IsPGroup 2 T ∧ ¬ 2 ∣ T.relIndex C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : IsPGroup 2 ↥(K.subgroupOf C) :=
    IsPGroup.of_equiv hK (subgroupOfEquivOfLe hKC).symm
  obtain ⟨R, hR⟩ := hK'.exists_le_sylow
  refine ⟨(R : Subgroup ↥C).map C.subtype, fun x hx => ?_, map_subtype_le _,
    R.isPGroup'.map C.subtype, ?_⟩
  · exact ⟨⟨x, hKC hx⟩, hR (show (⟨x, hKC hx⟩ : ↥C) ∈ K.subgroupOf C from hx), rfl⟩
  · have hS' : ((R : Subgroup ↥C).map C.subtype).subgroupOf C = (R : Subgroup ↥C) := by
      ext z
      rw [Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨w, hw, hwz⟩
        have : w = z := Subtype.ext hwz
        rwa [this] at hw
      · intro hz
        exact ⟨z, hz, rfl⟩
    have : ((R : Subgroup ↥C).map C.subtype).relIndex C = (R : Subgroup ↥C).index := by
      unfold Subgroup.relIndex
      rw [hS']
    rw [this]
    exact Sylow.not_dvd_index R

namespace Hyp59

variable {H : Type} [Group H] [Finite H] {h : Hyp59 H}

namespace L81Hyp

variable {H₁ : h.L81Hyp}

namespace Data

variable {d : Data H₁} {v : H} (hv : d.IsV v) (I : In81) (hst : d.Stage7 v)
  {N : Subgroup H} [N.Normal] (hNc : IsCyclic (H ⧸ N)) (hNa : h.a * d.sigma ∉ N)

include hNa in
theorem b_not_mem_N : d.b ∉ N := by
  intro hb
  apply hNa
  have := Normal.conj_mem (inferInstance : N.Normal) _ hb (h.x * d.g)⁻¹
  rwa [← conj_c_asigma (d := d), show (h.x * d.g)⁻¹ * (h.x * d.g * (h.a * d.sigma) *
    (h.x * d.g)⁻¹) * (h.x * d.g)⁻¹⁻¹ = h.a * d.sigma by group] at this

include I hst hNc in
theorem a_mem_N : h.a ∈ N :=
  X11.commutator_le_of_isCyclic hNc (commutator_mono le_top le_top
    (d.a_mem_commutator_F I.sy I.b1 I.b6 I.cf23 I.cf24 I.cfc I.cf1 I.cf2 hst.facts))

include hNc in
theorem J_le_N : h.J ≤ N := by
  rw [← TBLit.commutator_self_of_isPComponent h.J_le h.isPComponent_J]
  exact (commutator_mono le_top le_top).trans (X11.commutator_le_of_isCyclic hNc)

include hst hNa in
theorem eq_a_of_mem_P_inf_N {t : H} (htP : t ∈ h.P) (htN : t ∈ N) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : t = h.a := by
  by_contra hta
  obtain ⟨c, hc⟩ := hst.fusion t htP ht2 ht1 hta
  apply b_not_mem_N hNa
  have := Normal.conj_mem (inferInstance : N.Normal) _ htN c
  rwa [← hc, show c * (c⁻¹ * d.b * c) * c⁻¹ = d.b by group] at this

include hst hNa in
theorem eq_a_of_mem_Y9_inf_N {t : H} (htY : t ∈ Y9 h) (htN : t ∈ N) (ht2 : t * t = 1)
    (ht1 : t ≠ 1) : t = h.a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := P_sylow_Y9 H₁
  have hidx : ¬ 2 ∣ h.P.relIndex (Y9 h) := by
    have := Sylow.not_dvd_index R
    rwa [hR] at this
  have ht2' : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (by rw [pow_two]; exact ht2) ht1)
  obtain ⟨c, hcY, hc⟩ := exists_conj_into_sylow (zpowers_le.mpr htY) ht2' (P_le_Y9 h)
    (h.toHyp52.isPGroup_S.to_le inf_le_left) hidx
  have h1 := hc t (mem_zpowers t)
  have hcN : c⁻¹ * t * c ∈ N := by
    have := Normal.conj_mem (inferInstance : N.Normal) _ htN c⁻¹
    rwa [inv_inv] at this
  have h2 : c⁻¹ * t * c = h.a := eq_a_of_mem_P_inf_N hst hNa h1 hcN
    (by rw [show c⁻¹ * t * c * (c⁻¹ * t * c) = c⁻¹ * (t * t) * c by group, ht2]; group)
    (fun h3 => ht1 (by
      calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
        _ = 1 := by rw [h3]; group))
  have hca : c * h.a = h.a * c := (mem_centralizer_singleton_iff.mp (mem_inf.mp hcY).1)
  calc t = c * (c⁻¹ * t * c) * c⁻¹ := by group
    _ = c * h.a * c⁻¹ := by rw [h2]
    _ = h.a := by rw [hca, mul_inv_cancel_right]

include I hst hNc hNa in
theorem card_le_two_of_le_centralizer_J {E : Subgroup H}
    (hE : E ≤ centralizer (h.J : Set H) ⊓ N) (hE2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer (h.J : Set H) ⊓ N with hC
  have haC : h.a ∈ C := mem_inf.mpr ⟨mem_centralizer_iff.mpr fun j hj =>
    mem_centralizer_singleton_iff.mp (h.J_le hj), a_mem_N I hst hNc⟩
  have hCY : ∀ t ∈ C, t * h.a = h.a * t → t ∈ Y9 h ∧ t ∈ N := fun t htC hta =>
    ⟨mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hta,
      X11.centralizer_le_coreActionKernel h.J (mem_inf.mp htC).1⟩, (mem_inf.mp htC).2⟩
  have ha2 : h.a * h.a = 1 := Six.a_mul_a_self h.toHyp52
  have ha1 : h.a ≠ 1 := a_ne_one' (h := h)
  have hza : IsPGroup 2 (zpowers h.a) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h.orderOf_a, pow_one])
  obtain ⟨T, haT, hTC, hT2, hTidx⟩ := X11.exists_sylowIn_ge (zpowers_le.mpr haC) hza
  have haT' : h.a ∈ T := haT (mem_zpowers _)
  obtain ⟨w, hwT, hw1, hwZ⟩ := Seven.exists_mem_center_of_normal hT2 le_rfl
    (fun s hs n hn => mul_mem (mul_mem hs hn) (inv_mem hs))
    (fun hT => ha1 (by rw [hT] at haT'; exact mem_bot.mp haT'))
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hT2) ⟨w, hwT⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := fun hk0 => hw1 (by rw [hk0, pow_zero] at hk; exact orderOf_eq_one_iff.mp hk)
  set t₀ := w ^ (orderOf w / 2) with ht₀
  have ht₀ord : orderOf t₀ = 2 := orderOf_pow_orderOf_div (by rw [hk]; positivity)
    (by rw [hk]; exact dvd_pow_self 2 hk0)
  have ht₀T : t₀ ∈ T := pow_mem hwT _
  have ht₀Z : ∀ s ∈ T, s * t₀ = t₀ * s := fun s hs => ((Commute.pow_right (hwZ s hs) _).eq)
  have ht₀2 : t₀ * t₀ = 1 := by rw [← pow_two, ← ht₀ord, pow_orderOf_eq_one]
  have ht₀1 : t₀ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at ht₀ord
    exact absurd ht₀ord (by norm_num)
  obtain ⟨ht₀Y, ht₀N⟩ := hCY t₀ (hTC ht₀T) (ht₀Z _ haT').symm
  have ht₀a : t₀ = h.a := eq_a_of_mem_Y9_inf_N hst hNa ht₀Y ht₀N ht₀2 ht₀1
  have hTinv : ∀ s ∈ T, s * s = 1 → s ≠ 1 → s = h.a := by
    intro s hs hs2 hs1
    obtain ⟨hsY, hsN⟩ := hCY s (hTC hs) (by rw [← ht₀a]; exact ht₀Z s hs)
    exact eq_a_of_mem_Y9_inf_N hst hNa hsY hsN hs2 hs1
  have hE2' : IsPGroup 2 E := IsPGroup.iff_orderOf.mpr fun x => by
    have hx : x ^ 2 = 1 := Subtype.ext (by rw [pow_two]; exact hE2 x x.2)
    rcases (Nat.dvd_prime Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx) with h1 | h1
    · exact ⟨0, by rw [h1, pow_zero]⟩
    · exact ⟨1, by rw [h1, pow_one]⟩
  obtain ⟨c, hcC, hc⟩ := exists_conj_into_sylow hE hE2' hTC hT2 hTidx
  have hEle : E ≤ zpowers (c * h.a * c⁻¹) := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · have h1 := hTinv _ (hc x hx)
        (by rw [show c⁻¹ * x * c * (c⁻¹ * x * c) = c⁻¹ * (x * x) * c by group, hE2 x hx]; group)
        (fun h2 => hx1 (by
          calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
            _ = 1 := by rw [h2]; group))
      have : x = c * h.a * c⁻¹ := by
        calc x = c * (c⁻¹ * x * c) * c⁻¹ := by group
          _ = c * h.a * c⁻¹ := by rw [h1]
      rw [this]
      exact mem_zpowers _
  have h3 := Subgroup.card_le_of_le hEle
  rw [Nat.card_zpowers] at h3
  have h4 : orderOf (c * h.a * c⁻¹) = 2 := by
    rw [← h.orderOf_a]
    exact orderOf_injective (MulAut.conj c).toMonoidHom (MulAut.conj c).injective h.a
  rwa [h4] at h3

end Data

end L81Hyp

end Hyp59

end CFSG.ComponentClassification.GSThmB
