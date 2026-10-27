module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8H69S

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

namespace OHyp69

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T E : Subgroup G}
  {β : G} {B : Subgroup G} {S : Subgroup G}
  (h : OHyp69 L z t T E B β S)

include h

theorem W_norm_E {w : G} (hw : w ∈ L ⊓ centralizer ({t} : Set G)) {e : G} (he : e ∈ E) :
    w * e * w⁻¹ ∈ E :=
  h.wf.normal w hw.1 (mem_centralizer_singleton_iff.1 hw.2) e he

theorem E_le_W : E ≤ L ⊓ centralizer ({t} : Set G) := fun e he =>
  ⟨h.wf.E_le he, mem_centralizer_singleton_iff.2 (h.t_comm_E e he)⟩

theorem B_le_W : B ≤ L ⊓ centralizer ({t} : Set G) := fun b hb =>
  ⟨h.ob.B_le hb, h.ob.B_cent hb⟩

theorem E_inf_B {y : G} (hyE : y ∈ E) (hyB : y ∈ B) : y = 1 := by
  obtain ⟨eB⟩ := h.ob.B_iso
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup ↥B := MulEquiv.isSimpleGroup eB
  have hnorm : ((E ⊓ B).subgroupOf B).Normal := by
    refine ⟨fun k hk b => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    refine ⟨?_, ?_⟩
    · exact h.W_norm_E (h.B_le_W b.2) hk.1
    · exact (b * ⟨_, hk.2⟩ * b⁻¹).2
  haveI := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((E ⊓ B).subgroupOf B) with h1 | h1
  · have : (⟨y, hyB⟩ : ↥B) ∈ (E ⊓ B).subgroupOf B := mem_subgroupOf.2 ⟨hyE, hyB⟩
    rw [h1, mem_bot] at this
    exact congrArg Subtype.val this
  · exfalso
    have hBE : B ≤ E := fun b hb => by
      have : (⟨b, hb⟩ : ↥B) ∈ (E ⊓ B).subgroupOf B := by rw [h1]; exact mem_top _
      exact (mem_subgroupOf.1 this).1
    have hE2 : IsPGroup 2 E := h.oe.cfg.T_pgroup.to_le h.oe.E_le_T
    have hB2 : IsPGroup 2 B := hE2.to_le hBE
    obtain ⟨n, hn⟩ := hB2.exists_card_eq
    have h60 : Nat.card ↥B = 60 := by
      rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
      simp [Nat.card_eq_fintype_card, Fintype.card_fin]
      decide
    rw [h60] at hn
    have hn6 : n < 6 := by
      by_contra hn'
      push Not at hn'
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn'
      omega
    interval_cases n <;> omega

theorem W_decomp {w : G} (hw : w ∈ L ⊓ centralizer ({t} : Set G)) :
    ∃ b ∈ B, ∃ e ∈ E, w = b * e := by
  set Wg : Subgroup G := L ⊓ centralizer ({t} : Set G) with hWg
  let E' : Subgroup ↥Wg := E.subgroupOf Wg
  have hE'n : E'.Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [mem_subgroupOf] at hk ⊢
    exact h.W_norm_E g.2 hk
  let ι : ↥B →* ↥Wg := Subgroup.inclusion h.B_le_W
  let φ : ↥B →* ↥Wg ⧸ E' := (QuotientGroup.mk' E').comp ι
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    have h1 : ι b ∈ E' := (QuotientGroup.eq_one_iff _).1 hb
    have h2 : (b : G) ∈ E := mem_subgroupOf.1 h1
    have := h.E_inf_B h2 b.2
    exact (mem_bot.2 (Subtype.ext this))
  have hcardE : Nat.card ↥E' = 32 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.E_le_W).toEquiv]
    exact h.wf.card_E
  have hcardB : Nat.card ↥B = 60 := by
    obtain ⟨eB⟩ := h.ob.B_iso
    rw [Nat.card_congr eB.toEquiv, nat_card_alternatingGroup]
    simp [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hcardW : Nat.card ↥Wg = 1920 := h.wf.card_cent
  have hq : Nat.card (↥Wg ⧸ E') = 60 := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup E'
    rw [hcardW, hcardE] at this
    omega
  have hbij : Function.Bijective φ :=
    hinj.bijective_of_nat_card_le (by rw [hq, hcardB])
  obtain ⟨b, hb⟩ := hbij.2 (QuotientGroup.mk ⟨w, hw⟩)
  have h1 : (ι b)⁻¹ * ⟨w, hw⟩ ∈ E' := QuotientGroup.eq.1 hb
  have h2 : (b : G)⁻¹ * w ∈ E := mem_subgroupOf.1 h1
  exact ⟨b, b.2, _, h2, by group⟩

theorem W_cent_S {w : G} (hw : w ∈ L ⊓ centralizer ({t} : Set G)) {s : G} (hs : s ∈ S) :
    w * s = s * w := by
  obtain ⟨b, hb, e, he, rfl⟩ := h.W_decomp hw
  calc b * e * s = b * (e * s) := by group
    _ = b * (s * e) := by rw [← h.S_comm_E s hs e he]
    _ = (b * s) * e := by group
    _ = (s * b) * e := by rw [h.BS b hb s hs]
    _ = s * (b * e) := by group

theorem E_le_cent_S : E ≤ centralizer (S : Set G) := fun e he =>
  mem_centralizer_iff.2 fun s hs => h.S_comm_E s hs e he

theorem W_norm_U {w : G} (hw : w ∈ L ⊓ centralizer ({t} : Set G)) {u : G} (hu : u ∈ S ⊔ E) :
    w * u * w⁻¹ ∈ S ⊔ E := by
  obtain ⟨s, hs, e, he, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer h.E_le_cent_S hu
  have h1 : w * (s * e) * w⁻¹ = s * (w * e * w⁻¹) := by
    calc w * (s * e) * w⁻¹ = (w * s) * e * w⁻¹ := by group
      _ = (s * w) * e * w⁻¹ := by rw [h.W_cent_S hw hs]
      _ = s * (w * e * w⁻¹) := by group
  rw [h1]
  exact mul_mem (mem_sup_left hs) (mem_sup_right (h.W_norm_E hw he))

theorem W_mem_M {w : G} (hw : w ∈ L ⊓ centralizer ({t} : Set G)) :
    w ∈ normalizer ((S ⊔ E : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro u
  refine ⟨fun hu => h.W_norm_U hw hu, fun hu => ?_⟩
  have := h.W_norm_U (inv_mem hw) hu
  simpa [mul_assoc] using this

@[expose] noncomputable def actW : ↥(L ⊓ centralizer ({t} : Set G)) →* MulAut ↥E :=
  E.normalizerMonoidHom.comp (Subgroup.inclusion (W_le_normalizer h.wf))

theorem two_le_card_range_ker : 960 ≤ Nat.card (actW h).range := by
  set f := actW h with hf
  have htW : t ∈ L ⊓ centralizer ({t} : Set G) :=
    ⟨h.oe.cfg.t_mem_A, mem_centralizer_singleton_iff.2 rfl⟩
  have hker : f.ker ≤ zpowers (⟨t, htW⟩ : ↥(L ⊓ centralizer ({t} : Set G))) := by
    intro k hk
    rw [MonoidHom.mem_ker] at hk
    have hkc : ∀ e ∈ E, (k : G) * e = e * (k : G) := by
      intro e he
      have := congrArg (fun m : MulAut ↥E => ((m ⟨e, he⟩ : ↥E) : G)) hk
      simp only [MulAut.one_apply] at this
      have h2 : (k : G) * e * (k : G)⁻¹ = e := this
      calc (k : G) * e = (k : G) * e * (k : G)⁻¹ * (k : G) := by group
        _ = e * (k : G) := by rw [h2]
    rcases h.wf.cent k k.2.1 (fun e he => hkc e he) with h1 | h1
    · have : k = 1 := Subtype.ext h1
      rw [this]; exact one_mem _
    · have : k = ⟨t, htW⟩ := Subtype.ext h1
      rw [this]; exact mem_zpowers _
  have hcardk : Nat.card f.ker ≤ 2 := by
    have := Subgroup.card_le_of_le hker
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, h.oe.cfg.t_order'] at this
    exact this
  have h1 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker, h.wf.card_cent] at h1
  have hk0 : 0 < Nat.card f.ker := Nat.card_pos
  nlinarith

theorem index_range_le_two : (actW h).range.index ≤ 2 := by
  have h1 := Subgroup.card_mul_index (actW h).range
  have h2 := h.ef.card_aut
  have h3 := h.two_le_card_range_ker
  by_contra hcon
  push Not at hcon
  nlinarith

theorem W_orbit_two {e e' : G} (he : e ∈ E) (he1 : e * e = 1) (he2 : e ≠ 1) (he3 : e ≠ t)
    (he' : e' ∈ E) (he1' : e' * e' = 1) (he2' : e' ≠ 1) (he3' : e' ≠ t) :
    ∃ w ∈ L ⊓ centralizer ({t} : Set G), w * e * w⁻¹ = e' := by
  obtain ⟨φ, hφ, hφe⟩ := h.ef.orbit_two (actW h).range h.index_range_le_two ⟨e, he⟩ ⟨e', he'⟩
    he1 he2 he3 he1' he2' he3'
  obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hφ
  exact ⟨w, w.2, congrArg Subtype.val hφe⟩

theorem W_orbit_four {e e' : G} (he : e ∈ E) (he1 : e * e = t) (he' : e' ∈ E)
    (he1' : e' * e' = t) :
    ∃ w ∈ L ⊓ centralizer ({t} : Set G), w * e * w⁻¹ = e' := by
  obtain ⟨φ, hφ, hφe⟩ := h.ef.orbit_four (actW h).range h.index_range_le_two ⟨e, he⟩ ⟨e', he'⟩
    he1 he1'
  obtain ⟨w, rfl⟩ := MonoidHom.mem_range.1 hφ
  exact ⟨w, w.2, congrArg Subtype.val hφe⟩

end OHyp69

end CFSG.EvenSporadicStandard.Fin76b
