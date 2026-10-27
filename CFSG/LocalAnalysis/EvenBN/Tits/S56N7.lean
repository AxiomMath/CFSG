module

public import CFSG.LocalAnalysis.EvenBN.Tits.S56Bridge
public import CFSG.LocalAnalysis.EvenBN.Tits.S56N3

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.EvenBN.Tits

open Subgroup CFSG.Sporadic.Schreier.Tits
open scoped Pointwise

namespace Data

variable {G : Type} [Group G] [Finite G] {d : Data G}


theorem Hyp.s56_comm_P10_CNt_F (h49 : d.Thm49Statement) (hd : d.Hyp) {c f : G}
    (hcP : c ∈ d.s56P10) (hct : c ∈ centralizer ({d.t} : Set G)) (hf : f ∈ d.F) :
    c * f * c⁻¹ * f⁻¹ ∈ d.s56U11 := by
  obtain ⟨hcP0, hcC⟩ := mem_inf.1 (s56P10_def d ▸ hcP)
  have hbridge := hd.s56_rho_P0_mem_hatC h49 hcP0 hct
  obtain ⟨f', hf'F, hf'D, rfl⟩ := mem_liftSub.1 hf
  set r : Equiv.Perm (Fin 1755) := ↑(d.ρ ⟨c, hct⟩) with hr
  have hrA : r ∈ titsA := (d.ρ ⟨c, hct⟩).2
  have hconj : r * f' * r⁻¹ ∈ titsD := (Model.conj_mem_titsD_iff hrA (titsD_le_titsA hf'D)).2 hf'D
  have hcomm : ∀ a ∈ titsD, d.lift a ∈ d.s56U10 → r * a = a * r := fun a haD ha =>
    (hd.commute_lift_iff hct haD).1 (mem_centralizer_iff.1 hcC _ ha).symm
  have h10D := s56_parrottV_mem_titsD (i := 10) (by omega)
  have h11D := s56_parrottV_mem_titsD (i := 11) (by omega)
  have h12D : Model.parrottV 12 ∈ titsD := by
    rw [Model.parrottV_twelve]; exact titsZ_mem_titsD
  have h10 := hcomm _ h10D (s56_pv10_mem_U10 d)
  have h11 := hcomm _ h11D (s56_U11_le_U10 d (s56_pv11_mem_U11 d))
  have h12 : r * Model.parrottV 12 = Model.parrottV 12 * r := hcomm _ h12D (by
    have : d.lift (Model.parrottV 12) = d.z := s56_pv12 d
    rw [this]; exact s56_U11_le_U10 d (s56_z_mem_U11 d))
  have hU := Model.hatC_comm_mem hbridge h10 h11 h12 hf'F
  have e1 : c * d.lift f' * c⁻¹ = d.lift (r * f' * r⁻¹) :=
    hd.conj_lift_eq hct hf'D hconj (by rw [hr]; group)
  have e2 : c * d.lift f' * c⁻¹ * (d.lift f')⁻¹ = d.lift (r * f' * r⁻¹ * f'⁻¹) := by
    rw [e1, ← d.lift_inv hf'D, ← d.lift_mul hconj (inv_mem hf'D)]
  rw [e2, s56U11_eq_liftSub]
  exact mem_liftSub.2 ⟨_, hU, mul_mem hconj (inv_mem hf'D), rfl⟩

theorem Hyp.s56_comm_P10_CNt_B (h49 : d.Thm49Statement) (hd : d.Hyp) {c b : G}
    (hcP : c ∈ d.s56P10) (hct : c ∈ centralizer ({d.t} : Set G)) (hb : b ∈ d.B) :
    c * b * c⁻¹ * b⁻¹ ∈ d.s56U11 := by
  have hct' : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 hct
  rcases (hd.s56_mem_B_iff).1 hb with hf | hf
  · exact hd.s56_comm_P10_CNt_F h49 hcP hct hf
  · obtain ⟨f, hfdef⟩ : ∃ f, f = d.t * b := ⟨_, rfl⟩
    rw [← hfdef] at hf
    have hb' : b = d.t * f := by rw [hfdef, ← mul_assoc, hd.t_mul_self, one_mul]
    have hw := hd.s56_comm_P10_CNt_F h49 hcP hct hf
    have hwL : c * f * c⁻¹ * f⁻¹ ∈ d.L := by
      rw [s56U11_eq_liftSub] at hw
      exact d.liftSub_le _ hw
    have hcom := hd.L_comm_t hwL
    have e : c * (d.t * f) * c⁻¹ * (d.t * f)⁻¹ = c * f * c⁻¹ * f⁻¹ := by
      calc c * (d.t * f) * c⁻¹ * (d.t * f)⁻¹ = d.t * (c * f * c⁻¹ * f⁻¹) * d.t⁻¹ := by
            have h1 : c * (d.t * f) = d.t * (c * f) := by
              rw [← mul_assoc, hct', mul_assoc]
            calc c * (d.t * f) * c⁻¹ * (d.t * f)⁻¹ = (c * (d.t * f)) * c⁻¹ * (d.t * f)⁻¹ := rfl
              _ = (d.t * (c * f)) * c⁻¹ * (d.t * f)⁻¹ := by rw [h1]
              _ = d.t * (c * f * c⁻¹ * f⁻¹) * d.t⁻¹ := by group
        _ = c * f * c⁻¹ * f⁻¹ := by rw [← hcom]; group
    rw [hb', e]
    exact hw

theorem Hyp.s56_eps_mem_F_of_N (h49 : d.Thm49Statement) (hd : d.Hyp) {n : G} (hn : n ∈ d.N) :
    d.s56Eps n ∈ d.F := by
  obtain ⟨h1, -, -⟩ := hd.thm51 h49 (D := d.B) (Or.inr rfl)
  have hmem : n * d.t * n⁻¹ ∈ d.tG ∩ d.B :=
    ⟨⟨n, rfl⟩, (mem_normalizer_iff.1 hn _).1 (s56_t_mem_B d)⟩
  rw [h1] at hmem
  obtain ⟨x, hx, hxe⟩ := hmem
  have hxF : x ∈ d.F := hd.s56_B_inf_L (mem_inf.1 hx).1 (mem_inf.1 hx).2
  rw [s56Eps, ← hxe, ← mul_assoc, hd.t_mul_self, one_mul]
  exact hxF

theorem Hyp.s56_P0_transitive (h49 : d.Thm49Statement) (hd : d.Hyp) {f : G} (hf : f ∈ d.F) :
    ∃ p ∈ d.s56P0, p * d.t * p⁻¹ = d.t * f := by
  obtain ⟨h1, -, h3⟩ := hd.thm51 h49 (D := d.B) (Or.inr rfl)
  have hs : d.t * f ∈ d.tG ∩ d.B := by
    rw [h1]
    exact ⟨f, mem_inf.2 ⟨s56_F_le_B d hf, s56_F_le_L d hf⟩, rfl⟩
  obtain ⟨n, hn, hnt⟩ := h3 _ hs
  obtain ⟨p, hp, c, hc, rfl⟩ := hd.s56_N_decomp h49 hn
  refine ⟨p, hp, ?_⟩
  have hct : c * d.t = d.t * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).2
  rw [← hnt]
  calc p * d.t * p⁻¹ = p * (c * d.t * c⁻¹) * p⁻¹ := by rw [hct]; group
    _ = (p * c) * d.t * (p * c)⁻¹ := by group

theorem Hyp.s56_CP0t_le_M (hd : d.Hyp) {c : G} (hcP : c ∈ d.s56P0)
    (hct : c ∈ centralizer ({d.t} : Set G)) : c ∈ d.M := by
  have h := CFSG.Quasithin.twoF4S_le_twoF4H (hd.s56_rho_P0_mem_twoF4S hcP hct)
  rw [← Model.titsA_inf_normalizer_hatE] at h
  exact (hd.mem_normalizer_tSup_iff (Model.hatE_le_titsJ.trans titsJ_le_titsD) hct).2
    (mem_inf.1 h).2

theorem s56_U11_le_E (d : Data G) (hd : d.Hyp) : d.s56U11 ≤ d.E := fun u hu => by
  rcases s56_mem_U11_iff.1 hu with rfl | rfl | rfl | rfl
  · exact one_mem _
  · exact s56_pv11_mem_E d
  · exact hd.s56_z_mem_E
  · exact mul_mem (s56_pv11_mem_E d) hd.s56_z_mem_E

theorem Hyp.s56_Q2_inf_N_le_P0 (h49 : d.Thm49Statement) (hd : d.Hyp) {q : G} (hq : q ∈ d.s56Q2)
    (hqN : q ∈ d.N) : q ∈ d.s56P0 := by
  rw [← hd.s56_CN_U11_eq h49]
  exact mem_inf.2 ⟨hqN, mem_centralizer_iff.2 fun u hu =>
    ((s56_mem_Q2_iff).1 hq).2 u (s56_U11_le_E d hd hu)⟩

theorem Hyp.s56_P0_inf_M_iff (h49 : d.Thm49Statement) (hd : d.Hyp) {p : G} :
    p ∈ d.s56P0 ⊓ d.M ↔ p ∈ d.s56P0 ∧ ∃ e ∈ d.E, p * d.t * p⁻¹ = d.t * e := by
  constructor
  · intro h
    obtain ⟨hp, hpM⟩ := mem_inf.1 h
    exact ⟨hp, d.s56Eps p, hd.s56_eps_mem_E hpM, hd.s56_conj_t p⟩
  · rintro ⟨hp, e, he, hpe⟩
    refine mem_inf.2 ⟨hp, ?_⟩
    have hεF := hd.s56_eps_mem_F_of_N h49 (s56_P0_le_N d hp)
    have hε : d.s56Eps p = e := by
      rw [s56Eps, hpe, ← mul_assoc, hd.t_mul_self, one_mul]
    rw [hε] at hεF
    obtain ⟨-, -, htrans, -⟩ := hd.s56_structure_M h49
    obtain ⟨q, hq, hqt⟩ := htrans e he
    have hqε : d.s56Eps q = e := by
      rw [s56Eps, hqt, ← mul_assoc, hd.t_mul_self, one_mul]
    have hq0 : q ∈ d.s56Q0 := hd.s56_Q2_le_Q0 h49 hq
    have hqN : q ∈ d.N := (hd.s56_mem_N_iff_eps h49 hq0).2 (by rw [hqε]; exact hεF)
    have hqP : q ∈ d.s56P0 := hd.s56_Q2_inf_N_le_P0 h49 hq hqN
    have hqM : q ∈ d.M := ((s56_mem_Q2_iff).1 hq).1
    have hc : q⁻¹ * p ∈ centralizer ({d.t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      have h1 : q * d.t * q⁻¹ = p * d.t * p⁻¹ := by rw [hqt, hpe]
      calc (q⁻¹ * p) * d.t = q⁻¹ * (p * d.t * p⁻¹) * p := by group
        _ = q⁻¹ * (q * d.t * q⁻¹) * p := by rw [← h1]
        _ = d.t * (q⁻¹ * p) := by group
    have hcM := hd.s56_CP0t_le_M (mul_mem (inv_mem hqP) hp) hc
    have : p = q * (q⁻¹ * p) := by group
    rw [this]
    exact mul_mem hqM hcM

theorem Hyp.s56_card_E_inf_F (hd : d.Hyp) : Nat.card (d.E ⊓ d.F : Subgroup G) = 16 := by
  set W : Subgroup G := d.E ⊓ d.F with hW
  have hWF : W ≤ d.F := inf_le_right
  have hidx : (W.subgroupOf d.F).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨d.pv 7, hd.s56_pv7_mem_F⟩, fun b => ?_⟩
    have hbv : b.1 * d.pv 7 = d.pv 7 * b.1 := hd.s56_F_comm b.2 hd.s56_pv7_mem_F
    have hmem : ∀ x : ↥d.F, x ∈ W.subgroupOf d.F ↔ x.1 ∈ d.E := fun x => by
      rw [mem_subgroupOf]; exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩
    show Xor' (b * ⟨d.pv 7, hd.s56_pv7_mem_F⟩ ∈ W.subgroupOf d.F) (b ∈ W.subgroupOf d.F)
    rw [hmem, hmem]
    show Xor' (b.1 * d.pv 7 ∈ d.E) (b.1 ∈ d.E)
    rw [hbv]
    rcases Hyp.s56_F_cases d b.2 with h | h
    · refine Or.inr ⟨h, fun h' => hd.s56_pv7_not_mem_E ?_⟩
      have := mul_mem h' (inv_mem h)
      simpa using this
    · refine Or.inl ⟨h, fun h' => hd.s56_pv7_not_mem_E ?_⟩
      have := mul_mem h (inv_mem h')
      simpa using this
  have h := (W.subgroupOf d.F).card_mul_index
  rw [hidx, Nat.card_congr (subgroupOfEquivOfLe hWF).toEquiv, hd.B_facts.1] at h
  omega

theorem Hyp.s56_P0_inf_M_relIndex (h49 : d.Thm49Statement) (hd : d.Hyp) :
    (d.s56P0 ⊓ d.M).relIndex d.s56P0 = 2 := by
  set H : Subgroup G := d.s56P0 ⊓ d.M with hH
  set C₀ : Subgroup G := d.s56P0 ⊓ centralizer ({d.t} : Set G) with hC₀
  have horbP : {y | ∃ k ∈ d.s56P0, k * d.t * k⁻¹ = y} = (fun f => d.t * f) '' (d.F : Set G) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨d.s56Eps k, hd.s56_eps_mem_F_of_N h49 (s56_P0_le_N d hk), ?_⟩
      exact (hd.s56_conj_t k).symm
    · rintro ⟨f, hf, rfl⟩
      exact hd.s56_P0_transitive h49 hf
  have horbH : {y | ∃ k ∈ H, k * d.t * k⁻¹ = y} =
      (fun f => d.t * f) '' ((d.E ⊓ d.F : Subgroup G) : Set G) := by
    ext y
    constructor
    · rintro ⟨k, hk, rfl⟩
      obtain ⟨hkP, hkM⟩ := mem_inf.1 hk
      exact ⟨d.s56Eps k, mem_inf.2 ⟨hd.s56_eps_mem_E hkM,
        hd.s56_eps_mem_F_of_N h49 (s56_P0_le_N d hkP)⟩, (hd.s56_conj_t k).symm⟩
    · rintro ⟨f, hf, rfl⟩
      obtain ⟨hfE, hfF⟩ := mem_inf.1 hf
      obtain ⟨p, hp, hpt⟩ := hd.s56_P0_transitive h49 hfF
      exact ⟨p, (hd.s56_P0_inf_M_iff h49).2 ⟨hp, f, hfE, hpt⟩, hpt⟩
  have hHC : H ⊓ centralizer ({d.t} : Set G) = C₀ := by
    ext x
    constructor
    · intro hx
      obtain ⟨hxH, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨(mem_inf.1 hxH).1, hxC⟩
    · intro hx
      obtain ⟨hxP, hxC⟩ := mem_inf.1 hx
      exact mem_inf.2 ⟨mem_inf.2 ⟨hxP, hd.s56_CP0t_le_M hxP hxC⟩, hxC⟩
  have hcF : ((d.F : Set G)).ncard = 32 := by
    rw [← Nat.card_coe_set_eq]; exact hd.B_facts.1
  have hcEF : (((d.E ⊓ d.F : Subgroup G) : Set G)).ncard = 16 := by
    rw [← Nat.card_coe_set_eq]; exact hd.s56_card_E_inf_F
  have h1 := card_eq_ncard_conj_mul d.s56P0 d.t
  have h2 := card_eq_ncard_conj_mul H d.t
  rw [horbP, Set.ncard_image_of_injective _ (mul_right_injective d.t), hcF] at h1
  rw [horbH, Set.ncard_image_of_injective _ (mul_right_injective d.t), hcEF, hHC] at h2
  have h3 := Subgroup.relIndex_mul_card (H := H) (K := d.s56P0)
  rw [inf_of_le_left (inf_le_left : H ≤ d.s56P0), h2, h1] at h3
  have hpos : 0 < 16 * Nat.card C₀ := Nat.mul_pos (by norm_num) Nat.card_pos
  have h5 : (H.relIndex d.s56P0) * (16 * Nat.card C₀) = 2 * (16 * Nat.card C₀) := by
    rw [h3]; ring
  exact Nat.eq_of_mul_eq_mul_right hpos h5

end Data

end CFSG.LocalAnalysis.EvenBN.Tits
