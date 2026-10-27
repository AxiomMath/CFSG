module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7S4e
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB81Fus2
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82Frontier

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr Seven

namespace Eight2

variable {X : Type} [Group X] [Finite X]

theorem secQ_injOn {h : Hyp52 X} {y : X} {Y : Subgroup X} (hY : IsPGroup 2 Y)
    (hYB : Y ⊓ h.secB0 y = ⊥) :
    Set.InjOn (h.subQ y) ((Y.subgroupOf (h.secSub y) : Subgroup _) : Set ↥(h.secSub y)) :=
  Hyp52.subQ_injOn hY hYB

theorem card_map_secQ_of_inf {h : Hyp52 X} {y : X} {Y : Subgroup X} (hY : IsPGroup 2 Y)
    (hYH : Y ≤ h.secSub y) (hYB : Y ⊓ h.secB0 y = ⊥) :
    Nat.card ↥((Y.subgroupOf (h.secSub y)).map (h.subQ y)) = Nat.card Y :=
  Hyp52.card_map_subQ_of_inf hY hYH hYB

omit [Finite X] in
theorem map_conjugate' {G G' : Type*} [Group G] [Group G'] (f : G →* G') (K : Subgroup G)
    (g : G) : (conjugate K g).map f = conjugate (K.map f) (f g) := by
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, mem_conjugate_iff] at hw
    rw [mem_conjugate_iff]
    refine ⟨g * w * g⁻¹, hw, ?_⟩
    simp only [map_mul, map_inv]
  · intro hv
    rw [mem_conjugate_iff] at hv
    obtain ⟨w, hw, hwv⟩ := hv
    refine ⟨g⁻¹ * w * g, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_conjugate_iff, show g * (g⁻¹ * w * g) * g⁻¹ = w by group]
      exact hw
    · rw [map_mul, map_mul, map_inv, hwv]
      group

abbrev Setting3.Ct (s : Setting3 X) : Subgroup X := s.Dt ⊓ s.h.P

namespace Setting3

variable (s : Setting3 X)

theorem D_comm_P {d p : X} (hd : d ∈ s.h.D) (hp : p ∈ s.h.P) : d * p = p * d := by
  have hDP := s.h.D_inf_P_eq_bot s.center_J
  have h1 : d * p * d⁻¹ * p⁻¹ ∈ s.h.D ⊓ s.h.P := by
    refine mem_inf.mpr ⟨?_, ?_⟩
    · rw [show d * p * d⁻¹ * p⁻¹ = d * (p * d⁻¹ * p⁻¹) by group]
      exact mul_mem hd (s.h.sec8_conj_mem_D (s.h.P_le_S hp) (inv_mem hd))
    · exact mul_mem (s.h.conj_mem_P (s.h.D_le_S hd) hp) (inv_mem hp)
  rw [hDP, mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem B0_le_P : s.h.secB0 s.y ≤ s.h.P := (s.h.secB0_le_B s.y).trans s.h.B_le_P

theorem D_le_centralizer_B0 : s.h.D ≤ centralizer (s.h.secB0 s.y : Set X) := fun _ hd =>
  mem_centralizer_iff.mpr fun _ hb => (s.D_comm_P hd (s.B0_le_P hb)).symm

theorem D_le_G0 : s.h.D ≤ s.h.secG0 s.y :=
  s.D_le_centralizer_B0.trans (centralizer_le_normalizer _)

theorem D_le_secSub : s.h.D ≤ s.h.secSub s.y :=
  (le_inf s.h.D_le_S s.D_le_G0).trans (s.h.S_inf_le_secSub s.y)

theorem D_inf_B0 : s.h.D ⊓ s.h.secB0 s.y = ⊥ := by
  rw [eq_bot_iff, ← s.h.D_inf_P_eq_bot s.center_J]
  exact inf_le_inf_left _ s.B0_le_P

theorem D_le_J0 : s.h.D ≤ GSLit.fixedLayer s.h.J (s.h.secB0 s.y) := by
  rw [GSLit.fixedLayer_eq_closure s.h.sec8_quasisimple_Jbar
    ((s.h.secB0_le_B s.y).trans s.h.sec8_B_le_kernel_J) (s.h.isPGroup_secB0 s.y)]
  intro d hd
  refine subset_closure ⟨mem_inf.mpr ⟨s.h.D_le_J hd, s.D_le_centralizer_B0 hd⟩, ?_⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 (s.h.isPGroup_S.to_le s.h.D_le_S) ⟨d, hd⟩
  exact ⟨k, (Subgroup.orderOf_coe (⟨d, hd⟩ : s.h.D)).trans hk⟩

theorem map_D_le : (s.h.D.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) ≤
    s.sec.S ⊓ s.sec.J := by
  rw [s.sec_S, s.sec_J]
  refine le_inf (map_mono fun w hw => ?_) (map_mono fun w hw => ?_)
  · have hwD : (w : X) ∈ s.h.D := mem_subgroupOf.mp hw
    exact mem_inf.mpr ⟨s.S0_le_hr (mem_inf.mpr ⟨s.h.D_le_S hwD, s.D_le_G0 hwD⟩), s.D_le_G0 hwD⟩
  · exact s.D_le_J0 (mem_subgroupOf.mp hw)

theorem card_secD : Nat.card ↥(s.sec.S ⊓ s.sec.J) = Nat.card s.h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, -, hT⟩ := s.h.sec8_exists_sylow_Dbar
  obtain ⟨T', -, hT'⟩ := s.sec.toHyp52.sec8_exists_sylow_Dbar
  obtain ⟨e⟩ := s.sec_J_equiv
  have h1 := T.card_eq_multiplicity
  have h2 := T'.card_eq_multiplicity
  rw [Nat.card_congr e.toEquiv] at h2
  rw [← hT, ← hT', h1, h2]

theorem map_D_eq : (s.h.D.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) = s.sec.S ⊓ s.sec.J :=
  eq_of_le_of_card_ge s.map_D_le (by
    rw [s.card_secD,
      card_map_secQ_of_inf (s.h.isPGroup_S.to_le s.h.D_le_S) s.D_le_secSub s.D_inf_B0])

theorem Dt_le : s.Dt ≤ s.h.S ⊓ s.h.secG0 s.y := by
  intro w hw
  rw [mem_conjugate_iff] at hw
  have h1 : s.t * w * s.t⁻¹ ∈ s.h.S ⊓ s.h.secG0 s.y :=
    mem_inf.mpr ⟨s.h.D_le_S hw, s.D_le_G0 hw⟩
  have := (mem_normalizer_iff.mp (inv_mem s.t_norm) _).mp h1
  rwa [show s.t⁻¹ * (s.t * w * s.t⁻¹) * s.t⁻¹⁻¹ = w by group] at this

theorem Dt_le_S : s.Dt ≤ s.h.S := s.Dt_le.trans inf_le_left

theorem Dt_le_G0 : s.Dt ≤ s.h.secG0 s.y := s.Dt_le.trans inf_le_right

theorem Dt_le_secSub : s.Dt ≤ s.h.secSub s.y := s.Dt_le.trans (s.h.S_inf_le_secSub s.y)

theorem isPGroup_Dt : IsPGroup 2 s.Dt := s.h.isPGroup_S.to_le s.Dt_le_S

theorem Dt_comm_B0 {c b : X} (hc : c ∈ s.Dt) (hb : b ∈ s.h.secB0 s.y) : c * b = b * c := by
  rw [mem_conjugate_iff] at hc
  have hb' : s.t * b * s.t⁻¹ ∈ s.h.secB0 s.y := (mem_normalizer_iff.mp s.t_G0 b).mp hb
  have h1 := mem_centralizer_iff.mp (s.D_le_centralizer_B0 hc) _ hb'
  calc c * b = s.t⁻¹ * ((s.t * c * s.t⁻¹) * (s.t * b * s.t⁻¹)) * s.t := by group
    _ = s.t⁻¹ * ((s.t * b * s.t⁻¹) * (s.t * c * s.t⁻¹)) * s.t := by rw [h1]
    _ = b * c := by group

theorem Dt_inf_B0 : s.Dt ⊓ s.h.secB0 s.y = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨hwD, hwB⟩ := mem_inf.mp hw
  rw [mem_conjugate_iff] at hwD
  have hb' : s.t * w * s.t⁻¹ ∈ s.h.secB0 s.y := (mem_normalizer_iff.mp s.t_G0 w).mp hwB
  have h1 := s.D_inf_B0 ▸ mem_inf.mpr ⟨hwD, hb'⟩
  rw [mem_bot] at h1 ⊢
  calc w = s.t⁻¹ * (s.t * w * s.t⁻¹) * s.t := by group
    _ = 1 := by rw [h1]; group

theorem map_Dt_eq : (s.Dt.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) =
    conjugate (s.sec.S ⊓ s.sec.J) s.tb := by
  have h1 : s.Dt.subgroupOf (s.h.secSub s.y) =
      conjugate (s.h.D.subgroupOf (s.h.secSub s.y)) ⟨s.t, s.t_H⟩ := by
    ext w
    rw [mem_subgroupOf, mem_conjugate_iff, mem_conjugate_iff, mem_subgroupOf]
    rfl
  rw [h1, map_conjugate', s.map_D_eq, s.t_lift]

theorem mem_P_of_secQ_mem {c : ↥(s.h.secSub s.y)} (hcS : (c : X) ∈ s.h.S)
    (hcP : s.h.subQ s.y c ∈ s.sec.toHyp52.P) : (c : X) ∈ s.h.P := by
  rw [s.sec_P] at hcP
  obtain ⟨p, hp, hpc⟩ := mem_map.mp hcP
  have hpP : (p : X) ∈ s.hsec.P := (mem_inf.mp (mem_subgroupOf.mp hp)).1
  have hcp : (c : X) * (p : X)⁻¹ ∈ s.hsec.S :=
    mul_mem (s.S0_le_hr (mem_inf.mpr ⟨hcS, s.h.secSub_le_G0 s.y c.2⟩))
      (inv_mem (s.hsec.P_le_S hpP))
  obtain ⟨k, hk⟩ := s.hsec.isPGroup_S ⟨_, hcp⟩
  have hk' : ((c * p⁻¹ : ↥(s.h.secSub s.y)) : X) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h1 : s.h.subQ s.y (c * p⁻¹) = 1 := by rw [map_mul, map_inv, hpc, mul_inv_cancel]
  have h2 := secQ_eq_one_of_two (w := c * p⁻¹) hk' h1
  have hcP' : (c : X) ∈ s.hsec.P := by
    have := mul_mem (((s.h.secB0_le_B s.y).trans s.hsec.B_le_P) h2) hpP
    simpa using this
  exact Hyp52.mem_P_of_reChooseSX hcS hcP'

theorem map_Ct_eq : (s.Ct.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) =
    conjugate (s.sec.S ⊓ s.sec.J) s.tb ⊓ coreActionKernel s.sec.J := by
  apply le_antisymm
  · rw [← s.map_Dt_eq]
    refine le_inf (map_mono fun w hw => (mem_inf.mp (mem_subgroupOf.mp hw)).1) ?_
    rintro _ ⟨w, hw, rfl⟩
    have hwP : (w : X) ∈ s.h.P := (mem_inf.mp (mem_subgroupOf.mp hw)).2
    exact (mem_inf.mp (s.subQ_mem_secP hwP (s.h.secSub_le_G0 s.y w.2) w.2)).2
  · intro σ hσ
    obtain ⟨hσD, hσK⟩ := mem_inf.mp hσ
    rw [← s.map_Dt_eq] at hσD
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hσD
    have hcD : (c : X) ∈ s.Dt := mem_subgroupOf.mp hc
    have hcS : s.h.subQ s.y c ∈ s.sec.S :=
      s.subQ_mem_secS (s.Dt_le_S hcD) (s.Dt_le_G0 hcD) c.2
    have hcP' : (c : X) ∈ s.h.P :=
      s.mem_P_of_secQ_mem (s.Dt_le_S hcD) (mem_inf.mpr ⟨hcS, hσK⟩)
    exact mem_map_of_mem _ (show c ∈ s.Ct.subgroupOf _ from mem_inf.mpr ⟨hcD, hcP'⟩)

theorem isPGroup_Ct : IsPGroup 2 s.Ct := s.isPGroup_Dt.to_le inf_le_left

theorem Ct_le_secSub : s.Ct ≤ s.h.secSub s.y := inf_le_left.trans s.Dt_le_secSub

theorem Ct_le_P : s.Ct ≤ s.h.P := inf_le_right

theorem Ct_inf_B0 : s.Ct ⊓ s.h.secB0 s.y = ⊥ :=
  le_bot_iff.mp (s.Dt_inf_B0 ▸ inf_le_inf_right _ inf_le_left)

theorem Ct_comm_B0 {c b : X} (hc : c ∈ s.Ct) (hb : b ∈ s.h.secB0 s.y) : c * b = b * c :=
  s.Dt_comm_B0 (mem_inf.mp hc).1 hb

theorem two_mul_card_Ct
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    2 * Nat.card s.Ct = Nat.card s.h.D := by
  rw [← card_map_secQ_of_inf s.isPGroup_Ct s.Ct_le_secSub s.Ct_inf_B0, s.map_Ct_eq]
  have h1 := relIndex_mul_card
    (H := conjugate (s.sec.S ⊓ s.sec.J) s.tb ⊓ coreActionKernel s.sec.J)
    (K := conjugate (s.sec.S ⊓ s.sec.J) s.tb)
  rw [s.Dt_index_A10 hA, inf_eq_left.mpr inf_le_left, card_conjugate, s.card_secD] at h1
  exact h1

theorem D_comm_Dt {d e : X} (hd : d ∈ s.h.D) (he : e ∈ s.Dt) : d * e = e * d := by
  have hdG := s.D_le_secSub hd
  have heG := s.Dt_le_secSub he
  have h1 : s.h.subQ s.y ⟨d, hdG⟩ ∈ s.sec.S ⊓ s.sec.J := by
    rw [← s.map_D_eq]
    exact mem_map_of_mem _ (show (⟨d, hdG⟩ : ↥(s.h.secSub s.y)) ∈ s.h.D.subgroupOf _ from hd)
  have h2 : s.h.subQ s.y ⟨e, heG⟩ ∈ conjugate (s.sec.S ⊓ s.sec.J) s.tb := by
    rw [← s.map_Dt_eq]
    exact mem_map_of_mem _ (show (⟨e, heG⟩ : ↥(s.h.secSub s.y)) ∈ s.Dt.subgroupOf _ from he)
  have h3 := s.D_comm _ h1 _ h2
  have hwD : d * e * d⁻¹ * e⁻¹ ∈ s.h.D := by
    rw [show d * e * d⁻¹ * e⁻¹ = d * (e * d⁻¹ * e⁻¹) by group]
    exact mul_mem hd (s.h.sec8_conj_mem_D (s.Dt_le_S he) (inv_mem hd))
  set w : ↥(s.h.secSub s.y) := ⟨d, hdG⟩ * ⟨e, heG⟩ * ⟨d, hdG⟩⁻¹ * ⟨e, heG⟩⁻¹ with hw
  have hw1 : s.h.subQ s.y w = 1 := by
    rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, h3]
    group
  obtain ⟨k, hk⟩ := s.h.isPGroup_S ⟨_, s.h.D_le_S hwD⟩
  have hk' : (w : X) ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa [hw] using this
  have h4 : (w : X) ∈ s.h.D ⊓ s.h.secB0 s.y := mem_inf.mpr ⟨hwD, secQ_eq_one_of_two hk' hw1⟩
  rw [s.D_inf_B0, mem_bot] at h4
  have h5 : d * e * d⁻¹ * e⁻¹ = 1 := h4
  calc d * e = d * e * d⁻¹ * e⁻¹ * (e * d) := by group
    _ = e * d := by rw [h5, one_mul]

abbrev Cp : Subgroup X := (s.h.D ⊔ s.Dt) ⊓ s.h.P

theorem D_sup_Dt_le_S : s.h.D ⊔ s.Dt ≤ s.h.S := sup_le s.h.D_le_S s.Dt_le_S

theorem D_sup_Dt_le_G0 : s.h.D ⊔ s.Dt ≤ s.h.secG0 s.y := sup_le s.D_le_G0 s.Dt_le_G0

theorem D_sup_Dt_le_secSub : s.h.D ⊔ s.Dt ≤ s.h.secSub s.y := sup_le s.D_le_secSub s.Dt_le_secSub

theorem isPGroup_Cp : IsPGroup 2 s.Cp := s.h.isPGroup_S.to_le (inf_le_left.trans s.D_sup_Dt_le_S)

theorem Cp_le_secSub : s.Cp ≤ s.h.secSub s.y := inf_le_left.trans s.D_sup_Dt_le_secSub

theorem Cp_le_P : s.Cp ≤ s.h.P := inf_le_right

theorem D_sup_Dt_inf_B0 : (s.h.D ⊔ s.Dt) ⊓ s.h.secB0 s.y = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxV, hxB⟩ := mem_inf.mp hx
  obtain ⟨d, hd, e, he, rfl⟩ := exists_mul_of_mem_sup (fun u hu v hv => s.D_comm_Dt hu hv) hxV
  have hdG := s.D_le_secSub hd
  have heG := s.Dt_le_secSub he
  have hθ : s.h.subQ s.y ⟨d, hdG⟩ * s.h.subQ s.y ⟨e, heG⟩ = 1 := by
    rw [← map_mul]
    have : (⟨d, hdG⟩ * ⟨e, heG⟩ : ↥(s.h.secSub s.y)) = ⟨d * e, mul_mem hdG heG⟩ := rfl
    rw [this]
    exact Hyp52.subQ_eq_one_of_mem_secB0 hxB
  have h1 : s.h.subQ s.y ⟨d, hdG⟩ ∈ s.sec.S ⊓ s.sec.J := by
    rw [← s.map_D_eq]
    exact mem_map_of_mem _ (show (⟨d, hdG⟩ : ↥(s.h.secSub s.y)) ∈ s.h.D.subgroupOf _ from hd)
  have h2 : s.h.subQ s.y ⟨e, heG⟩ ∈ conjugate (s.sec.S ⊓ s.sec.J) s.tb := by
    rw [← s.map_Dt_eq]
    exact mem_map_of_mem _ (show (⟨e, heG⟩ : ↥(s.h.secSub s.y)) ∈ s.Dt.subgroupOf _ from he)
  have hde : s.h.subQ s.y ⟨d, hdG⟩ = (s.h.subQ s.y ⟨e, heG⟩)⁻¹ := eq_inv_of_mul_eq_one_left hθ
  have h3 : s.h.subQ s.y ⟨d, hdG⟩ ∈ (s.sec.S ⊓ s.sec.J) ⊓ conjugate (s.sec.S ⊓ s.sec.J) s.tb :=
    mem_inf.mpr ⟨h1, hde ▸ inv_mem h2⟩
  rw [s.D_inf, mem_bot] at h3
  have h4 : s.h.subQ s.y ⟨e, heG⟩ = 1 := by
    rw [h3, eq_comm, inv_eq_one] at hde
    exact hde
  obtain ⟨k, hk⟩ := s.h.isPGroup_S ⟨d, s.h.D_le_S hd⟩
  obtain ⟨m, hm⟩ := s.h.isPGroup_S ⟨e, s.Dt_le_S he⟩
  have hd1 : d ∈ s.h.secB0 s.y :=
    secQ_eq_one_of_two (w := ⟨d, hdG⟩) (k := k) (by simpa using congrArg Subtype.val hk) h3
  have he1 : e ∈ s.h.secB0 s.y :=
    secQ_eq_one_of_two (w := ⟨e, heG⟩) (k := m) (by simpa using congrArg Subtype.val hm) h4
  have hd' := s.D_inf_B0 ▸ mem_inf.mpr ⟨hd, hd1⟩
  have he' := s.Dt_inf_B0 ▸ mem_inf.mpr ⟨he, he1⟩
  rw [mem_bot] at hd' he'
  rw [hd', he', one_mul]
  exact one_mem _

theorem Cp_inf_B0 : s.Cp ⊓ s.h.secB0 s.y = ⊥ :=
  le_bot_iff.mp (s.D_sup_Dt_inf_B0 ▸ inf_le_inf_right _ inf_le_left)

theorem Cp_comm_B0 {c b : X} (hc : c ∈ s.Cp) (hb : b ∈ s.h.secB0 s.y) : c * b = b * c := by
  obtain ⟨d, hd, e, he, rfl⟩ :=
    exists_mul_of_mem_sup (fun u hu v hv => s.D_comm_Dt hu hv) (mem_inf.mp hc).1
  rw [mul_assoc, s.Dt_comm_B0 he hb, ← mul_assoc, s.D_comm_P hd (s.B0_le_P hb), mul_assoc]

theorem map_Cp_eq : (s.Cp.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) =
    (s.sec.S ⊓ generalizedFitting (s.h.subQuot s.y)) ⊓ coreActionKernel s.sec.J := by
  have hV : ((s.h.D ⊔ s.Dt).subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) =
      s.sec.S ⊓ generalizedFitting (s.h.subQuot s.y) := by
    rw [subgroupOf_sup s.D_le_secSub s.Dt_le_secSub, Subgroup.map_sup, s.map_D_eq, s.map_Dt_eq,
      s.D_sup]
  apply le_antisymm
  · rw [← hV]
    refine le_inf (map_mono fun w hw => (mem_inf.mp (mem_subgroupOf.mp hw)).1) ?_
    rintro _ ⟨w, hw, rfl⟩
    have hwP : (w : X) ∈ s.h.P := (mem_inf.mp (mem_subgroupOf.mp hw)).2
    exact (mem_inf.mp (s.subQ_mem_secP hwP (s.h.secSub_le_G0 s.y w.2) w.2)).2
  · intro σ hσ
    obtain ⟨hσV, hσK⟩ := mem_inf.mp hσ
    rw [← hV] at hσV
    obtain ⟨c, hc, rfl⟩ := mem_map.mp hσV
    have hcV : (c : X) ∈ s.h.D ⊔ s.Dt := mem_subgroupOf.mp hc
    have hcS : s.h.subQ s.y c ∈ s.sec.S := (mem_inf.mp (hV ▸ mem_map_of_mem _ hc)).1
    have hcP' : (c : X) ∈ s.h.P :=
      s.mem_P_of_secQ_mem (s.D_sup_Dt_le_S hcV) (mem_inf.mpr ⟨hcS, hσK⟩)
    exact mem_map_of_mem _ (show c ∈ s.Cp.subgroupOf _ from mem_inf.mpr ⟨hcV, hcP'⟩)

theorem two_mul_card_Cp
    (hA : ¬ Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    2 * Nat.card s.Cp = Nat.card s.h.D := by
  rw [← card_map_secQ_of_inf s.isPGroup_Cp s.Cp_le_secSub s.Cp_inf_B0, s.map_Cp_eq, s.Cp_card hA,
    s.card_secD]

theorem isCyclic_Cp
    (hA : ¬ Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    IsCyclic s.Cp := by
  have hc := s.Cp_cyclic hA
  rw [← s.map_Cp_eq] at hc
  have hinj : Function.Injective
      ((s.h.subQ s.y).subgroupMap (s.Cp.subgroupOf (s.h.secSub s.y))) := by
    intro v w hvw
    exact Subtype.ext (secQ_injOn s.isPGroup_Cp s.Cp_inf_B0 v.2 w.2 (congrArg Subtype.val hvw))
  let e1 := MulEquiv.ofBijective _ ⟨hinj, (s.h.subQ s.y).subgroupMap_surjective
    (s.Cp.subgroupOf (s.h.secSub s.y))⟩
  let e2 := subgroupOfEquivOfLe s.Cp_le_secSub
  exact isCyclic_of_surjective (e1.symm.trans e2).toMonoidHom (MulEquiv.surjective _)

theorem inf_genFitting_le_map_S0 : s.sec.S ⊓ generalizedFitting (s.h.subQuot s.y) ≤
    (s.h.S.subgroupOf (s.h.secSub s.y)).map (s.h.subQ s.y) := by
  rw [← s.D_sup, ← s.map_Dt_eq, ← s.map_D_eq]
  refine sup_le (map_mono fun w hw => ?_) (map_mono fun w hw => ?_)
  · exact s.h.D_le_S (mem_subgroupOf.mp hw)
  · exact s.Dt_le_S (mem_subgroupOf.mp hw)

end Setting3

end Eight2

end CFSG.ComponentClassification.GSThmB
