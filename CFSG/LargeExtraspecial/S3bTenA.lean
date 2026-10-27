module

public import CFSG.LargeExtraspecial.OrthoF2Radical
public import CFSG.LargeExtraspecial.S3Two
public import CFSG.LargeExtraspecial.S3bConj

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_mul)

theorem exists_mem_not_mem_finset_of_card_lt {X : Type*} [Group X] {H : Subgroup X} [Finite H]
    (F : Finset X) (h : F.card < Nat.card H) : ∃ x ∈ H, x ∉ F := by
  by_contra hc
  push Not at hc
  have hle : ((H : Set X)).ncard ≤ (F : Set X).ncard :=
    Set.ncard_le_ncard (fun x hx => hc x hx) (Finset.finite_toSet F)
  rw [← Nat.card_coe_set_eq, Set.ncard_coe_finset] at hle
  change Nat.card H ≤ F.card at hle
  omega

namespace Setting

variable {G : Type*} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem commutator_mem_QG_inf_Qa_of_mem_L0 {g y v : G} (hy : y ∈ S.L0 g) (hv : v ∈ S.QG)
    (hva : v * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * v) :
    y * v * y⁻¹ * v⁻¹ ∈ S.QG ⊓ S.Qa g := by
  set T := S.conjBy g
  have hvT : v ∈ T.M := T.mem_M_iff.mpr hva
  refine ⟨S.commutator_mem_QG (S.L0_le_M g hy) hv, ?_⟩
  have h1 : v * y⁻¹ * v⁻¹ ∈ T.QG := T.conj_mem_QG hvT (T.QG.inv_mem hy.1)
  have := T.QG.mul_mem hy.1 h1
  rwa [show y * (v * y⁻¹ * v⁻¹) = y * v * y⁻¹ * v⁻¹ by group] at this

theorem commutator_mem_QG_inf_Qa {g y v : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hy : y ∈ S.La g) (hv : v ∈ S.QG)
    (hva : v * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * v) :
    y * v * y⁻¹ * v⁻¹ ∈ S.QG ⊓ S.Qa g := by
  set X := S.QG ⊓ S.Qa g with hX
  have hzX : S.z ∈ X := ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩
  let P : G → Prop := fun y => y ∈ S.M ∧ (∀ w, y * w * y⁻¹ ∈ X ↔ w ∈ X) ∧
    ∀ v ∈ S.QG, v * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * v → y * v * y⁻¹ * v⁻¹ ∈ X
  have hQ : ∀ q ∈ S.QG, P q := by
    intro q hq
    have hconj : ∀ w ∈ S.QG, q * w * q⁻¹ = w ∨ q * w * q⁻¹ = w * S.z := fun w hw => by
      rcases S.mul_comm_or hq hw with h | h
      · left
        rw [h]
        group
      · right
        rw [h, show S.z * (w * q) * q⁻¹ = S.z * w by group, S.z_comm_QG hw]
    refine ⟨S.QG_le_M hq, fun w => ⟨fun hw => ?_, fun hw => ?_⟩, fun v hv _ => ?_⟩
    · have hwQ : w ∈ S.QG := by
        have := S.QG.mul_mem (S.QG.mul_mem (S.QG.inv_mem hq) hw.1) hq
        rwa [show q⁻¹ * (q * w * q⁻¹) * q = w by group] at this
      rcases hconj w hwQ with h | h
      · rwa [h] at hw
      · rw [h] at hw
        have := X.mul_mem hw hzX
        rwa [mul_assoc, S.z_mul_z, mul_one] at this
    · rcases hconj w hw.1 with h | h
      · rwa [h]
      · rw [h]
        exact X.mul_mem hw hzX
    · rcases S.commutator_eq_one_or_z hq hv with h | h
      · rw [h]
        exact X.one_mem
      · rw [h]
        exact hzX
  have hL : ∀ l ∈ S.L0 g, P l := by
    intro l hl
    have hlM := S.L0_le_M g hl
    refine ⟨hlM, fun w => ⟨fun hw => ⟨?_, ?_⟩, fun hw => ⟨S.conj_mem_QG hlM hw.1, ?_⟩⟩,
      fun v hv hva => S.commutator_mem_QG_inf_Qa_of_mem_L0 hl hv hva⟩
    · have := S.conj_mem_QG (S.M.inv_mem hlM) hw.1
      rwa [show l⁻¹ * (l * w * l⁻¹) * l⁻¹⁻¹ = w by group] at this
    · have := (S.Qa g).mul_mem ((S.Qa g).mul_mem ((S.Qa g).inv_mem hl.1) hw.2) hl.1
      rwa [show l⁻¹ * (l * w * l⁻¹) * l = w by group] at this
    · exact (S.Qa g).mul_mem ((S.Qa g).mul_mem hl.1 hw.2) ((S.Qa g).inv_mem hl.1)
  have hP : ∀ y ∈ S.La g, P y := by
    intro y hy
    unfold La at hy
    rw [sup_eq_closure] at hy
    induction hy using closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hQ y hy
      · exact hL y hy
    | one =>
      refine ⟨S.M.one_mem, fun w => by simp, fun v _ _ => by simp⟩
    | mul y₁ y₂ _ _ h₁ h₂ =>
      refine ⟨S.M.mul_mem h₁.1 h₂.1, fun w => ?_, fun v hv hva => ?_⟩
      · rw [show y₁ * y₂ * w * (y₁ * y₂)⁻¹ = y₁ * (y₂ * w * y₂⁻¹) * y₁⁻¹ by group, h₁.2.1,
          h₂.2.1]
      · have e : y₁ * y₂ * v * (y₁ * y₂)⁻¹ * v⁻¹ =
            y₁ * (y₂ * v * y₂⁻¹ * v⁻¹) * y₁⁻¹ * (y₁ * v * y₁⁻¹ * v⁻¹) := by group
        rw [e]
        exact X.mul_mem ((h₁.2.1 _).mpr (h₂.2.2 v hv hva)) (h₁.2.2 v hv hva)
    | inv y _ h =>
      refine ⟨S.M.inv_mem h.1, fun w => ?_, fun v hv hva => ?_⟩
      · rw [← h.2.1, show y * (y⁻¹ * w * y⁻¹⁻¹) * y⁻¹ = w by group]
      · have e : y⁻¹ * v * y⁻¹⁻¹ * v⁻¹ = y⁻¹ * (y * v * y⁻¹ * v⁻¹)⁻¹ * y⁻¹⁻¹ := by group
        rw [e, ← h.2.1, show y * (y⁻¹ * (y * v * y⁻¹ * v⁻¹)⁻¹ * y⁻¹⁻¹) * y⁻¹ =
          (y * v * y⁻¹ * v⁻¹)⁻¹ by group]
        exact X.inv_mem (h.2.2 v hv hva)
  exact (hP y hy).2.2 v hv hva

theorem sub_mem_clSub_of_mem_Lbar {g v : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {s : S.O} (hs : s ∈ S.Lbar g) (hv : v ∈ S.QG)
    (hva : v * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * v) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl v) - S.cl v ∈ S.clSub (S.QG ⊓ S.Qa g) := by
  obtain ⟨y, hy, rfl⟩ := S.mem_Lbar_iff.mp hs
  have h := S.commutator_mem_QG_inf_Qa haQ hne ((le_sup_right : S.L0 g ≤ S.La g) hy) hv hva
  rw [← S.cl_commutator y.2 hv]
  exact S.cl_mem_clSub h h.1

@[expose] noncomputable def CQa (g : G) : Subgroup G :=
  S.Qa g ⊓ centralizer ((S.QG ⊓ S.Qa g : Subgroup G) : Set G)

@[expose] noncomputable def Abar (g : G) : Subgroup S.O := ((S.CQa g).subgroupOf S.M).map S.ρ

theorem CQa_le_L0 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.CQa g ≤ S.L0 g := fun _ hx =>
  ⟨hx.1, mem_centralizer_singleton_iff.mpr
    ((mem_centralizer_iff.mp hx.2) S.z ⟨S.z_mem_QG, S.z_mem_Qa haQ hne⟩).symm⟩

omit [Finite G] in
theorem QG_inf_CQa {g : G} (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.QG ⊓ S.CQa g = S.QG ⊓ S.Qa g := by
  refine le_antisymm (fun x hx => ⟨hx.1, hx.2.1⟩) fun x hx =>
    ⟨hx.1, hx.2, mem_centralizer_iff.mpr fun y hy => S.QG_inf_Qa_comm hne hy hx⟩

theorem card_CQa_mul {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) :
    Nat.card (S.CQa g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = 2 ^ (2 * S.width + 2) := by
  set T := S.conjBy g with hT
  set X := S.QG ⊓ S.Qa g with hX
  have hXT : X ≤ T.QG := inf_le_right
  have haX : T.z ∈ X := ⟨haQ, T.z_mem_QG⟩
  have hC : S.CQa g = T.clPre (LinearMap.BilinForm.orthogonal T.q.polarBilin (T.clSub X)) :=
    T.centralizer_inf_QG_eq_clPre hXT
  have hcardX : Nat.card X = 2 * 2 ^ finrank (ZMod 2) (T.clSub X) := by
    rw [← T.card_submodule, ← T.card_clPre, T.clPre_clSub hXT haX]
  have hle : finrank (ZMod 2) (T.clSub X) ≤ finrank (ZMod 2) T.Qt := Submodule.finrank_le _
  have hdim : finrank (ZMod 2) T.Qt = 2 * S.width := by
    rw [T.finrank_Qt_eq_two_mul_width, S.width_conjBy]
  rw [hC, T.card_clPre, T.card_submodule, LinearMap.BilinForm.finrank_orthogonal T.q_nondegenerate,
    hcardX, hdim]
  rw [hdim] at hle
  have e : 2 * S.width + 2 = (2 * S.width - finrank (ZMod 2) (T.clSub X)) + 1 +
      (finrank (ZMod 2) (T.clSub X) + 1) := by omega
  rw [e, pow_add, pow_add, pow_add, pow_one]
  ring

theorem Abar_le_Lbar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    S.Abar g ≤ S.Lbar g :=
  map_mono fun _ hx => mem_subgroupOf.mpr (S.CQa_le_L0 haQ hne (mem_subgroupOf.mp hx))

theorem mem_Abar_iff {g : G} {s : S.O} :
    s ∈ S.Abar g ↔ ∃ y : S.M, (y : G) ∈ S.CQa g ∧ S.ρ y = s := by
  simp only [Abar, mem_map, mem_subgroupOf]

theorem card_Abar_mul {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    Nat.card (S.Abar g) * Nat.card (S.QG ⊓ S.Qa g : Subgroup G) = Nat.card (S.CQa g) := by
  have hCM : S.CQa g ≤ S.M := (S.CQa_le_L0 haQ hne).trans (S.L0_le_M g)
  set f : S.CQa g →* S.O := S.ρ.comp (inclusion hCM)
  have hrange : f.range = S.Abar g := by
    rw [MonoidHom.range_comp, inclusion_range]
    rfl
  have hker : f.ker = S.QG.subgroupOf (S.CQa g) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact S.ρ_eq_one_iff _
  have h := card_ker_mul_card_range f
  rw [hrange, hker, ← inf_subgroupOf_right,
    Nat.card_congr (subgroupOfEquivOfLe (inf_le_right : S.QG ⊓ S.CQa g ≤ S.CQa g)).toEquiv,
    S.QG_inf_CQa hne, mul_comm] at h
  exact h

theorem four_le_card_Abar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hle : Nat.card (S.QG ⊓ S.Qa g : Subgroup G) ≤ 2 ^ S.width) : 4 ≤ Nat.card (S.Abar g) := by
  have h1 := S.card_CQa_mul haQ
  rw [← S.card_Abar_mul haQ hne] at h1
  set c := Nat.card (S.QG ⊓ S.Qa g : Subgroup G)
  have hc : 0 < c := Nat.card_pos
  have h2 : c * c ≤ 2 ^ S.width * 2 ^ S.width := Nat.mul_le_mul hle hle
  have h3 : 2 ^ (2 * S.width + 2) = 4 * (2 ^ S.width * 2 ^ S.width) := by
    rw [← pow_add, show 2 * S.width + 2 = 2 + (S.width + S.width) by ring, pow_add]
    norm_num
  by_contra h4
  push Not at h4
  have h5 : Nat.card (S.Abar g) * c * c < 4 * (2 ^ S.width * 2 ^ S.width) := by
    calc Nat.card (S.Abar g) * c * c = Nat.card (S.Abar g) * (c * c) := by ring
      _ < 4 * (c * c) := Nat.mul_lt_mul_of_pos_right h4 (Nat.mul_pos hc hc)
      _ ≤ 4 * (2 ^ S.width * 2 ^ S.width) := Nat.mul_le_mul_left 4 h2
  omega

theorem mem_CQa_of_fix {g y : G} (hne : g * S.z * g⁻¹ ≠ S.z) (hy : y ∈ S.L0 g)
    (hfix : ∀ w ∈ S.QG ⊓ S.Qa g, (S.ρ ⟨y, S.L0_le_M g hy⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) =
      S.cl w) : y ∈ S.CQa g := by
  have hyM := S.L0_le_M g hy
  refine ⟨hy.1, mem_centralizer_iff.mpr fun w hw => ?_⟩
  have h1 := hfix w hw
  rw [S.ρ_cl _ hw.1] at h1
  rcases (S.cl_eq_cl_iff hw.1 (S.conj_mem_QG hyM hw.1)).mp h1.symm with h' | h'
  · calc w * y = y * w * y⁻¹ * y := by rw [h']
      _ = y * w := by group
  · exfalso
    rcases (S.conjBy g).commutator_eq_one_or_z hy.1 hw.2 with h'' | h''
    · rw [h', show w * S.z * w⁻¹ = S.z by rw [S.z_comm_QG hw.1]; group] at h''
      exact S.z_ne_one h''
    · rw [h', show w * S.z * w⁻¹ = S.z by rw [S.z_comm_QG hw.1]; group] at h''
      exact hne h''.symm

theorem Lbar_comm {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) {s t : S.O} (hs : s ∈ S.Lbar g)
    (ht : t ∈ S.Lbar g) : s * t = t * s := by
  have h := (S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨s, hs⟩ ⟨t, ht⟩
  exact congrArg Subtype.val h

theorem fix_cl_of_mem_Abar {g : G} {s : S.O} (hs : s ∈ S.Abar g) {w : G}
    (hw : w ∈ S.QG ⊓ S.Qa g) : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl w) = S.cl w := by
  obtain ⟨y, hy, rfl⟩ := S.mem_Abar_iff.mp hs
  rw [S.ρ_cl y hw.1]
  have h := (mem_centralizer_iff.mp hy.2) w hw
  rw [← h]
  congr 1
  group

theorem fix_of_mem_Abar {g : G} {s : S.O} (hs : s ∈ S.Abar g) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  obtain ⟨w, hw, -, rfl⟩ := S.mem_clSub_iff.mp hv
  exact S.fix_cl_of_mem_Abar hs hw

theorem sub_mem_span_of_mem_Abar {g v : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {s : S.O} (hs : s ∈ S.Abar g) (hv : v ∈ S.QG)
    (hva : v * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * v) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl v) - S.cl v ∈ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  obtain ⟨y, hy, hys⟩ := S.mem_Abar_iff.mp hs
  have hyL : (y : G) ∈ S.L0 g := S.CQa_le_L0 haQ hne hy
  set c := (y : G) * v * (y : G)⁻¹ * v⁻¹ with hc
  have hcX : c ∈ S.QG ⊓ S.Qa g := S.commutator_mem_QG_inf_Qa_of_mem_L0 hyL hv hva
  have hcl : S.cl c = (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl v) - S.cl v := by
    rw [hc, S.cl_commutator y.2 hv, hys]
  have hfix : ∀ y' ∈ S.L0 g, S.cl (y' * c * y'⁻¹) = S.cl c := by
    intro y' hy'
    set s' := S.ρ ⟨y', S.L0_le_M g hy'⟩
    have hs' : s' ∈ S.Lbar g := S.ρ_mem_Lbar hy'
    rw [← S.ρ_cl ⟨y', S.L0_le_M g hy'⟩ hcX.1, hcl]
    have hw := S.sub_mem_clSub_of_mem_Lbar haQ hne hs' hv hva
    have hcomm := S.Lbar_comm haQ hs' (S.Abar_le_Lbar haQ hne hs)
    have hsw := S.fix_of_mem_Abar hs hw
    set vt := S.cl v
    set w := (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) vt - vt
    have hsv : (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) vt = vt + w := by rw [add_sub_cancel]
    have hss : (s' : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) vt) =
        (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((s' : S.Qt ≃ₗ[ZMod 2] S.Qt) vt) := by
      rw [← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, ← Subgroup.coe_mul,
        ← Subgroup.coe_mul, hcomm]
    rw [map_sub, hss, hsv, map_add, hsw]
    abel
  rcases S.mem_of_cl_fixed_by_L0 haQ hne hcX hfix with h | h | h | h
  · rw [← hcl, h, S.cl_one]
    exact Submodule.zero_mem _
  · rw [← hcl, h]
    exact Submodule.mem_span_singleton_self _
  · rw [← hcl, h, S.cl_z]
    exact Submodule.zero_mem _
  · rw [← hcl, h, S.cl_mul S.z_mem_QG haQ, S.cl_z, zero_add]
    exact Submodule.mem_span_singleton_self _

theorem mem_pointRadical_of_mem_Abar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {s : S.O} (hs : s ∈ S.Abar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  have hsa : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
    S.mem_fixLbar.mp (S.cl_mem_fixLbar_self haQ) s (S.Abar_le_Lbar haQ hne hs)
  refine ⟨s.2, hsa, fun x hx => ?_, fun v => ?_⟩
  · obtain ⟨v, hv, rfl⟩ := S.exists_cl x
    have hva : v * (g * S.z * g⁻¹) = g * S.z * g⁻¹ * v := by
      have := (S.polar_cl_eq_zero_iff haQ hv).mp hx
      exact this.symm
    exact S.sub_mem_span_of_mem_Abar haQ hne hs hv hva
  · have h1 : polar S.q (S.cl (g * S.z * g⁻¹)) ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) v) =
        polar S.q (S.cl (g * S.z * g⁻¹)) v := by
      conv_lhs => rw [← hsa]
      exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup s.2 _ _
    rw [polar_sub_right, h1, sub_self]

theorem eichler_data_of_mem_Abar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) {s : S.O} (hs : s ∈ S.Abar g)
    (hs1 : s ≠ 1) {u : S.Qt} (hau : polar S.q (S.cl (g * S.z * g⁻¹)) u = 0)
    (hsu : (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = eichler S.q (S.cl (g * S.z * g⁻¹)) u) :
    u ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ∧ S.q u = 1 ∧
      u ∈ LinearMap.BilinForm.orthogonal S.q.polarBilin (S.clSub (S.QG ⊓ S.Qa g)) := by
  have ha0 := S.cl_conj_z_ne_zero haQ hne
  have haq := S.q_cl_conj_z haQ
  have hu : u ∉ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
    intro hu
    apply hs1
    refine Subtype.ext ?_
    rw [hsu, (eichler_eq_one_iff S.q_nondegenerate ha0 haq hau).mpr hu]
    rfl
  refine ⟨hu, ?_, ?_⟩
  · rcases zmod2_eq_zero_or_eq_one (S.q u) with h | h
    · exfalso
      obtain ⟨y, hy, rfl⟩ := S.mem_Abar_iff.mp hs
      have hyQ : (y : G) ∉ S.QG := fun h' => hs1 ((S.ρ_eq_one_iff y).mpr h')
      have hA := (eichler_type_of_not_mem_span S.q_nondegenerate ha0 haq hau hu).2.1 h
      rw [← hsu] at hA
      exact hno (S.hasTypeAInL_of_mem_L0 (S.CQa_le_L0 haQ hne hy) hyQ hA)
    · exact h
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    obtain ⟨w, hw, -, rfl⟩ := S.mem_clSub_iff.mp hx
    have h1 := S.fix_cl_of_mem_Abar hs hw
    have hwa : polar S.q (S.cl w) (S.cl (g * S.z * g⁻¹)) = 0 :=
      (S.polar_cl_eq_zero_iff hw.1 haQ).mpr (S.QG_inf_Qa_comm hne hw ⟨haQ, S.conj_z_mem_Qa g⟩)
    rw [hsu, eichler_apply_zmod2 haq hau, hwa, zero_smul, add_zero, mul_zero, add_zero,
      add_eq_left] at h1
    rw [polarBilin_apply_apply]
    rcases zmod2_eq_zero_or_eq_one (polar S.q (S.cl w) u) with h | h
    · exact h
    · rw [h, one_smul] at h1
      exact absurd h1 ha0

theorem exists_eichler_of_mem_Abar {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) {s : S.O} (hs : s ∈ S.Abar g) :
    ∃ u, polar S.q (S.cl (g * S.z * g⁻¹)) u = 0 ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) = eichler S.q (S.cl (g * S.z * g⁻¹)) u :=
  (mem_pointRadical_iff S.q_nondegenerate (S.cl_conj_z_ne_zero haQ hne) (S.q_cl_conj_z haQ)).mp
    (S.mem_pointRadical_of_mem_Abar haQ hne hs)

end Setting

end CFSG.LargeExtraspecial
