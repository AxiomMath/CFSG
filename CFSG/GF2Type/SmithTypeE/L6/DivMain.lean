module

public import CFSG.GF2Type.SmithTypeE.L6.DivOrbit
public import CFSG.GF2Type.SmithTypeE.L6.TrBase
public import CFSG.LargeExtraspecial.S14SMKDeltaBasic
public import CFSG.GF2Type.SmithTypeE.L6.IdMod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.L6

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.LMod CFSG.SmithL6
open CFSG.LargeExtraspecial.S14.SMK (Inputs10 z_not_mem_Qa mem_centralizer_of_mem_Qa mem_cMbar)
open CFSG.LargeExtraspecial.SMod20 (V)
open scoped MatrixGroups

theorem card_range_eq_index {H X : Type*} [Group H] (f : H → X) (K : Subgroup H)
    (hK : ∀ a b, f a = f b ↔ a⁻¹ * b ∈ K) : Nat.card (Set.range f) = K.index := by
  rw [Subgroup.index]
  refine Nat.card_congr (Equiv.ofBijective (fun q : H ⧸ K => (⟨Quotient.liftOn' q f
    (fun a b hab => (hK a b).mpr (QuotientGroup.leftRel_apply.mp hab)), by
      induction q using QuotientGroup.induction_on with | H a => exact ⟨a, rfl⟩⟩ :
      Set.range f)) ⟨fun q q' hqq => ?_, fun y => ?_⟩).symm
  · induction q using QuotientGroup.induction_on with | H a => ?_
    induction q' using QuotientGroup.induction_on with | H b => ?_
    have e : f a = f b := congrArg Subtype.val hqq
    exact QuotientGroup.eq.mpr ((hK a b).mp e)
  · obtain ⟨_, a, rfl⟩ := y
    exact ⟨QuotientGroup.mk a, rfl⟩

variable {G : Type} [Group G] [Finite G] {S : Setting G}

section Conj

variable (S : Setting G) (k : G)

@[expose] noncomputable def cMa : Subgroup S.M :=
  (centralizer ({k⁻¹ * S.z * k} : Set G)).subgroupOf S.M

omit [Finite G] in
theorem mem_cMa {c : S.M} : c ∈ cMa S k ↔ Commute (c : G) (k⁻¹ * S.z * k) := by
  rw [cMa, mem_subgroupOf, mem_centralizer_singleton_iff]
  exact Iff.rfl

omit [Finite G] in
theorem conj_mem_M_of_commute {b : G} (hb : Commute b (k⁻¹ * S.z * k)) :
    k * b * k⁻¹ ∈ S.M := by
  rw [S.mem_M_iff]
  calc k * b * k⁻¹ * S.z = k * (b * (k⁻¹ * S.z * k)) * k⁻¹ := by group
    _ = k * ((k⁻¹ * S.z * k) * b) * k⁻¹ := by rw [hb.eq]
    _ = S.z * (k * b * k⁻¹) := by group

@[expose] noncomputable def conjK : cMa S k →* S.M where
  toFun c := ⟨k * (c : G) * k⁻¹, conj_mem_M_of_commute S k ((mem_cMa S k).mp c.2)⟩
  map_one' := Subtype.ext (by simp)
  map_mul' c d := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit [Finite G] in
theorem coe_conjK (c : cMa S k) : (conjK S k c : G) = k * (c : G) * k⁻¹ := rfl

end Conj


section Omega

variable (S : Setting G) (k : G)

@[expose] def IsOm (b : G) : Prop :=
  IsConj S.z b ∧ b ∈ S.QG ∧ Commute b (k⁻¹ * S.z * k) ∧ b ∉ S.Qa k⁻¹

variable
  (ψ : Mbar0 S ≃* T6)

open Classical in
@[expose] noncomputable def fK (b : G) : Equiv.Perm (Fin 1953) :=
  if hb : k * b * k⁻¹ ∈ S.M then piM S ψ (rhoM S ⟨_, hb⟩) else 1

theorem fK_of_mem {b : G} (hb : k * b * k⁻¹ ∈ S.M) :
    fK S k ψ b = piM S ψ (rhoM S ⟨_, hb⟩) := by
  simp only [fK, hb, ↓reduceDIte]

theorem fK_conj (c : cMa S k) {b : G} (hb : Commute b (k⁻¹ * S.z * k)) :
    fK S k ψ ((c : G) * b * (c : G)⁻¹) =
      piM S ψ (rhoM S (conjK S k c)) * fK S k ψ b * (piM S ψ (rhoM S (conjK S k c)))⁻¹ := by
  have hb' := conj_mem_M_of_commute S k hb
  have hcb : Commute ((c : G) * b * (c : G)⁻¹) (k⁻¹ * S.z * k) := by
    have hc := (mem_cMa S k).mp c.2
    exact (hc.mul_left hb).mul_left hc.inv_left
  have e : (⟨k * ((c : G) * b * (c : G)⁻¹) * k⁻¹, conj_mem_M_of_commute S k hcb⟩ : S.M) =
      conjK S k c * ⟨k * b * k⁻¹, hb'⟩ * (conjK S k c)⁻¹ :=
    Subtype.ext (by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjK]
      group)
  rw [fK_of_mem S k ψ (conj_mem_M_of_commute S k hcb), fK_of_mem S k ψ hb', e]
  simp only [map_mul, map_inv]

omit [Finite G] in
theorem isOm_conj (c : cMa S k) {b : G} (hb : IsOm S k b) :
    IsOm S k ((c : G) * b * (c : G)⁻¹) := by
  obtain ⟨hbz, hbQ, hba, hbQa⟩ := hb
  have hc := (mem_cMa S k).mp c.2
  have hcM : (c : G) ∈ S.M := (c : S.M).2
  refine ⟨hbz.trans (isConj_iff.mpr ⟨c, rfl⟩), S.conj_mem_QG hcM hbQ,
    (hc.mul_left hba).mul_left hc.inv_left, fun h => hbQa ?_⟩
  have hcT : (c : G)⁻¹ ∈ (S.conjBy k⁻¹).M := by
    rw [mem_centralizer_singleton_iff]
    show (c : G)⁻¹ * (k⁻¹ * S.z * k⁻¹⁻¹) = k⁻¹ * S.z * k⁻¹⁻¹ * (c : G)⁻¹
    rw [inv_inv]
    exact hc.inv_left.eq
  have := (S.conjBy k⁻¹).conj_mem_QG hcT h
  rwa [show (c : G)⁻¹ * ((c : G) * b * (c : G)⁻¹) * (c : G)⁻¹⁻¹ = b by group] at this

end Omega


theorem card_conj_orbit {H P : Type*} [Group H] [Group P] (σ : H →* P) (F : P) :
    Nat.card (Set.range fun c : H => σ c * F * (σ c)⁻¹) =
      ((centralizer ({F} : Set P)).comap σ).index := by
  refine card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, mem_centralizer_singleton_iff, map_mul, map_inv]
  constructor
  · intro h
    calc (σ a)⁻¹ * σ b * F = (σ a)⁻¹ * (σ b * F * (σ b)⁻¹) * σ b := by group
      _ = (σ a)⁻¹ * (σ a * F * (σ a)⁻¹) * σ b := by rw [h]
      _ = F * ((σ a)⁻¹ * σ b) := by group
  · intro h
    calc σ a * F * (σ a)⁻¹ = σ a * (F * ((σ a)⁻¹ * σ b)) * (σ b)⁻¹ := by group
      _ = σ a * ((σ a)⁻¹ * σ b * F) * (σ b)⁻¹ := by rw [h]
      _ = σ b * F * (σ b)⁻¹ := by group

theorem card_perm_orbit {H X : Type*} [Group H] (τ : H →* Equiv.Perm X) (x : X) :
    Nat.card (Set.range fun c : H => τ c x) =
      ((MulAction.stabilizer (Equiv.Perm X) x).comap τ).index := by
  refine card_range_eq_index _ _ fun a b => ?_
  rw [mem_comap, MulAction.mem_stabilizer_iff, map_mul, map_inv, Equiv.Perm.smul_def,
    Equiv.Perm.mul_apply]
  constructor
  · intro h
    rw [← h, perm_inv_apply_self]
  · intro h
    calc τ a x = τ a ((τ a)⁻¹ (τ b x)) := by rw [h]
      _ = τ b x := perm_apply_inv_self _ _

section Main

variable
  [IsSimpleGroup G] (I : Inputs10) {ψ : Mbar0 S ≃* T6} {φ : S.Qt ≃ₗ[ZMod 2] V}

omit [IsSimpleGroup G] in
theorem fK_mul_z {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG) {b : G}
    (hb : Commute b (k⁻¹ * S.z * k)) : fK S k ψ (b * S.z) = fK S k ψ b := by
  have hza : Commute S.z (k⁻¹ * S.z * k) := by
    show S.z * (k⁻¹ * S.z * k) = k⁻¹ * S.z * k * S.z
    have h1 := conj_mem_M_of_commute S k (show Commute (S.z : G) (k⁻¹ * S.z * k) from by
      rw [Commute, SemiconjBy]
      have : k * S.z * k⁻¹ * S.z = S.z * (k * S.z * k⁻¹) := (S.z_comm (S.QG_le_M hvQ))
      calc S.z * (k⁻¹ * S.z * k) = k⁻¹ * (k * S.z * k⁻¹ * S.z) * k := by group
        _ = k⁻¹ * (S.z * (k * S.z * k⁻¹)) * k := by rw [this]
        _ = k⁻¹ * S.z * k * S.z := by group)
    have : k * S.z * k⁻¹ * S.z = S.z * (k * S.z * k⁻¹) := (S.z_comm (S.QG_le_M hvQ))
    calc S.z * (k⁻¹ * S.z * k) = k⁻¹ * (k * S.z * k⁻¹ * S.z) * k := by group
      _ = k⁻¹ * (S.z * (k * S.z * k⁻¹)) * k := by rw [this]
      _ = k⁻¹ * S.z * k * S.z := by group
  have hbz : Commute (b * S.z) (k⁻¹ * S.z * k) := hb.mul_left hza
  have hb' := conj_mem_M_of_commute S k hb
  have hvM : k * S.z * k⁻¹ ∈ S.M := S.QG_le_M hvQ
  have e : (⟨k * (b * S.z) * k⁻¹, conj_mem_M_of_commute S k hbz⟩ : S.M) =
      ⟨k * b * k⁻¹, hb'⟩ * ⟨k * S.z * k⁻¹, hvM⟩ := Subtype.ext (by
    simp only [Subgroup.coe_mul]
    group)
  have hv1 : rhoM S ⟨k * S.z * k⁻¹, hvM⟩ = 1 := Subtype.ext ((S.ρ_eq_one_iff _).mpr hvQ)
  rw [fK_of_mem S k ψ (conj_mem_M_of_commute S k hbz), fK_of_mem S k ψ hb', e, map_mul, hv1,
    mul_one]

omit [IsSimpleGroup G] in
theorem meetCard_eq_one_iff {i j : ℕ} (hi : i < 1395) (hj : j < 1395) :
    meetCard i j = 1 ↔ ¬ (distB i j ≤ 1) ∧ distB i j ≠ 3 := by
  rcases (dist_parts hi hj).1 with h | h | h | h <;> simp [distB, h]

include I in
theorem commute_not_mem_Qa_iff (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {k h' : G}
    (haQ : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.QG) (hane : k⁻¹ * S.z * k⁻¹⁻¹ ≠ S.z)
    (hbQ : h' * S.z * h'⁻¹ ∈ S.QG) (hbne : h' * S.z * h'⁻¹ ≠ S.z) :
    (Commute (h' * S.z * h'⁻¹) (k⁻¹ * S.z * k⁻¹⁻¹) ∧ h' * S.z * h'⁻¹ ∉ S.Qa k⁻¹) ↔
      meetCard (planeOf S ψ k⁻¹) (planeOf S ψ h') = 1 := by
  have hc := commute_iff_not_opp I ψ hw haQ hane hbQ hbne haQ hane
  have hq := mem_Qa_iff_adjW I hφ hw haQ hane hbQ hbne
  have h3 : distB (planeOf S ψ k⁻¹) (planeOf S ψ h') ≠ 3 ↔
      ¬ Opp (planeOf S ψ h') (planeOf S ψ k⁻¹) := by
    rw [ne_eq, distB_eq_three_iff (planeOf S ψ k⁻¹).2 (planeOf S ψ h').2]
    unfold Opp
    rw [disjoint_comm]
  rw [meetCard_eq_one_iff (planeOf S ψ k⁻¹).2 (planeOf S ψ h').2,
    ← adjW_iff (planeOf S ψ k⁻¹).2 (planeOf S ψ h').2, h3, Commute, SemiconjBy, hc, ← hq]
  exact and_comm

omit [IsSimpleGroup G] in
theorem fK_mem_UA (hw : S.width = 10) {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG)
    (hvne : k * S.z * k⁻¹ ≠ S.z) {b : G} (hb : IsOm S k b) :
    fK S k ψ b ∈ UA (planeOf S ψ k).val ∧ fK S k ψ b ≠ 1 := by
  have hbM := conj_mem_M_of_commute S k hb.2.2.1
  have hL : k * b * k⁻¹ ∈ S.L0 k :=
    ⟨(SME.mem_Qa_iff S k _).mpr (by
      rw [show k⁻¹ * (k * b * k⁻¹) * k = b by group]
      exact hb.2.1), hbM⟩
  rw [fK_of_mem S k ψ hbM]
  refine ⟨?_, fun hb1 => ?_⟩
  · rw [← planeOf_spec ψ hw hvQ hvne]
    exact ⟨rhoM S ⟨_, hbM⟩, mem_subgroupOf.mpr ⟨⟨_, hbM⟩, mem_subgroupOf.mpr hL, rfl⟩, rfl⟩
  · rw [← map_one (piM S ψ)] at hb1
    have h2 := congrArg Subtype.val (piM_injective ψ hb1)
    have h3 : k * b * k⁻¹ ∈ S.QG := (S.ρ_eq_one_iff _).mp h2
    apply hb.2.2.2
    rw [SME.mem_Qa_iff, inv_inv]
    exact h3

include I in
theorem fK_eq_conj_of_planeHom (hw : S.width = 10) {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG)
    {c₀ : G} (hx'Q : c₀ * S.z * c₀⁻¹ ∈ S.QG) (hx'ne : c₀ * S.z * c₀⁻¹ ≠ S.z)
    (hx'a : Commute (c₀ * S.z * c₀⁻¹) (k⁻¹ * S.z * k)) (c : cMa S k) {h' : G}
    (hbQ : h' * S.z * h'⁻¹ ∈ S.QG) (hbne : h' * S.z * h'⁻¹ ≠ S.z)
    (hpl : planeHom S ψ (rhoM S (c : S.M)) (planeOf S ψ c₀) = planeOf S ψ h') :
    fK S k ψ (h' * S.z * h'⁻¹) = piM S ψ (rhoM S (conjK S k c)) *
      fK S k ψ (c₀ * S.z * c₀⁻¹) * (piM S ψ (rhoM S (conjK S k c)))⁻¹ := by
  obtain ⟨y, hy⟩ : ∃ y : G, y = ((c : S.M) : G) := ⟨_, rfl⟩
  have hyM : y ∈ S.M := hy ▸ (c : S.M).2
  have hya : Commute y (k⁻¹ * S.z * k) := hy ▸ (mem_cMa S k).mp c.2
  have e1 : y * c₀ * S.z * (y * c₀)⁻¹ = y * (c₀ * S.z * c₀⁻¹) * y⁻¹ := by group
  have hcx : y * c₀ * S.z * (y * c₀)⁻¹ ∈ S.QG := by
    rw [e1]
    exact S.conj_mem_QG hyM hx'Q
  have hcxne : y * c₀ * S.z * (y * c₀)⁻¹ ≠ S.z := by
    intro h
    apply hx'ne
    have e : c₀ * S.z * c₀⁻¹ = y⁻¹ * (y * c₀ * S.z * (y * c₀)⁻¹) * y := by group
    rw [e, h, mul_assoc, ← S.z_comm hyM, ← mul_assoc, inv_mul_cancel, one_mul]
  have hpl' : planeOf S ψ (y * c₀) = planeOf S ψ h' := by
    have := planeOf_mul ψ hw hx'Q hx'ne (c : S.M)
    rw [← hy] at this
    rw [this, hpl]
  have hcl := cl_eq_of_planeOf_eq ψ I hw hbQ hbne hcx hcxne hpl'
  have hcx_a : Commute (y * c₀ * S.z * (y * c₀)⁻¹) (k⁻¹ * S.z * k) := by
    rw [e1]
    exact (hya.mul_left hx'a).mul_left hya.inv_left
  have hconj := fK_conj S k ψ c hx'a
  rw [← hy, ← e1] at hconj
  rw [← hconj]
  rcases (S.cl_eq_cl_iff hcx hbQ).mp hcl with h2 | h2
  · rw [h2]
  · rw [h2, fK_mul_z hvQ hcx_a]

include I in
theorem exists_cMa_of_mem_PA (hw : S.width = 10) {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG)
    (hvne : k * S.z * k⁻¹ ≠ S.z) {g' : Equiv.Perm (Fin 1953)}
    (hg' : g' ∈ PA (planeOf S ψ k).val) :
    ∃ c : cMa S k, piM S ψ (rhoM S (conjK S k c)) = g' := by
  obtain ⟨m, h0, hm⟩ := exists_rhoM_mem_Mbar0 ψ ⟨g', (Subgroup.mem_inf.1 hg').1⟩
  have hst := (stab_eq I ψ hw hvQ hvne ⟨rhoM S m, h0⟩).mpr (by rw [hm]; exact hg')
  have hfix := (mem_cMbar.mp hst).2
  obtain ⟨m', hm'v, hm'm⟩ := exists_commute_rhoM_eq S hvQ hvne m hfix
  have hcM : k⁻¹ * (m' : G) * k ∈ S.M := by
    rw [mem_centralizer_singleton_iff]
    have := (SmithGraph.commute_conj_iff k (m' : G) (k * S.z * k⁻¹)).mpr hm'v
    rw [show k⁻¹ * (k * S.z * k⁻¹) * k = S.z by group] at this
    exact this.eq
  have hca : Commute (k⁻¹ * (m' : G) * k) (k⁻¹ * S.z * k) :=
    (SmithGraph.commute_conj_iff k (m' : G) S.z).mpr
      (mem_centralizer_singleton_iff.mp m'.2)
  refine ⟨⟨⟨_, hcM⟩, (mem_cMa S k).mpr hca⟩, ?_⟩
  have e : conjK S k ⟨⟨_, hcM⟩, (mem_cMa S k).mpr hca⟩ = m' := Subtype.ext (by
    show k * (k⁻¹ * (m' : G) * k) * k⁻¹ = m'
    group)
  rw [e, hm'm]
  have := piM_of_mem ψ ⟨rhoM S m, h0⟩
  rw [hm] at this
  exact this

include I in
theorem piM_eq_tvP_of_mem_Qa (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) {k : G}
    (hv : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa g) :
    ∃ p : Fin 1953, p ∈ wPlane (planeOf S ψ k) ∧
      piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) = tvP p := by
  have hvQ : k * S.z * k⁻¹ ∈ S.QG := hv.1
  have hvne : k * S.z * k⁻¹ ≠ S.z := fun h => z_not_mem_Qa S hxQ (h ▸ hv.2)
  have hzQv : S.z ∈ S.Qa k := S.z_mem_Qa hvQ hvne
  have hka : k⁻¹ * S.z * k⁻¹⁻¹ = k⁻¹ * S.z * k := by rw [inv_inv]
  have haQ : k⁻¹ * S.z * k⁻¹⁻¹ ∈ S.QG := by
    rw [hka]
    exact (SME.mem_Qa_iff S k S.z).mp hzQv
  have hane : k⁻¹ * S.z * k⁻¹⁻¹ ≠ S.z := by
    intro h
    apply hvne
    calc k * S.z * k⁻¹ = k * (k⁻¹ * S.z * k⁻¹⁻¹) * k⁻¹ := by rw [h]
      _ = S.z := by group
  have hzQa : S.z ∈ S.Qa k⁻¹ := S.z_mem_Qa haQ hane
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : G, c₀ = k⁻¹ * g := ⟨_, rfl⟩
  have hx' : c₀ * S.z * c₀⁻¹ = k⁻¹ * (g * S.z * g⁻¹) * k := by rw [hc₀]; group
  have hvx : k * S.z * k⁻¹ ≠ g * S.z * g⁻¹ := fun h => hxQ (h ▸ hvQ)
  have hx'Q : c₀ * S.z * c₀⁻¹ ∈ S.QG := by
    rw [hx']
    exact SME.mem_Qa_symm S ((SME.mem_Qa_iff S g _).mp hv.2) hvx
  have hzx : Commute (g * S.z * g⁻¹) S.z := mem_centralizer_singleton_iff.mp hxM
  have hx'a : Commute (c₀ * S.z * c₀⁻¹) (k⁻¹ * S.z * k) := by
    rw [hx']
    exact (SmithGraph.commute_conj_iff k _ _).mpr hzx
  have hx'Qa : c₀ * S.z * c₀⁻¹ ∉ S.Qa k⁻¹ := by
    intro h
    apply hxQ
    have := (SME.mem_Qa_iff S k⁻¹ _).mp h
    rwa [hx', show k⁻¹⁻¹ * (k⁻¹ * (g * S.z * g⁻¹) * k) * k⁻¹ = g * S.z * g⁻¹ by group] at this
  have hx'ne : c₀ * S.z * c₀⁻¹ ≠ S.z := fun h => hx'Qa (by rw [h]; exact hzQa)
  have hx'Om : IsOm S k (c₀ * S.z * c₀⁻¹) := ⟨isConj_iff.mpr ⟨c₀, rfl⟩, hx'Q, hx'a, hx'Qa⟩
  have hF₀ : fK S k ψ (c₀ * S.z * c₀⁻¹) = piM S ψ (rhoM S ⟨g * S.z * g⁻¹, hxM⟩) := by
    have e : (⟨k * (c₀ * S.z * c₀⁻¹) * k⁻¹, conj_mem_M_of_commute S k hx'a⟩ : S.M) =
        ⟨g * S.z * g⁻¹, hxM⟩ := Subtype.ext (by
      show k * (c₀ * S.z * c₀⁻¹) * k⁻¹ = g * S.z * g⁻¹
      rw [hx']
      group)
    rw [fK_of_mem S k ψ (conj_mem_M_of_commute S k hx'a), e]
  have hmeet : ∀ {h' : G}, h' * S.z * h'⁻¹ ∈ S.QG → IsOm S k (h' * S.z * h'⁻¹) →
      meetCard (planeOf S ψ k⁻¹) (planeOf S ψ h') = 1 := by
    intro h' hbQ hb
    have hbne : h' * S.z * h'⁻¹ ≠ S.z := fun h => hb.2.2.2 (by rw [h]; exact hzQa)
    refine (commute_not_mem_Qa_iff I hφ hw haQ hane hbQ hbne).mp ⟨?_, hb.2.2.2⟩
    rw [hka]
    exact hb.2.2.1
  have hx'meet := hmeet hx'Q hx'Om
  have hO : fK S k ψ '' {b | IsOm S k b} ⊆ (UA (planeOf S ψ k).val : Set _) := by
    rintro _ ⟨b, hb, rfl⟩
    exact (fK_mem_UA hw hvQ hvne hb).1
  have h1 : (1 : Equiv.Perm (Fin 1953)) ∉ fK S k ψ '' {b | IsOm S k b} := by
    rintro ⟨b, hb, hb1⟩
    exact (fK_mem_UA hw hvQ hvne hb).2 hb1
  have hne : (fK S k ψ '' {b | IsOm S k b}).Nonempty := ⟨_, _, hx'Om, rfl⟩
  have hinv : ∀ g' ∈ PA (planeOf S ψ k).val, ∀ u ∈ fK S k ψ '' {b | IsOm S k b},
      g' * u * g'⁻¹ ∈ fK S k ψ '' {b | IsOm S k b} := by
    rintro g' hg' _ ⟨b, hb, rfl⟩
    obtain ⟨c, hc⟩ := exists_cMa_of_mem_PA I hw hvQ hvne hg'
    rw [← hc, ← fK_conj S k ψ c hb.2.2.1]
    exact ⟨_, isOm_conj S k c hb, rfl⟩
  have hcomm : ∀ c : cMa S k, Commute ((c : S.M) : G) (k⁻¹ * S.z * k⁻¹⁻¹) := fun c => by
    rw [hka]
    exact (mem_cMa S k).mp c.2
  have hdvd : (fK S k ψ '' {b | IsOm S k b}).ncard ∣ 784 := by
    set σ : cMa S k →* Equiv.Perm (Fin 1953) := (piM S ψ).comp ((rhoM S).comp (conjK S k))
      with hσ
    set τ : cMa S k →* Equiv.Perm (Fin 1395) :=
      (planeHom S ψ).comp ((rhoM S).comp (cMa S k).subtype) with hτ
    have hr1 : (Set.range fun c : cMa S k => σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) * (σ c)⁻¹) =
        fK S k ψ '' {b | IsOm S k b} := by
      ext u
      constructor
      · rintro ⟨c, rfl⟩
        exact ⟨_, isOm_conj S k c hx'Om, fK_conj S k ψ c hx'a⟩
      · rintro ⟨b, hb, rfl⟩
        obtain ⟨h', rfl⟩ := isConj_iff.mp hb.1
        have hbQ := hb.2.1
        have hbne : h' * S.z * h'⁻¹ ≠ S.z := fun h => hb.2.2.2 (by rw [h]; exact hzQa)
        obtain ⟨c, hc, hpl⟩ := exists_commute_planeHom ψ I hw haQ hane
          (hx'meet.trans (hmeet hbQ hb).symm)
        have hc' : c ∈ cMa S k := (mem_cMa S k).mpr (by rw [← hka]; exact hc)
        exact ⟨⟨c, hc'⟩, (fK_eq_conj_of_planeHom I hw hvQ hx'Q hx'ne hx'a ⟨c, hc'⟩ hbQ hbne
          hpl).symm⟩
    have hr2 : (Set.range fun c : cMa S k => τ c (planeOf S ψ c₀)) =
        {j : Fin 1395 | meetCard (planeOf S ψ k⁻¹) j.val = 1} := by
      ext j
      constructor
      · rintro ⟨c, rfl⟩
        show meetCard (planeOf S ψ k⁻¹) (planeHom S ψ (rhoM S (c : S.M)) (planeOf S ψ c₀)) = 1
        have := meetCard_planeHom ψ (rhoM S (c : S.M)) (planeOf S ψ k⁻¹) (planeOf S ψ c₀)
        rw [planeHom_planeOf_of_commute ψ hw haQ hane (c : S.M) (hcomm c)] at this
        rw [this, hx'meet]
      · intro hj
        obtain ⟨c, hc, hpl⟩ := exists_commute_planeHom ψ I hw haQ hane (hx'meet.trans hj.symm)
        exact ⟨⟨c, (mem_cMa S k).mpr (by rw [← hka]; exact hc)⟩, hpl⟩
    have hK : (MulAction.stabilizer (Equiv.Perm (Fin 1395)) (planeOf S ψ c₀)).comap τ ≤
        (centralizer ({fK S k ψ (c₀ * S.z * c₀⁻¹)} : Set _)).comap σ := by
      intro c hc
      rw [mem_comap, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def] at hc
      have h : fK S k ψ (c₀ * S.z * c₀⁻¹) = σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) * (σ c)⁻¹ :=
        fK_eq_conj_of_planeHom I hw hvQ hx'Q hx'ne hx'a c hx'Q hx'ne hc
      rw [mem_comap, mem_centralizer_singleton_iff]
      show σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) = fK S k ψ (c₀ * S.z * c₀⁻¹) * σ c
      calc σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) =
          (σ c * fK S k ψ (c₀ * S.z * c₀⁻¹) * (σ c)⁻¹) * σ c := by group
        _ = fK S k ψ (c₀ * S.z * c₀⁻¹) * σ c := by rw [← h]
    have e1 := card_conj_orbit σ (fK S k ψ (c₀ * S.z * c₀⁻¹))
    rw [hr1] at e1
    have e2 := card_perm_orbit τ (planeOf S ψ c₀)
    rw [hr2] at e2
    rw [← Nat.card_coe_set_eq, e1]
    have h336 := ncard_meetCard_one (planeOf S ψ k⁻¹).2
    rw [← Nat.card_coe_set_eq, e2] at h336
    rw [← h336]
    exact Subgroup.index_dvd_of_le hK
  have hrank := orbit_rank_one (planeOf S ψ k).2 hO h1 hne hinv hdvd
  have hF₀O : fK S k ψ (c₀ * S.z * c₀⁻¹) ∈ fK S k ψ '' {b | IsOm S k b} := ⟨_, hx'Om, rfl⟩
  rw [hrank] at hF₀O
  obtain ⟨p, hp, hpF⟩ := hF₀O
  exact ⟨p, hp, by rw [← hF₀, hpF]⟩

include I in
theorem acts_tv_of_mem_Qa (hφ : IsModelPhi S ψ φ) (hw : S.width = 10) {g : G}
    (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG) {k : G}
    (hv : k * S.z * k⁻¹ ∈ S.QG ⊓ S.Qa g) :
    ∃ p : Fin 1953, p ∈ wPlane (planeOf S ψ k) ∧
      Phi S φ ⟨g * S.z * g⁻¹, hxM⟩ = tvEquiv p.val := by
  have hvne : k * S.z * k⁻¹ ≠ S.z := fun h => z_not_mem_Qa S hxQ (h ▸ hv.2)
  obtain ⟨p, hp, hpx⟩ := piM_eq_tvP_of_mem_Qa I hφ hw hxM hxQ hv
  obtain ⟨m₀, hm₀⟩ := exists_piM_eq (S := S) ψ (tvP_mem p)
  have h1 : (m₀ : S.Mbar) = rhoM S ⟨g * S.z * g⁻¹, hxM⟩ :=
    piM_injective ψ (by rw [hm₀, hpx])
  have h0 : rhoM S ⟨g * S.z * g⁻¹, hxM⟩ ∈ Mbar0 S := h1 ▸ m₀.2
  refine ⟨p, hp, ?_⟩
  rw [hφ.Phi_eq_rhoMod I hw hv.1 hvne _ h0]
  have e : ψ ⟨rhoM S ⟨g * S.z * g⁻¹, hxM⟩, h0⟩ = ⟨tvP p, tvP_mem p⟩ := by
    apply Subtype.ext
    rw [← piM_of_mem]
    exact hpx
  rw [e, rhoMod_tvP]

end Main

end CFSG.GF2Type.SmithTypeE.L6
