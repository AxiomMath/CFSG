module

public import CFSG.LargeExtraspecial.S14SMELocal
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GF2Type.SmithTypeE.E7.IdMod

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup QuadraticMap CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
  CFSG.GF2Type.SmithTypeE.DMod CFSG.SmithD6
open CFSG.LargeExtraspecial.S14.SMK (Inputs10)

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
    rw [← h]
    exact (τ a).symm_apply_apply x
  · intro h
    calc τ a x = τ a ((τ a)⁻¹ (τ b x)) := by rw [h]
      _ = τ b x := (τ a).apply_symm_apply _

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

@[expose] def IsOm (S : Setting G) (k b : G) : Prop :=
  IsConj S.z b ∧ b ∈ S.QG ∧ Commute b (k⁻¹ * S.z * k) ∧ b ∉ S.Qa k⁻¹

omit [Finite G] in
theorem isOm_conj (S : Setting G) (k : G) (c : cMa S k) {b : G} (hb : IsOm S k b) :
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

section Omega


@[expose] noncomputable def psiM (S : Setting G) (ψ : S.Mbar ≃* TD6) : S.M →* TD6 :=
  ψ.toMonoidHom.comp (rhoM S)

theorem psiM_apply (ψ : S.Mbar ≃* TD6) (m : S.M) : psiM S ψ m = ψ (rhoM S m) := rfl

variable (S : Setting G) (k : G) (ψ : S.Mbar ≃* TD6)

open Classical in
@[expose] noncomputable def fK (b : G) : TD6 :=
  if hb : k * b * k⁻¹ ∈ S.M then ψ (rhoM S ⟨_, hb⟩) else 1

theorem fK_of_mem {b : G} (hb : k * b * k⁻¹ ∈ S.M) :
    fK S k ψ b = ψ (rhoM S ⟨_, hb⟩) := by
  simp only [fK, hb, ↓reduceDIte]

theorem fK_conj (c : cMa S k) {b : G} (hb : Commute b (k⁻¹ * S.z * k)) :
    fK S k ψ ((c : G) * b * (c : G)⁻¹) =
      psiM S ψ (conjK S k c) * fK S k ψ b * (psiM S ψ (conjK S k c))⁻¹ := by
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
  simp only [psiM_apply, map_mul, map_inv]

theorem fK_mul_z {k : G} (hvQ : k * S.z * k⁻¹ ∈ S.QG) {b : G}
    (hb : Commute b (k⁻¹ * S.z * k)) : fK S k ψ (b * S.z) = fK S k ψ b := by
  have hza : Commute S.z (k⁻¹ * S.z * k) := by
    show S.z * (k⁻¹ * S.z * k) = k⁻¹ * S.z * k * S.z
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

end Omega

theorem exists_commute_rhoM_eq (S : Setting G) {h : G} (haQ : h * S.z * h⁻¹ ∈ S.QG)
    (hne : h * S.z * h⁻¹ ≠ S.z) (m : S.M)
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) =
      S.cl (h * S.z * h⁻¹)) :
    ∃ c : S.M, Commute (c : G) (h * S.z * h⁻¹) ∧ rhoM S c = rhoM S m := by
  set a := h * S.z * h⁻¹ with ha
  rw [S.ρ_cl m haQ] at hm
  rcases (S.cl_eq_cl_iff haQ (S.conj_mem_QG m.2 haQ)).mp hm.symm with h1 | h1
  · refine ⟨m, ?_, rfl⟩
    show (m : G) * a = a * m
    calc (m : G) * a = (m : G) * a * (m : G)⁻¹ * m := by group
      _ = a * m := by rw [h1]
  · have ha1 : a ≠ 1 := SME.ne_one_of_isConj S (isConj_iff.mpr ⟨h, rfl⟩)
    obtain ⟨q, hq, hqa⟩ := SME.exists_conj_eq_mul_z S haQ ha1 hne
    have hqM : q⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem hq)
    refine ⟨⟨q⁻¹, hqM⟩ * m, ?_, ?_⟩
    · have e1 : q⁻¹ * (a * S.z) * q = a := by rw [← hqa]; group
      show q⁻¹ * (m : G) * a = a * (q⁻¹ * m)
      calc q⁻¹ * (m : G) * a = q⁻¹ * ((m : G) * a * (m : G)⁻¹) * q * (q⁻¹ * m) := by group
        _ = q⁻¹ * (a * S.z) * q * (q⁻¹ * m) := by rw [h1]
        _ = a * (q⁻¹ * m) := by rw [e1]
    · have h1' : rhoM S ⟨q⁻¹, hqM⟩ = 1 :=
        Subtype.ext ((S.ρ_eq_one_iff _).mpr (S.QG.inv_mem hq))
      rw [map_mul, h1', one_mul]


section Planes

variable
  {φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2)} {ψ : S.Mbar ≃* TD6}

open Classical in
@[expose] noncomputable def planeOf (S : Setting G) (φ : S.Qt ≃ₗ[ZMod 2] (Fin 32 → ZMod 2))
    (g : G) : Fin 75735 :=
  if h : ∃ i : Fin 75735, φ (S.cl (g * S.z * g⁻¹)) = wtV i.val then h.choose else 0

theorem planeOf_eq_of {g : G} {i : Fin 75735} (h : φ (S.cl (g * S.z * g⁻¹)) = wtV i.val) :
    planeOf S φ g = i := by
  have hex : ∃ i : Fin 75735, φ (S.cl (g * S.z * g⁻¹)) = wtV i.val := ⟨i, h⟩
  unfold planeOf
  rw [dif_pos hex]
  exact Fin.ext (wtV_injective hex.choose.2 i.2 (hex.choose_spec.symm.trans h))

variable [IsSimpleGroup G]

theorem cl_eq_wtV_planeOf (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    φ (S.cl (g * S.z * g⁻¹)) = wtV (planeOf S φ g).val := by
  obtain ⟨i, hi⟩ := exists_weight_of_conj I hw hO hΦ haQ hne
  rw [planeOf_eq_of hi]
  exact hi

theorem planeOf_mul (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) (m : S.M) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) :
    planeOf S φ ((m : G) * g) = ψ (rhoM S m) • planeOf S φ g := by
  refine planeOf_eq_of ?_
  rw [phi_cl_mul hΦ m haQ, cl_eq_wtV_planeOf I hw hO hΦ haQ hne, rhoMod_wtV]

theorem exists_planeOf_eq (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (j : Fin 75735) :
    ∃ h : G, h * S.z * h⁻¹ ∈ S.QG ∧ h * S.z * h⁻¹ ≠ S.z ∧ planeOf S φ h = j := by
  obtain ⟨h, hQ, hne', hw'⟩ := exists_conj_with_weight_of I hw hO hΦ haQ hne j
  exact ⟨h, hQ, hne', planeOf_eq_of hw'⟩

theorem cl_eq_of_planeOf_eq (I : Inputs10) (hw : S.width = 16)
    (hO : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6))
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {g h : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hane : g * S.z * g⁻¹ ≠ S.z) (hbQ : h * S.z * h⁻¹ ∈ S.QG)
    (hbne : h * S.z * h⁻¹ ≠ S.z) (hpl : planeOf S φ g = planeOf S φ h) :
    S.cl (g * S.z * g⁻¹) = S.cl (h * S.z * h⁻¹) := by
  apply φ.injective
  rw [cl_eq_wtV_planeOf I hw hO hΦ haQ hane, cl_eq_wtV_planeOf I hw hO hΦ hbQ hbne, hpl]

omit [IsSimpleGroup G] in
theorem psi_smul_eq_iff (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m))) {h : G}
    {i : Fin 75735} (hi : φ (S.cl (h * S.z * h⁻¹)) = wtV i.val) (m : S.Mbar) :
    ψ m • i = i ↔
      ((m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹) := by
  have h1 := rhoMod_psi_apply hΦ m (S.cl (h * S.z * h⁻¹))
  rw [hi] at h1
  have h2 : rhoMod (ψ m) (wtV i.val) = wtV ((ψ m • i).val) := rhoMod_wtV (ψ m) i
  constructor
  · intro hs
    apply φ.injective
    rw [← h1, h2, hs, hi]
  · intro hs
    apply Fin.ext
    refine wtV_injective (ψ m • i).2 i.2 ?_
    rw [← h2, h1, hs, hi]

omit [IsSimpleGroup G] in
theorem smul_planeOf_of_commute {h : G} {i : Fin 75735}
    (hΦ : ∀ m : S.M, Phi S φ m = rhoMod (ψ (rhoM S m)))
    (hi : φ (S.cl (h * S.z * h⁻¹)) = wtV i.val) (haQ : h * S.z * h⁻¹ ∈ S.QG) (c : S.M)
    (hc : Commute (c : G) (h * S.z * h⁻¹)) : ψ (rhoM S c) • i = i := by
  refine (psi_smul_eq_iff hΦ hi (rhoM S c)).2 ?_
  show ((S.ρ c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (h * S.z * h⁻¹)) = S.cl (h * S.z * h⁻¹)
  rw [S.ρ_cl c haQ]
  congr 1
  calc (c : G) * (h * S.z * h⁻¹) * (c : G)⁻¹ = h * S.z * h⁻¹ * (c : G) * (c : G)⁻¹ := by
        rw [hc.eq]
    _ = h * S.z * h⁻¹ := by group

end Planes

@[expose] def Mid (i j : Fin 75735) : Prop := adjW i.val j.val = false ∧ ¬ Opp i.val j.val

section Mid


theorem mid_smul (g : TD6) (i j : Fin 75735) : Mid (g • i) (g • j) ↔ Mid i j := by
  unfold Mid
  rw [opp_smul g i j, Bool.eq_false_iff, Bool.eq_false_iff, Ne, Ne, adjW_smul_iff g i j]

structure UWInput : Prop where
  orbit_roots : ∀ (O : Set TD6), O.Nonempty → (∀ u ∈ O, u ∈ K0) → (1 : TD6) ∉ O →
    (∀ g ∈ Stab0, ∀ u ∈ O, g * u * g⁻¹ ∈ O) → O.ncard ∣ 41664 →
    (∀ u ∈ O, ∀ E : Fin 75735, ¬ Opp E.val (u • E).val) →
    ∀ u ∈ O, ∃ p : Fin 365211, (∀ x ∈ lineSet p.val, x ∈ planeSub 0) ∧
      u = ⟨tvP p, tvP_mem p⟩
  ncard_mid : {j : Fin 75735 | Mid 0 j}.ncard = 41664
  exists_mid : ∀ {j j' : Fin 75735}, Mid 0 j → Mid 0 j' → ∃ g ∈ Stab0, g • j = j'

variable (hUW : UWInput)

include hUW in
theorem ncard_mid_general (i : Fin 75735) : {j : Fin 75735 | Mid i j}.ncard = 41664 := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i 0
  have himg : (fun j : Fin 75735 => g₀ • j) '' {j | Mid i j} = {j | Mid 0 j} := by
    ext j'
    constructor
    · rintro ⟨j, hj, rfl⟩
      show Mid 0 (g₀ • j)
      rw [← hg₀]
      exact (mid_smul g₀ i j).2 hj
    · intro hj'
      refine ⟨g₀⁻¹ • j', ?_, by simp⟩
      show Mid i (g₀⁻¹ • j')
      rw [← mid_smul g₀ i, smul_inv_smul, hg₀]
      exact hj'
  rw [← hUW.ncard_mid, ← himg, Set.ncard_image_of_injective _ (MulAction.injective g₀)]

include hUW in
theorem exists_stab_mid_general {i j j' : Fin 75735} (hj : Mid i j) (hj' : Mid i j') :
    ∃ g ∈ MulAction.stabilizer TD6 i, g • j = j' := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_planes_eq i 0
  have h1 : Mid 0 (g₀ • j) := hg₀ ▸ (mid_smul g₀ i j).2 hj
  have h2 : Mid 0 (g₀ • j') := hg₀ ▸ (mid_smul g₀ i j').2 hj'
  obtain ⟨g, hg, hgj⟩ := hUW.exists_mid h1 h2
  refine ⟨g₀⁻¹ * g * g₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul, mul_smul, hg₀]
    have := MulAction.mem_stabilizer_iff.mp hg
    rw [this]
    rw [← hg₀, inv_smul_smul]
  · rw [mul_smul, mul_smul, hgj, inv_smul_smul]

end Mid

end CFSG.GF2Type.SmithTypeE.E7
