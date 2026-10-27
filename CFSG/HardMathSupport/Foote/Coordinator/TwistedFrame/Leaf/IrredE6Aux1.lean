module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.IrredE6Aux0
public import CFSG.RankThree.PartOne.KE.CTStatement

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped Matrix

set_option linter.unusedSectionVars false


abbrev V6 : Type := Fin Tag.E6.rank → ℤ

@[expose] def a2 : V6 := Pi.single 1 1
@[expose] def b2 : V6 := ![1, 1, 2, 3, 2, 1]
@[expose] def e0 : V6 := Pi.single 0 1
@[expose] def e2 : V6 := Pi.single 2 1
@[expose] def e4 : V6 := Pi.single 4 1
@[expose] def e5 : V6 := Pi.single 5 1

@[expose] def gam0 : List V6 := [e0, e2, e4, e5, -e0, -e2, -e4, -e5]

@[expose] def posL : List V6 := [e0, e2, e4, e5]

@[expose] def Mlist : List V6 :=
  [![0, 1, 1, 2, 1, 0], ![0, 1, 1, 2, 1, 1], ![0, 1, 1, 2, 2, 1], ![1, 1, 1, 2, 1, 0],
    ![1, 1, 1, 2, 1, 1], ![1, 1, 1, 2, 2, 1], ![1, 1, 2, 2, 1, 0], ![1, 1, 2, 2, 1, 1],
    ![1, 1, 2, 2, 2, 1], ![0, 1, 0, 1, 0, 0], ![0, 1, 0, 1, 1, 0], ![0, 1, 0, 1, 1, 1],
    ![0, 1, 1, 1, 0, 0], ![0, 1, 1, 1, 1, 0], ![0, 1, 1, 1, 1, 1], ![1, 1, 1, 1, 0, 0],
    ![1, 1, 1, 1, 1, 0], ![1, 1, 1, 1, 1, 1]]

@[expose] def hw1 : V6 := ![1, 1, 1, 1, 1, 1]
@[expose] def hw2 : V6 := ![1, 1, 2, 2, 2, 1]

theorem highRoot_E6 : highRoot Tag.E6 = ![1, 2, 2, 3, 2, 1] := rfl

theorem iθ_E6 : iθ Tag.E6 = 1 := rfl

theorem mem_Deg1_E6 {β : V6} : β ∈ Deg1 Tag.E6 ↔ β ∈ rootFinset Tag.E6 ∧ β 1 = 1 := by
  rw [CoordAux.mem_Deg1, mem_rootFinset, iθ_E6]

theorem b2_eq : b2 = highRoot Tag.E6 - a2 := by decide +kernel

theorem a2_eq : a2 = highRoot Tag.E6 - b2 := by decide +kernel

theorem a2_mem_Deg1 : a2 ∈ Deg1 Tag.E6 := mem_Deg1_E6.2 ⟨by decide +kernel, by decide +kernel⟩

theorem b2_mem_Deg1 : b2 ∈ Deg1 Tag.E6 := mem_Deg1_E6.2 ⟨by decide +kernel, by decide +kernel⟩

theorem a2_ne_b2 : a2 ≠ b2 := by decide +kernel

theorem gam0_facts : ∀ γ ∈ gam0, γ ∈ rootFinset Tag.E6 ∧ γ 1 = 0 := by
  decide +kernel

theorem posL_sub : ∀ γ ∈ posL, γ ∈ gam0 := by
  decide +kernel

theorem Mlist_facts : ∀ ν ∈ Mlist, ν ∈ rootFinset Tag.E6 ∧ ν 1 = 1 ∧ ν ≠ a2 ∧ ν ≠ b2 := by
  decide +kernel

theorem mem_Mlist_of {ν : V6} (h : ν ∈ rootFinset Tag.E6) (h1 : ν 1 = 1) (ha : ν ≠ a2)
    (hb : ν ≠ b2) : ν ∈ Mlist := by
  have key : ∀ ν ∈ rootFinset Tag.E6, ν 1 = 1 → ν ≠ a2 → ν ≠ b2 → ν ∈ Mlist := by
    decide +kernel
  exact key ν h h1 ha hb

theorem Mlist_mem_Deg1 {ν : V6} (h : ν ∈ Mlist) : ν ∈ Deg1 Tag.E6 :=
  mem_Deg1_E6.2 ⟨(Mlist_facts ν h).1, (Mlist_facts ν h).2.1⟩

theorem not_mem_Mlist {ν : V6} (h : ν ∉ Mlist) : ν ∉ Deg1 Tag.E6 ∨ ν = a2 ∨ ν = b2 := by
  by_cases hD : ν ∈ Deg1 Tag.E6
  · obtain ⟨h1, h2⟩ := mem_Deg1_E6.1 hD
    by_cases ha : ν = a2
    · exact Or.inr (Or.inl ha)
    · by_cases hb : ν = b2
      · exact Or.inr (Or.inr hb)
      · exact absurd (mem_Mlist_of h1 h2 ha hb) h
  · exact Or.inl hD

theorem Mlist_three : ∀ ν ∈ Mlist, ν 3 = 1 ∨ ν 3 = 2 := by
  decide +kernel

abbrev wE : WeylGroup Tag.E6 := TwClass.e6Six.w

theorem wE_smul (α : V6) :
    wE • α = CFSG.RankThree.Lattice.wordMat Tag.E6 TwClass.wordE6 *ᵥ α :=
  CFSG.RankThree.PartOne.KE.wordProd_smul_eq_wordMat_mulVec Tag.E6 TwClass.wordE6 α

theorem wE_theta : wE • highRoot Tag.E6 = highRoot Tag.E6 := by
  rw [wE_smul]; decide +kernel

theorem wE_invol (α : V6) : wE • (wE • α) = α := by
  rw [wE_smul, wE_smul, Matrix.mulVec_mulVec]
  have : CFSG.RankThree.Lattice.wordMat Tag.E6 TwClass.wordE6 *
      CFSG.RankThree.Lattice.wordMat Tag.E6 TwClass.wordE6 = 1 := by decide +kernel
  rw [this, Matrix.one_mulVec]

theorem wE_a2 : wE • a2 = b2 := by rw [wE_smul]; decide +kernel

theorem wE_b2 : wE • b2 = a2 := by rw [← wE_a2, wE_invol]

theorem wE_e0 : wE • e0 = e4 := by rw [wE_smul]; decide +kernel
theorem wE_e2 : wE • e2 = e5 := by rw [wE_smul]; decide +kernel
theorem wE_e4 : wE • e4 = e0 := by rw [← wE_e0, wE_invol]
theorem wE_e5 : wE • e5 = e2 := by rw [← wE_e2, wE_invol]

theorem wE_Mlist : ∀ ν ∈ Mlist, wE • ν ∈ Mlist ∧ (wE • ν) 3 ≠ ν 3 := by
  have key : ∀ ν ∈ Mlist, CFSG.RankThree.Lattice.wordMat Tag.E6 TwClass.wordE6 *ᵥ ν ∈ Mlist ∧
      (CFSG.RankThree.Lattice.wordMat Tag.E6 TwClass.wordE6 *ᵥ ν) 3 ≠ ν 3 := by
    decide +kernel
  intro ν hν
  rw [wE_smul]
  exact key ν hν

@[expose] def aE (γ μ : V6) : ℤ :=
  if μ + γ ∈ rootFinset Tag.E6 then commConst Tag.E6 γ μ (1, 1) else 0

@[expose] def opT {F : Type} [Field F] (γ : V6) : (V6 → F) →ₗ[F] (V6 → F) where
  toFun v := fun ν => (aE γ (ν - γ) : F) * v (ν - γ)
  map_add' v v' := by
    funext ν
    simp only [Pi.add_apply]
    ring
  map_smul' c v := by
    funext ν
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

theorem opT_apply {F : Type} [Field F] (γ : V6) (v : V6 → F) (ν : V6) :
    opT γ v ν = (aE γ (ν - γ) : F) * v (ν - γ) := rfl

theorem opT_single {F : Type} [Field F] (γ μ : V6) (c : F) :
    opT γ (Pi.single μ c : V6 → F) = Pi.single (μ + γ) ((aE γ μ : F) * c) := by
  funext ν
  rw [opT_apply]
  by_cases h : ν - γ = μ
  · have h' : ν = μ + γ := sub_eq_iff_eq_add.1 h
    subst h'
    rw [h, Pi.single_eq_same, Pi.single_eq_same]
  · have h' : ν ≠ μ + γ := fun e => h (sub_eq_iff_eq_add.2 e)
    rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h', mul_zero]

theorem ne_of_deg {γ μ : V6} (hγ0 : γ 1 = 0) (hμ1 : μ 1 = 1) : γ ≠ μ ∧ γ ≠ -μ := by
  constructor
  · intro h
    rw [h] at hγ0
    omega
  · intro h
    rw [h] at hγ0
    simp [hμ1] at hγ0

theorem simplyLaced_E6 : Tag.E6 = .D4 ∨ Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 :=
  Or.inr (Or.inl rfl)

theorem aE_unit {γ μ : V6} (hγ : γ ∈ rootFinset Tag.E6) (hγ0 : γ 1 = 0)
    (hμ : μ ∈ rootFinset Tag.E6) (hμ1 : μ 1 = 1) (h : μ + γ ∈ rootFinset Tag.E6) :
    aE γ μ = 1 ∨ aE γ μ = -1 := by
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  obtain ⟨hε, -⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6
    (mem_rootFinset.1 hγ) (mem_rootFinset.1 hμ) hne hne').1
      (mem_rootFinset.1 (by rwa [add_comm] at h))
  rw [aE, if_pos h]
  exact hε

theorem aE_ne_zero {F : Type} [Field F] {γ μ : V6} (hγ : γ ∈ rootFinset Tag.E6) (hγ0 : γ 1 = 0)
    (hμ : μ ∈ rootFinset Tag.E6) (hμ1 : μ 1 = 1) (h : μ + γ ∈ rootFinset Tag.E6) :
    (aE γ μ : F) ≠ 0 := by
  rcases aE_unit hγ hγ0 hμ hμ1 h with h' | h' <;> rw [h'] <;> simp

theorem aE_eq_zero {γ μ : V6} (h : μ + γ ∉ rootFinset Tag.E6) : aE γ μ = 0 := by
  rw [aE, if_neg h]

section Conj

variable {F : Type} [Field F]

theorem commute_theta {γ : V6} (hγ : γ ∈ rootFinset Tag.E6) (hγ0 : γ 1 = 0) (t c : F) :
    pinnedX Tag.E6 F γ t * pinnedX Tag.E6 F (highRoot Tag.E6) c =
      pinnedX Tag.E6 F (highRoot Tag.E6) c * pinnedX Tag.E6 F γ t := by
  have hθ1 : highRoot Tag.E6 1 = 2 := by decide
  have hne : γ ≠ highRoot Tag.E6 := fun h => by rw [h, hθ1] at hγ0; omega
  have hne' : γ ≠ -highRoot Tag.E6 := fun h => by
    rw [h, Pi.neg_apply, hθ1] at hγ0; omega
  have hnot : ¬ IsRoot Tag.E6 (γ + highRoot Tag.E6) := by
    intro hr
    have h2 := CoordAux.eq_highRoot_of_two_le hr (by
      rw [iθ_E6, Pi.add_apply, hγ0, hθ1]; norm_num)
    have : γ = 0 := by
      have := congrArg (· - highRoot Tag.E6) h2
      simpa using this
    rw [this] at hγ
    exact absurd hγ (by decide +kernel)
  exact ((simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6 (mem_rootFinset.1 hγ)
    (isRoot_highRoot Tag.E6) hne hne').2 hnot F _ (mem_rootSubgroup.2 ⟨t, rfl⟩) _
      (mem_rootSubgroup.2 ⟨c, rfl⟩)).eq

theorem conj_gen_deg1 {γ μ : V6} (hγ : γ ∈ rootFinset Tag.E6) (hγ0 : γ 1 = 0)
    (hμ : μ ∈ Deg1 Tag.E6) (t c : F) :
    pinnedX Tag.E6 F γ t * pinnedX Tag.E6 F μ c * (pinnedX Tag.E6 F γ t)⁻¹ ∈ Qθ Tag.E6 F ∧
    heisCoord Tag.E6 F (pinnedX Tag.E6 F γ t * pinnedX Tag.E6 F μ c * (pinnedX Tag.E6 F γ t)⁻¹) =
      heisCoord Tag.E6 F (pinnedX Tag.E6 F μ c) +
        t • opT γ (heisCoord Tag.E6 F (pinnedX Tag.E6 F μ c)) := by
  obtain ⟨hμr, hμ1⟩ := mem_Deg1_E6.1 hμ
  have hγr : IsRoot Tag.E6 γ := mem_rootFinset.1 hγ
  obtain ⟨hne, hne'⟩ := ne_of_deg hγ0 hμ1
  have hμQ : pinnedX Tag.E6 F μ c ∈ Qθ Tag.E6 F := pinnedX_mem_Qθ_of_Deg1 hμ c
  have hμc : heisCoord Tag.E6 F (pinnedX Tag.E6 F μ c) = Pi.single μ c :=
    (heisCoord_spec Tag.E6 F).pinnedX_deg1 μ hμ c
  rw [hμc, opT_single]
  by_cases h : μ + γ ∈ rootFinset Tag.E6
  · have hr : IsRoot Tag.E6 (γ + μ) := mem_rootFinset.1 (by rwa [add_comm] at h)
    have hD : μ + γ ∈ Deg1 Tag.E6 := mem_Deg1_E6.2 ⟨h, by simp [hγ0, hμ1]⟩
    obtain ⟨-, hform⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6 hγr
      (mem_rootFinset.1 hμr) hne hne').1 hr
    have hf := hform F t c
    rw [commutatorElement_def] at hf
    have hconj : pinnedX Tag.E6 F γ t * pinnedX Tag.E6 F μ c * (pinnedX Tag.E6 F γ t)⁻¹ =
        pinnedX Tag.E6 F (μ + γ) ((commConst Tag.E6 γ μ (1, 1) : F) * t * c) *
          pinnedX Tag.E6 F μ c := by
      rw [add_comm μ γ, ← hf]
      group
    have hP : pinnedX Tag.E6 F (μ + γ) ((commConst Tag.E6 γ μ (1, 1) : F) * t * c) ∈
        Qθ Tag.E6 F := pinnedX_mem_Qθ_of_Deg1 hD _
    rw [hconj]
    refine ⟨mul_mem hP hμQ, ?_⟩
    rw [(heisCoord_spec Tag.E6 F).mul _ hP _ hμQ, (heisCoord_spec Tag.E6 F).pinnedX_deg1 _ hD,
      hμc, aE, if_pos h, add_comm, ← Pi.single_smul]
    congr 2
    rw [smul_eq_mul]
    ring
  · have hnot : ¬ IsRoot Tag.E6 (γ + μ) := fun hr => h (by rw [add_comm]; exact mem_rootFinset.2 hr)
    have hcomm := ((simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6 hγr
      (mem_rootFinset.1 hμr) hne hne').2 hnot F _ (mem_rootSubgroup.2 ⟨t, rfl⟩) _
        (mem_rootSubgroup.2 ⟨c, rfl⟩)).eq
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one, aE, if_neg h]
    refine ⟨hμQ, ?_⟩
    rw [hμc]
    simp

theorem conj_deg0 {γ : V6} (hγ : γ ∈ rootFinset Tag.E6) (hγ0 : γ 1 = 0) (t : F) :
    ∀ q ∈ Qθ Tag.E6 F,
      pinnedX Tag.E6 F γ t * q * (pinnedX Tag.E6 F γ t)⁻¹ ∈ Qθ Tag.E6 F ∧
      heisCoord Tag.E6 F (pinnedX Tag.E6 F γ t * q * (pinnedX Tag.E6 F γ t)⁻¹) =
        heisCoord Tag.E6 F q + t • opT γ (heisCoord Tag.E6 F q) := by
  set x := pinnedX Tag.E6 F γ t
  refine Qθ_induction (P := fun q => x * q * x⁻¹ ∈ Qθ Tag.E6 F ∧
      heisCoord Tag.E6 F (x * q * x⁻¹) = heisCoord Tag.E6 F q + t • opT γ (heisCoord Tag.E6 F q))
    ?_ ?_ ?_ ?_ ?_
  · rw [mul_one, mul_inv_cancel, heisCoord_one, map_zero, smul_zero, add_zero]
    exact ⟨one_mem _, rfl⟩
  · rintro q q' hq hq' ⟨h1, h2⟩ ⟨h1', h2'⟩
    have e : x * (q * q') * x⁻¹ = (x * q * x⁻¹) * (x * q' * x⁻¹) := by group
    refine ⟨by rw [e]; exact mul_mem h1 h1', ?_⟩
    rw [e, (heisCoord_spec Tag.E6 F).mul _ h1 _ h1', h2, h2',
      (heisCoord_spec Tag.E6 F).mul _ hq _ hq', map_add, smul_add]
    abel
  · rintro q hq ⟨h1, h2⟩
    have e : x * q⁻¹ * x⁻¹ = (x * q * x⁻¹)⁻¹ := by group
    refine ⟨by rw [e]; exact inv_mem h1, ?_⟩
    rw [e, heisCoord_inv h1, h2, heisCoord_inv hq, map_neg, smul_neg, neg_add]
  · intro μ hμ c
    exact conj_gen_deg1 hγ hγ0 hμ t c
  · intro c
    have hc := commute_theta hγ hγ0 t c
    have e : x * pinnedX Tag.E6 F (highRoot Tag.E6) c * x⁻¹ =
        pinnedX Tag.E6 F (highRoot Tag.E6) c := by
      rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    rw [e, (heisCoord_spec Tag.E6 F).pinnedX_highRoot, map_zero, smul_zero, add_zero]
    exact ⟨pinnedX_highRoot_mem_Qθ c, rfl⟩

theorem highRoot_sub_facts : ∀ β ∈ rootFinset Tag.E6, β 1 = 1 →
    highRoot Tag.E6 - β ∈ rootFinset Tag.E6 ∧ highRoot Tag.E6 - β ≠ β := by
  decide +kernel

@[expose] def NC (β : V6) : ℤ := commConst Tag.E6 (highRoot Tag.E6 - β) β (1, 1)

theorem NC_unit {β : V6} (hβ : β ∈ Deg1 Tag.E6) : NC β = 1 ∨ NC β = -1 := by
  obtain ⟨hβr, hβ1⟩ := mem_Deg1_E6.1 hβ
  obtain ⟨hr, hne⟩ := highRoot_sub_facts β hβr hβ1
  have hne' : highRoot Tag.E6 - β ≠ -β := by
    intro h
    have h2 := congrFun h 1
    have hθ1 : highRoot Tag.E6 1 = 2 := by decide
    rw [Pi.sub_apply, Pi.neg_apply, hβ1, hθ1] at h2
    omega
  have hsum : highRoot Tag.E6 - β + β = highRoot Tag.E6 := sub_add_cancel _ _
  exact ((simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6 (mem_rootFinset.1 hr)
    (mem_rootFinset.1 hβr) hne hne').1 (by rw [hsum]; exact isRoot_highRoot _)).1

theorem NC_ne_zero {β : V6} (hβ : β ∈ Deg1 Tag.E6) : (NC β : F) ≠ 0 := by
  rcases NC_unit hβ with h | h <;> rw [h] <;> simp

theorem conj_Deg1 {β : V6} (hβ : β ∈ Deg1 Tag.E6) {q : ModGL Tag.E6 F} (hq : q ∈ Qθ Tag.E6 F)
    (c : F) :
    q * pinnedX Tag.E6 F β c * q⁻¹ =
      pinnedX Tag.E6 F (highRoot Tag.E6) ((NC β : F) * c * heisCoord Tag.E6 F q (highRoot Tag.E6 - β)) *
        pinnedX Tag.E6 F β c := by
  obtain ⟨hβr, hβ1⟩ := mem_Deg1_E6.1 hβ
  obtain ⟨hr, hne⟩ := highRoot_sub_facts β hβr hβ1
  have hne' : highRoot Tag.E6 - β ≠ -β := by
    intro h
    have h2 := congrFun h 1
    have hθ1 : highRoot Tag.E6 1 = 2 := by decide
    rw [Pi.sub_apply, Pi.neg_apply, hβ1, hθ1] at h2
    omega
  have hsum : highRoot Tag.E6 - β + β = highRoot Tag.E6 := sub_add_cancel _ _
  obtain ⟨-, hform⟩ := (simply_laced_root_commutator_unit.{0} Tag.E6 simplyLaced_E6
    (mem_rootFinset.1 hr) (mem_rootFinset.1 hβr) hne hne').1
      (by rw [hsum]; exact isRoot_highRoot _)
  have h := comm_Qθ_pinnedX_of (F := F) hβ hsum (NC β : F) c (fun s => by
    have := hform F s c
    rw [commutatorElement_def, hsum] at this
    exact this) hq
  rw [← h]
  group

theorem lin_of_commute {q : ModGL Tag.E6 F} (hq : q ∈ Qθ Tag.E6 F) (c₀ a b : F)
    (hc : q * (pinnedX Tag.E6 F (highRoot Tag.E6) c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b) =
      (pinnedX Tag.E6 F (highRoot Tag.E6) c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b) * q) :
    (NC a2 : F) * a * heisCoord Tag.E6 F q b2 + (NC b2 : F) * b * heisCoord Tag.E6 F q a2 = 0 := by
  have e1 := conj_Deg1 a2_mem_Deg1 hq a
  have e2 := conj_Deg1 b2_mem_Deg1 hq b
  rw [← b2_eq] at e1
  rw [← a2_eq] at e2
  set θ := highRoot Tag.E6
  have hθ : q * pinnedX Tag.E6 F θ c₀ * q⁻¹ = pinnedX Tag.E6 F θ c₀ := by
    rw [← Qθ_comm_highRoot hq c₀, mul_assoc, mul_inv_cancel, mul_one]
  have hθa : pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F θ ((NC b2 : F) * b * heisCoord Tag.E6 F q a2) =
      pinnedX Tag.E6 F θ ((NC b2 : F) * b * heisCoord Tag.E6 F q a2) * pinnedX Tag.E6 F a2 a :=
    (Qθ_comm_highRoot (pinnedX_mem_Qθ_of_Deg1 a2_mem_Deg1 a) _).symm
  have key : q * (pinnedX Tag.E6 F θ c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b) * q⁻¹ =
      pinnedX Tag.E6 F θ ((NC a2 : F) * a * heisCoord Tag.E6 F q b2 +
        (NC b2 : F) * b * heisCoord Tag.E6 F q a2) *
      (pinnedX Tag.E6 F θ c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b) := by
    calc q * (pinnedX Tag.E6 F θ c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b) * q⁻¹
        = (q * pinnedX Tag.E6 F θ c₀ * q⁻¹) * (q * pinnedX Tag.E6 F a2 a * q⁻¹) *
            (q * pinnedX Tag.E6 F b2 b * q⁻¹) := by group
      _ = pinnedX Tag.E6 F θ c₀ *
            (pinnedX Tag.E6 F θ ((NC a2 : F) * a * heisCoord Tag.E6 F q b2) * pinnedX Tag.E6 F a2 a) *
            (pinnedX Tag.E6 F θ ((NC b2 : F) * b * heisCoord Tag.E6 F q a2) *
              pinnedX Tag.E6 F b2 b) := by rw [hθ, e1, e2]
      _ = pinnedX Tag.E6 F θ c₀ *
            pinnedX Tag.E6 F θ ((NC a2 : F) * a * heisCoord Tag.E6 F q b2) *
            (pinnedX Tag.E6 F a2 a *
              pinnedX Tag.E6 F θ ((NC b2 : F) * b * heisCoord Tag.E6 F q a2)) *
            pinnedX Tag.E6 F b2 b := by group
      _ = pinnedX Tag.E6 F θ c₀ *
            pinnedX Tag.E6 F θ ((NC a2 : F) * a * heisCoord Tag.E6 F q b2) *
            (pinnedX Tag.E6 F θ ((NC b2 : F) * b * heisCoord Tag.E6 F q a2) *
              pinnedX Tag.E6 F a2 a) *
            pinnedX Tag.E6 F b2 b := by rw [hθa]
      _ = pinnedX Tag.E6 F θ ((NC a2 : F) * a * heisCoord Tag.E6 F q b2 +
            (NC b2 : F) * b * heisCoord Tag.E6 F q a2) *
          (pinnedX Tag.E6 F θ c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b) := by
          rw [pinnedX_add, ← mul_assoc, ← mul_assoc, ← pinnedX_add, ← pinnedX_add,
            ← pinnedX_add]
          rw [show c₀ + (NC a2 : F) * a * heisCoord Tag.E6 F q b2 +
              (NC b2 : F) * b * heisCoord Tag.E6 F q a2 =
            ((NC a2 : F) * a * heisCoord Tag.E6 F q b2 + (NC b2 : F) * b * heisCoord Tag.E6 F q a2) +
              c₀ by ring, pinnedX_add]
          group
  set u := pinnedX Tag.E6 F θ c₀ * pinnedX Tag.E6 F a2 a * pinnedX Tag.E6 F b2 b with hu
  set S := (NC a2 : F) * a * heisCoord Tag.E6 F q b2 + (NC b2 : F) * b * heisCoord Tag.E6 F q a2
  have hqu : q * u * q⁻¹ = u := by rw [hc, mul_inv_cancel_right]
  rw [hqu] at key
  have h1 : pinnedX Tag.E6 F θ S = 1 := by
    have h := congrArg (fun z => z * u⁻¹) key
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h
    exact h.symm
  rw [← pinnedX_zero (τ := Tag.E6) (R := F) θ] at h1
  exact pinnedX_injective Tag.E6 F θ h1

end Conj

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.IrredE6Aux
