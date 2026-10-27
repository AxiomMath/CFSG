module

public import CFSG.CGT.PushingUpLit.SolK.PermModule
public import CFSG.CGT.PushingUpLit.BHS.OffenderInternal
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.RankThree.PartOne.S12.PushingUp

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 Equiv Equiv.Perm
open scoped commutatorElement

variable {L : Type} [Group L]

theorem hom_eq_one_of_oResidual {B : Type*} [Group B] (hres : oResidualTwo L = ⊤)
    (hB : IsPGroup 2 B) (f : L →* B) : f = 1 := by
  have hq : IsPGroup 2 (L ⧸ f.ker) :=
    (hB.to_subgroup f.range).of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hle : oResidualTwo L ≤ f.ker := sInf_le ⟨inferInstance, hq⟩
  rw [hres, top_le_iff] at hle
  ext l
  have : l ∈ f.ker := by rw [hle]; exact Subgroup.mem_top l
  simpa using this

theorem forall_eq_one_of_mul {B : Subgroup L} (hres : oResidualTwo L = ⊤) (hB2 : IsPGroup 2 B)
    (κ : L → L) (hκB : ∀ l, κ l ∈ B) (hκ : ∀ a b, κ (a * b) = κ a * κ b) (l : L) :
    κ l = 1 := by
  let f : L →* ↥B := MonoidHom.mk' (fun l => ⟨κ l, hκB l⟩) (fun a b => Subtype.ext (hκ a b))
  have h : f l = 1 := DFunLike.congr_fun (hom_eq_one_of_oResidual hres hB2 f) l
  exact congrArg Subtype.val h

theorem isPGroup_of_le {H K : Subgroup L} (hK : IsPGroup 2 K) (hHK : H ≤ K) : IsPGroup 2 H := by
  intro g
  obtain ⟨k, hk⟩ := hK ⟨g, hHK g.2⟩
  exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩

theorem commutator_mul_right (y a b : L) : ⁅y, a * b⁆ = ⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem shortU_le_pCore : shortU L ≤ CFSG.pCore 2 L := Subgroup.commutator_le_left _ _

variable [Finite L]

theorem shortU_comm_pCore (hL : IsShortGroup L) {u y : L} (hu : u ∈ shortU L)
    (hy : y ∈ CFSG.pCore 2 L) : u * y = y * u := by
  obtain ⟨c, hc, rfl⟩ := hL.U_le_center hu
  have := Subgroup.mem_center_iff.mp hc ⟨y, hy⟩
  exact congrArg Subtype.val this.symm

theorem shortU_sq_eq_one (hL : IsShortGroup L) {n : ℕ} (hnat : IsNaturalAltModule L n) :
    ∀ u ∈ shortU L, u ^ 2 = 1 := by
  classical
  obtain ⟨φ, ψ, hsum, hsurj, hker, hequiv⟩ := hnat
  have hY2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have hUY : shortU L ≤ CFSG.pCore 2 L := shortU_le_pCore
  have hCU : shortC L ≤ shortU L := inf_le_left
  have hCZ : shortC L ≤ Subgroup.center L := inf_le_right
  have hC2 : IsPGroup 2 (shortC L) := isPGroup_of_le hY2 (hCU.trans hUY)
  have hUn : (shortU L).Normal := by
    unfold shortU
    infer_instance
  have hsq : ∀ u ∈ shortU L, u ^ 2 ∈ shortC L := by
    intro u hu
    have h1 : ψ ⟨u ^ 2, (shortU L).pow_mem hu 2⟩ = 1 := by
      have : (⟨u ^ 2, (shortU L).pow_mem hu 2⟩ : ↥(shortU L)) = (⟨u, hu⟩ : ↥(shortU L)) ^ 2 :=
        Subtype.ext (by simp)
      rw [this, map_pow]
      refine Multiplicative.toAdd.injective ?_
      funext i
      show 2 • (Multiplicative.toAdd (ψ ⟨u, hu⟩) i) = 0
      rw [two_nsmul]
      exact CharTwo.add_self_eq_zero _
    have h2 : (⟨u ^ 2, (shortU L).pow_mem hu 2⟩ : ↥(shortU L)) ∈ ψ.ker := h1
    rw [hker, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hgen : ∀ y ∈ CFSG.pCore 2 L, ∀ l : L, ⁅y, l⁆ ^ 2 = 1 := by
    intro y hy
    have hmemU : ∀ l : L, ⁅y, l⁆ ∈ shortU L := fun l =>
      Subgroup.commutator_mem_commutator hy (Subgroup.mem_top l)
    refine forall_eq_one_of_mul hL.residual_eq hC2 (fun l => ⁅y, l⁆ ^ 2)
      (fun l => hsq _ (hmemU l)) (fun a b => ?_)
    show ⁅y, a * b⁆ ^ 2 = ⁅y, a⁆ ^ 2 * ⁅y, b⁆ ^ 2
    rw [commutator_mul_right]
    have hB : a * ⁅y, b⁆ * a⁻¹ ∈ shortU L := hUn.conj_mem _ (hmemU b) a
    have hcomm : Commute ⁅y, a⁆ (a * ⁅y, b⁆ * a⁻¹) :=
      shortU_comm_pCore hL (hmemU a) (hUY hB)
    rw [hcomm.mul_pow]
    congr 1
    have hc : ⁅y, b⁆ ^ 2 ∈ Subgroup.center L := hCZ (hsq _ (hmemU b))
    have := Subgroup.mem_center_iff.mp hc a
    calc (a * ⁅y, b⁆ * a⁻¹) ^ 2 = a * ⁅y, b⁆ ^ 2 * a⁻¹ := conj_pow
      _ = ⁅y, b⁆ ^ 2 := by rw [this, mul_inv_cancel_right]
  intro u hu
  have hu' : u ∈ Subgroup.closure
      {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} := by
    rw [← Subgroup.commutator_def]
    exact hu
  refine Subgroup.closure_induction (p := fun x _ => x ^ 2 = 1) ?_ ?_ ?_ ?_ hu'
  · rintro x ⟨y, hy, l, -, rfl⟩
    exact hgen y hy l
  · exact one_pow 2
  · intro x z hx hz hx2 hz2
    have hxU : x ∈ shortU L := by
      have : Subgroup.closure {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} =
          shortU L := (Subgroup.commutator_def _ _).symm
      rwa [this] at hx
    have hzU : z ∈ shortU L := by
      have : Subgroup.closure {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} =
          shortU L := (Subgroup.commutator_def _ _).symm
      rwa [this] at hz
    have hcomm : Commute x z := shortU_comm_pCore hL hxU (hUY hzU)
    rw [hcomm.mul_pow, hx2, hz2, mul_one]
  · intro x _ hx2
    rw [inv_pow, hx2, inv_one]

structure AltBlockData (L : Type) [Group L] [Finite L] (n : ℕ) where
  ρ : L →* Perm (Fin (2 * n + 1))
  ρ_alt : ∀ l, ρ l ∈ alternatingGroup (Fin (2 * n + 1))
  ρ_surj : ∀ a ∈ alternatingGroup (Fin (2 * n + 1)), ∃ l, ρ l = a
  ker_ρ : ρ.ker = CFSG.pCore 2 L
  β : ↥(shortU L) ≃* ↥(coreMod (2 * n + 1))
  equivar : ∀ (l : L) (u : ↥(shortU L)) (hu : l * (u : L) * l⁻¹ ∈ shortU L),
    β ⟨l * (u : L) * l⁻¹, hu⟩ = coreAct (2 * n + 1) (ρ l) (β u)

theorem exists_altBlockData (hL : IsShortGroup L) {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule L n) : Nonempty (AltBlockData L n) := by
  classical
  have hsq := shortU_sq_eq_one hL hnat
  obtain ⟨φ, ψ, hsum, hsurj, hker, hequiv⟩ := hnat
  have hY2 : IsPGroup 2 (CFSG.pCore 2 L) := CFSG.pCore_isPGroup
  have hUY : shortU L ≤ CFSG.pCore 2 L := shortU_le_pCore
  have hCU : shortC L ≤ shortU L := inf_le_left
  have hCZ : shortC L ≤ Subgroup.center L := inf_le_right
  have hC2 : IsPGroup 2 (shortC L) := isPGroup_of_le hY2 (hCU.trans hUY)
  have hUn : (shortU L).Normal := by
    unfold shortU
    infer_instance
  have hUcomm : ∀ u ∈ shortU L, ∀ v ∈ shortU L, u * v = v * u := fun u hu v hv =>
    shortU_comm_pCore hL hu (hUY hv)
  have hUe : IsElemAbelian 2 (shortU L) := isElemAbelian_of_forall' hUcomm hsq
  let _ : CommGroup ↥(shortU L) := commGroupOfElemAbelian hUe
  have _ := hUn
  have hW : ∀ w : ↥(shortU L), w ^ 2 = 1 := fun w => Subtype.ext (by
    rw [SubgroupClass.coe_pow]
    exact hsq w w.2)
  have hdodd : Odd (2 * n + 1) := odd_two_mul_add_one n
  have hd5 : 5 ≤ 2 * n + 1 := by omega
  let ρ : L →* Perm (Fin (2 * n + 1)) :=
    (alternatingGroup (Fin (2 * n + 1))).subtype.comp
      (φ.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 L)))
  have ρ_alt : ∀ l, ρ l ∈ alternatingGroup (Fin (2 * n + 1)) := fun l =>
    (φ (l : L ⧸ CFSG.pCore 2 L)).2
  have ρ_surj : ∀ a ∈ alternatingGroup (Fin (2 * n + 1)), ∃ l, ρ l = a := by
    intro a ha
    obtain ⟨q, hq⟩ := φ.surjective ⟨a, ha⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, congrArg Subtype.val hq⟩
  have ker_ρ : ρ.ker = CFSG.pCore 2 L := by
    ext l
    rw [MonoidHom.mem_ker]
    show ((φ (l : L ⧸ CFSG.pCore 2 L) : alternatingGroup (Fin (2 * n + 1))) :
      Perm (Fin (2 * n + 1))) = 1 ↔ _
    constructor
    · intro h
      have h1 : φ (l : L ⧸ CFSG.pCore 2 L) = 1 := Subtype.ext h
      have h2 : (l : L ⧸ CFSG.pCore 2 L) = 1 := by simpa using h1
      exact (QuotientGroup.eq_one_iff l).1 h2
    · intro h
      have h2 : (l : L ⧸ CFSG.pCore 2 L) = 1 := (QuotientGroup.eq_one_iff l).2 h
      rw [h2, map_one]
      rfl
  let β0 : ↥(shortU L) →* ↥(coreMod (2 * n + 1)) :=
    { toFun := fun u => ⟨ψ u, mem_coreMod.2 (hsum u)⟩
      map_one' := by
        apply Subtype.ext
        simp only [map_one]
        rfl
      map_mul' := fun a b => Subtype.ext (by simp only [map_mul]; rfl) }
  have hβ0surj : Function.Surjective β0 := by
    intro v
    obtain ⟨u, hu⟩ := hsurj (fun i => Multiplicative.toAdd v.1 i) (mem_coreMod.1 v.2)
    exact ⟨u, Subtype.ext hu⟩
  have hβ0equiv : ∀ (l : L) (u : ↥(shortU L)) (hu : l * (u : L) * l⁻¹ ∈ shortU L),
      β0 ⟨l * (u : L) * l⁻¹, hu⟩ = coreAct (2 * n + 1) (ρ l) (β0 u) := by
    intro l u hu
    apply Subtype.ext
    have h := hequiv l u u.2 hu
    show ψ ⟨l * (u : L) * l⁻¹, hu⟩ = _
    rw [h]
    rfl
  have hβ0ker : ∀ u : ↥(shortU L), β0 u = 1 ↔ (u : L) ∈ shortC L := by
    intro u
    have : β0 u = 1 ↔ ψ u = 1 := by
      constructor
      · intro h
        exact congrArg Subtype.val h
      · intro h
        exact Subtype.ext h
    rw [this, ← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  let conjN : L →* MulAut ↥(shortU L) := MulAut.conjNormal
  let ρ' : L →* ↥(alternatingGroup (Fin (2 * n + 1))) := ρ.codRestrict _ ρ_alt
  have hρ'surj : Function.Surjective ρ' := fun a => by
    obtain ⟨l, hl⟩ := ρ_surj a a.2
    exact ⟨l, Subtype.ext hl⟩
  have hker_le : ρ'.ker ≤ conjN.ker := by
    intro l hl
    have hlY : l ∈ CFSG.pCore 2 L := by
      rw [← ker_ρ]
      rw [MonoidHom.mem_ker] at hl ⊢
      exact congrArg Subtype.val hl
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun u => Subtype.ext ?_
    show l * (u : L) * l⁻¹ = (u : L)
    rw [← shortU_comm_pCore hL u.2 hlY]
    simp
  let act : alternatingGroup (Fin (2 * n + 1)) →* MulAut ↥(shortU L) :=
    MonoidHom.liftOfSurjective ρ' hρ'surj ⟨conjN, hker_le⟩
  have hact : ∀ l, act (ρ' l) = conjN l := fun l =>
    MonoidHom.liftOfRightInverse_comp_apply ρ' _ _ ⟨conjN, hker_le⟩ l
  have hconj : ∀ (l : L) (u : ↥(shortU L)), ((conjN l u : ↥(shortU L)) : L) = l * (u : L) * l⁻¹ :=
    fun l u => MulAut.conjNormal_apply l u
  have hequivact : ∀ (σ : alternatingGroup (Fin (2 * n + 1))) (w : ↥(shortU L)),
      β0 (act σ w) = coreAct (2 * n + 1) (σ : Perm (Fin (2 * n + 1))) (β0 w) := by
    intro σ w
    obtain ⟨l, rfl⟩ := hρ'surj σ
    rw [hact]
    have hu : l * (w : L) * l⁻¹ ∈ shortU L := hUn.conj_mem _ w.2 l
    have h1 : conjN l w = ⟨l * (w : L) * l⁻¹, hu⟩ := Subtype.ext (hconj l w)
    rw [h1, hβ0equiv l w hu]
    rfl
  have hfixact : ∀ w : ↥(shortU L), β0 w = 1 → ∀ σ, act σ w = w := by
    intro w hw σ
    obtain ⟨l, rfl⟩ := hρ'surj σ
    rw [hact]
    have hwC : (w : L) ∈ shortC L := (hβ0ker w).1 hw
    have hz := Subgroup.mem_center_iff.mp (hCZ hwC) l
    refine Subtype.ext ?_
    rw [hconj, hz, mul_inv_cancel_right]
  obtain ⟨s, hs1, hs2⟩ := exists_equivariant_section hW hdodd hd5 act β0 hβ0surj hequivact hfixact
  have hCbot : ∀ c : ↥(shortU L), β0 c = 1 → c = 1 := by
    let π : ↥(shortU L) →* ↥(shortU L) :=
      MonoidHom.mk' (fun u => u * (s (β0 u))⁻¹) (fun a b => by
        simp only [map_mul, mul_inv_rev]
        ac_rfl)
    have hπβ : ∀ u, β0 (π u) = 1 := by
      intro u
      show β0 (u * (s (β0 u))⁻¹) = 1
      rw [map_mul, map_inv, hs1]
      exact mul_inv_cancel _
    have hπC : ∀ u, ((π u : ↥(shortU L)) : L) ∈ shortC L := fun u => (hβ0ker _).1 (hπβ u)
    have hπconj : ∀ (l : L) (u : ↥(shortU L)), π (conjN l u) = π u := by
      intro l u
      have h1 : β0 (conjN l u) = coreAct (2 * n + 1) (ρ l) (β0 u) := by
        have hu : l * (u : L) * l⁻¹ ∈ shortU L := hUn.conj_mem _ u.2 l
        have h1 : conjN l u = ⟨l * (u : L) * l⁻¹, hu⟩ := Subtype.ext (hconj l u)
        rw [h1, hβ0equiv l u hu]
      have h2 : s (β0 (conjN l u)) = conjN l (s (β0 u)) := by
        rw [h1, ← hact, hs2]
        rfl
      have hz := Subgroup.mem_center_iff.mp (hCZ (hπC u)) l
      have hcc : (conjN l (π u) : ↥(shortU L)) = π u :=
        Subtype.ext (by rw [hconj, hz, mul_inv_cancel_right])
      have hπ : π (conjN l u) = conjN l (π u) := by
        show conjN l u * (s (β0 (conjN l u)))⁻¹ = conjN l (u * (s (β0 u))⁻¹)
        rw [h2, map_mul, map_inv]
      rw [hπ, hcc]
    have hπcomm : ∀ y ∈ CFSG.pCore 2 L, ∀ x : L, ∀ h : ⁅y, x⁆ ∈ shortU L, π ⟨⁅y, x⁆, h⟩ = 1 := by
      intro y hy
      let P : L → L := fun g => if h : g ∈ shortU L then ((π ⟨g, h⟩ : ↥(shortU L)) : L) else 1
      have hP : ∀ g (h : g ∈ shortU L), P g = ((π ⟨g, h⟩ : ↥(shortU L)) : L) := fun g h => by
        simp only [P, h, dite_true]
      have hmemU : ∀ x : L, ⁅y, x⁆ ∈ shortU L := fun x =>
        Subgroup.commutator_mem_commutator hy (Subgroup.mem_top x)
      have hκ : ∀ x, P ⁅y, x⁆ = 1 := by
        refine forall_eq_one_of_mul hL.residual_eq hC2 (fun x => P ⁅y, x⁆) (fun x => ?_)
          (fun a b => ?_)
        · rw [hP _ (hmemU x)]
          exact hπC _
        · show P ⁅y, a * b⁆ = P ⁅y, a⁆ * P ⁅y, b⁆
          have hB : a * ⁅y, b⁆ * a⁻¹ ∈ shortU L := hUn.conj_mem _ (hmemU b) a
          rw [commutator_mul_right, hP _ (Subgroup.mul_mem _ (hmemU a) hB), hP _ (hmemU a),
            hP _ (hmemU b)]
          have : (⟨⁅y, a⁆ * (a * ⁅y, b⁆ * a⁻¹), Subgroup.mul_mem _ (hmemU a) hB⟩ : ↥(shortU L)) =
              ⟨⁅y, a⁆, hmemU a⟩ * conjN a ⟨⁅y, b⁆, hmemU b⟩ :=
            Subtype.ext (by rw [Subgroup.coe_mul, hconj])
          rw [this, map_mul, hπconj]
          rfl
      intro x h
      have := hκ x
      rw [hP _ h] at this
      exact Subtype.ext this
    intro c hc
    have h0 : π c = c := by
      show c * (s (β0 c))⁻¹ = c
      rw [hc, map_one, inv_one, mul_one]
    have hmem : (c : L) ∈ Subgroup.closure
        {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} := by
      rw [← Subgroup.commutator_def]
      exact c.2
    have key : ∀ (g : L) (hg : g ∈ shortU L), π ⟨g, hg⟩ = 1 := by
      intro g hg
      have hg' : g ∈ Subgroup.closure
          {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} := by
        rw [← Subgroup.commutator_def]
        exact hg
      refine Subgroup.closure_induction
        (p := fun g _ => ∀ hg : g ∈ shortU L, π ⟨g, hg⟩ = 1) ?_ ?_ ?_ ?_ hg' hg
      · rintro x ⟨y, hy, l, -, rfl⟩ h
        exact hπcomm y hy l h
      · intro h
        exact map_one π
      · intro x z _ _ hx hz h
        have hxU : x ∈ shortU L := by
          have hx' : x ∈ Subgroup.closure
              {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} := by assumption
          rwa [← Subgroup.commutator_def] at hx'
        have hzU : z ∈ shortU L := by
          have hz' : z ∈ Subgroup.closure
              {g | ∃ y ∈ CFSG.pCore 2 L, ∃ l ∈ (⊤ : Subgroup L), ⁅y, l⁆ = g} := by assumption
          rwa [← Subgroup.commutator_def] at hz'
        have : (⟨x * z, h⟩ : ↥(shortU L)) = ⟨x, hxU⟩ * ⟨z, hzU⟩ := rfl
        rw [this, map_mul, hx hxU, hz hzU, mul_one]
      · intro x hx hx1 h
        have hxU : x ∈ shortU L := by
          rwa [← Subgroup.commutator_def] at hx
        have : (⟨x⁻¹, h⟩ : ↥(shortU L)) = ⟨x, hxU⟩⁻¹ := rfl
        rw [this, map_inv, hx1 hxU, inv_one]
    rw [← h0]
    exact key c c.2
  have hβ0inj : Function.Injective β0 := by
    rw [injective_iff_map_eq_one]
    exact hCbot
  exact ⟨{ ρ := ρ
           ρ_alt := ρ_alt
           ρ_surj := ρ_surj
           ker_ρ := ker_ρ
           β := MulEquiv.ofBijective β0 ⟨hβ0inj, hβ0surj⟩
           equivar := fun l u hu => hβ0equiv l u hu }⟩

end CFSG.CGT.PushingUpLit.SolK
