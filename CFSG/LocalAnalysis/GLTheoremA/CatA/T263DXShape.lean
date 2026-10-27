module

import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynBridge
import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FDynTri
import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerOrder
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXA5
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyInner
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXEasyModelTw

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.DX

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.ComponentClassification.OuterAutomorphisms (innAutDerived)

@[expose] def ModelSelD (p : ℕ) (T : Type) [Group T] [Finite T] : Prop :=
  ∀ β : MulAut T, β ∈ innAutDerived T → β ^ p = 1 → β ≠ 1 → ∀ P : Subgroup T,
    P ≤ fixSubgroup β → IsPGroup 2 ↥P → P ≠ ⊥ →
    ∃ J : Subgroup T, IsComponentOf J (fixSubgroup β) ∧
      p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧ ⁅P, J⁆ ≠ ⊥ ∧
      P ≤ J ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (J : Set T))

section Lift

open scoped commutatorElement

variable {G T : Type} [Group G] [Group T]

private theorem commutator_le_self_fix (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

private theorem commutator_mul_central_fix {a b z₁ z₂ : G} (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) : ⁅a * z₁, b * z₂⁆ = ⁅a, b⁆ :=
  CFSG.HardMathSupport.Solomon.Coordinator.commutatorElement_mul_mul'
    (Commute.symm (Subgroup.mem_center_iff.1 h₁ b))
    (Commute.symm (Subgroup.mem_center_iff.1 h₁ z₂))
    (Commute.symm (Subgroup.mem_center_iff.1 h₂ a))

private theorem lift_component_fix (σ : G →* T) (hσ : Function.Surjective σ)
    (hker : σ.ker ≤ Subgroup.center G) (α : MulAut G) (β : MulAut T)
    (hαβ : ∀ k, σ (α k) = β (σ k)) {JT : Subgroup T} (hJT : IsComponentOf JT (fixSubgroup β)) :
    ∃ J₀ : Subgroup G, J₀ ≤ fixSubgroup α ∧ J₀.map σ = JT ∧
      IsSubnormal J₀ (fixSubgroup α) ∧ CFSG.Open.IsQuasisimple ↥J₀ ∧
      Nonempty (↥J₀ ⧸ Subgroup.center ↥J₀ ≃* ↥JT ⧸ Subgroup.center ↥JT) ∧
      ∀ d : G, σ d ∈ Subgroup.centralizer (JT : Set T) → d ∈ Subgroup.centralizer (J₀ : Set G) := by
  set H : Subgroup G := JT.comap σ with hH
  have hHmap : H.map σ = JT := Subgroup.map_comap_eq_self_of_surjective hσ JT
  haveI hJTperf : Group.IsPerfect ↥JT := ⟨hJT.2.2.1⟩
  have hJTcomm : ⁅JT, JT⁆ = JT := Subgroup.commutator_eq_self
  have hJ₀map : (⁅H, H⁆ : Subgroup G).map σ = JT := by
    rw [Subgroup.map_commutator, hHmap, hJTcomm]
  have hdecomp : ∀ g ∈ H, ∃ a ∈ (⁅H, H⁆ : Subgroup G), ∃ z ∈ Subgroup.center G, g = a * z := by
    intro g hg
    have : σ g ∈ (⁅H, H⁆ : Subgroup G).map σ := by
      rw [hJ₀map]
      exact hg
    obtain ⟨a, ha, haeq⟩ := this
    refine ⟨a, ha, a⁻¹ * g, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    change (σ a)⁻¹ * σ g = 1
    rw [haeq, inv_mul_cancel]
  have hJ₀H : (⁅H, H⁆ : Subgroup G) ≤ H := commutator_le_self_fix H
  have hJ₀perf : ⁅(⁅H, H⁆ : Subgroup G), ⁅H, H⁆⁆ = ⁅H, H⁆ := by
    refine le_antisymm (commutator_le_self_fix _) ?_
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := hdecomp g₁ hg₁
    obtain ⟨a₂, ha₂, z₂, hz₂, rfl⟩ := hdecomp g₂ hg₂
    rw [commutator_mul_central_fix hz₁ hz₂]
    exact Subgroup.commutator_mem_commutator ha₁ ha₂
  have hJ₀C : (⁅H, H⁆ : Subgroup G) ≤ fixSubgroup α := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    exact CFSG.HardMathSupport.Solomon.Coordinator.comm_mem_fixSubgroup σ hker α β hαβ
      (hJT.1 hg₁) (hJT.1 hg₂)
  have hsub : IsSubnormal (⁅H, H⁆ : Subgroup G) (fixSubgroup α) := by
    have h1 : IsSubnormal H ((fixSubgroup β).comap σ) := hJT.2.1.comap σ
    have h2 := h1.inf (fixSubgroup α)
    have hle : fixSubgroup α ≤ (fixSubgroup β).comap σ := fun s hs =>
      CFSG.HardMathSupport.Solomon.Coordinator.map_fixSubgroup_le σ hker α β hαβ ⟨s, hs, rfl⟩
    rw [inf_eq_right.2 hle] at h2
    refine IsSubnormal.step (M := H ⊓ fixSubgroup α) (le_inf hJ₀H hJ₀C) ?_ h2
    rw [Subgroup.normal_subgroupOf_iff (le_inf hJ₀H hJ₀C)]
    intro h m hh hm
    obtain ⟨a, ha, z, hz, rfl⟩ := hdecomp m hm.1
    have hzc : h * z = z * h := Subgroup.mem_center_iff.1 hz h
    have : a * z * h * (a * z)⁻¹ = a * h * a⁻¹ := by
      calc a * z * h * (a * z)⁻¹ = a * (z * h) * z⁻¹ * a⁻¹ := by group
        _ = a * (h * z) * z⁻¹ * a⁻¹ := by rw [hzc]
        _ = a * h * a⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hh) (Subgroup.inv_mem _ ha)
  haveI hJ₀perfect : Group.IsPerfect ↥(⁅H, H⁆ : Subgroup G) := Subgroup.isPerfect_iff.2 hJ₀perf
  let φ : ↥(⁅H, H⁆ : Subgroup G) →* ↥JT :=
    (σ.comp (⁅H, H⁆ : Subgroup G).subtype).codRestrict JT (fun j => hJ₀H j.2)
  have hφsurj : Function.Surjective φ := by
    intro b
    have hb : (b : T) ∈ (⁅H, H⁆ : Subgroup G).map σ := by
      rw [hJ₀map]
      exact b.2
    obtain ⟨a, ha, hab⟩ := hb
    exact ⟨⟨a, ha⟩, Subtype.ext hab⟩
  have hφker : φ.ker ≤ Subgroup.center ↥(⁅H, H⁆ : Subgroup G) := by
    intro j hj
    have h1 : σ (j : G) = 1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hj)
    have h2 : (j : G) ∈ Subgroup.center G := hker h1
    exact Subgroup.mem_center_iff.2 fun y => Subtype.ext (Subgroup.mem_center_iff.1 h2 y)
  obtain ⟨hq, ⟨he⟩⟩ := perfect_cover hJ₀perfect.commutator_eq_top hJT.2.2 φ hφsurj hφker
  have hcent : ∀ d : G, σ d ∈ Subgroup.centralizer (JT : Set T) →
      d ∈ Subgroup.centralizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
    intro d hd
    have hz : ⁅(⁅H, H⁆ : Subgroup G), (Subgroup.centralizer (JT : Set T)).comap σ⁆ ≤
        Subgroup.center G := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      apply hker
      rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      have hσb : σ b ∈ Subgroup.centralizer (JT : Set T) := hb
      exact Subgroup.mem_centralizer_iff.1 hσb (σ a) (hJ₀H ha)
    have hbot : ⁅(⁅H, H⁆ : Subgroup G), (Subgroup.centralizer (JT : Set T)).comap σ⁆ = ⊥ := by
      refine CFSG.ComponentClassification.Quasisimple.perfect_double_commutator _ _ ?_
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hz.trans (Subgroup.center_le_centralizer _)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hbot
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.1 (hbot ha) d hd).symm
  exact ⟨⁅H, H⁆, hJ₀C, hJ₀map, hsub, hq, ⟨he⟩, hcent⟩

end Lift

variable {p : ℕ}


theorem modelSelD_adjointGroup {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K = 2) (hK4 : 4 ≤ Nat.card K) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K ^ 2 - 1) : ModelSelD p ↥(adjointGroup τ K) := by
  intro β hβmem hβp hβ1 P hPβ hP2 hP1
  exact exists_comp_of_two_adjointGroup hτ hK2 hK4 hp hp2 hpq β hβmem hβp hβ1 P hPβ hP2 hP1

theorem modelSelD_twistedE6 {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))
    (hq4 : 4 ≤ 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ (2 ^ f) ^ 2 - 1) :
    ModelSelD p ↥(twistedE6RootGroup K σ) := by
  haveI : Finite ↥(twistedE6RootGroup K σ) := Subtype.finite
  intro β hβmem hβp hβ1 P hPβ hP2 hP1
  exact exists_comp_of_two_twistedE6 hf hK σ hσ hq4 hp hp2 hpq β hβmem hβp hβ1 P hPβ hP2 hP1

theorem exists_modelSelD_e6Shape (hp : p.Prime) (hp2 : p ≠ 2) {X : Type} [Group X]
    (h : catalogIs X (t263GE6Shape p)) :
    ∃ (T : Type) (_ : Group T) (_ : Finite T), Nonempty (X ≃* T) ∧ ModelSelD p T := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | lie d =>
    obtain ⟨d, hv⟩ := d
    cases d with
    | E6 q =>
      obtain ⟨hq2, hq4, hp3, h3⟩ := hi
      have hpq : p ∣ q.card ^ 2 - 1 := by
        rw [hp3]
        exact h3.trans (Nat.sub_one_dvd_pow_sub_one q.card 2)
      obtain ⟨K, _, _, hK, hKchar, ⟨φ⟩⟩ :=
        CFSG.LieType.SeitzGeneration.exists_catEquiv_adjointGroup
          CFSG.TauCetiBridge.Even.chevalleyBridgesAll.e6 q hv
      have hK2 : ringChar K = 2 := by
        haveI : CharP K 2 := by rw [← hq2]; exact hKchar
        exact ringChar.eq K 2
      exact ⟨↥(adjointGroup Tag.E6 K), inferInstance, inferInstance, ⟨e.trans φ⟩,
        modelSelD_adjointGroup (Or.inr (Or.inr (Or.inl rfl))) hK2 (by rw [hK]; exact hq4) hp hp2
          (by rw [hK]; exact hpq)⟩
    | twistedE6 q =>
      obtain ⟨hq2, hq4, hp3, h3⟩ := hi
      have hpq : p ∣ q.card ^ 2 - 1 := by
        rw [hp3]
        have hfac : q.card ^ 2 - 1 = (q.card + 1) * (q.card - 1) := by
          simpa using Nat.sq_sub_sq q.card 1
        rw [hfac]
        exact h3.mul_right _
      have hqc : q.card = 2 ^ q.exponent := by rw [TauCeti.PrimePower.card_def, hq2]
      obtain ⟨K, _, _, σ, hK, hσ, ⟨ψ⟩⟩ := exists_native_model_twisted
        CFSG.TauCetiBridge.Even.chevalleyBridgesAll.twistedE6 q hv
      have hK2 : Nat.card K = (2 ^ q.exponent) ^ 2 := by
        rw [hq2] at hK
        exact hK
      have hσ2 : ∀ c, σ c = c ^ (2 ^ q.exponent) := by
        rw [hq2] at hσ
        exact hσ
      rw [hqc] at hq4 hpq
      exact ⟨↥(twistedE6RootGroup K σ), inferInstance, inferInstance, ⟨e.trans ψ⟩,
        modelSelD_twistedE6 q.exponent_pos hK2 σ hσ2 hq4 hp hp2 hpq⟩
    | _ => exact False.elim hi
  | cyclic r hr => exact False.elim hi
  | alternating n hn => exact False.elim hi
  | sporadic s => exact False.elim hi

variable {Ω : Type} [Group Ω] [Finite Ω]

private theorem chevAut_mem_innAutDerived_of_innDiagOn (hp : p.Prime) (hp2 : p ≠ 2)
    {S : Subgroup Ω} {x : Ω} (hx : x ∈ Subgroup.normalizer (S : Set Ω))
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1)
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) :
    chevAut p S ⟨x, hx⟩ ∈ innAutDerived (PSimple p S) := by
  have hL : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  have hqS : CFSG.Open.IsQuasisimple (PQuot p S) := isQuasisimple_pQuot_of_glaPComponent hp hL
  obtain ⟨labL, hLabQuot, hinDiag⟩ := I141F.innDiagKind_chevAut hx hqS hInn
  have hcen : Subgroup.center (PSimple p S) = ⊥ := Y10F.center_centerQuot_eq_bot hqS
  haveI : Group.IsPerfect (PQuot p S) := ⟨hqS.1⟩
  have hperf : commutator (PSimple p S) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p S)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  have hLabPS : Y10F.HasLabel (PSimple p S) (· = labL) :=
    Y10F.hasLabel_of_equiv_centerQuot hperf
      ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).symm hLabQuot
  have hαp : chevAut p S ⟨x, hx⟩ ^ p = 1 := chevAut_pow_eq_one p S hx hxp
  by_cases hder : labL.tag = .B2der ∨ labL.tag = .G2der ∨ labL.tag = .twF4der
  · have hMq : CFSG.StandardType.MarkedModel labL
        (PSimple p S ⧸ Subgroup.center (PSimple p S)) :=
      CanonSubcomp.markedModel_of_hasLabel hLabPS
    let eZ : PSimple p S ⧸ Subgroup.center (PSimple p S) ≃* PSimple p S :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
    exact CFSG.ComponentClassification.OuterAutomorphisms.inner_le_innAutDerived _
      (mem_inner_of_pow_of_isPGroup_two_outer
        (T2021.t2021Layer_isPGroup_outer hder (hMq.of_mulEquiv eZ)) hp hp2 hαp)
  · rw [not_or, not_or] at hder
    exact I141F.Tri.mem_innAutDerived_of_innDiagKind_of_not_derived hcen hder hinDiag

private theorem exists_induced_aut (hp : p.Prime) (hp2 : p ≠ 2) {S : Subgroup Ω} {x : Ω}
    (hx : x ∈ Subgroup.normalizer (S : Set Ω)) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hSp : GLAPPrimeCore p ↥S = ⊥) (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S) {T : Type} [Group T]
    (e : ↥S ⧸ Subgroup.center ↥S ≃* T) :
    ∃ β : MulAut T, β ∈ innAutDerived T ∧ β ^ p = 1 ∧ β ≠ 1 ∧
      ∀ s : ↥S, centerQuotHom e (S.normalizerMonoidHom ⟨x, hx⟩ s) = β (centerQuotHom e s) := by
  have hL : GLAPComponent p S S := glaPComponent_self_p hSq hSp
  let eP : PSimple p S ≃* T := (pSimpleEquiv hSp).trans e
  have hσ : ∀ s : ↥S, centerQuotHom e s = eP (chevQuotHom p S s) := by
    intro s
    change e (QuotientGroup.mk s) = e (pSimpleEquiv hSp (chevQuotHom p S s))
    rw [pSimpleEquiv_chevQuotHom]
  refine ⟨MulAut.congr eP (chevAut p S ⟨x, hx⟩), ?_, ?_, ?_, ?_⟩
  · exact (CFSG.ComponentClassification.OuterAutomorphisms.mem_innAutDerived_congr eP).2
      (chevAut_mem_innAutDerived_of_innDiagOn hp hp2 hx hSq hSp hxp hInn)
  · rw [← map_pow, chevAut_pow_eq_one p S hx hxp, map_one]
  · intro h
    have h1 : chevAut p S ⟨x, hx⟩ = 1 := (MulAut.congr eP).injective (h.trans (map_one _).symm)
    exact hxC ((centMod_iff_centralizer hSp hx).1 ((chevAut_eq_one_iff hp hL hx).1 h1))
  · intro s
    rw [hσ, hσ, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, chevAut_chevQuotHom]

private theorem selCompCore_of_componentD (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω}
    {x : Ω} (hSq : CFSG.Open.IsQuasisimple ↥S) (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    (hx : x ∈ Subgroup.normalizer (S : Set Ω))
    (hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω))
    {T : Type} [Group T] [Finite T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) {β : MulAut T}
    (hβp : β ^ p = 1) (hβ1 : β ≠ 1)
    (hcompat : ∀ s : ↥S, centerQuotHom e (S.normalizerMonoidHom ⟨x, hx⟩ s) = β (centerQuotHom e s))
    {P JT : Subgroup T}
    (hP : P = ((⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω).subgroupOf S).map
      (centerQuotHom e))
    (hJTc : IsComponentOf JT (fixSubgroup β))
    (hJTp : p ∣ Nat.card (↥JT ⧸ Subgroup.center ↥JT)) (hJTa : ⁅P, JT⁆ ≠ ⊥)
    (hJTP : P ≤ JT ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (JT : Set T))) :
    ∃ J : Subgroup Ω, SelCompCore p S B₀ T' x J := by
  subst hP
  set S₁ : Subgroup Ω := ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ with hS₁def
  let σ : ↥S →* T := centerQuotHom e
  have hσs : Function.Surjective σ := centerQuotHom_surjective e
  have hσk : ∀ s : ↥S, σ s = 1 ↔ s ∈ Subgroup.center ↥S := centerQuotHom_eq_one_iff e
  have hσker : σ.ker ≤ Subgroup.center ↥S := fun s hs => (hσk s).1 hs
  set S₁' : Subgroup ↥S := S₁.subgroupOf S with hS₁'
  obtain ⟨J₀, hJ₀C, hJ₀map, hJ₀sub, hJ₀q, ⟨hJ₀e⟩, hJ₀cent⟩ :=
    lift_component_fix σ hσs hσker (S.normalizerMonoidHom ⟨x, hx⟩) β hcompat hJTc
  let ρ : ↥J₀ ≃* ↥(J₀.map S.subtype) :=
    Subgroup.equivMapOfInjective J₀ S.subtype S.subtype_injective
  have hCeq : fixSubgroup (S.normalizerMonoidHom ⟨x, hx⟩) =
      (S ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S := fixSubgroup_normalizerMonoidHom hx
  have hmapC : ((S ⊓ Subgroup.centralizer ({x} : Set Ω)).subgroupOf S).map S.subtype =
      S ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 inf_le_left
  have hJX : J₀.map S.subtype ≤ S ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    rw [← hmapC, ← hCeq]
    exact Subgroup.map_mono hJ₀C
  have hJsub : IsSubnormal (J₀.map S.subtype) (S ⊓ Subgroup.centralizer ({x} : Set Ω)) := by
    have := hJ₀sub.map S.subtype
    rwa [hCeq, hmapC] at this
  have hJq : CFSG.Open.IsQuasisimple ↥(J₀.map S.subtype) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv ρ.symm hJ₀q
  let ε₁ : ↥(J₀.map S.subtype) ⧸ Subgroup.center ↥(J₀.map S.subtype) ≃*
      ↥J₀ ⧸ Subgroup.center ↥J₀ := QuotientGroup.congr _ _ ρ.symm (Subgroup.map_center_eq ρ.symm)
  have ε := ε₁.trans hJ₀e
  refine ⟨J₀.map S.subtype, ⟨⟨hJX, hJsub, hJq⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [Nat.card_congr ε.toEquiv]
    exact hJTp
  · intro hbot
    apply hJTa
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    rintro _ ⟨s, hs, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hJ₀map] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot (show (s : Ω) ∈ S₁ from hs)
    have h2 : (j : Ω) * s = s * j :=
      Subgroup.mem_centralizer_iff.1 h1 (j : Ω) (Subgroup.mem_map_of_mem S.subtype hj)
    change σ j * σ s = σ s * σ j
    rw [← map_mul, ← map_mul]
    exact congrArg σ (Subtype.ext h2)
  · intro s hs
    have hsS : s ∈ S := (hS₁S hs).1
    have hsC : s ∈ Subgroup.centralizer ({x} : Set Ω) := (hS₁S hs).2
    have hmem : σ ⟨s, hsS⟩ ∈ JT ⊔ (fixSubgroup β ⊓ Subgroup.centralizer (JT : Set T)) :=
      hJTP (Subgroup.mem_map_of_mem σ (show (⟨s, hsS⟩ : ↥S) ∈ S₁' from hs))
    obtain ⟨b, hb, c, hc, hbc⟩ := (GL83.CompFam.mem_sup_of_commute (H := JT)
      (K := fixSubgroup β ⊓ Subgroup.centralizer (JT : Set T))
      (fun a ha c hc => Subgroup.mem_centralizer_iff.1 hc.2 a ha)).1 hmem
    rw [← hJ₀map] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    set d : ↥S := j⁻¹ * ⟨s, hsS⟩ with hd
    have hσd : σ d = c := by
      rw [hd, map_mul, map_inv, ← hbc]
      exact inv_mul_cancel_left _ _
    have hdcent : d ∈ Subgroup.centralizer (J₀ : Set ↥S) :=
      hJ₀cent d (by rw [hσd]; exact hc.2)
    have hjJ : (j : Ω) ∈ J₀.map S.subtype := Subgroup.mem_map_of_mem S.subtype hj
    have hdD : (d : Ω) ∈ S ⊓ Subgroup.centralizer ({x} : Set Ω) ⊓
        Subgroup.centralizer ((J₀.map S.subtype : Subgroup Ω) : Set Ω) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d.2, ?_⟩, ?_⟩
      · have hjC := (hJX hjJ).2
        have : (d : Ω) = (j : Ω)⁻¹ * s := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hjC) hsC
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨j', hj', rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hdcent j' hj')
    have hs_eq : s = (j : Ω) * (d : Ω) := by
      simp [hd]
    rw [hs_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjJ) (Subgroup.mem_sup_right hdD)
  · have hTs : IsSimpleGroup T := by
      haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
      exact e.symm.isSimpleGroup
    have hTnc : ∃ a b : T, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := (native_of_open_dx hSq).2.2
      exact ⟨e a, e b, fun h => hab (e.injective (by rwa [map_mul, map_mul]))⟩
    have hcomp : IsComponentOf JT (CFSG.LocalAnalysis.GLTheoremA.I142.centFix
        (Subgroup.zpowers β)) := by
      rw [CFSG.LocalAnalysis.GLTheoremA.I142C.centFix_zpowers']
      exact hJTc
    exact isChevSimple_of_equiv ε.symm
      (CFSG.LocalAnalysis.GLTheoremA.I142M.Three.chevCompTypes_holds T hTs hTnc
        (isChevSimple_of_equiv e hSc) p hp hp2 β hβp hβ1 JT hcomp)

private theorem selComp_or_a5_of_coreD (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω}
    {x : Ω} (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S)
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S)
    (hdvd : p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S)) {J : Subgroup Ω}
    (hJ : SelCompCore p S B₀ T' x J) :
    SelComp p S B₀ T' x J ∨
      (p = 3 ∧ IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)) ∧
        Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) := by
  by_cases h3 : p = 3
  · subst h3
    by_cases hm : GLAMarking (↥J) (fun lab _ _ _ _ _ => lab.n = 1)
    · right
      refine ⟨rfl, hJ.comp, ?_⟩
      obtain ⟨labS, hMS⟩ := exists_markedInnDiag hp hSq hdvd hInn
      obtain ⟨hperf, lab, hlam, hraw⟩ := hm
      obtain ⟨R, _, I, F, hs, hna, θ, hn1⟩ :=
        CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
      have hlabJ : LabelOf J lab := by
        refine ⟨hperf, lab, hlam, ?_⟩
        exact CFSG.StandardType.Canonical.largeEvenRawDatum_mono
          (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw
      rcases labS_dvd_of_labelOf hp hp2 hSn hxp hxC hMS hJ.comp hlam hlabJ with
        h | ⟨htag, hrank, -⟩
      · exfalso
        rw [hn1] at h
        have hS1 : labS.n = 1 := Nat.dvd_one.1 h
        refine hF2 rfl (CFSG.StandardType.Canonical.largeEvenMarking_mono
          (fun lab' R _ I F θ h => ?_) hMS)
        rw [h.1]
        exact hS1
      · refine card_centerQuot_of_label_twD ?_ hraw
        obtain ⟨t, r, n⟩ := lab
        simp only at htag hrank hn1
        subst htag hrank hn1
        rfl
    · exact Or.inl (hJ.toSelComp fun _ => hm)
  · exact Or.inl (hJ.toSelComp fun h => absurd h h3)

theorem selComp_or_a5_of_modelSelD (hp : p.Prime) (hp2 : p ≠ 2) {S B₀ T' : Subgroup Ω} {x : Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S))
    (hF2 : p = 3 → ¬ GLAMarking (↥S) (fun lab _ _ _ _ _ => lab.n = 1))
    (hxp : x ^ p = 1) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hInn : InnDiagOn p (Subgroup.zpowers x) S)
    (hS₁ : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥)
    (hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω))
    (hS₁2 : IsPGroup 2 ↥(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω))
    {T : Type} [Group T] [Finite T] (e : ↥S ⧸ Subgroup.center ↥S ≃* T) (hT : ModelSelD p T) :
    ∃ J : Subgroup Ω, SelComp p S B₀ T' x J ∨
      (p = 3 ∧ IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω)) ∧
        Nat.card (↥J ⧸ Subgroup.center ↥J) = 60) := by
  have hx : x ∈ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact Subgroup.mem_top x
  obtain ⟨β, hβmem, hβp, hβ1, hcompat⟩ := exists_induced_aut hp hp2 hx hSq hSp hxp hxC hInn e
  set S₁ : Subgroup Ω := ⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ with hS₁def
  let σ : ↥S →* T := centerQuotHom e
  set S₁' : Subgroup ↥S := S₁.subgroupOf S with hS₁'
  set P : Subgroup T := S₁'.map σ with hP
  have hPfix : P ≤ fixSubgroup β := by
    rintro _ ⟨s, hs, rfl⟩
    have hsx : (s : Ω) * x = x * s :=
      Subgroup.mem_centralizer_singleton_iff.1 (hS₁S (show (s : Ω) ∈ S₁ from hs)).2
    rw [CFSG.HardMathSupport.Solomon.Coordinator.mem_fixSubgroup, ← hcompat s]
    congr 1
    apply Subtype.ext
    change x * (s : Ω) * x⁻¹ = s
    rw [← hsx]
    group
  have hP2 : IsPGroup 2 ↥P := hS₁2.comap_subtype.map σ
  have hPne : P ≠ ⊥ :=
    map_centerQuotHom_ne_bot hp hp2 hSp hS₁ (hS₁S.trans inf_le_left) hS₁2 e
  obtain ⟨JT, hJTc, hJTp, hJTa, hJTP⟩ := hT β hβmem hβp hβ1 P hPfix hP2 hPne
  have hdvd : p ∣ Nat.card (↥S ⧸ Subgroup.center ↥S) := by
    rw [Nat.card_congr e.toEquiv]
    exact hJTp.trans
      ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card JT))
  obtain ⟨J, hJ⟩ := selCompCore_of_componentD hp hp2 hSq hSc hx hS₁S e hβp hβ1 hcompat rfl hJTc
    hJTp hJTa hJTP
  exact ⟨J, selComp_or_a5_of_coreD hp hp2 hSn hSq hF2 hxp hxC hInn hdvd hJ⟩

theorem t263SelWP_e6Shape : T263SelWP t263GE6Shape := by
  intro p hp hp2 Ω _ _ hK S B hSn hSq hSp hSc hcat hF2 hSB hΩ hB h4 hT hC B₀ hB₀ hdich hcase T'
    hT'ne hT'2 hT'S hBT' hker x hxB₀ hxC hxcomm
  obtain ⟨hBel, hBcard, -⟩ : IsElemAbelian p B ∧ Nat.card ↥B = p ^ GLATwoLocalRank p Ω ∧
      ∃ U : Subgroup Ω, U ≠ ⊥ ∧ IsPGroup 2 U ∧ B ≤ Subgroup.normalizer (U : Set Ω) := id hB
  have hB₀B : B₀ ≤ B := hB₀.1
  have hxB : x ∈ B := hB₀B hxB₀
  have hxp : x ^ p = 1 := hBel.2 x hxB
  have hInn : InnDiagOn p (Subgroup.zpowers x) S :=
    S10.innDiagOn_mono hB₀.2.1 (Subgroup.zpowers_le.2 hxB₀)
  obtain ⟨T, _, _, ⟨e⟩, hTsel⟩ := exists_modelSelD_e6Shape hp hp2 hcat
  obtain ⟨-, -, hPT'⟩ :=
    norm_data_dx hSn (fun a ha b hb => isElemAbelian_commute hBel ha hb) hB₀B hxB₀ hBT'
  have hS₁x : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      Subgroup.centralizer ({x} : Set Ω) := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    have h1 : g₁ ∈ Subgroup.centralizer ({x} : Set Ω) :=
      Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hBel (hB₀B hg₁) hxB)
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1 hg₂.2) (inv_mem h1)) (inv_mem hg₂.2)
  have hS₁S : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
      S ⊓ Subgroup.centralizer ({x} : Set Ω) := le_inf (hPT'.trans hT'S) hS₁x
  obtain ⟨J, hJ | ⟨hp3, hJc, h60⟩⟩ := selComp_or_a5_of_modelSelD hp hp2 hSn hSq hSp hSc hF2 hxp
    hxC hInn hxcomm hS₁S (hT'2.to_le hPT') e hTsel
  · exact Or.inr ⟨J, hJ⟩
  · subst hp3
    refine Or.inl (t263GConcl_of_a5 hSn hBel ?_ hxB hJc h60)
    rw [hBcard]
    exact Nat.pow_le_pow_right (by norm_num) h4

end CFSG.LocalAnalysis.GLTheoremA.T263.DX
