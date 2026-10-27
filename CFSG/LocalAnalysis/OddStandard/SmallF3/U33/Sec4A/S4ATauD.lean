module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauC
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4AB1A
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ACtxSteps
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ATauB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

namespace S4A

section Tau

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho : G}

theorem ctx_tau_exists (h : Ctx0 t L S x₁ x₂ lam rho) (hi : CtxIdxFacts t L S x₁ x₂ lam) :
    ∃ tau : G, CtxTauFacts t L S x₁ x₂ lam rho tau := by
  obtain ⟨hx₁L, hx₂L, hlamL⟩ := generators_mem_L h
  let x₁' : ↥L := ⟨x₁, hx₁L⟩
  let x₂' : ↥L := ⟨x₂, hx₂L⟩
  let lam' : ↥L := ⟨lam, hlamL⟩
  let rho' : ↥L := ⟨rho, h.rho_mem⟩
  have hf : Function.Injective L.subtype := L.subtype_injective
  have hw' : WreathRel x₁' x₂' lam' := WreathRel.of_injective L.subtype hf h.wreath
  have hBmap : (baseGrp x₁' x₂').map L.subtype = baseGrp x₁ x₂ :=
    map_baseGrp' L.subtype x₁' x₂'
  have hTmap : (wreathGrp x₁' x₂' lam').map L.subtype = wreathGrp x₁ x₂ lam :=
    map_wreathGrp' L.subtype x₁' x₂' lam'
  have hBmem : ∀ w : ↥L, w ∈ baseGrp x₁' x₂' ↔ (w : G) ∈ baseGrp x₁ x₂ := fun w => by
    rw [← hBmap]
    exact (Subgroup.mem_map_iff_mem hf).symm
  have hTmem : ∀ w : ↥L, w ∈ wreathGrp x₁' x₂' lam' ↔ (w : G) ∈ wreathGrp x₁ x₂ lam :=
    fun w => by
      rw [← hTmap]
      exact (Subgroup.mem_map_iff_mem hf).symm
  have hρN₀ : rho ∈ normalizer ((baseGrp x₁ x₂ : Subgroup G) : Set G) := by
    have := Subgroup.normalizer_commutator_ge_right (ctxW t x₁ x₂) (zpowers rho)
      (Subgroup.mem_zpowers rho)
    rwa [h.comm_rho] at this
  have hρN : ∀ w ∈ baseGrp x₁' x₂', rho' * w * rho'⁻¹ ∈ baseGrp x₁' x₂' := by
    intro w hw
    rw [hBmem] at hw ⊢
    exact (Subgroup.mem_normalizer_iff.mp hρN₀ (w : G)).mp hw
  have hρC : ∀ w ∈ baseGrp x₁' x₂', rho' * w = w * rho' → w = 1 := by
    intro w hw hc
    have hwB : (w : G) ∈ baseGrp x₁ x₂ := (hBmem w).mp hw
    have hc' : rho * (w : G) = (w : G) * rho := congrArg Subtype.val hc
    have hwW : (w : G) ∈ ctxW t x₁ x₂ := Subgroup.mem_sup_right hwB
    have hwC : (w : G) ∈ centralizer ({rho} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hc'.symm
    have hwP : (w : G) ∈ twoCore t := by
      have hmem : (w : G) ∈ ctxW t x₁ x₂ ⊓ centralizer ({rho} : Set G) := ⟨hwW, hwC⟩
      rwa [h.cent_rho] at hmem
    have hmem2 : (w : G) ∈ twoCore t ⊓ baseGrp x₁ x₂ := ⟨hwP, hwB⟩
    rw [pt_inf_base h, Subgroup.mem_bot] at hmem2
    exact Subtype.ext hmem2
  have hlr : lam' * rho' * lam'⁻¹ = rho'⁻¹ := Subtype.ext h.lam_rho
  have hord : orderOf rho' = 3 := (orderOf_injective L.subtype hf rho').symm.trans h.ord_rho
  have hcard : Nat.card (ctxConjHomS h).range = 64 := card_range_ctxConjHomS h hi.card_S
  have hTŜ : ∀ w ∈ wreathGrp x₁' x₂' lam', MulAut.conj w ∈ (ctxConjHomS h).range :=
    fun w hw => (ctxConjHomS_inner h).mpr ((hTmem w).mp hw)
  have hŜT : ∀ w : ↥L, MulAut.conj w ∈ (ctxConjHomS h).range → w ∈ wreathGrp x₁' x₂' lam' :=
    fun w hw => (hTmem w).mpr ((ctxConjHomS_inner h).mp hw)
  obtain ⟨α, hαŜ, hα⟩ := exists_alpha h.hyp.lieModel hw' hρN hρC hlr (ctxConjHomS h).range hcard
    hTŜ hŜT
  obtain ⟨s, hs⟩ := hαŜ
  have hsapp : ∀ x : ↥L, ((α x : ↥L) : G) = (s : G) * (x : G) * (s : G)⁻¹ := fun x => by
    rw [← hs]
    exact ctxConjHomS_apply h s x
  have key : ∀ a b : ↥L, α a = b → (s : G) * (a : G) * (s : G)⁻¹ = (b : G) := fun a b hab => by
    rw [← hsapp a, hab]
  have e₁ : (s : G) * x₁ * (s : G)⁻¹ = x₁⁻¹ := key x₁' x₁'⁻¹ hα.x₁
  have e₂ : (s : G) * x₂ * (s : G)⁻¹ = x₂⁻¹ := key x₂' x₂'⁻¹ hα.x₂
  have e₃ : (s : G) * lam * (s : G)⁻¹ = lam := key lam' lam' hα.lam
  have e₄ : (s : G) * rho * (s : G)⁻¹ = rho := key rho' rho' hα.rho
  have hsq : (s : G) ^ 2 ∈ twoCore t := by
    have h1 : ctxConjHomS h (s * s) = 1 := by
      rw [map_mul, hs]
      exact hα.sq
    have h2 : s * s ∈ (ctxConjHomS h).ker := MonoidHom.mem_ker.mpr h1
    rw [ctxConjHomS_ker h, Subgroup.mem_subgroupOf] at h2
    rw [pow_two]
    exact h2
  have hnot : (s : G) ∉ twoCore t ⊔ L := by
    intro hmem
    obtain ⟨k, hk⟩ := (ctxConjHom_inner_iff h.hyp ⟨(s : G), h.le_invCent s.2⟩).mpr hmem
    apply hα.outer k
    rw [← hs]
    exact hk
  have hfix : (autFixed α).map L.subtype = L ⊓ centralizer ({(s : G)} : Set G) := by
    ext g
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨k.2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hk' : ((α k : ↥L) : G) = (k : G) := congrArg Subtype.val hk
      rw [hsapp] at hk'
      calc (k : G) * (s : G) = ((s : G) * (k : G) * (s : G)⁻¹) * (s : G) := by rw [hk']
        _ = (s : G) * (k : G) := by group
    · intro hg
      obtain ⟨hgL, hgC⟩ := Subgroup.mem_inf.mp hg
      rw [Subgroup.mem_centralizer_singleton_iff] at hgC
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      apply Subtype.ext
      rw [hsapp]
      calc (s : G) * g * (s : G)⁻¹ = (g * (s : G)) * (s : G)⁻¹ := by rw [hgC]
        _ = g := by group
  have hcentL : L ⊓ centralizer ({(s : G)} : Set G) =
      closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Set G) := by
    have hm : (closure ({x₁' ^ 2, (x₁' * x₂') ^ 2, rho', lam'} : Set ↥L)).map L.subtype =
        closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, rho, lam} : Set G) :=
      map_closure_yzrl' L.subtype x₁' x₂' rho' lam'
    rw [← hfix, hα.autFixed_eq h.hyp.lieModel hw' hord, hm]
  have hperm : Nonempty (↥(L ⊓ centralizer ({(s : G)} : Set G)) ≃* Equiv.Perm (Fin 4)) := by
    obtain ⟨e⟩ := hα.perm_four h.hyp.lieModel
    exact ⟨(((autFixed α).equivMapOfInjective L.subtype hf).trans
      (MulEquiv.subgroupCongr hfix)).symm.trans e⟩
  have hcentT : wreathGrp x₁ x₂ lam ⊓ centralizer ({(s : G)} : Set G) =
      closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set G) := by
    have hm : (closure ({x₁' ^ 2, (x₁' * x₂') ^ 2, lam'} : Set ↥L)).map L.subtype =
        closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set G) :=
      map_closure_yzl' L.subtype x₁' x₂' lam'
    have h1 := congrArg (Subgroup.map L.subtype) (hα.wreathGrp_inf_autFixed h.hyp.lieModel hw')
    rw [Subgroup.map_inf _ _ _ hf, hTmap, hfix, hm, ← inf_assoc,
      inf_eq_left.mpr (wreathGrp_le_L_ctx0 h)] at h1
    exact h1
  have hdih : Nonempty (↥(closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set G)) ≃*
      DihedralGroup 4) := by
    obtain ⟨e⟩ := hα.dihedral h.hyp.lieModel hw'
    have hm : (closure ({x₁' ^ 2, (x₁' * x₂') ^ 2, lam'} : Set ↥L)).map L.subtype =
        closure ({x₁ ^ 2, (x₁ * x₂) ^ 2, lam} : Set G) :=
      map_closure_yzl' L.subtype x₁' x₂' lam'
    exact ⟨(((closure ({x₁' ^ 2, (x₁' * x₂') ^ 2, lam'} : Set ↥L)).equivMapOfInjective
      L.subtype hf).trans (MulEquiv.subgroupCongr hm)).symm.trans e⟩
  refine ⟨(s : G), ?_⟩
  exact
    { S_eq := S_eq_of_mem h hi.index_PT s.2 hnot
      tau_mem := s.2
      tau_not_mem := hnot
      tau_sq_mem := hsq
      tau_x₁ := e₁
      tau_x₂ := e₂
      tau_lam := by
        calc (s : G) * lam = ((s : G) * lam * (s : G)⁻¹) * (s : G) := by group
          _ = lam * (s : G) := by rw [e₃]
      tau_rho := by
        calc (s : G) * rho = ((s : G) * rho * (s : G)⁻¹) * (s : G) := by group
          _ = rho * (s : G) := by rw [e₄]
      cent_L_tau := hcentL
      perm_four := hperm
      cent_T_tau := hcentT
      dihedral := hdih }

end Tau

end S4A

theorem ctxTau_holds : CtxTauStmt :=
  fun h _ hi _ => S4A.ctx_tau_exists h hi

end CFSG.OddStandard.SmallF3.HarrisU33
