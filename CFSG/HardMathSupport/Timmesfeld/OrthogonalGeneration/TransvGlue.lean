module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvFacts
public import CFSG.HardMathSupport.Timmesfeld.Proving.PlaneImage

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {X : Type*} [Group X] {K : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {B : Subgroup X} {e : ↥K ≃* ↥(elementaryGroup Q)}

theorem card_range_rho {p : ℕ} [Finite X] {D : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) (hDB : D ≤ B)
    (hcO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ y ∈ elementaryGroup Q, g * y = y * g) → g = 1)
    {Yh : B →* ↥(elementaryGroup Q)} (hY : ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V))
    (hrange : Nat.card (Proving.planeAct (hDB.trans hBN)).range = p ^ 2) :
    Nat.card (((elementaryGroup Q).subtype.comp Yh).comp (Subgroup.inclusion hDB)).range =
      p ^ 2 := by
  set ρD : D →* (V ≃ₗ[ZMod 2] V) := ((elementaryGroup Q).subtype.comp Yh).comp
    (Subgroup.inclusion hDB) with hρD
  have hker : ρD.ker = (Proving.planeAct (hDB.trans hBN)).ker := by
    ext d
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hdB : (d : X) ∈ B := hDB d.2
    constructor
    · intro hd
      have hd' : (Yh ⟨d, hdB⟩ : V ≃ₗ[ZMod 2] V) = 1 := hd
      refine MulEquiv.ext fun k => Subtype.ext ?_
      change (d : X) * k * (d : X)⁻¹ = k
      have h1 := (ActsAsConj.commute_iff (hBN hdB) (hY ⟨d, hdB⟩) k.2).mpr (by
        rw [hd']
        simp)
      exact mul_inv_eq_iff_eq_mul.mpr h1
    · intro hd
      have hc : ∀ k : ↥K, (d : X) * k = k * d := by
        intro k
        have := congrArg (fun φ : MulAut ↥K => ((φ k : K) : X)) hd
        have h2 : (d : X) * k * (d : X)⁻¹ = k := this
        exact mul_inv_eq_iff_eq_mul.mp h2
      change (Yh ⟨d, hdB⟩ : V ≃ₗ[ZMod 2] V) = 1
      refine hcO _ (Yh_mem_orthogonalGroup (Yh := Yh) ⟨(d : X), hdB⟩) fun y hy => ?_
      obtain ⟨k, hk⟩ := e.surjective ⟨y, hy⟩
      have h3 := (ActsAsConj.commute_iff (hBN hdB) (hY ⟨d, hdB⟩) k.2).mp (hc k)
      have h4 : (e k : V ≃ₗ[ZMod 2] V) = y := by rw [hk]
      rw [embK_apply, h4] at h3
      exact h3
  have h1 := Subgroup.card_ker_mul_card_range ρD
  have h2 := Subgroup.card_ker_mul_card_range (Proving.planeAct (hDB.trans hBN))
  rw [hker] at h1
  have hpos : 0 < Nat.card (Proving.planeAct (hDB.trans hBN)).ker := Nat.card_pos
  have := h1.trans h2.symm
  rw [hrange] at this
  exact Nat.eq_of_mul_eq_mul_left hpos this

theorem transv_case_two [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T D : Subgroup X}
    (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hTN : T ≤ Subgroup.normalizer (K : Set X)) (hBT : B ≤ Subgroup.normalizer (T : Set X))
    (hDB : D ≤ B) [Module.Finite (ZMod 2) V] (hQ : (polarBilin Q).Nondegenerate)
    (hAut : ∀ σ : MulAut ↥(elementaryGroup Q), σ ^ p = 1 →
      ∃ y : ↥(elementaryGroup Q), σ = MulAut.conj y)
    (hcenterO : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      (∀ x ∈ elementaryGroup Q, g * x = x * g) → g = 1)
    (hfix : ∀ E : Subgroup (V ≃ₗ[ZMod 2] V), E ≤ TauCeti.QuadraticMap.orthogonalGroup Q →
      (∀ x ∈ E, x ^ p = 1) → ∃ P : HypPair Q, ∀ g ∈ E, g P.e = P.e ∧ g P.f = P.f)
    (hPi : ∀ g ∈ TauCeti.QuadraticMap.orthogonalGroup Q, g ^ p = 1 →
      4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers g)) →
        IsSimpleGroup ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          (∃ a b : ↥(orthJ Q (fixSub (Subgroup.zpowers g))), a * b ≠ b * a) ∧
          p ∣ Nat.card ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
          ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧
            IsOmegaTwo ε' (n' + 1) ↥(orthJ Q (fixSub (Subgroup.zpowers g))) ∧
            HasFixedPointFreeOrder ε' n' p)
    {t : V ≃ₗ[ZMod 2] V} (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {v : V}
    {f : V →ₗ[ZMod 2] ZMod 2} (hv : v ≠ 0) (hf0 : f ≠ 0) (htv : ∀ x, t x = x + f x • v)
    (hTact : ∀ x ∈ T, ActsAsConj e x 1 ∨ ActsAsConj e x t) (hTex : ∃ x ∈ T, ActsAsConj e x t)
    (hrange : Nat.card (Proving.planeAct (hDB.trans hBN)).range = p ^ 2) :
    ∃ (𝒟 : Set X) (Kf : X → Subgroup X), (∀ d ∈ 𝒟, d ∈ D ∧ d ≠ 1) ∧
      (∀ d ∈ 𝒟, GLAPComponent p (K ⊓ Subgroup.centralizer ({d} : Set X)) (Kf d) ∧
        B ⊔ T ≤ Subgroup.normalizer (Kf d : Set X) ∧ LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kf d) ∧
        ¬ T ≤ Subgroup.centralizer (Kf d : Set X)) ∧
      K = ⨆ d ∈ 𝒟, Kf d := by
  classical
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcenter := hcenter_of_hcenterO hcenterO
  obtain ⟨Yh, hY⟩ := exists_action_hom hB hBN e hAut hcenter
  have ht1 : t ≠ 1 := by
    intro h1
    obtain ⟨y, hy⟩ : ∃ y, f y ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (LinearMap.ext h)
    have := htv y
    rw [h1] at this
    have h2 : f y • v = 0 := by
      have h3 : y = y + f y • v := this
      simpa using h3.symm
    rcases smul_eq_zero.mp h2 with h | h
    · exact hy h
    · exact hv h
  have hcommt := commute_of_actsAsConj_transv hBN hTN hBT hcenterO hY ht ht1 hTact hTex
  have hρp : ∀ b : B, (Yh b : V ≃ₗ[ZMod 2] V) ^ p = 1 := by
    intro b
    have hbp : b ^ p = 1 := Subtype.ext (hB.2 b b.2)
    have h1 : (Yh b : ↥(elementaryGroup Q)) ^ p = 1 := by rw [← map_pow, hbp, map_one]
    have h2 := congrArg (fun z : ↥(elementaryGroup Q) => (z : V ≃ₗ[ZMod 2] V)) h1
    simpa using h2
  have hρcomm : ∀ a b : B, (Yh a : V ≃ₗ[ZMod 2] V) * (Yh b : V ≃ₗ[ZMod 2] V) =
      (Yh b : V ≃ₗ[ZMod 2] V) * (Yh a : V ≃ₗ[ZMod 2] V) := by
    intro a b
    have := hB.1.is_comm.comm a b
    have h := congrArg (fun y : B => ((Yh y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V)) this
    simpa using h
  set ρD : D →* (V ≃ₗ[ZMod 2] V) := ((elementaryGroup Q).subtype.comp Yh).comp
    (Subgroup.inclusion hDB) with hρD
  have hρD_apply : ∀ d : D, ρD d = (Yh ⟨(d : X), hDB d.2⟩ : V ≃ₗ[ZMod 2] V) := fun d => rfl
  set A : Subgroup (V ≃ₗ[ZMod 2] V) := ρD.range with hA
  have hAO : A ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨d, rfl⟩
    rw [hρD_apply]
    exact Yh_mem_orthogonalGroup _
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    rintro _ ⟨d, rfl⟩ _ ⟨d', rfl⟩
    rw [hρD_apply, hρD_apply]
    exact hρcomm _ _
  have hAexp : ∀ x ∈ A, x ^ p = 1 := by
    rintro _ ⟨d, rfl⟩
    rw [hρD_apply]
    exact hρp _
  have hAcard : Nat.card A = p ^ 2 := card_range_rho hBN hDB hcenterO hY hrange
  obtain ⟨P, hP⟩ := hfix A hAO hAexp
  have hgen := elementaryGroup_le_iSup_orthJ hp hp2 hQ hcenterO A hAO hAcomm hAexp hAcard P
    (fun h hh => (hP h hh).1) (fun h hh => (hP h hh).2)
  let ρX : X → (V ≃ₗ[ZMod 2] V) := fun x => if h : x ∈ B then (Yh ⟨x, h⟩ : V ≃ₗ[ZMod 2] V) else 1
  have hρX : ∀ (x : X) (h : x ∈ B), ρX x = (Yh ⟨x, h⟩ : V ≃ₗ[ZMod 2] V) := fun x h => by simp [ρX, h]
  let Kf : X → Subgroup X := fun x => liftSub e (orthJ Q (fixSub (Subgroup.zpowers (ρX x))))
  have hKf : ∀ (x : X) (h : x ∈ B), Kf x = Kb e Yh ⟨x, h⟩ := fun x h => by
    show liftSub e (orthJ Q (fixSub (Subgroup.zpowers (ρX x)))) = _
    rw [hρX x h]
    rfl
  let 𝒟 : Set X := {d | d ∈ D ∧ ρX d ≠ 1 ∧ 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers (ρX d)))}
  refine ⟨𝒟, Kf, ?_, ?_, ?_⟩
  · rintro d ⟨hdD, hne, -⟩
    refine ⟨hdD, fun h => hne ?_⟩
    have hdB : d ∈ B := hDB hdD
    rw [hρX d hdB]
    have : (⟨d, hdB⟩ : B) = 1 := Subtype.ext h
    rw [this, map_one]
    rfl
  · rintro d ⟨hdD, hne, h4⟩
    have hdB : d ∈ B := hDB hdD
    rw [hρX d hdB] at hne h4
    have hpi : PiDataOf p ↥(Kb e Yh ⟨d, hdB⟩) :=
      piDataOf_Kb ⟨d, hdB⟩ (hPi _ (Yh_mem_orthogonalGroup _) (hρp _) h4)
    rw [hKf d hdB]
    exact ⟨glaPComponent_Kb hp hBN hY ⟨d, hdB⟩ hpi,
      sup_le (B_le_normalizer_Kb hB hBN hY ⟨d, hdB⟩)
        (T_le_normalizer_Kb hTN hcommt ht hTact ⟨d, hdB⟩),
      isPiGroup_Kb hp ⟨d, hdB⟩ hpi,
      not_T_le_centralizer_Kb hQ hodd hTN hcommt hv hf0 htv hTex ⟨d, hdB⟩ (hρp _) h4⟩
  · let J : {d // d ∈ 𝒟} → Subgroup (V ≃ₗ[ZMod 2] V) :=
      fun i => orthJ Q (fixSub (Subgroup.zpowers (ρX i.1)))
    have hsup : elementaryGroup Q ≤ ⨆ i, J i := by
      refine hgen.trans (iSup₂_le fun a ha => ?_)
      obtain ⟨⟨d, hdD⟩, rfl⟩ := ha.1
      have hdB : d ∈ B := hDB hdD
      have hd𝒟 : d ∈ 𝒟 := by
        refine ⟨hdD, ?_, ?_⟩
        · rw [hρX d hdB]
          exact ha.2.1
        · rw [hρX d hdB]
          exact ha.2.2
      have := le_iSup J ⟨d, hd𝒟⟩
      simp only [J] at this
      rw [hρX d hdB] at this
      exact this
    have key := liftSub_iSup_eq e J (fun i => orthJ_le_elementaryGroup Q _) hsup
    rw [← key, iSup_subtype']

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
