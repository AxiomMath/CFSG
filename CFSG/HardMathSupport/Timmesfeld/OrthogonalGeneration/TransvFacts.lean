module

public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvPi
public import CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration.TransvT

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.Open CFSG.LocalAnalysis.GLTheoremB

@[expose] def PiDataOf (p : ℕ) (G : Type*) [Group G] : Prop :=
  IsSimpleGroup G ∧ (∃ a b : G, a * b ≠ b * a) ∧ p ∣ Nat.card G ∧
    ∃ (n' : ℕ) (ε' : Bool), 1 ≤ n' ∧ IsOmegaTwo ε' (n' + 1) G ∧ HasFixedPointFreeOrder ε' n' p

variable {X : Type*} [Group X] {K : Subgroup X} {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V} {t : V ≃ₗ[ZMod 2] V}
  {B : Subgroup X} {e : ↥K ≃* ↥(elementaryGroup Q)}

@[expose] def Kb (e : ↥K ≃* ↥(elementaryGroup Q)) (Yh : B →* ↥(elementaryGroup Q)) (b : B) :
    Subgroup X :=
  liftSub e (orthJ Q (fixSub (Subgroup.zpowers (Yh b : V ≃ₗ[ZMod 2] V))))

section Facts

variable {Yh : B →* ↥(elementaryGroup Q)}

theorem Yh_mem_orthogonalGroup (b : B) :
    (Yh b : V ≃ₗ[ZMod 2] V) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  elementaryGroup_le_orthogonalGroup Q (Yh b).2

theorem Kb_le_inf_centralizer (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hY : ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V)) (b : B) :
    Kb e Yh b ≤ K ⊓ Subgroup.centralizer ({(b : X)} : Set X) :=
  ActsAsConj.liftSub_le_inf_centralizer (hBN b.2) (hY b)
    (commute_of_forall_apply_eq_orthJ (Yh_mem_orthogonalGroup b)
      (fun _ hw => mem_fixSub_zpowers.mp hw))

theorem normal_Kb (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hY : ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V)) (b : B) :
    ((Kb e Yh b).subgroupOf (K ⊓ Subgroup.centralizer ({(b : X)} : Set X))).Normal := by
  refine normal_subgroupOf_liftSub (Kb_le_inf_centralizer hBN hY b) ?_
  intro k hk hkC z hz
  have hc : (b : X) * k = k * b :=
    Subgroup.mem_centralizer_iff.mp hkC (b : X) rfl
  have h1 := (ActsAsConj.commute_iff (hBN b.2) (hY b) hk).mp hc
  exact (mem_orthJ_conj_iff (embK_mem e ⟨k, hk⟩ |> elementaryGroup_le_orthogonalGroup Q) h1.symm z).mp hz

theorem B_le_normalizer_Kb {p : ℕ} (hB : IsElemAbelian p B) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hY : ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V)) (b : B) :
    B ≤ Subgroup.normalizer (Kb e Yh b : Set X) := by
  intro x hx
  refine ActsAsConj.mem_normalizer_liftSub (hBN hx) (hY ⟨x, hx⟩) fun z => ?_
  refine mem_orthJ_conj_iff (Yh_mem_orthogonalGroup ⟨x, hx⟩) ?_ z
  have := hB.1.is_comm.comm (⟨x, hx⟩ : B) b
  have h2 := congrArg (fun y : B => ((Yh y : ↥(elementaryGroup Q)) : V ≃ₗ[ZMod 2] V)) this
  simpa using h2

theorem T_le_normalizer_Kb {T : Subgroup X} (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hcommt : ∀ b : B, (Yh b : V ≃ₗ[ZMod 2] V) * t = t * (Yh b : V ≃ₗ[ZMod 2] V))
    (ht : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hTact : ∀ x ∈ T, ActsAsConj e x 1 ∨ ActsAsConj e x t) (b : B) :
    T ≤ Subgroup.normalizer (Kb e Yh b : Set X) := by
  intro x hx
  rcases hTact x hx with h | h
  · refine ActsAsConj.mem_normalizer_liftSub (hTN hx) h fun z => ?_
    simp
  · refine ActsAsConj.mem_normalizer_liftSub (hTN hx) h fun z => ?_
    exact mem_orthJ_conj_iff ht (hcommt b).symm z

theorem PiDataOf.of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    (h : PiDataOf p G) : PiDataOf p H := by
  obtain ⟨hs, ⟨a, b, hab⟩, hdvd, n', ε', h1, h2, h3⟩ := h
  refine ⟨(haveI := hs; φ.symm.isSimpleGroup), ⟨φ a, φ b, fun h => hab (φ.injective (by rw [map_mul, map_mul, h]))⟩,
    (Nat.card_congr φ.toEquiv) ▸ hdvd, n', ε', h1, ?_, h3⟩
  cases ε'
  · obtain ⟨ψ⟩ := h2
    exact ⟨φ.symm.trans ψ⟩
  · obtain ⟨ψ⟩ := h2
    exact ⟨φ.symm.trans ψ⟩

theorem piDataOf_Kb {p : ℕ} (b : B)
    (hpi : PiDataOf p ↥(orthJ Q (fixSub (Subgroup.zpowers (Yh b : V ≃ₗ[ZMod 2] V))))) :
    PiDataOf p ↥(Kb e Yh b) :=
  hpi.of_mulEquiv (liftSubEquiv e (orthJ_le_elementaryGroup Q _)).symm

theorem glaPComponent_Kb {p : ℕ} (hp : p.Prime) [Finite X] (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hY : ∀ b : B, ActsAsConj e (b : X) (Yh b : V ≃ₗ[ZMod 2] V)) (b : B)
    (hpi : PiDataOf p ↥(Kb e Yh b)) :
    GLAPComponent p (K ⊓ Subgroup.centralizer ({(b : X)} : Set X)) (Kb e Yh b) := by
  obtain ⟨hs, hnc, hdvd, -⟩ := hpi
  exact GL83.PiGen.glaPComponent_of_normal_simple hp (Kb_le_inf_centralizer hBN hY b)
    (normal_Kb hBN hY b) hnc hdvd

theorem isPiGroup_Kb {p : ℕ} (hp : p.Prime) [Finite X] (b : B) (hpi : PiDataOf p ↥(Kb e Yh b)) :
    LocalAnalysis.GLTheoremB.IsPiGroup p ↥(Kb e Yh b) := by
  obtain ⟨hs, hnc, hdvd, hΩ⟩ := hpi
  exact isPiGroup_of_simple_data hp hnc hdvd hΩ

theorem not_T_le_centralizer_Kb [Module.Finite (ZMod 2) V] {p : ℕ} (hQ : (polarBilin Q).Nondegenerate)
    (hodd : Odd p) {T : Subgroup X} (hTN : T ≤ Subgroup.normalizer (K : Set X))
    (hcommt : ∀ b : B, (Yh b : V ≃ₗ[ZMod 2] V) * t = t * (Yh b : V ≃ₗ[ZMod 2] V))
    {v : V} {f : V →ₗ[ZMod 2] ZMod 2} (hv : v ≠ 0) (hf0 : f ≠ 0) (htv : ∀ x, t x = x + f x • v)
    (hTex : ∃ x ∈ T, ActsAsConj e x t) (b : B) (hbp : (Yh b : V ≃ₗ[ZMod 2] V) ^ p = 1)
    (h4 : 4 ≤ finrank (ZMod 2) (fixSub (Subgroup.zpowers (Yh b : V ≃ₗ[ZMod 2] V)))) :
    ¬ T ≤ Subgroup.centralizer (Kb e Yh b : Set X) := by
  intro hTC
  obtain ⟨x0, hx0T, hx0⟩ := hTex
  refine not_commute_orthJ_transv hQ hodd (Yh_mem_orthogonalGroup b) hbp hv hf0 htv
    (hcommt b) h4 fun z hz => ?_
  obtain ⟨k, hk1, hk2⟩ := exists_mem_liftSub e (orthJ_le_elementaryGroup Q _) hz
  have hc : x0 * (k : X) = (k : X) * x0 :=
    (Subgroup.mem_centralizer_iff.mp (hTC hx0T) (k : X) hk1).symm
  rw [← hk2]
  exact (ActsAsConj.commute_iff (hTN hx0T) hx0 k.2).mp hc

end Facts

end CFSG.HardMathSupport.Timmesfeld.OrthogonalGeneration
