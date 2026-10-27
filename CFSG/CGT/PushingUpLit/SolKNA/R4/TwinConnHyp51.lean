module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinConnQuiet
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinUActsPf
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameConn
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtU

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open scoped commutatorElement

section Hyp51Quiet

variable {G : Type} [Group G] [Finite G]

theorem hyp51At_of_quietR {B : Subgroup G} (hB : IsElemAbelian 2 B) {a c : G} (haB : a ∈ B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (hq : Quiet c a haC) : Hyp51At B c :=
  have key : ∀ {L : Subgroup (OddQuot c)}, CFSG.IsComponent L → MovedByAll B c L → False := by
    intro L hL hm
    obtain ⟨w, hw, hne⟩ := hm _ (oddQuotMk_mem_modOdd haB haC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC)
    exact hne (hq L hL w hw)
  ⟨fun _ _ h₁ _ m₁ _ => (key h₁ m₁).elim, fun _ hL hm => (key hL hm).elim⟩

end Hyp51Quiet

section Frame


variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {r n : ℕ}
  {K K' J : Subgroup G} {z u t : G}

theorem nbr_cmR (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R)
    {N J : Subgroup G} {z t : G} (hN : N ∈ CoreAssembly.conjClass (tightCore R))
    (hz : IsUniqueInvolution N z)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) N) (ht : IsUniqueInvolution J t)
    (htz : t ≠ z) (hzt : z * t = t * z) {c : G} (hc : c = t ∨ c = z * t) :
    c ∈ centralizerModOdd ⊤ N ∧ c * c = 1 ∧ c ≠ 1 := by
  obtain ⟨SK, hK⟩ := exists_datum_atR h hRc hN hz
  have hRcK : tightCore N = N := TwinVtx.tightCore_eq_of_mem hRc hN
  have hJe : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore N)) (tightCore N) := by
    rw [hRcK, TwinVtx.conjClass_eq_of_mem hN]
    exact hJ
  obtain ⟨ht2, -, htm⟩ := TwinEdge.edge_involution hK.datum hRcK hK.hyp hJe ht htz
  have hzm : z ∈ centralizerModOdd ⊤ N :=
    mem_centralizerModOdd_of_commutator hz.sq fun r hr => by
      have : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hK.datum.cent hr)
      have h1 : ⁅z, r⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this.symm
      rw [h1]
      exact Subgroup.one_mem _
  refine ⟨?_, ?_, ?_⟩
  · rcases hc with rfl | rfl
    · exact htm
    · exact Subgroup.mul_mem _ hzm htm
  · rcases hc with rfl | rfl
    · exact ht2
    · calc z * t * (z * t) = z * (t * z) * t := by group
        _ = z * (z * t) * t := by rw [← hzt]
        _ = (z * z) * (t * t) := by group
        _ = 1 := by rw [hz.sq, ht2, one_mul]
  · rcases hc with rfl | rfl
    · exact ht.ne_one
    · intro e
      have h1 : t = z⁻¹ := eq_inv_of_mul_eq_one_right e
      rw [inv_eq_of_mul_eq_one_right hz.sq] at h1
      exact htz h1


theorem u_cmR (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hum : u ∈ centralizerModOdd ⊤ J) {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t) :
    c ∈ centralizerModOdd ⊤ J ∧ c * c = 1 ∧ c ≠ 1 := by
  obtain ⟨SJ, hJd⟩ := exists_datum_atR h hRc hf.hJ.1 hf.ht
  have hRcJ : tightCore J = J := TwinVtx.tightCore_eq_of_mem hRc hf.hJ.1
  have hΩ := h.hyp
  have hKe : K ∈ omegaNbr (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, TwinVtx.conjClass_eq_of_mem hf.hJ.1]
    exact Q3CL.T3.omegaNbr_symm Sec6Gen.l6_2Gen hΩ hf.mem hf.hJ.1
      (hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz))
  obtain ⟨hz2, -, hzm⟩ := TwinEdge.edge_involution hJd.datum hRcJ hJd.hyp hKe hf.hz hf.t_ne_z.symm
  have htm : t ∈ centralizerModOdd ⊤ J :=
    mem_centralizerModOdd_of_commutator hf.ht.sq fun r hr => by
      have : r * t = t * r := Subgroup.mem_centralizer_singleton_iff.mp (hJd.datum.cent hr)
      have h1 : ⁅t, r⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact this.symm
      rw [h1]
      exact Subgroup.one_mem _
  obtain ⟨hcB, hc1, -, -, -, -⟩ := ucoset_facts hΩ hf hc
  have hcm : c ∈ centralizerModOdd ⊤ J := by
    rcases hc with rfl | rfl | rfl | rfl
    · exact hum
    · exact Subgroup.mul_mem _ hzm hum
    · exact Subgroup.mul_mem _ hum htm
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hzm hum) htm
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  exact ⟨hcm, (sq c).symm.trans (hB.2 c hcB), hc1⟩


theorem quiet_nbr_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    {M M'' J : Subgroup G} {z t : G} (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    (hz : IsUniqueInvolution M z)
    (hM'' : M'' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) M) (hne : M'' ≠ M)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M)
    (hJ'' : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M'')
    (ht : IsUniqueInvolution J t) (htz : t ≠ z) (hzt : z * t = t * z) {c : G}
    (hc : c = t ∨ c = z * t) (hzc : z ∈ Subgroup.centralizer ({c} : Set G)) :
    Quiet c z hzc := by
  obtain ⟨SK, hK⟩ := exists_datum_atR h hRc hM hz
  have hRcK : tightCore M = M := TwinVtx.tightCore_eq_of_mem hRc hM
  have hz'' : IsUniqueInvolution M'' z := isUniqueInvolution_of_mem_twinSet hz hM''
  have hM''Ω : M'' ∈ CoreAssembly.conjClass (tightCore R) := hM''.1
  obtain ⟨hcm, hc2, hc1⟩ := nbr_cmR h hRc hM hz hJ ht htz hzt hc
  obtain ⟨hcm'', -, -⟩ := nbr_cmR h hRc hM''Ω hz'' hJ'' ht htz hzt hc
  have hcK'' : c ∈ Balance.Bootstrap.trivialOnQuot M'' := ⟨hcm''.2.1, fun x hx => hcm''.2.2.2 x hx⟩
  have hM''tw : M'' ∈ twinSet (CoreAssembly.conjClass (tightCore M)) (tightCore M) := by
    rw [hRcK, TwinVtx.conjClass_eq_of_mem hM]
    exact hM''
  have hne' : M'' ≠ tightCore M := by rw [hRcK]; exact hne
  exact quiet_of_twin_R h4 hT hK hRcK hZ hc2 hc1 hcm hzc hM''tw hne' hcK''

theorem hyp51At_nbr_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) {c : G}
    (hc : c = t ∨ c = z * t) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hΩ := h.hyp
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  have hzB := TwinFrame.z_mem z u t
  have htB := TwinFrame.t_mem z u t
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
    rcases hc with rfl | rfl
    · exact htB
    · exact Subgroup.mul_mem _ hzB htB
  have hzc := Lemma52Proof.le_centralizer_of_mem hB hcB hzB
  have hc1 : c ≠ 1 := by
    rcases hc with rfl | rfl
    · exact hf.ht.ne_one
    · exact TwinFrame.zt_ne_one hf
  have hac : z ≠ c := by
    rcases hc with rfl | rfl
    · exact hf.t_ne_z.symm
    · intro e
      have : t = 1 := by
        have h1 : z * t = z * 1 := by rw [mul_one]; exact e.symm
        exact mul_left_cancel h1
      exact hf.ht.ne_one this
  have hzt : z * t = t * z := A7Q.Gen.comm_zt hΩ hf
  have hJK := hf.hJ.2 K (mem_twinSet_self hf.mem hf.hz)
  have hJK' := hf.hJ.2 K' hf.hK'
  have hq := quiet_nbr_R h4 hT h hRc hZ hf.mem hf.hz hf.hK' hf.hne hJK hJK' hf.ht hf.t_ne_z hzt hc
    hzc
  exact hyp51At_of_quietR hB hzB hcB hc1 hf.hz.ne_one hac hzc hq

theorem quiet_u_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (hum : u ∈ centralizerModOdd ⊤ J) {J' : Subgroup G}
    (hf' : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J' t)
    (hJ' : J' ∈ twinSet (CoreAssembly.conjClass (tightCore R)) J) (hJne : J' ≠ J)
    (hum' : u ∈ centralizerModOdd ⊤ J') {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t)
    (htc : t ∈ Subgroup.centralizer ({c} : Set G)) : Quiet c t htc := by
  obtain ⟨SJ, hJd⟩ := exists_datum_atR h hRc hf.hJ.1 hf.ht
  have hRcJ : tightCore J = J := TwinVtx.tightCore_eq_of_mem hRc hf.hJ.1
  obtain ⟨hcm, hc2, hc1⟩ := u_cmR h hRc hf hum hc
  obtain ⟨hcm', -, -⟩ := u_cmR h hRc hf' hum' hc
  have hcK' : c ∈ Balance.Bootstrap.trivialOnQuot J' := ⟨hcm'.2.1, fun x hx => hcm'.2.2.2 x hx⟩
  have hJ'tw : J' ∈ twinSet (CoreAssembly.conjClass (tightCore J)) (tightCore J) := by
    rw [hRcJ, TwinVtx.conjClass_eq_of_mem hf.hJ.1]
    exact hJ'
  have hne' : J' ≠ tightCore J := by rw [hRcJ]; exact hJne
  exact quiet_of_twin_R h4 hT hJd hRcJ hZ hc2 hc1 hcm htc hJ'tw hne' hcK'

theorem hyp51At_u_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) {c : G}
    (hc : c = u ∨ c = z * u ∨ c = u * t ∨ c = z * u * t) :
    Hyp51At (Subgroup.closure ({z, u, t} : Set G)) c := by
  have hΩ := h.hyp
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  have htB := TwinFrame.t_mem z u t
  obtain ⟨hcB, hc1, hzc, htc, hztc, hBeq⟩ := ucoset_facts hΩ hf hc
  have htC : t ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB htB
  obtain ⟨J', hJ', hJne⟩ := TwinFrame.exists_twin_of_trans hΩ
    (TwinFrame.trans_conjClass _) hf.mem hf.hK' hf.hne hf.hJ.1
  have hf' := frameData_twin_J hΩ hf hJ'
  have hAct := TwinUActsPf.twinFrameUActs_of_hyp hΩ
  have hq := quiet_u_R h4 hT h hRc hZ hf (hAct K K' J z u t hf) hf' hJ' hJne
    (hAct K K' J' z u t hf') hc htC
  exact hyp51At_of_quietR hB htB hcB hc1 hf.ht.ne_one htc htC hq

theorem hyp51_of_frameData_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t) :
    Hyp51 (Subgroup.closure ({z, u, t} : Set G)) := by
  have hΩ := h.hyp
  obtain ⟨hB, hB8⟩ := TwinFrame.shape_of_frameData hΩ hf
  refine ⟨hB, hB8, fun c hc hc1 => ?_⟩
  rcases TwinFrame.mem_closure_cases hΩ hf hc with e | e | e | e | e | e | e | e
  · exact absurd e hc1
  · subst e
    exact TwinFrame.hyp51At_z hΩ hsolv hf
  · exact hyp51At_nbr_R h4 hT h hRc hZ hf (Or.inl e)
  · exact hyp51At_nbr_R h4 hT h hRc hZ hf (Or.inr e)
  · exact hyp51At_u_R h4 hT h hRc hZ hf (Or.inl e)
  · exact hyp51At_u_R h4 hT h hRc hZ hf (Or.inr (Or.inl e))
  · exact hyp51At_u_R h4 hT h hRc hZ hf (Or.inr (Or.inr (Or.inl e)))
  · exact hyp51At_u_R h4 hT h hRc hZ hf (Or.inr (Or.inr (Or.inr e)))

theorem hyp51_of_mem_frameSet_R (h4 : Thm4RTwinBelow r n) (hT : Thm1RTwinInO2 r n)
    (h : TwinStdR r n G R S t₀) (hRc : tightCore R = R) (hZ : Subgroup.center G = ⊥)
    (hsolv : ∀ M ∈ CoreAssembly.conjClass (tightCore R), Group.IsSolvable ↥M) {B : Subgroup G}
    (hB : B ∈ TwinFrame.frameSet (CoreAssembly.conjClass (tightCore R))) : Hyp51 B := by
  obtain ⟨K, K', J, z, u, t, hf, rfl⟩ := hB
  exact hyp51_of_frameData_R h4 hT h hRc hZ hsolv hf

end Frame

end CFSG.CGT.PushingUpLit.SolKNA.R4
