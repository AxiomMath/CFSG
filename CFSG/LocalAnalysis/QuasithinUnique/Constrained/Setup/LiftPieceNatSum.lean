module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceNatTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftPieceCommon

public section

namespace CFSG.QuasithinUnique.Setup.Lift

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.QuasithinUnique.Setup.Lift.Piece
open scoped commutatorElement

section Tools

variable {G : Type} [Group G]

theorem le_normalizer_map_conj_of_mem {K A : Subgroup G} {g : G}
    (hK : K ≤ normalizer (A : Set G)) (hg : g ∈ normalizer (K : Set G)) :
    K ≤ normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) := by
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := (Subgroup.mem_normalizer_iff''.mp hg k).mp hk
  have hk'' : g⁻¹ * k⁻¹ * g ∈ K := (Subgroup.mem_normalizer_iff''.mp hg k⁻¹).mp (K.inv_mem hk)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(g⁻¹ * k * g) * a * (g⁻¹ * k * g)⁻¹, (Subgroup.mem_normalizer_iff.mp (hK hk') a).mp ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨a, ha, hax⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hax
    have hx : x = k⁻¹ * (g * a * g⁻¹) * k := by
      rw [hax]
      group
    have hmem : (g⁻¹ * k⁻¹ * g) * a * (g⁻¹ * k⁻¹ * g)⁻¹ ∈ A :=
      (Subgroup.mem_normalizer_iff.mp (hK hk'') a).mp ha
    refine ⟨_, hmem, ?_⟩
    rw [hx]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

def natCommutatorSub (G₀ Q W : Subgroup G) (hW : G₀ ≤ normalizer (W : Set G)) : Subgroup G where
  carrier := {k | k ∈ G₀ ∧ ∀ q ∈ Q, ⁅q, k⁆ ∈ W}
  one_mem' := ⟨one_mem _, fun q _ => by
    rw [commutatorElement_one_right]
    exact one_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha, hag⟩ ⟨hb, hbg⟩
    refine ⟨mul_mem ha hb, fun q hq => ?_⟩
    have e : ⁅q, a * b⁆ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (hag q hq) ((Subgroup.mem_normalizer_iff.mp (hW ha) _).mp (hbg q hq))
  inv_mem' := by
    rintro a ⟨ha, hag⟩
    refine ⟨inv_mem ha, fun q hq => ?_⟩
    have e : ⁅q, a⁻¹⁆ = a⁻¹ * (⁅q, a⁆)⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.mp (hW (inv_mem ha)) _).mp (inv_mem (hag q hq))
    simpa using this

theorem modComm_mono {V : Subgroup G} {A A' : Subgroup (MulAut V)} (h : A ≤ A') :
    modComm V A ≤ modComm V A' :=
  Subgroup.closure_mono fun _ ⟨a, ha, v, hv⟩ => ⟨a, h ha, v, hv⟩

theorem modComm_iSup {ι : Sort*} (V : Subgroup G) (A : ι → Subgroup (MulAut V)) :
    modComm V (⨆ i, A i) = ⨆ i, modComm V (A i) := by
  refine le_antisymm ?_ (iSup_le fun i => modComm_mono (le_iSup A i))
  set W : Subgroup G := ⨆ i, modComm V (A i) with hW
  let T : Subgroup (MulAut V) :=
    { carrier := {a | ∀ v : V, ((a v : V) : G) * ((v : V) : G)⁻¹ ∈ W}
      one_mem' := fun v => by
        simp only [MulAut.one_apply, mul_inv_cancel]
        exact one_mem _
      mul_mem' := by
        intro a b ha hb v
        have e : ((((a * b) v : V) : G)) * ((v : V) : G)⁻¹ =
            (((a (b v) : V) : G) * ((b v : V) : G)⁻¹) * (((b v : V) : G) * ((v : V) : G)⁻¹) := by
          rw [MulAut.mul_apply]
          group
        rw [e]
        exact mul_mem (ha (b v)) (hb v)
      inv_mem' := by
        intro a ha v
        have e : ((((a⁻¹) v : V) : G)) * ((v : V) : G)⁻¹ =
            ((((a ((a⁻¹) v) : V) : G)) * ((((a⁻¹) v : V) : G))⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]
          group
        rw [e]
        exact inv_mem (ha ((a⁻¹) v)) }
  have hle : (⨆ i, A i) ≤ T := iSup_le fun i a haA v =>
    Subgroup.mem_iSup_of_mem i (Subgroup.subset_closure ⟨a, haA, v, rfl⟩)
  refine (Subgroup.closure_le W).mpr ?_
  rintro _ ⟨a, ha, v, rfl⟩
  exact hle ha v

end Tools

section Main

theorem natSumProp
    : NatSumProp := by
  intro G _ _ R M V n F _ r Lc ctx i P hloc hres had hq hgen
  classical
  have hS := ctx.setting
  have hbridge := even_SL2_original_bridge hS ctx.comps
  have hbase := hloc.base
  have hSP : baum R ≤ P := hloc.basic.lt.le
  have hPLS := hres.le_LS
  have hLn := natL_normal (G := G)
  have hQn := natQ_normal hS
  have hLSn := normal_L_sup_baum hS
  have hVn : V.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hS.reduced.2.1)
  have hnormV : ∀ A : Subgroup G, A ≤ Subgroup.normalizer (V : Set G) := fun A x _ =>
    ctx.hX (Subgroup.mem_top x)
  set L : Subgroup G := oddOrderSubgroup (⊤ : Subgroup G) with hL
  set B : Subgroup G := oddOrderSubgroup P with hB
  set Q : Subgroup G := pCoreOf 2 (L ⊔ baum R) with hQ
  have hQt : ∀ t : G, t ∈ Subgroup.normalizer (Q : Set G) := fun t => by
    have := hQn
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top t
  have hQc : ∀ t : G, Q.map (MulAut.conj t).toMonoidHom = Q := fun t =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hQt t)
  have hQB : ⁅Q, B⁆ = modComm V (Lc i) := hq.comm
  have hOB : ⁅pCoreOf 2 B, B⁆ = modComm V (Lc i) := had.coreComm
  have hBP : B ≤ P := oddOrderSubgroup_le P
  have hI : modComm V (Lc i) = ⁅B, V⁆ := by
    rw [← hloc.K.image]
    exact modComm_autOn (hBP.trans (le_top.trans ctx.hX))
  have hLV : ⁅V, L⁆ = ⁅L, V⁆ := Subgroup.commutator_comm _ _
  have hIW : modComm V (Lc i) ≤ ⁅V, L⁆ := by
    rw [hI, hLV]
    exact Subgroup.commutator_mono (oddOrderSubgroup_mono le_top) le_rfl
  have hWn : (⁅V, L⁆ : Subgroup G).Normal := inferInstance
  refine ⟨fun t ht => ?_, fun t ht => ?_, ?_⟩
  ·
    exact le_normalizer_map_conj_of_mem hq.normalizes (hQt t)
  · refine ⟨?_, ?_⟩
    · rw [← hQB, Subgroup.map_commutator, hQc]
    · rw [pCoreOf_map_equiv 2 (MulAut.conj t) B, ← Subgroup.map_commutator, hOB]
  ·
    have hWsub : ⁅Q, L⁆ ≤ ⁅V, L⁆ := by
      have hWG : (L ⊔ baum R) ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun g _ => by
        have := hWn
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top g
      have hBt : ∀ t ∈ R, B.map (MulAut.conj t).toMonoidHom ≤
          natCommutatorSub (L ⊔ baum R) Q ⁅V, L⁆ hWG := by
        intro t ht x hx
        refine ⟨?_, fun q hq' => ?_⟩
        · obtain ⟨b, hb, rfl⟩ := hx
          have hbLS : b ∈ L ⊔ baum R := hPLS (hBP hb)
          have := (Subgroup.mem_normalizer_iff.mp
            (by have := hLSn; rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top t) b).mp hbLS
          simpa using this
        · have h1 : ⁅q, x⁆ ∈ ⁅Q, B.map (MulAut.conj t).toMonoidHom⁆ :=
            Subgroup.commutator_mem_commutator hq' hx
          have h2 : ⁅Q, B.map (MulAut.conj t).toMonoidHom⁆ = (modComm V (Lc i)).map
              (MulAut.conj t).toMonoidHom := by
            rw [← hQB, Subgroup.map_commutator, hQc]
          rw [h2] at h1
          obtain ⟨y, hy, hyx⟩ := h1
          rw [← hyx]
          have := (Subgroup.mem_normalizer_iff.mp
            (by have := hWn; rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top t) y).mp
            (hIW hy)
          simpa using this
      have hLle : L ≤ natCommutatorSub (L ⊔ baum R) Q ⁅V, L⁆ hWG :=
        (show L ≤ conjJoin R B from hgen.gen.le).trans (iSup_le fun s => hBt s s.2)
      exact Subgroup.commutator_le.mpr fun q hq' l hl => (hLle hl).2 q hq'
    have hQL : ⁅Q, L⁆ = ⁅V, L⁆ :=
      le_antisymm hWsub (Subgroup.commutator_mono hbase.V_le_Q le_rfl)
    have hVL : ⁅V, L⁆ = ⨆ j, modComm V (Lc j) := by
      calc ⁅V, L⁆ = ⁅L, V⁆ := hLV
        _ = modComm V (autOn L V) := (modComm_autOn (hnormV L)).symm
        _ = modComm V (⨆ j, Lc j) := by rw [hbridge.K_eq, hbridge.K_prod]
        _ = ⨆ j, modComm V (Lc j) := modComm_iSup V Lc
    refine ⟨hQL, hVL, ?_⟩
    rw [← hVL, ← hQL]
    exact hgen.central

end Main

end CFSG.QuasithinUnique.Setup.Lift
