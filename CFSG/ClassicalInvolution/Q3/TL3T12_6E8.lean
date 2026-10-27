module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6E8Sec
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfE8Aut

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {G : Type} [Group G]

theorem E8Struct.conj {X E : Subgroup G} (hE : E8Struct X E) (g : G) :
    E8Struct (conjSub g X) (conjSub g E) where
  le := conjSub_mono hE.le
  normal := by
    intro x hx e he
    rw [mem_conjSub_iff] at hx he ⊢
    have h := hE.normal _ hx _ he
    convert h using 1
    group
  card := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hE.card
  sq := by
    intro e he
    rw [mem_conjSub_iff] at he
    have h := hE.sq _ he
    calc e * e = g * ((g⁻¹ * e * g) * (g⁻¹ * e * g)) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  cent := by
    intro x hx hc
    rw [mem_conjSub_iff] at hx ⊢
    refine hE.cent _ hx fun e he => ?_
    have h := hc (g * e * g⁻¹) (conj_mem_conjSub he)
    calc g⁻¹ * x * g * e = g⁻¹ * (x * (g * e * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * e * g⁻¹) * x) * g := by rw [h]
      _ = e * (g⁻¹ * x * g) := by group
  core := by
    intro Q hQX hQn hQ2
    have hQ2' : IsPGroup 2 ↥(conjSub g⁻¹ Q) := hQ2.map (MulAut.conj g⁻¹).toMonoidHom
    have hle : conjSub g⁻¹ Q ≤ E := by
      refine hE.core _ ?_ ?_ hQ2'
      · intro x hx
        rw [mem_conjSub_iff] at hx
        have h := hQX hx
        rw [mem_conjSub_iff] at h
        have e : g⁻¹ * (g⁻¹⁻¹ * x * g⁻¹) * g = x := by group
        rwa [e] at h
      · intro y hy q hq
        rw [mem_conjSub_iff] at hq ⊢
        have hgy : g * y * g⁻¹ ∈ conjSub g X := conj_mem_conjSub hy
        have h := hQn _ hgy _ hq
        convert h using 1
        group
    intro q hq
    rw [mem_conjSub_iff]
    have := hle (conj_mem_conjSub (n := g⁻¹) hq)
    simpa using this
  index := by
    have h1 := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) E X
      (MulAut.conj g).injective
    exact h1.trans hE.index

theorem cLeafE8G_proved (IH : ℕ → Prop) : CLeafE8G 3 IH := by
  intro G _ _ Ω K J hS E hE
  have hK : K ∈ Ω := hS.adj.1
  have hJ : J ∈ Ω := hS.adj.2.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hKπ' : K ∈ orbOf (TC.nbrAdj Ω) J K := mem_orbOf_self J K
  have hP : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) K J) := hS.secHyp
  have hH1 : NoCentralInv (orbOf (TC.nbrAdj Ω) K J) := hP.e8_noCentralInv hE
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  obtain ⟨⟨zJ, hzJ⟩, -⟩ := hS.hyp.omega1 J hJ
  obtain ⟨g, hg⟩ := hS.trans K hK J hJ
  have hStepA : ∀ y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K), y * z = z * y →
      (∃ a : ℕ, y ^ 3 ^ a = 1) → ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y :=
    fun y hy hyz hy3 => hS.centralizes_of_three hH1 hz (fun y hyN hy3 hyJ =>
      TwinThinPf.e8_centralizes hE hzJ.mem (hP.e8_inv_mem hE hJπ hzJ)
        (fun k hk e he => hP.e8_conj_mem_or hE hJπ hzJ hk he)
        (fun e he hc => hP.e8_eq_of_comm hE hJπ hzJ he hc) hyN hy3 hyJ) hy hyz hy3
  have hP' : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) J K) := hS.swap.secHyp
  have hE' : E8Struct (pSpan (orbOf (TC.nbrAdj Ω) J K)) (conjSub g E) := by
    rw [hS.pSpan_swap_eq hg]
    exact hE.conj g
  have hT := hP'.e8_le_closure_threeElts hE' hKπ' hz
  have hTc : Subgroup.closure {w : G | w ∈ pSpan (orbOf (TC.nbrAdj Ω) J K) ∧ w * z = z * w ∧
      ∃ a : ℕ, w ^ 3 ^ a = 1} ≤
      Subgroup.centralizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨hwX', hwz, hw3⟩ x hx
    exact (hStepA w hwX' hwz hw3 x hx).symm
  exact hS.false_of_cent hH1 fun L hL u hu x hx =>
    Subgroup.mem_centralizer_iff.mp (hTc (hT (hP'.e8_inv_mem hE' hL hu))) x hx

end CFSG.ClassicalInvolution.Q3.TC.Thin
