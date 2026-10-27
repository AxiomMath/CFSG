module

public import CFSG.ClassicalInvolution.Q3.TL3T12_6E64Ker
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPf2Thin
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfClosureE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfMembers

public section

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Graph CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

variable {G : Type} [Group G] [Finite G]

theorem noCentralInv_of_e64 {P : Set (Subgroup G)} (I : AEIdentOn P 7 AE.e64Sets AE.e64Sub)
    (hc8 : ∀ L ∈ P, Nat.card L = 8) : NoCentralInv P := by
  intro L hL u hu hc
  obtain ⟨α, hα, h4, b, hlab⟩ := I.label L hL
  set uS : ↥(pSpan P) := ⟨u, le_pSpan hL hu.mem⟩ with huS
  have hZ : Subgroup.center ↥I.φ.range = ⊥ := by
    rw [I.range_eq]
    exact TwinThinPf.center_e64_eq_bot
  have hcS : ∀ y : ↥(pSpan P), y * uS = uS * y := fun y => Subtype.ext (hc y y.2)
  have hmem : (⟨I.φ uS, uS, rfl⟩ : ↥I.φ.range) ∈ Subgroup.center ↥I.φ.range := by
    rw [Subgroup.mem_center_iff]
    rintro ⟨_, y, rfl⟩
    apply Subtype.ext
    show I.φ y * I.φ uS = I.φ uS * I.φ y
    rw [← map_mul, ← map_mul, hcS y]
  rw [hZ, Subgroup.mem_bot] at hmem
  have h1 : I.φ uS = I.φ ⟨1, le_pSpan hL L.one_mem⟩ := by
    have := congrArg Subtype.val hmem
    have e : (⟨1, le_pSpan hL L.one_mem⟩ : ↥(pSpan P)) = 1 := rfl
    rw [e, map_one]
    exact this
  exact hu.ne_one (phi_injOn I.φ (by norm_num) hL (hc8 L hL) hlab hu.mem L.one_mem h1)

theorem cLeafE64G_proved (IH : ℕ → Prop) :
    CLeafE64G 3 IH := by
  intro G _ _ Ω K J hS ⟨I⟩
  have hK : K ∈ Ω := hS.adj.1
  have hJ : J ∈ Ω := hS.adj.2.1
  have hJπ : J ∈ orbOf (TC.nbrAdj Ω) K J := mem_orbOf_self K J
  have hKπ' : K ∈ orbOf (TC.nbrAdj Ω) J K := mem_orbOf_self J K
  have hP : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) K J) := hS.secHyp
  have hP' : SecHyp 3 Ω (orbOf (TC.nbrAdj Ω) J K) := hS.swap.secHyp
  have hc8 : ∀ L ∈ Ω, Nat.card L = 8 := fun L hL => by rw [hS.card L hL]; norm_num
  have hH1 : NoCentralInv (orbOf (TC.nbrAdj Ω) K J) :=
    noCentralInv_of_e64 I fun L hL => hc8 L (hP.sub hL)
  obtain ⟨⟨z, hz⟩, -⟩ := hS.hyp.omega1 K hK
  obtain ⟨g, hg⟩ := hS.trans K hK J hJ
  have hStepA : ∀ y ∈ pSpan (orbOf (TC.nbrAdj Ω) J K), y * z = z * y →
      (∃ a : ℕ, y ^ 3 ^ a = 1) → ∀ x ∈ pSpan (orbOf (TC.nbrAdj Ω) K J), y * x = x * y :=
    fun y hy hyz hy3 => hS.centralizes_of_three hH1 hz (fun y hyN hy3 hyJ =>
      TwinThinPf.centralizes_of_e64_proved I hyN hy3 hJπ hyJ
        (fun L' hL' => hP.trans J hJπ L' hL')) hy hyz hy3
  let I' : AEIdentOn (orbOf (TC.nbrAdj Ω) J K) 7 AE.e64Sets AE.e64Sub :=
    AEIdentOn.ofEq (hS.orb_swap_eq hg) (I.conj g)
  have hk2 : IsPGroup 2 I'.φ.ker := I'.toLabel.isPGroup_ker hP'.odd
  have hc8' : ∀ L ∈ orbOf (TC.nbrAdj Ω) J K, Nat.card L = 8 := fun L hL => hc8 L (hP'.sub hL)
  have hinj' : ∀ L ∈ orbOf (TC.nbrAdj Ω) J K, ∀ L' ∈ orbOf (TC.nbrAdj Ω) J K,
      (L.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) J K))).map I'.φ =
        (L'.subgroupOf (pSpan (orbOf (TC.nbrAdj Ω) J K))).map I'.φ → L = L' := by
    intro L hL L' hL' he
    obtain ⟨α, -, h4, b, hlab⟩ := I'.label L hL
    exact TL4.eq_of_map_le_memBar hS.hyp hS.two (by norm_num) I'.φ hk2 (hP'.sub hL)
      (hP'.sub hL') (le_pSpan hL) (le_pSpan hL') hlab he.le
  have hker := AEIdentOn.ker_le_threeClosure_e64 I' hP'.odd hc8' hP'.inv hinj' hKπ' hz
  refine hS.false_of_cent hH1 fun L hL u hu x hx => ?_
  obtain ⟨t, htT, htk⟩ := TwinThinPf.exists_mem_threeClosure (by norm_num) I'
    TwinThinPf.oddClosure_e64 hP'.odd hc8' hKπ' hz hL hu
  have huT : (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K))) ∈
      Subgroup.closure (TwinThinPf.threeGens (orbOf (TC.nbrAdj Ω) J K)
        (⟨z, le_pSpan hKπ' hz.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K)))) := by
    have := Subgroup.mul_mem _ htT (hker _ htk)
    simpa using this
  have hle : Subgroup.closure (TwinThinPf.threeGens (orbOf (TC.nbrAdj Ω) J K)
      (⟨z, le_pSpan hKπ' hz.mem⟩ : ↥(pSpan (orbOf (TC.nbrAdj Ω) J K)))) ≤
      (Subgroup.centralizer ((pSpan (orbOf (TC.nbrAdj Ω) K J) : Subgroup G) : Set G)).comap
        (pSpan (orbOf (TC.nbrAdj Ω) J K)).subtype := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨hwz, a, hwa⟩ x hx
    have hwz' : (w : G) * z = z * (w : G) := congrArg Subtype.val hwz
    have hw3 : ∃ a : ℕ, (w : G) ^ 3 ^ a = 1 :=
      ⟨a, by simpa using congrArg Subtype.val hwa⟩
    exact (hStepA w w.2 hwz' hw3 x hx).symm
  exact Subgroup.mem_centralizer_iff.mp (hle huT) x hx

end CFSG.ClassicalInvolution.Q3.TC.Thin
