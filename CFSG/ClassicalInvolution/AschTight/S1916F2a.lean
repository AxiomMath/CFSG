module

public import CFSG.ClassicalInvolution.AschTight.S1916WrC
public import CFSG.ClassicalInvolution.AschTight.S1916CSR
public import CFSG.ClassicalInvolution.AschTight.S1911Case2a
public import CFSG.ClassicalInvolution.AschTight.Hall196QD
public import CFSG.ClassicalInvolution.AschTight.S1916WrAut2

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem isSylow2In_inf_sec19X (hd : Sec19Data p f K z S W) :
    IsSylow2In ((S : Subgroup G) ⊓ sec19X K z) (sec19X K z) :=
  isSylow2In_inf S hd.hSz (sec19X_le_centralizer K z) fun _ hc =>
    mem_normalizer_iff_conjSub_eq.mpr (conjSub_sec19X K hc)

theorem eq_W_of_le_centralizer [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {u : G} (huW : u ∈ W) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hPX : P ≤ sec19X K z) (hPu : P ≤ Subgroup.centralizer ({u} : Set G)) (hWP : W ≤ P) :
    P = W := by
  have hd := hDT.toSec19Data
  have hI := isUniqueInvolution_of_tight hd.tight.toTightBranch
  obtain ⟨A, hA, hPA⟩ := IsSylow2In.exists_ge hP2 hPX
  have hwr := (S1911.isSL2Three_sec19X_of_case2 hDT h1).wreathed A hA
  obtain ⟨a, c, b, B, hB⟩ := isWreathed_wrData hwr
  have hcardA : Nat.card A = 2 * Nat.card W := by
    rw [hA.natCard_eq (isSylow2In_inf_sec19X hd), S1911.inf_sec19X_eq_of_case2 hDT h1,
      S1911.card_inf_sup hDT]
  have hBW : W = B := by
    refine hB.eq_of_comm (hWP.trans hPA) (S1911.comm_of_mem hd) ?_
    have h2 := hB.card_P
    rw [hcardA, ← hB.card_B] at h2
    omega
  have hzB : z ∈ B := hBW ▸ Hall196.mem_W_of_sec19DataT hDT
  have hbz : b * z = z * b :=
    Subgroup.mem_centralizer_singleton_iff.mp (sec19X_le_centralizer K z (hA.1 hB.bP))
  have hzc : z ∈ Subgroup.zpowers (a * c) := hB.fix hzB (by rw [hbz]; group)
  have huB : u ∈ B := hBW ▸ huW
  have huc : u ∉ Subgroup.zpowers (a * c) := fun hu' =>
    huz (eq_of_mul_self_eq_one_of_isCyclic (Subgroup.isCyclic_zpowers _) hu' hzc hu2 hI.sq hu1
      hI.ne_one)
  refine le_antisymm (fun x hx => ?_) hWP
  rw [hBW]
  exact hB.mem_of_comm huB huc (hPA hx) (Subgroup.mem_centralizer_singleton_iff.mp (hPu hx))

theorem isSylow2In_W_centralizer [IsSimpleGroup G] (hDT : Sec19DataT p f K z S W L t V)
    (h1 : W ⊔ sec19Y K z = oddCoreOf (sec19Y K z) ⊔ W) {u : G} (huW : u ∈ W) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) (huz : u ≠ z) :
    IsSylow2In W (sec19X K z ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have hd := hDT.toSec19Data
  refine ⟨le_inf (S1911.le_sec19X hd) fun w hw => Subgroup.mem_centralizer_singleton_iff.mpr
      (S1911.comm_of_mem hd w hw u huW), S.isPGroup'.to_le hd.hWS, fun P hP hP2 hWP => ?_⟩
  exact eq_W_of_le_centralizer hDT h1 huW hu2 hu1 huz hP2 (hP.trans inf_le_left)
    (hP.trans inf_le_right) hWP

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
