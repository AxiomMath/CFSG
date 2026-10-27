
module

public import CFSG.Certificates.Kernel.HexaKSound
import CFSG.Certificates.Kernel.HeFixKSnd.Clos
import CFSG.Certificates.Kernel.HeFixKSnd.Small
import CFSG.Certificates.Kernel.HeFixKSnd.Outer
public import Certificates.Data.Kernel.HeFixK

public section

namespace CFSG.KC.HeFixK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.HexaK CFSG.KC.HeAutK
open CFSG.KLie.CT (fget)
open CFSG.PSL3Four.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SuzOddCore
open CFSG.ComponentClassification.GrSLit.HeldFix

@[expose] noncomputable def decS (nb w SA SB i : Nat) : List ℕ × List ℕ :=
  ((List.range 32).map (pg 6 (mask 6) (fget SA i 192)),
    (List.range nb).map (pg w (mask w) (fget SB i (nb * w))))

@[expose] noncomputable def setS (nb w N SA SB : Nat) : Finset (List ℕ × List ℕ) :=
  ((List.range N).map (decS nb w SA SB)).toFinset

theorem card_setS (nb w N SA SB : Nat) : (setS nb w N SA SB).card ≤ N := by
  unfold setS
  refine (List.toFinset_card_le _).trans ?_
  rw [List.length_map, List.length_range]

theorem decS_mem {nb w N SA SB i : Nat} (hi : i < N) : decS nb w SA SB i ∈ setS nb w N SA SB := by
  unfold setS
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨i, List.mem_range.2 hi, rfl⟩

theorem closK_sound {n w nb N SA SB SM q t j : Nat} (h : closK n w nb N SA SB SM q t j = true) :
    ∀ p ∈ setS nb w N SA SB,
      (p.1.map ((unpack 32 6 q)[·]!), p.2.map ((unpack n w t)[·]!)) ∈ setS nb w N SA SB := by
  intro p hp
  unfold setS at hp ⊢
  rw [List.mem_toFinset, List.mem_map] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨m, hm, h1, h2⟩ := CFSG.KC.HeFixKSnd.closK_spec h i (List.mem_range.1 hi)
  rw [List.mem_toFinset, List.mem_map]
  exact ⟨m, List.mem_range.2 hm, Prod.ext h1 h2⟩

@[expose] def sylow32G (gT gA gE : Array Tab) : Prop :=
  enumOK 32 gT (enumBFS 32 gT 1024) = true ∧ (enumBFS 32 gT 1024).tabs.size = 1024 ∧
    enumOK 32 gA (enumBFS 32 gA 2048) = true ∧ (enumBFS 32 gA 2048).tabs.size = 2048 ∧
    ((enumBFS 32 gT 1024).tabs.toList.filter (commAll 32 gT)).length = 2 ∧
    enumOK 32 gE (enumBFS 32 gE 64) = true ∧ (enumBFS 32 gE 64).tabs.size = 64 ∧
    (∀ i < 6, ∀ j < 6, comp 32 gE[i]! gE[j]! = comp 32 gE[j]! gE[i]!) ∧
    (∀ i < 6, comp 32 gE[i]! gE[i]! = idTab 32) ∧
    normalOK 32 (enumBFS 32 gE 64).tabs gT (gT.map (invTab 32)) gE = true ∧
    hfOuterE8Check 32 (enumBFS 32 gT 1024).tabs (enumBFS 32 gA 2048).tabs = true

theorem hfSylow32_iff :
    (enumOK 32 hfTTabs32 hfTEnum32 = true ∧ hfTEnum32.tabs.size = 1024 ∧
      enumOK 32 hfT0Tabs32 hfT0Enum32 = true ∧ hfT0Enum32.tabs.size = 2048 ∧
      (hfTEnum32.tabs.toList.filter (commAll 32 hfTTabs32)).length = 2 ∧
      enumOK 32 hfETabs32 hfEEnum32 = true ∧ hfEEnum32.tabs.size = 64 ∧
      (∀ i < 6, ∀ j < 6, comp 32 hfETabs32[i]! hfETabs32[j]! =
        comp 32 hfETabs32[j]! hfETabs32[i]!) ∧
      (∀ i < 6, comp 32 hfETabs32[i]! hfETabs32[i]! = idTab 32) ∧
      normalOK 32 hfEEnum32.tabs hfTTabs32 (hfTTabs32.map (invTab 32)) hfETabs32 = true ∧
      hfOuterE8Check 32 hfTEnum32.tabs hfT0Enum32.tabs = true) ↔
      sylow32G hfTTabs32 hfT0Tabs32 hfETabs32 :=
  Iff.rfl

theorem sylow32K_sound {gT gA gE : Array Tab} {cT cA cE NT NA NE IT WT : Nat}
    {GT GA GE TT TA TE ET EA EE ST SA SE : Nat → Nat}
    (pT : Pin 32 6 gT.toList cT GT NT TT ET ST) (pA : Pin 32 6 gA.toList cA GA NA TA EA SA)
    (pE : Pin 32 6 gE.toList cE GE NE TE EE SE) (hsz : NT = 1024 ∧ NA = 2048 ∧ NE = 64)
    (hE : cE = 6) (hc : cenK NT TT cT GT = 2) (he : eK cE GE = true)
    (hn : normK cT GT NE TE cE GE = true) (hi : itK NT TT IT = true)
    (ho : 0 < outerK NA TA NT TT IT WT) : sylow32G gT gA gE := by
  obtain ⟨hNT, hNA, hNE⟩ := hsz
  have PT := CFSG.KC.HeFixKSnd.pin_pts_PP pT
  have PA := CFSG.KC.HeFixKSnd.pin_pts_PP pA
  have GT' := CFSG.KC.HeFixKSnd.pin_gen_PP pT
  have GE' := CFSG.KC.HeFixKSnd.pin_gen_PP pE
  have PE := CFSG.KC.HeFixKSnd.pin_pts_PP pE
  obtain ⟨eT1, eT2⟩ := CFSG.KC.HeFixKSnd.pin_enum pT (cap := 1024) (by omega)
  obtain ⟨eA1, eA2⟩ := CFSG.KC.HeFixKSnd.pin_enum pA (cap := 2048) (by omega)
  obtain ⟨eE1, eE2⟩ := CFSG.KC.HeFixKSnd.pin_enum pE (cap := 64) (by omega)
  obtain ⟨ek1, ek2⟩ := CFSG.KC.HeFixKSnd.eK_tabs (CFSG.KC.HeFixKSnd.pin_size pE)
    (CFSG.KC.HeFixKSnd.pin_bind pE) GE' he
  subst hE
  refine ⟨eT1, ?_, eA1, ?_, ?_, eE1, ?_, ek1, ek2, ?_, ?_⟩
  · rw [eT2, Array.size_ofFn]
    exact hNT
  · rw [eA2, Array.size_ofFn]
    exact hNA
  · rw [eT2]
    exact CFSG.KC.HeFixKSnd.cen_count (CFSG.KC.HeFixKSnd.pin_size pT)
      (CFSG.KC.HeFixKSnd.pin_bind pT) GT' PT hc
  · rw [eE2, Array.size_ofFn]
    exact hNE
  · rw [eE2]
    exact CFSG.KC.HeFixKSnd.norm_tabs (CFSG.KC.HeFixKSnd.pin_size pT)
      (CFSG.KC.HeFixKSnd.pin_bind pT) GT' (CFSG.KC.HeFixKSnd.pin_size pE)
      (CFSG.KC.HeFixKSnd.pin_bind pE) GE' PE hn
  · rw [eT2, eA2]
    exact CFSG.KC.HeFixKSnd.outer_tabs PT PA hi ho

end CFSG.KC.HeFixK

end
