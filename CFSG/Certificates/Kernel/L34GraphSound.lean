module

public import Certificates.Data.Kernel.L34Graph
public import CFSG.Certificates.Kernel.L34W.Tab42Sound
import CFSG.Certificates.Kernel.L34KeySound
import CFSG.Certificates.Kernel.L34FieldSound
import CFSG.Certificates.Kernel.L34ScanSound
import CFSG.Certificates.Kernel.Spor.RawOrbEval

public section

namespace CFSG.KC.L34Graph

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KS.Raw CFSG.KC.BfsPin CFSG.KC.L34K CFSG.KC.L34KSnd
open CFSG.KC.L34Scan CFSG.KC.L34W CFSG.KC.L34Field CFSG.KC.L34Key CFSG.PSL3Four.Native
open CFSG.ComponentClassification.GrSLit.L34Facts
open CFSG.KLie.CT (andB orB notB)

variable {G : Nat → Nat}

theorem forceL_eq : ∀ (l : List Nat) (k : List Nat → Bool), forceL l k = k l
  | [], _ => rfl
  | x :: l, k => by
    change strictB x (fun x' => forceL l fun l' => k (x' :: l')) = k (x :: l)
    rw [strictB_app, forceL_eq l]

theorem xTab_eq (hG : GensG G) (k m : Nat) :
    xTab k m = unpack 42 6 (pcomp 42 6 (mask 6) (tgK G k) (tgK G (4 * m))) := by
  unfold xTab
  rw [(tgK_eq hG k).2, (tgK_eq hG (4 * m)).2, comp_unpack' (tgK_eq hG k).1 (tgK_eq hG (4 * m)).1]

theorem xTabs_eq (hG : GensG G) (κ : Nat) : xTabs κ = (pxK G κ).map (unpack 42 6) := by
  unfold xTabs pxK
  rw [List.map_flatMap]
  refine congrArg (fun F => (List.range 16).flatMap F) (funext fun k => ?_)
  rw [List.map_map]
  exact congrArg (fun F => List.map F _) (funext fun m => xTab_eq hG k m)

theorem pxK_cn (hG : GensG G) (κ : Nat) : ∀ v ∈ pxK G κ, Cn v := by
  intro v hv
  unfold pxK at hv
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hv
  obtain ⟨m, -, rfl⟩ := List.mem_map.1 hk
  exact cp (tgK_eq hG k).1 (tgK_eq hG (4 * m)).1

theorem decompOK_of (hG : GensG G) (h : decK G = true) : decompOK = true := by
  unfold decK at h
  rw [forceL_eq, forceL_eq] at h
  unfold decompOK
  rw [CFSG.KS.BfsReplay.allBelow_iff]
  intro k hk
  have h' := CFSG.KS.Raw.Orb.allN_iff.1 h k hk
  rw [strictB_app] at h'
  simp only [List.any_map, Function.comp_apply] at h'
  obtain ⟨k₁, hk₁, h1⟩ := List.any_eq_true.1 h'
  obtain ⟨m, hm, h2⟩ := List.any_eq_true.1 h1
  unfold anyBelow
  refine List.any_eq_true.2 ⟨k₁, hk₁, List.any_eq_true.2 ⟨m, hm, ?_⟩⟩
  rw [xTab_eq hG, (tgK_eq hG k).2,
    beq_unpack (cp (tgK_eq hG k₁).1 (tgK_eq hG (4 * m)).1) (tgK_eq hG k).1]
  exact h2

theorem contains_map {L : List Nat} {y : Nat} (hL : ∀ v ∈ L, Cn v) (hy : Cn y) :
    (L.map (unpack 42 6)).contains (unpack 42 6 y) = L.any fun v => Nat.beq v y := by
  rw [Bool.eq_iff_iff, List.contains_iff_exists_mem_beq, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, e⟩
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ha
    refine ⟨v, hv, ?_⟩
    rw [beq_unpack hy (hL v hv)] at e
    rw [Nat.eq_of_beq_eq_true e]
    exact Nat.beq_refl v
  · rintro ⟨v, hv, e⟩
    refine ⟨unpack 42 6 v, List.mem_map_of_mem hv, ?_⟩
    rw [Nat.eq_of_beq_eq_true e]
    exact beq_self_eq_true _

theorem invertOK_of (hG : GensG G) {ρ : Nat} (hρ : Cn ρ)
    (h : invK (tgK G 4) (tgK G 8) [pxK G 0, pxK G 1, pxK G 2] ρ = true) :
    invertOK xAll (unpack 42 6 ρ) = true := by
  obtain ⟨c4, e4⟩ := tgK_eq hG 4
  obtain ⟨c8, e8⟩ := tgK_eq hG 8
  unfold invK at h
  unfold invertOK
  rw [e4, e8, comp_unpack' hρ c4, comp_unpack' c4 hρ, comp_unpack' hρ c8, comp_unpack' c8 hρ,
    beq_unpack (cp hρ c4) (cp c4 hρ), beq_unpack (cp hρ c8) (cp c8 hρ), ← commPt_eq hρ c4,
    ← commPt_eq hρ c8]
  rcases orB_iff.1 h with h1 | h1
  · have h1' := notB_iff.1 h1
    have e : (commPt 42 6 ρ (tgK G 4) && commPt 42 6 ρ (tgK G 8)) = false := by
      cases a : commPt 42 6 ρ (tgK G 4) <;> rw [a] at h1' <;> first | rfl | exact h1'
    rw [e]
    rfl
  · rw [Bool.or_eq_true]
    right
    rw [List.all_eq_true]
    intro L hL
    have hX : ∀ κ, κ < 3 → (pxK G κ).all (fun x => strictB (pcomp 42 6 (mask 6)
        (pcomp 42 6 (mask 6) ρ x) ρ) fun y => CFSG.KLie.CT.orB (CFSG.KLie.CT.notB ((pxK G κ).any fun v => Nat.beq v y))
          (Nat.beq (pcomp 42 6 (mask 6) y x) (pidn 42 6))) = true := by
      intro κ hκ
      have := List.all_eq_true.1 h1
      match κ, hκ with
      | 0, _ => exact this _ (by simp)
      | 1, _ => exact this _ (by simp)
      | 2, _ => exact this _ (by simp)
    have hL' : L = xTabs 0 ∨ L = xTabs 1 ∨ L = xTabs 2 := by
      unfold xAll at hL
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using hL
    obtain ⟨κ, hκ, hLκ⟩ : ∃ κ, κ < 3 ∧ L = xTabs κ := by
      rcases hL' with e | e | e
      · exact ⟨0, Nat.zero_lt_succ _, e⟩
      · exact ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ _), e⟩
      · exact ⟨2, Nat.lt_succ_self _, e⟩
    rw [hLκ]
    have hc := pxK_cn hG κ
    rw [xTabs_eq hG, List.all_map, List.all_eq_true]
    intro x hx
    have h2 := List.all_eq_true.1 (hX κ hκ) x hx
    rw [strictB_app] at h2
    have cx := hc x hx
    have cy := cp (cp hρ cx) hρ
    simp only [Function.comp_apply]
    unfold conjTab
    rw [comp_unpack' hρ cx, comp_unpack' (cp hρ cx) hρ, contains_map hc cy, comp_unpack' cy cx,
      idTab42, beq_unpack (cp cy cx) cn_pidn]
    rcases orB_iff.1 h2 with h3 | h3
    · rw [notB_iff] at h3
      rw [h3]
      rfl
    · rw [h3]
      simp
end CFSG.KC.L34Graph

end
