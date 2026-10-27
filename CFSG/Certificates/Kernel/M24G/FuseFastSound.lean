module

public import Certificates.Data.Kernel.M24G.FuseFast
public import CFSG.Certificates.Kernel.M24G.FusePackSound

public section

namespace CFSG.KC.M24G

theorem conjGoF_cons (q x s : Nat) (ss : List Nat) :
    conjGoF q x (s :: ss) = q >>> (x >>> s % 32 * 5) % 32 + 32 * conjGoF q x ss := rfl

theorem conjGoF_pkL (q x : Nat) : ∀ ss : List Nat,
    conjGoF q x ss = pkL (ss.map fun s => q >>> (x >>> s % 32 * 5) % 32)
  | [] => rfl
  | s :: ss => by rw [conjGoF_cons, conjGoF_pkL q x ss, List.map_cons, pkL]

theorem shiftRight_lane (x v : Nat) : x >>> ((23 - v) * 5) % 32 = laneP x v := by
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_comm, Nat.pow_mul, laneP]

theorem conjGoF_conjP {h h' q : Nat} {r : List Nat} (hr : ∀ v ∈ r, v < 32) (hlen : r.length = 24)
    (he : h' = pkL r) (hq : ∀ u < 32, q >>> (u * 5) % 32 = laneP h u) (x : Nat) :
    conjGoF q x (r.map fun v => (23 - v) * 5) = conjP (h, h') x := by
  have hm : ∀ y ∈ r.map (laneP x), y < 32 := by
    intro y hy
    obtain ⟨v, -, rfl⟩ := List.mem_map.1 hy
    exact Nat.mod_lt _ (by decide)
  have h1 := mulGoP_pkL x r hr
  have h2 := mulGoP_pkL h (r.map (laneP x)) hm
  rw [List.length_map, hlen] at h2
  rw [hlen] at h1
  rw [conjP, mulP, mulP, he, h1, h2, conjGoF_pkL, List.map_map, List.map_map]
  congr 1
  apply List.map_congr_left
  intro v _
  simp only [Function.comp_apply]
  rw [shiftRight_lane]
  exact hq _ (Nat.mod_lt _ (by decide))

def fuseRA : List Nat :=
  [10, 15, 17, 2, 8, 6, 21, 9, 22, 12, 5, 14, 7, 23, 16, 19, 11, 18, 13, 1, 0, 20, 4, 3]

def fuseRBi : List Nat :=
  [11, 7, 21, 15, 23, 3, 22, 16, 12, 9, 6, 20, 19, 10, 1, 8, 17, 2, 5, 4, 0, 13, 14, 18]

def fuseRB : List Nat :=
  [19, 17, 21, 12, 11, 0, 7, 16, 20, 1, 2, 15, 23, 10, 14, 8, 22, 13, 5, 4, 18, 6, 9, 3]

theorem fuseSA_eq : fuseSA = fuseRA.map fun v => (23 - v) * 5 := by decide +kernel

theorem fuseSBi_eq : fuseSBi = fuseRBi.map fun v => (23 - v) * 5 := by decide +kernel

theorem fuseSB_eq : fuseSB = fuseRB.map fun v => (23 - v) * 5 := by decide +kernel

theorem fuseRA_lt : ∀ v ∈ fuseRA, v < 32 := by decide +kernel

theorem fuseRBi_lt : ∀ v ∈ fuseRBi, v < 32 := by decide +kernel

theorem fuseRB_lt : ∀ v ∈ fuseRB, v < 32 := by decide +kernel

theorem fuseRA_pk : (130618774265195527788604973352306154 : Nat) = pkL fuseRA := by decide +kernel

theorem fuseRBi_pk : (766391294027834038598208565066323179 : Nat) = pkL fuseRBi := by
  decide +kernel

theorem fuseRB_pk : (136564164338441043102435244607166003 : Nat) = pkL fuseRB := by
  decide +kernel

theorem fuseQA_lane : ∀ u < 32, fuseQA >>> (u * 5) % 32 =
    laneP 130618774265195527788604973352306154 u := by decide +kernel

theorem fuseQB_lane : ∀ u < 32, fuseQB >>> (u * 5) % 32 =
    laneP 136564164338441043102435244607166003 u := by decide +kernel

theorem fuseQBi_lane : ∀ u < 32, fuseQBi >>> (u * 5) % 32 =
    laneP 766391294027834038598208565066323179 u := by decide +kernel

theorem fuseStepA_eq : (fun x => conjGoF fuseQA x fuseSA) =
    conjP (130618774265195527788604973352306154, 130618774265195527788604973352306154) := by
  funext x
  rw [fuseSA_eq]
  exact conjGoF_conjP fuseRA_lt rfl fuseRA_pk fuseQA_lane x

theorem fuseStepB_eq : (fun x => conjGoF fuseQB x fuseSBi) =
    conjP (136564164338441043102435244607166003, 766391294027834038598208565066323179) := by
  funext x
  rw [fuseSBi_eq]
  exact conjGoF_conjP fuseRBi_lt rfl fuseRBi_pk fuseQB_lane x

theorem fuseStepBi_eq : (fun x => conjGoF fuseQBi x fuseSB) =
    conjP (766391294027834038598208565066323179, 136564164338441043102435244607166003) := by
  funext x
  rw [fuseSB_eq]
  exact conjGoF_conjP fuseRB_lt rfl fuseRB_pk fuseQBi_lane x

theorem fuseStepsF_eq : fuseStepsF = fuseStepsP := by
  rw [fuseStepsF, fuseStepA_eq, fuseStepB_eq, fuseStepBi_eq, fuseStepsP, fusePairsP,
    List.map_cons, List.map_cons, List.map_cons, List.map_nil]

end CFSG.KC.M24G
