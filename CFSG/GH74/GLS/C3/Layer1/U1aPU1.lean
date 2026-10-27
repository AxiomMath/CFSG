module

public import CFSG.GH74.GLS.C3.Layer1.U1aSetup
public import CFSG.GH74.Uniqueness.Statements
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.C3.Layer1.U1a

open Subgroup CFSG.GH74.Uniqueness CFSG.ABGLocalTools

section Sets

variable {G : Type} [Group G]

@[expose] def pu1Z (W : Subgroup G) : Set G :=
  {z | orderOf z = 2 ∧ ∃ h : G, h⁻¹ * z * h ∈ W}

theorem mem_pu1Z {W : Subgroup G} {z : G} :
    z ∈ pu1Z W ↔ orderOf z = 2 ∧ ∃ h : G, h⁻¹ * z * h ∈ W := Iff.rfl

theorem pu1Z_invariant (W : Subgroup G) : IsInvariantInvolutionSet (pu1Z W) := by
  refine ⟨fun z hz => (mem_pu1Z.mp hz).1, fun z hz g => ?_⟩
  obtain ⟨hz2, h, hh⟩ := mem_pu1Z.mp hz
  refine mem_pu1Z.mpr ⟨by rw [orderOf_conj_eq]; exact hz2, g⁻¹ * h, ?_⟩
  have e : (g⁻¹ * h)⁻¹ * (g⁻¹ * z * g) * (g⁻¹ * h) = h⁻¹ * z * h := by group
  rwa [e]

end Sets

section Solvable

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_normalizer_sylow_two (P : Sylow 2 G) :
    Group.IsSolvable ↥(normalizer ((P : Subgroup G) : Set G)) := by
  set N := normalizer ((P : Subgroup G) : Set G) with hN
  have hPN : (P : Subgroup G) ≤ N := le_normalizer
  have hP : Group.IsSolvable ↥(P : Subgroup G) := by
    have := P.isPGroup'.isNilpotent
    infer_instance
  have hT : Group.IsSolvable ↥((P : Subgroup G).subgroupOf N) :=
    Group.isSolvable_of_isSolvable_injective (f := (subgroupOfEquivOfLe hPN).toMonoidHom)
      (subgroupOfEquivOfLe hPN).injective
  have hodd : Odd (Nat.card (↥N ⧸ (P : Subgroup G).subgroupOf N)) := by
    change Odd ((P : Subgroup G).relIndex N)
    refine Nat.not_even_iff_odd.1 fun he => P.not_dvd_index ?_
    exact dvd_trans (even_iff_two_dvd.1 he) (relIndex_dvd_index_of_le hPN)
  have hQ : Group.IsSolvable (↥N ⧸ (P : Subgroup G).subgroupOf N) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  exact Group.isSolvable_of_ker_le_range ((P : Subgroup G).subgroupOf N).subtype
    (QuotientGroup.mk' ((P : Subgroup G).subgroupOf N))
    (by rw [QuotientGroup.ker_mk', range_subtype])

end Solvable

section Main

variable {G : Type} [Group G] [Finite G] {M L N W Q T : Subgroup G}

theorem pu1_claimU_of_sylow [Finite G] {Q W M : Subgroup G}
    (hQ : IsSylowOf 2 Q W) (hWM : W ≤ M)
    (hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M)
    {x : G} (hx : x ∈ W) (hx2 : orderOf x = 2) {g : G} (hg : g⁻¹ * x * g ∈ M) : g ∈ M := by
  obtain ⟨c, hc, hxc⟩ := exists_conj_involution_mem hQ hx hx2
  have h1 : (c⁻¹ * g)⁻¹ * (c⁻¹ * x * c) * (c⁻¹ * g) ∈ M := by
    have e : (c⁻¹ * g)⁻¹ * (c⁻¹ * x * c) * (c⁻¹ * g) = g⁻¹ * x * g := by group
    rwa [e]
  have h2 : c⁻¹ * g ∈ M := hU _ hxc (by rw [orderOf_conj_eq]; exact hx2) _ h1
  have h3 : c * (c⁻¹ * g) ∈ M := M.mul_mem (hWM hc) h2
  simpa using h3

theorem pu1_mem_W_of_normal {W M : Subgroup G}
    (hWM : W ≤ M)
    (hWnorm : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (huniq : ∀ w ∈ W, orderOf w = 2 → ∀ g : G, g⁻¹ * w * g ∈ M → g ∈ M)
    {z : G} (hz : z ∈ pu1Z W) (hzM : z ∈ M) : z ∈ W := by
  obtain ⟨hz2, h, hh⟩ := mem_pu1Z.mp hz
  have ha2 : orderOf (h⁻¹ * z * h) = 2 := by rw [orderOf_conj_eq]; exact hz2
  have hhM : h⁻¹ ∈ M := by
    refine huniq (h⁻¹ * z * h) hh ha2 (g := h⁻¹) ?_
    have e : (h⁻¹)⁻¹ * (h⁻¹ * z * h) * h⁻¹ = z := by group
    rwa [e]
  have hhM' : h ∈ M := by simpa using M.inv_mem hhM
  have h1 := hWnorm h hhM' _ hh
  have e : h * (h⁻¹ * z * h) * h⁻¹ = z := by group
  rwa [e] at h1

theorem pu1_centralizer_le_of_mem_normal {W M : Subgroup G}
    (hWM : W ≤ M)
    (huniq : ∀ w ∈ W, orderOf w = 2 → ∀ g : G, g⁻¹ * w * g ∈ M → g ∈ M)
    {w : G} (hw : w ∈ W) (hw2 : orderOf w = 2) :
    centralizer ({w} : Set G) ≤ M := by
  intro c hc
  rw [mem_centralizer_singleton_iff] at hc
  refine huniq w hw hw2 c ?_
  have hc' : c⁻¹ * w * c = w := by
    calc c⁻¹ * w * c = c⁻¹ * (w * c) := by group
      _ = c⁻¹ * (c * w) := by rw [hc]
      _ = w := by group
  rw [hc']
  exact hWM hw

theorem pu1_centralizer_le_of_normal {W M : Subgroup G}
    (hWM : W ≤ M)
    (hWnorm : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (huniq : ∀ w ∈ W, orderOf w = 2 → ∀ g : G, g⁻¹ * w * g ∈ M → g ∈ M)
    {u : G} (hu : u ∈ productInvolutions (pu1Z W)) (huM : u ∈ M) :
    centralizer ({u} : Set G) ≤ M := by
  obtain ⟨hu2, x, hx, z, hz, hxz, rfl⟩ := hu
  obtain ⟨hx2, h, hh⟩ := mem_pu1Z.mp hx
  have ha2 : orderOf (h⁻¹ * x * h) = 2 := by rw [orderOf_conj_eq]; exact hx2
  have hxx : x * x = 1 := mul_self_eq_one_of_orderOf_eq_two hx2
  have hcent : h⁻¹ * (x * z) * h ∈ centralizer ({h⁻¹ * x * h} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have e1 : h⁻¹ * (x * z) * h * (h⁻¹ * x * h) = h⁻¹ * (x * (z * x)) * h := by group
    have e2 : h⁻¹ * x * h * (h⁻¹ * (x * z) * h) = h⁻¹ * (x * (x * z)) * h := by group
    rw [e1, e2, ← hxz]
  have hu'M : h⁻¹ * (x * z) * h ∈ M :=
    pu1_centralizer_le_of_mem_normal hWM huniq hh ha2 hcent
  have hz' : h⁻¹ * z * h = (h⁻¹ * x * h) * (h⁻¹ * (x * z) * h) := by
    calc h⁻¹ * z * h = h⁻¹ * ((x * x) * z) * h := by rw [hxx, one_mul]
      _ = (h⁻¹ * x * h) * (h⁻¹ * (x * z) * h) := by group
  have hz'M : h⁻¹ * z * h ∈ M := by
    rw [hz']
    exact M.mul_mem (hWM hh) hu'M
  have hz'W : h⁻¹ * z * h ∈ W :=
    pu1_mem_W_of_normal hWM hWnorm huniq ((pu1Z_invariant W).2 z hz h) hz'M
  have hu'W : h⁻¹ * (x * z) * h ∈ W := by
    rw [eq_inv_mul_of_mul_eq hz'.symm]
    exact W.mul_mem (W.inv_mem hh) hz'W
  have hu'2 : orderOf (h⁻¹ * (x * z) * h) = 2 := by rw [orderOf_conj_eq]; exact hu2
  have hhM : h⁻¹ ∈ M := by
    refine huniq (h⁻¹ * (x * z) * h) hu'W hu'2 (g := h⁻¹) ?_
    have e : (h⁻¹)⁻¹ * (h⁻¹ * (x * z) * h) * h⁻¹ = x * z := by group
    rwa [e]
  have hhM' : h ∈ M := by simpa using M.inv_mem hhM
  have huW : x * z ∈ W := by
    have h1 := hWnorm h hhM' _ hu'W
    have e : h * (h⁻¹ * (x * z) * h) * h⁻¹ = x * z := by group
    rwa [e] at h1
  exact pu1_centralizer_le_of_mem_normal hWM huniq huW hu2

theorem pu1_productDisconnected_of_normal {W M : Subgroup G}
    (hMproper : M ≠ ⊤)
    (hWM : W ≤ M)
    (hWnorm : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (hWinv : ∃ w ∈ W, orderOf w = 2)
    (huniq : ∀ w ∈ W, orderOf w = 2 → ∀ g : G, g⁻¹ * w * g ∈ M → g ∈ M) :
    IsProductDisconnected (pu1Z W) M := by
  refine ⟨hMproper, ?_, ?_, ?_⟩
  · obtain ⟨w, hwW, hw2⟩ := hWinv
    exact ⟨w, mem_pu1Z.mpr ⟨hw2, 1, by simpa using hwW⟩, hWM hwW⟩
  · intro z hz hzM g
    refine ⟨fun hg => ?_, fun hg => ?_⟩
    · exact huniq z (pu1_mem_W_of_normal hWM hWnorm huniq hz hzM) (mem_pu1Z.mp hz).1 g hg
    · exact M.mul_mem (M.mul_mem (M.inv_mem hg) hzM) hg
  · intro u hu huM
    exact pu1_centralizer_le_of_normal hWM hWnorm huniq hu huM

theorem pu1_false_of_normal_even_of_corZD [Finite G]
    (hCor : S_CorZD) (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a)
    {M W : Subgroup G}
    (hMproper : M ≠ ⊤)
    (hMns : ¬ Group.IsSolvable ↥M)
    (hWM : W ≤ M)
    (hWnorm : ∀ m ∈ M, ∀ w ∈ W, m * w * m⁻¹ ∈ W)
    (hWinv : ∃ w ∈ W, orderOf w = 2)
    (huniq : ∀ w ∈ W, orderOf w = 2 → ∀ g : G, g⁻¹ * w * g ∈ M → g ∈ M) :
    False := by
  obtain ⟨-, P, hP⟩ :=
    hCor G hG hnon (pu1Z W) M (pu1Z_invariant W)
      (pu1_productDisconnected_of_normal hMproper hWM hWnorm hWinv huniq)
  exact hMns (by rw [hP]; exact isSolvable_normalizer_sylow_two P)


theorem pu1_claimU (S : Setup M L N W Q T)
    (hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M)
    {x : G} (hx : x ∈ W) (hx2 : orderOf x = 2) {g : G} (hg : g⁻¹ * x * g ∈ M) : g ∈ M :=
  pu1_claimU_of_sylow S.sylowQ S.W_le hU hx hx2 hg

theorem pu1_mem_W (S : Setup M L N W Q T)
    (hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M)
    {z : G} (hz : z ∈ pu1Z W) (hzM : z ∈ M) : z ∈ W :=
  pu1_mem_W_of_normal S.W_le S.W_norm
    (fun w hw hw2 g hg => pu1_claimU S hU hw hw2 hg) hz hzM

theorem pu1_centralizer_le (S : Setup M L N W Q T)
    (hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M)
    {u : G} (hu : u ∈ productInvolutions (pu1Z W)) (huM : u ∈ M) :
    centralizer ({u} : Set G) ≤ M :=
  pu1_centralizer_le_of_normal S.W_le S.W_norm
    (fun w hw hw2 g hg => pu1_claimU S hU hw hw2 hg) hu huM

theorem pu1_productDisconnected (S : Setup M L N W Q T)
    (hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M) :
    IsProductDisconnected (pu1Z W) M := by
  refine pu1_productDisconnected_of_normal S.M_ne_top S.W_le S.W_norm ?_
    (fun w hw hw2 g hg => pu1_claimU S hU hw hw2 hg)
  obtain ⟨a, haQ, -, -, ha2, -, -, -⟩ := S.rankQ
  exact ⟨a, S.Q_le_W haQ, ha2⟩

theorem pu1_false (hCor : S_CorZD) (hG : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a)
    (S : Setup M L N W Q T)
    (hU : ∀ x ∈ Q, orderOf x = 2 → ∀ g : G, g⁻¹ * x * g ∈ M → g ∈ M) : False := by
  refine pu1_false_of_normal_even_of_corZD hCor hG hnon S.M_ne_top S.M_not_solvable S.W_le S.W_norm ?_
    (fun w hw hw2 g hg => pu1_claimU S hU hw hw2 hg)
  obtain ⟨a, haQ, -, -, ha2, -, -, -⟩ := S.rankQ
  exact ⟨a, S.Q_le_W haQ, ha2⟩

end Main

end CFSG.GH74.GLS.C3.Layer1.U1a
