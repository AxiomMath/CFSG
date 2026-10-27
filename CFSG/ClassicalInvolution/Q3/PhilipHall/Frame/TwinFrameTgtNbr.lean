module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtSylow
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecFrame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdgeSecEdge
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameSec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.Q3CH
open scoped commutatorElement

section Plumbing

variable {G : Type} [Group G] [Finite G]

theorem oddQuotMk_mem_of_lifted (hBelow : CIT3Below (Nat.card G)) (hZ : Subgroup.center G = ⊥)
    {B : Subgroup G} (hB : IsElemAbelian 2 B) {c z : G} (hcB : c ∈ B) (hc1 : c ≠ 1)
    (hzB : z ∈ B) (hz1 : z ≠ 1) (hzc : z ≠ c)
    (hzC : z ∈ Subgroup.centralizer ({c} : Set G)) {K₁ K₂ : Subgroup G}
    (h₁ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) K₁ z)
    (h₂ : Q3NL.IsSectionMember3 (Subgroup.centralizer ({c} : Set G)) K₂ z) {x y : G}
    (hx : x ∈ K₁) (hy : y ∈ K₂) (hxC : x ∈ Subgroup.centralizer ({c} : Set G))
    (hyC : y ∈ Subgroup.centralizer ({c} : Set G))
    (huC : x * y ∈ Subgroup.centralizer ({c} : Set G))
    {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L) (hmov : MovedByAll B c L) :
    oddQuotMk c ⟨x * y, huC⟩ ∈ L := by
  have hsnc : ¬ ({c} : Set G) ⊆ Subgroup.center G := fun h => hc1 (by
    have h1 : c ∈ Subgroup.center G := h (Set.mem_singleton c)
    rwa [hZ, Subgroup.mem_bot] at h1)
  have hΦ := secData3_sFamily3 h₁ h₂ h₁
  obtain ⟨ι, -, ⟨D⟩⟩ := lieSystemMod3_of_secData3 hΦ hBelow hsnc
  obtain ⟨j₁, hj₁⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_one c K₁ K₂ K₁)
  obtain ⟨j₂, hj₂⟩ := exists_modOdd_le_secComp hΦ D (mem_sFamily3_two c K₁ K₂ K₁)
  have hzmov : ∃ w ∈ L, oddQuotMk c ⟨z, hzC⟩ * w ≠ w * oddQuotMk c ⟨z, hzC⟩ :=
    hmov _ (oddQuotMk_mem_modOdd hzB hzC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hzB hz1 hzc hzC)
  have hz₁ : oddQuotMk c ⟨z, hzC⟩ ∈ secComp hΦ D j₁ := hj₁ (oddQuotMk_mem_modOdd h₁.mem hzC)
  have hz₂ : oddQuotMk c ⟨z, hzC⟩ ∈ secComp hΦ D j₂ := hj₂ (oddQuotMk_mem_modOdd h₂.mem hzC)
  have hL₁ : L = secComp hΦ D j₁ := eq_secComp_of_not_commute hΦ D hz₁ hL hzmov
  have hL₂ : L = secComp hΦ D j₂ := eq_secComp_of_not_commute hΦ D hz₂ hL hzmov
  have hxL : oddQuotMk c ⟨x, hxC⟩ ∈ L := by
    rw [hL₁]; exact hj₁ (oddQuotMk_mem_modOdd hx hxC)
  have hyL : oddQuotMk c ⟨y, hyC⟩ ∈ L := by
    rw [hL₂]; exact hj₂ (oddQuotMk_mem_modOdd hy hyC)
  have e : oddQuotMk c ⟨x * y, huC⟩ = oddQuotMk c ⟨x, hxC⟩ * oddQuotMk c ⟨y, hyC⟩ := by
    rw [← map_mul]
    rfl
  rw [e]
  exact L.mul_mem hxL hyL

end Plumbing

section Vertex

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t₀ : G} {n : ℕ}

theorem mem_coreAt {R : Subgroup G} {c r : G} (hrR : r ∈ R)
    (hrC : r ∈ Subgroup.centralizer ({c} : Set G)) (hr2 : IsPGroup 2 (Subgroup.zpowers r)) :
    r ∈ coreAt R c := by
  have h1 : (⟨r, hrC⟩ : Subgroup.centralizer ({c} : Set G)) ∈
      tightCore (R.subgroupOf (Subgroup.centralizer ({c} : Set G))) :=
    Subgroup.subset_closure ⟨Subgroup.mem_subgroupOf.mpr hrR,
      isPGroup_zpowers_coe_iff.mp hr2⟩
  exact ⟨_, h1, rfl⟩

theorem edge_mem_centralizerModOdd (h : TwinCoreHyp n G R S t₀) (hRc : tightCore R = R)
    {M J : Subgroup G} {z t : G} (hM : M ∈ CoreAssembly.conjClass (tightCore R))
    (hz : IsUniqueInvolution M z)
    (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) M) (ht : IsUniqueInvolution J t)
    (htz : t ≠ z) : t ∈ centralizerModOdd ⊤ M := by
  obtain ⟨SK, hK⟩ := exists_datum_at h hRc hM hz
  have hRcK : tightCore M = M := tightCore_eq_of_mem hRc hM
  have hJe : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore M)) (tightCore M) := by
    rw [hRcK, conjClass_eq_of_mem hM]
    exact hJ
  exact (edge_involution hK.datum hRcK hK.hyp hJe ht htz).2.2

variable {K K' J : Subgroup G} {z u t : G}

theorem ubar_mem_of_lifted (h : TwinCoreHyp n G R S t₀) (hZ : Subgroup.center G = ⊥)
    (hf : TwinFrameData (CoreAssembly.conjClass (tightCore R)) K K' z u J t)
    (htK : t ∈ centralizerModOdd ⊤ K) (htK' : t ∈ centralizerModOdd ⊤ K') {c : G}
    (hc : c = t ∨ c = z * t) (hzc : z ∈ Subgroup.centralizer ({c} : Set G))
    (hlK : LiftedAt K c z) (hlK' : LiftedAt K' c z)
    {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L)
    (hmov : MovedByAll (Subgroup.closure ({z, u, t} : Set G)) c L)
    (huc : u ∈ Subgroup.centralizer ({c} : Set G)) :
    oddQuotMk c ⟨u, huc⟩ ∈ L := by
  have hΩ := h.hyp
  have hBelow : CIT3Below (Nat.card G) := h.card ▸ h.below
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hf.hz hf.hK'
  have hB := TwinFrame.isElemAbelian_of_frameData hΩ hf
  have hzB := TwinFrame.z_mem z u t
  have htB := TwinFrame.t_mem z u t
  have hcB : c ∈ Subgroup.closure ({z, u, t} : Set G) := by
    rcases hc with rfl | rfl
    · exact htB
    · exact Subgroup.mul_mem _ hzB htB
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
  obtain ⟨R₁, R₂, hR₁, hR₂, -, hR₁t, hR₂t, x, hx, y, hy, -, -, hxy⟩ :=
    exists_sylow_frame_gen hΩ hf htK htK'
  have hzt : z * t = t * z := A7Q.Gen.comm_zt hΩ hf
  have hcomm_c : ∀ {L₀ R₀ : Subgroup G}, R₀ ≤ L₀ → L₀ ≤ Subgroup.centralizer ({z} : Set G) →
      (∀ r ∈ R₀, r * t = t * r) → ∀ r ∈ R₀, r * c = c * r := by
    intro L₀ R₀ hRL hLz hRt r hr
    have hrz : r * z = z * r := Subgroup.mem_centralizer_singleton_iff.mp (hLz (hRL hr))
    rcases hc with hc | hc
    · rw [hc]
      exact hRt r hr
    · rw [hc]
      calc r * (z * t) = (r * z) * t := by group
        _ = (z * r) * t := by rw [hrz]
        _ = z * (r * t) := by group
        _ = z * (t * r) := by rw [hRt r hr]
        _ = (z * t) * r := by group
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_unique hf.hz
  have hK'z : K' ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_unique hzK'
  have hxc : x * c = c * x := hcomm_c hR₁.1 hKz hR₁t x hx
  have hyc : y * c = c * y := hcomm_c hR₂.1 hK'z hR₂t y hy
  have hxC : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxc
  have hyC : y ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyc
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := hR₁.2.1.to_le (Subgroup.zpowers_le.mpr hx)
  have hy2 : IsPGroup 2 (Subgroup.zpowers y) := hR₂.2.1.to_le (Subgroup.zpowers_le.mpr hy)
  obtain ⟨K₁, h₁, hcore₁⟩ := hlK
  obtain ⟨K₂, h₂, hcore₂⟩ := hlK'
  have hxK₁ : x ∈ K₁ := hcore₁ (mem_coreAt (hR₁.1 hx) hxC hx2)
  have hyK₂ : y ∈ K₂ := hcore₂ (mem_coreAt (hR₂.1 hy) hyC hy2)
  subst hxy
  exact oddQuotMk_mem_of_lifted hBelow hZ hB hcB hc1 hzB hf.hz.ne_one hac hzc h₁ h₂ hxK₁ hyK₂
    hxC hyC huc hL hmov

theorem moved_false_of_quiet {B : Subgroup G} (hB : IsElemAbelian 2 B) {a c : G} (haB : a ∈ B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) (ha1 : a ≠ 1) (hac : a ≠ c)
    (haC : a ∈ Subgroup.centralizer ({c} : Set G)) (hq : Quiet c a haC)
    {L : Subgroup (OddQuot c)} (hL : CFSG.IsComponent L) (hm : MovedByAll B c L) : False := by
  obtain ⟨w, hw, hne⟩ := hm _ (oddQuotMk_mem_modOdd haB haC)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 haB ha1 hac haC)
  exact hne (hq L hL w hw)

end Vertex

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
