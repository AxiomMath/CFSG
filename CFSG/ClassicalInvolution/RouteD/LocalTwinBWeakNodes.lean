module

public import CFSG.ClassicalInvolution.RouteD.LocalTwinBLocal
public import CFSG.ClassicalInvolution.RouteD.TypeF4Nodes
public import CFSG.ClassicalInvolution.RouteD.TypeF4LiftWeak

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.CurtisTits CFSG.Timmesfeld CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub FundamentalSingleClass
  fundamentalSubgroups modelUniv InClass IsClassicalMember LocalOddCentral ExactMembers
  centralizingMembers le_centralizingLayer)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockPair
  SymplecticBlockStandardPair longBlock shortBlock)
open scoped MatrixGroups commutatorElement

variable {p f : ℕ} [Fact p.Prime]

section Pairs

variable {F : Type} [Field F] [Finite F] {X : Type} [Group X]

theorem symplecticBlockPair_perfect (h4 : 4 ≤ Nat.card F) {W U V : Subgroup X}
    (h : SymplecticBlockPair F W U V) : U ≤ ⁅U, U⁆ ∧ V ≤ ⁅V, V⁆ := by
  obtain ⟨θ, c, -, -, -, hU, hV⟩ := h
  refine ⟨?_, ?_⟩
  · have := range_perfect_of_sl2 h4 (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp (longBlock F 2 1)))
    rwa [MonoidHom.range_comp, MonoidHom.range_comp, hU] at this
  · have := range_perfect_of_sl2 h4 (θ.comp ((MulAut.conj c⁻¹).toMonoidHom.comp
      (shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1))))
    rwa [MonoidHom.range_comp, MonoidHom.range_comp, hV] at this

variable {Y : Type} [Group Y]

omit [Finite F] in
theorem symplecticBlockPair_map_central (h5 : 5 ≤ Nat.card F) {W U V : Subgroup X}
    (h : SymplecticBlockStandardPair F W U V) (φ : X →* Y) (hφ : φ.ker ≤ Subgroup.center X) :
    SymplecticBlockPair F (W.map φ) (U.map φ) (V.map φ) := by
  obtain ⟨θ, c, hrange, hker, hinjL, -, hU, hV⟩ := h
  have : Group.IsPerfect (StatedSp 2 F) :=
    CFSG.ClassicalInvolution.ModelFacts.OddCover.isPerfect_sp4 h5
  have hcen : ∀ s : StatedSp 2 F, φ (θ s) = 1 → s ∈ Subgroup.center (StatedSp 2 F) := by
    intro s hs
    have hc : θ s ∈ Subgroup.center X := hφ (MonoidHom.mem_ker.mpr hs)
    refine mem_center_of_comm_mem_center fun t => hker ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_def,
      ← Subgroup.mem_center_iff.mp hc (θ t)]
    group
  set C : StatedSp 2 F →* StatedSp 2 F := (MulAut.conj c⁻¹).toMonoidHom with hC
  refine ⟨φ.comp θ, c, ?_, fun s hs => hcen s hs, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hrange]
  · intro l₁ l₂ hl
    simp only [MonoidHom.comp_apply] at hl
    have h1 : φ (θ (C (longBlock F 2 1 (l₁⁻¹ * l₂)))) = 1 := by
      simp only [map_mul, map_inv]
      rw [hl, inv_mul_cancel]
    have h2 := hcen _ h1
    have h3 : longBlock F 2 1 (l₁⁻¹ * l₂) ∈ Subgroup.center (StatedSp 2 F) := by
      have h4 := (inferInstance : (Subgroup.center (StatedSp 2 F)).Normal).conj_mem _ h2 c
      have e : c * C (longBlock F 2 1 (l₁⁻¹ * l₂)) * c⁻¹ = longBlock F 2 1 (l₁⁻¹ * l₂) := by
        simp only [hC, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rwa [e] at h4
    have h5' := CFSG.ClassicalInvolution.Models.SymplecticPairs.eq_one_of_mem_center_of_mem_suppGroup
      h3 (CFSG.ClassicalInvolution.Models.SymplecticPairs.isSupp_longBlock (1 : Fin 2) _)
      (t := Sum.inl (0 : Fin 2)) (by
        simp only [CFSG.ClassicalInvolution.Models.SymplecticPairs.coords, Set.mem_insert_iff,
          Set.mem_singleton_iff, not_or]
        decide)
    have h6 : l₁⁻¹ * l₂ = 1 := by
      apply CFSG.ClassicalInvolution.Models.SymplecticPairs.longBlock_injective (1 : Fin 2)
      rw [h5', map_one]
    exact inv_mul_eq_one.mp h6
  · show ((longBlock F 2 1).range.map C).map (φ.comp θ) = U.map φ
    rw [← hU]
    simp only [Subgroup.map_map, MonoidHom.comp_assoc]
  · show ((shortBlock F (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map C).map (φ.comp θ) = V.map φ
    rw [← hV]
    simp only [Subgroup.map_map, MonoidHom.comp_assoc]

end Pairs

namespace TCtx

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem exists_nodes_odd_full {m : ℕ} (hm : 3 ≤ m) (c : TCtx p f .POmegaOdd m Ω K z) :
    ∃ j : Fin m → Subgroup G,
      (∀ a : Fin m, a.val + 1 < m → j a ∈ centralizingMembers Ω {z} ∧ j a ≠ K ∧
        ¬ locImg Ω z (j a) ≤ c.d.Q₁) ∧
      (∀ a, j a ≤ locLayer Ω z) ∧ (∀ a, ⁅j a, j a⁆ = j a) ∧ (∀ a, Commutes K (j a)) ∧
      (∀ a b : Fin m, a.val + 1 < b.val → Commutes (j a) (j b)) ∧
      (∀ a b : Fin m, a.val + 1 = b.val → b.val + 1 < m → ∃ W : Subgroup G,
        LinearBlockStandardPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a b : Fin m, a.val + 2 = m → b.val + 1 = m → ∃ W : Subgroup G,
        SymplecticBlockPair (GaloisField p f) W (j a) (j b)) ∧
      (∀ a : Fin m, locImg Ω z (j a) =
        (rankOne (modelUniv .POmegaOdd m p f Fact.out).D.rootGroup a).map c.d.ψ) := by
  have h2 : (2 : GaloisField p f) ≠ 0 := two_ne_zero_galoisField c.hp2
  have hF4 : 4 ≤ Nat.card (GaloisField p f) := c.h4
  have h5 : 5 ≤ Nat.card (GaloisField p f) := by rw [c.card_eq]; exact c.hq
  let R : Fin (m - 1) → Subgroup (modelUniv .POmegaOdd m p f Fact.out).K := fun a =>
    rankOne (oddDatum m (GaloisField p f)).rootGroup
      (⟨a.val, by have := a.isLt; show a.val < m; omega⟩ : Fin (oddDatum m (GaloisField p f)).rank)
  let Rs : Subgroup (modelUniv .POmegaOdd m p f Fact.out).K :=
    rankOne (oddDatum m (GaloisField p f)).rootGroup
      (⟨m - 1, by show m - 1 < m; omega⟩ : Fin (oddDatum m (GaloisField p f)).rank)
  have hR : ∀ a, R a ∈ fundamentalSubgroups .POmegaOdd (modelUniv .POmegaOdd m p f Fact.out).D :=
    fun a => rankOne_mem_fundamentalSubgroups_oddDatum hm
      (by show a.val + 1 < m; have := a.isLt; omega)
  have hRc : ∀ a b : Fin (m - 1), a ≠ b → ¬ (a.val + 1 = b.val) → ¬ (b.val + 1 = a.val) →
      Commutes (R a) (R b) := by
    intro a b hab h1 h2'
    refine commutes_rankOne_oddDatum hm h2 ?_
    refine cartanB_eq_zero_of_far ?_
    have : a.val ≠ b.val := fun e => hab (Fin.ext e)
    simp only
    omega
  have hRs : ∀ a b : Fin (m - 1), a.val + 1 = b.val → ∃ W,
      LinearBlockStandardPair (GaloisField p f) W (R a) (R b) := by
    intro a b hab
    have hbl := b.isLt
    exact standardPair_oddDatum_edge' (F := GaloisField p f) hm
      (i := (⟨a.val, by show a.val < m; omega⟩ : Fin m))
      (j := (⟨b.val, by show b.val < m; omega⟩ : Fin m)) hab (by show b.val + 1 < m; omega)
  obtain ⟨jl, hjl, hjlc, hjlp, hjlK⟩ := c.exists_nodes R hR (fun a b => a.val + 1 = b.val)
    hRc hRs
  obtain ⟨Wm, hWm⟩ := symplecticPair_oddDatum (F := GaloisField p f) hF4 h2 hm
  have hRsperf : Rs ≤ ⁅Rs, Rs⁆ :=
    (symplecticBlockPair_perfect hF4 hWm.pair).2
  have hSperf : Rs.map c.d.ψ ≤ ⁅Rs.map c.d.ψ, Rs.map c.d.ψ⁆ := by
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hRsperf
  obtain ⟨A, hAperf, hAmap⟩ := exists_perfect_lift c.hP1 hSperf
  set Yl : Subgroup G := locLayer Ω z with hYl
  let jS : Subgroup G := A.map Yl.subtype
  have hjSimg : locImg Ω z jS = Rs.map c.d.ψ := by
    show locImg Ω z (A.map Yl.subtype) = _
    rw [locImg_map_subtype, hAmap]
  have hjSY : jS ≤ Yl := Subgroup.map_subtype_le _
  have hjSperf : jS ≤ ⁅jS, jS⁆ := by
    show A.map Yl.subtype ≤ ⁅A.map Yl.subtype, A.map Yl.subtype⁆
    rw [← Subgroup.map_commutator]
    exact Subgroup.map_mono hAperf
  have hlY : ∀ a : Fin (m - 1), jl a ≤ Yl := fun a => le_centralizingLayer (hjl a).1
  have hlperf : ∀ a : Fin (m - 1), jl a ≤ ⁅jl a, jl a⁆ := fun a => by
    obtain ⟨z', hz'⟩ := c.hΩ.classical (jl a) (hjl a).1.1
    exact (commutator_eq_of_isClassicalMember hz').ge
  have hlimg : ∀ a, locImg Ω z (jl a) = (R a).map c.d.ψ := fun a => (hjl a).2.2.2
  have hjlc' : ∀ a b : Fin (m - 1), a.val + 1 < b.val → Commutes (jl a) (jl b) := fun a b hab =>
    hjlc a b (fun e => by have := congrArg Fin.val e; omega) (by omega) (by omega)
  have hKY : K ≤ Yl := le_centralizingLayer c.hKz
  have hKperf : K ≤ ⁅K, K⁆ := (commutator_eq_of_isClassicalMember c.hz).ge
  have hKS : Commutes K jS := commutes_of_commutes_locImg_perfect c.hP1 hKY hjSY hKperf (by
    intro a ha b hb
    rw [hjSimg] at hb
    exact c.d.comm₀ a (c.hQ₀ ha) b (by obtain ⟨x, _, rfl⟩ := hb; exact ⟨x, rfl⟩))
  have hlS : ∀ a : Fin (m - 1), a.val + 1 < m - 1 → Commutes (jl a) jS := by
    intro a ha
    refine commutes_of_commutes_locImg_perfect c.hP1 (hlY a) hjSY (hlperf a) ?_
    rw [hlimg a, hjSimg]
    refine commutes_map_hom c.d.ψ ?_
    exact commutes_rankOne_oddDatum hm h2 (cartanB_eq_zero_of_far (Or.inl (by simp only; omega)))
  have hsp : ∃ W : Subgroup G, SymplecticBlockPair (GaloisField p f) W
      (jl ⟨m - 2, by omega⟩) jS := by
    have hmap := symplecticBlockPair_map_central h5 hWm c.d.ψ c.d.ker_le
    refine symplecticBlockPair_of_locImg_perfect c.hp2 c.hq c.hP1 (hlY _) hjSY (hlperf _) hjSperf
      (W := Wm.map c.d.ψ) ?_
    rw [hlimg, hjSimg]
    exact hmap
  let j : Fin m → Subgroup G := fun a => if h : a.val + 1 < m then jl ⟨a.val, by omega⟩ else jS
  have hjlong : ∀ a : Fin m, ∀ (h : a.val + 1 < m), j a = jl ⟨a.val, by omega⟩ := fun a h => by
    simp only [j, h, dite_true]
  have hjshort : ∀ a : Fin m, a.val + 1 = m → j a = jS := fun a h => by
    have h' : ¬ (a.val + 1 < m) := by omega
    simp only [j, h', dite_false]
  refine ⟨j, fun a ha => ?_, fun a => ?_, fun a => ?_, fun a => ?_, ?_, ?_, ?_, fun a => ?_⟩
  · rw [hjlong a ha]
    exact ⟨(hjl _).1, (hjl _).2.1, (hjl _).2.2.1⟩
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]; exact hlY _
    · rw [hjshort a (by have := a.isLt; omega)]; exact hjSY
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]; exact le_antisymm (commutator_self_le _) (hlperf _)
    · rw [hjshort a (by have := a.isLt; omega)]; exact le_antisymm (commutator_self_le _) hjSperf
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]; exact hjlK _
    · rw [hjshort a (by have := a.isLt; omega)]; exact hKS
  · intro a b hab
    have hbl := b.isLt
    by_cases hb : b.val + 1 < m
    · rw [hjlong a (by omega), hjlong b hb]
      exact hjlc' _ _ hab
    · rw [hjlong a (by omega), hjshort b (by omega)]
      exact hlS _ (by simp only; omega)
  · intro a b hab hb
    rw [hjlong a (by omega), hjlong b hb]
    exact hjlp _ _ (by simp only; exact hab)
  · intro a b ha hb
    rw [hjlong a (by omega), hjshort b hb]
    have e : (⟨a.val, by omega⟩ : Fin (m - 1)) = ⟨m - 2, by omega⟩ := Fin.ext (by simp only; omega)
    rw [e]
    exact hsp
  · by_cases h : a.val + 1 < m
    · rw [hjlong a h]
      exact hlimg _
    · have h' : a.val + 1 = m := by have := a.isLt; omega
      rw [hjshort a h', hjSimg]
      have e : a = (⟨m - 1, by omega⟩ : Fin m) := Fin.ext (by simp only; omega)
      rw [e]
      rfl

end TCtx

end CFSG.ClassicalInvolution.RouteD
