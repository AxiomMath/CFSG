module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLAgreeTransport
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphNeighbour
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2EightLAgreeModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2GraphAlign

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open CFSG.SeitzReduction.LinearPilot (blockSpecialLinear mem_blockSpecialLinear)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]

theorem NsLinParam.conj_eq_q2Graph [CharP K 2] (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    {ε : ℕ} (hε : ε ≤ 1) {m : ℕ} (hm : 3 ≤ m) {e : L ≃* StatedSp (m + 1) K} {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2) {k : Fin (m + 1)} {κ : Sp2mKind}
    (hκ : κ = .linearEven ∨ κ = .linearOdd) (h : NsKindSp e t k κ) (P : NsLinParam hK ε e k)
    (x : q2Block ε K {k}) :
    t * P.Φ x * t⁻¹ = P.Φ (q2GraphBlock ε hK {k} x) := by
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set X : Subgroup G := modelToG e (nsTorusSp K k) with hXdef
  have hN : t ∈ normalizer (centralizerPerfectCore X : Set G) :=
    F4Pilot.normalizer_le_normalizer_centralizerPerfectCore _
      (UnitaryPilot.mem_normalizer_modelToG_of_mem_centralizer e htC _)
  obtain ⟨r, F, _, _, -, -, ε₀, -, hαo, -⟩ :=
    exists_mulEquiv_neighbourCore_linear_two hset hK hm e htC ht k rfl rfl hκ h hN
  set φQ : q2Block ε K {k} →* G := (MulAut.conj t).toMonoidHom.comp P.Φ with hφQ
  have hQinj : Function.Injective φQ := (MulAut.conj t).injective.comp P.injective
  have hr : P.Φ.range = φQ.range := by
    rw [hφQ, MonoidHom.range_comp, P.range_eq]
    ext g
    constructor
    · intro hg
      refine ⟨t⁻¹ * g * t, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
      have := (mem_normalizer_iff.1 (inv_mem hN) g).1 hg
      simpa [mul_assoc] using this
    · rintro ⟨y, hy, rfl⟩
      exact (mem_normalizer_iff.1 hN y).1 hy
  have hS : ∀ s ∈ q2SpBlock ε K hK ({k} : Finset (Fin (m + 1))), P.Φ s = φQ s := by
    intro s hs
    obtain ⟨y, hy, hys⟩ := (mem_q2SpBlock hK).1 hs
    have hs' : s = ⟨q2Embed ε hK y, (q2Embed_mem_q2Block_iff hK).2 hy⟩ := Subtype.ext hys.symm
    rw [hs']
    change P.Φ _ = t * P.Φ _ * t⁻¹
    rw [P.N1 y hy, ← mem_centralizer_iff.1 htC _ (e.symm y).2, mul_inv_cancel_right]
  obtain ⟨p, hp⟩ : ∃ p : Fin (m + 1), p ≠ k := ⟨if k = 0 then 1 else 0, by
    split_ifs with h0
    · rw [h0]
      exact Fin.ne_of_val_ne (by simp; omega)
    · exact Ne.symm h0⟩
  obtain ⟨p', hp'k, hp'p⟩ : ∃ p' : Fin (m + 1), p' ≠ k ∧ p' ≠ p := by
    obtain ⟨p', hp'⟩ := exists_ne_ne_of_three_le (by omega : 3 ≤ m + 1) k p
    exact ⟨p', hp'.1, hp'.2⟩
  have h3 : 3 ≤ ((planeCoordsQ2 ε ({k} : Finset (Fin (m + 1))))ᶜ).card := by
    rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_singleton, Fintype.card_fin]
    omega
  rcases eq_or_eq_q2Graph_of_range_eq hK hε (Ne.symm hp'p) (by simpa using hp)
      (by simpa using hp'k) h3 P.Φ φQ P.injective hQinj hr hS with h1 | h1
  ·
    exfalso
    apply hαo
    have hθ : (centralizerPerfectCore X).normalizerMonoidHom ⟨t, hN⟩ = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.one_apply]
      have hy : (y : G) ∈ P.Φ.range := by
        rw [P.range_eq]
        exact y.2
      obtain ⟨z, hz⟩ := hy
      rw [← hz]
      exact (h1 z).symm
    rw [hθ, map_one]
    exact ⟨1, map_one _⟩
  · have hγγ : q2GraphBlock ε hK {k} (q2GraphBlock ε hK {k} x) = x := Subtype.ext (by
      rw [coe_q2GraphBlock, coe_q2GraphBlock, ← MulAut.mul_apply, q2Graph_mul_self,
        MulAut.one_apply])
    have h2 := h1 (q2GraphBlock ε hK {k} x)
    rw [hγγ] at h2
    exact h2.symm

theorem q2Embed_mem_blockSpecialLinear_planeCoordsQ2 {N ε : ℕ} (hK : Nat.card K = 2)
    {R : Finset (Fin N)} {y : StatedSp N K} (hy : y ∈ spBlock K R) :
    q2Embed ε hK y ∈ blockSpecialLinear (planeCoordsQ2 ε R) := by
  rw [mem_blockSpecialLinear]
  intro a b hab
  obtain ⟨w, rfl⟩ := (q2Coord N ε).surjective a
  obtain ⟨w', rfl⟩ := (q2Coord N ε).surjective b
  rw [q2Embed_apply_q2Coord, Matrix.one_apply]
  simp only [(q2Coord N ε).injective.eq_iff]
  simp only [q2Coord_mem_planeCoordsQ2] at hab
  rcases w with u | i <;> rcases w' with v | j
  · rw [fromBlocks_apply₁₁, (mem_spBlock.1 hy) u v (by
      simp only [mem_planeCoords]
      rintro ⟨h1, h2⟩
      rcases hab with h | h
      · exact h h1
      · exact h h2), Matrix.one_apply]
    simp only [Sum.inl.injEq]
  · rw [fromBlocks_apply₁₂, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    simp
  · rw [fromBlocks_apply₂₂, Matrix.one_apply]
    simp

theorem commute_q2Embed_permSp_swap_q2Block (hK : Nat.card K = 2)
    {y : SpecialLinearGroup (Fin (2 * 4 + 0)) K} (hy : y ∈ q2Block 0 K ({0, 1} : Finset (Fin 4))) :
    Commute (q2Embed 0 hK (permSp K (Equiv.swap (0 : Fin 4) 1))) y :=
  LinearPilot.commute_blockSpecialLinear_of_disjoint disjoint_compl_right
    (q2Embed_mem_blockSpecialLinear_planeCoordsQ2 hK permSp_swap_mem_spBlock) hy

theorem conj_permSp_swap_overlap_eq [CharP K 2] (hset : SeitzSetting G L) (hK : Nat.card K = 2)
    {e : L ≃* StatedSp 4 K} {t : G} (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hkind : ∀ k : Fin 4, NsKindSp e t k .linearEven) (P₀ : NsLinParam hK 0 e 0)
    (x : SpecialLinearGroup (Fin (2 * 4 + 0)) K) (hx : x ∈ q2Block 0 K ({0, 1} : Finset (Fin 4))) :
    ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) *
        P₀.Φ ⟨x, q2Block_pair_le_left 0 1 hx⟩ *
      ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G)⁻¹ =
      P₀.Φ ⟨x, q2Block_pair_le_left 0 1 hx⟩ := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  set w : G := ((e.symm (permSp K (Equiv.swap (0 : Fin 4) 1)) : L) : G) with hw
  set Pw := q2Embed 0 hK (permSp K (Equiv.swap (0 : Fin 4) 1)) with hPw
  set P₁ := P₀.transport (Equiv.swap (0 : Fin 4) 1) 1 (by decide) with hP₁
  have hP₁x : ∀ (y : SpecialLinearGroup (Fin (2 * 4 + 0)) K)
      (hy : y ∈ q2Block 0 K ({0, 1} : Finset (Fin 4))),
      P₁.Φ ⟨y, q2Block_pair_le_right 0 1 hy⟩ = w * P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ * w⁻¹ := by
    intro y hy
    rw [hP₁, NsLinParam.transport_apply]
    have hc : q2BlockPermConj 0 hK (Equiv.swap (0 : Fin 4) 1) 0 1 (by decide)
        ⟨y, q2Block_pair_le_right 0 1 hy⟩ = ⟨y, q2Block_pair_le_left 0 1 hy⟩ := by
      apply Subtype.ext
      rw [coe_q2BlockPermConj, mul_assoc, ← (commute_q2Embed_permSp_swap_q2Block hK hy).eq,
        ← mul_assoc, inv_mul_cancel, one_mul]
    rw [hc]
  rcases NsLinParam.eq_or_eq_q2Graph_of_overlap zero_le_one le_rfl
      (show (0 : Fin 4) ≠ 1 by decide) P₀ P₁ with h1 | h1
  · rw [← hP₁x x hx, ← h1 x hx]
  exfalso
  have hγ : ∀ (y : SpecialLinearGroup (Fin (2 * 4 + 0)) K)
      (hy : y ∈ q2Block 0 K ({0, 1} : Finset (Fin 4))),
      w * P₀.Φ ⟨q2Graph 0 hK y, q2Block_pair_le_left 0 1 (q2Graph_mem_q2Block hK hy)⟩ * w⁻¹ =
        P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ := by
    intro y hy
    rw [← hP₁x _ (q2Graph_mem_q2Block hK hy), ← h1 y hy]
  have hP₀ := NsLinParam.conj_eq_q2Graph (m := 3) hset hK zero_le_one le_rfl htC ht
    (Or.inl rfl) (hkind 0) P₀
  set P₂ := P₀.transport (Equiv.swap (0 : Fin 4) 2) 2 (by decide) with hP₂def
  have hP₂ := NsLinParam.conj_eq_q2Graph (m := 3) hset hK zero_le_one le_rfl htC ht
    (Or.inl rfl) (hkind 2) P₂
  have hwt : ∀ (y : SpecialLinearGroup (Fin (2 * 4 + 0)) K)
      (hy : y ∈ q2Block 0 K ({0, 1} : Finset (Fin 4))),
      (w * t) * P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ * (w * t)⁻¹ =
        P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ := by
    intro y hy
    have h2 := hP₀ ⟨y, q2Block_pair_le_left 0 1 hy⟩
    have h3 : q2GraphBlock 0 hK {0} ⟨y, q2Block_pair_le_left 0 1 hy⟩ =
        ⟨q2Graph 0 hK y, q2Block_pair_le_left 0 1 (q2Graph_mem_q2Block hK hy)⟩ := rfl
    rw [h3] at h2
    calc (w * t) * P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ * (w * t)⁻¹ =
        w * (t * P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ * t⁻¹) * w⁻¹ := by group
      _ = P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ := by rw [h2, hγ y hy]
  have hτ₂ : q2SwapE hK ∈ q2Block 0 K ({2} : Finset (Fin 4)) :=
    q2Block_anti (by simp) (q2SwapE_mem_q2Block hK)
  set a : G := P₂.Φ ⟨q2SwapE hK, hτ₂⟩ with ha
  have hPw₂ : Pw ∈ q2Block 0 K ({2} : Finset (Fin 4)) :=
    (q2Embed_mem_q2Block_iff hK).2 (spBlock_mono (by decide) permSp_swap_mem_spBlock)
  have hP₂Pw : P₂.Φ ⟨Pw, hPw₂⟩ = w :=
    P₂.N1 _ (spBlock_mono (by decide) permSp_swap_mem_spBlock)
  have hPwinv : Pw⁻¹ = Pw := by
    rw [hPw, ← map_inv, ← permSp_inv, Equiv.swap_inv]
  have hta : a⁻¹ * t * a = w * t := by
    have h2 := hP₂ ⟨q2SwapE hK, hτ₂⟩
    have h3 : (⟨q2SwapE hK, hτ₂⟩ : q2Block 0 K ({2} : Finset (Fin 4)))⁻¹ *
        q2GraphBlock 0 hK {2} ⟨q2SwapE hK, hτ₂⟩ = ⟨Pw, hPw₂⟩ := by
      apply Subtype.ext
      change (q2SwapE hK)⁻¹ * q2Graph 0 hK (q2SwapE hK) = Pw
      rw [show (q2SwapE hK)⁻¹ * q2Graph 0 hK (q2SwapE hK) =
          ((q2Graph 0 hK (q2SwapE hK))⁻¹ * q2SwapE hK)⁻¹ by group, q2Graph_inv_mul_q2SwapE,
        ← hPw, hPwinv]
    calc a⁻¹ * t * a = a⁻¹ * (t * a * t⁻¹) * t := by group
      _ = P₂.Φ ((⟨q2SwapE hK, hτ₂⟩ : q2Block 0 K ({2} : Finset (Fin 4)))⁻¹ *
            q2GraphBlock 0 hK {2} ⟨q2SwapE hK, hτ₂⟩) * t := by
          rw [ha, h2, map_mul, map_inv]
      _ = w * t := by rw [h3, hP₂Pw]
  set ψ : q2Block 0 K ({0, 1} : Finset (Fin 4)) →* G := (MulAut.conj a).toMonoidHom.comp
    (P₀.Φ.comp (Subgroup.inclusion (q2Block_pair_le_left 0 1))) with hψ
  have hψapp : ∀ (y : SpecialLinearGroup (Fin (2 * 4 + 0)) K)
      (hy : y ∈ q2Block 0 K ({0, 1} : Finset (Fin 4))),
      ψ ⟨y, hy⟩ = a * P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩ * a⁻¹ := fun y hy => rfl
  have hperf : ⁅ψ.range, ψ.range⁆ = ψ.range := by
    have hB : Group.IsPerfect (q2Block 0 K ({0, 1} : Finset (Fin 4))) := by
      refine Subgroup.isPerfect_iff.mpr (commutator_q2Block_eq ?_)
      rw [Finset.card_compl, card_planeCoordsQ2, Finset.card_pair (by decide), Fintype.card_fin]
      norm_num
    have : Group.IsPerfect ψ.range :=
      Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) ψ.rangeRestrict_surjective
    exact Subgroup.isPerfect_iff.mp this
  have hψt : ψ.range ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨⟨y, hy⟩, rfl⟩
    rw [mem_centralizer_singleton_iff, hψapp]
    have h1 := hwt y hy
    rw [← hta] at h1
    set Φy := P₀.Φ ⟨y, q2Block_pair_le_left 0 1 hy⟩
    have h2 : Φy * (a⁻¹ * t * a) = (a⁻¹ * t * a) * Φy := by
      calc Φy * (a⁻¹ * t * a) = ((a⁻¹ * t * a) * Φy * (a⁻¹ * t * a)⁻¹) * (a⁻¹ * t * a) := by
            rw [h1]
        _ = (a⁻¹ * t * a) * Φy := by group
    calc a * Φy * a⁻¹ * t = a * (Φy * (a⁻¹ * t * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * t * a) * Φy) * a⁻¹ := by rw [h2]
      _ = t * (a * Φy * a⁻¹) := by group
  have hOut : Group.IsSolvable (Outer L) :=
    isSolvable_outer_of_isCyclic (isCyclic_outer_of_mulEquiv_statedSp (by norm_num) e)
  have hψL : ψ.range ≤ L := std_perfect_le hset.standardSetting hOut htC ht hperf hψt
  set u₂ : G := ((e.symm (nsElt (K := K) (2 : Fin 4)) : L) : G) with hu₂
  set u₃ : G := ((e.symm (nsElt (K := K) (3 : Fin 4)) : L) : G) with hu₃
  have ha₂ : Commute a u₂ := by
    have haE : a ∈ centralizerPerfectCore (modelToG e (nsTorusSp K 2)) := by
      rw [← P₂.range_eq]
      exact ⟨_, rfl⟩
    exact (mem_centralizer_iff.1 (F4Pilot.centralizerPerfectCore_le_centralizer _ haE) u₂
      (UnitaryPilot.symm_mem_modelToG e (nsElt_mem_nsTorusSp 2))).symm
  have h3mem : nsElt (K := K) (3 : Fin 4) ∈ spBlock K ({2} : Finset (Fin 4))ᶜ := by
    simpa using nsElt_mem_spBlock_compl (K := K) (show (2 : Fin 4) ≠ 3 by decide)
  have ha₃ : Commute a u₃ := by
    have h1 := P₂.N1 _ h3mem
    change a * u₃ = u₃ * a
    rw [hu₃, ← h1, ha, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_q2SwapE_q2Embed_nsElt_three hK).eq
  have hs : q2SigmaE (K := K) ∈ q2Block 0 K ({0, 1} : Finset (Fin 4)) := q2SigmaE_mem_q2Block
  have h2mem : nsElt (K := K) (2 : Fin 4) ∈ spBlock K ({0} : Finset (Fin 4))ᶜ := by
    simpa using nsElt_mem_spBlock_compl (K := K) (show (0 : Fin 4) ≠ 2 by decide)
  have h3mem' : nsElt (K := K) (3 : Fin 4) ∈ spBlock K ({0} : Finset (Fin 4))ᶜ := by
    simpa using nsElt_mem_spBlock_compl (K := K) (show (0 : Fin 4) ≠ 3 by decide)
  have hu0 : nsElt (K := K) (2 : Fin 4) * nsElt 3 ∈ spBlock K ({0} : Finset (Fin 4))ᶜ :=
    mul_mem h2mem h3mem'
  have hΦu : P₀.Φ ⟨q2Embed 0 hK (nsElt 2 * nsElt 3), (q2Embed_mem_q2Block_iff hK).2 hu0⟩ =
      u₂ * u₃ := by
    rw [P₀.N1 _ hu0, map_mul, L.coe_mul]
  have hsu : Commute (P₀.Φ ⟨q2SigmaE, q2Block_pair_le_left 0 1 hs⟩) (u₂ * u₃) := by
    change _ * _ = _ * _
    rw [← hΦu, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (commute_q2SigmaE_q2Embed hK).eq
  have hau : Commute a (u₂ * u₃) := ha₂.mul_right ha₃
  have hgL : ψ ⟨q2SigmaE, hs⟩ ∈ L := hψL ⟨_, rfl⟩
  set g : StatedSp 4 K := e ⟨ψ ⟨q2SigmaE, hs⟩, hgL⟩ with hg
  have hGu : Commute (ψ ⟨q2SigmaE, hs⟩) (u₂ * u₃) := by
    rw [hψapp]
    exact (hau.mul_left hsu).mul_left hau.inv_left
  have hgu : g * (nsElt 2 * nsElt 3) = (nsElt 2 * nsElt 3) * g := by
    have h1 : (⟨ψ ⟨q2SigmaE, hs⟩, hgL⟩ : L) * e.symm (nsElt 2 * nsElt 3) =
        e.symm (nsElt 2 * nsElt 3) * ⟨ψ ⟨q2SigmaE, hs⟩, hgL⟩ := by
      apply Subtype.ext
      rw [L.coe_mul, L.coe_mul, map_mul, L.coe_mul]
      exact hGu.eq
    have h2 := congrArg e h1
    rwa [map_mul e, map_mul e, MulEquiv.apply_symm_apply] at h2
  have hFL := commute_nsElt_sq_of_commute_nsElt_mul hK (show (2 : Fin 4) ≠ 3 by decide) hgu
  have hs2 : q2SigmaE (K := K) ^ 2 ∈ q2Block 0 K ({0, 1} : Finset (Fin 4)) := pow_mem hs 2
  have hψ2 : ψ ⟨q2SigmaE ^ 2, hs2⟩ = ψ ⟨q2SigmaE, hs⟩ ^ 2 := by
    rw [← map_pow]
    rfl
  have hcomm : Commute (ψ ⟨q2SigmaE ^ 2, hs2⟩) u₂ := by
    have h1 := congrArg e.symm hFL
    rw [hg, ← map_pow e, map_mul e.symm, map_mul e.symm, MulEquiv.symm_apply_apply] at h1
    have h2 := congrArg Subtype.val h1
    rw [L.coe_mul, L.coe_mul, L.coe_pow] at h2
    rw [hψ2]
    exact h2
  have hΦs2 : Commute (P₀.Φ ⟨q2SigmaE ^ 2, q2Block_pair_le_left 0 1 hs2⟩) u₂ := by
    rw [hψapp] at hcomm
    have h2 : a⁻¹ * (a * P₀.Φ ⟨q2SigmaE ^ 2, q2Block_pair_le_left 0 1 hs2⟩ * a⁻¹) * a =
        P₀.Φ ⟨q2SigmaE ^ 2, q2Block_pair_le_left 0 1 hs2⟩ := by group
    have h4 := (ha₂.inv_left.mul_left hcomm).mul_left ha₂
    rwa [h2] at h4
  have hΦ2 : P₀.Φ ⟨q2Embed 0 hK (nsElt 2), (q2Embed_mem_q2Block_iff hK).2 h2mem⟩ = u₂ :=
    P₀.N1 _ h2mem
  have h5 : P₀.Φ (⟨q2SigmaE ^ 2, q2Block_pair_le_left 0 1 hs2⟩ *
      ⟨q2Embed 0 hK (nsElt 2), (q2Embed_mem_q2Block_iff hK).2 h2mem⟩) =
      P₀.Φ (⟨q2Embed 0 hK (nsElt 2), (q2Embed_mem_q2Block_iff hK).2 h2mem⟩ *
        ⟨q2SigmaE ^ 2, q2Block_pair_le_left 0 1 hs2⟩) := by
    rw [map_mul, map_mul, hΦ2]
    exact hΦs2.eq
  exact not_commute_q2SigmaE_sq hK (congrArg Subtype.val (P₀.injective h5))

end CFSG.SeitzReduction.SymplecticPilot
