module

public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WSix
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3M1Borel
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec2Step22ivQuot
import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
import CFSG.LocalAnalysis.SeitzReduction.RankOneStart
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WFive
public import CFSG.LocalAnalysis.EvenBN.U5.Sec3WThree
import CFSG.LocalAnalysis.SeitzReduction.RankOneBranches

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

local notation "actΓ" => CFSG.RankThree.PartOne.U5K.Hyp.act

theorem isQuasisimple_of_isSimpleGroup' {X : Type*} [Group X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) : CFSG.Open.IsQuasisimple X := by
  refine ⟨CFSG.ComponentClassification.Helpers.commutator_eq_top X hnab, ?_⟩
  exact ((QuotientGroup.congr (center X) ⊥ (MulEquiv.refl X) (by
    rw [CFSG.ComponentClassification.Helpers.center_eq_bot X hnab]
    exact map_bot _)).trans (QuotientGroup.quotientBot (G := X))).isSimpleGroup

section Model

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem patSub_I₁_le_N₁sub : patSub h sI₁ isPattern_sI₁ ≤ N₁sub h := fun u hu => by
  rw [eq_uSU_of_mem hu]
  exact uSU_mem_N₁sub _

theorem mul_self_of_mem_patSub_I₁ {u : hypSU h 2 1} (hu : u ∈ patSub h sI₁ isPattern_sI₁) :
    u * u = 1 := by
  have := h.charP
  rw [eq_uSU_of_mem hu, ← uSU_add, CharTwo.add_self_eq_zero, uSU_zero]

end Model

namespace Data

variable {G : Type} [Group G] [Finite G] {f : ℕ} {K : Type} [Field K]
  {h : UnitaryFieldData 2 f K} {d : Data G h}

omit [Finite G] in
theorem N₁_le_centralizer_I₁ (d : Data G h) : d.N₁ ≤ centralizer (d.I₁ : Set G) := by
  rintro _ ⟨n, hn, rfl⟩
  refine mem_centralizer_iff.2 ?_
  rintro _ ⟨i, hi, rfl⟩
  rw [← map_mul, ← map_mul, N₁sub_comm_I₁sub hn hi]

theorem Hyp.t_mem_centralizer_I₁ (hd : d.Hyp) : d.t ∈ centralizer (d.I₁ : Set G) :=
  mem_centralizer_iff.2 fun _ hs => hd.comm_t (d.pull_le_L _ hs)

theorem Hyp.t_mem_centralizer_N₁ (hd : d.Hyp) : d.t ∈ centralizer (d.N₁ : Set G) :=
  mem_centralizer_iff.2 fun _ hs => hd.comm_t (d.pull_le_L _ hs)

omit [Finite G] in
theorem act_I₁_of_mem_centralizer (d : Data G h) {c : G} (hcL : c ∈ normalizer (d.L : Set G))
    {y : Gam h} (hy : Phi h y = d.act ⟨c, hcL⟩) (hc : c ∈ centralizer (d.I₁ : Set G)) :
    ∀ i ∈ I₁sub h, ∃ s ∈ hypScalars h 2 1, actΓ h y i = s * i := by
  intro i hi
  have e : d.η (actΓ h y i) = d.η i := by
    rw [← d.conj_η_eq hcL hy, ← mem_centralizer_iff.1 hc _ ⟨i, hi, rfl⟩, mul_inv_cancel_right]
  refine ⟨actΓ h y i * i⁻¹, ?_, by group⟩
  rw [← d.η_eq_one_iff, map_mul, map_inv, e, mul_inv_cancel]

omit [Finite G] in
theorem act_eq_of_η_eq_of_sq (d : Data G h) {y : Gam h} {g : hypSU h 2 1} (hg : g * g = 1)
    (he : d.η (actΓ h y g) = d.η g) : actΓ h y g = g := by
  have hs : actΓ h y g * g⁻¹ ∈ hypScalars h 2 1 := by
    rw [← d.η_eq_one_iff, map_mul, map_inv, he, mul_inv_cancel]
  have hsq : actΓ h y g * actΓ h y g = 1 := by rw [← act_mul, hg, act_one]
  set s := actΓ h y g * g⁻¹ with hsdef
  have hag : actΓ h y g = s * g := by rw [hsdef, inv_mul_cancel_right]
  have hs2 : s * s = 1 := by
    have hc := scalar_central hs g
    have e : (s * g) * (s * g) = (s * s) * (g * g) := by
      calc (s * g) * (s * g) = s * (g * s) * g := by group
        _ = s * (s * g) * g := by rw [hc]
        _ = (s * s) * (g * g) := by group
    rw [← hag, hsq, hg, mul_one] at e
    exact e.symm
  have hs5 := pow_five_of_mem_hypScalars hs
  have hs1 : s = 1 := by
    have e : s = s ^ 5 * ((s * s)⁻¹) ^ 2 := by group
    rw [e, hs5, hs2, inv_one, one_pow, one_mul]
  rw [hag, hs1, one_mul]

omit [Finite G] in
theorem pow_five_comm_of_mem_centralizer (d : Data G h) {g j : hypSU h 2 1} (hj : j ∈ I₁sub h)
    (hg : d.η g ∈ centralizer (d.I₁ : Set G)) : j ^ 5 * g = g * j ^ 5 := by
  have hc := mem_centralizer_iff.1 hg (d.η j) ⟨j, hj, rfl⟩
  have hs : g * j * g⁻¹ * j⁻¹ ∈ hypScalars h 2 1 := by
    rw [← d.η_eq_one_iff]
    simp only [map_mul, map_inv]
    rw [← hc]
    group
  set s := g * j * g⁻¹ * j⁻¹ with hsdef
  have hgj : g * j * g⁻¹ = s * j := by rw [hsdef, inv_mul_cancel_right]
  have h5 : g * j ^ 5 * g⁻¹ = j ^ 5 := by
    rw [← conj_pow, hgj, (Commute.mul_pow (scalar_central hs j).symm 5),
      pow_five_of_mem_hypScalars hs, one_mul]
  calc j ^ 5 * g = g * j ^ 5 * g⁻¹ * g := by rw [h5]
    _ = g * j ^ 5 := by group

theorem Hyp.isQuasisimple_N₁ (hd : d.Hyp) : CFSG.Open.IsQuasisimple d.N₁ := by
  have := h.charP
  have := h.finite
  let := Fintype.ofFinite K
  have h4 : 4 ≤ Fintype.card K := by
    rw [← Nat.card_eq_fintype_card, h.card_eq_sq]
    have := hd.four_le
    nlinarith
  have := GMSK.sl2_isSimpleGroup (CharTwo.two_eq_zero (R := K)) h4
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv d.N₁equiv.symm
    (isQuasisimple_of_isSimpleGroup' GMSK.sl2_exists_mul_ne)

theorem Hyp.commutator_N₁ (hd : d.Hyp) : ⁅d.N₁, d.N₁⁆ = d.N₁ := by
  have h1 : commutator d.N₁ = ⊤ := hd.isQuasisimple_N₁.1
  have h2 := congrArg (Subgroup.map d.N₁.subtype) h1
  rwa [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype] at h2

theorem Hyp.N₁_eq_commutator (hd : d.Hyp) :
    d.N₁ = ⁅d.L ⊓ centralizer (d.I₁ : Set G), d.L ⊓ centralizer (d.I₁ : Set G)⁆ := by
  have hle : d.N₁ ≤ d.L ⊓ centralizer (d.I₁ : Set G) :=
    le_inf (d.pull_le_L _) d.N₁_le_centralizer_I₁
  refine le_antisymm ?_ ?_
  · calc d.N₁ = ⁅d.N₁, d.N₁⁆ := hd.commutator_N₁.symm
      _ ≤ _ := commutator_mono hle hle
  · rw [commutator_le]
    intro a ha b hb
    obtain ⟨haL, haC⟩ := Subgroup.mem_inf.1 ha
    obtain ⟨hbL, hbC⟩ := Subgroup.mem_inf.1 hb
    rw [← d.range_η] at haL hbL
    obtain ⟨g, rfl⟩ := haL
    obtain ⟨g', rfl⟩ := hbL
    obtain ⟨j, hj, β, -, hβ, -, e1, e2, e3, e4, e5⟩ := exists_I₁_fifth (h := h) hd.two_le
    have ht : j ^ 5 ∈ hypTorus h 2 1 := pow_mem (torusEq_le _ hj) 5
    have hc := commutator_mem_N₁sub ht hβ e1 e2 e3 e4 e5
      (d.pow_five_comm_of_mem_centralizer hj haC) (d.pow_five_comm_of_mem_centralizer hj hbC)
    exact ⟨_, hc, map_commutatorElement d.η g g'⟩

theorem Hyp.conj_mem_N₁ (hd : d.Hyp) {c : G} (hcL : c ∈ normalizer (d.L : Set G))
    (hc : c ∈ centralizer (d.I₁ : Set G)) {n : G} (hn : n ∈ d.N₁) : c * n * c⁻¹ ∈ d.N₁ := by
  set M := d.L ⊓ centralizer (d.I₁ : Set G) with hM
  have hcM : c ∈ normalizer (M : Set G) :=
    Common.mem_normalizer_inf hcL (le_normalizer hc)
  have hmap : M.map (MulAut.conj c).toMonoidHom = M := by
    refine le_antisymm ?_ fun x hx => ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hcM x).1 hx
    · refine ⟨c⁻¹ * x * c, ?_, by simp [MulAut.conj_apply]; group⟩
      refine (mem_normalizer_iff.1 hcM _).2 ?_
      rw [show c * (c⁻¹ * x * c) * c⁻¹ = x by group]
      exact hx
  rw [hd.N₁_eq_commutator] at hn ⊢
  have e : (⁅M, M⁆ : Subgroup G).map (MulAut.conj c).toMonoidHom = ⁅M, M⁆ := by
    rw [map_commutator, hmap]
  rw [← e]
  exact ⟨n, hn, rfl⟩

theorem Hyp.isSylowOf_zpowers_N₁ (hd : d.Hyp) :
    IsSylowOf 2 (zpowers d.t) (centralizer (d.I₁ : Set G) ⊓ centralizer (d.N₁ : Set G)) := by
  refine CFSG.ComponentClassification.AS81.Sec2Quot.isSylowOf_of_forall_mem_normalizer
    (zpowers_le.2 ⟨hd.t_mem_centralizer_I₁, hd.t_mem_centralizer_N₁⟩) hd.isPGroup_zpowers_t
    fun c hc hcN ⟨k, hk⟩ => ?_
  obtain ⟨hcI, hcN₁⟩ := Subgroup.mem_inf.1 hc
  have hct : c ∈ centralizer ({d.t} : Set G) := by
    rw [← CFSG.SeitzReduction.RankOne.normalizer_zpowers_eq_centralizer_of_involution hd.t_two]
    exact hcN
  have hcL := hd.centralizer_le_normalizer hct
  obtain ⟨y, hy⟩ := Phi_surjective h (d.act ⟨c, hcL⟩)
  have hI := d.act_I₁_of_mem_centralizer hcL hy hcI
  have hfix : ∀ g ∈ N₁sub h, g * g = 1 → actΓ h y g = g := fun g hg hgg =>
    d.act_eq_of_η_eq_of_sq hgg (by
      rw [← d.conj_η_eq hcL hy, ← mem_centralizer_iff.1 hcN₁ _ ⟨g, hg, rfl⟩,
        mul_inv_cancel_right])
  have hU : ∀ u ∈ patSub h sI₁ isPattern_sI₁, actΓ h y u = u := fun u hu =>
    hfix u (patSub_I₁_le_N₁sub hu) (mul_self_of_mem_patSub_I₁ hu)
  have hr : actΓ h y (rSU h) = rSU h := hfix _ rSU_mem_N₁sub rSU_mul_self
  have hk' : Phi h y ^ 2 ^ k = 1 := by
    have e : (⟨c, hcL⟩ : normalizer (d.L : Set G)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using hk)
    rw [hy, ← map_pow, e, map_one]
  have hPhi := Phi_eq_one_of_centralizes_I₁N₁ hd.two_le hI hU hr hk'
  have hcC : c ∈ centralizer (d.L : Set G) := (d.act_eq_one_iff _).1 (by rw [← hy, hPhi])
  rw [← hd.sec3_1'.1]
  exact ⟨hcC, hct⟩

end Data

end CFSG.LocalAnalysis.EvenBN.U5
