module

public import CFSG.LocalAnalysis.RankThreeUC.StronglyEmbedded
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.RankThree.PartOne.Q1327T.GlueDatum
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16Facts

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {G : Type} [Group G] [Finite G]

theorem localSetting_of_witness {p : ℕ} {P : Sylow p G} {M T : Subgroup G} (hS : Standing G)
    (hp : p ∈ rankThreeSigmaA G) (hw : IsWitness p P M)
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T M) (hΓ : rankThreeGamma 1 p (P : Subgroup G) ≤ M)
    (hV1 : uCore M T ≠ ⊥) : LocalSetting p M (uCore M T) where
  elemAbelian := (uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT).2
  ne_bot := hV1
  normalizer_eq := normalizer_eq_of_isMaxTwoLocal hw.maxLocal hV1
    (elementary_isPGroup 2 _ (uCore_le_and_isElemAbelian hS.charTwo hw.maxLocal.1 hT).2)
    (le_normalizer_uCore M T)
  self_normalizing := maxTwoLocal_self_normalizing M hw.maxLocal
  spe := fun g hg => ((hw.gamma_one_le_iff hS hp).mp hΓ).2.2 g hg
  u2 := fun X hX1 hX2 h2 => hw.u2 _ ⟨X, hX1, hX2, rfl⟩ (by rwa [inf_comm])

omit [Finite G] in
theorem pElementSubgroup_le (p : ℕ) (M : Subgroup G) :
    CFSG.RankThree.PartOne.pElementSubgroup p M ≤ M :=
  (Subgroup.closure_le M).mpr fun _ hx => hx.1

omit [Finite G] in
theorem le_normalizer_pElementSubgroup (p : ℕ) (M : Subgroup G) :
    M ≤ normalizer ((CFSG.RankThree.PartOne.pElementSubgroup p M : Subgroup G) : Set G) := by
  intro m hm
  rw [mem_normalizer_iff_map_conj_eq]
  have h := CFSG.RankThree.PartOne.Equivariance.pElementSubgroup_conjBy p m M
  have hM : CFSG.RankThree.PartOne.conjBy m M = M := by
    unfold CFSG.RankThree.PartOne.conjBy
    exact (mem_normalizer_iff_map_conj_eq.mp ((Subgroup.le_normalizer (H := M)) hm))
  rw [hM] at h
  exact h.symm

theorem pRank_le_pElementSubgroup {p : ℕ} (hp : p.Prime) (M : Subgroup G) :
    CFSG.Open.pRank p M ≤ CFSG.Open.pRank p (CFSG.RankThree.PartOne.pElementSubgroup p M) := by
  obtain ⟨E, hEM, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt M
  exact CFSG.SectionRank.le_pRank hp.one_lt
    (fun x hx => CFSG.RankThree.PartOne.Q1327T.mem_pElementSubgroup_of_pow_eq_one hp (hEM hx)
      (hE.2 x hx)) hE hcard

omit [Finite G] in
theorem uCore_ne_bot_of_thompsonJ {M T : Subgroup G}
    (h : ¬ CFSG.Quasithin.thompsonJ T ≤ centralizer (uCore M T : Set G)) : uCore M T ≠ ⊥ := by
  intro hbot
  apply h
  intro x _
  rw [mem_centralizer_iff]
  intro y hy
  rw [hbot] at hy
  have : y = 1 := hy
  rw [this, one_mul, mul_one]

theorem not_le_centralizer_omegaOneCenterIn {p : ℕ} (hp : p.Prime) {M T : Subgroup G}
    (hM2 : 2 ≤ CFSG.Open.pRank p M)
    (hZ1 : CFSG.RankThree.PartOne.omegaOneCenterIn T ≠ ⊥)
    (H4 : ∀ C : Subgroup G, C ≠ ⊥ → C ≤ T → (C.subgroupOf T).Characteristic →
      CFSG.Open.pRank p (normalizer (C : Set G)) ≤ 1) :
    ¬ CFSG.RankThree.PartOne.pElementSubgroup p M ≤
      centralizer ((CFSG.RankThree.PartOne.omegaOneCenterIn T : Subgroup G) : Set G) := by
  intro h
  have h1 := H4 _ hZ1 (CFSG.RankThree.PartOne.Sec15Final.omegaOneCenterIn_le T)
    (omegaOneCenterIn_characteristic T)
  have h2 : CFSG.RankThree.PartOne.pElementSubgroup p M ≤
      normalizer ((CFSG.RankThree.PartOne.omegaOneCenterIn T : Subgroup G) : Set G) :=
    h.trans fun x hx => by
      rw [mem_normalizer_iff]
      intro y
      have hx' : ∀ z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T, x * z * x⁻¹ = z := fun z hz => by
        have := mem_centralizer_iff.mp hx z hz
        rw [← this]
        simp
      have hx'' : ∀ z ∈ CFSG.RankThree.PartOne.omegaOneCenterIn T, x⁻¹ * z * x = z := fun z hz => by
        have := mem_centralizer_iff.mp hx z hz
        rw [mul_assoc, this]
        simp
      constructor
      · intro hy; rw [hx' y hy]; exact hy
      · intro hy
        have := hx'' _ hy
        rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at this
        exact this ▸ hy
  have h3 := CFSG.SectionRank.pRank_mono hp.one_lt h2
  have h4 := pRank_le_pElementSubgroup hp M
  omega

end CFSG.LocalAnalysis.RankThreeUC
