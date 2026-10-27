module

public import CFSG.ClassicalInvolution.Q3.Q3P21Y3S
public import CFSG.ClassicalInvolution.Q3.Q3TY32

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3P21

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Phan
open scoped MatrixGroups

section Model

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem top_le_iSup_longRootSetU (hK : Nat.card K = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (hq : p ^ f ≠ 2) :
    (⊤ : Subgroup (Su K p f 4)) ≤
      ⨆ R ∈ longRootSetU (K := K) (p := p) (f := f) (by norm_num : 2 ≤ 4), R := by
  have h2 : (2 : K) ≠ 0 := CFSG.ClassicalInvolution.Models.two_ne_zero_of_charP_ne_two hp2
  rw [← iSup_range_blockEmb2 hK hq 3]
  refine iSup_le fun i => ?_
  have hi : (blockEmb2 K p f 3 i).range = LcU K p f (nodePair 3 i.1 i.2) :=
    range_blockEmb2_eq_LcU_nodePair h2 i.2
  rw [hi]
  exact le_iSup₂_of_le (LcU K p f (nodePair 3 i.1 i.2)) (LcU_mem_longRootSetU h2 _ _) le_rfl

end Model

section Context


variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G} {K : Subgroup G}

theorem range_le_iSup_fund_psu4 (c : Q3TP.TCtxS3 .PSU 4 Ω K z) :
    c.d.ψ.range ≤ ⨆ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
      R.map c.d.ψ := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hadmU : StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩
  obtain ⟨e, he⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadmU
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  have hgen := top_le_iSup_longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hK hp2
    (by norm_num)
  set S : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K :=
    ⨆ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D, R with hS
  have hSe : ⨆ R' ∈ longRootSetU (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1)
      (by norm_num : 2 ≤ 4), R' ≤ S.map e.toMonoidHom := by
    refine iSup₂_le fun R' hR' => ?_
    have hmem : R'.map e.symm.toMonoidHom ∈
        fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D := by
      rw [he]
      have : (R'.map e.symm.toMonoidHom).map e.toMonoidHom = R' := by
        rw [Subgroup.map_map]
        have : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ :=
          MonoidHom.ext fun x => by simp
        rw [this, Subgroup.map_id]
      rw [this]
      exact hR'
    have hle : R'.map e.symm.toMonoidHom ≤ S := le_iSup₂_of_le _ hmem le_rfl
    intro x hx
    refine Subgroup.mem_map.mpr ⟨e.symm x, hle ⟨x, hx, rfl⟩, by simp⟩
  have hSψ : S ≤ (⨆ R ∈ fundamentalSubgroups .PSU
      (modelUniv .PSU 4 3 1 Nat.prime_three).D, R.map c.d.ψ).comap c.d.ψ :=
    iSup₂_le fun R hR => Subgroup.map_le_iff_le_comap.mp (le_iSup₂_of_le R hR le_rfl)
  rintro _ ⟨x, rfl⟩
  have hx : e x ∈ S.map e.toMonoidHom := hSe (hgen (Subgroup.mem_top _))
  have hxS : x ∈ S := by
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.mp hx
    have : y = x := e.injective hye
    rwa [this] at hy
  exact hSψ hxS

theorem exists_noncomm_partner_psu4 (c : Q3TP.TCtxS3 .PSU 4 Ω K z) :
    ∀ R₀ ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
      ∃ R' ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
        R' ≠ R₀ ∧ ¬ Commutes R₀ R' := by
  intro R₀ hR₀
  obtain ⟨R, hR, R', hR', hRR', hnc⟩ := Q3TY.exists_noncommuting_fund_psu4
  obtain ⟨g, hg⟩ := c.hY.sc R hR R₀ hR₀
  have hinv : ∀ L : Subgroup (modelUniv .PSU 4 3 1 Nat.prime_three).K,
      conjSub g⁻¹ (conjSub g L) = L := fun L => by
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  refine ⟨conjSub g R', conjSub_mem_fundamentalSubgroups hR' g, fun h => hRR' ?_, fun h => hnc ?_⟩
  · rw [hg] at h
    have := congrArg (conjSub g⁻¹) h
    rw [hinv, hinv] at this
    exact this.symm
  · rw [hg] at h
    have := h.conjSub g⁻¹
    rwa [hinv, hinv] at this

variable {t : G}

theorem conjSub_twin_eq_psu4 (c : Q3TP.TCtxS3 .PSU 4 Ω K z) (ht : t * z * t⁻¹ = z)
    (h2t : t * t = 1) (hKt : conjSub t K = K) {T : Subgroup G}
    (hT : T ∈ centralizingMembers Ω {z}) (hTQ : locImg Ω z T ≤ c.d.Q₁) : conjSub t T = T := by
  by_contra hne
  have hΩ := c.hΩ.conjInvariant
  have hN₀z : conjSub t T ∈ centralizingMembers Ω {z} :=
    conjSub_mem_centralizingMembers3 hΩ ht hT
  have hTK : T ≠ K := c.twin_ne hT hTQ
  have hN₀K : conjSub t T ≠ K := fun h => hTK (by
    have := congrArg (conjSub t) h
    rwa [Gaps.conjSub_conjSub_self h2t, hKt] at this)
  have hall : ∀ L ∈ centralizingMembers Ω {z}, L ≠ conjSub t T → Commutes (conjSub t T) L := by
    intro L hL hLN
    have hL' : conjSub t L ∈ centralizingMembers Ω {z} :=
      conjSub_mem_centralizingMembers3 hΩ ht hL
    have hne' : conjSub t L ≠ T := fun h => hLN (by
      rw [← Gaps.conjSub_conjSub_self h2t L, h])
    have h1 := (c.commutes_T_of_ne hT hTQ hL' hne').conjSub t
    rwa [Gaps.conjSub_conjSub_self h2t] at h1
  have hN₀Q : ¬ locImg Ω z (conjSub t T) ≤ c.d.Q₁ := fun h =>
    hne (c.eq_of_locImg_le_Q₁ hN₀z hT h hTQ)
  obtain ⟨R₀, hR₀, hR₀eq⟩ := c.exists_fund_of_ne hN₀z hN₀K hN₀Q
  obtain ⟨R', hR', hR'R₀, hncR⟩ := exists_noncomm_partner_psu4 c R₀ hR₀
  obtain ⟨N', hN'z, -, -, hN'eq⟩ := c.exists_member_of_fund hR'
  have hnc : ¬ Commutes (conjSub t T) N' := fun h =>
    hncR ((c.commutes_iff_fund hN₀z hN'z hR₀ hR₀eq hN'eq).mp h)
  have hN'N₀ : N' ≠ conjSub t T := fun h => hR'R₀
    (eq_of_map_eq_of_pow3 c.d.ψ c.d.ker_le c.ker_cop (c.hY.pow3 R' hR') (c.hY.pow3 R₀ hR₀)
      (by rw [← hN'eq, ← hR₀eq, h]))
  exact hnc (hall N' hN'z hN'N₀)

theorem stab_psu4 (c : Q3TP.TCtxS3 .PSU 4 Ω K z) : StabStmt c := by
  intro t ht h2t hKt x
  have hΩ := c.hΩ.conjInvariant
  obtain ⟨T, hT, hTeq⟩ := c.exists_twin
  have hTt := conjSub_twin_eq_psu4 c ht h2t hKt hT hTeq.le
  have hS : ∀ R ∈ fundamentalSubgroups .PSU (modelUniv .PSU 4 3 1 Nat.prime_three).D,
      (R.map c.d.ψ).map (Gaps.locAut hΩ ht).toMonoidHom ≤ c.d.ψ.range := by
    intro R hR
    obtain ⟨N, hNz, hNK, hNQ, hNeq⟩ := c.exists_member_of_fund hR
    have hN'z := conjSub_mem_centralizingMembers3 hΩ ht hNz
    have hN'K : conjSub t N ≠ K := fun h => hNK (by
      have := congrArg (conjSub t) h
      rwa [Gaps.conjSub_conjSub_self h2t, hKt] at this)
    have hN'Q : ¬ locImg Ω z (conjSub t N) ≤ c.d.Q₁ := by
      intro h
      have h1 := c.eq_of_locImg_le_Q₁ hN'z hT h hTeq.le
      apply hNQ
      have : N = T := by rw [← Gaps.conjSub_conjSub_self h2t N, h1, hTt]
      rw [this, hTeq]
    obtain ⟨R', -, hR'eq⟩ := c.exists_fund_of_ne hN'z hN'K hN'Q
    rw [← hNeq, Gaps.locAut_locImg hΩ ht, hR'eq]
    rintro _ ⟨y, -, rfl⟩
    exact ⟨y, rfl⟩
  have hmap : c.d.ψ.range.map (Gaps.locAut hΩ ht).toMonoidHom ≤ c.d.ψ.range := by
    refine (Subgroup.map_mono (range_le_iSup_fund_psu4 c)).trans ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    exact iSup_le fun hR => hS R hR
  exact hmap ⟨_, ⟨x, rfl⟩, rfl⟩

end Context

end CFSG.ClassicalInvolution.Q3.Q3P21
