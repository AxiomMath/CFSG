module

public import CFSG.LocalAnalysis.SectionRank.QTK.OddTorusL
import CFSG.RankThree.PartTwo.Census.OddClassical.UnitaryWitness

public section

namespace CFSG.SectionRank.QTK

open CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.Census (torusSL torusSL_injective coe_torusSL torusEntries
  rootsOfUnity_pow_eq_one card_fun_rootsOfUnity card_rootsOfUnity_of_dvd isElemAbelian_range
  le_localRank_quotient_of_commute diagGL torusEntries_compLeft torusEntries_of_gt prod_torusEntries
  torusEntries_injective)

variable {K : Type} [Field K]

theorem le_localRank_statedSU_torus_odd [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K)
    (hp2 : p ≠ 2) {r m n : ℕ} (hr : r.Prime) (hrq : r ∣ p ^ f + 1) (hmn : m < n) (h2n : 2 < n)
    (hcen : m + 1 < n ∨ ¬ r ∣ n) :
    m ≤ localRank r (StatedProj (StatedSU n (p ^ f) K)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have h2 := CFSG.RankThree.PartTwo.Census.two_ne_zero_of_unitaryFieldData h hp2
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul', sq,
      show p ^ f * p ^ f - 1 = p ^ f * p ^ f - 1 * 1 by rw [mul_one],
      Nat.mul_self_sub_mul_self_eq]
    exact dvd_mul_of_dvd_left hrq _
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set d : (Fin m → μ) →* (Fin n → Kˣ) := (incl.compLeft (Fin n)).comp (torusEntries μ m n)
  set ψ := (diagGL n K).comp d
  have hd : ∀ s i, d s i = incl (torusEntries μ m n s i) := fun _ _ => rfl
  have hdr : ∀ s i, (d s i : K) ^ r = 1 := by
    intro s i
    rw [hd, ← Units.val_pow_eq_pow_val, ← map_pow, rootsOfUnity_pow_eq_one, map_one,
      Units.val_one]
  have hcoe : ∀ s, ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (d s i : K) := fun _ => rfl
  have hmem : ∀ s, ψ s ∈ StatedSU n (p ^ f) K := by
    intro s
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoe, det_diagonal, ← Units.coe_prod]
      have : ∏ i, d s i = incl (∏ i, torusEntries μ m n s i) := by
        rw [map_prod]
        rfl
      rw [this, prod_torusEntries hmn, map_one, Units.val_one]
    · rw [hcoe, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      refine congrArg diagonal (funext fun i => ?_)
      obtain ⟨k, hk⟩ := hrq
      rw [h.bar_apply, ← pow_succ, hk, pow_mul, hdr, one_pow]
  set ψ' : (Fin m → μ) →* StatedSU n (p ^ f) K := ψ.codRestrict _ hmem
  have hψ' : Function.Injective ψ' := by
    intro s t hst
    have h1 : ψ s = ψ t := congrArg Subtype.val hst
    have h3 : d s = d t := by
      funext i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h1
      simp only [hcoe, diagonal_apply_eq] at this
      exact Units.ext this
    exact torusEntries_injective hmn.le (funext fun i => Subtype.ext (congrFun h3 i))
  have htmem : twoSignGL n K ∈ StatedSU n (p ^ f) K := by
    refine (mem_unitarySU_iff h).mpr ⟨det_diagonal_twoSign (by omega), ?_⟩
    change ((diagonal (twoSign n K)).map h.bar)ᵀ * diagonal (twoSign n K) = 1
    rw [diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    refine congrArg diagonal (funext fun i => ?_)
    have hbar : h.bar (twoSign n K i) = twoSign n K i := by
      simp only [twoSign]
      split_ifs <;> simp
    rw [hbar, twoSign_mul_self]
  set Z := (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)
  set t : StatedSU n (p ^ f) K := ⟨twoSignGL n K, htmem⟩
  refine le_localRank_quotient_of_commute Z hr (E := ψ'.range)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) ψ') ?_ ?_
    (t := t) ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ').toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxZ⟩
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hxZ)
    have hc' : GeneralLinearGroup.scalar (Fin n) c = ψ s := hc
    have hci : ∀ i, (c : K) = (d s i : K) := by
      intro i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) hc'
      simpa only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, hcoe]
        using this
    have hc1 : (c : K) = 1 := by
      rcases hcen with hlt | hndvd
      · rw [hci ⟨m + 1, hlt⟩, hd, torusEntries_of_gt _ (by simp), map_one, Units.val_one]
      · have hcr : (c : K) ^ r = 1 := by rw [hci ⟨0, by omega⟩, hdr]
        have hcn : (c : K) ^ n = 1 := by
          have hdet := ((mem_unitarySU_iff h).mp (hmem s)).1
          rw [← hc', GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
            Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
          exact hdet
        have hg : (c : K) ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr hndvd), pow_one]
          at hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    change ψ s = 1
    rw [← hc', show c = 1 from Units.ext hc1, map_one]
  · intro htZ
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp htZ
    have hc' : GeneralLinearGroup.scalar (Fin n) c = twoSignGL n K := hc
    have h0 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨0, by omega⟩) hc'
    have h22 := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) ⟨2, h2n⟩
      ⟨2, h2n⟩) hc'
    change scalar (Fin n) (c : K) ⟨0, by omega⟩ ⟨0, by omega⟩ =
      diagonal (twoSign n K) ⟨0, by omega⟩ ⟨0, by omega⟩ at h0
    change scalar (Fin n) (c : K) ⟨2, h2n⟩ ⟨2, h2n⟩ =
      diagonal (twoSign n K) ⟨2, h2n⟩ ⟨2, h2n⟩ at h22
    rw [scalar_apply, diagonal_apply_eq, diagonal_apply_eq] at h0 h22
    exact twoSign_zero_ne_two h2 h2n (h0.symm.trans h22)
  · rw [show t ^ 2 = 1 from Subtype.ext (Units.ext (by
      rw [pow_two]
      exact diagonal_twoSign_mul_self))]
    exact Z.one_mem
  · rintro _ ⟨s, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    change ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * diagonal (twoSign n K) =
      diagonal (twoSign n K) * ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hcoe, diagonal_mul_diagonal, diagonal_mul_diagonal]
    exact congrArg diagonal (funext fun i => mul_comm _ _)

end CFSG.SectionRank.QTK
