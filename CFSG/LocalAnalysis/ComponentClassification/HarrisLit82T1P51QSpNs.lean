module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpSpl
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewComp
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneSpSkewE
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51QSpSelf
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate8046
public import Certificates.Certificate8049
public import Certificates.Certificate8052
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51Q

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext mem_statedSp_iff)
open CFSG.ComponentClassification.Burgoyne.Sp

variable {r : ℕ} {K : Type} [Field K] [Finite K]

theorem famF_concl_sp_nonsplit {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f)
    (hKc : Nat.card K = ℓ ^ f) (hq5 : 5 ≤ ℓ ^ f) (hr : 2 ≤ r) (hsq : ∀ l : K, l ^ 2 ≠ -1)
    {X : Type} [Group X] [Finite X] (π : StatedSp r K →* X) (hπ : Function.Surjective π)
    (hker : ∀ s, π s = 1 → ∃ μ : K,
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = μ • 1)
    {a : StatedSp r K}
    (ha : ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      skewNs r K (-1))
    (hz2 : π a * π a = 1) {P : Subgroup X} (hPC : P ≤ centralizer ({π a} : Set X))
    (h8 : Nat.card P = 8)
    (hP : ∀ L : Subgroup (centralizer ({π a} : Set X)), IsComponent L → Even (Nat.card L) →
      ∀ k ∈ L, ∀ g ∈ P, (k : X) * g = g * k) :
    ¬ ((∃ u ∈ P, ∃ v ∈ P, u * v ≠ v * u) ∧ ∀ q ∈ P, q * q = 1 → q = 1 ∨ q = π a) ∧
      ¬ ∀ q ∈ P, q * q = 1 := by
  have : Fintype K := Fintype.ofFinite K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  have hK : ringChar K ≠ 2 := by rw [ringChar.eq K ℓ]; exact hℓ2
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero hK
  have : NeZero r := ⟨by omega⟩
  have hd0 : (-1 : K) ≠ 0 := neg_ne_zero.2 one_ne_zero
  have hcard : Fintype.card K % 2 = 1 := by
    rw [← Nat.card_eq_fintype_card, hKc]
    exact Nat.odd_iff.1 (hℓ.odd_of_ne_two hℓ2).pow
  set Ma := ((a : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) with hMa
  have haa : Ma * Ma = -1 := by rw [ha, skewNs_mul_self, neg_one_smul]
  have hans : ∀ c : K, Ma ≠ c • 1 := by
    intro c hc
    have e := congrFun (congrFun hc (Sum.inr ⟨0, by omega⟩)) (Sum.inl ⟨0, by omega⟩)
    rw [ha, skewNs_apply_inr_inl] at e
    simp at e
  obtain ⟨L, hLF, hLn, hLq, hLp⟩ := exists_unitary_component hℓ hℓ2 hf hKc hr (Or.inr hq5)
    (skewNsGsp_ne_scalar (by omega) hd0) hsq (skewNs_mul_self (-1)) (skewNs_similitude (-1))
  have hcent : ∀ g : StatedSp r K, g ∈ centralizer ({a} : Set (StatedSp r K)) ↔
      g ∈ spCent r K (skewNsGsp r K hd0) := by
    intro g
    rw [mem_centralizer_singleton_iff, mem_spCent, coe_skewNsGsp, ← ha]
    constructor
    · intro h
      exact (congrArg (fun x : StatedSp r K =>
        ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h).symm
    · intro h
      exact Subtype.ext (Units.ext h.symm)
  have hNC : L ≤ centralizer ({a} : Set (StatedSp r K)) := fun x hx => (hcent x).2 (hLF hx)
  have hNn : ∀ x ∈ centralizer ({a} : Set (StatedSp r K)), ∀ m ∈ L, x * m * x⁻¹ ∈ L :=
    fun x hx m hm => hLn x ((hcent x).1 hx) m hm
  have hker' : ∀ s, π s = 1 → s ∈ center (StatedSp r K) := fun s hs => by
    obtain ⟨μ, hμ⟩ := hker s hs
    exact mem_center_of_coe_eq_smul_one hμ
  have hker2 : ∀ s, π s = 1 →
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 ∨
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = -1 :=
    fun s hs => by
      obtain ⟨μ, hμ⟩ := hker s hs
      exact eq_one_or_neg_of_coe_eq_smul hμ
  have hPT : ∀ g ∈ P, ∀ s, π s = g → s ∈ centralizer (L : Set (StatedSp r K)) := by
    intro g hg s hs
    have key := lift_commute_of_subnormal π hπ hker' a hLq le_rfl
      (fun x hx m hm => mul_mem (mul_mem hx hm) (inv_mem hx)) hNC hNn
      (fun L' hL' he k hk => hP L' hL' he k hk g hg) hs
    rw [mem_centralizer_iff]
    intro m hm
    exact (key m hm).symm
  have hTU : ∀ s ∈ centralizer (L : Set (StatedSp r K)),
      ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) * Ma =
        Ma * ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) →
      ∃ x y : K, x ^ 2 + y ^ 2 = 1 ∧
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          x • 1 + y • Ma := by
    intro s hs hsa
    obtain ⟨a₀, b₀, hab⟩ := exists_norm_neg_one hcard hd0
    have hab' : (-a₀) ^ 2 - (-1) * (-b₀) ^ 2 = -1 := by linear_combination hab
    have key : ∀ i j : Fin r, i ≠ j → ∀ a'' b'' : K, a'' ^ 2 - (-1) * b'' ^ 2 = -1 →
        ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
            skN (-1) i j a'' (b'' * -1) =
          skN (-1) i j a'' (b'' * -1) *
            ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      intro i j hij a'' b'' hab''
      obtain ⟨c1, c2, c3⟩ := skN_conds (r := r) hij hab''
      have hc : unipSp c1 c2 c3 1 ∈ spCent r K (skewNsGsp r K hd0) := by
        rw [mem_spCent, coe_unipSp, coe_skewNsGsp, Matrix.mul_add, Matrix.add_mul,
          Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul,
          (skN_commute (-1) i j a'' (b'' * -1)).symm]
      have hmem : unipSp c1 c2 c3 1 ∈ L := by
        refine hLp _ hc (statedSp_ext ?_)
        rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, coe_unipSp, one_add_smul_pow c3,
          CharP.cast_eq_zero, zero_mul, zero_smul, add_zero]
        rfl
      have h1 := (mem_centralizer_iff.1 hs) _ hmem
      have h1' := congrArg (fun x : StatedSp r K =>
        ((x : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
      simp only [Subgroup.coe_mul, Units.val_mul, coe_unipSp, one_smul] at h1'
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one] at h1'
      exact (add_left_cancel h1').symm
    have hMA : ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *
        skewNs r K (-1) =
          skewNs r K (-1) *
            ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [← ha]
      exact hsa
    obtain ⟨p', q', hpq⟩ := eq_add_smul_of_commute_skN (by omega) h2 hd0 hab hMA
      fun i j hij => ⟨key i j hij a₀ b₀ hab, key i j hij (-a₀) (-b₀) hab'⟩
    have hxy' : ((s : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
        p' • 1 + q' • Ma := by rw [hpq, ha]
    refine ⟨p', q', norm_eq_one_of_rot_mem (mem_statedSp_iff.1 a.2) haa ?_, hxy'⟩
    have hD := mem_statedSp_iff.1 s.2
    rwa [hxy'] at hD
  exact famF_concl_skew h2 π hπ hker2 haa hans hz2 hTU h8 hPC hPT

end CFSG.ComponentClassification.HarrisLit.T1.P51Q
