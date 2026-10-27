module

public import CFSG.LocalAnalysis.RankThreeTheoremC.OutCyclicEsix
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutRank
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294KDOutDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.RankThreeTheoremC

section Torus

variable {τ : Tag} {K : Type} [Field K]

theorem torusElt_mul_four_apply_single (i₁ i₂ i₃ i₄ k : Fin τ.rank) (a b c d : ℕ) (ζ : Kˣ) :
    ((torusElt τ K i₁ (ζ ^ a) * torusElt τ K i₂ (ζ ^ b) * torusElt τ K i₃ (ζ ^ c) *
        torusElt τ K i₄ (ζ ^ d) : (Module.End K (RootModule τ K))ˣ) :
        Module.End K (RootModule τ K)) (rootVec τ K (Pi.single k 1)) =
      (((ζ ^ a) ^ τ.cartan i₁ k * (ζ ^ b) ^ τ.cartan i₂ k * (ζ ^ c) ^ τ.cartan i₃ k *
        (ζ ^ d) ^ τ.cartan i₄ k : Kˣ) : K) • rootVec τ K (Pi.single k 1) := by
  have hr : IsRoot τ (Pi.single k (1 : ℤ)) := isRoot_single τ k
  simp only [Units.val_mul, Module.End.mul_apply, torusElt_rootVec _ _ hr, map_smul, smul_smul,
    sum_cartan_single]
  congr 1
  ring

end Torus

section Exceptional


theorem e6ThreeRankFour_holds : E6ThreeRankFour := by
  intro X _ _ ℓ f h h3
  obtain ⟨⟨hrp, hf1, -⟩, hm⟩ := h
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := nonempty_mulEquiv_adjointGroup .E6 hm
  have hcardU : 3 ∣ Nat.card Kˣ := by rw [Nat.card_units, hK]; exact h3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hcardU
  have hζ3 : ζ ^ 3 = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  let y : Fin Tag.E6.rank → adjointGroup Tag.E6 K := fun i =>
    ⟨torusElt Tag.E6 K i ζ, torusElt_mem_adjointGroup i ζ⟩
  have hy3 : ∀ i, y i ^ 3 = 1 := by
    intro i
    refine Subtype.ext ?_
    simp only [Subgroup.coe_pow, Subgroup.coe_one, y]
    rw [← torusElt_pow_eq, hζ3, torusElt_one]
  have hyc : ∀ i j, Commute (y i) (y j) := fun i j =>
    Subtype.ext (torusElt_mul_comm i j ζ ζ)
  refine four_le_pRank_of_mulEquiv e (y (0 : Fin 6)) (y (2 : Fin 6)) (y (3 : Fin 6))
    (y (4 : Fin 6)) (hy3 (0 : Fin 6)) (hy3 (2 : Fin 6)) (hy3 (3 : Fin 6)) (hy3 (4 : Fin 6))
    (hyc (0 : Fin 6) (2 : Fin 6)) (hyc (0 : Fin 6) (3 : Fin 6)) (hyc (0 : Fin 6) (4 : Fin 6))
    (hyc (2 : Fin 6) (3 : Fin 6)) (hyc (2 : Fin 6) (4 : Fin 6)) (hyc (3 : Fin 6) (4 : Fin 6)) ?_
  intro a b c d hind
  have hu : torusElt Tag.E6 K (0 : Fin 6) (ζ ^ a) * torusElt Tag.E6 K (2 : Fin 6) (ζ ^ b) *
      torusElt Tag.E6 K (3 : Fin 6) (ζ ^ c) * torusElt Tag.E6 K (4 : Fin 6) (ζ ^ d) = 1 := by
    have h := congrArg Subtype.val hind
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_one, y] at h
    rw [torusElt_pow_eq (τ := Tag.E6) (K := K) (0 : Fin 6) ζ a,
      torusElt_pow_eq (τ := Tag.E6) (K := K) (2 : Fin 6) ζ b,
      torusElt_pow_eq (τ := Tag.E6) (K := K) (3 : Fin 6) ζ c,
      torusElt_pow_eq (τ := Tag.E6) (K := K) (4 : Fin 6) ζ d]
    exact h
  have key : ∀ k : Fin Tag.E6.rank, (3 : ℤ) ∣ (a : ℤ) * Tag.cartan Tag.E6 (0 : Fin 6) k +
      b * Tag.cartan Tag.E6 (2 : Fin 6) k + c * Tag.cartan Tag.E6 (3 : Fin 6) k +
      d * Tag.cartan Tag.E6 (4 : Fin 6) k := by
    intro k
    have h1 := torusElt_mul_four_apply_single (τ := Tag.E6) (K := K) (0 : Fin 6) (2 : Fin 6)
      (3 : Fin 6) (4 : Fin 6) k a b c d ζ
    rw [hu, Units.val_one, Module.End.one_apply] at h1
    have h2 := rootVec_single_ne k _ h1.symm
    have h3 : ((ζ ^ a) ^ Tag.cartan Tag.E6 (0 : Fin 6) k *
        (ζ ^ b) ^ Tag.cartan Tag.E6 (2 : Fin 6) k * (ζ ^ c) ^ Tag.cartan Tag.E6 (3 : Fin 6) k *
        (ζ ^ d) ^ Tag.cartan Tag.E6 (4 : Fin 6) k : Kˣ) = 1 :=
      Units.ext h2
    have h4 : ζ ^ ((a : ℤ) * Tag.cartan Tag.E6 (0 : Fin 6) k + b * Tag.cartan Tag.E6 (2 : Fin 6) k +
        c * Tag.cartan Tag.E6 (3 : Fin 6) k + d * Tag.cartan Tag.E6 (4 : Fin 6) k) = 1 := by
      rw [← h3]
      simp only [zpow_add, zpow_mul, zpow_natCast]
    have h5 := orderOf_dvd_iff_zpow_eq_one.2 h4
    rw [hζ] at h5
    exact_mod_cast h5
  have k0 := key (0 : Fin 6)
  have k2 := key (2 : Fin 6)
  have k3 := key (3 : Fin 6)
  have k4 := key (4 : Fin 6)
  simp [Tag.cartan, Tag.cartanE] at k0 k2 k3 k4
  omega

end Exceptional

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
