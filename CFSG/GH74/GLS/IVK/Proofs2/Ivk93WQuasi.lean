module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4McL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WSpor

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.LU.Local CFSG.Blueprint
  CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore CFSG.ClassicalInvolution CFSG.Sporadic.Ly

theorem hN_of_two_pow {N k : ℕ} (hk : N.factorization 2 = k)
    (hq : ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ N → ¬ 2 ^ k ∣ q * (q ^ 2 - 1)) :
    ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ N →
      N.factorization 2 ≠ (q * (q ^ 2 - 1)).factorization 2 := by
  intro q hq5 hd heq
  have hne : q * (q ^ 2 - 1) ≠ 0 := by
    have := sl2_card_mono hq5
    norm_num at this
    omega
  apply hq q hq5 hd
  rw [Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne]
  omega

theorem hN40320_aux : ∀ q : ℕ, q ≤ 35 → 5 ≤ q → q * (q ^ 2 - 1) ∣ 40320 →
    ¬ 2 ^ 7 ∣ q * (q ^ 2 - 1) := by
  decide +kernel

theorem hN40320 : ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ 40320 → ¬ 2 ^ 7 ∣ q * (q ^ 2 - 1) := by
  intro q hq5 hd
  have hle : q * (q ^ 2 - 1) ≤ 40320 := Nat.le_of_dvd (by norm_num) hd
  have hq : q ≤ 35 := by
    by_contra h
    push Not at h
    have := sl2_card_mono (show 36 ≤ q by omega)
    norm_num at this
    omega
  exact hN40320_aux q hq hq5 hd

theorem hN39916800_aux : ∀ q : ℕ, q ≤ 341 → 5 ≤ q → q * (q ^ 2 - 1) ∣ 39916800 →
    ¬ 2 ^ 8 ∣ q * (q ^ 2 - 1) := by
  decide +kernel

theorem hN39916800 : ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ 39916800 → ¬ 2 ^ 8 ∣ q * (q ^ 2 - 1) := by
  intro q hq5 hd
  have hle : q * (q ^ 2 - 1) ≤ 39916800 := Nat.le_of_dvd (by norm_num) hd
  have hq : q ≤ 341 := by
    by_contra h
    push Not at h
    have := sl2_card_mono (show 342 ≤ q by omega)
    norm_num at this
    omega
  exact hN39916800_aux q hq hq5 hd

theorem ivk93w_mcl :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := hJ
  let e' : J ≃* ↥mclP := e.trans mclPermEquiv
  have hord : orderOf ((e' x : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.ord
  obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' x).2 hord
  let φ := GHInv.centralizerEquivConj mclP e' x hg hgt
  obtain ⟨hrange, -⟩ := mclRho_range
  obtain ⟨hs, hnab⟩ := mclX_simple
  have hs' : IsSimpleGroup ↥mclRho.range := by
    rw [hrange]
    exact hs
  have hnab' : ∃ a b : ↥mclRho.range, a * b ≠ b * a := by
    rw [hrange]
    exact hnab
  have hperf : Group.IsPerfect ↥mclCt := Subgroup.isPerfect_iff.2 mclCt_perfect
  have hqs : IsQuasisimple ↥mclCt :=
    GHInv.isQuasisimple_of_perfect_cover hperf mclRho.rangeRestrict mclRho.rangeRestrict_surjective hs'
      (by
        obtain ⟨a, b, hab⟩ := hnab'
        exact ⟨a, b, hab⟩)
      (by rw [MonoidHom.ker_rangeRestrict]; exact mclRho_ker_le_center)
  have hq : IsQuasisimple ↥(centralizer ({x} : Set J)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqs
  have hC : Nat.card ↥(centralizer ({x} : Set J)) = 40320 := by
    rw [Nat.card_congr φ.toEquiv]
    exact (mclT0_facts).2.2.2.1
  exact h.false_of_quasisimple_centralizer hq hC
    (hN_of_two_pow (k := 7) (nu2_eq_of (by norm_num) (by norm_num) (by norm_num)) hN40320)

theorem ivk93w_ly :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  obtain ⟨hkey, hq, -, hKcard⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  intro L _ _ hL y q B h _
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' y) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h.ord
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 → ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  obtain ⟨c, -, hcz⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' y)
    (Subgroup.mem_top _) hord
  obtain ⟨G, hG, φ, hqG, hcardG⟩ : ∃ (G : Type) (_ : Group G)
      (φ : ↥(centralizer ({y} : Set L)) ≃* G), CFSG.IsQuasisimple G ∧ Nat.card G = 39916800 :=
    ⟨↥LyProof.KJ, inferInstance,
      (GHInv.centralizerEquivConj (J : Subgroup (GL (Fin 111) (ZMod 5))) e' y
        (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5))) (g := (c : GL (Fin 111) (ZMod 5))) c.2
        (by rw [hcz]; simp)).trans
        ((GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans (MulEquiv.subgroupCongr hkey)),
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).1 hq, hKcard⟩
  have hq' : CFSG.IsQuasisimple ↥(centralizer ({y} : Set L)) :=
    LocalCores.isQuasisimple_of_mulEquiv φ.symm hqG
  have hC : Nat.card ↥(centralizer ({y} : Set L)) = 39916800 := by
    rw [Nat.card_congr φ.toEquiv]
    exact hcardG
  exact h.false_of_quasisimple_centralizer hq' hC
    (hN_of_two_pow (k := 8) (nu2_eq_of (by norm_num) (by norm_num) (by norm_num)) hN39916800)

end CFSG.GH74.GLS.IVK.Proofs2
