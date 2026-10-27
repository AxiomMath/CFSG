module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ParabolicCore
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.Parrott.P614K136Torus
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.RootCenterAutomorphismBasic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty (S622IsSimpleSection)
open Subgroup

theorem exists_stabilizer_eq_of_overgroup_borel {F : Type} [Field F] [Finite F]
    (hF : ∃ k : ℕ, Nat.card F = 2 ^ k) (h3 : ¬ 3 ∣ Nat.card F - 1)
    (P : Subgroup SL(3, F)) (hBP : upperTriangular 3 F ≤ P) (hne : P ≠ ⊤)
    {z : SL(3, F)} (hzP : z ∈ P) (hz : orderOf z = 3) :
    ∃ d : ℕ, 1 ≤ d ∧ d < 3 ∧ P = stabilizer (flagSpace 3 F d) := by
  obtain ⟨hPI, -⟩ := LinearFlag.borel_overgroups P hBP
  by_cases h1 : 1 ∈ LinearFlag.borelOvergroupCuts P
  · by_cases h2 : 2 ∈ LinearFlag.borelOvergroupCuts P
    ·
      have hle : P ≤ LinearFlag.upperTriangular 3 F := by
        refine CFSG.Quasithin.SzN2.le_upperTriangular_of_cuts hPI.le ?_
        intro i hi1 hin
        rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
        · exact h1
        · exact h2
      exact absurd hz
        (CFSG.Quasithin.SzN2.orderOf_ne_three_of_mem_upperTriangular hF h3 (hle hzP))
    ·
      have hI : LinearFlag.borelOvergroupCuts P = {1} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨h1, fun i hi => ?_⟩
        have hb : 1 ≤ i ∧ i < 3 := by
          obtain ⟨hi1, hin, -⟩ := hi
          exact ⟨hi1, hin⟩
        obtain ⟨hb1, hb2⟩ := hb
        rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
        · rfl
        · exact absurd hi h2
      refine ⟨1, by norm_num, by norm_num, ?_⟩
      rw [hPI, hI, LinearFlag.flagStabilizer_singleton]
  · by_cases h2 : 2 ∈ LinearFlag.borelOvergroupCuts P
    ·
      have hI : LinearFlag.borelOvergroupCuts P = {2} := by
        refine Set.eq_singleton_iff_unique_mem.mpr ⟨h2, fun i hi => ?_⟩
        have hb : 1 ≤ i ∧ i < 3 := by
          obtain ⟨hi1, hin, -⟩ := hi
          exact ⟨hi1, hin⟩
        obtain ⟨hb1, hb2⟩ := hb
        rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
        · exact absurd hi h1
        · rfl
      refine ⟨2, by norm_num, by norm_num, ?_⟩
      rw [hPI, hI, LinearFlag.flagStabilizer_singleton]
    ·
      have hI : LinearFlag.borelOvergroupCuts P = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun i hi => ?_
        have hb : 1 ≤ i ∧ i < 3 := by
          obtain ⟨hi1, hin, -⟩ := hi
          exact ⟨hi1, hin⟩
        obtain ⟨hb1, hb2⟩ := hb
        rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
        · exact h1 hi
        · exact h2 hi
      have hPtop : P = ⊤ := by
        rw [hPI, hI, LinearFlag.flagStabilizer_empty]
      exact absurd hPtop hne

theorem parabolic_section_of_psl3 {Kg : Type} [Group Kg] [Finite Kg] {n : ℕ}
    (hn : Odd n) (hn3 : 3 ≤ n) (φ : Kg ≃* PSL(3, GaloisField 2 n)) (Q : Sylow 2 Kg)
    (K₀ : Subgroup Kg) (hQ : normalizer (Q : Set Kg) ≤ K₀) (hne : K₀ ≠ ⊤)
    {z : Kg} (hz : orderOf z = 3) (hzK₀ : z ∈ K₀) :
    ∃ H N : Subgroup Kg, H ≤ K₀ ∧ S622IsSimpleSection H N ∧ z ∈ H ∧ z ∉ N ∧ 3 ∣ N.relIndex H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have h8 : 8 ≤ Nat.card (GaloisField 2 n) := by
    rw [hcard]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h3 : ¬ 3 ∣ Nat.card (GaloisField 2 n) - 1 := by
    rw [hcard]
    exact Parrott.P614.P614K136.not_three_dvd_two_pow_sub_one hn
  have hF3 : ∀ a : GaloisField 2 n, a ^ 3 = 1 → a = 1 :=
    fun a ha => Parrott.P614.P614K136.eq_one_of_pow_three hn hcard ha
  have hF : ∃ k : ℕ, Nat.card (GaloisField 2 n) = 2 ^ k := ⟨n, hcard⟩
  obtain ⟨Ut, hUt⟩ := LinearFlag.exists_sylow_unitriangular (K := GaloisField 2 n) 2 (n := 3)
    (by norm_num)
  obtain ⟨ε, hε⟩ := CFSG.ProperTwoGeneratedCore.RootCenter.exists_mulEquiv_map_eq
    (φ.trans (Parrott.P614.P614K136.pslEquivSL hF3))
    Ut Q
  have hU : Subgroup.map ε.toMonoidHom (LinearFlag.unitriangular 3 (GaloisField 2 n)) =
      (Q : Subgroup Kg) := by
    rw [← hUt]
    exact hε
  have hUB : Subgroup.map ε.toMonoidHom (LinearFlag.upperTriangular 3 (GaloisField 2 n)) =
      normalizer (Q : Set Kg) := by
    rw [← LinearFlag.normalizer_unitriangular, Subgroup.map_equiv_normalizer_eq, hU]
    rfl
  have hmap : Subgroup.map ε.toMonoidHom (LinearFlag.upperTriangular 3 (GaloisField 2 n)) ≤ K₀ := by
    rw [hUB]
    exact hQ
  obtain ⟨P, hP⟩ : ∃ P : Subgroup SL(3, GaloisField 2 n), P = K₀.comap ε.toMonoidHom :=
    ⟨_, rfl⟩
  have hBP : LinearFlag.upperTriangular 3 (GaloisField 2 n) ≤ P := by
    rw [hP]
    exact Subgroup.map_le_iff_le_comap.mp hmap
  have hPtop : P ≠ ⊤ := by
    intro htop
    apply hne
    rw [Subgroup.eq_top_iff']
    intro y
    have hy : ε.symm y ∈ P := by
      rw [htop]
      exact Subgroup.mem_top _
    rw [hP] at hy
    have hy' : ε.toMonoidHom (ε.symm y) ∈ K₀ := Subgroup.mem_comap.mp hy
    simpa using hy'
  have hzP : ε.symm z ∈ P := by
    rw [hP]
    refine Subgroup.mem_comap.mpr ?_
    simpa using hzK₀
  have hord : orderOf (ε.symm z) = 3 := by
    have h := orderOf_injective ε.symm.toMonoidHom ε.symm.injective z
    rw [hz] at h
    exact h
  obtain ⟨d, hd1, hd3, hPeq⟩ :=
    exists_stabilizer_eq_of_overgroup_borel hF h3 P hBP hPtop hzP hord
  have hscal : Nat.card (LinearFlag.scalars 3 (GaloisField 2 n)) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.card_scalars_eq_gcd (GaloisField 2 n)
      (by norm_num : 1 ≤ 3)]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
  have hinj : Function.Injective (LinearFlag.proj 3 (GaloisField 2 n)) := by
    refine (MonoidHom.ker_eq_bot_iff _).mp ?_
    rw [LinearFlag.ker_proj]
    exact Subgroup.eq_bot_of_card_eq (H := LinearFlag.scalars 3 (GaloisField 2 n)) hscal
  obtain ⟨pe, hpe⟩ : ∃ pe : SL(3, GaloisField 2 n) ≃* projectiveSL 3 (GaloisField 2 n),
      ∀ g, pe g = LinearFlag.proj 3 (GaloisField 2 n) g :=
    ⟨MulEquiv.ofBijective (LinearFlag.proj 3 (GaloisField 2 n))
      ⟨hinj, LinearFlag.proj_surjective 3 (GaloisField 2 n)⟩, fun g => rfl⟩
  obtain ⟨θ, hθ⟩ : ∃ θ : projectiveSL 3 (GaloisField 2 n) ≃* Kg,
      ∀ g : SL(3, GaloisField 2 n), θ (LinearFlag.proj 3 (GaloisField 2 n) g) = ε g :=
    ⟨pe.symm.trans ε, fun g => by
      show ε (pe.symm (LinearFlag.proj 3 (GaloisField 2 n) g)) = ε g
      rw [← hpe, MulEquiv.symm_apply_apply]⟩
  have hzbar_ord : orderOf (LinearFlag.proj 3 (GaloisField 2 n) (ε.symm z)) = 3 := by
    rw [orderOf_injective (LinearFlag.proj 3 (GaloisField 2 n)) hinj (ε.symm z)]
    exact hord
  have hzbar_mem : LinearFlag.proj 3 (GaloisField 2 n) (ε.symm z) ∈
      (LinearFlag.stabilizer (LinearFlag.flagSpace 3 (GaloisField 2 n) d)).map
        (LinearFlag.proj 3 (GaloisField 2 n)) := by
    refine Subgroup.mem_map_of_mem _ ?_
    rw [← hPeq]
    exact hzP
  obtain ⟨H, N, hHle, hsimple, hzH, hzN, hrel⟩ :=
    projSL3_parabolic_section h8 h3 hd1 hd3 hzbar_ord hzbar_mem
  have hθz : θ (LinearFlag.proj 3 (GaloisField 2 n) (ε.symm z)) = z := by
    rw [hθ (ε.symm z), ε.apply_symm_apply]
  refine ⟨H.map θ.toMonoidHom, N.map θ.toMonoidHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hyH, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp (hHle hyH)
    show θ (LinearFlag.proj 3 (GaloisField 2 n) g) ∈ K₀
    rw [hθ g]
    rw [← hPeq, hP] at hg
    exact Subgroup.mem_comap.mp hg
  · exact isSimpleSection_map_injective θ.toMonoidHom θ.injective hsimple
  · rw [← hθz]
    exact Subgroup.mem_map_of_mem _ hzH
  · intro hzN'
    obtain ⟨y, hyN, hy⟩ := Subgroup.mem_map.mp hzN'
    have hy' : θ y = z := hy
    have hyeq : y = LinearFlag.proj 3 (GaloisField 2 n) (ε.symm z) :=
      θ.injective (hy'.trans hθz.symm)
    rw [hyeq] at hyN
    exact hzN hyN
  · rw [Subgroup.relIndex_map_map_of_injective (f := θ.toMonoidHom) N H θ.injective]
    exact hrel

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
