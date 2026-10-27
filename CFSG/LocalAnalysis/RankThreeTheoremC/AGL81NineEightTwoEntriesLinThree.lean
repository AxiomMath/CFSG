module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntriesThree
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3Mat
import CFSG.GH74.GLS.Stage2.Signalizer.Odd87P47Rank3
import CFSG.GroupTheory.ElemAbelianPlaneAction
import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearBasic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoCriteria
import CFSG.Milestones.ASVolI.F411.aL3Core
import CFSG.RankThree.SteinbergR3ELinearRegularUnipotent

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3

section LinThree

variable {F : Type} [Field F] [Finite F]

theorem centralizer_theta_le_normalizer (p : ℕ) [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) :
    centralizer ({theta (⟨0, 0, 1⟩ : Heis F)} : Set (projectiveSL 3 F)) ≤
      normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) := by
  intro x hx
  obtain ⟨g, rfl⟩ := proj_surjective 3 F x
  have hc : proj 3 F g * proj 3 F (heisSL (⟨0, 0, 1⟩ : Heis F)) =
      proj 3 F (heisSL (⟨0, 0, 1⟩ : Heis F)) * proj 3 F g :=
    mem_centralizer_singleton_iff.mp hx
  have hzp : heisSL (⟨0, 0, 1⟩ : Heis F) ^ p ^ 1 = 1 := by
    rw [pow_one, ← map_pow, Heis.pow_prime_eq_one Fact.out hp2, map_one]
  have hgz : g * heisSL (⟨0, 0, 1⟩ : Heis F) * g⁻¹ = heisSL (⟨0, 0, 1⟩ : Heis F) := by
    refine ASVolI.burnsideF411a_eq_of_proj_eq p (by norm_num) 1 ?_ hzp ?_
    · rw [conj_pow, hzp, mul_one, mul_inv_cancel]
    · rw [map_mul, map_mul, map_inv, hc, mul_inv_cancel_right]
  have hgz' : g * heisSL (⟨0, 0, 1⟩ : Heis F) = heisSL (⟨0, 0, 1⟩ : Heis F) * g := by
    calc g * heisSL (⟨0, 0, 1⟩ : Heis F)
        = g * heisSL (⟨0, 0, 1⟩ : Heis F) * g⁻¹ * g := by group
      _ = heisSL (⟨0, 0, 1⟩ : Heis F) * g := by rw [hgz]
  have hmat : (g : Matrix (Fin 3) (Fin 3) F) * heisMat (⟨0, 0, 1⟩ : Heis F) =
      heisMat (⟨0, 0, 1⟩ : Heis F) * (g : Matrix (Fin 3) (Fin 3) F) := by
    have h := congrArg (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F))
      hgz'
    simpa [coe_heisSL] using h
  obtain ⟨h10, h20, h21⟩ := lower_entries_zero g 1 hmat
  have hgN : g ∈ normalizer (unitriangular 3 F : Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [normalizer_unitriangular]
    exact mem_upperTriangular_of_lower_entries h10 h20 h21
  exact le_normalizer_map (proj 3 F) (mem_map_of_mem _ hgN)

theorem centralizer_projUnitriangular_le (p : ℕ) [Fact p.Prime] [CharP F p] :
    centralizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) ≤ projUnitriangular 3 F := by
  intro y hy
  have hyN : y ∈ normalizer (projUnitriangular 3 F : Set (projectiveSL 3 F)) :=
    centralizer_le_normalizer _ hy
  rw [normalizer_projUnitriangular (K := F) (n := 3) p] at hyN
  obtain ⟨M, hM, rfl⟩ := hyN
  have hMT : ∀ i j : Fin 3, (i : ℕ) + 1 = (j : ℕ) →
      (M : Matrix (Fin 3) (Fin 3) F) * single i j (1 : F) =
        single i j (1 : F) * (M : Matrix (Fin 3) (Fin 3) F) := by
    intro i j hij
    have hlt : i < j := by
      rw [Fin.lt_def]
      omega
    have hT := QuasithinUnique.K1.transvection_mem_unitriangular hlt (1 : F)
    have h1 := mem_centralizer_iff.mp hy
      (proj 3 F (SpecialLinearGroup.transvection hlt.ne (1 : F))) (mem_map_of_mem _ hT)
    have h2 : proj 3 F (M * SpecialLinearGroup.transvection hlt.ne (1 : F) * M⁻¹) =
        proj 3 F (SpecialLinearGroup.transvection hlt.ne (1 : F)) := by
      rw [map_mul, map_mul, map_inv, ← h1]
      group
    have h3 := proj_injOn_unitriangular 3 (conj_mem_unitriangular hM hT) hT h2
    have h4 : M * SpecialLinearGroup.transvection hlt.ne (1 : F) =
        SpecialLinearGroup.transvection hlt.ne (1 : F) * M := by
      calc M * SpecialLinearGroup.transvection hlt.ne (1 : F)
          = (M * SpecialLinearGroup.transvection hlt.ne (1 : F) * M⁻¹) * M := by group
        _ = SpecialLinearGroup.transvection hlt.ne (1 : F) * M := by rw [h3]
    have h5 : (M : Matrix (Fin 3) (Fin 3) F) * (1 + single i j (1 : F)) =
        (1 + single i j (1 : F)) * (M : Matrix (Fin 3) (Fin 3) F) :=
      congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F)) h4
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul] at h5
    exact add_left_cancel h5
  obtain ⟨a, b, hab⟩ := QuasithinUnique.K1.eq_smul_one_add_single_of_commute (n := 3)
    (by norm_num) (M : Matrix (Fin 3) (Fin 3) F) hMT
  have hdiag : ∀ i : Fin 3, (M : Matrix (Fin 3) (Fin 3) F) i i = a := by
    intro i
    rw [hab]
    fin_cases i <;> simp
  have hdet : a ^ 3 = 1 := by
    have h := M.2
    rw [det_of_isUpperTriangular (mem_upperTriangular_iff_isUpperTriangular.mp hM)] at h
    simpa [Fin.prod_univ_three, hdiag, pow_succ, mul_assoc] using h
  have ha : a ≠ 0 := by
    rintro rfl
    simp at hdet
  let u : Fˣ := Units.mk0 a ha
  have hu3 : u ^ 3 = 1 := Units.ext (by simpa [u] using hdet)
  have hlt : (0 : Fin 3) < 2 := by decide
  have hmat : (M : Matrix (Fin 3) (Fin 3) F) =
      scalar (Fin 3) (a : F) * (1 + single (0 : Fin 3) (2 : Fin 3) (b / a)) := by
    rw [hab]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, single_apply, scalar_apply]
    field_simp
  have hfac : M = scalarElement u hu3 * SpecialLinearGroup.transvection hlt.ne (b / a) :=
    Subtype.ext hmat
  rw [hfac, map_mul, proj_eq_one_iff.mpr (scalarElement_mem_scalars u hu3), one_mul]
  exact mem_map_of_mem _ (QuasithinUnique.K1.transvection_mem_unitriangular hlt (b / a))

theorem centralizer_map_conj_projUnitriangular_le (p : ℕ) [Fact p.Prime] [CharP F p] :
    centralizer (((projUnitriangular 3 F).map
        (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) :
          Subgroup (MulAut (projectiveSL 3 F))) : Set (MulAut (projectiveSL 3 F))) ≤
      (projUnitriangular 3 F).map
        (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) := by
  intro α hα
  have hinj : Function.Injective
      (MulAut.conj : projectiveSL 3 F →* MulAut (projectiveSL 3 F)) :=
    CFSG.RankThree.RegularUnipotent.conj_injective_projectiveSL (by norm_num)
  have hfix : ∀ x ∈ projUnitriangular 3 F, α x = x := by
    intro x hx
    have h1 : MulAut.conj x * α = α * MulAut.conj x :=
      mem_centralizer_iff.mp hα _ (mem_map_of_mem _ hx)
    have h2 : MulAut.conj (α x) = α * MulAut.conj x * α⁻¹ := by
      ext y
      simp [MulAut.conj_apply]
    apply hinj
    rw [h2, ← h1, mul_inv_cancel_right]
  obtain ⟨g, rfl⟩ := ASVolI.burnsideF411a_inner_of_fix_projUnitriangular p α hfix
  refine mem_map_of_mem _ (centralizer_projUnitriangular_le p (mem_centralizer_iff.mpr ?_))
  intro x hx
  apply hinj
  rw [map_mul, map_mul]
  exact mem_centralizer_iff.mp hα _ (mem_map_of_mem _ hx)

theorem card_le_four_of_isElemAbelian_projectiveSL (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2)
    {E : Subgroup (projectiveSL 3 F)} (hE : IsElemAbelian 2 E) : Nat.card E ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff F p 2).mp h'))
  have hZ : ¬ 2 ∣ Nat.card (scalars 3 F) := by
    rw [card_scalars_eq_gcd F (by norm_num : 1 ≤ 3)]
    intro h
    have := Nat.dvd_trans h (Nat.gcd_dvd_left 3 (Nat.card F - 1))
    omega
  have hr : CFSG.Open.pRank 2 (⊤ : Subgroup (projectiveSL 3 F)) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (G := SpecialLinearGroup (Fin 3) F) (scalars 3 F) hZ]
    exact CFSG.GH74.GLS.Stage2.Signalizer.Odd87.pRank_two_sl3_le_two h2
  obtain ⟨k, hk, hkr⟩ := CFSG.GH74.GLS.Stage2.Signalizer.Odd87.card_le_of_pRank hE
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (hkr.trans hr)
    _ = 4 := by norm_num

theorem eq_bot_of_inf_centralizer_theta_eq_bot (p : ℕ) [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2)
    {E : Subgroup (projectiveSL 3 F)} (hE : IsElemAbelian 2 E)
    (hUE : projUnitriangular 3 F ≤ normalizer (E : Set (projectiveSL 3 F)))
    (hEz : E ⊓ centralizer ({theta (⟨0, 0, 1⟩ : Heis F)} : Set (projectiveSL 3 F)) = ⊥) :
    E = ⊥ := by
  have hp : p.Prime := Fact.out
  by_contra hne
  have hN : ∀ y : Heis F, theta y ∈ normalizer (E : Set (projectiveSL 3 F)) :=
    fun y => hUE (mem_map_of_mem _ (heisSL_mem_unitriangular y))
  have hcomm : ∀ y : Heis F, Commute (theta y) (theta (⟨0, 0, 1⟩ : Heis F)) := fun y =>
    Commute.map (mem_center_iff.mp
      (Heis.mem_center.mpr ⟨rfl, rfl⟩ : (⟨0, 0, 1⟩ : Heis F) ∈ center (Heis F)) y :
        Commute y (⟨0, 0, 1⟩ : Heis F)) theta
  have hpow : ∀ y : Heis F, theta y ^ p = 1 := fun y => by
    rw [← map_pow, Heis.pow_prime_eq_one hp hp2, map_one]
  have hwb : theta (⟨1, 0, 0⟩ : Heis F) * theta ⟨0, 1, 0⟩ * (theta ⟨1, 0, 0⟩)⁻¹ =
      theta ⟨0, 1, 0⟩ * theta ⟨0, 0, 1⟩ := by
    have h : (⟨1, 0, 0⟩ : Heis F) * ⟨0, 1, 0⟩ * (⟨1, 0, 0⟩ : Heis F)⁻¹ =
        ⟨0, 1, 0⟩ * ⟨0, 0, 1⟩ := by
      ext <;> simp
    simpa only [map_mul, map_inv] using congrArg theta h
  obtain ⟨c, hc⟩ : ∃ c : ℕ, Nat.card E = c ^ p :=
    ⟨_, CFSG.GroupTheory.PlaneAction.card_eq_card_inf_centralizer_pow hE hp hp2 (hN ⟨0, 1, 0⟩)
      (hN ⟨0, 0, 1⟩) (hN ⟨1, 0, 0⟩) (hcomm _) (hpow _) (hpow _) hwb (hcomm _) hEz⟩
  have hE0 : 0 < Nat.card E := Nat.card_pos
  have hE1 : Nat.card E ≠ 1 := fun h => hne (Subgroup.eq_bot_of_card_eq E h)
  have hc2 : 2 ≤ c := by
    rcases Nat.lt_or_ge c 2 with h | h
    · interval_cases c
      · rw [zero_pow hp.ne_zero] at hc
        omega
      · rw [one_pow] at hc
        exact absurd hc hE1
    · exact h
  have h8 : 2 ^ 3 ≤ Nat.card E := by
    rw [hc]
    calc 2 ^ 3 ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by have := hp.two_le; omega)
      _ ≤ c ^ p := Nat.pow_le_pow_left hc2 p
  have h4 := card_le_four_of_isElemAbelian_projectiveSL p hp2 hE
  omega

theorem mulAut_eq_bot_of_le_normalizer_projUnitriangular (p : ℕ) [Fact p.Prime] [CharP F p]
    (hp2 : p ≠ 2) (V : Subgroup (MulAut (projectiveSL 3 F))) (hV : IsPGroup 2 V)
    (hUV : ∀ u ∈ projUnitriangular 3 F,
      MulAut.conj u ∈ normalizer (V : Set (MulAut (projectiveSL 3 F)))) : V = ⊥ := by
  have hp : p.Prime := Fact.out
  have hZ : center (projectiveSL 3 F) = ⊥ :=
    CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot (by norm_num)
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := F) p (n := 3) (by norm_num)
  have hUp : IsPGroup p (projUnitriangular 3 F) := by
    rw [← hS]
    exact S.isPGroup'
  have hzU : theta (⟨0, 0, 1⟩ : Heis F) ∈ projUnitriangular 3 F :=
    mem_map_of_mem _ (heisSL_mem_unitriangular _)
  have hUz : projUnitriangular 3 F ≤
      centralizer ({theta (⟨0, 0, 1⟩ : Heis F)} : Set (projectiveSL 3 F)) := by
    intro u hu
    obtain ⟨y, rfl⟩ := exists_theta_of_mem_bar hu
    exact mem_centralizer_singleton_iff.mpr (Commute.map (mem_center_iff.mp
      (Heis.mem_center.mpr ⟨rfl, rfl⟩ : (⟨0, 0, 1⟩ : Heis F) ∈ center (Heis F)) y :
        Commute y (⟨0, 0, 1⟩ : Heis F)) theta)
  refine mulAut_eq_bot_of_central hZ Nat.prime_two hzU hUz ?_
    (fun E hE hUE hEz => eq_bot_of_inf_centralizer_theta_eq_bot p hp2 hE hUE hEz) V hV hUV
  exact mulAut_forall_eq_bot_of_selfCentralizing hZ hp Nat.prime_two hp2 hUp le_rfl
    (centralizer_theta_le_normalizer p hp2)
    (inf_le_right.trans (centralizer_map_conj_projUnitriangular_le p))

end LinThree

theorem kFactNineThreeNoTwoAt_linThree {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .A 2 q) :
    KFactNineThreeNoTwoAt p (.lie d) := by
  obtain ⟨q, rfl, -, hdq⟩ := hd
  obtain ⟨x, hv⟩ := d
  change x = _ at hdq
  subst hdq
  haveI : Fact q.p.Prime := ⟨hp⟩
  let e : TauCeti.ValidLieTypeIndex.Group ⟨.A 2 q, hv⟩ ≃*
      projectiveSL 3 (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 (GaloisField q.p q.exponent))
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := GaloisField q.p q.exponent) q.p (n := 3)
    (by norm_num)
  have hU : IsPGroup q.p (projUnitriangular 3 (GaloisField q.p q.exponent)) := by
    rw [← hS]
    exact S.isPGroup'
  exact kFactNineThreeNoTwoAt_of_model hp ⟨e.symm⟩ hU fun V hV hN =>
    mulAut_eq_bot_of_le_normalizer_projUnitriangular q.p hp2 V hV fun u hu => hN ⟨u, hu, rfl⟩

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
