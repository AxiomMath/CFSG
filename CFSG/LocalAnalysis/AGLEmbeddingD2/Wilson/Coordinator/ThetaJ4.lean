module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.ThetaAssembly
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PreprimitiveSolvable77
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.PrimeOrderNormalizes
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.ExistsCharOddCommRelIndex
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KCentralizer
public import CFSG.RankThree.PartTwo.Sec4.Item423Res3ProofJ4

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator

open CFSG.Sporadic.J4 CFSG.Quasithin.J4M2 CFSG.Quasithin.J4Loc CFSG.RankThree.LocalRank

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem prime_dvd_card_J4 {p : ℕ} (hp : p.Prime) (h : p ∣ 86775571046077562880) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37 ∨ p = 43 := by
  have e : (86775571046077562880 : ℕ) =
      2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 ^ 3 * 23 * 29 * 31 * 37 * 43 := by norm_num
  rw [e] at h
  have hq : ∀ q : ℕ, q.Prime → ∀ k, p ∣ q ^ k → p = q := fun q hq k hk =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow hk)
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h43
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h37
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h31
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h29
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h23
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h11
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h7
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h5
  rcases (Nat.Prime.dvd_mul hp).1 h with h2 | h3
  · exact Or.inl (hq 2 Nat.prime_two 21 h2)
  · exact Or.inr (Or.inl (hq 3 Nat.prime_three 3 h3))
  · exact Or.inr (Or.inr (Or.inl (hq 5 (by norm_num) 1 (by simpa using h5))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) 1 (by simpa using h7)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 11 (by norm_num) 3 h11)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 23 (by norm_num) 1 (by simpa using h23)))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hq 29 (by norm_num) 1 (by simpa using h29))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hq 31 (by norm_num) 1 (by simpa using h31)))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hq 37 (by norm_num) 1 (by simpa using h37))))))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hq 43 (by norm_num) 1 (by simpa using h43))))))))))

theorem isSolvable_of_mulEquiv' {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hG : Group.IsSolvable G) : Group.IsSolvable H :=
  Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

section Instance

theorem hP_of_rho (hF : J4Facts)
    (hprim : MulAction.IsPreprimitive ↥((L0.subgroupOf M2).map (rho hF)) (Fin 77))
    (hρ : 4620 < Nat.card ((L0.subgroupOf M2).map (rho hF)))
    (S : Subgroup J) (hSL : S ≤ L0) (hSn : ∀ l ∈ L0, ∀ s ∈ S, l * s * l⁻¹ ∈ S)
    (hS : Group.IsSolvable S) : S ≤ Kgrp := by
  set G1 := (L0.subgroupOf M2).map (rho hF) with hG1
  set S0 := S.subgroupOf M2 with hS0
  set S1 := S0.map (rho hF) with hS1
  have hSM : S ≤ M2 := hSL.trans L0_le_M2
  have hS1G1 : S1 ≤ G1 := Subgroup.map_mono (Subgroup.comap_mono hSL)
  set S2 : Subgroup G1 := S1.subgroupOf G1 with hS2
  have hS2n : S2.Normal := by
    constructor
    rintro ⟨x, hx⟩ hxS2 ⟨g, hg⟩
    obtain ⟨s, hs, rfl⟩ := hxS2
    obtain ⟨l, hl, rfl⟩ := hg
    show rho hF l * rho hF s * (rho hF l)⁻¹ ∈ S1
    refine ⟨l * s * l⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    exact hSn l.1 hl s.1 hs
  have hS0s : Group.IsSolvable S0 :=
    @isSolvable_of_mulEquiv' S S0 inferInstance inferInstance
      (Subgroup.subgroupOfEquivOfLe hSM).symm hS
  have hS1s : Group.IsSolvable S1 :=
    @Group.isSolvable_of_surjective S0 S1 inferInstance inferInstance _
      ((rho hF).subgroupMap_surjective S0) hS0s
  have hS2s : Group.IsSolvable S2 :=
    @isSolvable_of_mulEquiv' S1 S2 inferInstance inferInstance
      (Subgroup.subgroupOfEquivOfLe hS1G1).symm hS1s
  have hbot : S2 = ⊥ := @Proving.eq_bot_of_normal_solvable_77 G1 hprim S2 hS2n hS2s hρ
  intro s hs
  have hsM : s ∈ M2 := hSM hs
  rw [mem_Kgrp_iff_rho hF s hsM]
  have hmem : (⟨rho hF ⟨s, hsM⟩, hS1G1 ⟨⟨s, hsM⟩, hs, rfl⟩⟩ : G1) ∈ S2 := ⟨⟨s, hsM⟩, hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

end Instance

section Final

theorem theta_cE_central (hF : J4Facts)
    (hK : ∀ k ∈ Kgrp, k * cE = cE * k → ∃ e : Bool, ∃ i < 3, k = (if e then z0 else 1) * cE ^ i)
    (hprim : MulAction.IsPreprimitive ↥((L0.subgroupOf M2).map (rho hF)) (Fin 77))
    (hρ : 4620 < Nat.card ((L0.subgroupOf M2).map (rho hF)))
    (h7 : z0 ∈ Subgroup.closure {g | g ∈ L0 ∧ orderOf g = 7})
    (h11 : z0 ∈ Subgroup.closure {g | g ∈ L0 ∧ orderOf g = 11})
    (H3 : ∀ (N : Subgroup J) (t : J), t ^ 2 = 1 → t ≠ 1 → (∀ n ∈ N, t * n * t⁻¹ ∈ N) →
      (∀ n ∈ N, t * n = n * t → n = 1 ∨ n = t) →
      ∃ A : Subgroup J, A ≤ N ∧ (∀ g : J, (∀ n ∈ N, g * n * g⁻¹ ∈ N) → ∀ a ∈ A, g * a * g⁻¹ ∈ A) ∧
        Odd (Nat.card A) ∧ (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧ A.relIndex N ≤ 2) :
    aschbacherSolvableCore 3 (Subgroup.centralizer ({cE} : Set J)) ≤
      Subgroup.center (Subgroup.centralizer ({cE} : Set J)) := by
  have hcard : Nat.card J = 86775571046077562880 := card_J hF
  refine theta_central_core (z0_mul_self hF.mat) (z0_ne_one hF.mat) (orderOf_cE hF.mat)
    (Subgroup.mem_centralizer_singleton_iff.1 (cE_mem_M2 hF.mat)) Kgrp
    hK (hP_of_rho hF hprim hρ) ?_ ?_ ?_ h7 h11 H3 ?_
  · intro p hp hpG
    rw [hcard] at hpG
    exact prime_dvd_card_J4 hp hpG
  · intro p hp
    rw [hcard]
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
  · rw [hcard]; norm_num
  · intro P w q hq hw hwP hcop
    have : Fact q.Prime := ⟨hq⟩
    exact Proving.commute_of_orderOf_prime_normalizes P w q hw hwP hcop

theorem theta_J_of (hθ : aschbacherSolvableCore 3 (Subgroup.centralizer ({cE} : Set J)) ≤
      Subgroup.center (Subgroup.centralizer ({cE} : Set J)))
    (hA : ∀ b : J, b ^ 3 = 1 → b ≠ 1 → ∃ g : J, g * b * g⁻¹ = cE)
    (y : J) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) :
    aschbacherSolvableCore 3 (Subgroup.centralizer ({y} : Set J)) ≤
      Subgroup.center (Subgroup.centralizer ({y} : Set J)) := by
  obtain ⟨g, hg⟩ := hA y hy3 hy1
  rw [@Proving.aschbacherSolvableCore_three_centralizer_iff J J inferInstance inferInstance _
    (MulAut.conj g) y]
  have key : ∀ x : J, x = cE → aschbacherSolvableCore 3 (Subgroup.centralizer ({x} : Set J)) ≤
      Subgroup.center (Subgroup.centralizer ({x} : Set J)) := by
    rintro x rfl
    exact hθ
  exact key _ (by rw [MulAut.conj_apply]; exact hg)

theorem k423J4ThetaCentral_of_J
    (hJ : ∀ y : J, y ^ 3 = 1 → y ≠ 1 →
      aschbacherSolvableCore 3 (Subgroup.centralizer ({y} : Set J)) ≤
        Subgroup.center (Subgroup.centralizer ({y} : Set J))) :
    CFSG.RankThree.PartTwo.Sec4.K423J4ThetaCentral := by
  intro X _ _ ⟨φ⟩ b hb3 hb1
  have e : X ≃* J := φ.trans (seedEquiv j4Facts.mat)
  rw [@Proving.aschbacherSolvableCore_three_centralizer_iff X J _ inferInstance _ e b]
  have he3 : e b ^ 3 = 1 := by rw [← map_pow, hb3, map_one]
  have he1 : e b ≠ 1 := fun h => hb1 (e.injective (by rw [h, map_one]))
  exact hJ (e b) he3 he1

theorem k423J4ThetaCentral :
    CFSG.RankThree.PartTwo.Sec4.K423J4ThetaCentral := by
  have hθ := theta_cE_central j4Facts
    (MaximalityAmbient.KCheck.Kgrp_centralizer_cE j4Facts.mat)
    (MaximalityAmbient.L0Prim.L0_rho_isPreprimitive j4Facts)
    (MaximalityAmbient.L0Prim.four_thousand_six_hundred_twenty_lt_card_L0_rho j4Facts)
    NormalizerAction.z0_mem_closure_orderSeven NormalizerAction.z0_mem_closure_orderEleven
    (fun N t ht2 ht1 htN hC =>
      @Proving.exists_char_odd_comm_relIndex_le_two J inferInstance N inferInstance t ht2 ht1 htN hC)
  exact k423J4ThetaCentral_of_J (theta_J_of hθ NormalizerAction.exists_conj_cE_of_orderThree)

end Final

end CFSG.AGLEmbeddingD2.Wilson.Coordinator
