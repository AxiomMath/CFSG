module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Main
public import CFSG.ClassicalInvolution.RouteD.TriageSL4Sq

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open scoped MatrixGroups
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

variable {p f : ℕ} [Fact p.Prime]

theorem twinSL4Action_of_sqrt (hsq : ∃ i : (GaloisField p f)ˣ, i * i = -1) :
    TwinSL4Action p f := by
  intro G _ _ _ hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02 x₀ hx₀
  classical
  obtain ⟨i, hi⟩ := hsq
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hKΩ : K ∈ conjClass K := mem_conjClass_self K
  have hcen := center_eq_bot hnab
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f S.odd
  have hf : f ≠ 0 := by
    have := S.five
    rintro rfl
    simp at this
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [GaloisField.card p f hf]
    exact ((Fact.out : p.Prime).odd_of_ne_two S.odd).pow
  have hq4 : 4 ≤ p ^ f := by have := S.five; omega
  obtain ⟨c⟩ := TCtx.nonempty_A3 S.odd S.five hΩ hex hKΩ S.cls S.p1 hshape
  have hNC := not_commutes_of_twinSL4 hnab S hshape hβ ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02
  obtain ⟨W, hW⟩ := id hKβ
  have hne : ∀ {A B : Subgroup G}, A ∈ conjClass K → Commutes A B → A ≠ B := by
    intro A B hA hAB hAeq
    subst hAeq
    exact not_commutes_self_of_mem hΩ hA hAB
  have hjz : ∀ a, j a ∈ centralizingMembers (conjClass K) {z} := fun a =>
    mem_centralizingMembers_of_commutes (hjΩ a) S.cls.mem (hjK a).symm
  have hjKne : ∀ a, j a ≠ K := fun a h => hne hKΩ (hjK a) h.symm
  obtain ⟨W₀₁, hW₀₁⟩ := hp01
  obtain ⟨W₀₂, hW₀₂⟩ := hp02
  have hnc01 : ¬ Commutes (j 0) (j 1) := not_commutes_of_linearBlockStandardPair hW₀₁
  have hnc02 : ¬ Commutes (j 0) (j 2) := not_commutes_of_linearBlockStandardPair hW₀₂
  have hne01 : j 0 ≠ j 1 := ne_of_linearBlockStandardPair hW₀₁
  have hne02 : j 0 ≠ j 2 := ne_of_linearBlockStandardPair hW₀₂
  have hjQ : ∀ a : Fin 3, ¬ locImg (conjClass K) z (j a) ≤ c.d.Q₁ := by
    intro a
    fin_cases a
    · exact fun hQ => hnc01 (c.commutes_T_of_ne (hjz 0) hQ (hjz 1) hne01.symm)
    · exact fun hQ => hnc01 (c.commutes_T_of_ne (hjz 1) hQ (hjz 0) hne01).symm
    · exact fun hQ => hnc02 (c.commutes_T_of_ne (hjz 2) hQ (hjz 0) hne02).symm
  have hψj : ∀ a : Fin 3, locImg (conjClass K) z (j a) ≤ c.d.ψ.range := by
    intro a
    obtain ⟨R, -, hR⟩ := c.exists_fund_of_ne (hjz a) (hjKne a) (hjQ a)
    rw [hR]
    exact Subgroup.map_le_range _ _
  have hzt : Commute z t :=
    CFSG.ClassicalInvolution.RouteD.Gaps.standardPair_involutions_commute h2 hW S.cls.mem ht.mem
      S.cls.orderOf_eq_two ht.orderOf_eq_two
  have ht1 : t * z * t⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm.eq
  have ht2 : t * t = 1 := mul_self_of_isClassicalMember ht
  have hLz : ∀ k : Fin 3, ![j 1, j 0, j 2] k ∈ centralizingMembers (conjClass K) {z} := fun k => by
    fin_cases k <;> simp [hjz]
  obtain ⟨Θ, hkerΘ, hrangeΘ, hrangeΘ', hnodesΘ⟩ := exists_chart_of_chain hq4 hΩ hex c.d.ψ
    (L := ![j 1, j 0, j 2]) hLz
    (fun k => by
      fin_cases k
      exacts [hψj 1, hψj 0, hψj 2])
    (by simpa using hj12) ⟨_, CFSG.ClassicalInvolution.Generic.linearBlockStandardPair_symm hW₀₁⟩
    ⟨_, hW₀₂⟩
  have hn0 : Subgroup.map Θ (blockSL2 (GaloisField p f) 3 0).range =
      locImg (conjClass K) z (j 1) := hnodesΘ 0
  have hn1 : Subgroup.map Θ (blockSL2 (GaloisField p f) 3 1).range =
      locImg (conjClass K) z (j 0) := hnodesΘ 1
  have hn2 : Subgroup.map Θ (blockSL2 (GaloisField p f) 3 2).range =
      locImg (conjClass K) z (j 2) := hnodesΘ 2
  obtain ⟨s, hsβ, hss, hsz, hsK⟩ := exists_sqrt_of_standardPair h2 hW hi S.cls.mem ht.mem
    S.cls.orderOf_eq_two ht.orderOf_eq_two
  have hs1 : s * z * s⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hsz
  have hss1 : (s * s) * z * (s * s)⁻¹ = z := by
    rw [hss]
    exact ht1
  have hj1s : conjSub s (j 1) = j 1 := conjSub_eq_of_mem_of_commutes hsβ (hjβ 1 (by decide))
  have hle1 : j 1 ≤ Subgroup.centralizer ({s} : Set G) :=
    NonClassical.le_centralizer_of_commutes (hjβ 1 (by decide)).symm hsβ
  have hle2 : j 2 ≤ Subgroup.centralizer ({s} : Set G) :=
    NonClassical.le_centralizer_of_commutes (hjβ 2 (by decide)).symm hsβ
  set τ := locAut hΩ.conjInvariant hs1 with hτdef
  have hfixτ1 := (locAut_fixed_iff hΩ c.hP1 hs1 (hjz 1)).mp hle1
  have hfixτ2 := (locAut_fixed_iff hΩ c.hP1 hs1 (hjz 2)).mp hle2
  have hmemj0 : conjSub s (j 0) ∈ centralizingMembers (conjClass K) {z} := by
    have := centralizingMembers_conj hΩ.conjInvariant s z
    rw [hs1] at this
    rw [this]
    exact ⟨j 0, hjz 0, rfl⟩
  have hj0big : locImg (conjClass K) z (conjSub s (j 0)) ≤ c.d.ψ.range := by
    have hK' : conjSub s (j 0) ≠ K := fun h => hjKne 0 (conjSub_injective s (h.trans hsK.symm))
    have hQ' : ¬ locImg (conjClass K) z (conjSub s (j 0)) ≤ c.d.Q₁ := by
      intro hQ
      have hne' : j 1 ≠ conjSub s (j 0) := fun h =>
        hne01 (conjSub_injective s (h.symm.trans hj1s.symm))
      have hc := c.commutes_T_of_ne hmemj0 hQ (hjz 1) hne'
      have hc' : Commutes (conjSub s (j 0)) (conjSub s (j 1)) := by
        rw [hj1s]
        exact hc
      exact hnc01 ((commutes_conjSub_iff s).mp hc')
    obtain ⟨R, -, hR⟩ := c.exists_fund_of_ne hmemj0 hK' hQ'
    rw [hR]
    exact Subgroup.map_le_range _ _
  have hgenτ : ∀ k : Fin 3, ∀ u ∈ locImg (conjClass K) z (![j 1, j 0, j 2] k),
      τ u ∈ Θ.range := by
    intro k u hu
    rw [hrangeΘ]
    fin_cases k
    · rw [hfixτ1 u hu]
      exact hψj 1 hu
    · have : τ u ∈ locImg (conjClass K) z (conjSub s (j 0)) := by
        rw [← locAut_locImg hΩ.conjInvariant hs1 (j 0)]
        exact ⟨u, hu, rfl⟩
      exact hj0big this
    · rw [hfixτ2 u hu]
      exact hψj 2 hu
  have hstab : ∀ x, τ (Θ x) ∈ Θ.range := by
    have h1 : (Θ.range).map τ.toMonoidHom ≤ Θ.range := by
      rw [hrangeΘ', Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [← hrangeΘ']
      exact hgenτ k u hu
    intro x
    exact h1 ⟨Θ x, ⟨x, rfl⟩, rfl⟩
  have hfix₀ : ∀ A : SL(2, GaloisField p f), τ (Θ (blockSL2 (GaloisField p f) 3 0 A)) =
      Θ (blockSL2 (GaloisField p f) 3 0 A) := fun A => hfixτ1 _ (by
    rw [← hn0]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix₂ : ∀ A : SL(2, GaloisField p f), τ (Θ (blockSL2 (GaloisField p f) 3 2 A)) =
      Θ (blockSL2 (GaloisField p f) 3 2 A) := fun A => hfixτ2 _ (by
    rw [← hn2]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hcl : LinearAutClassification (GaloisField p f) (3 + 1) :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification S.odd S.five (by omega)
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  obtain ⟨ν, hν⟩ := blocks_sq_classification (by have := S.five; omega) hcl Θ hkerΘ τ hstab
    hfix₀ hfix₂
  set σ := locAut hΩ.conjInvariant ht1 with hσdef
  have hσσ : ∀ a, σ (σ a) = a := locAut_locAut hΩ.conjInvariant ht1 ht2
  have hστ : ∀ a, σ a = τ (τ a) := fun a => by
    rw [hσdef, locAut_congr hΩ.conjInvariant hss.symm ht1 hss1,
      locAut_mul hΩ.conjInvariant hs1 hs1 hss1]
  have hμ : ∀ x, σ (Θ x) = Θ (slConjugation (3 + 1) (GaloisField p f)
      (diagGL (blockEnt ν)) x) := fun x => by rw [hστ, hν]
  have hx₀z : x₀ * z * x₀⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hjK 1 z S.cls.mem x₀ hx₀.mem).symm
  have htx : (t * x₀) * z * (t * x₀)⁻¹ = z := by
    calc (t * x₀) * z * (t * x₀)⁻¹ = t * (x₀ * z * x₀⁻¹) * t⁻¹ := by group
      _ = z := by rw [hx₀z, ht1]
  have hx₀Y : x₀ ∈ locLayer (conjClass K) z := le_centralizingLayer (hjz 1) hx₀.mem
  have hw₀ : locMk (conjClass K) z ⟨x₀, hx₀Y⟩ = Θ (blockSL2 (GaloisField p f) 3 0 (-1)) := by
    have hu := ConnectedA2.isUniqueInvolution_locImg hex (hjz 1)
      (isUniqueInvolution_of_exact hodd (hex (j 1) (hjΩ 1)) hx₀)
    have hmem : Θ (blockSL2 (GaloisField p f) 3 0 (-1)) ∈
        locImg (conjClass K) z (j 1) := by
      rw [← hn0]
      exact ⟨_, ⟨-1, rfl⟩, rfl⟩
    have hsq' : Θ (blockSL2 (GaloisField p f) 3 0 (-1)) *
        Θ (blockSL2 (GaloisField p f) 3 0 (-1)) = 1 := by
      rw [← map_mul, ← map_mul, show (-1 : SL(2, GaloisField p f)) * -1 = 1 by simp, map_one,
        map_one]
    rcases hu.unique _ hmem hsq' with h | h
    · exfalso
      have hc := hkerΘ (MonoidHom.mem_ker.mpr h)
      obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
      have e0 := congrFun (congrFun hr 0) 0
      have e2 := congrFun (congrFun hr 2) 2
      rw [coe_blockSL2_negOne_zero] at e0 e2
      simp [Matrix.scalar_apply] at e0 e2
      apply h2
      linear_combination e0 - e2
    · exact h.symm
  rcases blockEnt_eq_of_involution Θ hkerΘ σ hσσ ν hμ with rfl | rfl
  ·
    exfalso
    have hle0 : j 0 ≤ Subgroup.centralizer ({t} : Set G) := by
      refine (locAut_fixed_iff hΩ c.hP1 ht1 (hjz 0)).mpr fun u hu => ?_
      rw [← hn1] at hu
      obtain ⟨_, ⟨A, rfl⟩, rfl⟩ := hu
      rw [hμ, slConjugation_blockEnt_one]
    rcases S.cp_at_member hcen hβ ht (L := j 0) ⟨hjΩ 0, hle0⟩ with h | h
    · exact hNC h
    · exact hnc01 (by rw [h]; exact hjβ 1 (by decide))
  ·
    refine (locAut_fixed_iff hΩ c.hP1 htx (hjz 0)).mpr fun u hu => ?_
    have hu' : u ∈ Θ.range := by
      rw [hrangeΘ']
      exact (le_iSup (fun k => locImg (conjClass K) z (![j 1, j 0, j 2] k)) 1) hu
    obtain ⟨x, rfl⟩ := hu'
    rw [locAut_mul hΩ.conjInvariant ht1 hx₀z htx,
      locAut_eq_conj hΩ.conjInvariant hx₀Y hx₀z, hw₀, ← map_inv, ← map_mul, ← map_mul]
    show σ (Θ _) = _
    rw [hμ, conj_negOne_block4]

theorem exists_sqrt_neg_one_of_eq_five (h5 : p ^ f = 5) :
    ∃ i : (GaloisField p f)ˣ, i * i = -1 := by
  have hf : f ≠ 0 := by
    rintro rfl
    simp at h5
  have hcard : Nat.card (GaloisField p f) = 5 := by
    rw [GaloisField.card p f hf]
    exact h5
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hsq : IsSquare (-1 : GaloisField p f) := by
    rw [FiniteField.isSquare_neg_one_iff, ← Nat.card_eq_fintype_card, hcard]
    norm_num
  obtain ⟨r, hr⟩ := hsq
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr.symm)⟩

theorem twinSL4Action_proved : TwinSL4Action p f := by
  by_cases h5 : p ^ f = 5
  · exact twinSL4Action_of_sqrt (exists_sqrt_neg_one_of_eq_five h5)
  · exact twinSL4Action_of_ne_five h5

end CFSG.ClassicalInvolution.Generic.CoreAssembly
