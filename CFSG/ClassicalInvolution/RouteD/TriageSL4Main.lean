module

public import CFSG.ClassicalInvolution.RouteD.TriageSL4Conn
public import CFSG.ClassicalInvolution.RouteD.TriageSL4Torus
public import CFSG.ClassicalInvolution.RouteD.TwinSL4BridgeMain
public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6AdaptGraph

public section

namespace CFSG.ClassicalInvolution.Generic.CoreAssembly

open scoped MatrixGroups
open CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair blockSL2)

variable {p f : ℕ} [Fact p.Prime]

theorem twinSL4Action_of_torus (h4 : ∃ a : (GaloisField p f)ˣ, a ^ 4 ≠ 1) : TwinSL4Action p f := by
  intro G _ _ _ hnab K z S hshape β hβ t ht hKβ j hjΩ hjK hjβ hj12 hp01 hp02 x₀ hx₀
  classical
  have hΩ : InClass p f (conjClass K) := S.inClass
  have hex := S.exact
  have hsingle : ∀ L ∈ conjClass K, ∃ g : G, L = conjSub g K := single_class K
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
  obtain ⟨T, hTz, hTimg⟩ := c.exists_twin
  have hTK : T ≠ K := c.twin_ne hTz hTimg.le
  have hTΩ : T ∈ conjClass K := hTz.1
  have hKT : Commutes K T := c.commutes_K_of_ne hTz hTK
  have hTj : ∀ a, j a ≠ T := fun a h => hjQ a (by rw [h]; exact hTimg.le)
  have hTcomm : ∀ N ∈ centralizingMembers (conjClass K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => c.commutes_T_of_ne hTz hTimg.le hN hNT
  have hzt : Commute z t :=
    CFSG.ClassicalInvolution.RouteD.Gaps.standardPair_involutions_commute h2 hW S.cls.mem ht.mem
      S.cls.orderOf_eq_two ht.orderOf_eq_two
  have ht1 : t * z * t⁻¹ = z := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm.eq
  have ht2 : t * t = 1 := mul_self_of_isClassicalMember ht
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hj1t : conjSub t (j 1) = j 1 := conjSub_eq_of_mem_of_commutes ht.mem (hjβ 1 (by decide))
  have hj2t : conjSub t (j 2) = j 2 := conjSub_eq_of_mem_of_commutes ht.mem (hjβ 2 (by decide))
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
  set σ := locAut hΩ.conjInvariant ht1 with hσdef
  have hσσ : ∀ a, σ (σ a) = a := locAut_locAut hΩ.conjInvariant ht1 ht2
  have hle1 : j 1 ≤ Subgroup.centralizer ({t} : Set G) :=
    NonClassical.le_centralizer_of_commutes (hjβ 1 (by decide)).symm ht.mem
  have hle2 : j 2 ≤ Subgroup.centralizer ({t} : Set G) :=
    NonClassical.le_centralizer_of_commutes (hjβ 2 (by decide)).symm ht.mem
  have hfixσ1 := (locAut_fixed_iff hΩ c.hP1 ht1 (hjz 1)).mp hle1
  have hfixσ2 := (locAut_fixed_iff hΩ c.hP1 ht1 (hjz 2)).mp hle2
  have hmemj0 : conjSub t (j 0) ∈ centralizingMembers (conjClass K) {z} := by
    have := centralizingMembers_conj hΩ.conjInvariant t z
    rw [ht1] at this
    rw [this]
    exact ⟨j 0, hjz 0, rfl⟩
  have hj0big : locImg (conjClass K) z (conjSub t (j 0)) ≤ c.d.ψ.range := by
    have hK' : conjSub t (j 0) ≠ K := fun h => hjKne 0 (conjSub_injective t (h.trans hKt.symm))
    have hQ' : ¬ locImg (conjClass K) z (conjSub t (j 0)) ≤ c.d.Q₁ := by
      intro hQ
      have hne' : j 1 ≠ conjSub t (j 0) := fun h =>
        hne01 (conjSub_injective t (h.symm.trans hj1t.symm))
      have hc := c.commutes_T_of_ne hmemj0 hQ (hjz 1) hne'
      have hc' : Commutes (conjSub t (j 0)) (conjSub t (j 1)) := by
        rw [hj1t]
        exact hc
      exact hnc01 ((commutes_conjSub_iff t).mp hc')
    obtain ⟨R, -, hR⟩ := c.exists_fund_of_ne hmemj0 hK' hQ'
    rw [hR]
    exact Subgroup.map_le_range _ _
  have hgenσ : ∀ k : Fin 3, ∀ u ∈ locImg (conjClass K) z (![j 1, j 0, j 2] k),
      σ u ∈ Θ.range := by
    intro k u hu
    rw [hrangeΘ]
    fin_cases k
    · rw [hfixσ1 u hu]
      exact hψj 1 hu
    · have : σ u ∈ locImg (conjClass K) z (conjSub t (j 0)) := by
        rw [← locAut_locImg hΩ.conjInvariant ht1 (j 0)]
        exact ⟨u, hu, rfl⟩
      exact hj0big this
    · rw [hfixσ2 u hu]
      exact hψj 2 hu
  have hstab : ∀ x, σ (Θ x) ∈ Θ.range := by
    have h1 : (Θ.range).map σ.toMonoidHom ≤ Θ.range := by
      rw [hrangeΘ', Subgroup.map_iSup]
      refine iSup_le fun k => ?_
      rintro _ ⟨u, hu, rfl⟩
      rw [← hrangeΘ']
      exact hgenσ k u hu
    intro x
    exact h1 ⟨Θ x, ⟨x, rfl⟩, rfl⟩
  have hfix₀ : ∀ A : SL(2, GaloisField p f), σ (Θ (blockSL2 (GaloisField p f) 3 0 A)) =
      Θ (blockSL2 (GaloisField p f) 3 0 A) := fun A => hfixσ1 _ (by
    rw [← hn0]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hfix₂ : ∀ A : SL(2, GaloisField p f), σ (Θ (blockSL2 (GaloisField p f) 3 2 A)) =
      Θ (blockSL2 (GaloisField p f) 3 2 A) := fun A => hfixσ2 _ (by
    rw [← hn2]
    exact ⟨_, ⟨A, rfl⟩, rfl⟩)
  have hcl : LinearAutClassification (GaloisField p f) (3 + 1) :=
    CFSG.ClassicalInvolution.ModelFacts.LinearAut.linearAutClassification S.odd S.five (by omega)
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
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
  rcases blocks_classification (by have := S.five; omega) hcl Θ hkerΘ σ hstab hfix₀ hfix₂ with
    ⟨μ, hμ⟩ | ⟨hinv, -⟩
  ·
    rcases blockEnt_eq_of_involution Θ hkerΘ σ hσσ μ hμ with rfl | rfl
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
  ·
    exfalso
    obtain ⟨a, ha⟩ := h4
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (Θ (sl4Pair a))
    have hHr : Θ (sl4Pair a) ∈ c.d.ψ.range := by
      have h : Θ (sl4Pair a) ∈ Θ.range := ⟨_, rfl⟩
      rw [hrangeΘ] at h
      exact h
    have hyH : locMk (conjClass K) z y = Θ (sl4Pair a) := hy
    have hcenQ : ∀ {L : Subgroup G} (hL : L ∈ centralizingMembers (conjClass K) {z})
        (Q : Subgroup (locQuot (conjClass K) z)), locImg (conjClass K) z L ≤ Q →
        Commutes Q c.d.ψ.range → L ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
      intro L hL Q hLQ hQ
      refine (le_centralizer_iff_locImg hΩ c.hP1 hL y).mpr fun u hu => ?_
      rw [Subgroup.mem_centralizer_singleton_iff, hyH]
      exact hQ u (hLQ hu) _ hHr
    have hyK : K ≤ Subgroup.centralizer ({(y : G)} : Set G) :=
      hcenQ c.hKz _ c.hQ₀ c.d.comm₀
    have hyT : T ≤ Subgroup.centralizer ({(y : G)} : Set G) :=
      hcenQ hTz _ hTimg.le c.d.comm₁
    have hyx : (y : G) * x₀ * (y : G)⁻¹ = x₀ := by
      have hcom : Commute (⟨x₀, hx₀Y⟩ : ↥(locLayer (conjClass K) z)) y := by
        refine CFSG.ClassicalInvolution.RouteD.NonClassical.commute_of_involution_of_mk c.hP1
          (Subtype.ext (mul_self_of_isClassicalMember hx₀)) ?_
        show Commute (locMk (conjClass K) z ⟨x₀, hx₀Y⟩) (locMk (conjClass K) z y)
        rw [hw₀, hyH]
        show _ * _ = _ * _
        rw [← map_mul, ← map_mul, (sl4Pair_comm_negOne a).symm]
      have := congrArg Subtype.val hcom.eq
      rw [mul_inv_eq_iff_eq_mul]
      exact this.symm
    have hsqβ := conjSub_sq_normalizes S hshape hβ ht hKβ (hjΩ 1) (hjΩ 2) hTΩ (hjK 1) (hjK 2) hKT
      (hjβ 1 (by decide)) (hjβ 2 (by decide)) hj12 (hTcomm (j 1) (hjz 1) (hTj 1))
      (fun h => hTj 2 h.symm) hx₀ hyK hyT hyx
    have htc : ((y : G) * (y : G)) * t * ((y : G) * (y : G))⁻¹ = t := by
      have hcl' := ht.conj ((y : G) * (y : G))
      rw [hsqβ] at hcl'
      exact unique_involution_of_isClassicalMember h2 (hex β hβ) hcl' ht
    set y₂ : ↥(locLayer (conjClass K) z) := y * y with hy₂
    have hlayer : layerAut hΩ.conjInvariant ht1 y₂ = y₂ := by
      apply Subtype.ext
      show t * ((y : G) * (y : G)) * t⁻¹ = (y : G) * (y : G)
      rw [mul_inv_eq_iff_eq_mul]
      exact (mul_inv_eq_iff_eq_mul.mp htc).symm
    have hσH2 : σ (Θ (sl4Pair a) * Θ (sl4Pair a)) = Θ (sl4Pair a) * Θ (sl4Pair a) := by
      have hmk : locMk (conjClass K) z y₂ = Θ (sl4Pair a) * Θ (sl4Pair a) := by
        rw [hy₂, map_mul, hyH]
      rw [← hmk]
      show locAut hΩ.conjInvariant ht1 (locMk (conjClass K) z y₂) = _
      rw [locAut_mk, hlayer]
    have hsqP : Θ (sl4Pair a) * Θ (sl4Pair a) = Θ (sl4Pair (a * a)) := by
      rw [← map_mul, sl4Pair_mul]
    have hσP := hinv (a * a)
    rw [← hsqP, hσH2] at hσP
    have hker1 : sl4Torus (a * a)⁻¹ ∈ Θ.ker := by
      rw [MonoidHom.mem_ker]
      have h1 := hσP
      rw [hsqP] at h1
      have h2 : Θ (sl4Torus (a * a)⁻¹) * Θ (sl4Pair (a * a)) = 1 * Θ (sl4Pair (a * a)) := by
        rw [one_mul]
        exact h1.symm
      exact mul_right_cancel h2
    have h' : (a * a) ^ 2 = 1 := by
      have := sq_eq_one_of_sl4Torus_center _ (hkerΘ hker1)
      rwa [inv_pow, inv_eq_one] at this
    apply ha
    calc a ^ 4 = (a ^ 2) ^ 2 := by rw [← pow_mul]
      _ = (a * a) ^ 2 := by rw [sq a]
      _ = 1 := h'

theorem exists_unit_pow_four_ne_one (hq : 5 ≤ p ^ f) (h5 : p ^ f ≠ 5) :
    ∃ a : (GaloisField p f)ˣ, a ^ 4 ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hf : f ≠ 0 := by
    rintro rfl
    simp at hq
  have hcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
  have htop : rootsOfUnity 4 (GaloisField p f) = ⊤ := by
    rw [eq_top_iff]
    intro a _
    exact (mem_rootsOfUnity 4 a).mpr (hcon a)
  have h4 : Nat.card (rootsOfUnity 4 (GaloisField p f)) ≤ 4 := card_rootsOfUnity _ _
  rw [htop, Subgroup.card_top, Nat.card_units, hcard] at h4
  omega

theorem twinSL4Action_of_ne_five (h5 : p ^ f ≠ 5) : TwinSL4Action p f := by
  intro G _ _ _ hnab K z S
  exact twinSL4Action_of_torus (exists_unit_pow_four_ne_one S.five h5) G hnab K z S

end CFSG.ClassicalInvolution.Generic.CoreAssembly
