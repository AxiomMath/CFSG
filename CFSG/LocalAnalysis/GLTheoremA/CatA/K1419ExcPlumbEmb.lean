module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcPlumbBasic
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcLang

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.CaseThreeNs
open CFSG.HardMathSupport.Dickson.Sec6
open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple
  (perfectInLayer_of_langSetup_of_prime)
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Component


theorem l3u3Plumb_exists_component {S : Type} [Group S] [Finite S] {β : MulAut S}
    (hβ : PerfectInLayer β) {I : Subgroup S} (hI : GLAPComponent 3 (fixSubgroup β) I)
    (hT : L3U3 (PQuot 3 I)) :
    IsComponentOf I (fixSubgroup β) ∧ L3U3 (↥I ⧸ Subgroup.center ↥I) ∧
      ∀ z ∈ Subgroup.center ↥I, z ^ 3 = 1 → z = 1 := by
  have hle : I ≤ GLALayer (fixSubgroup β) := hβ I hI.1 (glaPComponent_perfect hI)
  obtain ⟨hcomp, -⟩ := glaPComponent_isComponent_of_le_layer hI hle
  have hq : CFSG.IsQuasisimple ↥I := Up34Chev2.isQuasisimple_of_open_c2 hcomp.2.2
  have hbq : CFSG.Open.IsQuasisimple (PQuot 3 I) :=
    isQuasisimple_barOf_of_glaPComponent Nat.prime_three hI
  have hZ : Subgroup.center (PQuot 3 I) = ⊥ := l3u3Plumb_center_eq_bot hT hbq
  set N : Subgroup ↥I := GLAPPrimeCore 3 ↥I with hN
  have hNn : N.Normal := GLAPPrimeCore.normal 3 ↥I
  have hNZ : N ≤ Subgroup.center ↥I := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNn with h | h
    · exfalso
      have hsub : Subsingleton (PQuot 3 I) := by
        refine ⟨fun a b => ?_⟩
        induction a using QuotientGroup.induction_on with
        | H a =>
          induction b using QuotientGroup.induction_on with
          | H b =>
            rw [QuotientGroup.eq]
            change a⁻¹ * b ∈ GLAPPrimeCore 3 ↥I
            rw [← hN, h]
            exact Subgroup.mem_top _
      have hs2 : Subsingleton (PQuot 3 I ⧸ Subgroup.center (PQuot 3 I)) :=
        (QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 I))).subsingleton
      exact (not_nontrivial_iff_subsingleton.2 hs2) hbq.2.toNontrivial
    · exact h
  have hZN : Subgroup.center ↥I ≤ N := by
    intro z hz
    have hz' : (QuotientGroup.mk z : PQuot 3 I) ∈ Subgroup.center (PQuot 3 I) := by
      rw [Subgroup.mem_center_iff]
      intro g
      induction g using QuotientGroup.induction_on with
      | H g =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subgroup.mem_center_iff.1 hz g
    rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hz'
    exact hz'
  have hNeq : N = Subgroup.center ↥I := le_antisymm hNZ hZN
  refine ⟨hcomp, l3u3Plumb_of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hNeq) hT, ?_⟩
  intro z hz hz3
  have hzN : z ∈ N := hZN hz
  have hN3 : ¬ 3 ∣ Nat.card N :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_card_gLAPPrimeCore_aux 3 ↥I)
  by_contra hz1
  have hord : orderOf (⟨z, hzN⟩ : N) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hz3 hz1
  have := orderOf_dvd_natCard (⟨z, hzN⟩ : N)
  rw [hord] at this
  exact hN3 this

theorem noL3U3Layer_of_embedding {C G : Type} [Group C] [Group G] [Finite C] (ι : C →* G)
    (hι : Function.Injective ι) (β : MulAut C) (y : G) (hy : ∀ s, ι (β s) = y * ι s * y⁻¹)
    (hP : PerfectInLayer β)
    (hno : ∀ K : Subgroup G, IsComponentOf K (ι.range ⊓ Subgroup.centralizer {y}) →
      L3U3 (↥K ⧸ Subgroup.center ↥K) →
        ∃ z : G, z ∈ K ∧ (∀ g ∈ K, g * z = z * g) ∧ z ^ 3 = 1 ∧ z ≠ 1) :
    NoL3U3Layer β := by
  intro I hI hT
  obtain ⟨hcomp, hIT, hIZ⟩ := l3u3Plumb_exists_component hP hI hT
  have hfix := Up34Exc.map_fixSubgroup_eq_of_conj ι hι β y hy
  have hK : IsComponentOf (I.map ι) (ι.range ⊓ Subgroup.centralizer {y}) := by
    rw [← hfix]
    exact Up34Exc.isComponentOf_map_inj hcomp ι hι
  let e : ↥I ≃* ↥(I.map ι) := Subgroup.equivMapOfInjective I ι hι
  have hIq : CFSG.Open.IsQuasisimple ↥I := hcomp.2.2
  have hperf : Group.IsPerfect ↥I := ⟨hIq.1⟩
  have hker : (e : ↥I →* ↥(I.map ι)).ker ≤ Subgroup.center ↥I := by
    rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]
    exact bot_le
  obtain ⟨eq⟩ := CFSG.Goldschmidt.G37.nonempty_centerQuotientEquiv hperf (e : ↥I →* ↥(I.map ι))
    e.surjective hker
  obtain ⟨z, hzK, hzc, hz3, hz1⟩ := hno (I.map ι) hK (l3u3Plumb_of_mulEquiv eq hIT)
  obtain ⟨c, hcI, rfl⟩ := Subgroup.mem_map.1 hzK
  have hcent : (⟨c, hcI⟩ : ↥I) ∈ Subgroup.center ↥I := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply hι
    have := hzc (ι g) (Subgroup.mem_map_of_mem ι g.2)
    simpa [map_mul] using this
  have h3 : (⟨c, hcI⟩ : ↥I) ^ 3 = 1 := by
    apply Subtype.ext
    apply hι
    simpa [map_pow] using hz3
  have h1 : (⟨c, hcI⟩ : ↥I) = 1 := hIZ _ hcent h3
  apply hz1
  have : c = 1 := congrArg Subtype.val h1
  rw [this, map_one]

theorem noL3U3Layer_of_langSetup {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}
    (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ} {p : ℕ} (hp : p.Prime) {C : Type} [Group C]
    [Finite C] (ι : C →* ModGL τ L) (hι : Function.Injective ι) (hrange : ι.range = S.Γ)
    (β : MulAut C)
    (hβ : ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹)
    (hT : rootDiagUnit τ a ∈ S.D.torus) (hap : ∀ i, a i ^ p = 1) (h1 : rootDiagUnit τ a ≠ 1)
    (hTame : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) ∨
        Group.IsSolvable (rationalComponent S.ρ S.Γ (rootCharHom a) i))
    (hrat : ∀ i : KernelComponent (rootCharHom a),
      CFSG.IsQuasisimple (rationalComponent S.ρ S.Γ (rootCharHom a) i) →
        L3U3 (↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ⧸
          Subgroup.center ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i)) →
        ∃ z : ModGL τ L, z ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i ∧
          (∀ g ∈ rationalComponent S.ρ S.Γ (rootCharHom a) i, g * z = z * g) ∧
          z ^ 3 = 1 ∧ z ≠ 1) :
    NoL3U3Layer β := by
  have hP : PerfectInLayer β :=
    perfectInLayer_of_langSetup_of_prime S hp ι hι hrange β hβ hT hap h1 hTame
  haveI : Finite S.Γ := by
    rw [← hrange]
    exact Finite.of_surjective _ ι.rangeRestrict_surjective
  refine noL3U3Layer_of_embedding ι hι β (rootDiagUnit τ a) hβ hP fun K hK hKT => ?_
  rw [hrange] at hK
  obtain ⟨i, hi, rfl⟩ := Up34Exc.exists_rationalComponent_eq_of_isComponentOf S hp hT hap hTame
    inferInstance hK
  exact hrat i hi hKT

end Component

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
