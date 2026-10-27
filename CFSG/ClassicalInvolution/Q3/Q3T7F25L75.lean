module

public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75
public import CFSG.ClassicalInvolution.Q3.Q3T7F25M1

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.T7F25
section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic

abbrev L6_7 : Prop := Q3.Q3CP.L67Gen

theorem l6_7_proved : L6_7 := Q3.Q3CP.l67Gen

namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

noncomputable def muGroupConjEquiv [Finite G] (hΩ : HypOmegaMod Ω) (g : G) (W : Subgroup G) :
    ↥(muGroup Ω W) ≃* ↥(muGroup Ω (conjSub g W)) :=
  (MulEquiv.subgroupMap (nquotConj g (conjSub_sup_OCW g W)) (muGroup Ω W)).trans
    (MulEquiv.subgroupCongr (by
      ext q
      constructor
      · rintro ⟨q₀, hq₀, rfl⟩
        obtain ⟨m, hm, rfl⟩ := mem_muGroup_iff.mp hq₀
        have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
        show nquotConj g (conjSub_sup_OCW g W) (piG W m) ∈ _
        rw [nquotConj_piG g W hmN]
        refine piG_mem_muGroup ?_
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← Asc77.conjSub_sup]
        exact conj_mem_conjSub hm
      · intro hq
        obtain ⟨m', hm', rfl⟩ := mem_muGroup_iff.mp hq
        rw [← conjSub_MGrp hΩ, ← conjSub_OCW, ← Asc77.conjSub_sup, mem_conjSub_iff] at hm'
        refine ⟨piG W (g⁻¹ * m' * g), piG_mem_muGroup hm', ?_⟩
        have hmN : g⁻¹ * m' * g ∈ Subgroup.normalizer (W : Set G) :=
          MGrp_sup_le_normalizer Ω W hm'
        show nquotConj g (conjSub_sup_OCW g W) (piG W (g⁻¹ * m' * g)) = _
        rw [nquotConj_piG g W hmN]
        congr 1
        group))

end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace T75
open CFSG.ClassicalInvolution.Asc77.T75
variable {G : Type} [Group G]

@[expose] def OddConj (Ω : Set (Subgroup G)) : Prop :=
  ∀ ⦃K : Subgroup G⦄, K ∈ Ω → ∀ ⦃z : G⦄, IsUniqueInvolution K z →
    ∀ ⦃R V U : Subgroup G⦄, IsSylow2In R K → V ≤ R → U ≤ R → IsCyclic ↥V → IsCyclic ↥U →
      Nat.card V = 4 → Nat.card U = 4 → Nat.card R = 8 →
        ∃ y ∈ K, y ∈ Subgroup.normalizer (R : Set G) ∧ Odd (orderOf y) ∧ conjSub y V = U

theorem exists_odd_normalizer_conj {Ω : Set (Subgroup G)} (hΩ : OddConj Ω) {K : Subgroup G}
    (hK : K ∈ Ω) {z : G} (hz : IsUniqueInvolution K z) {R V U : Subgroup G} (hR : IsSylow2In R K)
    (hVR : V ≤ R) (hUR : U ≤ R) (hcV : IsCyclic ↥V) (hcU : IsCyclic ↥U) (hV4 : Nat.card V = 4)
    (hU4 : Nat.card U = 4) (hR8 : Nat.card R = 8) :
    ∃ y ∈ K, y ∈ Subgroup.normalizer (R : Set G) ∧ Odd (orderOf y) ∧ conjSub y V = U :=
  hΩ hK hz hR hVR hUR hcV hcU hV4 hU4 hR8
end T75
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace T75
open CFSG.ClassicalInvolution.Asc77.T75
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

structure Data (Ω : Set (Subgroup G)) (S : Sylow 2 G)
    (η β : Set (Subgroup G)) : Prop where
  hΩ : HypOmegaMod Ω
  hU : OddConj Ω
  hη : η ∈ etaSet Ω (S : Subgroup G)
  hηi : ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η
  hβ : β ∈ etaSet Ω (S : Subgroup G)
  hβi : ∀ s ∈ (S : Subgroup G), ∀ U ∈ β, conjSub s U ∈ β
variable {S : Sylow 2 G} {η β : Set (Subgroup G)}

theorem Data.symm (D : Data Ω S η β) : Data Ω S β η :=
  ⟨D.hΩ, D.hU, D.hβ, D.hβi, D.hη, D.hηi⟩

theorem Data.distinct (D : Data Ω S η β) {A B : Subgroup G} (hA : A ∈ η) (hB : B ∈ η)
    (hne : A ≠ B) {K : Subgroup G} (hK : K ∈ Ω) (hAK : A ≤ K) (hBK : B ≤ K) : False :=
  D.hη.2.1 A hA B hB hne K hK ⟨hAK, hBK⟩

theorem Data.commutes [Finite G] (D : Data Ω S η β) {A B : Subgroup G} (hA : A ∈ η)
    (hB : B ∈ η) : Commutes A B := by
  have h := ((l6_9_proved G Ω D.hΩ S).2 η D.hη D.hηi).1
  intro x hx y hy
  exact h x (Subgroup.mem_iSup_of_mem A (Subgroup.mem_iSup_of_mem hA hx)) y
    (Subgroup.mem_iSup_of_mem B (Subgroup.mem_iSup_of_mem hB hy))

theorem Data.partner [Finite G] (D : Data Ω S η β) {A : Subgroup G} (hA : A ∈ USet Ω)
    (hAS : A ≤ (S : Subgroup G)) : ∃! V : Subgroup G, V ∈ η ∧ (A = V ∨ A ⊔ V ∈ RSet Ω) :=
  l6_8 G Ω D.hΩ S A hA hAS η ⟨S, D.hη, D.hηi⟩ fun _ hV => (D.hη.1 hV).2
section Local
variable [Finite G]

theorem Data.local_facts (D : Data Ω S η β) {V U : Subgroup G} (hV : V ∈ η) (hVβ : V ∉ β)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) :
    ∃ K ∈ Ω, ∃ z : G, IsUniqueInvolution K z ∧ IsSylow2In (V ⊔ U) K ∧ z ∈ V ⊔ U ∧
      Nat.card ↥(V ⊔ U) = 8 ∧ Nat.card V = 4 ∧ Nat.card U = 4 ∧ IsCyclic ↥V ∧ IsCyclic ↥U ∧
      (∀ x ∈ V ⊔ U, (∀ r ∈ V ⊔ U, r * x = x * r) → x = 1 ∨ x = z) := by
  have hΩ := D.hΩ
  have hVU : V ∈ USet Ω ∧ V ≤ (S : Subgroup G) := D.hη.1 hV
  have hUU : U ∈ USet Ω ∧ U ≤ (S : Subgroup G) := D.hβ.1 hU
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hK
  have hVK : V ≤ K := le_sup_left.trans hRK.1
  have hUK : U ≤ K := le_sup_right.trans hRK.1
  have hcard : ∀ {A : Subgroup G}, A ∈ USet Ω → A ≤ K → Nat.card ↥(V ⊔ U) = 2 * Nat.card A := by
    intro A hA hAK
    obtain ⟨R', -, J, hJ, hR'J, hAR', -, hcard', -⟩ := hΩ.exists_data_of_mem_USet hA
    have hJK : J = K := hΩ.eq_of_mem_USet hA hJ hK (hAR'.trans hR'J.1) hAK
    subst hJK
    rw [hRK.natCard_eq hR'J, hcard']
  have hRV := hcard hVU.1 hVK
  have hRU := hcard hUU.1 hUK
  obtain ⟨-, -, -, -, -, -, hcV, -, -⟩ := hΩ.exists_data_of_mem_USet hVU.1
  obtain ⟨-, -, -, -, -, -, hcU, -, -⟩ := hΩ.exists_data_of_mem_USet hUU.1
  have hQ := hΩ.isQuatSub_of_mem_RSet hR
  have hVUne : V ≠ U := fun h => hVβ (h ▸ hU)
  have h8 : Nat.card ↥(V ⊔ U) = 8 := by
    refine AscL62.natCard_eq_eight_of_not_sixteen_le hQ fun h16 => hVUne ?_
    exact hQ.eq_of_cyclic le_sup_left le_sup_right hcV hcU hRV hRU h16
  have hzR : z ∈ V ⊔ U := by
    have hzN : z ∈ Subgroup.normalizer ((V ⊔ U : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have h1 := hz.commute_of_mem (hRK.1 hh)
        have e : z * h * z⁻¹ = h := by rw [h1]; group
        rw [e]
        exact hh
      · intro hh
        have hhK : z * h * z⁻¹ ∈ K := hRK.1 hh
        have hhK' : h ∈ K := by
          have := K.mul_mem (K.mul_mem (K.inv_mem hz.mem) hhK) hz.mem
          simpa [mul_assoc] using this
        have h1 := hz.commute_of_mem hhK'
        have e : z * h * z⁻¹ = h := by rw [h1]; group
        rwa [e] at hh
    exact T75.mem_of_mem_normalizer hRK hz.mem hzN
      (isPGroup_zpowers_of_mul_self_eq_one hz.sq hz.ne_one)
  refine ⟨K, hK, z, hz, hRK, hzR, h8, by omega, by omega, hcV, hcU, fun x hx hc => ?_⟩
  have hx2 : x * x = 1 := hQ.sq_eq_one_of_central hx fun y hy => (hc y hy).symm
  exact hz.unique x (hRK.1 hx) hx2

theorem Data.commutes_local (D : Data Ω S η β) {V U K : Subgroup G} (hV : V ∈ η)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) (hK : K ∈ Ω) (hRK : IsSylow2In (V ⊔ U) K)
    {A : Subgroup G} (hA : (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)) : Commutes (V ⊔ U) A := by
  have hRS : V ⊔ U ≤ (S : Subgroup G) := sup_le (D.hη.1 hV).2 (D.hβ.1 hU).2
  have hVK : V ≤ K := le_sup_left.trans hRK.1
  have hUK : U ≤ K := le_sup_right.trans hRK.1
  have hboth : A ∈ η → A ∈ β → Commutes (V ⊔ U) A := fun hAη hAβ =>
    commutes_sup (D.commutes hV hAη) (D.symm.commutes hU hAβ)
  rcases hA with ⟨hAη, hAV⟩ | ⟨hAβ, hAU⟩
  · by_cases hAβ : A ∈ β
    · exact hboth hAη hAβ
    · obtain ⟨U', ⟨hU'β, hU'⟩, -⟩ := D.symm.partner (D.hη.1 hAη).1 (D.hη.1 hAη).2
      rcases hU' with h | hRA
      · exact absurd (h ▸ hU'β) hAβ
      · have hRAS : A ⊔ U' ≤ (S : Subgroup G) := sup_le (D.hη.1 hAη).2 (D.hβ.1 hU'β).2
        have hne : V ⊔ U ≠ A ⊔ U' := by
          intro h
          exact D.distinct hAη hV hAV hK (le_sup_left.trans (h ▸ hRK.1)) hVK
        have hc := l6_7_proved G Ω D.hΩ S _ hR _ hRA hRS hRAS hne
        intro x hx y hy
        exact hc x hx y (Subgroup.mem_sup_left hy)
  · by_cases hAη : A ∈ η
    · exact hboth hAη hAβ
    · obtain ⟨V', ⟨hV'η, hV'⟩, -⟩ := D.partner (D.hβ.1 hAβ).1 (D.hβ.1 hAβ).2
      rcases hV' with h | hRA
      · exact absurd (h ▸ hV'η) hAη
      · have hRAS : A ⊔ V' ≤ (S : Subgroup G) := sup_le (D.hβ.1 hAβ).2 (D.hη.1 hV'η).2
        have hne : V ⊔ U ≠ A ⊔ V' := by
          intro h
          exact D.symm.distinct hAβ hU hAU hK (le_sup_left.trans (h ▸ hRK.1)) hUK
        have hc := l6_7_proved G Ω D.hΩ S _ hR _ hRA hRS hRAS hne
        intro x hx y hy
        exact hc x hx y (Subgroup.mem_sup_left hy)

theorem Data.le_normalizer_local (D : Data Ω S η β) {V U K : Subgroup G} (hV : V ∈ η)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) (hK : K ∈ Ω) (hRK : IsSylow2In (V ⊔ U) K) {z : G}
    (hz : IsUniqueInvolution K z) (hzR : z ∈ V ⊔ U) {A : Subgroup G}
    (hA : (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)) : A ≤ Subgroup.normalizer (K : Set G) := by
  have hVK : V ≤ K := le_sup_left.trans hRK.1
  have hUK : U ≤ K := le_sup_right.trans hRK.1
  have hAU : A ∈ USet Ω ∧ A ≤ (S : Subgroup G) := by
    rcases hA with ⟨h, -⟩ | ⟨h, -⟩
    · exact D.hη.1 h
    · exact D.hβ.1 h
  obtain ⟨J, hJ, hAJ⟩ := D.hΩ.exists_member_of_mem_USet hAU.1
  have hJK : J ≠ K := by
    intro hJK
    rw [hJK] at hAJ hJ
    rcases hA with ⟨hAη, hAV⟩ | ⟨hAβ, hAU'⟩
    · exact D.distinct hAη hV hAV hK hAJ hVK
    · exact D.symm.distinct hAβ hU hAU' hK hAJ hUK
  have hA2 : IsPGroup 2 ↥A := S.isPGroup'.to_le hAU.2
  obtain ⟨-, -, -, -, -, -, -, -, hA4⟩ := D.hΩ.exists_data_of_mem_USet hAU.1
  have hcomm := D.commutes_local hV hU hR hK hRK hA
  have hAc : A ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR a ha).symm
  exact D.hΩ.le_normalizer_of_le_centralizer hK hJ hJK.symm hz hAJ hA2 (by omega) hAc

theorem Data.exists_local_conj (D : Data Ω S η β) {V U : Subgroup G} (hV : V ∈ η)
    (hVβ : V ∉ β) (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) :
    ∃ y : G, conjSub y V = U ∧ (∀ A ∈ η, A ≠ V → ∀ g ∈ A, y * g = g * y) ∧
      ∀ A ∈ β, A ≠ U → ∀ g ∈ A, y * g = g * y := by
  obtain ⟨K, hK, z, hz, hRK, hzR, h8, hV4, hU4, hcV, hcU, hZ⟩ := D.local_facts hV hVβ hU hR
  set P : Subgroup G :=
    ⨆ A ∈ {A : Subgroup G | (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)}, A with hP
  have hother : ∀ A : Subgroup G, ((A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)) →
      A ≤ (S : Subgroup G) := by
    intro A hA
    rcases hA with ⟨h, -⟩ | ⟨h, -⟩
    · exact (D.hη.1 h).2
    · exact (D.hβ.1 h).2
  have hPS : P ≤ (S : Subgroup G) := iSup₂_le fun A hA => hother A hA
  have hP2 : IsPGroup 2 ↥P := S.isPGroup'.to_le hPS
  have hPR : P ≤ Subgroup.centralizer ((V ⊔ U : Subgroup G) : Set G) :=
    iSup₂_le fun A hA x hx => Subgroup.mem_centralizer_iff.mpr fun r hr =>
      (D.commutes_local hV hU hR hK hRK hA r hr x hx)
  have hPK : P ≤ Subgroup.normalizer (K : Set G) :=
    iSup₂_le fun A hA => D.le_normalizer_local hV hU hR hK hRK hz hzR hA
  obtain ⟨y₀, hy₀K, hy₀N, hy₀odd, hy₀V⟩ := exists_odd_normalizer_conj D.hU hK hz hRK
    le_sup_left le_sup_right hcV hcU hV4 hU4 h8
  obtain ⟨y, hyK, hyN, hyodd, hyact, hyP⟩ := exists_fixed_odd_conj hRK hzR hz.sq hz.ne_one
    (fun w hw => (hz.commute_of_mem hw).symm) hZ hy₀K hy₀N hy₀odd hP2 hPK hPR
  have hyV : conjSub y V = U := by
    have hle : conjSub y V ≤ U := by
      intro w hw
      have hv : y⁻¹ * w * y ∈ V := mem_conjSub_iff.mp hw
      have e : w = y * (y⁻¹ * w * y) * y⁻¹ := by group
      have hvR : y⁻¹ * w * y ∈ V ⊔ U := Subgroup.mem_sup_left hv
      rw [e, hyact _ hvR]
      have h1 : y₀ * (y⁻¹ * w * y) * y₀⁻¹ ∈ conjSub y₀ V := conj_mem_conjSub hv
      rw [hy₀V] at h1
      exact h1
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [AscL62.natCard_conjSub, hU4, hV4])
  refine ⟨y, hyV, fun A hAη hAV g hg => ?_, fun A hAβ hAU g hg => ?_⟩
  · exact (hyP g ((le_iSup₂ (f := fun A (_ : A ∈ {A : Subgroup G |
      (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)}) => A) A (Or.inl ⟨hAη, hAV⟩)) hg)).symm
  · exact (hyP g ((le_iSup₂ (f := fun A (_ : A ∈ {A : Subgroup G |
      (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)}) => A) A (Or.inr ⟨hAβ, hAU⟩)) hg)).symm
end Local
end T75
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace T75
open CFSG.ClassicalInvolution.Asc77.T75
variable {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {S : Sylow 2 G} {η β : Set (Subgroup G)}

theorem Data.false_of_sup_mem_RSet (D : Data Ω S η β) {U V : Subgroup G} (hU : U ∈ β)
    (hV : V ∈ β) (hne : U ≠ V) (hR : U ⊔ V ∈ RSet Ω) : False := by
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  exact D.symm.distinct hU hV hne hK (le_sup_left.trans hRK.1) (le_sup_right.trans hRK.1)

theorem Data.exists_conj_eq [Finite G] (D : Data Ω S η β) :
    ∃ c : G, conjSub c (⨆ A ∈ η, A) = ⨆ A ∈ β, A := by
  classical
  have hex : ∀ V : Subgroup G, V ∈ η → V ∉ β → ∃ U : Subgroup G, U ∈ β ∧ V ⊔ U ∈ RSet Ω := by
    intro V hV hVβ
    obtain ⟨U, ⟨hUβ, hU⟩, -⟩ := D.symm.partner (D.hη.1 hV).1 (D.hη.1 hV).2
    rcases hU with h | hR
    · exact absurd (h ▸ hUβ) hVβ
    · exact ⟨U, hUβ, hR⟩
  choose! partner hpβ hpR using hex
  have key : ∀ F : Finset (Subgroup G), (∀ V ∈ F, V ∈ η ∧ V ∉ β) →
      ∃ c : G, (∀ V ∈ F, conjSub c V = partner V) ∧
        ∀ A ∈ η, A ∉ F → ∀ g ∈ A, c * g * c⁻¹ = g := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨1, by simp, by simp⟩
    | insert V₀ F hV₀F ih =>
      intro hF
      obtain ⟨hV₀η, hV₀β⟩ := hF V₀ (Finset.mem_insert_self _ _)
      obtain ⟨c, hc1, hc2⟩ := ih fun V hV => hF V (Finset.mem_insert_of_mem hV)
      obtain ⟨y₀, hy₀V, hy₀η, hy₀β⟩ :=
        D.exists_local_conj hV₀η hV₀β (hpβ V₀ hV₀η hV₀β) (hpR V₀ hV₀η hV₀β)
      refine ⟨y₀ * c, ?_, ?_⟩
      · intro V hV
        rcases Finset.mem_insert.mp hV with rfl | hVF
        · have h1 : conjSub c V = V := conjSub_eq_of_fix (hc2 V hV₀η hV₀F)
          rw [conjSub_mul, h1, hy₀V]
        · obtain ⟨hVη, hVβ⟩ := hF V hV
          have hne : V ≠ V₀ := fun h => hV₀F (h ▸ hVF)
          have hne' : partner V ≠ partner V₀ := by
            intro h
            have hU := hpβ V hVη hVβ
            obtain ⟨V'', -, huniq⟩ := D.partner (D.hβ.1 hU).1 (D.hβ.1 hU).2
            have h1 : V = V'' := huniq V ⟨hVη, Or.inr (by rw [sup_comm]; exact hpR V hVη hVβ)⟩
            have h2 : V₀ = V'' := huniq V₀ ⟨hV₀η, Or.inr (by
              rw [sup_comm, h]; exact hpR V₀ hV₀η hV₀β)⟩
            exact hne (h1.trans h2.symm)
          rw [conjSub_mul, hc1 V hVF]
          exact conjSub_eq_of_fix fun g hg => by
            have := hy₀β (partner V) (hpβ V hVη hVβ) hne' g hg
            rw [this]; group
      · intro A hAη hAF g hg
        have hAV₀ : A ≠ V₀ := fun h => hAF (h ▸ Finset.mem_insert_self _ _)
        have hAF' : A ∉ F := fun h => hAF (Finset.mem_insert_of_mem h)
        have h1 := hc2 A hAη hAF' g hg
        calc y₀ * c * g * (y₀ * c)⁻¹ = y₀ * (c * g * c⁻¹) * y₀⁻¹ := by group
          _ = y₀ * g * y₀⁻¹ := by rw [h1]
          _ = g := by rw [hy₀η A hAη hAV₀ g hg]; group
  have hfin := Set.toFinite {V : Subgroup G | V ∈ η ∧ V ∉ β}
  obtain ⟨c, hc1, hc2⟩ := key hfin.toFinset fun V hV => (Set.Finite.mem_toFinset hfin).mp hV
  refine ⟨c, ?_⟩
  have hfixη : ∀ A ∈ η, A ∈ β → conjSub c A = A := fun A hAη hAβ =>
    conjSub_eq_of_fix (hc2 A hAη fun h => ((Set.Finite.mem_toFinset hfin).mp h).2 hAβ)
  have hmapη : ∀ A ∈ η, A ∉ β → conjSub c A = partner A := fun A hAη hAβ =>
    hc1 A ((Set.Finite.mem_toFinset hfin).mpr ⟨hAη, hAβ⟩)
  rw [conjSub_iSup₂]
  apply le_antisymm
  · refine iSup₂_le fun A hA => ?_
    by_cases hAβ : A ∈ β
    · rw [hfixη A hA hAβ]
      exact le_iSup₂ (f := fun A (_ : A ∈ β) => A) A hAβ
    · rw [hmapη A hA hAβ]
      exact le_iSup₂ (f := fun A (_ : A ∈ β) => A) _ (hpβ A hA hAβ)
  · refine iSup₂_le fun U hU => ?_
    by_cases hUη : U ∈ η
    · rw [← hfixη U hUη hU]
      exact le_iSup₂ (f := fun A (_ : A ∈ η) => conjSub c A) U hUη
    · obtain ⟨V, ⟨hVη, hV⟩, -⟩ := D.partner (D.hβ.1 hU).1 (D.hβ.1 hU).2
      rcases hV with h | hR
      · exact absurd (h ▸ hVη) hUη
      · have hVβ : V ∉ β := fun hVβ =>
          D.false_of_sup_mem_RSet hU hVβ (fun h => hUη (h ▸ hVη)) hR
        have hUp : partner V = U := by
          obtain ⟨U', -, huniq⟩ := D.symm.partner (D.hη.1 hVη).1 (D.hη.1 hVη).2
          have h1 : partner V = U' := huniq _ ⟨hpβ V hVη hVβ, Or.inr (hpR V hVη hVβ)⟩
          have h2 : U = U' := huniq _ ⟨hU, Or.inr (by rw [sup_comm]; exact hR)⟩
          exact h1.trans h2.symm
        rw [← hUp, ← hmapη V hVη hVβ]
        exact le_iSup₂ (f := fun A (_ : A ∈ η) => conjSub c A) V hVη
end T75

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem l7_5_2_of [Finite G] (hΩ : HypOmegaMod Ω) (hU : T75.OddConj Ω) {W : Subgroup G}
    (hW : W ∈ WSet Ω) {W' : Subgroup G} (hW' : W' ∈ WSet Ω) :
    Nonempty (↥(muGroup Ω W) ≃* ↥(muGroup Ω W')) := by
  obtain ⟨η, ⟨S₁, hη, hηi⟩, rfl⟩ := hW
  obtain ⟨β₀, ⟨S₂, hβ₀, hβ₀i⟩, rfl⟩ := hW'
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₂ S₁
  have hβ : conjSub g '' β₀ ∈ etaSet Ω (S₁ : Subgroup G) := by
    have := conjSub_image_mem_etaSet hΩ.conjInvariant hβ₀ g
    rwa [hg] at this
  have hβi : ∀ s ∈ (S₁ : Subgroup G), ∀ U ∈ conjSub g '' β₀, conjSub s U ∈ conjSub g '' β₀ := by
    rintro s hs _ ⟨U, hU, rfl⟩
    rw [← hg, mem_conjSub_iff] at hs
    refine ⟨conjSub (g⁻¹ * s * g) U, hβ₀i _ hs U hU, ?_⟩
    rw [← conjSub_mul, ← conjSub_mul]
    congr 1
    group
  obtain ⟨c, hc⟩ := (T75.Data.mk hΩ hU hη hηi hβ hβi).exists_conj_eq
  have himg : (⨆ A ∈ conjSub g '' β₀, A) = conjSub g (⨆ A ∈ β₀, A) := by
    rw [conjSub_iSup₂, iSup_image]
  rw [himg] at hc
  have hW'eq : conjSub (g⁻¹ * c) (⨆ A ∈ η, A) = ⨆ A ∈ β₀, A := by
    rw [conjSub_mul, hc, conjSub_inv_conjSub]
  have key : ∀ W₂ : Subgroup G, conjSub (g⁻¹ * c) (⨆ A ∈ η, A) = W₂ →
      Nonempty (↥(muGroup Ω (⨆ A ∈ η, A)) ≃* ↥(muGroup Ω W₂)) := by
    rintro W₂ rfl
    exact ⟨Thompson.muGroupConjEquiv hΩ _ _⟩
  exact key _ hW'eq

end Asc77

end

end CFSG.ClassicalInvolution.T7F25
