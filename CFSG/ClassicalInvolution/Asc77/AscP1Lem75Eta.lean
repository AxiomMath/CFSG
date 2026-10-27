module

public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75Odd

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

namespace T75

variable {G : Type} [Group G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

structure Data (p f : ℕ) [Fact p.Prime] (Ω : Set (Subgroup G)) (S : Sylow 2 G)
    (η β : Set (Subgroup G)) : Prop where
  hp : p ≠ 2
  hq : 5 ≤ p ^ f
  hΩ : HypOmegaMod p f Ω
  hη : η ∈ etaSet Ω (S : Subgroup G)
  hηi : ∀ s ∈ (S : Subgroup G), ∀ U ∈ η, conjSub s U ∈ η
  hβ : β ∈ etaSet Ω (S : Subgroup G)
  hβi : ∀ s ∈ (S : Subgroup G), ∀ U ∈ β, conjSub s U ∈ β

variable {S : Sylow 2 G} {η β : Set (Subgroup G)}

theorem Data.symm (D : Data p f Ω S η β) : Data p f Ω S β η :=
  ⟨D.hp, D.hq, D.hΩ, D.hβ, D.hβi, D.hη, D.hηi⟩

theorem Data.usetS (D : Data p f Ω S η β) {V : Subgroup G} (hV : V ∈ η) :
    V ∈ USet Ω ∧ V ≤ (S : Subgroup G) := D.hη.1 hV

theorem Data.distinct (D : Data p f Ω S η β) {A B : Subgroup G} (hA : A ∈ η) (hB : B ∈ η)
    (hne : A ≠ B) {K : Subgroup G} (hK : K ∈ Ω) (hAK : A ≤ K) (hBK : B ≤ K) : False :=
  D.hη.2.1 A hA B hB hne K hK ⟨hAK, hBK⟩

theorem Data.commutes [Finite G] (D : Data p f Ω S η β) {A B : Subgroup G} (hA : A ∈ η)
    (hB : B ∈ η) : Commutes A B := by
  have h := ((l6_9_proved p f D.hp D.hq G Ω D.hΩ S).2 η D.hη D.hηi).1
  intro x hx y hy
  exact h x (Subgroup.mem_iSup_of_mem A (Subgroup.mem_iSup_of_mem hA hx)) y
    (Subgroup.mem_iSup_of_mem B (Subgroup.mem_iSup_of_mem hB hy))

theorem Data.partner [Finite G] (D : Data p f Ω S η β) {A : Subgroup G} (hA : A ∈ USet Ω)
    (hAS : A ≤ (S : Subgroup G)) : ∃! V : Subgroup G, V ∈ η ∧ (A = V ∨ A ⊔ V ∈ RSet Ω) :=
  l6_8 p f D.hp D.hq G Ω D.hΩ S A hA hAS η ⟨S, D.hη, D.hηi⟩ fun _ hV => (D.hη.1 hV).2

theorem commutes_sup {A V U : Subgroup G} (hV : Commutes V A) (hU : Commutes U A) :
    Commutes (V ⊔ U) A := by
  have h : V ⊔ U ≤ Subgroup.centralizer (A : Set G) := by
    refine sup_le (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
      (fun x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    · exact (hV x hx y hy).symm
    · exact (hU x hx y hy).symm
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h hx) y hy).symm

section Local

variable [Finite G]

theorem Data.local_facts (D : Data p f Ω S η β) {V U : Subgroup G} (hV : V ∈ η) (hVβ : V ∉ β)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) :
    ∃ K ∈ Ω, ∃ z : G, IsUniqueInvolution K z ∧ IsSylow2In (V ⊔ U) K ∧ z ∈ V ⊔ U ∧
      Nat.card ↥(V ⊔ U) = 8 ∧ Nat.card V = 4 ∧ Nat.card U = 4 ∧ IsCyclic ↥V ∧ IsCyclic ↥U ∧
      (∀ x ∈ V ⊔ U, (∀ r ∈ V ⊔ U, r * x = x * r) → x = 1 ∨ x = z) := by
  have hΩ := D.hΩ
  have hVU : V ∈ USet Ω ∧ V ≤ (S : Subgroup G) := D.hη.1 hV
  have hUU : U ∈ USet Ω ∧ U ≤ (S : Subgroup G) := D.hβ.1 hU
  obtain ⟨K, hK, hRK⟩ := exists_isSylow2In_of_mem_RSet hR
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution D.hp D.hq hK
  have hVK : V ≤ K := le_sup_left.trans hRK.1
  have hUK : U ≤ K := le_sup_right.trans hRK.1
  have hcard : ∀ {A : Subgroup G}, A ∈ USet Ω → A ≤ K → Nat.card ↥(V ⊔ U) = 2 * Nat.card A := by
    intro A hA hAK
    obtain ⟨R', -, J, hJ, hR'J, hAR', -, hcard', -⟩ := hΩ.exists_data_of_mem_USet D.hp hA
    have hJK : J = K := hΩ.eq_of_mem_USet D.hp hA hJ hK (hAR'.trans hR'J.1) hAK
    subst hJK
    rw [hRK.natCard_eq hR'J, hcard']
  have hRV := hcard hVU.1 hVK
  have hRU := hcard hUU.1 hUK
  obtain ⟨-, -, -, -, -, -, hcV, -, -⟩ := hΩ.exists_data_of_mem_USet D.hp hVU.1
  obtain ⟨-, -, -, -, -, -, hcU, -, -⟩ := hΩ.exists_data_of_mem_USet D.hp hUU.1
  have hQ := hΩ.isQuatSub_of_mem_RSet D.hp hR
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

theorem Data.commutes_local (D : Data p f Ω S η β) {V U K : Subgroup G} (hV : V ∈ η)
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
        have hc := l6_7_proved p f D.hp D.hq G Ω D.hΩ S _ hR _ hRA hRS hRAS hne
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
        have hc := l6_7_proved p f D.hp D.hq G Ω D.hΩ S _ hR _ hRA hRS hRAS hne
        intro x hx y hy
        exact hc x hx y (Subgroup.mem_sup_left hy)

theorem Data.le_normalizer_local (D : Data p f Ω S η β) {V U K : Subgroup G} (hV : V ∈ η)
    (hU : U ∈ β) (hR : V ⊔ U ∈ RSet Ω) (hK : K ∈ Ω) (hRK : IsSylow2In (V ⊔ U) K) {z : G}
    (hz : IsUniqueInvolution K z) (hzR : z ∈ V ⊔ U) {A : Subgroup G}
    (hA : (A ∈ η ∧ A ≠ V) ∨ (A ∈ β ∧ A ≠ U)) : A ≤ Subgroup.normalizer (K : Set G) := by
  have hVK : V ≤ K := le_sup_left.trans hRK.1
  have hUK : U ≤ K := le_sup_right.trans hRK.1
  have hAU : A ∈ USet Ω ∧ A ≤ (S : Subgroup G) := by
    rcases hA with ⟨h, -⟩ | ⟨h, -⟩
    · exact D.hη.1 h
    · exact D.hβ.1 h
  obtain ⟨J, hJ, hAJ⟩ := D.hΩ.exists_member_of_mem_USet D.hp hAU.1
  have hJK : J ≠ K := by
    intro hJK
    rw [hJK] at hAJ hJ
    rcases hA with ⟨hAη, hAV⟩ | ⟨hAβ, hAU'⟩
    · exact D.distinct hAη hV hAV hK hAJ hVK
    · exact D.symm.distinct hAβ hU hAU' hK hAJ hUK
  have hA2 : IsPGroup 2 ↥A := S.isPGroup'.to_le hAU.2
  obtain ⟨-, -, -, -, -, -, -, -, hA4⟩ := D.hΩ.exists_data_of_mem_USet D.hp hAU.1
  have hcomm := D.commutes_local hV hU hR hK hRK hA
  have hAc : A ≤ Subgroup.centralizer ({z} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzR a ha).symm
  exact D.hΩ.le_normalizer_of_le_centralizer D.hp D.hq hK hJ hJK.symm hz hAJ hA2 (by omega) hAc

theorem Data.exists_local_conj (D : Data p f Ω S η β) {V U : Subgroup G} (hV : V ∈ η)
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
  obtain ⟨y₀, hy₀K, hy₀N, hy₀odd, hy₀V⟩ := exists_odd_normalizer_conj D.hp D.hΩ hK hz hRK
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

end CFSG.ClassicalInvolution.Asc77
