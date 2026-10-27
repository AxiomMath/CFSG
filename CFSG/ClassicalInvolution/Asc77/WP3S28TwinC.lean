module

public import CFSG.ClassicalInvolution.Asc77.WP3S28TwinB
public import CFSG.ClassicalInvolution.Asc77.WP3FrameTwinP1

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Asc77.S28

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.Assembly.LowTwoRank

local notation "𝒞" => CoreAssembly.conjClass

section PairStab

variable {G : Type} [Group G]

@[expose] def pairStab (a b : G) : Subgroup G where
  carrier := {x | (x * a * x⁻¹ = a ∧ x * b * x⁻¹ = b) ∨ (x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a)}
  one_mem' := Or.inl ⟨by group, by group⟩
  mul_mem' := by
    rintro x y (⟨hxa, hxb⟩ | ⟨hxa, hxb⟩) (⟨hya, hyb⟩ | ⟨hya, hyb⟩)
    · left
      exact ⟨by calc x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
                _ = a := by rw [hya, hxa],
        by calc x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
          _ = b := by rw [hyb, hxb]⟩
    · right
      exact ⟨by calc x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
                _ = b := by rw [hya, hxb],
        by calc x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
          _ = a := by rw [hyb, hxa]⟩
    · right
      exact ⟨by calc x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
                _ = b := by rw [hya, hxa],
        by calc x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
          _ = a := by rw [hyb, hxb]⟩
    · left
      exact ⟨by calc x * y * a * (x * y)⁻¹ = x * (y * a * y⁻¹) * x⁻¹ := by group
                _ = a := by rw [hya, hxb],
        by calc x * y * b * (x * y)⁻¹ = x * (y * b * y⁻¹) * x⁻¹ := by group
          _ = b := by rw [hyb, hxa]⟩
  inv_mem' := by
    rintro x (⟨hxa, hxb⟩ | ⟨hxa, hxb⟩)
    · left
      exact ⟨by calc x⁻¹ * a * x⁻¹⁻¹ = x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ := by rw [hxa]
                _ = a := by group,
        by calc x⁻¹ * b * x⁻¹⁻¹ = x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ := by rw [hxb]
          _ = b := by group⟩
    · right
      exact ⟨by calc x⁻¹ * a * x⁻¹⁻¹ = x⁻¹ * (x * b * x⁻¹) * x⁻¹⁻¹ := by rw [hxb]
                _ = b := by group,
        by calc x⁻¹ * b * x⁻¹⁻¹ = x⁻¹ * (x * a * x⁻¹) * x⁻¹⁻¹ := by rw [hxa]
          _ = a := by group⟩

theorem mem_pairStab {a b x : G} :
    x ∈ pairStab a b ↔
      (x * a * x⁻¹ = a ∧ x * b * x⁻¹ = b) ∨ (x * a * x⁻¹ = b ∧ x * b * x⁻¹ = a) := Iff.rfl

end PairStab

section Members

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K T : Subgroup G} {z w : G}
  (h : FalseTwinPure Ω K T z w)

include h

theorem inv_conj_eq {x : G} (hx : x * z * x⁻¹ = z) : x⁻¹ * z * x⁻¹⁻¹ = z := by
  calc x⁻¹ * z * x⁻¹⁻¹ = x⁻¹ * (x * z * x⁻¹) * x := by rw [hx]; group
    _ = z := by group

theorem conj_mem_of_centralizes {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {z})
    (hMK : M ≠ K) (hMT : M ≠ T) {x : G} (hx : x * z * x⁻¹ = z) :
    conjSub x M ∈ centralizingMembers Ω {z} ∧ conjSub x M ≠ K ∧ conjSub x M ≠ T := by
  refine ⟨?_, fun e => hMK ?_, fun e => hMT ?_⟩
  · have := mem_centralizingMembers_conj h.conj x z hM
    rwa [hx] at this
  · have h1 : M = conjSub x⁻¹ K := by rw [← e, conjSub_inv_conjSub]
    rw [h1]
    exact h.conj_K_eq (inv_conj_eq h hx)
  · have h1 : M = conjSub x⁻¹ T := by rw [← e, conjSub_inv_conjSub]
    rw [h1]
    exact h.conj_T_eq (inv_conj_eq h hx)

section Finite

variable [Finite G]

theorem conj_swap_mem {M : Subgroup G} (hM : M ∈ centralizingMembers Ω {z})
    (hMK : M ≠ K) (hMT : M ≠ T) {s : G} (hsK : conjSub s K = T) (hsT : conjSub s T = K)
    (hsz : s * z * s⁻¹ = w) :
    conjSub s M ∈ centralizingMembers Ω {z} ∧ conjSub s M ≠ K ∧ conjSub s M ≠ T := by
  refine ⟨?_, fun e => hMT ?_, fun e => hMK ?_⟩
  · have := mem_centralizingMembers_conj h.conj s z hM
    rwa [hsz, h.centralizingMembers_w_eq] at this
  · have h1 : M = conjSub s⁻¹ K := by rw [← e, conjSub_inv_conjSub]
    rw [h1, ← hsT, conjSub_inv_conjSub]
  · have h1 : M = conjSub s⁻¹ T := by rw [← e, conjSub_inv_conjSub]
    rw [h1, ← hsK, conjSub_inv_conjSub]

theorem inv_mem_of_adjacent {g : G} (hM : conjSub g K ∈ centralizingMembers Ω {z})
    (hMK : conjSub g K ≠ K) (hMT : conjSub g K ≠ T) :
    conjSub g⁻¹ K ∈ centralizingMembers Ω {z} ∧ conjSub g⁻¹ K ≠ K ∧ conjSub g⁻¹ K ≠ T := by
  refine ⟨?_, fun e => hMK ?_, fun e => h.M₂_ne_K hMT ?_⟩
  · have h1 := h.K_mem_conj hM hMK
    have := mem_centralizingMembers_conj h.conj g⁻¹ _ h1
    have e2 : g⁻¹ * (g * z * g⁻¹) * g⁻¹⁻¹ = z := by group
    rwa [e2] at this
  · have h2 := congrArg (conjSub g) e
    rw [conjSub_conjSub_inv] at h2
    exact h2.symm
  · have h2 := congrArg (conjSub g) e
    rw [conjSub_conjSub_inv] at h2
    exact h2.symm

end Finite

end Members

section Main

variable {p f : ℕ} [Fact p.Prime]


theorem twinInvolutionRow {tY : StatedLieTag} {nY : ℕ} (hrow : TwinRow tY nY)
    (hmf : TwinProductCentral p f tY nY) {G : Type} [Group G]
    [Finite G] [IsSimpleGroup G] (hnab : ∃ x y : G, x * y ≠ y * x) {K : Subgroup G} {z : G}
    (S : RouteDSetup p f K z) (hshape : LocalShapeT p f 2 tY nY (𝒞 K) z) {T : Subgroup G}
    (hT : IsTwinAt (𝒞 K) K T z) : IsClassicalMember p f T z := by
  classical
  by_contra hnot
  obtain ⟨hG2, hD4, hnA1⟩ := hrow.tag_facts
  have rf := LocalShapeT.twinRowFacts hshape S.odd S.five hG2 hD4 hnA1
  obtain ⟨d⟩ := LocalShapeT.nonempty_dictT2 hD4 rf.fsc S.inClass
    (CoreAssembly.mem_conjClass_self K) S.cls hshape
  let L₀ : TwinLocal p f (𝒞 K) z tY nY := ⟨S.inClass, S.exact, S.p1, rf, d⟩
  obtain ⟨w, hw⟩ := S.inClass.classical T hT.mem.1
  have hwz : w ≠ z := by
    rintro rfl
    exact hnot hw
  have hKΩ : K ∈ centralizingMembers (𝒞 K) {z} :=
    ⟨CoreAssembly.mem_conjClass_self K, le_centralizer_of_isClassicalMember S.cls⟩
  have hFT : FalseTwinPure (𝒞 K) K T z w :=
    { conj := S.inClass.conjInvariant
      trans := fun M ⟨g, hg⟩ => ⟨g, hg⟩
      hK := CoreAssembly.mem_conjClass_self K
      hT := hT.mem.1
      hz := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five S.cls
      hw := ConnectedA2.isUniqueInvolution_of_isClassicalMember S.odd S.five hw
      hwz := hwz
      hKT := Ne.symm hT.ne
      hKc := le_centralizer_of_isClassicalMember S.cls
      hTc := le_centralizer_of_isClassicalMember hw
      hTz := hT.mem.2
      commK := hT.comm_K
      commT := hT.comm_T
      noniso := fun L hL hLK hLT => exists_noncomm_of_ne S.inClass S.exact S.p1 rf d hKΩ hT.mem
        (Ne.symm hT.ne) hT.comm_K hT.comm_T hL hLK hLT }
  obtain ⟨ε, hε⟩ := claimA L₀ hFT S.cls hw hmf
  obtain ⟨g₀, hg₀, hg₀K, hg₀T⟩ := exists_member L₀ hFT S.cls hw
  obtain ⟨s, hsK, hsT, hsz, hsw⟩ := hFT.exists_swap
  set u₀ : G := z * w with hu₀
  have hεg₀ : g₀ * u₀ * g₀⁻¹ = ε := hε g₀ hg₀ hg₀K hg₀T
  have hStabC : ∀ x : G, x * z * x⁻¹ = z → x ∈ pairStab u₀ ε := by
    intro x hx
    left
    have hxw := hFT.conj_w_eq_of_conj_z_eq hx
    refine ⟨?_, ?_⟩
    · calc x * u₀ * x⁻¹ = (x * z * x⁻¹) * (x * w * x⁻¹) := by rw [hu₀]; group
        _ = u₀ := by rw [hx, hxw]
    · obtain ⟨h1, h2, h3⟩ := conj_mem_of_centralizes hFT hg₀ hg₀K hg₀T hx
      have := hε (x * g₀) (by rw [conjSub_mul]; exact h1) (by rw [conjSub_mul]; exact h2)
        (by rw [conjSub_mul]; exact h3)
      calc x * ε * x⁻¹ = x * (g₀ * u₀ * g₀⁻¹) * x⁻¹ := by rw [hεg₀]
        _ = (x * g₀) * u₀ * (x * g₀)⁻¹ := by group
        _ = ε := this
  have hStabS : s ∈ pairStab u₀ ε := by
    left
    refine ⟨?_, ?_⟩
    · calc s * u₀ * s⁻¹ = (s * z * s⁻¹) * (s * w * s⁻¹) := by rw [hu₀]; group
        _ = w * z := by rw [hsz, hsw]
        _ = u₀ := hFT.comm_zw.symm
    · obtain ⟨h1, h2, h3⟩ := conj_swap_mem hFT hg₀ hg₀K hg₀T hsK hsT hsz
      have := hε (s * g₀) (by rw [conjSub_mul]; exact h1) (by rw [conjSub_mul]; exact h2)
        (by rw [conjSub_mul]; exact h3)
      calc s * ε * s⁻¹ = s * (g₀ * u₀ * g₀⁻¹) * s⁻¹ := by rw [hεg₀]
        _ = (s * g₀) * u₀ * (s * g₀)⁻¹ := by group
        _ = ε := this
  have hStabA : ∀ g : G, conjSub g K ∈ centralizingMembers (𝒞 K) {z} → conjSub g K ≠ K →
      conjSub g K ≠ T → g ∈ pairStab u₀ ε := by
    intro g h1 h2 h3
    right
    refine ⟨hε g h1 h2 h3, ?_⟩
    obtain ⟨i1, i2, i3⟩ := inv_mem_of_adjacent hFT h1 h2 h3
    have := hε g⁻¹ i1 i2 i3
    calc g * ε * g⁻¹ = g * (g⁻¹ * u₀ * g⁻¹⁻¹) * g⁻¹ := by rw [this]
      _ = u₀ := by group
  let 𝔖 : Set (Subgroup G) :=
    {M | M ∈ 𝒞 K ∧ ∃ x ∈ pairStab u₀ ε, conjSub x K = M}
  have hK𝔖 : K ∈ 𝔖 := ⟨CoreAssembly.mem_conjClass_self K, 1, (pairStab u₀ ε).one_mem,
    conjSub_one K⟩
  have hcl : ∀ N ∈ 𝔖, ∀ L ∈ 𝒞 K, L ≠ N → Commutes N L → L ∈ 𝔖 := by
    rintro N ⟨-, x, hx, rfl⟩ L ⟨y, rfl⟩ hLN hNL
    refine ⟨⟨y, rfl⟩, y, ?_, rfl⟩
    have hM : conjSub (x⁻¹ * y) K = conjSub x⁻¹ (conjSub y K) := conjSub_mul _ _ _
    have hKx : conjSub x⁻¹ (conjSub x K) = K := conjSub_inv_conjSub x K
    have hcomm : Commutes K (conjSub (x⁻¹ * y) K) := by
      have := hNL.conjSub x⁻¹
      rwa [hKx, ← hM] at this
    have hMK : conjSub (x⁻¹ * y) K ≠ K := by
      intro e
      apply hLN
      have h2 : conjSub x⁻¹ (conjSub y K) = conjSub x⁻¹ (conjSub x K) := by rw [← hM, e, hKx]
      exact conjSub_injective x⁻¹ h2
    have hMz : conjSub (x⁻¹ * y) K ∈ centralizingMembers (𝒞 K) {z} :=
      ⟨S.inClass.conjInvariant _ K (CoreAssembly.mem_conjClass_self K), fun m hm => by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hcomm z S.cls.mem m hm).symm⟩
    have hxy : x⁻¹ * y ∈ pairStab u₀ ε := by
      by_cases hMT : conjSub (x⁻¹ * y) K = T
      · have hn : conjSub (s⁻¹ * (x⁻¹ * y)) K = K := by
          rw [conjSub_mul, hMT, ← hsK, conjSub_inv_conjSub]
        have hnz := hFT.conj_K_stab hn
        have := (pairStab u₀ ε).mul_mem hStabS (hStabC _ hnz)
        simpa using this
      · exact hStabA _ hMz hMK hMT
    have := (pairStab u₀ ε).mul_mem hx hxy
    simpa using this
  have hall : 𝒞 K ⊆ 𝔖 := subset_of_adj_closed S.conn (fun M hM => hM.1) ⟨K, hK𝔖⟩ hcl
  have hallStab : ∀ g : G, g ∈ pairStab u₀ ε := by
    intro g
    obtain ⟨-, x, hx, hxg⟩ := hall ⟨g, rfl⟩
    have hxg' : conjSub x K = conjSub g K := hxg
    have hn : conjSub (x⁻¹ * g) K = K := by rw [conjSub_mul, ← hxg', conjSub_inv_conjSub]
    have hnz := hFT.conj_K_stab hn
    have := (pairStab u₀ ε).mul_mem hx (hStabC _ hnz)
    simpa using this
  have hz2 : z * z = 1 := hFT.hz.sq
  have hu1 : u₀ ≠ 1 := by
    intro h1
    apply hwz
    calc w = z * (z * w) := by rw [← mul_assoc, hz2, one_mul]
      _ = z := by rw [← hu₀, h1, mul_one]
  by_cases hεu : ε = u₀
  ·
    have hcen : u₀ ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      rcases hallStab g with ⟨h1, -⟩ | ⟨h1, -⟩
      · calc g * u₀ = (g * u₀ * g⁻¹) * g := by group
          _ = u₀ * g := by rw [h1]
      · calc g * u₀ = (g * u₀ * g⁻¹) * g := by group
          _ = ε * g := by rw [h1]
          _ = u₀ * g := by rw [hεu]
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at hcen
    exact hu1 hcen
  ·
    have hnorm : (Subgroup.centralizer ({u₀} : Set G)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hn ⊢
      have hnu : n * u₀ * n⁻¹ = u₀ := by rw [hn]; group
      have ha : n * (g⁻¹ * u₀ * g) * n⁻¹ = g⁻¹ * u₀ * g := by
        have hg := hallStab g⁻¹
        rcases hg with ⟨h1, -⟩ | ⟨h1, -⟩
        · have : g⁻¹ * u₀ * g⁻¹⁻¹ = u₀ := h1
          rw [show g⁻¹ * u₀ * g = u₀ from by simpa using this]
          exact hnu
        · have h1' : g⁻¹ * u₀ * g = ε := by simpa using h1
          rw [h1']
          rcases hallStab n with ⟨h2, h3⟩ | ⟨h2, h3⟩
          · exact h3
          · exact absurd (hnu.symm.trans h2) (Ne.symm hεu)
      have hgu : g * (g⁻¹ * u₀ * g) * g⁻¹ = u₀ := by group
      calc (g * n * g⁻¹) * u₀ = (g * n * g⁻¹) * u₀ * (g * n * g⁻¹)⁻¹ * (g * n * g⁻¹) := by group
        _ = g * (n * (g⁻¹ * u₀ * g) * n⁻¹) * g⁻¹ * (g * n * g⁻¹) := by group
        _ = g * (g⁻¹ * u₀ * g) * g⁻¹ * (g * n * g⁻¹) := by rw [ha]
        _ = u₀ * (g * n * g⁻¹) := by rw [hgu]
    have := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.centralizer ({u₀} : Set G)) with hb | ht
    · have hzmem : z ∈ Subgroup.centralizer ({u₀} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc z * u₀ = z * (w * z) := by rw [hu₀, hFT.comm_zw]
          _ = u₀ * z := by rw [hu₀]; group
      rw [hb, Subgroup.mem_bot] at hzmem
      exact hFT.hz.ne_one hzmem
    · have hg₀mem : g₀ ∈ Subgroup.centralizer ({u₀} : Set G) := by rw [ht]; trivial
      rw [Subgroup.mem_centralizer_singleton_iff] at hg₀mem
      apply hεu
      rw [← hεg₀]
      calc g₀ * u₀ * g₀⁻¹ = (u₀ * g₀) * g₀⁻¹ := by rw [hg₀mem]
        _ = u₀ := by group

end Main

end CFSG.ClassicalInvolution.Asc77.S28
