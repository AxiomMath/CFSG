module

public import CFSG.ClassicalInvolution.Q3.Q3WAAllA1
public import CFSG.ClassicalInvolution.Q3.Q3WAWeak
public import CFSG.ClassicalInvolution.Q3.Q3WAM11Comp

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank

section Universal

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

@[expose] def Universal3 (Ω : Set (Subgroup G)) (x : G) (N : Subgroup G) : Prop :=
  ∀ N' ∈ centralizingMembers Ω {x}, N' ≠ N → Commutes N N'

theorem universal3_conj (hΩ : ConjInvariant Ω) (g x : G) {N : Subgroup G}
    (h : Universal3 Ω x N) : Universal3 Ω (g * x * g⁻¹) (conjSub g N) := by
  intro N' hN' hne
  rw [centralizingMembers_conj hΩ] at hN'
  obtain ⟨N'', hN'', rfl⟩ := hN'
  exact (h N'' hN'' fun h' => hne (by rw [h'])).conjSub g

theorem exists_conj_of_mem3 {K L T : Subgroup G} (hL : L ∈ conjClass3 K)
    (hT : T ∈ conjClass3 K) : ∃ g : G, T = conjSub g L := by
  obtain ⟨g₀, rfl⟩ := single_class3 K L hL
  obtain ⟨g₁, rfl⟩ := single_class3 K T hT
  exact ⟨g₁ * g₀⁻¹, by rw [← conjSub_mul, inv_mul_cancel_right]⟩

end Universal

section Kinds

theorem compData_m11_ne_sl23 : CompData.m11 ≠ CompData.sl23 := by
  intro hA
  have h1 : Nat.card CompData.m11.G = 7920 := card_m11_kernel
  have h2 : Nat.card CompData.sl23.G = 24 := natCard_sl2Three
  rw [hA] at h1
  omega

end Kinds

section Shape


variable {G : Type} [Group G] [Finite G] {ι : Type} {Ω : Set (Subgroup G)} {x : G}

theorem universal3_of_a1comp (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i : ι} (hi : IsA1Comp3 D i)
    {N : Subgroup G} (hN : N ∈ compMembers3 Ω x D i) : Universal3 Ω x N := by
  intro N' hN' hne
  obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hN'
  by_cases hji : j = i
  · subst hji
    exact absurd (eq_of_mem_compMembers_a13 hΩ hex hP1 hO3 hi hj hN) hne
  · exact commutes_of_ne_comp3 hΩ hex hP1 hO3 D (Ne.symm hji) hN hj

theorem not_commutes_of_nonuniversal_m11 (hΩ : InClass3 Ω) (hex : ExactMembers3 Ω)
    (hP1 : LocalOddCentral Ω {x}) (hO3 : LocalOddThreeFree3 Ω x)
    (D : LieSystemData3 ι (locQuot Ω x) (locFamily Ω x)) {i₁ : ι}
    (hk : D.kind i₁ = CompData.m11) (hrest : ∀ i, i ≠ i₁ → D.kind i = CompData.sl23)
    {N₁ N₂ : Subgroup G} (h₁ : N₁ ∈ centralizingMembers Ω {x})
    (h₂ : N₂ ∈ centralizingMembers Ω {x}) (hu₁ : ¬ Universal3 Ω x N₁)
    (hu₂ : ¬ Universal3 Ω x N₂) : ¬ Commutes N₁ N₂ := by
  have comp : ∀ N ∈ centralizingMembers Ω {x}, ¬ Universal3 Ω x N →
      N ∈ compMembers3 Ω x D i₁ := by
    intro N hN hnu
    obtain ⟨j, hj, -⟩ := exists_unique_comp3 hΩ hex hP1 hO3 D hN
    by_cases hji : j = i₁
    · rw [hji] at hj
      exact hj
    · exact absurd (universal3_of_a1comp hΩ hex hP1 hO3 D (hrest j hji) hj) hnu
  exact not_commutes_of_m11_comp3 hΩ hex hP1 hO3 hk (comp N₁ h₁ hu₁) (comp N₂ h₂ hu₂)

end Shape

section Main



variable {G : Type} [Group G] [Finite G]

theorem false_of_m11_two_a1_3 [IsSimpleGroup G]
    {K : Subgroup G} {z : G} (h : RouteD3Setup K z) (h3 : LocalOddThreeFree3 (conjClass3 K) z)
    {a : ℕ} (ha : 2 ≤ a) (hshape : LocalShapeC3 a CompData.m11 (conjClass3 K) z) : False := by
  classical
  have hMFZ := RouteD.Gaps.fundNoncentral 3
  have hΩ := h.inClass
  obtain ⟨hex, hP1⟩ := h.setup
  obtain ⟨ι, hι, D, hcard, i₁, hk, hrest⟩ := hshape
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} := ⟨hKΩ, isSubnormal_le h.cls.subnormal⟩
  have := Fintype.ofFinite ι
  have hc3 : 2 < Fintype.card ι := by
    rw [← Nat.card_eq_fintype_card, hcard]
    omega
  obtain ⟨u, v, t, huv, hut, hvt⟩ := Fintype.two_lt_card_iff.mp hc3
  obtain ⟨i₂, i₃, h23, h2, h3'⟩ : ∃ i₂ i₃ : ι, i₂ ≠ i₃ ∧ i₂ ≠ i₁ ∧ i₃ ≠ i₁ := by
    by_cases hu : u = i₁
    · exact ⟨v, t, hvt, fun h' => huv (hu.trans h'.symm), fun h' => hut (hu.trans h'.symm)⟩
    · by_cases hv : v = i₁
      · exact ⟨u, t, hut, hu, fun h' => hvt (hv.trans h'.symm)⟩
      · exact ⟨u, v, huv, hu, hv⟩
  have hi₁ : ¬ IsA1Comp3 D i₁ := by
    intro hA
    unfold IsA1Comp3 at hA
    rw [hk] at hA
    exact compData_m11_ne_sl23 hA
  obtain ⟨T₂, hT₂⟩ := exists_mem_compMembers3 (D := D) i₂
  obtain ⟨T₃, hT₃⟩ := exists_mem_compMembers3 (D := D) i₃
  have hu₂ := universal3_of_a1comp hΩ hex hP1 h3 D (hrest i₂ h2) hT₂
  have hu₃ := universal3_of_a1comp hΩ hex hP1 h3 D (hrest i₃ h3') hT₃
  have hT₂₃ : T₂ ≠ T₃ := by
    intro he
    obtain ⟨j, -, hj⟩ := exists_unique_comp3 hΩ hex hP1 h3 D hT₂.1
    exact h23 ((hj i₂ hT₂).trans (hj i₃ (he ▸ hT₃)).symm)
  have hT₂₃c : Commutes T₂ T₃ := hu₂ T₃ hT₃.1 (Ne.symm hT₂₃)
  obtain ⟨J, J', hJ, hJ', hJJ'⟩ := exists_ne_of_not_isA1Comp3 hΩ hex hP1 h3 hi₁
  have hnc : ¬ Commutes J J' := not_commutes_of_m11_comp3 hΩ hex hP1 h3 hk hJ hJ'
  have hne_comp : ∀ {N : Subgroup G} {i : ι}, N ∈ compMembers3 (conjClass3 K) z D i → i ≠ i₁ →
      N ≠ J := by
    intro N i hN hi he
    obtain ⟨j, -, hj⟩ := exists_unique_comp3 hΩ hex hP1 h3 D hN.1
    exact hi ((hj i hN).trans (hj i₁ (he ▸ hJ)).symm)
  have hcomm₂ : Commutes T₂ J := hu₂ J hJ.1 (Ne.symm (hne_comp hT₂ h2))
  have hcomm₃ : Commutes T₃ J := hu₃ J hJ.1 (Ne.symm (hne_comp hT₃ h3'))
  have hJΩ : J ∈ conjClass3 K := hJ.1.1
  obtain ⟨g, hg⟩ := single_class3 K J hJΩ
  obtain ⟨w, hw⟩ := hΩ.classical J hJΩ
  have hwg : w = g * z * g⁻¹ := by
    have hcl : IsClassicalMember3 J (g * z * g⁻¹) := by
      rw [hg]
      exact h.cls.conj g
    exact involution_unique3 hw hcl
  have hKu : Universal3 (conjClass3 K) z K := fun N' hN' hne =>
    (commutes_or_eq_of_involution3 hMFZ hΩ hex hP1 h3 D hKz hN' h.cls).resolve_right hne
  have hJu : Universal3 (conjClass3 K) w J := by
    rw [hwg, hg]
    exact universal3_conj hΩ.conjInvariant g z hKu
  have key : ∀ T : Subgroup G, T ∈ centralizingMembers (conjClass3 K) {z} →
      Universal3 (conjClass3 K) z T → T ∈ centralizingMembers (conjClass3 K) {w} →
        ¬ Universal3 (conjClass3 K) w T := by
    intro T hTz hTu hTw hTuw
    obtain ⟨wT, hwT⟩ := hΩ.classical T hTz.1
    have e1 : centralizingMembers (conjClass3 K) {wT} = centralizingMembers (conjClass3 K) {z} :=
      centralizingMembers_eq_of_twin3 hΩ h.cls hwT (exists_conj_of_mem3 hKΩ hTz.1) hTz hTu
    have e2 : centralizingMembers (conjClass3 K) {wT} = centralizingMembers (conjClass3 K) {w} :=
      centralizingMembers_eq_of_twin3 hΩ hw hwT (exists_conj_of_mem3 hJΩ hTz.1) hTw hTuw
    have hJ'w : J' ∈ centralizingMembers (conjClass3 K) {w} := by
      rw [← e2, e1]
      exact hJ'.1
    exact hnc (hJu J' hJ'w (Ne.symm hJJ'))
  have hT₂w : T₂ ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hT₂.1.1 hw.mem hcomm₂
  have hT₃w : T₃ ∈ centralizingMembers (conjClass3 K) {w} :=
    mem_centralizingMembers_of_commutes hT₃.1.1 hw.mem hcomm₃
  have hnu₂ := key T₂ hT₂.1 hu₂ hT₂w
  have hnu₃ := key T₃ hT₃.1 hu₃ hT₃w
  have back : ∀ T ∈ centralizingMembers (conjClass3 K) {w}, ¬ Universal3 (conjClass3 K) w T →
      ∃ T₀ ∈ centralizingMembers (conjClass3 K) {z}, ¬ Universal3 (conjClass3 K) z T₀ ∧
        T = conjSub g T₀ := by
    intro T hT hnu
    rw [hwg, centralizingMembers_conj hΩ.conjInvariant] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    refine ⟨T₀, hT₀, fun hu => hnu ?_, rfl⟩
    rw [hwg]
    exact universal3_conj hΩ.conjInvariant g z hu
  obtain ⟨T₂₀, hT₂₀, hnu₂₀, rfl⟩ := back T₂ hT₂w hnu₂
  obtain ⟨T₃₀, hT₃₀, hnu₃₀, rfl⟩ := back T₃ hT₃w hnu₃
  exact not_commutes_of_nonuniversal_m11 hΩ hex hP1 h3 D hk hrest hT₂₀ hT₃₀ hnu₂₀ hnu₃₀
    ((commutes_conjSub_iff g).mp hT₂₃c)

theorem shapePiece3_m11_of_two_le (h3 : OddThreeFreeInput) {a : ℕ} (ha : 2 ≤ a) :
    ShapePiece3 a CompData.m11 := by
  intro G _ _ _ hnab K z hR hshape
  exact (false_of_m11_two_a1_3 hR (h3 G K z hR) ha hshape).elim

theorem pieceM11₃_of_one (h3 : OddThreeFreeInput) (h1 : ShapePiece3 1 CompData.m11) :
    PieceM11₃ := by
  intro a
  rcases Nat.lt_or_ge a 2 with ha | ha
  · interval_cases a
    · exact shapePiece3_zero CompData.m11
    · exact h1
  · exact shapePiece3_m11_of_two_le h3 ha

end Main

end CFSG.ClassicalInvolution.Q3.Q3W
