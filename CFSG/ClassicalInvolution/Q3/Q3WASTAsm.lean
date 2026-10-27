module

public import CFSG.ClassicalInvolution.Q3.Q3WASTClosure
public import CFSG.ClassicalInvolution.Q3.Q3WASTImg
public import CFSG.ClassicalInvolution.Q3.Q3WANodes

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.Phan (UnitaryBlockStandardPair)

section Products

variable {G : Type} [Group G]

theorem le_centralizer_of_mul_left3 {N : Subgroup G} {a b : G}
    (h₁ : N ≤ Subgroup.centralizer ({a} : Set G))
    (h₂ : N ≤ Subgroup.centralizer ({a * b} : Set G)) :
    N ≤ Subgroup.centralizer ({b} : Set G) := by
  intro n hn
  have c₁ : Commute n a := Subgroup.mem_centralizer_singleton_iff.mp (h₁ hn)
  have c₂ : Commute n (a * b) := Subgroup.mem_centralizer_singleton_iff.mp (h₂ hn)
  have := c₁.inv_right.mul_right c₂
  rw [inv_mul_cancel_left] at this
  exact Subgroup.mem_centralizer_singleton_iff.mpr this

theorem le_centralizer_of_mul_right3 {N : Subgroup G} {a b : G}
    (h₁ : N ≤ Subgroup.centralizer ({b} : Set G))
    (h₂ : N ≤ Subgroup.centralizer ({a * b} : Set G)) :
    N ≤ Subgroup.centralizer ({a} : Set G) := by
  intro n hn
  have c₁ : Commute n b := Subgroup.mem_centralizer_singleton_iff.mp (h₁ hn)
  have c₂ : Commute n (a * b) := Subgroup.mem_centralizer_singleton_iff.mp (h₂ hn)
  have := c₂.mul_right c₁.inv_right
  rw [mul_inv_cancel_right] at this
  exact Subgroup.mem_centralizer_singleton_iff.mpr this

end Products

section Assembly

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem twin_condition_x3
    (hD1all : ∀ N ∈ Ω, ∀ u : G, IsClassicalMember3 N u → ∀ L ∈ centralizingMembers Ω {u},
      L ≠ N → Commutes N L)
    {K j₀ : Subgroup G} {z w₀ x : G} (hK : K ∈ Ω) (hj₀ : j₀ ∈ Ω)
    (hz : IsClassicalMember3 K z) (hw₀ : IsClassicalMember3 j₀ w₀)
    (hKj₀ : Commutes K j₀) (hx : z * w₀ = x) :
    ∀ N ∈ centralizingMembers Ω {x}, (N = K ∨ Commutes N K) ↔ (N = j₀ ∨ Commutes N j₀) := by
  intro N hN
  constructor
  · rintro (h | hc)
    · rw [h]
      exact Or.inr hKj₀
    · have h₁ : N ≤ Subgroup.centralizer ({z} : Set G) := le_centralizer_of_commutes3 hc hz.mem
      have h₂ : N ≤ Subgroup.centralizer ({z * w₀} : Set G) := by
        rw [hx]
        exact hN.2
      have h₃ := le_centralizer_of_mul_left3 h₁ h₂
      by_cases hNj : N = j₀
      · exact Or.inl hNj
      · exact Or.inr (hD1all j₀ hj₀ w₀ hw₀ N ⟨hN.1, h₃⟩ hNj).symm
  · rintro (h | hc)
    · rw [h]
      exact Or.inr hKj₀.symm
    · have h₃ : N ≤ Subgroup.centralizer ({w₀} : Set G) := le_centralizer_of_commutes3 hc hw₀.mem
      have h₂ : N ≤ Subgroup.centralizer ({z * w₀} : Set G) := by
        rw [hx]
        exact hN.2
      have h₁ := le_centralizer_of_mul_right3 h₃ h₂
      by_cases hNK : N = K
      · exact Or.inl hNK
      · exact Or.inr (hD1all K hK z hz N ⟨hN.1, h₁⟩ hNK).symm

theorem centralizes_layer3 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hΩ : InClass3 Ω) (hconn : RouteD.DeltaConnected Ω)
    {K : Subgroup G} (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → Commutes K L)
    {j₀ j₁ : Subgroup G} {w₀ w₁ : G} (hj₀ : j₀ ∈ Ω) (hj₁ : j₁ ∈ Ω)
    (hw₀ : IsClassicalMember3 j₀ w₀) (hw₁ : IsClassicalMember3 j₁ w₁)
    (hKj₀ : Commutes K j₀) (hKj₁ : Commutes K j₁) (hnc : ¬ Commutes j₀ j₁)
    (hw₀w₁ : w₀ * w₁ = w₁ * w₀) (hlayer : ∀ N ∈ Ω, Commutes K N → N ≤ j₀ ⊔ j₁)
    (hnorm : conjSub w₀ j₁ = j₁)
    (hdich : ∀ t : G, t * w₁ * t⁻¹ = w₁ → t * t = 1 → K ≤ Subgroup.centralizer ({t} : Set G) →
      conjSub t j₁ = j₁ →
      (∀ N ∈ centralizingMembers Ω {w₁}, N ≠ j₁ → N ≤ Subgroup.centralizer ({t} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {w₁}, N ≠ j₁ →
        N ≤ Subgroup.centralizer ({t * z} : Set G))) :
    ∀ N ∈ centralizingMembers Ω {w₁}, N ≠ j₁ →
      N ≤ Subgroup.centralizer ({z * w₀} : Set G) := by
  have hD1all : ∀ N ∈ Ω, ∀ u : G, IsClassicalMember3 N u → ∀ L ∈ centralizingMembers Ω {u},
      L ≠ N → Commutes N L := fun N hN u hu L hL hLN =>
    commutes_of_centralizing3 hΩ hsingle hz hD1 hN hu hL hLN
  have hzz : z * z = 1 := mul_self_of_isClassicalMember3 hz
  have hww₀ : w₀ * w₀ = 1 := mul_self_of_isClassicalMember3 hw₀
  have hzw₀ : z * w₀ = w₀ * z := hKj₀ z hz.mem w₀ hw₀.mem
  have hzw₁ : z * w₁ = w₁ * z := hKj₁ z hz.mem w₁ hw₁.mem
  have htw₁ : (z * w₀) * w₁ * (z * w₀)⁻¹ = w₁ := by
    rw [mul_inv_eq_iff_eq_mul]
    calc z * w₀ * w₁ = z * (w₀ * w₁) := by rw [mul_assoc]
      _ = z * (w₁ * w₀) := by rw [hw₀w₁]
      _ = (z * w₁) * w₀ := by rw [mul_assoc]
      _ = (w₁ * z) * w₀ := by rw [hzw₁]
      _ = w₁ * (z * w₀) := by rw [mul_assoc]
  have htt : (z * w₀) * (z * w₀) = 1 := by
    calc z * w₀ * (z * w₀) = z * (w₀ * z) * w₀ := by group
      _ = z * (z * w₀) * w₀ := by rw [← hzw₀]
      _ = (z * z) * (w₀ * w₀) := by group
      _ = 1 := by rw [hzz, hww₀, one_mul]
  have hKt : K ≤ Subgroup.centralizer ({z * w₀} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k z :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hz.subnormal hk)
    have c₂ : Commute k w₀ := hKj₀ k hk w₀ hw₀.mem
    exact c₁.mul_right c₂
  have hjt : conjSub (z * w₀) j₁ = j₁ := by
    rw [conjSub_mul, hnorm]
    exact conjSub_eq_of_mem_of_commutes hz.mem hKj₁
  rcases hdich (z * w₀) htw₁ htt hKt hjt with h | h
  · exact h
  · exfalso
    have htz : z * w₀ * z = w₀ := by
      calc z * w₀ * z = z * (w₀ * z) := by rw [mul_assoc]
        _ = z * (z * w₀) := by rw [← hzw₀]
        _ = (z * z) * w₀ := by rw [mul_assoc]
        _ = w₀ := by rw [hzz, one_mul]
    refine false_of_nbhd_subset3 hnab hΩ hconn hsingle hz hD1 hK hj₀ hj₁ hKj₀ hlayer ?_
    intro N hN hc
    have hNw₁ : N ∈ centralizingMembers Ω {w₁} :=
      ⟨hN, le_centralizer_of_commutes3 hc.symm hw₁.mem⟩
    have hNj₁ : N ≠ j₁ := fun h' => not_commutes_self3 hw₁ (h' ▸ hc)
    have hNw₀ : N ≤ Subgroup.centralizer ({w₀} : Set G) := by
      have := h N hNw₁ hNj₁
      rwa [htz] at this
    have hNj₀ : N ≠ j₀ := fun h' => hnc (h' ▸ hc).symm
    exact hD1all j₀ hj₀ w₀ hw₀ N ⟨hN, hNw₀⟩ hNj₀

end Assembly

section LocAut

variable {G : Type} [Group G] {Ω : Set (Subgroup G)}

theorem map_conjSub_hom3 {X : Type*} [Group X] (ψ : G →* X) (g : G) (H : Subgroup G) :
    (conjSub g H).map ψ = conjSub (ψ g) (H.map ψ) := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem locAut_eq_conj3 (hΩ : ConjInvariant Ω) {w z : G} (hzY : z ∈ locLayer Ω w)
    (hzw : z * w * z⁻¹ = w) (a : locQuot Ω w) :
    locAut hΩ hzw a = locMk Ω w ⟨z, hzY⟩ * a * (locMk Ω w ⟨z, hzY⟩)⁻¹ := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ a
  rw [locAut_mk, ← map_inv, ← map_mul, ← map_mul]
  congr 1

theorem locAut_mul3 (hΩ : ConjInvariant Ω) {w t z : G} (ht : t * w * t⁻¹ = w)
    (hz : z * w * z⁻¹ = w) (htz : (t * z) * w * (t * z)⁻¹ = w) (a : locQuot Ω w) :
    locAut hΩ htz a = locAut hΩ ht (locAut hΩ hz a) := by
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective _ a
  rw [locAut_mk, locAut_mk, locAut_mk]
  congr 1
  apply Subtype.ext
  rw [coe_layerAut, coe_layerAut, coe_layerAut]
  group

theorem locImg_sup3 {x : G} {A B : Subgroup G} (hA : A ≤ locLayer Ω x) (hB : B ≤ locLayer Ω x) :
    locImg Ω x (A ⊔ B) = locImg Ω x A ⊔ locImg Ω x B := by
  unfold locImg
  rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hA hB]

end LocAut

section Chain

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_twin_chain3 [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a)
    (hΩ : InClass3 Ω) (hconn : RouteD.DeltaConnected Ω) (hex : ExactMembers3 Ω)
    (hIH : LocalLieSystems3 Ω) {K : Subgroup G} (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (hK : K ∈ Ω) {z : G} (hz : IsClassicalMember3 K z)
    (hD1 : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → Commutes K L)
    {j₀ j₁ : Subgroup G} {w₀ w₁ : G} (hj₀ : j₀ ∈ Ω) (hj₁ : j₁ ∈ Ω)
    (hw₀ : IsClassicalMember3 j₀ w₀) (hw₁ : IsClassicalMember3 j₁ w₁) (hj₀K : j₀ ≠ K)
    (hj₀j₁ : j₀ ≠ j₁) (hKj₀ : Commutes K j₀) (hKj₁ : Commutes K j₁) (hnc : ¬ Commutes j₀ j₁)
    (hw₀w₁ : w₀ * w₁ = w₁ * w₀) (hlayer : ∀ N ∈ Ω, Commutes K N → N ≤ j₀ ⊔ j₁)
    (hnorm : conjSub w₀ j₁ = j₁)
    (hdich : ∀ t : G, t * w₁ * t⁻¹ = w₁ → t * t = 1 → K ≤ Subgroup.centralizer ({t} : Set G) →
      conjSub t j₁ = j₁ →
      (∀ N ∈ centralizingMembers Ω {w₁}, N ≠ j₁ → N ≤ Subgroup.centralizer ({t} : Set G)) ∨
      (∀ N ∈ centralizingMembers Ω {w₁}, N ≠ j₁ →
        N ≤ Subgroup.centralizer ({t * z} : Set G)))
    (hP1x : LocalOddCentral Ω {z * w₀}) (hO3x : LocalOddThreeFree3 Ω (z * w₀))
    {β : Subgroup G} {v : G}
    (hβ : β ∈ centralizingMembers Ω {w₁}) (hβj₁ : β ≠ j₁) (hv : IsClassicalMember3 β v)
    (hnKβ : ¬ Commutes K β) (hKβ : K ≠ β) (hvK : conjSub v K = K)
    (hpair₀₁ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hpair₂₃ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W j₀ j₁) :
    ∃ U : Fin 4 → Subgroup G, (∀ i, U i ∈ Ω) ∧
      (∀ i j : Fin 4, (i : ℕ) + 1 < j → Commutes (U i) (U j)) ∧
      ∀ i j : Fin 4, (j : ℕ) = i + 1 →
        ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (U i) (U j) := by
  have hD1all : ∀ N ∈ Ω, ∀ u : G, IsClassicalMember3 N u → ∀ L ∈ centralizingMembers Ω {u},
      L ≠ N → Commutes N L := fun N hN u hu L hL hLN =>
    commutes_of_centralizing3 hΩ hsingle hz hD1 hN hu hL hLN
  have hlay := centralizes_layer3 hnab hΩ hconn hsingle hK hz hD1 hj₀ hj₁ hw₀ hw₁ hKj₀ hKj₁ hnc
    hw₀w₁ hlayer hnorm hdich
  have hzw₀ : z * w₀ = w₀ * z := hKj₀ z hz.mem w₀ hw₀.mem
  have hzw : z ≠ w₀ := by
    intro h
    have hj₁w₀ : j₁ ∈ centralizingMembers Ω {w₀} :=
      ⟨hj₁, h ▸ le_centralizer_of_commutes3 hKj₁.symm hz.mem⟩
    exact hnc (hD1all j₀ hj₀ w₀ hw₀ j₁ hj₁w₀ hj₀j₁.symm)
  have hKx : K ∈ centralizingMembers Ω {z * w₀} := by
    refine ⟨hK, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k z :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hz.subnormal hk)
    have c₂ : Commute k w₀ := hKj₀ k hk w₀ hw₀.mem
    exact c₁.mul_right c₂
  have hMx : j₀ ∈ centralizingMembers Ω {z * w₀} := by
    refine ⟨hj₀, fun k hk => ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have c₁ : Commute k z :=
      Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_commutes3 hKj₀.symm hz.mem hk)
    have c₂ : Commute k w₀ :=
      Subgroup.mem_centralizer_singleton_iff.mp (isSubnormal_le hw₀.subnormal hk)
    exact c₁.mul_right c₂
  have hβx : β ∈ centralizingMembers Ω {z * w₀} := ⟨hβ.1, hlay β hβ hβj₁⟩
  have hx2 : orderOf (z * w₀) = 2 :=
    orderOf_mul_of_commute_involutions hz.orderOf_eq_two hw₀.orderOf_eq_two hzw₀ hzw
  have hxc : ¬ ({z * w₀} : Set G) ⊆ Subgroup.center G := by
    intro hsub
    have h' : z * w₀ ∈ Subgroup.center G := hsub (Set.mem_singleton _)
    rw [CoreAssembly.center_eq_bot hnab, Subgroup.mem_bot] at h'
    rw [h', orderOf_one] at hx2
    omega
  have hβw₁ : Commutes j₁ β := hD1all j₁ hj₁ w₁ hw₁ β hβ hβj₁
  have hβj₀ : β ≠ j₀ := by
    intro h
    have : j₀ ∈ centralizingMembers Ω {w₁} := h ▸ hβ
    exact hnc (hD1all j₁ hj₁ w₁ hw₁ j₀ this hj₀j₁).symm
  have hnβM : ¬ Commutes β j₀ := by
    intro hc
    have h₁ : β ≤ Subgroup.centralizer ({w₀} : Set G) := le_centralizer_of_commutes3 hc hw₀.mem
    have h₂ : β ≤ Subgroup.centralizer ({z * w₀} : Set G) := hβx.2
    have h₃ := le_centralizer_of_mul_right3 h₁ h₂
    exact hnKβ (hD1 β ⟨hβ.1, h₃⟩ hKβ.symm)
  have htwin := twin_condition_x3 hD1all hK hj₀ hz hw₀ hKj₀ rfl
  have hs := chainSign_images3 hΩ hex hIH hxc hP1x hO3x hz hv hw₀ hKx hβx hMx rfl hzw hKj₀
    hj₀K.symm hKβ hβj₀ hnKβ hnβM hvK htwin
  have hpair₁₂ := linear_of_chainSign_images3 hΩ hex hP1x hO3x hKx hβx hMx hs hpair₀₁
  refine ⟨![K, β, j₀, j₁], ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    exacts [hK, hβ.1, hj₀, hj₁]
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hKj₀
    · exact hKj₁
    · exact hβw₁.symm
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact hpair₀₁
    · exact hpair₁₂
    · exact hpair₂₃

end Chain

end CFSG.ClassicalInvolution.Q3.Q3W
