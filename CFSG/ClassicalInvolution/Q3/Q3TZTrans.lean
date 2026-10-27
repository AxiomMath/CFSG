module

public import CFSG.ClassicalInvolution.Q3.Q3TIYAtT

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TZ

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TIV
open CFSG.ClassicalInvolution.RouteD.TwinY (IsTwinAt)

section Lifting

theorem le_of_le_sup_central_of_exponent {Y : Type} [Group Y] {N B O : Subgroup Y}
    (hO : O ≤ Subgroup.center Y) (hcop : ∀ o ∈ O, Nat.Coprime (orderOf o) 6)
    (hN : ∀ l ∈ N, l ^ 12 = 1) (h : N ≤ B ⊔ O) : N ≤ B := by
  have : O.Normal := ⟨fun n hn g => by
    have h1 := Subgroup.mem_center_iff.mp (hO hn) g
    rwa [h1, mul_inv_cancel_right]⟩
  intro l hl
  obtain ⟨b, hb, o, ho, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp (h hl)
  have hoc : Commute b o := Subgroup.mem_center_iff.mp (hO ho) b
  have h12 : (b * o) ^ 12 = 1 := hN _ hl
  rw [hoc.mul_pow] at h12
  have ho12 : o ^ 12 = (b ^ 12)⁻¹ := eq_inv_of_mul_eq_one_right h12
  have hmemB : o ^ 12 ∈ B := by
    rw [ho12]
    exact B.inv_mem (B.pow_mem hb 12)
  have hc12 : Nat.Coprime 12 (orderOf o) := by
    have h36 : Nat.Coprime (orderOf o) (6 ^ 2) := Nat.Coprime.pow_right 2 (hcop o ho)
    exact (Nat.Coprime.coprime_dvd_right (by norm_num) h36).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hc12
  have hoB : o ∈ B := by
    rw [← hm]
    exact B.pow_mem hmemB m
  exact B.mul_mem hb hoB

theorem coprime_six_of_mem_oddCore3 {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {x : G}
    (hO3 : LocalOddThreeFree3 Ω x) {o : ↥(locLayer Ω x)}
    (ho : o ∈ classicalInvolutionOddCore ↥(locLayer Ω x)) : Nat.Coprime (orderOf o) 6 := by
  have hodd : Odd (Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x))) :=
    CFSG.ComponentClassification.OddCore.odd_card _
  have hdvd : orderOf o ∣ Nat.card (classicalInvolutionOddCore ↥(locLayer Ω x)) := by
    have := orderOf_dvd_natCard (⟨o, ho⟩ : classicalInvolutionOddCore ↥(locLayer Ω x))
    rwa [Subgroup.orderOf_mk] at this
  have h2 : ¬ 2 ∣ orderOf o := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h.trans hdvd))
  have h3 : ¬ 3 ∣ orderOf o := fun h => hO3 (h.trans hdvd)
  have c2 : Nat.Coprime (orderOf o) 2 := ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
  have c3 : Nat.Coprime (orderOf o) 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
  exact Nat.Coprime.mul_right c2 c3

end Lifting

section Trans

variable {G : Type} [Group G] [Finite G] {K T J : Subgroup G} {z t : G} {tY : StatedLieTag}
  {nY : ℕ}


theorem conjSub_mem_cm3 {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {x : G} {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {y : G} (hy : y ∈ locLayer Ω x) :
    conjSub y L ∈ centralizingMembers Ω {x} := by
  have hyx : y ∈ Subgroup.centralizer ({x} : Set G) :=
    centralizingLayer_le_centralizer Ω {x} hy
  refine ⟨hΩ _ L hL.1, fun a ha => ?_⟩
  rw [mem_conjSub_iff] at ha
  have hx' := hL.2 ha
  have : a = y * (y⁻¹ * a * y) * y⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyx hx') ((Subgroup.inv_mem _) hyx)

theorem link_big'3 {Ω : Set (Subgroup G)} {x : G} (c : TwinLoc3 tY nY Ω x)
    {K T L L' : Subgroup G} (hK : K ∈ centralizingMembers Ω {x})
    (hT : T ∈ centralizingMembers Ω {x}) (hKT : K ≠ T)
    (hKiso : ∀ L'' ∈ centralizingMembers Ω {x}, L'' ≠ K → Commutes K L'')
    (hTiso : ∀ L'' ∈ centralizingMembers Ω {x}, L'' ≠ T → Commutes T L'')
    (hL : L ∈ centralizingMembers Ω {x}) (hLK : L ≠ K) (hLT : L ≠ T)
    (hL' : L' ∈ centralizingMembers Ω {x}) (hL'K : L' ≠ K) (hL'T : L' ≠ T) :
    ∃ y : G, ∃ hy : y ∈ locLayer Ω x, conjSub y L = L' ∧
      Gaps.locMk Ω x ⟨y, hy⟩ ∈ c.d.ψ.range := by
  obtain ⟨R, hR, hLR⟩ := c.big_of_ne hK hT hKT hKiso hTiso hL hLK hLT
  obtain ⟨R', hR', hLR'⟩ := c.big_of_ne hK hT hKT hKiso hTiso hL' hL'K hL'T
  obtain ⟨g, hg⟩ := c.rf.y.sc R hR R' hR'
  have hg' : R' = R.map (MulAut.conj g).toMonoidHom := hg
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (c.d.ψ g)
  have hconj : conjSub (y : G) L ∈ centralizingMembers Ω {x} :=
    conjSub_mem_cm3 c.hΩ.conjInvariant hL y.2
  refine ⟨(y : G), y.2, locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hconj hL' ?_, ⟨g, hy.symm⟩⟩
  rw [Gaps.locImg_conjSub_layer, hLR, hLR', show Gaps.locMk Ω x y = c.d.ψ g from hy, hg']
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem locImg_conjSub_eq3 (A : AtT3 K T J z t tY nY) {y : G}
    (hy : y ∈ locLayer (conjClass3 K) t) {k : (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hk : A.c.d.ψ k = Gaps.locMk (conjClass3 K) t ⟨y, hy⟩) :
    locImg (conjClass3 K) t (conjSub y K) = (conjSub k A.RK).map A.c.d.ψ := by
  rw [Gaps.locImg_conjSub_layer K ⟨y, hy⟩, A.hKR, ← hk]
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext a
  simp

theorem conjSub_eq_of_stab3 (A : AtT3 K T J z t tY nY) {y : G}
    (hy : y ∈ locLayer (conjClass3 K) t) {k : (modelUniv tY nY 3 1 Nat.prime_three).K}
    (hk : A.c.d.ψ k = Gaps.locMk (conjClass3 K) t ⟨y, hy⟩)
    (hkS : k ∈ G2D4Models.conjStabilizer
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K))) :
    conjSub y K = K ∨ conjSub y K = T := by
  have himg := locImg_conjSub_eq3 A hy hk
  have hconj : conjSub y K ∈ centralizingMembers (conjClass3 K) {t} :=
    conjSub_mem_cm3 A.c.hΩ.conjInvariant A.hKt hy
  have hkR : conjSub k A.RK ∈
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)) :=
    (G2D4Models.mem_conjStabilizer_iff.mp hkS A.RK).mpr (Set.mem_insert _ _)
  rcases hkR with h | h
  · left
    rw [h] at himg
    exact locImg_injOn3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hconj A.hKt (himg.trans A.hKR.symm)
  · right
    rw [h] at himg
    exact locImg_injOn3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hconj A.hTt (himg.trans A.hTR.symm)

theorem transfer_max3 (A : AtT3 K T J z t tY nY)
    (hMax : IsCoatom (G2D4Models.conjStabilizer
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K))))
    (𝒩 : Subgroup G)
    (hN : ∀ y ∈ locLayer (conjClass3 K) t, (conjSub y K = K ∨ conjSub y K = T) → y ∈ 𝒩) :
    (∀ N ∈ centralizingMembers (conjClass3 K) {t}, N ≠ J → N ≠ A.J₂ → N ≤ 𝒩) ∨
      ∀ y ∈ 𝒩, ∀ hy : y ∈ locLayer (conjClass3 K) t,
        Gaps.locMk (conjClass3 K) t ⟨y, hy⟩ ∈ A.c.d.ψ.range →
          conjSub y K = K ∨ conjSub y K = T := by
  classical
  set Yt : Subgroup G := locLayer (conjClass3 K) t with hYt
  set 𝒩' : Subgroup ↥Yt := 𝒩.subgroupOf Yt with h𝒩'
  set Sd : Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K :=
    (𝒩'.map (Gaps.locMk (conjClass3 K) t)).comap A.c.d.ψ with hSd
  have hP : G2D4Models.conjStabilizer
      ({A.RK, A.RT} : Set (Subgroup (modelUniv tY nY 3 1 Nat.prime_three).K)) ≤ Sd := by
    intro k hk
    obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (A.c.d.ψ k)
    have hyk : A.c.d.ψ k = Gaps.locMk (conjClass3 K) t y := hy.symm
    have hyK := conjSub_eq_of_stab3 A (y := (y : G)) y.2 (k := k) hyk hk
    have hy𝒩 : (y : G) ∈ 𝒩 := hN y y.2 hyK
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy𝒩, hy⟩
  rcases hMax.le_iff.mp hP with htop | hnorm
  · left
    intro N hNΩ hNJ hNJ₂
    obtain ⟨R, hR, hNR⟩ := A.c.big_of_ne A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso hNΩ hNJ hNJ₂
    obtain ⟨zN, hzN⟩ := A.c.hΩ.classical N hNΩ.1
    obtain ⟨e⟩ := hzN.nonempty_equiv_sl2 (A.c.hex N hNΩ.1)
    have hN12 : ∀ l ∈ N.subgroupOf Yt, l ^ 12 = 1 := by
      intro l hl
      have h1 := pow_twelve_of_equiv_sl2Three e ⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩
      apply Subtype.ext
      simpa using congrArg Subtype.val h1
    have hle : N.subgroupOf Yt ≤ 𝒩' ⊔ classicalInvolutionOddCore ↥Yt := by
      intro a ha
      have ha' : Gaps.locMk (conjClass3 K) t a ∈ locImg (conjClass3 K) t N := ⟨a, ha, rfl⟩
      rw [hNR] at ha'
      obtain ⟨k₀, -, hk₀⟩ := Subgroup.mem_map.mp ha'
      have hk₀S : k₀ ∈ Sd := by rw [htop]; trivial
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hk₀S
      have hmem : b⁻¹ * a ∈ classicalInvolutionOddCore ↥Yt :=
        QuotientGroup.eq.mp (hba.trans hk₀)
      have : a = b * (b⁻¹ * a) := by group
      rw [this]
      exact Subgroup.mul_mem_sup hb hmem
    have hNle := le_of_le_sup_central_of_exponent A.c.hP1
      (fun o ho => coprime_six_of_mem_oddCore3 A.c.hO3 ho) hN12 hle
    intro n hn
    have hnY : n ∈ Yt := le_centralizingLayer hNΩ hn
    have h1 : (⟨n, hnY⟩ : ↥Yt) ∈ N.subgroupOf Yt := Subgroup.mem_subgroupOf.mpr hn
    exact Subgroup.mem_subgroupOf.mp (hNle h1)
  · right
    intro y hy𝒩 hyY hyψ
    obtain ⟨k, hk⟩ := hyψ
    have hkS : k ∈ Sd := by
      show A.c.d.ψ k ∈ 𝒩'.map (Gaps.locMk (conjClass3 K) t)
      rw [hk]
      exact ⟨⟨y, hyY⟩, Subgroup.mem_subgroupOf.mpr hy𝒩, rfl⟩
    rw [hnorm] at hkS
    exact conjSub_eq_of_stab3 A hyY hk hkS

end Trans

end CFSG.ClassicalInvolution.Q3.Q3TZ
