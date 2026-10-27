module

public import CFSG.ClassicalInvolution.Asc77.AscE186CentA
public import CFSG.ClassicalInvolution.Asc77.AscSix63
public import CFSG.ClassicalInvolution.Asc77.AscT7ABasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

namespace T7A

omit [Finite G] in
theorem conjSub_eta_eq {S : Subgroup G} {η : Set (Subgroup G)}
    (hinv : ∀ s ∈ S, ∀ U ∈ η, conjSub s U ∈ η) {s : G} (hs : s ∈ S) :
    conjSub s (⨆ U ∈ η, U) = ⨆ U ∈ η, U := by
  have hle : ∀ {s : G}, s ∈ S → conjSub s (⨆ U ∈ η, U) ≤ ⨆ U ∈ η, U := by
    intro s hs
    unfold conjSub
    rw [Subgroup.map_iSup]
    refine iSup_le fun U => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hU => ?_
    exact le_iSup₂_of_le (conjSub s U) (hinv s hs U hU) le_rfl
  refine le_antisymm (hle hs) ?_
  have h2 := conjSub_mono (n := s) (hle (S.inv_mem hs))
  rwa [conjSub_conjSub_inv] at h2

omit [Finite G] in
theorem orderOf_eq_four_of_sq {K : Subgroup G} {z x : G} (hz : IsUniqueInvolution K z)
    (hx : x * x = z) : orderOf x = 4 := by
  have h1 : ¬ x ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, hx]
    exact hz.ne_one
  have h2 : x ^ 2 ^ (1 + 1) = 1 := by
    calc x ^ 2 ^ (1 + 1) = (x * x) * (x * x) := by simp [pow_succ, mul_assoc]
      _ = 1 := by rw [hx]; exact hz.sq
  have := orderOf_eq_prime_pow (p := 2) h1 h2
  rw [this]
  norm_num

end T7A

theorem exists_estand {K K' : Subgroup G} (hst : AscStand p f Ω K) (hK' : K' ∈ twinSet Ω K)
    (hne : K' ≠ K) :
    ∃ (S : Sylow 2 G) (R W : Subgroup G), EStand p f Ω K S R W := by
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  obtain ⟨z, hz⟩ := hΩ.exists_uniqueInvolution hp hq hK
  have hK'Ω : K' ∈ Ω := hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hK'
  obtain ⟨R₀, hR₀, -⟩ := IsSylow2In.exists_ge (isPGroup_two_bot (G := G)) (bot_le : ⊥ ≤ K)
  have hKN : K ≤ Subgroup.normalizer (K' : Set G) :=
    hΩ.le_normalizer_of_twin hK hK'Ω hne.symm hz hzK'
  obtain ⟨R', hR', hR'fix⟩ := exists_sylow_normalized hR₀.2.1 (hR₀.1.trans hKN)
  have hRn : R₀ ≤ Subgroup.normalizer (R' : Set G) := fun r hr =>
    mem_normalizer_iff_conjSub_eq.mpr (hR'fix r hr)
  have h2 : IsPGroup 2 ↥(R₀ ⊔ R') := hR₀.2.1.to_sup_of_normal_right' hR'.2.1 hRn
  obtain ⟨S, hS⟩ := h2.exists_le_sylow
  obtain ⟨η, hη, hηinv⟩ := exists_invariant_mem_etaSet hp hq hΩ S
  refine ⟨S, R₀, ⨆ U ∈ η, U, ?_⟩
  refine
    { odd := hp
      five := hq
      hyp := hΩ
      below := hst.below f hq
      mem := hK
      aEmpty := hst.aEmpty K hK
      twin := ⟨K', hK', hne, R', mem_RSet_of_isSylow2In hK'Ω hR', hR'.1,
        le_sup_right.trans hS⟩
      hR := ⟨mem_RSet_of_isSylow2In hK hR₀, hR₀.1, le_sup_left.trans hS⟩
      hW := ⟨⟨η, ⟨S, hη, hηinv⟩, rfl⟩, ?_, fun s hs => T7A.conjSub_eta_eq hηinv hs⟩ }
  exact iSup₂_le fun U hU => (hη.1 hU).2

structure StdCent (Ω : Set (Subgroup G)) (K H : Subgroup G) (z : G) : Prop where
  z_le : Subgroup.centralizer ({z} : Set G) ≤ H
  nonTwin : ∀ L ∈ twinSet Ω K, ∀ J ∈ omegaNbr Ω L, ∀ z' : G, IsUniqueInvolution J z' → z' ≠ z →
    Subgroup.centralizer ({z'} : Set G) ≤ H ∧ Subgroup.centralizer ({z * z'} : Set G) ≤ H
  twin : ∀ L ∈ twinSet Ω K, ∀ L' ∈ twinSet Ω K, L' ≠ L → ∀ R₁ R₂ : Subgroup G,
    IsSylow2In R₁ L → IsSylow2In R₂ L' → Commutes R₁ R₂ → ∀ x ∈ R₁, ∀ y ∈ R₂, orderOf x = 4 →
      orderOf y = 4 → Subgroup.centralizer ({x * y} : Set G) ≤ H

theorem centralizersSylowPairs_of_stdCent (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    {K H : Subgroup G} {z : G} (hz : IsUniqueInvolution K z) (h : StdCent Ω K H z) :
    CentralizersSylowPairs Ω K H := by
  intro L hL J hJ R₁ R₂ hR₁ hR₁L hR₂ hR₂J hcomm a ha ha1 ha2
  have hLΩ : L ∈ Ω := hL.1
  have hzL : IsUniqueInvolution L z := isUniqueInvolution_of_mem_twinSet hz hL
  have hR₁syl : IsSylow2In R₁ L := hΩ.isSylow2In_of_mem_RSet_of_le hp hLΩ hR₁ hR₁L
  rcases Set.mem_insert_iff.mp hJ with hJL | hJnbr
  ·
    have haL : a ∈ L := (sup_le hR₁L (hR₂J.trans hJL.le)) ha
    rcases hzL.unique a haL ha2 with h1 | h1
    · exact absurd h1 ha1
    · rw [h1]
      exact h.z_le
  · have hJΩ : J ∈ Ω := hJnbr.1
    have hJL : J ≠ L := hJnbr.2.1
    obtain ⟨z', hz'⟩ := hΩ.exists_uniqueInvolution hp hq hJΩ
    have hR₂syl : IsSylow2In R₂ J := hΩ.isSylow2In_of_mem_RSet_of_le hp hJΩ hR₂ hR₂J
    have hne : R₂ ≠ R₁ := by
      intro heq
      have h1 := hΩ.card_le_two_of_le_inf hLΩ hJΩ hJL.symm hR₁syl.2.1 hR₁L
        (by rw [← heq]; exact hR₂J)
      have h2 := hΩ.eight_le_of_mem_RSet hp hR₁
      omega
    have hc : Commutes R₁ R₂ := hcomm.resolve_right hne
    obtain ⟨x, hx, y, hy, rfl⟩ := AscE186.exists_mul_of_mem_sup_of_commutes hc ha
    have hcxy : x * y = y * x := hc x hx y hy
    have hsq : (x * x) * (y * y) = 1 := by
      calc (x * x) * (y * y) = x * (x * y) * y := by group
        _ = x * (y * x) * y := by rw [hcxy]
        _ = (x * y) * (x * y) := by group
        _ = 1 := ha2
    have hcard : Nat.card ↥(R₁ ⊓ R₂) ≤ 2 :=
      hΩ.card_le_two_of_le_inf hLΩ hJΩ hJL.symm (hR₁syl.2.1.to_le inf_le_left)
        (inf_le_left.trans hR₁L) (inf_le_right.trans hR₂J)
    have hA : ∀ e ∈ R₁ ⊓ R₂, e * e = 1 := by
      intro e he
      have hd : orderOf e ∣ Nat.card ↥(R₁ ⊓ R₂) := Subgroup.orderOf_dvd_natCard _ he
      have hpos : 0 < Nat.card ↥(R₁ ⊓ R₂) := Nat.card_pos
      have h2 : orderOf e ∣ 2 := by
        interval_cases hc2 : Nat.card ↥(R₁ ⊓ R₂)
        · exact hd.trans (one_dvd 2)
        · exact hd
      have := orderOf_dvd_iff_pow_eq_one.mp h2
      rwa [pow_two] at this
    have hxxA : x * x ∈ R₁ ⊓ R₂ := by
      refine ⟨R₁.mul_mem hx hx, ?_⟩
      have : x * x = (y * y)⁻¹ := eq_inv_of_mul_eq_one_left hsq
      rw [this]
      exact R₂.inv_mem (R₂.mul_mem hy hy)
    have hxx2 : (x * x) * (x * x) = 1 := hA _ hxxA
    have hxL : x ∈ L := hR₁L hx
    have hyJ : y ∈ J := hR₂J hy
    by_cases hzz : z' = z
    · have hzJ : IsUniqueInvolution J z := hzz ▸ hz'
      have hJtw : J ∈ twinSet Ω K := ⟨hJΩ, z, hz, hzJ⟩
      rcases hzL.unique (x * x) (L.mul_mem hxL hxL) hxx2 with hx2 | hx2
      · have hy2 : y * y = 1 := by rwa [hx2, one_mul] at hsq
        have hxz : x = 1 ∨ x = z := hzL.unique x hxL hx2
        have hyz : y = 1 ∨ y = z := hzJ.unique y hyJ hy2
        have hcase : x * y = z := by
          rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
          · exact absurd (by rw [h1, h2, one_mul]) ha1
          · rw [h1, h2, one_mul]
          · rw [h1, h2, mul_one]
          · exact absurd (by rw [h1, h2]; exact hz.sq) ha1
        rw [hcase]
        exact h.z_le
      · have hy2 : y * y = z := by
          have h1 : y * y = z⁻¹ := eq_inv_of_mul_eq_one_right (by rwa [hx2] at hsq)
          rw [h1]
          exact inv_eq_of_mul_eq_one_right hz.sq
        have hx4 : orderOf x = 4 := T7A.orderOf_eq_four_of_sq hz hx2
        have hy4 : orderOf y = 4 := T7A.orderOf_eq_four_of_sq hz hy2
        exact h.twin L hL J hJtw hJL R₁ R₂ hR₁syl hR₂syl hc x hx y hy hx4 hy4
    · have hx2 : x * x = 1 := by
        by_contra hne1
        have h1 : x * x = z := (hzL.unique _ (L.mul_mem hxL hxL) hxx2).resolve_left hne1
        have hxxJ : x * x ∈ J := hR₂J (Subgroup.mem_inf.mp hxxA).2
        have h2 : x * x = z' := (hz'.unique _ hxxJ hxx2).resolve_left hne1
        exact hzz (h2.symm.trans h1)
      have hy2 : y * y = 1 := by rwa [hx2, one_mul] at hsq
      have hxz : x = 1 ∨ x = z := hzL.unique x hxL hx2
      have hyz : y = 1 ∨ y = z' := hz'.unique y hyJ hy2
      obtain ⟨hC1, hC2⟩ := h.nonTwin L hL J hJnbr z' hz' hzz
      rcases hxz with h1 | h1 <;> rcases hyz with h2 | h2
      · exact absurd (by rw [h1, h2, one_mul]) ha1
      · rw [h1, h2, one_mul]
        exact hC1
      · rw [h1, h2, mul_one]
        exact h.z_le
      · rw [h1, h2]
        exact hC2

theorem thmE_apply (hE : ThmEWithSylow p f) {K K' : Subgroup G} {z : G} (hst : AscStand p f Ω K)
    (hz : IsUniqueInvolution K z) (hK' : K' ∈ twinSet Ω K) (hne : K' ≠ K) {H : Subgroup G}
    (hstd : StdCent Ω K H z)
    (htrans : ∀ J ∈ dstarComp Ω K, ∃ h ∈ H, conjSub h K = J) : H = ⊤ := by
  obtain ⟨S, R, W, hS⟩ := exists_estand hst hK' hne
  exact hE hst.odd hst.five G Ω K S R W H hS
    ⟨htrans, centralizersSylowPairs_of_stdCent hst.odd hst.five hst.hyp hz hstd⟩

end CFSG.ClassicalInvolution.Asc77
