module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.Permutable
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Escape

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_le_of_isSylow {p : ℕ} [Fact p.Prime] {H S X : Subgroup G}
    (hS : ∃ T : Sylow p H, (T : Subgroup H).map H.subtype = S) (hXH : X ≤ H)
    (hX : IsPGroup p X) : ∃ h ∈ H, X.map (MulAut.conj h).toMonoidHom ≤ S := by
  obtain ⟨T, rfl⟩ := hS
  have hXp : IsPGroup p (X.subgroupOf H) := hX.comap_subtype
  obtain ⟨T', hT'⟩ := hXp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H T' T
  refine ⟨c, c.2, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have hxH : x ∈ H := hXH hx
  have hxT' : (⟨x, hxH⟩ : H) ∈ T' := hT' hx
  have hconj : c * ⟨x, hxH⟩ * c⁻¹ ∈ ((c • T' : Sylow p H) : Set H) := by
    rw [@Sylow.coe_smul p H _ c T']
    exact ⟨⟨x, hxH⟩, hxT', rfl⟩
  rw [hc] at hconj
  exact ⟨c * ⟨x, hxH⟩ * c⁻¹, hconj, rfl⟩

theorem eq_of_card_eq_prime_of_pRank_le_one {p : ℕ} (hp : p.Prime) {S Y P : Subgroup G}
    (hS : IsPGroup p S) (hrank : pRank p S ≤ 1) (hYS : Y ≤ S) (hPS : P ≤ S)
    (hY : Nat.card Y = p) (hP : Nat.card P = p) : Y = P := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hYne : Y ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hY
    exact hp.one_lt.ne hY
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hYne
  have : Nontrivial S := ⟨⟨⟨(a : G), hYS a.2⟩, 1, fun h => ha (Subtype.ext (by simpa using congrArg (fun x : ↥S => (x : G)) h))⟩⟩
  have hZ : IsPGroup p (Subgroup.center ↥S) := hS.to_subgroup _
  have := hS.center_nontrivial
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : Nat.card (Subgroup.center ↥S) = 1 := by simpa using hn
    exact (not_subsingleton (Subgroup.center ↥S)) (Nat.card_eq_one_iff_unique.mp this).1
  have hdvd : p ∣ Nat.card (Subgroup.center ↥S) := by
    rw [hn]; exact dvd_pow_self p hn0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥S) p hdvd
  set zG : G := ((z : S) : G) with hzG
  have hzord : orderOf zG = p := by
    have h1 : orderOf (z : S) = p := by rw [← hz]; exact (Subgroup.orderOf_coe z)
    rw [hzG, Subgroup.orderOf_coe (z : S), h1]
  set Z₁ : Subgroup G := Subgroup.zpowers zG with hZ₁
  have hZ₁card : Nat.card Z₁ = p := by rw [hZ₁, Nat.card_zpowers, hzord]
  have hZ₁S : Z₁ ≤ S := (Subgroup.zpowers_le).mpr (z : S).2
  have hcentral : ∀ s ∈ S, s * zG = zG * s := by
    intro s hs
    have := Subgroup.mem_center_iff.mp z.2 ⟨s, hs⟩
    exact congrArg Subtype.val this
  have key : ∀ W : Subgroup G, W ≤ S → Nat.card W = p → W = Z₁ := by
    intro W hWS hW
    by_contra hne
    have hinf : W ⊓ Z₁ = ⊥ := by
      by_contra hbot
      have hd : Nat.card (W ⊓ Z₁ : Subgroup G) ∣ p := hW ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime hp).mp hd with h1 | h1
      · exact hbot (Subgroup.eq_bot_of_card_eq _ h1)
      · apply hne
        have h2 : W ⊓ Z₁ = W := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hW])
        have h3 : W ⊓ Z₁ = Z₁ := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h1, hZ₁card])
        rw [← h2, h3]
    have hcomm : ∀ w ∈ W, ∀ x ∈ Z₁, w * x = x * w := by
      intro w hw x hx
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.zpow_right (show Commute w zG from hcentral w (hWS hw)) m))
    have hperm : (W : Set G) * (Z₁ : Set G) = (Z₁ : Set G) * (W : Set G) := by
      ext x
      constructor
      · rintro ⟨w, hw, y, hy, rfl⟩
        exact ⟨y, hy, w, hw, (hcomm w hw y hy).symm⟩
      · rintro ⟨y, hy, w, hw, rfl⟩
        exact ⟨w, hw, y, hy, hcomm w hw y hy⟩
    have hcard := card_sup_of_permutable hperm hinf
    rw [hW, hZ₁card] at hcard
    have hcoe := coe_sup_eq_mul_of_permutable hperm
    have hWp : ∀ w ∈ W, w ^ p = 1 := by
      intro w hw
      have := pow_card_eq_one' (G := W) (x := ⟨w, hw⟩)
      rw [hW] at this
      exact congrArg Subtype.val this
    have hZp : ∀ x ∈ Z₁, x ^ p = 1 := by
      intro x hx
      have := pow_card_eq_one' (G := Z₁) (x := ⟨x, hx⟩)
      rw [hZ₁card] at this
      exact congrArg Subtype.val this
    have hWcomm : ∀ w w' : G, w ∈ W → w' ∈ W → w * w' = w' * w := by
      intro w w' hw hw'
      have hcyc : IsCyclic W := isCyclic_of_prime_card hW
      letI : CommGroup W := IsCyclic.commGroup
      exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : W) ⟨w', hw'⟩)
    have hZcomm : ∀ x x' : G, x ∈ Z₁ → x' ∈ Z₁ → x * x' = x' * x := by
      intro x x' hx hx'
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      obtain ⟨m', rfl⟩ := Subgroup.mem_zpowers_iff.mp hx'
      exact (Commute.zpow_zpow_self zG m m')
    have hE : IsElemAbelian p (W ⊔ Z₁) := by
      refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      · have ha : (a : G) ∈ (W : Set G) * (Z₁ : Set G) := hcoe ▸ a.2
        have hb : (b : G) ∈ (W : Set G) * (Z₁ : Set G) := hcoe ▸ b.2
        obtain ⟨w, hw, x, hx, hax⟩ := ha
        obtain ⟨w', hw', x', hx', hbx⟩ := hb
        apply Subtype.ext
        show (a : G) * (b : G) = (b : G) * (a : G)
        rw [← hax, ← hbx]
        calc w * x * (w' * x') = w * (x * w') * x' := by simp only [mul_assoc]
          _ = w * (w' * x) * x' := by rw [← hcomm w' hw' x hx]
          _ = (w * w') * (x * x') := by simp only [mul_assoc]
          _ = (w' * w) * (x' * x) := by rw [hWcomm w w' hw hw', hZcomm x x' hx hx']
          _ = w' * (w * x') * x := by simp only [mul_assoc]
          _ = w' * (x' * w) * x := by rw [hcomm w hw x' hx']
          _ = w' * x' * (w * x) := by simp only [mul_assoc]
      · have hx' : x ∈ (W : Set G) * (Z₁ : Set G) := hcoe ▸ hx
        obtain ⟨w, hw, y, hy, rfl⟩ := hx'
        have hc := hcomm w hw y hy
        rw [Commute.mul_pow (show Commute w y from hc), hWp w hw, hZp y hy, one_mul]
    have h2 : 2 ≤ pRank p (W ⊔ Z₁) := by
      refine CFSG.AGLEmbeddingD2.le_pRank_of_isElemAbelian hp hE ?_
      rw [hcard]; ring
    have h3 : pRank p (W ⊔ Z₁) ≤ pRank p S :=
      pRank_mono p hp (sup_le hWS hZ₁S)
    omega
  rw [key Y hYS hY, key P hPS hP]

theorem exists_conj_of_pRank_le_one {p : ℕ} (hp : p.Prime) {H Y P : Subgroup G}
    (hrank : pRank p H ≤ 1) (hYH : Y ≤ H) (hPH : P ≤ H) (hY : Nat.card Y = p)
    (hP : Nat.card P = p) : ∃ h ∈ H, Y.map (MulAut.conj h).toMonoidHom = P := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPp : IsPGroup p (P.subgroupOf H) := by
    have : IsPGroup p P := by
      rw [IsPGroup.iff_card]; exact ⟨1, by rw [hP]; simp⟩
    exact this.comap_subtype
  obtain ⟨T, hT⟩ := hPp.exists_le_sylow
  set S : Subgroup G := (T : Subgroup H).map H.subtype with hS
  have hSH : S ≤ H := Subgroup.map_subtype_le _
  have hSp : IsPGroup p S := T.isPGroup'.map H.subtype
  have hPS : P ≤ S := by
    intro x hx
    exact ⟨⟨x, hPH hx⟩, hT hx, rfl⟩
  have hYp : IsPGroup p Y := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [hY]; simp⟩
  obtain ⟨h, hhH, hh⟩ := exists_conj_le_of_isSylow (p := p) (H := H) (S := S) ⟨T, rfl⟩ hYH hYp
  refine ⟨h, hhH, ?_⟩
  have hcard : Nat.card (Y.map (MulAut.conj h).toMonoidHom) = p := by
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective, hY]
  exact eq_of_card_eq_prime_of_pRank_le_one hp hSp ((pRank_mono p hp hSH).trans hrank) hh hPS
    hcard hP

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
