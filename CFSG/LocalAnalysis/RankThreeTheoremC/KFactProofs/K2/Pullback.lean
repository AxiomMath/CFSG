module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open scoped MatrixGroups

section Pullback

variable {G : Type} [Group G] [Finite G]

theorem pa_ker : (barMk G).ker = primeComplementCore (G := G) 3 :=
  QuotientGroup.ker_mk' _

theorem inf_ker_bar_eq_bot {D : Subgroup G} (hD : IsPGroup 3 D) : D ⊓ (barMk G).ker = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  rintro x ⟨hxD, hxK⟩
  rw [pa_ker] at hxK
  obtain ⟨k, hk⟩ := hD ⟨x, hxD⟩
  have hk' : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf x ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf x ∣ Nat.card (primeComplementCore (G := G) 3) :=
    Subgroup.orderOf_dvd_natCard _ hxK
  have hcop : Nat.Coprime (Nat.card (primeComplementCore (G := G) 3)) (3 ^ k) :=
    (primeComplementCore_coprime 3).symm.pow_right k
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)

theorem pa_injOn {D : Subgroup G} (hD : IsPGroup 3 D) : Set.InjOn (barMk G) (D : Set G) := by
  intro x hx y hy hxy
  have hxy' : (x : Bar G) = (y : Bar G) := hxy
  have hmem : x⁻¹ * y ∈ primeComplementCore (G := G) 3 := QuotientGroup.eq.mp hxy'
  have hQmem : x⁻¹ * y ∈ D := D.mul_mem (D.inv_mem hx) hy
  have h1 : x⁻¹ * y ∈ D ⊓ (barMk G).ker := by
    refine ⟨hQmem, ?_⟩
    rw [pa_ker]
    exact hmem
  rw [inf_ker_bar_eq_bot hD, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem card_map_bar {D : Subgroup G} (hD : IsPGroup 3 D) :
    Nat.card (D.map (barMk G)) = Nat.card D := by
  have := Nat.card_image_of_injOn (pa_injOn hD)
  rw [← Subgroup.coe_map] at this
  exact this

theorem isElemAbelian_map_bar {D : Subgroup G} (hD : IsElemAbelian 3 D) :
    IsElemAbelian 3 (D.map (barMk G)) :=
  hD.map (barMk G)

end Pullback

section Pullback

variable {G : Type} [Group G] [Finite G]

theorem K2Concl.of_bar (h1 : ∃ N : Subgroup (Bar G), N.Normal ∧ N.index = 3)
    (h2 : ∀ D : Subgroup (Bar G), IsElemAbelian 3 D → Nat.card D = 9 →
      ∀ W : Subgroup (Bar G), D ≤ normalizer (W : Set (Bar G)) →
        Nat.Coprime (Nat.card W) 6 → W = ⊥) : K2Concl G := by
  obtain ⟨Nb, hN, hi⟩ := h1
  unfold K2Concl
  refine ⟨⟨Nb.comap (barMk G), hN.comap (barMk G), ?_⟩, ?_⟩
  · rw [Subgroup.index_comap_of_surjective (H := Nb) (f := barMk G)
      (QuotientGroup.mk'_surjective (primeComplementCore (G := G) 3)), hi]
  · intro D hD hD9 W hDW hW
    have hDp : IsPGroup 3 D := fun y => ⟨1, Subtype.ext (by simpa using hD.2 (y : G) y.2)⟩
    have hDb : IsElemAbelian 3 (D.map (barMk G)) := isElemAbelian_map_bar hD
    have hDb9 : Nat.card (D.map (barMk G)) = 9 := (card_map_bar hDp).trans hD9
    have hDWb : D.map (barMk G) ≤
        normalizer ((W.map (barMk G) : Subgroup (Bar G)) : Set (Bar G)) :=
      (Subgroup.map_mono (f := barMk G) hDW).trans
        (Subgroup.le_normalizer_map (H := W) (f := barMk G))
    have hWb : Nat.Coprime (Nat.card (W.map (barMk G))) 6 :=
      Nat.Coprime.coprime_dvd_left
        (Subgroup.card_map_dvd (H := W) (f := barMk G)) hW
    have hbot : W.map (barMk G) = ⊥ :=
      h2 (D.map (barMk G)) hDb hDb9 (W.map (barMk G)) hDWb hWb
    intro w hw
    have hmem : barMk G w ∈ W.map (barMk G) := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have hker0 : (barMk G).ker = primeComplementCore (G := G) 3 :=
      QuotientGroup.ker_mk' (primeComplementCore (G := G) 3)
    have hker : w ∈ (barMk G).ker := MonoidHom.mem_ker.mpr hmem
    rw [hker0] at hker
    exact hker

end Pullback

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.K2
