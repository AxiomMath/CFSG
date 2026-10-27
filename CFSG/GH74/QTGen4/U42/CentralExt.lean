module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GH74.QTGen4.U42

open CFSG.Quasithin

theorem exists_complement_of_sylow {G : Type*} [Group G] [Finite G]
    (V : Subgroup G) [V.Normal] [IsMulCommutative V] (hV : IsPGroup 2 V)
    (Q : Subgroup G) (hQ : IsPGroup 2 Q) (hQi : ¬ 2 ∣ Q.index)
    (K0 : Subgroup G) (hK0 : K0 ≤ Q) (h1 : V ⊓ K0 = ⊥) (h2 : V ⊔ K0 = Q) :
    ∃ K : Subgroup G, V ⊓ K = ⊥ ∧ V ⊔ K = ⊤ := by
  let P : Sylow 2 G := hQ.toSylow hQi
  have hPQ : (P : Subgroup G) = Q := IsPGroup.toSylow_coe hQ hQi
  have hK : ∃ K : Subgroup G, K ≤ P ∧ V ⊓ K = ⊥ ∧ V ⊔ K = P := by
    refine ⟨K0, ?_, h1, ?_⟩
    · rw [show (P : Subgroup G) = Q from hPQ]; exact hK0
    · rw [show (P : Subgroup G) = Q from hPQ]; exact h2
  exact (gaschutz hV P).mpr hK

theorem exists_complement_mod_central {G : Type*} [Group G] [Finite G]
    (Δ V0 K0 Q0 : Subgroup G) [Δ.Normal] [V0.Normal]
    (hΔV : Δ ≤ V0) (hV : ∀ a ∈ V0, ∀ b ∈ V0, a * b = b * a)
    (hV2 : IsPGroup 2 V0) (hK02 : IsPGroup 2 K0)
    (hQ : Q0 = V0 ⊔ K0) (hQi : ¬ 2 ∣ Q0.index)
    (h1 : ∀ x ∈ V0, x ∈ K0 → x ∈ Δ) :
    ∃ C : Subgroup G, Δ ≤ C ∧ C ⊓ V0 = Δ ∧ C ⊔ V0 = ⊤ := by
  have hsurj : Function.Surjective (QuotientGroup.mk' Δ) := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨x, rfl⟩
  have hΔQ : Δ ≤ Q0 := by rw [hQ]; exact hΔV.trans le_sup_left
  have hK0Q : K0 ≤ Q0 := by rw [hQ]; exact le_sup_right
  have hker : (QuotientGroup.mk' Δ).ker ≤ Q0 := fun x hx =>
    hΔQ ((QuotientGroup.eq_one_iff x).mp (MonoidHom.mem_ker.mp hx))
  haveI : (V0.map (QuotientGroup.mk' Δ)).Normal := Subgroup.Normal.map inferInstance _ hsurj
  have hcomm : ∀ a ∈ V0.map (QuotientGroup.mk' Δ), ∀ b ∈ V0.map (QuotientGroup.mk' Δ),
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    rw [← map_mul, ← map_mul, hV x hx y hy]
  haveI : IsMulCommutative (V0.map (QuotientGroup.mk' Δ)) :=
    ⟨⟨fun a b => Subtype.ext (hcomm a a.2 b b.2)⟩⟩
  have hQ0 : IsPGroup 2 Q0 := by
    rw [hQ]; exact IsPGroup.to_sup_of_normal_left hV2 hK02
  have hint : V0.map (QuotientGroup.mk' Δ) ⊓ K0.map (QuotientGroup.mk' Δ) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hx1
    obtain ⟨k, hk, hkv⟩ := Subgroup.mem_map.mp hx2
    have hδ : k⁻¹ * v ∈ Δ := QuotientGroup.eq.mp hkv
    have hkV : k ∈ V0 := by
      have h := V0.mul_mem hv (hΔV (Δ.inv_mem hδ))
      rwa [show v * (k⁻¹ * v)⁻¹ = k by group] at h
    have hkΔ : k ∈ Δ := h1 k hkV hk
    rw [← hkv]
    exact (QuotientGroup.eq_one_iff k).mpr hkΔ
  have hQi' : ¬ 2 ∣ (Q0.map (QuotientGroup.mk' Δ)).index := by
    rw [Subgroup.index_map_eq Q0 hsurj hker]; exact hQi
  obtain ⟨K, hK1, hK2⟩ := exists_complement_of_sylow
    (V0.map (QuotientGroup.mk' Δ)) (IsPGroup.map hV2 _)
    (Q0.map (QuotientGroup.mk' Δ)) (IsPGroup.map hQ0 _) hQi'
    (K0.map (QuotientGroup.mk' Δ)) (Subgroup.map_mono hK0Q) hint
    (by rw [hQ, Subgroup.map_sup])
  have hΔC : Δ ≤ K.comap (QuotientGroup.mk' Δ) := fun x hx => by
    show QuotientGroup.mk' Δ x ∈ K
    rw [show QuotientGroup.mk' Δ x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact K.one_mem
  refine ⟨K.comap (QuotientGroup.mk' Δ), hΔC, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxC, hxV⟩
      have hmem : QuotientGroup.mk' Δ x ∈ V0.map (QuotientGroup.mk' Δ) ⊓ K :=
        ⟨Subgroup.mem_map.mpr ⟨x, hxV, rfl⟩, hxC⟩
      rw [hK1, Subgroup.mem_bot] at hmem
      exact (QuotientGroup.eq_one_iff x).mp hmem
    · intro hx
      exact ⟨hΔC hx, hΔV hx⟩
  · rw [eq_top_iff]
    intro x _
    have h : QuotientGroup.mk' Δ x ∈ V0.map (QuotientGroup.mk' Δ) ⊔ K := by
      rw [hK2]; exact Subgroup.mem_top _
    rw [Subgroup.mem_sup_of_normal_left] at h
    obtain ⟨y, hy, k, hk, hyk⟩ := h
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨c, rfl⟩ := hsurj k
    have hδ : (v * c)⁻¹ * x ∈ Δ := by
      apply QuotientGroup.eq.mp
      show QuotientGroup.mk' Δ (v * c) = QuotientGroup.mk' Δ x
      rw [map_mul]
      exact hyk
    have hconj : c⁻¹ * v * c ∈ V0 := by
      have := Subgroup.Normal.conj_mem ‹V0.Normal› v hv c⁻¹
      rwa [inv_inv] at this
    refine Subgroup.mem_sup_of_normal_right.mpr ⟨c, hk, c⁻¹ * v * c * ((v * c)⁻¹ * x),
      V0.mul_mem hconj (hΔV hδ), ?_⟩
    group

end CFSG.GH74.QTGen4.U42

end
