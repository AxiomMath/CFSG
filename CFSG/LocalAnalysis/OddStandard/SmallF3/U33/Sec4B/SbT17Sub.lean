module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4A.S4ADefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Basic

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalIn_of_unique_normal_E16 {𝒮 Y : Subgroup G} (hY : IsE16In 𝒮 Y) (hN : NormalIn Y 𝒮)
    (huniq : ∀ R : Subgroup G, IsPGroup 2 R → 𝒮 ≤ R →
      ∀ A : Subgroup G, IsE16In R A → NormalIn A R → A = Y) :
    ∀ R : Subgroup G, IsPGroup 2 R → 𝒮 ≤ R → NormalIn Y R := by
  suffices H : ∀ n, ∀ R : Subgroup G, Nat.card R = n → IsPGroup 2 R → 𝒮 ≤ R →
      NormalIn Y R by
    intro R hR hSR
    exact H (Nat.card R) R rfl hR hSR
  intro n
  refine Nat.strong_induction_on n ?_
  intro k ih R hcard hR hSR
  by_cases hEq : 𝒮 = R
  · rw [← hEq]
    exact hN
  · have hproper : 𝒮.subgroupOf R ≠ ⊤ := by
      intro htop
      apply hEq
      refine le_antisymm hSR ?_
      intro r hr
      have : (⟨r, hr⟩ : ↥R) ∈ 𝒮.subgroupOf R := by
        rw [htop]; trivial
      rwa [Subgroup.mem_subgroupOf] at this
    obtain htop | ⟨M, hMcoat, hSM⟩ := eq_top_or_exists_le_coatom (𝒮.subgroupOf R)
    · exact absurd htop hproper
    · let R₁ : Subgroup G := M.map R.subtype
      have hR1le : R₁ ≤ R := Subgroup.map_subtype_le M
      have hSR1 : 𝒮 ≤ R₁ := by
        intro s hs
        exact Subgroup.mem_map.mpr
          ⟨⟨s, hSR hs⟩, hSM (by rw [Subgroup.mem_subgroupOf]; exact hs), rfl⟩
      have hR1 : IsPGroup 2 R₁ := hR.to_le hR1le
      have hsub : R₁.subgroupOf R = M := by
        ext x
        rw [Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          rcases Subgroup.mem_map.mp hx with ⟨m, hm, hmx⟩
          have hmx' : m = x := Subtype.ext hmx
          rwa [← hmx']
        · intro hx
          exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      have hR1normalIn : (R₁.subgroupOf R).Normal := by
        rw [hsub]
        haveI : Group.IsNilpotent ↥R := IsPGroup.isNilpotent hR
        exact Group.normalizerCondition_of_isNilpotent.normal_of_coatom M hMcoat
      have hR1conj : ∀ h k : G, h ∈ R₁ → k ∈ R → k * h * k⁻¹ ∈ R₁ :=
        (Subgroup.normal_subgroupOf_iff hR1le).mp hR1normalIn
      have hcardR1 : Nat.card R₁ < Nat.card R := by
        have hlt : M < ⊤ := lt_top_iff_ne_top.mpr hMcoat.1
        calc Nat.card R₁ = Nat.card M := Subgroup.card_subtype R M
          _ < Nat.card (⊤ : Subgroup ↥R) := Subgroup.card_lt_of_lt hlt
          _ = Nat.card R := Subgroup.card_top
      have IH1 : NormalIn Y R₁ :=
        ih (Nat.card R₁) (by simpa [hcard] using hcardR1) R₁ rfl hR1 hSR1
      have key : ∀ r ∈ R, Y.map (MulAut.conj r).toMonoidHom = Y := by
        intro r hr
        let A : Subgroup G := Y.map (MulAut.conj r).toMonoidHom
        have hAR1 : A ≤ R₁ := by
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
          have hyR1 : y ∈ R₁ := hSR1 (hY.1 hy)
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
            hR1conj y r hyR1 hr
        have hAelem : CFSG.Open.IsElemAbelian 2 A := by
          haveI : IsMulCommutative Y := hY.2.1.1
          refine ⟨?_, ?_⟩
          · change IsMulCommutative (Y.map (MulAut.conj r).toMonoidHom)
            infer_instance
          · intro x hx
            rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
            rw [← MonoidHom.map_pow, hY.2.1.2 y hy, map_one]
        have hAcard : Nat.card A = 16 := by
          rw [Subgroup.card_map_of_injective (K := Y)
            (f := (MulAut.conj r).toMonoidHom) (MulAut.conj r).injective, hY.2.2]
        have hAnorm : NormalIn A R₁ := by
          refine ⟨hAR1, ?_⟩
          intro g hg k hk
          rcases Subgroup.mem_map.mp hk with ⟨y, hy, rfl⟩
          have hgr : r⁻¹ * g * r ∈ R₁ := by
            have hg' := hR1conj g r⁻¹ hg (R.inv_mem hr)
            rwa [inv_inv] at hg'
          have hinner : (r⁻¹ * g * r) * y * (r⁻¹ * g * r)⁻¹ ∈ Y :=
            IH1.2 (r⁻¹ * g * r) hgr y hy
          have heq : g * (MulAut.conj r).toMonoidHom y * g⁻¹
              = (MulAut.conj r).toMonoidHom
                  ((r⁻¹ * g * r) * y * (r⁻¹ * g * r)⁻¹) := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group
          rw [heq]
          exact Subgroup.mem_map.mpr ⟨_, hinner, rfl⟩
        exact huniq R₁ hR1 hSR1 A ⟨hAR1, hAelem, hAcard⟩ hAnorm
      refine ⟨hY.1.trans hSR, ?_⟩
      intro g hg k hk
      have hA := key g hg
      have hmem : (MulAut.conj g).toMonoidHom k ∈ Y.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨k, hk, rfl⟩
      rw [hA] at hmem
      simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
