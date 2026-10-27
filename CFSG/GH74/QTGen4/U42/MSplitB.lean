module

public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.GH74.QTGen4.U42

theorem exists_complement_of_sylow_complement {G : Type} [Group G] [Finite G]
    {H V T K0 : Subgroup G} (hVH : V ≤ H) (hVT : V ≤ T) (hTH : T ≤ H)
    (hVn : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V)
    (hVp : IsPGroup 2 V) (hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hT2 : IsPGroup 2 T) (hidx : ¬ 2 ∣ (T.subgroupOf H).index)
    (hK0T : K0 ≤ T) (hK0V : V ⊓ K0 = ⊥)
    (hdec : ∀ t ∈ T, ∃ v ∈ V, ∃ k ∈ K0, v * k = t) :
    ∃ A : Subgroup G, A ≤ H ∧ A ⊓ V = ⊥ ∧ V ⊔ A = H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup H := V.subgroupOf H with hN
  haveI hNn : N.Normal := ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
    (by simpa using hVn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  haveI hNc : IsMulCommutative N := ⟨⟨fun a b => by
    have h := hVc _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
    exact Subtype.ext (Subtype.ext h)⟩⟩
  have hNp : IsPGroup 2 N := hVp.of_equiv (Subgroup.subgroupOfEquivOfLe hVH).symm
  have hTsub : IsPGroup 2 (T.subgroupOf H) := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hPc : ((hTsub.toSylow hidx : Sylow 2 H) : Subgroup H) = T.subgroupOf H :=
    IsPGroup.toSylow_coe hTsub hidx
  obtain ⟨A₀, hA₁, hA₂⟩ := (CFSG.Quasithin.gaschutz hNp (hTsub.toSylow hidx)).mpr
    ⟨K0.subgroupOf H, by
      rw [hPc]
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hK0T (Subgroup.mem_subgroupOf.mp hx)),
     by
      rw [eq_bot_iff]
      rintro x ⟨hxN, hxK⟩
      have hv : (x : G) ∈ V ⊓ K0 :=
        ⟨Subgroup.mem_subgroupOf.mp hxN, Subgroup.mem_subgroupOf.mp hxK⟩
      rw [hK0V, Subgroup.mem_bot] at hv
      rw [Subgroup.mem_bot]
      exact Subtype.ext hv,
     by
      rw [hPc]
      apply le_antisymm
      · apply sup_le
        · intro x hx
          exact Subgroup.mem_subgroupOf.mpr (hVT (Subgroup.mem_subgroupOf.mp hx))
        · intro x hx
          exact Subgroup.mem_subgroupOf.mpr (hK0T (Subgroup.mem_subgroupOf.mp hx))
      · intro x hx
        obtain ⟨v, hv, k, hk, hvk⟩ := hdec x hx
        have e : (⟨v, hVH hv⟩ : H) * ⟨k, hTH (hK0T hk)⟩ = x := Subtype.ext hvk
        rw [← e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hv))
          (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hk))⟩
  refine ⟨A₀.map H.subtype, Subgroup.map_subtype_le A₀, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxV⟩
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hxA
    have hkN : k ∈ N := Subgroup.mem_subgroupOf.mpr hxV
    have hk1 : k ∈ N ⊓ A₀ := ⟨hkN, hk⟩
    rw [hA₁, Subgroup.mem_bot] at hk1
    rw [Subgroup.mem_bot, hk1, map_one]
  · apply le_antisymm (sup_le hVH (Subgroup.map_subtype_le A₀))
    intro x hx
    have htop : (⟨x, hx⟩ : H) ∈ N ⊔ A₀ := by
      rw [hA₂]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, k, hk, hnk⟩ := Subgroup.mem_sup_of_normal_left.mp htop
    have e : (n : G) * (k : G) = x := congrArg Subtype.val hnk
    rw [← e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hn))
      (Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩))

end CFSG.GH74.QTGen4.U42
