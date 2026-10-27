module

public import CFSG.CGT.Timmesfeld75.Sec3TwelveAlg
public import CFSG.CGT.Timmesfeld75.Sec3Lift
public import CFSG.CGT.Timmesfeld75.L2Orbit

public section

namespace CFSG.CGT.T75I

open CFSG.Open CFSG.CGT.Timmesfeld75

section Rigid

variable {X : Type} [Group X] {S : Subgroup X} {q : ℕ}

theorem eq_refl_of_fix_of_map_conj (hX : IsL2Pair X S q) (φ : X ≃* X) (hfix : ∀ s ∈ S, φ s = s)
    {a : X} (ha : conjSubgroup a S ≠ S)
    (h : (conjSubgroup a S).map φ.toMonoidHom = conjSubgroup a S) : φ = MulEquiv.refl X := by
  refine IsL2Pair.eq_refl_of_map_conjSubgroup_eq hX φ fun g => ?_
  by_cases hg : conjSubgroup g S = S
  · rw [hg]
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact (hfix s hs).symm ▸ hs
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  · obtain ⟨s, hs, hgs⟩ := IsL2Pair.exists_mem_conj_eq hX ha hg
    rw [hgs, map_conjSubgroup_mulEquiv, h, hfix s hs]

end Rigid

section Action

variable {G : Type} [Group G] [Finite G] {T T₁ : Subgroup G}

theorem comm_mem_cfgM_of_centralizer [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]
    (hS : Sec3 T T₁) {q : ℕ}
    (hpair : IsL2Pair (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) q)
    {u : G} (huT : u ∈ Subgroup.centralizer (T : Set G)) (huT₁ : conjSubgroup u T₁ = T₁) :
    ∀ x ∈ T ⊔ T₁, x⁻¹ * (u * x * u⁻¹) ∈ cfgM T T₁ := by
  classical
  have huTn : conjSubgroup u T = T := mem_normalizer_iff_conjSubgroup_eq.1
    (Subgroup.centralizer_le_normalizer (T : Set G) huT)
  have hX : conjSubgroup u (T ⊔ T₁) = T ⊔ T₁ := by
    rw [conjSubgroup_sup_eq_sup, huTn, huT₁]
  have hM : conjSubgroup u (cfgM T T₁) = cfgM T T₁ := by
    rw [← cfgM_conj, huTn, huT₁]
  set φ := quotConjAut (T ⊔ T₁) (cfgM T T₁) u hX hM with hφ
  have hfix : ∀ s ∈ (T.subgroupOf (T ⊔ T₁)).map
      (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))), φ s = s := by
    intro s hs
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hs
    have htT : (t : G) ∈ T := Subgroup.mem_subgroupOf.1 ht
    show quotConjAut (T ⊔ T₁) (cfgM T T₁) u hX hM (QuotientGroup.mk t) = QuotientGroup.mk t
    rw [quotConjAut_mk]
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show u * (t : G) * u⁻¹ = t
    have := Subgroup.mem_centralizer_iff.1 huT (t : G) htT
    rw [← this]
    group
  obtain ⟨x₀, hx₀, hT₁⟩ := hS.conj
  have hconjT : conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩)
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) =
      (T₁.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [← map_subgroupOf_conjSubgroup_of_mem (T ⊔ T₁) (cfgM T T₁) T hx₀, ← hT₁]
  have hne : conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩)
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) ≠
      (T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))) := by
    rw [hconjT]
    exact hS.map_ne_map
  have hmap : (conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩)
      ((T.subgroupOf (T ⊔ T₁)).map
        (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁))))).map φ.toMonoidHom =
      conjSubgroup (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)) ⟨x₀, hx₀⟩)
        ((T.subgroupOf (T ⊔ T₁)).map
          (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) := by
    rw [hconjT, ← map_subgroupOf_conjSubgroup_eq (T ⊔ T₁) (cfgM T T₁) u hX hM T₁, huT₁]
  have hid := eq_refl_of_fix_of_map_conj hpair φ hfix hne hmap
  intro x hx
  exact mem_of_quotConjAut_mk_eq (T ⊔ T₁) (cfgM T T₁) u hX hM ⟨x, hx⟩
    (by rw [← hφ, hid]; rfl)

theorem conj_eq_of_centralizer [hN : ((cfgM T T₁).subgroupOf (T ⊔ T₁)).Normal]
    (hS : Sec3 T T₁) {q : ℕ}
    (hpair : IsL2Pair (↥(T ⊔ T₁) ⧸ (cfgM T T₁).subgroupOf (T ⊔ T₁))
      ((T.subgroupOf (T ⊔ T₁)).map (QuotientGroup.mk' ((cfgM T T₁).subgroupOf (T ⊔ T₁)))) q)
    {u : G} (huT : u ∈ Subgroup.centralizer (T : Set G)) (huT₁ : conjSubgroup u T₁ = T₁) :
    ∀ m ∈ cfgM T T₁, u * m * u⁻¹ = m := by
  have hcomm := comm_mem_cfgM_of_centralizer hS hpair huT huT₁
  have huTn : conjSubgroup u T = T := mem_normalizer_iff_conjSubgroup_eq.1
    (Subgroup.centralizer_le_normalizer (T : Set G) huT)
  have hM : conjSubgroup u (cfgM T T₁) = cfgM T T₁ := by
    rw [← cfgM_conj, huTn, huT₁]
  have hMab := hS.cfg.isElemAbelian_cfgM
  obtain ⟨g, hg, hT₁g⟩ := hS.conj
  have hvT₁ : ∀ y ∈ T₁, (g * u * g⁻¹) * y = y * (g * u * g⁻¹) := by
    intro y hy
    rw [hT₁g, mem_conjSubgroup] at hy
    have := Subgroup.mem_centralizer_iff.1 huT _ hy
    calc g * u * g⁻¹ * y = g * (u * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * u) * g⁻¹ := by rw [← this]
      _ = y * (g * u * g⁻¹) := by group
  have hvu : g * u * g⁻¹ * u⁻¹ ∈ cfgM T T₁ := by
    have := hcomm g⁻¹ ((T ⊔ T₁).inv_mem hg)
    simpa [mul_assoc] using this
  have hL : ∀ l ∈ normIn T T₁, u * l * u⁻¹ = l := by
    intro l hl
    have hlT : l ∈ T := normIn_le _ _ hl
    have := Subgroup.mem_centralizer_iff.1 huT l hlT
    rw [← this]
    group
  have hL₁ : ∀ x ∈ normIn T₁ T, u * x * u⁻¹ = x := by
    intro x hx
    have hxT₁ : x ∈ T₁ := normIn_le _ _ hx
    have hxM : x ∈ cfgM T T₁ := Cfg.normIn_le_cfgM_right T T₁ hx
    have huxM : u * x * u⁻¹ ∈ cfgM T T₁ := by
      have : u * x * u⁻¹ ∈ conjSubgroup u (cfgM T T₁) := conj_mem_conjSubgroup u hxM
      rwa [hM] at this
    obtain ⟨m, hm⟩ : ∃ m : G, m = g * u * g⁻¹ * u⁻¹ := ⟨_, rfl⟩
    have hmM : m ∈ cfgM T T₁ := hm ▸ hvu
    have hv : g * u * g⁻¹ = m * u := by rw [hm]; group
    have hmy : m * (u * x * u⁻¹) = (u * x * u⁻¹) * m := elemAbelian_mul_comm hMab hmM huxM
    have e1 : (g * u * g⁻¹) * x * (g * u * g⁻¹)⁻¹ = x := by
      calc (g * u * g⁻¹) * x * (g * u * g⁻¹)⁻¹ = (x * (g * u * g⁻¹)) * (g * u * g⁻¹)⁻¹ := by
            rw [hvT₁ x hxT₁]
        _ = x := by group
    have e2 : (g * u * g⁻¹) * x * (g * u * g⁻¹)⁻¹ = u * x * u⁻¹ := by
      calc (g * u * g⁻¹) * x * (g * u * g⁻¹)⁻¹ = (m * u) * x * (m * u)⁻¹ := by rw [hv]
        _ = m * (u * x * u⁻¹) * m⁻¹ := by group
        _ = (u * x * u⁻¹) * m * m⁻¹ := by rw [hmy]
        _ = u * x * u⁻¹ := by group
    exact e2.symm.trans e1
  intro m hm
  obtain ⟨l, hl, x, hx, rfl⟩ := hS.cfg.mem_cfgM_iff.1 hm
  calc u * (l * x) * u⁻¹ = (u * l * u⁻¹) * (u * x * u⁻¹) := by group
    _ = l * x := by rw [hL l hl, hL₁ x hx]

end Action

end CFSG.CGT.T75I
