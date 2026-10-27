module

public import CFSG.CGT.Stroth76.Lemma4

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

variable {G : Type*} [Group G] [Finite G] (K : Config G) [Fact (Nat.Prime 2)]

theorem eq_of_le_centralizer_w
    (hfusE : ∀ e ∈ Subgroup.closure {K.x ^ 2, K.y ^ 2, K.uv, K.t}, e ≠ 1 →
      IsConj e ((K.x * K.y) ^ 2))
    (hAnn1 : ¬ IsConj K.w ((K.x * K.y) ^ 2)) (S : Sylow 2 G) (hTS : Tsub K ≤ S)
    (hSN : (S : Subgroup G) ≤ Subgroup.normalizer (K.A : Set G))
    (hchar : ∀ g, g ∈ Subgroup.normalizer
      (((S : Subgroup G) ⊓ Subgroup.centralizer {K.w} : Subgroup G) : Set G) →
        g ∈ Subgroup.normalizer (K.A : Set G))
    {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQw : Q ≤ Subgroup.centralizer {K.w})
    (hQQ : (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} ≤ Q) :
    Q = (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} := by
  set Q₁ := (S : Subgroup G) ⊓ Subgroup.centralizer {K.w} with hQ₁
  by_contra hne
  have hlt : Q₁ < Q := lt_of_le_of_ne hQQ (Ne.symm hne)
  set R := Q ⊓ Subgroup.normalizer (Q₁ : Set G) with hRdef
  have hRgt : Q₁ < R := CFSG.GroupTheory.lt_inf_normalizer_of_isPGroup hQ hlt
  have hRp : IsPGroup 2 R := hQ.to_le inf_le_left
  have hRN : R ≤ Subgroup.normalizer (K.A : Set G) := fun g hg => hchar g hg.2
  obtain ⟨c, hcN, hc⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (Subgroup.normalizer (K.A : Set G)) S hSN R hRN hRp
  obtain ⟨s, hsT, hs⟩ := exists_T_conj_of_normalizer_A K hfusE hAnn1 (Subgroup.inv_mem _ hcN)
  rw [inv_inv] at hs
  have hle : R.map (MulAut.conj (s * c)).toMonoidHom ≤ Q₁ := by
    rintro _ ⟨r, hr, rfl⟩
    have hcr : c * r * c⁻¹ ∈ (S : Subgroup G) := hc ⟨r, hr, rfl⟩
    have hsS : s ∈ (S : Subgroup G) := hTS hsT
    have hT : s * c * r * (s * c)⁻¹ ∈ (S : Subgroup G) := by
      have := (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hsS hcr)
        ((S : Subgroup G).inv_mem hsS)
      rwa [show s * (c * r * c⁻¹) * s⁻¹ = s * c * r * (s * c)⁻¹ by group] at this
    have he : (MulAut.conj (s * c)).toMonoidHom r = s * c * r * (s * c)⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [he]
    refine Subgroup.mem_inf.2 ⟨hT, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have hrw : r * K.w = K.w * r := Subgroup.mem_centralizer_singleton_iff.1 (hQw hr.1)
    have hw : s * c * K.w * (s * c)⁻¹ = K.w := by
      calc s * c * K.w * (s * c)⁻¹ = s * (c * K.w * c⁻¹) * s⁻¹ := by group
        _ = s * (s⁻¹ * K.w * s) * s⁻¹ := by rw [hs]
        _ = K.w := by group
    calc s * c * r * (s * c)⁻¹ * K.w
        = s * c * r * (s * c)⁻¹ * (s * c * K.w * (s * c)⁻¹) := by rw [hw]
      _ = s * c * (r * K.w) * (s * c)⁻¹ := by group
      _ = s * c * (K.w * r) * (s * c)⁻¹ := by rw [hrw]
      _ = s * c * K.w * (s * c)⁻¹ * (s * c * r * (s * c)⁻¹) := by group
      _ = K.w * (s * c * r * (s * c)⁻¹) := by rw [hw]
  have h1 : Nat.card R ≤ Nat.card Q₁ := by
    rw [← card_map_conj (s * c) R]
    exact Subgroup.card_le_of_le hle
  have h2 : Nat.card Q₁ < Nat.card R := Subgroup.card_lt_of_lt hRgt
  omega

theorem exists_conj_le_of_maximal {g₀ : G} {Q₁ : Subgroup G}
    (hQ₁c : Q₁ ≤ Subgroup.centralizer {g₀}) (hQ₁p : IsPGroup 2 Q₁)
    (hmax : ∀ {Q : Subgroup G}, IsPGroup 2 Q → Q ≤ Subgroup.centralizer {g₀} → Q₁ ≤ Q → Q = Q₁)
    {M : Subgroup G} (hM : IsPGroup 2 M) (hMc : M ≤ Subgroup.centralizer {g₀}) :
    ∃ k ∈ Subgroup.centralizer ({g₀} : Set G), ∀ m ∈ M, k⁻¹ * m * k ∈ Q₁ := by
  set C := Subgroup.centralizer ({g₀} : Set G)
  have hQ' : IsPGroup 2 (Q₁.subgroupOf C) :=
    hQ₁p.of_equiv (Subgroup.subgroupOfEquivOfLe hQ₁c).symm
  obtain ⟨P, hP⟩ := hQ'.exists_le_sylow
  have hPeq : (P : Subgroup C).map C.subtype = Q₁ := by
    refine hmax (P.2.map C.subtype) ?_ ?_
    · rintro _ ⟨g, -, rfl⟩
      exact g.2
    · intro q hq
      exact ⟨⟨q, hQ₁c hq⟩, hP hq, rfl⟩
  have hM' : IsPGroup 2 (M.subgroupOf C) := hM.of_equiv (Subgroup.subgroupOfEquivOfLe hMc).symm
  obtain ⟨P', hP'⟩ := hM'.exists_le_sylow
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq C P' P
  refine ⟨(k : G)⁻¹, C.inv_mem k.2, fun m hm => ?_⟩
  have hmP' : (⟨m, hMc hm⟩ : C) ∈ (P' : Subgroup C) := hP' hm
  have hmem : MulAut.conj k (⟨m, hMc hm⟩ : C) ∈ (P : Subgroup C) := by
    rw [← hk, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul _ _ _ hmP'
  have hQ : ((MulAut.conj k (⟨m, hMc hm⟩ : C) : C) : G) ∈ Q₁ := by
    rw [← hPeq]
    exact ⟨_, hmem, rfl⟩
  rw [inv_inv]
  exact hQ

theorem isConj_mul_of_isConj_central (S : Sylow 2 G) {z v r : G}
    (hzS : (S : Subgroup G) ≤ Subgroup.centralizer {z})
    (hfact : ∀ r' ∈ (S : Subgroup G), r' * r' = 1 → r' ≠ 1 → r' ≠ z →
      ∃ q ∈ (S : Subgroup G), q⁻¹ * r' * q = r' * z)
    (hvz : IsConj v z) (hrS : r ∈ (S : Subgroup G)) (hvS : v ∈ (S : Subgroup G))
    (hrv : r * v = v * r) (hr2 : r * r = 1) (hr1 : r ≠ 1) (hne : r ≠ v) :
    IsConj r (r * v) := by
  obtain ⟨g₀, hg₀⟩ := isConj_iff.1 hvz
  set W := ((S : Subgroup G) ⊓ Subgroup.centralizer {v}).map (MulAut.conj g₀).toMonoidHom
  have hWz : W ≤ Subgroup.centralizer {z} := by
    rintro _ ⟨a, ha, rfl⟩
    have hav : a * v = v * a := Subgroup.mem_centralizer_singleton_iff.1 ha.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg₀]
    calc g₀ * a * g₀⁻¹ * (g₀ * v * g₀⁻¹) = g₀ * (a * v) * g₀⁻¹ := by group
      _ = g₀ * (v * a) * g₀⁻¹ := by rw [hav]
      _ = g₀ * v * g₀⁻¹ * (g₀ * a * g₀⁻¹) := by group
  have hWp : IsPGroup 2 W := (S.isPGroup'.to_le inf_le_left).map _
  obtain ⟨h, hh, hW⟩ := CFSG.QuasiDihedralFusion.exists_conj_le_sylow
    (Subgroup.centralizer {z}) S hzS W hWz hWp
  have hhz : h * z * h⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hh
    rw [this]; group
  set m := h * g₀
  have hr' : m * r * m⁻¹ ∈ (S : Subgroup G) := by
    have := hW ⟨g₀ * r * g₀⁻¹, ⟨r, Subgroup.mem_inf.2 ⟨hrS,
      Subgroup.mem_centralizer_singleton_iff.2 hrv⟩, rfl⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    simpa [m, mul_assoc] using this
  have hmv : m * v * m⁻¹ = z := by
    calc m * v * m⁻¹ = h * (g₀ * v * g₀⁻¹) * h⁻¹ := by simp [m]; group
      _ = z := by rw [hg₀, hhz]
  have hr'2 : (m * r * m⁻¹) * (m * r * m⁻¹) = 1 := by
    calc (m * r * m⁻¹) * (m * r * m⁻¹) = m * (r * r) * m⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hr'1 : m * r * m⁻¹ ≠ 1 := fun h' => hr1 (by
    calc r = m⁻¹ * (m * r * m⁻¹) * m := by group
      _ = 1 := by rw [h']; group)
  have hr'z : m * r * m⁻¹ ≠ z := fun h' => hne (by
    calc r = m⁻¹ * (m * r * m⁻¹) * m := by group
      _ = m⁻¹ * (m * v * m⁻¹) * m := by rw [h', hmv]
      _ = v := by group)
  obtain ⟨q, -, hq⟩ := hfact _ hr' hr'2 hr'1 hr'z
  rw [isConj_iff]
  refine ⟨m⁻¹ * q⁻¹ * m, ?_⟩
  calc m⁻¹ * q⁻¹ * m * r * (m⁻¹ * q⁻¹ * m)⁻¹
      = m⁻¹ * (q⁻¹ * (m * r * m⁻¹) * q) * m := by group
    _ = m⁻¹ * ((m * r * m⁻¹) * z) * m := by rw [hq]
    _ = m⁻¹ * ((m * r * m⁻¹) * (m * v * m⁻¹)) * m := by rw [hmv]
    _ = r * v := by group

end CFSG.CGT.Stroth76
