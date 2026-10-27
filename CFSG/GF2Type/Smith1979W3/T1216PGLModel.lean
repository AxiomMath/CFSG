module

public import CFSG.GF2Type.Smith1979W3.T1216Census

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 CFSG.GF2Type.Smith1979W3.Cert690

variable {G : Type} [Group G] [Finite G] (S : Setting G) (L : S.Qt ≃ₗ[ZMod 2] V₀)

@[expose] noncomputable def pglM0 : Subgroup S.O :=
  S.Mbar ⊓ KPGL0.comap ((conjL L).toMonoidHom.comp S.O.subtype)

theorem mem_pglM0_iff {u : S.O} :
    u ∈ pglM0 S L ↔ u ∈ S.Mbar ∧ conjL L (u : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ KPGL0 := by
  rw [pglM0, Subgroup.mem_inf, Subgroup.mem_comap]
  rfl

theorem ρ_mem_pglM0_iff (y : S.M) :
    S.ρ y ∈ pglM0 S L ↔ conjL L (S.ρ y : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ KPGL0 := by
  rw [mem_pglM0_iff]
  exact ⟨fun h => h.2, fun h => ⟨⟨y, rfl⟩, h⟩⟩

theorem pglM0_le : pglM0 S L ≤ S.Mbar := fun _ h => ((mem_pglM0_iff S L).mp h).1

theorem relIndex_pglM0 (hF : PGLFactsProp) (hK : mbarModel S L = KPGL) :
    (pglM0 S L).relIndex S.Mbar = 2 := by
  let ψ : S.O →* (V₀ ≃ₗ[ZMod 2] V₀) := (conjL L).toMonoidHom.comp S.O.subtype
  have hψinj : Function.Injective ψ :=
    fun a b h => S.O.subtype_injective ((conjL L).injective h)
  have hmodel : mbarModel S L = S.Mbar.map ψ := by rw [mbarModel, Subgroup.map_map]
  have hKPGL0 : KPGL0 ≤ KPGL := by
    rw [← hF.2.2.1]
    simpa using Subgroup.commutator_le_of_le (le_refl KPGL) (le_refl KPGL)
  have h1 : S.Mbar.map ψ = KPGL := by rw [← hmodel]; exact hK
  have h2 : (KPGL0.comap ψ).map ψ = KPGL0 := by
    refine le_antisymm (Subgroup.map_comap_le ψ KPGL0) ?_
    intro x hx
    have hxK : x ∈ S.Mbar.map ψ := by rw [h1]; exact hKPGL0 hx
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hxK
    exact Subgroup.mem_map_of_mem ψ (Subgroup.mem_comap.mpr hx)
  have hmap : (pglM0 S L).map ψ = KPGL0 := by
    rw [pglM0, Subgroup.map_inf S.Mbar (KPGL0.comap ψ) ψ hψinj, h1, h2,
      inf_eq_right.mpr hKPGL0]
  have hcardM : Nat.card S.Mbar = 336 := by
    rw [← card_mbarModel S L, hK]; exact hF.2.1
  have hcard0 : Nat.card (pglM0 S L) = 168 := by
    rw [← Subgroup.card_map_of_injective (f := ψ) hψinj, hmap, hF.2.2.2.1]
  have hmul : (pglM0 S L).relIndex S.Mbar * Nat.card ↥(pglM0 S L ⊓ S.Mbar) =
      Nat.card S.Mbar := Subgroup.relIndex_mul_card (pglM0 S L) S.Mbar
  rw [inf_eq_left.mpr (pglM0_le S L), hcard0, hcardM] at hmul
  omega

theorem pgl_exists_conj (hF : PGLFactsProp) (hK : mbarModel S L = KPGL) :
    ∀ u ∈ S.Mbar, u ∉ pglM0 S L → u * u = 1 →
      ∀ u' ∈ S.Mbar, u' ∉ pglM0 S L → u' * u' = 1 →
        ∃ k ∈ S.Mbar, k * u * k⁻¹ = u' := by
  unfold PGLFactsProp at hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hconj, -⟩ := hF
  let ψ : S.O →* (V₀ ≃ₗ[ZMod 2] V₀) := (conjL L).toMonoidHom.comp S.O.subtype
  have hψinj : Function.Injective ψ :=
    fun a b h => S.O.subtype_injective ((conjL L).injective h)
  have hmodel : mbarModel S L = S.Mbar.map ψ := by rw [mbarModel, Subgroup.map_map]
  have hmem : ∀ {u : S.O}, u ∈ S.Mbar → ψ u ∈ KPGL := by
    intro u hu
    rw [← hK, hmodel]
    exact Subgroup.mem_map_of_mem ψ hu
  have hnot : ∀ {u : S.O}, u ∈ S.Mbar → u ∉ pglM0 S L → ψ u ∉ KPGL0 := by
    intro u hu hu0 h
    exact hu0 ((mem_pglM0_iff S L).mpr ⟨hu, h⟩)
  intro u huM hu0 hu2 u' hu'M hu'0 hu'2
  have hu2' : ψ u * ψ u = 1 := by rw [← map_mul, hu2, map_one]
  have hu'2' : ψ u' * ψ u' = 1 := by rw [← map_mul, hu'2, map_one]
  obtain ⟨k, hkK, hkk⟩ := hconj (ψ u) (hmem huM) (hnot huM hu0) hu2'
    (ψ u') (hmem hu'M) (hnot hu'M hu'0) hu'2'
  have hkM : k ∈ S.Mbar.map ψ := by rw [← hmodel, hK]; exact hkK
  obtain ⟨k₀, hk₀M, hk₀⟩ := Subgroup.mem_map.mp hkM
  refine ⟨k₀, hk₀M, hψinj ?_⟩
  rw [map_mul, map_mul, map_inv, hk₀]
  exact hkk

theorem pgl_centralizer_outer (hF : PGLFactsProp) (hK : mbarModel S L = KPGL) :
    ∀ u ∈ S.Mbar, u ∉ pglM0 S L → u * u = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O)) = 12 ∧
      ∀ N : Subgroup S.O, N ≤ S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O) →
        (∀ c ∈ S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O), ∀ n ∈ N,
          c * n * c⁻¹ ∈ N) →
        IsPGroup 2 N → N ≤ Subgroup.zpowers u := by
  unfold PGLFactsProp at hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hcen, -, -⟩ := hF
  let ψ : S.O →* (V₀ ≃ₗ[ZMod 2] V₀) := (conjL L).toMonoidHom.comp S.O.subtype
  have hψinj : Function.Injective ψ :=
    fun a b h => S.O.subtype_injective ((conjL L).injective h)
  have hmodel : mbarModel S L = S.Mbar.map ψ := by rw [mbarModel, Subgroup.map_map]
  have hmem : ∀ {u : S.O}, u ∈ S.Mbar → ψ u ∈ KPGL := by
    intro u hu
    rw [← hK, hmodel]
    exact Subgroup.mem_map_of_mem ψ hu
  have hmapC : ∀ u : S.O, (S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O)).map ψ =
      KPGL ⊓ Subgroup.centralizer ({ψ u} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    intro u
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyM, hyC⟩ := hy
      have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact ⟨hmem hyM, Subgroup.mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul, hyu])⟩
    · rintro x ⟨hxK, hxC⟩
      have hxK' : x ∈ S.Mbar.map ψ := by rw [← hmodel, hK]; exact hxK
      obtain ⟨y, hyM, rfl⟩ := Subgroup.mem_map.mp hxK'
      have hxu : ψ y * ψ u = ψ u * ψ y :=
        Subgroup.mem_centralizer_singleton_iff.mp hxC
      exact Subgroup.mem_map_of_mem ψ ⟨hyM,
        Subgroup.mem_centralizer_singleton_iff.mpr (hψinj (by
          rw [map_mul, map_mul]; exact hxu))⟩
  intro u huM hu0 hu2
  have hKu : ψ u ∈ KPGL := hmem huM
  have hK0 : ψ u ∉ KPGL0 := by
    intro h
    exact hu0 ((mem_pglM0_iff S L).mpr ⟨huM, h⟩)
  have hu2' : ψ u * ψ u = 1 := by rw [← map_mul, hu2, map_one]
  obtain ⟨hcard, hnorm⟩ := hcen (ψ u) hKu hK0 hu2'
  constructor
  · rw [← Subgroup.card_map_of_injective (f := ψ) hψinj, hmapC u]
    exact hcard
  · intro N hNle hNnorm hN2
    have hNleK : N.map ψ ≤ KPGL ⊓
        Subgroup.centralizer ({ψ u} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
      rintro _ ⟨n, hn, rfl⟩
      rw [← hmapC u]
      exact Subgroup.mem_map_of_mem ψ (hNle hn)
    have hNnormK : ∀ c ∈ KPGL ⊓ Subgroup.centralizer ({ψ u} : Set (V₀ ≃ₗ[ZMod 2] V₀)),
        ∀ n ∈ N.map ψ, c * n * c⁻¹ ∈ N.map ψ := by
      intro c hc n hn
      rw [← hmapC u] at hc
      obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.mp hc
      obtain ⟨n₀, hn₀, rfl⟩ := Subgroup.mem_map.mp hn
      rw [show ψ c₀ * ψ n₀ * (ψ c₀)⁻¹ = ψ (c₀ * n₀ * c₀⁻¹) by
        rw [map_mul, map_mul, map_inv]]
      exact Subgroup.mem_map_of_mem ψ (hNnorm c₀ hc₀ n₀ hn₀)
    have hNK := hnorm (N.map ψ) hNleK hNnormK (hN2.map ψ)
    intro n hn
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.mp (hNK (Subgroup.mem_map_of_mem ψ hn))
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, hψinj (by rw [map_zpow, hk])⟩

theorem pgl_centralizer_inner (hF : PGLFactsProp) (hK : mbarModel S L = KPGL) :
    ∀ w ∈ pglM0 S L, w ≠ 1 → w * w = 1 →
      Nat.card ↥(S.Mbar ⊓ Subgroup.centralizer ({w} : Set S.O)) = 16 ∧
      Nat.card {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} = 16 := by
  unfold PGLFactsProp at hF
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hinner⟩ := hF
  let ψ : S.O →* (V₀ ≃ₗ[ZMod 2] V₀) := (conjL L).toMonoidHom.comp S.O.subtype
  have hψinj : Function.Injective ψ :=
    fun a b h => S.O.subtype_injective ((conjL L).injective h)
  have hmodel : mbarModel S L = S.Mbar.map ψ := by rw [mbarModel, Subgroup.map_map]
  have hmem : ∀ {u : S.O}, u ∈ S.Mbar → ψ u ∈ KPGL := by
    intro u hu
    rw [← hK, hmodel]
    exact Subgroup.mem_map_of_mem ψ hu
  have hmapC : ∀ u : S.O, (S.Mbar ⊓ Subgroup.centralizer ({u} : Set S.O)).map ψ =
      KPGL ⊓ Subgroup.centralizer ({ψ u} : Set (V₀ ≃ₗ[ZMod 2] V₀)) := by
    intro u
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hyM, hyC⟩ := hy
      have hyu : y * u = u * y := Subgroup.mem_centralizer_singleton_iff.mp hyC
      exact ⟨hmem hyM, Subgroup.mem_centralizer_singleton_iff.mpr (by
        rw [← map_mul, ← map_mul, hyu])⟩
    · rintro x ⟨hxK, hxC⟩
      have hxK' : x ∈ S.Mbar.map ψ := by rw [← hmodel, hK]; exact hxK
      obtain ⟨y, hyM, rfl⟩ := Subgroup.mem_map.mp hxK'
      have hxu : ψ y * ψ u = ψ u * ψ y :=
        Subgroup.mem_centralizer_singleton_iff.mp hxC
      exact Subgroup.mem_map_of_mem ψ ⟨hyM,
        Subgroup.mem_centralizer_singleton_iff.mpr (hψinj (by
          rw [map_mul, map_mul]; exact hxu))⟩
  intro w hw hw1 hw2
  obtain ⟨-, hwK0⟩ := (mem_pglM0_iff S L).mp hw
  have hw'1 : ψ w ≠ 1 := fun h => hw1 (hψinj (by rw [h, map_one]))
  have hw'2 : ψ w * ψ w = 1 := by rw [← map_mul, hw2, map_one]
  obtain ⟨hcard, hfix⟩ := hinner (ψ w) hwK0 hw'1 hw'2
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.card_map_of_injective (f := ψ) hψinj, hmapC w]
    exact hcard
  · have he : {v : S.Qt // (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} ≃
        {v : V₀ // conjL L (w : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v} :=
      { toFun := fun v => ⟨L v.1, by
          rw [conjL_apply, LinearEquiv.symm_apply_apply, v.2]⟩
        invFun := fun v => ⟨L.symm v.1, by
          have h := congrArg (⇑L.symm) v.2
          simpa [conjL_apply] using h⟩
        left_inv := fun v => Subtype.ext (L.symm_apply_apply v.1)
        right_inv := fun v => Subtype.ext (L.apply_symm_apply v.1) }
    exact (Nat.card_congr he).trans hfix

theorem pgl_eq_z_of_commute (hF : PGLFactsProp) [IsSimpleGroup G] (hw : S.width = 3)
    (h336 : Nat.card S.Mbar = 336) (hL : ∀ v, qModel false (L v) = S.q v)
    (hK : mbarModel S L = KPGL) :
    ∀ y : S.M, S.ρ y ∉ pglM0 S L → ∀ e ∈ S.QG, IsConj e S.z →
      e * (y : G) = (y : G) * e → e = S.z := by
  unfold PGLFactsProp at hF
  obtain ⟨-, -, -, -, -, -, hdisj, -, -, hswap, -, -, hnocensus, -, -, -⟩ := hF
  have hplus : QtPlusType S := qtPlusType_of_card S hw (Or.inl h336)
  have hminus : (false = true) ↔ ¬ QtPlusType S :=
    ⟨fun h => absurd h (by decide), fun h => absurd hplus h⟩
  intro y hy e heQ heconj hey
  by_contra hne
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_comm.mp heconj)
  have hgQ : g * S.z * g⁻¹ ∈ S.QG := hg.symm ▸ heQ
  have hgne : g * S.z * g⁻¹ ≠ S.z := by rw [hg]; exact hne
  obtain ⟨hb0, hbq, hcond⟩ := censusCond_conj S L false hw hL hminus hgQ hgne
  rw [hg] at hb0 hbq hcond
  have hcondK : CensusCond false KPGL
      (((S.Lbar g).map S.O.subtype).map (conjL L).toMonoidHom) (L (S.cl e)) :=
    hK ▸ hcond
  have hbV : L (S.cl e) ∈ VPlus ∨ L (S.cl e) ∈ VStar := by
    by_contra h
    simp only [not_or] at h
    exact hnocensus (L (S.cl e)) hb0 hbq h.1 h.2 _ hcondK
  have hfix : ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl e) = S.cl e := by
    rw [S.ρ_cl y heQ]
    have hye : (y : G) * e * (y : G)⁻¹ = e := by
      calc (y : G) * e * (y : G)⁻¹ = e * (y : G) * (y : G)⁻¹ := by rw [← hey]
        _ = e := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [hye]
  have hfixψ : conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (L (S.cl e)) =
      L (S.cl e) := by
    rw [conjL_apply, LinearEquiv.symm_apply_apply, hfix]
  have hmemK : conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ KPGL := by
    rw [← hK]
    exact conjL_ρ_mem_mbarModel S L y
  have hnotK : conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ∉ KPGL0 := by
    intro h
    exact hy ((ρ_mem_pglM0_iff S L y).mpr h)
  obtain ⟨hVPlus, hVStar⟩ := hswap (conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt))
    hmemK hnotK
  have hbPlus : L (S.cl e) ∈ VPlus := by
    rcases hbV with h | h
    · exact h
    · have h1 : (conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (L (S.cl e)) ∈
          VStar.map ((conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
            V₀ →ₗ[ZMod 2] V₀) := Submodule.mem_map_of_mem h
      rw [hfixψ, hVStar] at h1
      exact h1
  have hbStar : L (S.cl e) ∈ VStar := by
    have h1 : (conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) (L (S.cl e)) ∈
        VPlus.map ((conjL L ((S.ρ y : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
          V₀ →ₗ[ZMod 2] V₀) := Submodule.mem_map_of_mem hbPlus
    rw [hfixψ, hVPlus] at h1
    exact h1
  have hbot : L (S.cl e) ∈ (⊥ : Submodule (ZMod 2) V₀) := by
    rw [← hdisj]
    exact ⟨hbPlus, hbStar⟩
  rw [Submodule.mem_bot] at hbot
  exact hb0 hbot

end CFSG.GF2Type.Smith1979W3

end
