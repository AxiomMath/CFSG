module

public import CFSG.LocalAnalysis.ComponentClassification.UGSChainOrbitFixedLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerTwoLayerOrbitLocation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBRankProjectiveAction

public section

namespace CFSG.ComponentClassification.Sol78

open CFSG Subgroup UnbalancedLayer UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem map_pPrimeCore_le_of_isPComponent' {J Y : Subgroup X} (hJY : J ≤ Y)
    (hJ : IsPComponent 2 (J.subgroupOf Y)) :
    (pPrimeCore 2 J).map J.subtype ≤ (pPrimeCore 2 Y).map Y.subtype := by
  have hsub : (J.subgroupOf Y).IsSubnormal := by
    obtain ⟨_, _, h, _, _⟩ := hJ
    exact h
  rw [← pPrimeCore_map_subgroupOf 2 J Y hJY,
    UnbalancedCorr.map_pPrimeCore_eq_inf_of_isSubnormal hsub]
  exact map_mono inf_le_right

theorem gsFixedLayer_normal (L : Subgroup X) (y : X) :
    ((gsFixedLayer L y).subgroupOf (L ⊓ centralizer ({y} : Set X))).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar := CatalogueBPrimeJoin.pLayer_characteristic (G := ↥(L ⊓ centralizer ({y} : Set X)))
    (p := 2)
  have hn : (pLayer ↥(L ⊓ centralizer ({y} : Set X)) 2).Normal := inferInstance
  have h : (gsFixedLayer L y).subgroupOf (L ⊓ centralizer ({y} : Set X)) =
      pLayer ↥(L ⊓ centralizer ({y} : Set X)) 2 := by
    unfold gsFixedLayer
    exact comap_map_eq_self_of_injective (subtype_injective _) _
  rw [h]
  exact hn

theorem mem_gsFixedLayer_of_cover {L : Subgroup X} {y : X} (hy : orderOf y = 2) (hyL : y ∈ L)
    (hcov : (gsFixedLayer L y : Set X) * ((pPrimeCore 2 L).map L.subtype : Set X) = L) :
    y ∈ gsFixedLayer L y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := L ⊓ centralizer ({y} : Set X) with hC
  set T := gsFixedLayer L y with hT
  have hTC : T ≤ C := gsFixedLayer_le_inf L y
  have hn := gsFixedLayer_normal L y
  have hyC : y ∈ C := mem_inf.mpr ⟨hyL, mem_centralizer_singleton_iff.mpr rfl⟩
  have hyL' : y ∈ ((T : Set X) * ((pPrimeCore 2 L).map L.subtype : Set X)) := by
    rw [hcov]
    exact hyL
  obtain ⟨t, ht, o, ho, hto⟩ := hyL'
  have hoC : o ∈ C := by
    have h1 : o = t⁻¹ * y := by rw [← hto]; group
    rw [h1]
    exact mul_mem (inv_mem (hTC ht)) hyC
  set q := QuotientGroup.mk' (T.subgroupOf C) with hq
  have htq : q ⟨t, hTC ht⟩ = 1 := by
    rw [hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ht
  have hyo : q ⟨y, hyC⟩ = q ⟨o, hoC⟩ := by
    have h1 : (⟨y, hyC⟩ : C) = ⟨t, hTC ht⟩ * ⟨o, hoC⟩ := Subtype.ext hto.symm
    rw [h1, map_mul, htq, one_mul]
  have hodd : Odd (orderOf o) := by
    obtain ⟨o', ho', rfl⟩ := ho
    have h := (pPrimeCore 2 L).orderOf_dvd_natCard ho'
    rw [L.subtype_apply, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat (Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2))) h
  have hy2 : orderOf (q ⟨y, hyC⟩) ∣ 2 := by
    have h := orderOf_map_dvd q (⟨y, hyC⟩ : C)
    rwa [Subgroup.orderOf_mk, hy] at h
  have ho2 : orderOf (q ⟨o, hoC⟩) ∣ orderOf o := by
    have h := orderOf_map_dvd q (⟨o, hoC⟩ : C)
    rwa [Subgroup.orderOf_mk] at h
  rw [hyo] at hy2
  have hcop : Nat.Coprime 2 (orderOf (q ⟨o, hoC⟩)) :=
    Nat.coprime_two_left.mpr (hodd.of_dvd_nat ho2)
  have h1 : orderOf (q ⟨o, hoC⟩) = 1 := Nat.Coprime.eq_one_of_dvd hcop.symm hy2
  rw [orderOf_eq_one_iff, ← hyo, hq, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem pump_setup (hS : SchreierFor Blueprint.Catalog)
    (hK : Assembly.KProper Blueprint.Catalog X) {x y : X} {L : Subgroup X} (hx : orderOf x = 2)
    (hy : orderOf y = 2) (hyZ : y ∉ center X) (hLx : L ≤ centralizer ({x} : Set X))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set X)))) (hyL : y ∈ L)
    (hLy : ∀ l ∈ L, l⁻¹ * y⁻¹ * l * y ∈ (pPrimeCore 2 L).map L.subtype) :
    gsFixedLayer L y ≤ centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X) ∧
      IsPComponent 2 ((gsFixedLayer L y).subgroupOf
        (centralizer ({x} : Set X) ⊓ centralizer ({y} : Set X))) ∧
      (gsFixedLayer L y : Set X) * ((pPrimeCore 2 L).map L.subtype : Set X) = L ∧
      (pPrimeCore 2 (gsFixedLayer L y)).map (gsFixedLayer L y).subtype =
        gsFixedLayer L y ⊓ (pPrimeCore 2 L).map L.subtype ∧
      (∃ φ : gsFixedLayer L y ⧸ pPrimeCore 2 (gsFixedLayer L y) ≃* L ⧸ pPrimeCore 2 L,
        ∀ (t : gsFixedLayer L y) (ht : (t : X) ∈ L),
          φ t = ((⟨(t : X), ht⟩ : L) : L ⧸ pPrimeCore 2 L)) ∧
      y ∈ gsFixedLayer L y ∧
      ∃ M : Subgroup X, M ≤ centralizer ({y} : Set X) ∧
        IsPComponent 2 (M.subgroupOf (centralizer ({y} : Set X))) ∧
        gsFixedLayer L y ≤ M ⊔ conjugate M x ∧
        IsPComponent 2 ((gsFixedLayer L y).subgroupOf
          ((M ⊔ conjugate M x) ⊓ centralizer ({x} : Set X))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxy : x * y = y * x := (mem_centralizer_singleton_iff.mp (hLx hyL)).symm
  set Cx := centralizer ({x} : Set X) with hCx
  set Hb := centralizer ({y} : Set X) with hHb
  have hLxL : conjugate L x = L := UnbalancedCorr.conjugate_eq_self_of_le_centralizer hLx
  have hKe : ∀ k ∈ L ⊔ conjugate L x, k⁻¹ * y⁻¹ * k * y ∈ (pPrimeCore 2 Cx).map Cx.subtype := by
    intro k hk
    rw [hLxL, sup_idem] at hk
    exact map_pPrimeCore_le_of_isPComponent' hLx hL (hLy k hk)
  obtain ⟨-, -, -, -, hTab, hTpc, hTV, hVE, hcov, hcore, φ, hφ⟩ :=
    UGSChain.kProper_core_trivial_orbit_fixed_layer_containment_of_schreier hS hK (a := x)
      (b := x) (e := y) hx hy rfl hxy hyZ hLx hL hKe
  have hyT : y ∈ gsFixedLayer L y := mem_gsFixedLayer_of_cover hy hyL hcov
  refine ⟨hTab, hTpc, hcov, hcore, ⟨φ, hφ⟩, hyT, ?_⟩
  have hTE : gsFixedLayer L y ≤ (pLayer Hb 2).map Hb.subtype := hTV.trans hVE
  have hTHb : gsFixedLayer L y ≤ Hb := hTab.trans inf_le_right
  have hxHb : x ∈ Hb := mem_centralizer_singleton_iff.mpr hxy
  have hx' : orderOf (⟨x, hxHb⟩ : Hb) = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hcenx : centralizer ({(⟨x, hxHb⟩ : Hb)} : Set Hb) = (Cx ⊓ Hb).subgroupOf Hb := by
    ext w
    rw [mem_centralizer_singleton_iff, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    exact ⟨fun h => ⟨congrArg Subtype.val h, w.2⟩, fun h => Subtype.ext h.1⟩
  have hT'C : (gsFixedLayer L y).subgroupOf Hb ≤
      centralizer ({(⟨x, hxHb⟩ : Hb)} : Set Hb) := by
    rw [hcenx]
    intro w hw
    exact mem_subgroupOf.mpr (hTab (mem_subgroupOf.mp hw))
  have hT'pc : IsPComponent 2 (((gsFixedLayer L y).subgroupOf Hb).subgroupOf
      (centralizer ({(⟨x, hxHb⟩ : Hb)} : Set Hb))) := by
    rw [hcenx, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_right 2
      Nat.prime_two]
    exact hTpc
  have hT'E : (gsFixedLayer L y).subgroupOf Hb ≤ pLayer Hb 2 := by
    intro w hw
    obtain ⟨z, hz, hzw⟩ := mem_map.mp (hTE (mem_subgroupOf.mp hw))
    rwa [← Subtype.ext hzw]
  obtain ⟨M', hM', hT'K, hT'Kpc⟩ := two_layer_fixed_component_orbit_location hx' hT'C hT'pc hT'E
  obtain ⟨M, hMHb, rfl⟩ : ∃ M : Subgroup X, M ≤ Hb ∧ M.subgroupOf Hb = M' :=
    ⟨M'.map Hb.subtype, map_subtype_le _, comap_map_eq_self_of_injective Hb.subtype_injective _⟩
  obtain ⟨hMaHb, -⟩ := UGSChain.conjugate_isPComponent_centralizer (b := y) hxy hMHb hM'
  have hconj : conjugate (M.subgroupOf Hb) ⟨x, hxHb⟩ = (conjugate M x).subgroupOf Hb :=
    conjugate_subgroupOf_eq M Hb ⟨x, hxHb⟩
  have hK'eq : M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨x, hxHb⟩ =
      (M ⊔ conjugate M x).subgroupOf Hb := by
    rw [hconj, subgroupOf_sup hMHb hMaHb]
  have hKHb : M ⊔ conjugate M x ≤ Hb := sup_le hMHb hMaHb
  have hCeq : (M.subgroupOf Hb ⊔ conjugate (M.subgroupOf Hb) ⟨x, hxHb⟩) ⊓
      centralizer ({(⟨x, hxHb⟩ : Hb)} : Set Hb) = ((M ⊔ conjugate M x) ⊓ Cx).subgroupOf Hb := by
    rw [hK'eq, hcenx]
    ext w
    simp only [mem_inf, mem_subgroupOf]
    exact ⟨fun h => ⟨h.1, h.2.1⟩, fun h => ⟨h.1, h.2, w.2⟩⟩
  refine ⟨M, hMHb, hM', ?_, ?_⟩
  · intro t ht
    have h1 := hT'K (show (⟨t, hTHb ht⟩ : Hb) ∈ (gsFixedLayer L y).subgroupOf Hb from ht)
    rw [hK'eq] at h1
    exact h1
  · rw [hCeq, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left.trans hKHb) 2 Nat.prime_two] at hT'Kpc
    exact hT'Kpc

end CFSG.ComponentClassification.Sol78
