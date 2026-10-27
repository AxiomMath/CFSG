module

public import CFSG.GH74.GLS.Types
public import CFSG.GH74.Uniqueness.Statements

import CFSG.GH74.GLS.NT44.ConjugateFusion
import CFSG.GH74.GLS.C3.Layer1.U1a
import CFSG.GH74.GLS.Bg.Iii2.L41Basic

set_option autoImplicit false

public section

namespace CFSG.GH74.GLS.NT44

open Subgroup

theorem isProductDisconnected_conjugatesOf_of_gammaK_conjugate_closure_ne_top
    {G : Type} [Group G] [Finite G]
    {T : Subgroup G} {x : G}
    (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤)
    (hx2 : orderOf x = 2)
    (hxT : x ∈ T)
    (hTC : T ≤ Subgroup.centralizer ({x} : Set G))
    (hZel : CFSG.IsElementaryAbelian 2
      ↥(Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}))
    (hZrank : 2 ≤ CFSG.pRank 2
      ↥(Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}))
    (hGamma : CFSG.GH74.GLS.gammaK 2
      (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) 1 ≠ ⊤) :
    CFSG.GH74.Uniqueness.IsProductDisconnected (conjugatesOf x)
      (CFSG.GH74.GLS.gammaK 2
        (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a}) 1) := by
  classical
  set Z : Subgroup G := Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} with hZdef
  set M : Subgroup G := gammaK 2 Z 1 with hMdef
  have hxZ : x ∈ Z := by
    rw [hZdef]
    exact Subgroup.subset_closure ⟨hxT, IsConj.refl x⟩
  have hZcomm : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a := by
    have : IsMulCommutative Z := hZel.toIsMulCommutative
    intro a ha b hb
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := Z)).comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hCx_le_M : Subgroup.centralizer ({x} : Set G) ≤ M := by
    rw [hMdef]
    exact CFSG.GH74.GLS.C3.Layer1.U1a.centralizer_le_gammaK hxZ hx2
  have hxM : x ∈ M := by
    refine hCx_le_M ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
  have hTN : T ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hZdef, Subgroup.le_normalizer_closure_iff]
    intro t ht a ha
    exact Subgroup.subset_closure
      ⟨T.mul_mem (T.mul_mem ht ha.1) (T.inv_mem ht),
        ha.2.trans (isConj_iff.mpr ⟨t, rfl⟩)⟩
  have hNM : Subgroup.normalizer (Z : Set G) ≤ M := by
    rw [hMdef]
    unfold gammaK
    refine le_iSup₂_of_le Z le_rfl ?_
    exact le_iSup_of_le (le_trans (by decide : 1 ≤ 2) hZrank) le_rfl
  have hTM : T ≤ M := hTN.trans hNM
  have hTsylowM : CFSG.ABGLocalTools.IsSylowOf 2 T M :=
    hT.of_le hTM le_top
  have h_order_conj : ∀ (a z : G), orderOf (a * z * a⁻¹) = orderOf z := by
    intro a z
    have hsem : SemiconjBy a z (a * z * a⁻¹) := by
      unfold SemiconjBy
      group
    exact (SemiconjBy.orderOf_eq a hsem).symm
  have hseed : ∀ g : G, g⁻¹ * x * g ∈ M ↔ g ∈ M := by
    intro g
    constructor
    · intro hgM
      have hg2 : orderOf (g⁻¹ * x * g) = 2 := by
        simpa using (h_order_conj (g⁻¹) x).trans hx2
      obtain ⟨p, hpM, hpconj⟩ :=
        CFSG.GH74.GLS.Bg.Iii2.L41.exists_conj_mem_sylow
          (H := M) (Q := T) hTsylowM (t := g⁻¹ * x * g) hgM hg2
      let m : G := p⁻¹
      let y : G := (g * m)⁻¹ * x * (g * m)
      have hmM : m ∈ M := by
        dsimp [m]
        exact M.inv_mem hpM
      have hyT : y ∈ T := by
        have he : y = p * (g⁻¹ * x * g) * p⁻¹ := by
          dsimp [y, m]
          group
        rw [he]
        exact hpconj
      have hyZ : y ∈ Z := by
        rw [hZdef]
        exact Subgroup.subset_closure
          ⟨hyT, isConj_iff.mpr ⟨(g * m)⁻¹, by dsimp [y]; group⟩⟩
      have hyC : y ∈ Subgroup.centralizer (Z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hZcomm y hyZ z hz).symm
      have hxC : x ∈ Subgroup.centralizer (Z : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (hZcomm x hxZ z hz).symm
      have hD : ({x} : Set G) ⊆
          (Subgroup.centralizer
            (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G) : Set G) := by
        intro d hd
        rw [Set.mem_singleton_iff] at hd
        subst d
        simpa [hZdef] using hxC
      have hDg : (fun d : G => (g * m)⁻¹ * d * ((g * m)⁻¹)⁻¹) '' ({x} : Set G) ⊆
          (Subgroup.centralizer
            (Subgroup.closure {a : G | a ∈ T ∧ IsConj x a} : Set G) : Set G) := by
        rintro _ ⟨d, hd, rfl⟩
        rw [Set.mem_singleton_iff] at hd
        subst d
        simpa [hZdef, y] using hyC
      obtain ⟨n, hnN, hnconj⟩ :=
        exists_normalizer_conj_eq_on_of_conjugate_closure
          (T := T) (x := x) (hT := hT) (D := ({x} : Set G))
          (g := (g * m)⁻¹) hD hDg
      have hnx : n * x * n⁻¹ = (g * m)⁻¹ * x * (g * m) := by
        have hn := hnconj x (by simp)
        simpa using hn
      have hnM : n ∈ M := by
        refine hNM ?_
        simpa [hZdef] using hnN
      have hgmCx : (g * m) * n ∈ Subgroup.centralizer ({x} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 : ((g * m) * n) * x * ((g * m) * n)⁻¹ = x := by
          calc (g * m) * n * x * ((g * m) * n)⁻¹
              = (g * m) * (n * x * n⁻¹) * (g * m)⁻¹ := by group
            _ = (g * m) * ((g * m)⁻¹ * x * (g * m)) * (g * m)⁻¹ := by rw [hnx]
            _ = x := by group
        calc ((g * m) * n) * x
            = (((g * m) * n) * x * ((g * m) * n)⁻¹) * ((g * m) * n) := by group
          _ = x * ((g * m) * n) := by rw [h1]
      have hgmM : (g * m) * n ∈ M := hCx_le_M hgmCx
      have hg_eq : g = ((g * m) * n) * n⁻¹ * m⁻¹ := by group
      rw [hg_eq]
      exact M.mul_mem (M.mul_mem hgmM (M.inv_mem hnM)) (M.inv_mem hmM)
    · intro hg
      exact M.mul_mem (M.mul_mem (M.inv_mem hg) hxM) hg
  have hall : ∀ z ∈ conjugatesOf x, z ∈ M →
      ∀ g : G, g⁻¹ * z * g ∈ M ↔ g ∈ M := by
    intro z hz hzM g
    have hz_conj : IsConj x z := hz
    obtain ⟨k, hk⟩ := isConj_iff.mp hz_conj
    have hk_inv_M : k⁻¹ ∈ M := by
      refine (hseed k⁻¹).mp ?_
      have hkz : (k⁻¹)⁻¹ * x * k⁻¹ = z := by
        rw [← hk]
        group
      rw [hkz]
      exact hzM
    have hkM : k ∈ M := by
      simpa using M.inv_mem hk_inv_M
    have hg_eq : g⁻¹ * z * g = (k⁻¹ * g)⁻¹ * x * (k⁻¹ * g) := by
      rw [← hk]
      group
    rw [hg_eq, hseed (k⁻¹ * g)]
    constructor
    · intro hkg
      have hg_eq' : g = k * (k⁻¹ * g) := by group
      rw [hg_eq']
      exact M.mul_mem hkM hkg
    · intro hg
      exact M.mul_mem hk_inv_M hg
  have hprod : ∀ u ∈ CFSG.GH74.Uniqueness.productInvolutions (conjugatesOf x), u ∈ M →
      Subgroup.centralizer ({u} : Set G) ≤ M := by
    intro u hu huM
    obtain ⟨hu2, s, hs, t, ht, hst, hu_eq⟩ := hu
    obtain ⟨a, haM, hauT⟩ :=
      CFSG.GH74.GLS.Bg.Iii2.L41.exists_conj_mem_sylow
        (H := M) (Q := T) hTsylowM (t := u) huM hu2
    let v : G := a * u * a⁻¹
    let s' : G := a * s * a⁻¹
    let t' : G := a * t * a⁻¹
    have hvT : v ∈ T := hauT
    have hvdef : v = a * u * a⁻¹ := rfl
    have hs'def : s' = a * s * a⁻¹ := rfl
    have ht'def : t' = a * t * a⁻¹ := rfl
    have hs_conj : IsConj x s := hs
    have ht_conj : IsConj x t := ht
    have hs'_conj : IsConj x s' := by
      refine hs_conj.trans ?_
      rw [hs'def]
      exact isConj_iff.mpr ⟨a, rfl⟩
    have ht'_conj : IsConj x t' := by
      refine ht_conj.trans ?_
      rw [ht'def]
      exact isConj_iff.mpr ⟨a, rfl⟩
    have hv2 : orderOf v = 2 := by
      rw [hvdef]
      exact (h_order_conj a u).trans hu2
    have hst' : s' * t' = t' * s' := by
      rw [hs'def, ht'def]
      calc (a * s * a⁻¹) * (a * t * a⁻¹) = a * (s * t) * a⁻¹ := by group
        _ = a * (t * s) * a⁻¹ := by rw [hst]
        _ = (a * t * a⁻¹) * (a * s * a⁻¹) := by group
    have hv_eq : v = s' * t' := by
      rw [hvdef, hs'def, ht'def, hu_eq]
      group
    obtain ⟨c₀, hc₀⟩ := isConj_iff.mp hs'_conj
    let g : G := c₀⁻¹
    have hs'g : s' = g⁻¹ * x * g := by
      dsimp [g]
      rw [← hc₀]
      group
    have hgsg : g * s' * g⁻¹ = x := by
      rw [hs'g]
      group
    let t₀ : G := g * t' * g⁻¹
    have ht'comm : t' * s' = s' * t' := hst'.symm
    have ht₀Cx : t₀ ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      dsimp [t₀]
      calc (g * t' * g⁻¹) * x = g * t' * s' * g⁻¹ := by rw [← hgsg]; group
        _ = g * (t' * s') * g⁻¹ := by group
        _ = g * (s' * t') * g⁻¹ := by rw [ht'comm]
        _ = x * (g * t' * g⁻¹) := by rw [← hgsg]; group
    have ht'2 : orderOf t' = 2 := by
      obtain ⟨q, hq⟩ := isConj_iff.mp ht'_conj
      rw [← hq]
      exact (h_order_conj q x).trans hx2
    have ht₀2 : orderOf t₀ = 2 := by
      dsimp [t₀]
      exact (h_order_conj g t').trans ht'2
    obtain ⟨p, hpCx, hpconj⟩ :=
      CFSG.GH74.GLS.Bg.Iii2.L41.exists_conj_mem_sylow
        (H := Subgroup.centralizer ({x} : Set G)) (Q := T)
        (hT.of_le hTC le_top) (t := t₀) ht₀Cx ht₀2
    let d : G := p⁻¹
    let c : G := g⁻¹ * d * g
    have hdCx : d ∈ Subgroup.centralizer ({x} : Set G) := by
      dsimp [d]
      exact (Subgroup.centralizer ({x} : Set G)).inv_mem hpCx
    have hdM : d ∈ M := hCx_le_M hdCx
    have hdcomm : d * x = x * d :=
      Subgroup.mem_centralizer_singleton_iff.mp hdCx
    have hdt₀T : d⁻¹ * t₀ * d ∈ T := by
      dsimp [d]
      simpa using hpconj
    have hcCs : c ∈ Subgroup.centralizer ({s'} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff, hs'g]
      dsimp [c]
      calc (g⁻¹ * d * g) * (g⁻¹ * x * g) = g⁻¹ * (d * x) * g := by group
        _ = g⁻¹ * (x * d) * g := by rw [hdcomm]
        _ = (g⁻¹ * x * g) * (g⁻¹ * d * g) := by group
    have hc_s : c⁻¹ * s' * c = s' := by
      have hcs := Subgroup.mem_centralizer_singleton_iff.mp hcCs
      calc c⁻¹ * s' * c = c⁻¹ * (s' * c) := by group
        _ = c⁻¹ * (c * s') := by rw [hcs]
        _ = s' := by group
    have htcT : g * (c⁻¹ * t' * c) * g⁻¹ ∈ T := by
      have he : c⁻¹ * t' * c = g⁻¹ * (d⁻¹ * t₀ * d) * g := by
        dsimp [c, t₀]
        group
      have he2 : g * (c⁻¹ * t' * c) * g⁻¹ = d⁻¹ * t₀ * d := by
        rw [he]
        group
      rw [he2]
      exact hdt₀T
    have htcZ : g * (c⁻¹ * t' * c) * g⁻¹ ∈ Z := by
      have he : g * (c⁻¹ * t' * c) * g⁻¹ = d⁻¹ * t₀ * d := by
        have h1 : c⁻¹ * t' * c = g⁻¹ * (d⁻¹ * t₀ * d) * g := by
          dsimp [c, t₀]
          group
        calc g * (c⁻¹ * t' * c) * g⁻¹
            = g * (g⁻¹ * (d⁻¹ * t₀ * d) * g) * g⁻¹ := by rw [h1]
          _ = d⁻¹ * t₀ * d := by group
      rw [he, hZdef]
      refine Subgroup.subset_closure ⟨hdt₀T, ?_⟩
      have h1 : IsConj x t₀ := ht'_conj.trans (by
        dsimp [t₀]
        exact isConj_iff.mpr ⟨g, rfl⟩)
      exact h1.trans (isConj_iff.mpr ⟨d⁻¹, by group⟩)
    let w : G := g * (c⁻¹ * v * c) * g⁻¹
    have hvc : c⁻¹ * v * c = s' * (c⁻¹ * t' * c) := by
      rw [hv_eq]
      calc c⁻¹ * (s' * t') * c = (c⁻¹ * s' * c) * (c⁻¹ * t' * c) := by group
        _ = s' * (c⁻¹ * t' * c) := by rw [hc_s]
    have hwZ : w ∈ Z := by
      have he : w = (g * s' * g⁻¹) * (g * (c⁻¹ * t' * c) * g⁻¹) := by
        dsimp [w]
        rw [hvc]
        group
      rw [he, hgsg]
      exact Z.mul_mem hxZ htcZ
    have hw_eq : w = (g * c⁻¹) * v * (g * c⁻¹)⁻¹ := by
      dsimp [w]
      group
    have hw2 : orderOf w = 2 := by
      rw [hw_eq]
      exact (h_order_conj (g * c⁻¹) v).trans hv2
    have hCw : Subgroup.centralizer ({w} : Set G) ≤ M := by
      rw [hMdef]
      exact CFSG.GH74.GLS.C3.Layer1.U1a.centralizer_le_gammaK hwZ hw2
    have hwdef : w = (c * g⁻¹)⁻¹ * v * (c * g⁻¹) := by
      dsimp [w]
      group
    have hCv_le_map : Subgroup.centralizer ({v} : Set G) ≤
        M.map (MulAut.conj (c * g⁻¹)).toMonoidHom := by
      intro z hz
      have hzW : (c * g⁻¹)⁻¹ * z * (c * g⁻¹) ∈
          Subgroup.centralizer ({w} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
        rw [hwdef]
        calc ((c * g⁻¹)⁻¹ * z * (c * g⁻¹)) * ((c * g⁻¹)⁻¹ * v * (c * g⁻¹))
            = (c * g⁻¹)⁻¹ * (z * v) * (c * g⁻¹) := by group
          _ = (c * g⁻¹)⁻¹ * (v * z) * (c * g⁻¹) := by rw [hz]
          _ = ((c * g⁻¹)⁻¹ * v * (c * g⁻¹)) *
              ((c * g⁻¹)⁻¹ * z * (c * g⁻¹)) := by group
      have hzM := hCw hzW
      rw [Subgroup.mem_map]
      refine ⟨(c * g⁻¹)⁻¹ * z * (c * g⁻¹), hzM, ?_⟩
      change (c * g⁻¹) * ((c * g⁻¹)⁻¹ * z * (c * g⁻¹)) * (c * g⁻¹)⁻¹ = z
      group
    have hxv : x ∈ Subgroup.centralizer ({v} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hTC hvT)).symm
    have hxMk : x ∈ M.map (MulAut.conj (c * g⁻¹)).toMonoidHom := hCv_le_map hxv
    rw [Subgroup.mem_map] at hxMk
    obtain ⟨m, hmM, hmx⟩ := hxMk
    have hxMg : x ∈ M.map (MulAut.conj (g⁻¹)).toMonoidHom := by
      rw [Subgroup.mem_map]
      refine ⟨d * m * d⁻¹, M.mul_mem (M.mul_mem hdM hmM) (M.inv_mem hdM), ?_⟩
      change (c * g⁻¹) * m * (c * g⁻¹)⁻¹ = x at hmx
      change g⁻¹ * (d * m * d⁻¹) * (g⁻¹)⁻¹ = x
      have hcdef : c = g⁻¹ * d * g := rfl
      rw [hcdef] at hmx
      calc g⁻¹ * (d * m * d⁻¹) * (g⁻¹)⁻¹
          = (g⁻¹ * d * g * g⁻¹) * m * (g⁻¹ * d * g * g⁻¹)⁻¹ := by group
        _ = x := hmx
    have hgxM : g * x * g⁻¹ ∈ M := by
      rw [Subgroup.mem_map_equiv] at hxMg
      simpa [MulAut.conj_symm_apply] using hxMg
    have hg_inv_M : g⁻¹ ∈ M := by
      refine (hseed g⁻¹).mp ?_
      simpa using hgxM
    have hgM : g ∈ M := by
      simpa using M.inv_mem hg_inv_M
    have hcM : c ∈ M := by
      have hcdef : c = g⁻¹ * d * g := rfl
      rw [hcdef]
      exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hdM) hgM
    have hcgM : c * g⁻¹ ∈ M := M.mul_mem hcM (M.inv_mem hgM)
    have hMmap : M.map (MulAut.conj (c * g⁻¹)).toMonoidHom = M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hcgM)
    have hCv_le_M : Subgroup.centralizer ({v} : Set G) ≤ M := by
      calc Subgroup.centralizer ({v} : Set G) ≤
            M.map (MulAut.conj (c * g⁻¹)).toMonoidHom := hCv_le_map
        _ = M := hMmap
    have hCu_le_M : Subgroup.centralizer ({u} : Set G) ≤ M := by
      intro z hz
      have hzV : a * z * a⁻¹ ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
        rw [hvdef]
        calc (a * z * a⁻¹) * (a * u * a⁻¹) = a * (z * u) * a⁻¹ := by group
          _ = a * (u * z) * a⁻¹ := by rw [hz]
          _ = (a * u * a⁻¹) * (a * z * a⁻¹) := by group
      have hzM := hCv_le_M hzV
      have hz_eq : z = a⁻¹ * (a * z * a⁻¹) * a := by group
      rw [hz_eq]
      exact M.mul_mem (M.mul_mem (M.inv_mem haM) hzM) haM
    exact hCu_le_M
  refine ⟨?_, ?_, hall, hprod⟩
  · exact hGamma
  · exact ⟨x, mem_conjugatesOf_self, hxM⟩

end CFSG.GH74.GLS.NT44

end
