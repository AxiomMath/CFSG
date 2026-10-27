module

public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialCore
public import CFSG.CharacterTheory.Semidihedral.FixedCoreNontrivialDGroup
public import CFSG.CharacterTheory.Semidihedral.Principal.TrivialCoreTorusSubgroupsSupport

public section

namespace CFSG.Semidihedral.FixedCoreNontrivial

open CFSG.GorensteinWalter

variable {G : Type*} [Group G] {t s d : G} {J B W : Subgroup G}

namespace LocalData

variable (h : LocalData t s d J B W)
include h

theorem d_orderOf : orderOf d = 4 := by
  have h4 : d ^ 2 ^ (1 + 1) = 1 := by
    rw [show 2 ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two, h.d_sq, h.t_sq]
  have h2 : ¬ d ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, h.d_sq]
    exact h.t_ne_one
  exact orderOf_eq_prime_pow h2 h4

theorem d_pow_four : d ^ 4 = 1 := by
  rw [← h.d_orderOf]
  exact pow_orderOf_eq_one d

theorem s_d_inv : s * d * s⁻¹ = d⁻¹ := by
  have hsi := h.s_inv_eq
  have hds : d * s = t * s * d := by
    calc d * s = d * s * d⁻¹ * d := by group
      _ = t * s * d := by rw [h.d_s]
  have hts : s * t = t * s := h.ts.symm
  have htd : t * d = d⁻¹ := by
    have h4 := h.d_pow_four
    rw [eq_inv_iff_mul_eq_one, ← h.d_sq, ← h4]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc s * d * s⁻¹ = s * (d * s) := by rw [hsi, mul_assoc]
    _ = s * (t * s * d) := by rw [hds]
    _ = t * (s * s) * d := by rw [← mul_assoc, ← mul_assoc, hts]; group
    _ = d⁻¹ := by rw [h.s_sq, mul_one, htd]

theorem s_not_mem_J : s ∉ J := by
  intro hs
  rcases h.J_inv s hs h.s_sq with h1 | h1
  · exact h.s_ne_one h1
  · exact h.s_ne h1

theorem s_not_mem_zpowers_d : s ∉ Subgroup.zpowers d := fun hs =>
  h.s_not_mem_J ((Subgroup.zpowers_le.mpr h.d_mem) hs)

theorem ts_ne_one : t * s ≠ 1 := by
  intro h1
  apply h.s_ne
  calc s = t⁻¹ * (t * s) := by group
    _ = t := by rw [h1, mul_one, h.t_inv_eq]

theorem conj_inv_of_three_cycle {g : G} (hgt : g * t * g⁻¹ = s) (hgs : g * s * g⁻¹ = t * s) :
    g⁻¹ * t * g⁻¹⁻¹ = t * s := by
  have h1 : g * (t * s) * g⁻¹ = t := by
    calc g * (t * s) * g⁻¹ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
      _ = s * (t * s) := by rw [hgt, hgs]
      _ = t * (s * s) := by rw [← mul_assoc, ← h.ts, mul_assoc]
      _ = t := by rw [h.s_sq, mul_one]
  calc g⁻¹ * t * g⁻¹⁻¹ = g⁻¹ * (g * (t * s) * g⁻¹) * g := by rw [h1, inv_inv]
    _ = t * s := by group

theorem mem_normalizer_V_of_three_cycle [Finite G] {g : G} (hgt : g * t * g⁻¹ = s)
    (hgs : g * s * g⁻¹ = t * s) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) : Set G) := by
  apply mem_normalizer_of_conj_mem
  intro x hx
  have htV : t ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s ∈ (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  rcases h.mem_V_cases hx with rfl | rfl | rfl | rfl
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · rw [hgt]
    exact hsV
  · rw [hgs]
    exact Subgroup.mul_mem _ htV hsV
  · have h1 : g * (t * s) * g⁻¹ = (g * t * g⁻¹) * (g * s * g⁻¹) := by group
    rw [h1, hgt, hgs]
    exact Subgroup.mul_mem _ hsV (Subgroup.mul_mem _ htV hsV)

end LocalData

variable {G : Type} [Group G] {t s d : G} {J B W : Subgroup G}

theorem LocalData.dgroup_step
    [Finite G] (hL : LocalData t s d J B W)
    (hV : IsKleinFour (Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G))
    (hWodd : Odd (Nat.card W))
    (hsup : Subgroup.zpowers t ⊔ Subgroup.zpowers s ⊔ W =
      Subgroup.centralizer ((Subgroup.zpowers t ⊔ Subgroup.zpowers s : Subgroup G) : Set G))
    (hconf : ∀ u ∈ B, u ≠ 1 →
      Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer ({t} : Set G))
    {g : G} (hgt : g * t * g⁻¹ = s) (hgs : g * s * g⁻¹ = t * s)
    (hgW : g ∈ Subgroup.centralizer (W : Set G))
    (W₀ F : Subgroup G) (hW₀ : W₀ ≤ W) (hne : W₀ ≠ ⊥)
    (hFN : F ≤ Subgroup.normalizer (W₀ : Set G))
    (hCF : Subgroup.centralizer (W₀ : Set G) ≤ F) (hdF : d ∈ F)
    (hM₀ : (Subgroup.centralizer (W₀ : Set G)).relIndex F = 2)
    (P : Sylow 2 F)
    (hP : (P : Subgroup F).map F.subtype = Subgroup.zpowers d ⊔ Subgroup.zpowers s) :
    (CFSG.pPrimeCore 2 F).map F.subtype = W ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (φ : F ⧸ CFSG.pPrimeCore 2 F ≃* CFSG.GorensteinWalter.PGL2 K),
      IsOddPrimePower (Nat.card K) ∧ (Nat.card K % 8 = 3 ∨ Nat.card K % 8 = 5) ∧
      (3 < Nat.card K →
        (((Subgroup.centralizer (W₀ : Set G)).subgroupOf F).map
          (QuotientGroup.mk' (CFSG.pPrimeCore 2 F))).map φ.toMonoidHom =
        (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := K)).range) := by
  classical
  set V : Subgroup G := Subgroup.zpowers t ⊔ Subgroup.zpowers s with hVdef
  have hWCV : W ≤ Subgroup.centralizer (V : Set G) := hsup ▸ le_sup_right
  have hVCW : V ≤ Subgroup.centralizer (W : Set G) := Subgroup.le_centralizer_iff.mpr hWCV
  have hCW₀ : Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (W₀ : Set G) :=
    Subgroup.centralizer_le hW₀
  have hWCW : W ≤ Subgroup.centralizer (W : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact hL.W_comm y hy x hx
  have hVF : V ≤ F := (hVCW.trans hCW₀).trans hCF
  have hWF : W ≤ F := (hWCW.trans hCW₀).trans hCF
  have hgF : g ∈ F := hCF (hCW₀ hgW)
  have hginvF : g⁻¹ ∈ F := F.inv_mem hgF
  have htV : t ∈ V := Subgroup.mem_sup_left (Subgroup.mem_zpowers t)
  have hsV : s ∈ V := Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
  have hsF : s ∈ F := hVF hsV
  have hgV := hL.mem_normalizer_V_of_three_cycle hgt hgs
  have hgN : g ∈ Subgroup.normalizer (W : Set G) := Subgroup.centralizer_le_normalizer _ hgW
  have hg'N : g⁻¹ ∈ Subgroup.normalizer (W : Set G) := Subgroup.inv_mem _ hgN
  have hOle : (CFSG.pPrimeCore 2 F).map F.subtype ≤ W :=
    hL.oddCore_le W₀ hW₀ hne F hFN hVF hV.card_four hgF hginvF hgt
      (hL.conj_inv_of_three_cycle hgt hgs) hgV hgN hg'N hconf
  set d' : F := ⟨d, hdF⟩ with hd'def
  set s' : F := ⟨s, hsF⟩ with hs'def
  set g' : F := ⟨g, hgF⟩ with hg'def
  have hd4 : orderOf d' = 4 := by rw [hd'def, Subgroup.orderOf_mk]; exact hL.d_orderOf
  have hs2 : s' * s' = 1 := Subtype.ext hL.s_sq
  have hsd : s' * d' * s'⁻¹ = d'⁻¹ := Subtype.ext hL.s_d_inv
  have hsnot : s' ∉ Subgroup.zpowers d' := by
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hL.s_not_mem_zpowers_d
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  have hinj := F.subtype_injective
  have hmapV : (Subgroup.zpowers (d' * d') ⊔ Subgroup.zpowers s' : Subgroup F).map F.subtype =
      V := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    change Subgroup.zpowers (d * d) ⊔ Subgroup.zpowers s = V
    rw [hL.d_sq]
  have hV' : (Subgroup.zpowers (d' * d') ⊔ Subgroup.zpowers s' : Subgroup F) = V.subgroupOf F := by
    apply Subgroup.map_injective hinj
    rw [hmapV, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVF]
  have hP' : (P : Subgroup F) = Subgroup.zpowers d' ⊔ Subgroup.zpowers s' := by
    apply Subgroup.map_injective hinj
    rw [hP, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hVK : IsKleinFour (Subgroup.zpowers (d' * d') ⊔ Subgroup.zpowers s' : Subgroup F) := by
    have : IsKleinFour V := hV
    exact isKleinFour_of_mulEquiv ((MulEquiv.subgroupCongr hmapV).symm.trans
      ((Subgroup.zpowers (d' * d') ⊔ Subgroup.zpowers s').equivMapOfInjective F.subtype
        hinj).symm)
  have hWeq : Nat.card (W.subgroupOf F) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWF).toEquiv
  have hWcyc : IsCyclic (W.subgroupOf F) := by
    have := hL.W_cyclic
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hWF).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hWF).symm.surjective
  have hWodd' : Odd (Nat.card (W.subgroupOf F)) := hWeq ▸ hWodd
  have hCV : Subgroup.centralizer
      ((Subgroup.zpowers (d' * d') ⊔ Subgroup.zpowers s' : Subgroup F) : Set F) =
      Subgroup.zpowers (d' * d') ⊔ Subgroup.zpowers s' ⊔ W.subgroupOf F := by
    rw [hV']
    apply Subgroup.map_injective hinj
    rw [Principal.map_centralizer_subgroupOf hVF, Subgroup.map_sup,
      Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVF,
      inf_eq_left.mpr hWF, ← hsup]
    exact inf_eq_right.mpr (sup_le hVF hWF)
  have hdW : ∀ w ∈ W.subgroupOf F, d' * w * d'⁻¹ = w⁻¹ := fun w hw =>
    Subtype.ext (hL.d_inv w (Subgroup.mem_subgroupOf.mp hw))
  have hOW : CFSG.pPrimeCore 2 F ≤ W.subgroupOf F := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hOle ⟨x, hx, rfl⟩)
  have hgt' : g' * (d' * d') * g'⁻¹ = s' := by
    apply Subtype.ext
    change g * (d * d) * g⁻¹ = s
    rw [hL.d_sq, hgt]
  have hgs' : g' * s' * g'⁻¹ = d' * d' * s' := by
    apply Subtype.ext
    change g * s * g⁻¹ = d * d * s
    rw [hL.d_sq, hgs]
  obtain ⟨hcore, K, hKf, hKfin, φ, hK, hmod, hpsl⟩ :=
    quotient_pgl2_of_dihedral_sylow hd4 hs2 hsd hsnot P hP' hVK hM₀ hWcyc hWodd' hCV hdW hOW
      hgt' hgs'
  refine ⟨?_, K, hKf, hKfin, φ, hK, hmod, hpsl⟩
  rw [hcore, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWF]

end CFSG.Semidihedral.FixedCoreNontrivial
