module

public import CFSG.LocalAnalysis.OddStandard.AltStdCycTwoStageFRoot
public import CFSG.LocalAnalysis.OddStandard.AltStdSecRootS4

public section

namespace CFSG.OddStandard.AltStdCycTwo.StageF

open Subgroup Equiv AltStdBal AltStdSec CFSG.ComponentClassification.RestrictedStd.Spor
open scoped Pointwise

section Perfect

variable {G : Type} [Group G]

private theorem stageF_mem_sup_of_le_normalizer {W N : Subgroup G}
    (hWN : W ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ W ⊔ N) :
    ∃ w ∈ W, ∃ m ∈ N, w * m = x := by
  have hle : W ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hWN Subgroup.le_normalizer
  have : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hle
  have hx' : (⟨x, hx⟩ : ↥(W ⊔ N)) ∈ W.subgroupOf (W ⊔ N) ⊔ N.subgroupOf (W ⊔ N) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, m, hm, hwm⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨w, hw, m, hm, congrArg Subtype.val hwm⟩

private theorem le_of_isPerfect_of_le_sup {K W N : Subgroup G} (hK : Group.IsPerfect K)
    (hKWN : K ≤ W ⊔ N) (hWN : W ≤ Subgroup.normalizer (N : Set G))
    (hW : Group.IsSolvable W) : K ≤ N := by
  have : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
      (sup_le hWN Subgroup.le_normalizer)
  set U := W ⊔ N with hU
  set π := QuotientGroup.mk' (N.subgroupOf U) with hπ
  have hsolv : Group.IsSolvable (U ⧸ N.subgroupOf U) := by
    have hWs : Group.IsSolvable (W.subgroupOf U) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ U)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ U)).injective
    have hsurj : Function.Surjective (π.comp (W.subgroupOf U).subtype) := by
      intro y
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf U) y
      obtain ⟨w, hw, m, hm, hwm⟩ := stageF_mem_sup_of_le_normalizer hWN u.2
      refine ⟨⟨⟨w, le_sup_left (a := W) hw⟩, hw⟩, ?_⟩
      show QuotientGroup.mk' (N.subgroupOf U) ⟨w, le_sup_left (a := W) hw⟩ =
        QuotientGroup.mk' (N.subgroupOf U) u
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have : (((⟨w, le_sup_left (a := W) hw⟩ : ↥U)⁻¹ * u : ↥U) : G) = m := by
        show w⁻¹ * (u : G) = m
        rw [← hwm]
        group
      rw [this]
      exact hm
    exact Group.isSolvable_of_surjective hsurj
  have hKU : Group.IsPerfect (K.subgroupOf U) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKWN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKWN).symm.surjective
  have hbot : (K.subgroupOf U).map π = ⊥ := by
    by_contra hne
    have : Nontrivial ((K.subgroupOf U).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    have : Group.IsPerfect ((K.subgroupOf U).map π) := Group.IsPerfect.map π
    have : Group.IsSolvable ((K.subgroupOf U).map π) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
    exact Group.IsPerfect.not_isSolvable _ this
  intro x hx
  have h1 : π (⟨x, hKWN hx⟩ : ↥U) ∈ (K.subgroupOf U).map π := ⟨⟨x, hKWN hx⟩, hx, rfl⟩
  rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end Perfect

section Partner

variable {G : Type} [Group G] [Finite G] {L Q : Subgroup G} {n : ℕ} {z : G}

theorem Inner.le_conjSub_of_perfect (c : Inner G L Q n z) {y g : G} (hg : g * z * g⁻¹ = z * y)
    {N : Subgroup G} (hNL : N ≤ L) (hNy : ∀ w ∈ N, w * y = y * w)
    (hNp : Group.IsPerfect N) : N ≤ conjSub g L := by
  obtain ⟨θ⟩ := c.iso
  have hN'C : conjSub g⁻¹ N ≤ centralizer ({z} : Set G) := by
    intro x hx
    have hgx : g * x * g⁻¹ ∈ N := by
      have := mem_conjSub_iff.1 hx
      simpa using this
    have h1 := conj_commute_z hg (mem_centralizer_singleton_iff.1 (c.le_cent (hNL hgx)))
      (hNy _ hgx)
    have h2 : g⁻¹ * (g * x * g⁻¹) * g = x := by group
    rw [h2] at h1
    exact mem_centralizer_singleton_iff.2 h1
  have hN'p : Group.IsPerfect (conjSub g⁻¹ N) := by
    let ψ : ↥N ≃* ↥(conjSub g⁻¹ N) :=
      N.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective
    exact Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hsolv : Group.IsSolvable ↥(centralizer (L : Set G)) :=
    solvable_centralizer_of_weakShape (weakShape_of_cyc c.std.standard θ c.cyc c.card)
  have hle : conjSub g⁻¹ N ≤ centralizer (L : Set G) ⊔ L := by
    rw [sup_comm]
    exact hN'C.trans c.hE
  have hN'L : conjSub g⁻¹ N ≤ L :=
    le_of_isPerfect_of_le_sup hN'p hle (Subgroup.centralizer_le_normalizer _) hsolv
  intro x hx
  rw [mem_conjSub_iff]
  apply hN'L
  rw [mem_conjSub_iff, inv_inv]
  have h3 : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [h3]
  exact hx

theorem Inner.normalizes_conj (c : Inner G L Q n z) {y g : G} (hy : y ∈ L)
    (hg : g * z * g⁻¹ = z * y) {N : Subgroup G} (hNL : N ≤ L)
    (hN : ∀ c ∈ L, c * y = y * c → c ∈ normalizer (N : Set G)) {l : G} (hl : l ∈ L)
    (hly : l * (g⁻¹ * y * g) = (g⁻¹ * y * g) * l) :
    l ∈ normalizer ((conjSub g⁻¹ N : Subgroup G) : Set G) := by
  have hlz : l * z = z * l := mem_centralizer_singleton_iff.1 (c.le_cent hl)
  set c' : G := g * l * g⁻¹ with hc'
  have hc'y : c' * y = y * c' := by
    calc c' * y = g * (l * (g⁻¹ * y * g)) * g⁻¹ := by rw [hc']; group
      _ = g * ((g⁻¹ * y * g) * l) * g⁻¹ := by rw [hly]
      _ = y * c' := by rw [hc']; group
  have hca : c' * (z * y) = (z * y) * c' := by
    rw [← hg]
    calc c' * (g * z * g⁻¹) = g * (l * z) * g⁻¹ := by rw [hc']; group
      _ = g * (z * l) * g⁻¹ := by rw [hlz]
      _ = (g * z * g⁻¹) * c' := by rw [hc']; group
  have hc'z : c' * z = z * c' := by
    have h2 : (c' * z) * y = (z * c') * y := by
      calc (c' * z) * y = c' * (z * y) := by group
        _ = (z * y) * c' := hca
        _ = z * (y * c') := by group
        _ = z * (c' * y) := by rw [hc'y]
        _ = (z * c') * y := by group
    exact mul_right_cancel h2
  have hcmem : c' ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.2 hc'z
  have hKN : centralizer (L : Set G) ≤ normalizer (L : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hm := Subgroup.coe_mul_of_right_le_normalizer_left L (centralizer (L : Set G)) hKN
  have hc'' : c' ∈ (L : Set G) * (centralizer (L : Set G) : Set G) := by
    rw [← hm]
    exact c.hE hcmem
  have hc'N : c' ∈ normalizer (N : Set G) := by
    obtain ⟨l₀, hl₀, k, hk, hlk⟩ := Set.mem_mul.1 hc''
    have hky : k * y = y * k := (mem_centralizer_iff.1 hk y hy).symm
    have hl₀y : l₀ * y = y * l₀ := by
      have h2 : (l₀ * k) * y = y * (l₀ * k) := by rw [hlk]; exact hc'y
      have h3 : (l₀ * y) * k = (y * l₀) * k := by
        calc (l₀ * y) * k = l₀ * (y * k) := by group
          _ = l₀ * (k * y) := by rw [hky]
          _ = (l₀ * k) * y := by group
          _ = y * (l₀ * k) := h2
          _ = (y * l₀) * k := by group
      exact mul_right_cancel h3
    have hkN : k ∈ normalizer (N : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le hNL hk)
    rw [← hlk]
    exact mul_mem (hN _ hl₀ hl₀y) hkN
  exact (mem_normalizer_map_conj_iff (A := N) (g := g⁻¹) (y := l)).2 (by simpa [hc'] using hc'N)

theorem Inner.exists_corr_eq_conj (c : Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n))
    {y g : G} (hy : y ∈ L) (hy2 : orderOf y = 2) (hg : g * z * g⁻¹ = z * y)
    (hf5 : 5 ≤ (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card)
    (hid : NormalAltIdent n
      (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card) :
    ∃ F' : Finset (Fin n),
      F'.card = (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ∧
      conjSub g⁻¹ (corr (X := G) e
        (altSub (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))))) =
        corr (X := G) e (altSub F') := by
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  have hNL : corr (X := G) e (altSub F) ≤ L := corr_le e _
  have hNy : ∀ w ∈ corr (X := G) e (altSub F), w * y = y * w :=
    fun w hw => comm_of_mem_corr_of_fix e hy (fun i hi => mem_fixFin.1 hi) hw
  obtain ⟨φ⟩ := exists_equiv_corr_altSub (X := G) e F
  have hNg : corr (X := G) e (altSub F) ≤ conjSub g L :=
    c.le_conjSub_of_perfect hg hNL hNy ⟨(isQuasisimple_of_alt hf5 φ).1⟩
  have hyg : y ∈ conjSub g L := c.mem_conjSub_of_partner hy hg
  have hyL : g⁻¹ * y * g ∈ L := mem_conjSub_iff.1 hyg
  have hN'L : conjSub g⁻¹ (corr (X := G) e (altSub F)) ≤ L := by
    intro x hx
    have h1 : g * x * g⁻¹ ∈ corr (X := G) e (altSub F) := by
      have := mem_conjSub_iff.1 hx
      simpa using this
    have h2 := mem_conjSub_iff.1 (hNg h1)
    simpa [mul_assoc] using h2
  set ye' : Perm (Fin n) := ((e ⟨g⁻¹ * y * g, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n))
    with hye'
  have hye'2 : orderOf ye' = 2 := by
    rw [hye', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    have : g⁻¹ * y * g = (MulAut.conj g⁻¹) y := by simp
    rw [this, MulEquiv.orderOf_eq]
    exact hy2
  have hKt : permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))) ≤
      centralizer ({ye'} : Set (Perm (Fin n))) := by
    intro σ hσ
    obtain ⟨x, hx, rfl⟩ := (mem_permImg e).1 hσ
    rw [mem_centralizer_singleton_iff]
    have hgx : g * (x : G) * g⁻¹ ∈ corr (X := G) e (altSub F) := by
      simpa using mem_conjSub_iff.1 hx
    have h1 := hNy _ hgx
    have h2 : (x : G) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * x := by
      calc (x : G) * (g⁻¹ * y * g) = g⁻¹ * ((g * x * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * x * g⁻¹)) * g := by rw [h1]
        _ = (g⁻¹ * y * g) * x := by group
    have h3 : x * ⟨g⁻¹ * y * g, hyL⟩ = ⟨g⁻¹ * y * g, hyL⟩ * x := Subtype.ext h2
    have h4 := congrArg e h3
    rw [map_mul, map_mul] at h4
    exact congrArg Subtype.val h4
  have hKn : ∀ c ∈ alternatingGroup (Fin n), c ∈ centralizer ({ye'} : Set (Perm (Fin n))) →
      ∀ k ∈ permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))),
        c * k * c⁻¹ ∈ permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))) := by
    intro c₀ hcA hcC k hk
    obtain ⟨x, hx, rfl⟩ := (mem_permImg e).1 hk
    set l : L := e.symm ⟨c₀, hcA⟩ with hl
    have hel : e l = ⟨c₀, hcA⟩ := by simp [hl]
    have hly : (l : G) * (g⁻¹ * y * g) = (g⁻¹ * y * g) * l := by
      have h1 : c₀ * ye' = ye' * c₀ := mem_centralizer_singleton_iff.1 hcC
      have h2 : e (l * ⟨g⁻¹ * y * g, hyL⟩) = e (⟨g⁻¹ * y * g, hyL⟩ * l) := by
        rw [map_mul, map_mul, hel]
        exact Subtype.ext h1
      exact congrArg Subtype.val (e.injective h2)
    have hnorm := c.normalizes_conj hy hg hNL
      (fun c' hc' hc'y => mem_normalizer_corr_fix e hy hc' hc'y) l.2 hly
    have hx' : (l : G) * x * (l : G)⁻¹ ∈ conjSub g⁻¹ (corr (X := G) e (altSub F)) :=
      (mem_normalizer_iff.1 hnorm _).1 hx
    refine (mem_permImg e).2 ⟨l * x * l⁻¹, hx', ?_⟩
    rw [map_mul, map_mul, map_inv, hel]
    rfl
  have hKequiv : Nonempty (permImg e (conjSub g⁻¹ (corr (X := G) e (altSub F))) ≃*
      alternatingGroup (Fin F.card)) := by
    let ψ : ↥(corr (X := G) e (altSub F)) ≃* ↥(conjSub g⁻¹ (corr (X := G) e (altSub F))) :=
      (corr (X := G) e (altSub F)).equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective
    exact ⟨((permImgEquiv e hN'L).symm.trans ψ.symm).trans φ⟩
  obtain ⟨hKeq, hcard⟩ := hid ye' hye'2 (e ⟨g⁻¹ * y * g, hyL⟩).2 _ (permImg_le_alt e _) hKt hKn
    hKequiv
  refine ⟨fixFin ye', hcard, ?_⟩
  rw [← hKeq]
  exact (corr_permImg e hN'L).symm

theorem Inner.exists_common_root_of_fix (c : Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n))
    {y g : G} (hy : y ∈ L) (hy2 : orderOf y = 2) (hg : g * z * g⁻¹ = z * y)
    (hf5 : 5 ≤ (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card)
    (hf6 : (fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card ≠ 6)
    {S : Finset (Fin n)}
    (hS : ∀ i ∈ S, ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i) :
    ∃ S₁ : Finset (Fin n), S₁.card = S.card ∧
      rootGroup (G := G) e S = conjSub g (rootGroup e S₁) := by
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hy⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  obtain ⟨F', hcard, hconj⟩ :=
    c.exists_corr_eq_conj e hy hy2 hg hf5 (normalAltIdent_of_five_le hf5)
  have hFF' : ∀ x ∈ corr (X := G) e (altSub F), g⁻¹ * x * g ∈ corr (X := G) e (altSub F') := by
    intro x hx
    rw [← hconj]
    refine mem_conjSub_iff.2 ?_
    have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
    simpa [this] using hx
  have hF'F : ∀ x ∈ corr (X := G) e (altSub F'), g * x * g⁻¹ ∈ corr (X := G) e (altSub F) := by
    intro x hx
    rw [← hconj] at hx
    simpa using mem_conjSub_iff.1 hx
  obtain ⟨β, hβ1, hβ2, hβ3, hβ4⟩ :=
    exists_conj_intertwining e g hcard.symm (Or.inl ⟨hf5, hf6⟩) hFF' hF'F
  have hSF : S ⊆ F := fun i hi => mem_fixFin.2 (hS i hi)
  refine ⟨S.image β, ?_, rootGroup_eq_conjSub_image e g hFF' hF'F hβ1 hβ2 hβ3 hβ4 hSF⟩
  exact Finset.card_image_of_injOn fun i hi j hj hij => hβ2 i (hSF hi) j (hSF hj) hij

theorem Inner.isZStar_rootGroup_of_card_eq (c : Inner G L Q n z)
    (e : L ≃* alternatingGroup (Fin n)) {S S' : Finset (Fin n)} (hS : S.card = S'.card)
    (h2 : 2 ≤ S.card) (hz : IsZStar (rootGroup e S) z) : IsZStar (rootGroup e S') z := by
  obtain ⟨σ, hσ, himg⟩ := exists_even_perm_image_eq hS h2
  set l : L := e.symm ⟨σ, Perm.mem_alternatingGroup.2 hσ⟩ with hl
  have hlz : (l : G) * z * (l : G)⁻¹ = z := by
    have := mem_centralizer_singleton_iff.1 (c.le_cent l.2)
    rw [this]
    group
  have := hz.conj (l : G)
  rw [hlz, ← rootGroup_eq_conjSub e hσ himg] at this
  exact this

theorem Inner.isZStar_rootGroup_iff (c : Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n))
    {S S' : Finset (Fin n)} (hS : S.card = S'.card) (h2 : 2 ≤ S.card) :
    IsZStar (rootGroup e S) z ↔ IsZStar (rootGroup e S') z :=
  ⟨c.isZStar_rootGroup_of_card_eq e hS h2, c.isZStar_rootGroup_of_card_eq e hS.symm (hS ▸ h2)⟩

theorem Inner.false_of_zstar_common_root (hlookup : AltComponentLookup)
    (hHN : HNLocalComponentsInput) (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple)
    (hFour : FourExactOuterInput) (c : Inner G L Q n z) (e : L ≃* alternatingGroup (Fin n))
    {y g : G} (hy : y ∈ FusionSet L z) (hg : g * z * g⁻¹ = z * y) {S S₁ : Finset (Fin n)}
    (hS : S.card = 3 ∨ S.card = 4) (hyC : y ∈ centralizer (rootGroup e S : Set G))
    (hcomm : rootGroup (G := G) e S = conjSub g (rootGroup e S₁))
    (h1 : IsZStar (rootGroup e S) z) (h2 : IsZStar (rootGroup e S₁) z) : False := by
  have hSc : 9 ≤ n - S.card := by
    have := c.hn
    omega
  have hRD := c.rootData hlookup hHN hOut hFour e hS hSc
  have h2' : IsZStar (rootGroup (G := G) e S) (z * y) := by
    have := h2.conj g
    rw [← hcomm, hg] at this
    exact this
  exact false_of_isZStar_pair c.cyc hRD (by omega) hy.2.1 hy.1 hyC h1 h2'

theorem Inner.nearGives (hlookup : AltComponentLookup) (hHN : HNLocalComponentsInput)
    (hOut : CFSG.RankThree.PartOne.SporadicOuterOrderLeTwoSimple) (hFour : FourExactOuterInput)
    (c : Inner G L Q n z) (hodd : Odd n) (e : L ≃* alternatingGroup (Fin n)) {k : ℕ} (hk3 : 3 ≤ k)
    (hk4 : k ≤ 4) {y : G} (hy : y ∈ FusionSet L z)
    (hf4 : 4 ≤ (fixFin ((e ⟨y, hy.1⟩ : alternatingGroup (Fin n)) : Perm (Fin n))).card) :
    ∃ S : Finset (Fin n), S.card = k ∧ ∀ b ∈ L, b ∈ centralizer (rootGroup e S : Set G) →
      orderOf b = 2 → ∃ h' ∈ centralizer (rootGroup e S : Set G), h' * z * h'⁻¹ = z * b := by
  obtain ⟨hyL, hy2, g, hg⟩ := hy
  set F : Finset (Fin n) :=
    fixFin ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) with hF
  have hf4' : 4 ≤ F.card := hf4
  have hodd : Odd F.card :=
    odd_card_fixFin hodd (orderOf_perm_of_mem e hyL hy2)
      (Perm.mem_alternatingGroup.1 (e ⟨y, hyL⟩).2)
  obtain ⟨j, hj⟩ := hodd
  have hf5 : 5 ≤ F.card := by omega
  have hf6 : F.card ≠ 6 := by omega
  obtain ⟨S, hSF, hSk⟩ := Finset.exists_subset_card_eq (by omega : k ≤ F.card)
  refine ⟨S, hSk, ?_⟩
  rcases c.zstar_or_fusion hlookup hHN hOut hFour e hk3 hk4 S hSk with hz | hfus
  · exfalso
    have hfS : ∀ i ∈ S, ((e ⟨y, hyL⟩ : alternatingGroup (Fin n)) : Perm (Fin n)) i = i :=
      fun i hi => mem_fixFin.1 (hSF hi)
    obtain ⟨S₁, hS₁c, hS₁⟩ := c.exists_common_root_of_fix e hyL hy2 hg hf5 hf6 hfS
    have hS' : S.card = 3 ∨ S.card = 4 := by omega
    have hz₁ : IsZStar (rootGroup e S₁) z :=
      (c.isZStar_rootGroup_iff e hS₁c.symm (by omega)).1 hz
    exact c.false_of_zstar_common_root hlookup hHN hOut hFour e ⟨hyL, hy2, g, hg⟩ hg hS'
      (mem_centralizer_rootGroup_of_fix e hyL hfS) hS₁ hz hz₁
  · exact hfus

end Partner

end CFSG.OddStandard.AltStdCycTwo.StageF
