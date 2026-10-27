module

public import CFSG.ClassicalGroups.Alternating.I4SpLeviDefs
public import CFSG.ClassicalGroups.Alternating.I4SpLineElt

public section

namespace CFSG.ClassicalGroups.Alternating

open LinearMap (BilinForm)
open Module

variable {K : Type*} [Field K] {N : Type*} [AddCommGroup N] [Module K N] {BN : BilinForm K N}

section Planes

variable [FiniteDimensional K N] (hBN : BN.IsAlt) {ℓ H : Submodule K N}

include hBN in
theorem IsLeviSpace.eq_zero_of_mem_of_mem (hH : IsLeviSpace BN ℓ H) {x : N} (hxH : x ∈ H)
    (hxW : x ∈ BN.orthogonal H) : x = 0 := by
  have h : x ∈ H ⊓ BN.orthogonal H := ⟨hxH, hxW⟩
  rw [(hH.isCompl hBN).inf_eq_bot] at h
  exact (Submodule.mem_bot K).mp h

omit [FiniteDimensional K N] in
theorem leviGroup_fix_line (hH : IsLeviSpace BN ℓ H) {g : Gsp BN} (hg : g ∈ leviGroup BN H)
    {x : N} (hx : x ∈ ℓ) : g.app x = x :=
  hg x (hH.2.1 hx)

omit [FiniteDimensional K N] in
include hBN in
theorem leviGroup_commute_planeGroup (hH : IsLeviSpace BN ℓ H) {g h : Gsp BN}
    (hg : g ∈ leviGroup BN H) (hh : h ∈ planeGroup hBN ℓ) : g * h = h * g := by
  have : planeGroup hBN ℓ ≤ Subgroup.centralizer {g} := by
    rw [planeGroup, Subgroup.closure_le]
    rintro _ ⟨a, ha, c, hc, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro k hk
    rw [Set.mem_singleton_iff.mp hk]
    exact (commute_lineElt_of_app_eq hBN (leviGroup_fix_line hH hg ha)
      (leviGroup_fix_line hH hg hc)).eq
  exact Subgroup.mem_centralizer_iff.mp (this hh) g rfl

variable (hBNnd : BN.Nondegenerate)

include hBN hBNnd in
theorem exists_isPlane_eq_sup (hH : IsLeviSpace BN ℓ H) {π : Submodule K N} (hπ : IsPlane BN π)
    (hℓπ : ℓ ≤ π) :
    ∃ n ∈ BN.orthogonal H, n ≠ 0 ∧ π = ℓ ⊔ Submodule.span K {n} := by
  have hπle : π ≤ ℓ ⊔ BN.orthogonal H := by
    rw [← hH.orthogonal_line hBN hBNnd]
    exact fun p hp l hl => hπ.1 l (hℓπ hl) p hp
  obtain ⟨x, hxπ, hxℓ⟩ : ∃ x ∈ π, x ∉ ℓ := by
    by_contra hcon
    push Not at hcon
    have : π = ℓ := le_antisymm hcon hℓπ
    have h3 := hπ.2
    rw [this, hH.1.2] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨l, hl, w, hw, rfl⟩ := Submodule.mem_sup.mp (hπle hxπ)
  have hwπ : w ∈ π := by
    have := π.sub_mem hxπ (hℓπ hl)
    rwa [add_sub_cancel_left] at this
  have hw0 : w ≠ 0 := by
    rintro rfl
    exact hxℓ (by simpa using hl)
  have hinf : ℓ ⊓ Submodule.span K {w} = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyℓ, hyw⟩
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hyw
    exact (Submodule.mem_bot K).mpr (hH.eq_zero_of_mem_of_mem hBN (hH.2.1 hyℓ)
      ((BN.orthogonal H).smul_mem s hw))
  refine ⟨w, hw, hw0, (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm⟩
  · exact sup_le hℓπ ((Submodule.span_singleton_le_iff_mem w π).mpr hwπ)
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq ℓ (Submodule.span K {w})
    rw [hinf, finrank_bot, add_zero, hH.1.2, finrank_span_singleton hw0] at h1
    rw [h1, hπ.2]

include hBN in
theorem isPlane_sup_span (hH : IsLeviSpace BN ℓ H) {n : N} (hn : n ∈ BN.orthogonal H)
    (hn0 : n ≠ 0) : IsPlane BN (ℓ ⊔ Submodule.span K {n}) := by
  have hnℓ : ∀ l ∈ ℓ, BN l n = 0 := fun l hl => hn l (hH.2.1 hl)
  have hℓn : ∀ l ∈ ℓ, BN n l = 0 := fun l hl => by rw [← hBN.neg_eq, hnℓ l hl, neg_zero]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    obtain ⟨l, hl, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨l', hl', u', hu', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hu'
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hH.1.1 l hl l' hl', hnℓ l hl, hℓn l' hl', hBN.self_eq_zero]
    ring
  · have hinf : ℓ ⊓ Submodule.span K {n} = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyℓ, hyw⟩
      obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hyw
      exact (Submodule.mem_bot K).mpr (hH.eq_zero_of_mem_of_mem hBN (hH.2.1 hyℓ)
        ((BN.orthogonal H).smul_mem s hn))
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq ℓ (Submodule.span K {n})
    rw [hinf, finrank_bot, add_zero, hH.1.2, finrank_span_singleton hn0] at h1
    exact h1

end Planes


section Embedding

variable [FiniteDimensional K N] (hBN : BN.IsAlt) {ℓ H : Submodule K N}
  (hH : IsLeviSpace BN ℓ H)

omit [FiniteDimensional K N] in
theorem orthogonal_orth : ∀ p ∈ H, ∀ w ∈ BN.orthogonal H, BN p w = 0 := fun _ hp _ hw => hw _ hp

@[expose] noncomputable def leviEmb : Gsp (BN.restrict (BN.orthogonal H)) →* Gsp BN :=
  extId (hH.isCompl hBN) hBN orthogonal_orth

theorem leviEmb_app (g : Gsp (BN.restrict (BN.orthogonal H))) {p w : N} (hp : p ∈ H)
    (hw : w ∈ BN.orthogonal H) :
    (leviEmb hBN hH g).app (p + w) = p + (g.app ⟨w, hw⟩ : N) :=
  extId_app (hH.isCompl hBN) hBN orthogonal_orth g hp hw

theorem leviEmb_mem (g : Gsp (BN.restrict (BN.orthogonal H))) :
    leviEmb hBN hH g ∈ leviGroup BN H := fun _ hx =>
  extId_app_of_mem (hH.isCompl hBN) hBN orthogonal_orth g hx

theorem leviEmb_injective : Function.Injective (leviEmb hBN hH) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  refine Gsp.ext' fun w => ?_
  have h := leviEmb_app hBN hH g H.zero_mem w.2
  rw [hg, zero_add, Gsp.app_one] at h
  rw [Gsp.app_one]
  exact Subtype.ext (by simpa using h.symm)

include hBN hH in
theorem exists_leviEmb_eq {g : Gsp BN} (hg : g ∈ leviGroup BN H) :
    ∃ g' : Gsp (BN.restrict (BN.orthogonal H)), leviEmb hBN hH g' = g := by
  have hW : ∀ k ∈ leviGroup BN H, ∀ w ∈ BN.orthogonal H, k.app w ∈ BN.orthogonal H := by
    intro k hk w hw p hp
    have := Gsp.form_app k p w
    rw [hk p hp] at this
    rw [this]
    exact hw p hp
  let f : ↥(BN.orthogonal H) →ₗ[K] ↥(BN.orthogonal H) := g.lin.restrict (hW g hg)
  let f' : ↥(BN.orthogonal H) →ₗ[K] ↥(BN.orthogonal H) :=
    g⁻¹.lin.restrict (hW g⁻¹ (inv_mem hg))
  let e : ↥(BN.orthogonal H) ≃ₗ[K] ↥(BN.orthogonal H) :=
    LinearEquiv.ofLinear f f'
      (LinearMap.ext fun w => Subtype.ext (Gsp.app_app_inv g w))
      (LinearMap.ext fun w => Subtype.ext (Gsp.app_inv_app g w))
  have hiso : ∀ x y : ↥(BN.orthogonal H), (BN.restrict (BN.orthogonal H)) (e x) (e y) =
      (BN.restrict (BN.orthogonal H)) x y := fun x y => Gsp.form_app g x y
  refine ⟨⟨LinearMap.GeneralLinearGroup.ofLinearEquiv e,
    CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mpr hiso⟩, ?_⟩
  refine Gsp.ext' fun v => ?_
  obtain ⟨p, hp, w, hw, rfl⟩ := CFSG.ClassicalGroups.exists_add_eq (hH.isCompl hBN) v
  rw [leviEmb_app hBN hH _ hp hw, Gsp.map_add, hg p hp]
  rfl


@[expose] noncomputable def leviEquiv : Gsp (BN.restrict (BN.orthogonal H)) ≃* leviGroup BN H :=
  MulEquiv.ofBijective ((leviEmb hBN hH).codRestrict (leviGroup BN H) (leviEmb_mem hBN hH))
    ⟨fun _ _ h => leviEmb_injective hBN hH (congrArg Subtype.val h), fun ⟨g, hg⟩ => by
      obtain ⟨g', hg'⟩ := exists_leviEmb_eq hBN hH hg
      exact ⟨g', Subtype.ext hg'⟩⟩

theorem leviEquiv_apply (g : Gsp (BN.restrict (BN.orthogonal H))) :
    ((leviEquiv hBN hH g : leviGroup BN H) : Gsp BN) = leviEmb hBN hH g := rfl

include hBN hH in
theorem nonempty_mulEquiv_leviGroup :
    Nonempty (Gsp (BN.restrict (BN.orthogonal H)) ≃* leviGroup BN H) :=
  ⟨leviEquiv hBN hH⟩

include hBN hH in
theorem IsLeviSpace.restrict_orthogonal_nondegenerate (hBNnd : BN.Nondegenerate) :
    (BN.restrict (BN.orthogonal H)).Nondegenerate := by
  rw [LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal hBN.isRefl,
    LinearMap.BilinForm.orthogonal_orthogonal hBNnd hBN.isRefl]
  exact (hH.isCompl hBN).symm

omit [FiniteDimensional K N] in
theorem map_lin_eq_of_fixed (g : Gsp BN) {S : Submodule K N} (hg : ∀ x ∈ S, g.app x = x) :
    S.map g.lin = S := by
  refine le_antisymm ?_ fun y hy => ⟨y, hy, hg y hy⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [Gsp.lin_apply, hg x hx]
  exact hx

variable (hBNnd : BN.Nondegenerate)

include hBN hBNnd hH in
theorem exists_mem_leviGroup_map_eq {π π' : Submodule K N} (hπ : IsPlane BN π) (hℓπ : ℓ ≤ π)
    (hπ' : IsPlane BN π') (hℓπ' : ℓ ≤ π') : ∃ g ∈ leviGroup BN H, π.map g.lin = π' := by
  obtain ⟨n, hn, hn0, rfl⟩ := exists_isPlane_eq_sup hBN hBNnd hH hπ hℓπ
  obtain ⟨n', hn', hn0', rfl⟩ := exists_isPlane_eq_sup hBN hBNnd hH hπ' hℓπ'
  obtain ⟨g', hg'⟩ := CFSG.ClassicalGroups.Symplectic.exists_gsp_apply_eq (isAlt_restrict hBN _)
    (hH.restrict_orthogonal_nondegenerate hBN hBNnd) (x := ⟨n, hn⟩) (y := ⟨n', hn'⟩)
    (by simpa using hn0) (by simpa using hn0')
  have hgn : (leviEmb hBN hH g').app n = n' := by
    have := leviEmb_app hBN hH g' H.zero_mem hn
    rw [zero_add, zero_add, hg'] at this
    exact this
  refine ⟨leviEmb hBN hH g', leviEmb_mem hBN hH g', ?_⟩
  rw [Submodule.map_sup, Submodule.map_span, Set.image_singleton, Gsp.lin_apply, hgn,
    map_lin_eq_of_fixed _ fun x hx => leviEmb_mem hBN hH g' x (hH.2.1 hx)]

end Embedding


section Root

variable (hBN : BN.IsAlt)

@[expose] noncomputable def rootHom (n : N) : Multiplicative K →* Gsp BN where
  toFun c := Tsp hBN n c.toAdd
  map_one' := by
    show Tsp hBN n 0 = 1
    exact Subtype.ext (symplecticTransvection_zero hBN n)
  map_mul' s t := by
    rw [toAdd_mul]
    exact (Tsp_mul_Tsp hBN n s.toAdd t.toAdd).symm

theorem leviRoot_eq_range (n : N) : leviRoot hBN n = (rootHom hBN n).range := by
  refine le_antisymm ?_ ?_
  · rw [leviRoot, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩
  · rintro _ ⟨t, rfl⟩
    exact Subgroup.subset_closure ⟨t.toAdd, rfl⟩

theorem mem_leviRoot_iff {n : N} {g : Gsp BN} : g ∈ leviRoot hBN n ↔ ∃ c : K, g = Tsp hBN n c := by
  rw [leviRoot_eq_range]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.toAdd, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Multiplicative.ofAdd c, rfl⟩

include hBN in
theorem leviRoot_le_leviGroup {H : Submodule K N} {n : N} (hn : n ∈ BN.orthogonal H) :
    leviRoot hBN n ≤ leviGroup BN H := by
  rw [leviRoot, Subgroup.closure_le]
  rintro _ ⟨c, rfl⟩ x hx
  rw [Tsp_app, hn x hx, mul_zero, zero_smul, add_zero]

variable {ℓ H : Submodule K N}

include hBN in
theorem app_eq_of_mem_leviRoot (hH : IsLeviSpace BN ℓ H) {n : N} (hn : n ∈ BN.orthogonal H)
    {g : Gsp BN} (hg : g ∈ leviRoot hBN n) {x : N} (hx : x ∈ ℓ ⊔ Submodule.span K {n}) :
    g.app x = x := by
  obtain ⟨c, rfl⟩ := (mem_leviRoot_iff hBN).mp hg
  obtain ⟨l, hl, u, hu, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hu
  have h1 : BN l n = 0 := hn l (hH.2.1 hl)
  rw [Gsp.map_add, Gsp.map_smul, Tsp_app, Tsp_app]
  simp [h1, hBN.self_eq_zero]

include hBN in
theorem map_sup_span_eq_of_mem_leviRoot (hH : IsLeviSpace BN ℓ H) {n : N}
    (hn : n ∈ BN.orthogonal H) {g : Gsp BN} (hg : g ∈ leviRoot hBN n) :
    (ℓ ⊔ Submodule.span K {n}).map g.lin = ℓ ⊔ Submodule.span K {n} :=
  map_lin_eq_of_fixed g fun _ hx => app_eq_of_mem_leviRoot hBN hH hn hg hx

include hBN in
theorem mul_self_of_mem_leviRoot [CharP K 2] {n : N} {g : Gsp BN} (hg : g ∈ leviRoot hBN n) :
    g * g = 1 := by
  obtain ⟨c, rfl⟩ := (mem_leviRoot_iff hBN).mp hg
  exact Tsp_mul_self hBN n c

include hBN in
theorem card_leviRoot [FiniteDimensional K N] (hBNnd : BN.Nondegenerate) {n : N} (hn0 : n ≠ 0) :
    Nat.card (leviRoot hBN n) = Nat.card K := by
  have hinj : Function.Injective (rootHom hBN n) := by
    rw [injective_iff_map_eq_one]
    intro t ht
    have : Tsp hBN n t.toAdd = 1 := ht
    rcases (Tsp_eq_one_iff hBN hBNnd n t.toAdd).mp this with h | h
    · exact absurd h hn0
    · exact Multiplicative.toAdd.injective h
  rw [leviRoot_eq_range, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  exact Nat.card_congr Multiplicative.toAdd

include hBN in
theorem leviRoot_ne_of_linearIndependent [FiniteDimensional K N] (hBNnd : BN.Nondegenerate)
    {n n' : N} (hind : LinearIndependent K ![n, n']) : leviRoot hBN n ≠ leviRoot hBN n' := by
  intro h
  have h1 : Tsp hBN n 1 ∈ leviRoot hBN n' := h ▸ (mem_leviRoot_iff hBN).mpr ⟨1, rfl⟩
  obtain ⟨c, hc⟩ := (mem_leviRoot_iff hBN).mp h1
  obtain ⟨z, hz⟩ := exists_apply_eq_of_linearIndependent hBNnd hind ![1, 0]
  have hzn : BN z n = 1 := by simpa using hz 0
  have hzn' : BN z n' = 0 := by simpa using hz 1
  have h2 := congrArg (fun g : Gsp BN => g.app z) hc
  simp only [Tsp_app, hzn, hzn', mul_zero, zero_smul, add_zero, mul_one, one_smul] at h2
  have hn0 : n ≠ 0 := by simpa using hind.ne_zero (0 : Fin 2)
  exact hn0 (add_eq_left.mp h2)

end Root

section Six

variable [Finite K] [CharP K 2] [FiniteDimensional K N] (hBN : BN.IsAlt) (hBNnd : BN.Nondegenerate)
  {ℓ H : Submodule K N} (hH : IsLeviSpace BN ℓ H)

include hBN hBNnd hH in
theorem leviRoot_sup_eq_leviGroup (hdim : finrank K N = 6) {n n' : N}
    (hn : n ∈ BN.orthogonal H) (hn' : n' ∈ BN.orthogonal H) (hind : LinearIndependent K ![n, n']) :
    leviRoot hBN n ⊔ leviRoot hBN n' = leviGroup BN H := by
  have hBW := isAlt_restrict hBN (BN.orthogonal H)
  have hWnd := hH.restrict_orthogonal_nondegenerate hBN hBNnd
  have hWdim : finrank K ↥(BN.orthogonal H) = 2 := by
    rw [hH.finrank_orthogonal hBNnd, hdim]
  have hn0 : n ≠ 0 := by simpa using hind.ne_zero (0 : Fin 2)
  have hn0' : n' ≠ 0 := by simpa using hind.ne_zero (1 : Fin 2)
  have hu0 : (⟨n, hn⟩ : ↥(BN.orthogonal H)) ≠ 0 := fun h => hn0 (congrArg Subtype.val h)
  have hu0' : (⟨n', hn'⟩ : ↥(BN.orthogonal H)) ≠ 0 := fun h => hn0' (congrArg Subtype.val h)
  have hform : (BN.restrict (BN.orthogonal H)) ⟨n', hn'⟩ ⟨n, hn⟩ ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := exists_eq_smul_of_apply_eq_zero hBW hWnd hWdim hu0 (hBW.eq_iff.mp h0)
    have ht' : n' = t • n := congrArg Subtype.val ht
    have := LinearIndependent.pair_iff.mp hind t (-1) (by rw [ht']; module)
    exact one_ne_zero (neg_eq_zero.mp this.2)
  have hLL : Lsp (BN.restrict (BN.orthogonal H)) hBW ⟨n, hn⟩ ⊔
      Lsp (BN.restrict (BN.orthogonal H)) hBW ⟨n', hn'⟩ = ⊤ :=
    by
      rw [Lsp, Lsp, ← Subgroup.subgroupOf_sup (pointRadical_le_bilinIsometryGroup hBW _)
        (pointRadical_le_bilinIsometryGroup hBW _),
        pointRadical_sup_eq_bilinIsometryGroup hBW hWnd hform, Subgroup.subgroupOf_self]
  have hmapTop : (⊤ : Subgroup (Gsp (BN.restrict (BN.orthogonal H)))).map (leviEmb hBN hH) =
      leviGroup BN H := by
    ext g
    constructor
    · rintro ⟨g', -, rfl⟩
      exact leviEmb_mem hBN hH g'
    · intro hg
      obtain ⟨g', hg'⟩ := exists_leviEmb_eq hBN hH hg
      exact ⟨g', trivial, hg'⟩
  have hroot : ∀ v : ↥(BN.orthogonal H), v ≠ 0 →
      (Lsp (BN.restrict (BN.orthogonal H)) hBW v).map (leviEmb hBN hH) = leviRoot hBN (v : N) := by
    intro v hv0
    ext g
    constructor
    · rintro ⟨g', hg', rfl⟩
      obtain ⟨w, c, hw, hgw⟩ := mem_Lsp.mp hg'
      obtain ⟨t, rfl⟩ := exists_eq_smul_of_apply_eq_zero hBW hWnd hWdim hv0 hw
      have : g' = Ssp hBW v (t • v) c := Subtype.ext hgw.symm
      rw [this, Ssp_smul_self]
      exact (mem_leviRoot_iff hBN).mpr ⟨c, extId_Tsp (hH.isCompl hBN) hBN orthogonal_orth v c⟩
    · intro hg
      obtain ⟨c, rfl⟩ := (mem_leviRoot_iff hBN).mp hg
      exact ⟨Tsp hBW v c, Tsp_mem_Lsp hBW v c,
        extId_Tsp (hH.isCompl hBN) hBN orthogonal_orth v c⟩
  have := congrArg (Subgroup.map (leviEmb hBN hH)) hLL
  rwa [Subgroup.map_sup, hroot _ hu0, hroot _ hu0', hmapTop] at this

omit [Finite K] [CharP K 2] in
include hBN hH in
theorem sup_inf_orthogonal_eq {S : Submodule K N} (hS : S ≤ BN.orthogonal H) :
    (ℓ ⊔ S) ⊓ BN.orthogonal H = S := by
  refine le_antisymm ?_ (le_inf le_sup_right hS)
  rintro x ⟨hx, hxW⟩
  obtain ⟨l, hl, t, ht, rfl⟩ := Submodule.mem_sup.mp hx
  have hlW : l ∈ BN.orthogonal H := by
    have := (BN.orthogonal H).sub_mem hxW (hS ht)
    rwa [add_sub_cancel_right] at this
  have hl0 : l = 0 := hH.eq_zero_of_mem_of_mem hBN (hH.2.1 hl) hlW
  rw [hl0, zero_add]
  exact ht

omit [CharP K 2] in
include hBN hBNnd hH in
theorem card_isPlane_through (hdim : finrank K N = 6) :
    Nat.card {π : Submodule K N // IsPlane BN π ∧ ℓ ≤ π} = Nat.card K + 1 := by
  have hWdim : finrank K ↥(BN.orthogonal H) = 2 := by
    rw [hH.finrank_orthogonal hBNnd, hdim]
  rw [← Projectivization.card_of_finrank_two K ↥(BN.orthogonal H) hWdim]
  have hsub : ∀ p : Projectivization K ↥(BN.orthogonal H),
      p.submodule.map (BN.orthogonal H).subtype = Submodule.span K {(p.rep : N)} := by
    intro p
    rw [Projectivization.submodule_eq, Submodule.map_span, Set.image_singleton]
    rfl
  have key : ∀ p : Projectivization K ↥(BN.orthogonal H),
      IsPlane BN (ℓ ⊔ p.submodule.map (BN.orthogonal H).subtype) := by
    intro p
    rw [hsub p]
    exact isPlane_sup_span hBN hH p.rep.2 (fun h => p.rep_nonzero (Subtype.ext h))
  let f : Projectivization K ↥(BN.orthogonal H) →
      {π : Submodule K N // IsPlane BN π ∧ ℓ ≤ π} :=
    fun p => ⟨ℓ ⊔ p.submodule.map (BN.orthogonal H).subtype, key p, le_sup_left⟩
  refine (Nat.card_congr (Equiv.ofBijective f ⟨fun p p' h => ?_, fun π => ?_⟩)).symm
  · have h1 : ℓ ⊔ p.submodule.map (BN.orthogonal H).subtype =
        ℓ ⊔ p'.submodule.map (BN.orthogonal H).subtype := congrArg Subtype.val h
    have h2 := congrArg (· ⊓ BN.orthogonal H) h1
    rw [sup_inf_orthogonal_eq hBN hH (Submodule.map_subtype_le _ _),
      sup_inf_orthogonal_eq hBN hH (Submodule.map_subtype_le _ _)] at h2
    exact Projectivization.submodule_injective
      (Submodule.map_injective_of_injective (BN.orthogonal H).injective_subtype h2)
  · obtain ⟨n, hn, hn0, hπ⟩ := exists_isPlane_eq_sup hBN hBNnd hH π.2.1 π.2.2
    have hn0' : (⟨n, hn⟩ : ↥(BN.orthogonal H)) ≠ 0 := fun h => hn0 (congrArg Subtype.val h)
    refine ⟨Projectivization.mk K ⟨n, hn⟩ hn0', Subtype.ext ?_⟩
    show ℓ ⊔ (Projectivization.mk K ⟨n, hn⟩ hn0').submodule.map (BN.orthogonal H).subtype = π.1
    rw [Projectivization.submodule_mk, Submodule.map_span, Set.image_singleton, hπ]
    rfl

end Six

end CFSG.ClassicalGroups.Alternating
