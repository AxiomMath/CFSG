module

public import CFSG.Quasithin.Background.ConjTransport
public import CFSG.CGT.PushingUpLit.CGT6.EmbCbDefs
public import CFSG.Quasithin.Background.B19Basic

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUp CFSG.Open Equiv

variable {V : Type} [CommGroup V] [Finite V] {Y X : Subgroup (MulAut V)} {t : MulAut V} {m : ℕ}

omit [Finite V] in
private theorem cbj_mem_map {g z : MulAut V} :
    z ∈ X.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * z * g ∈ X := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

omit [Finite V] in
private theorem cbj_mem_Y {g z : MulAut V} (hgY : Y.map (MulAut.conj g).toMonoidHom = Y) :
    g⁻¹ * z * g ∈ Y ↔ z ∈ Y := by
  have h := cbj_mem_map (X := Y) (g := g) (z := z)
  rw [hgY] at h
  exact h.symm

omit [Finite V] in
private def cbjθ {A : Type*} [Group A] (g : MulAut V) (θ : ↥X ≃* A) :
    ↥(X.map (MulAut.conj g).toMonoidHom) ≃* A :=
  (MulEquiv.subgroupMap (MulAut.conj g) X).symm.trans θ

omit [Finite V] in
private theorem cbjθ_apply {A : Type*} [Group A] {g z : MulAut V} (θ : ↥X ≃* A)
    (hz : z ∈ X.map (MulAut.conj g).toMonoidHom) (hz' : g⁻¹ * z * g ∈ X) :
    cbjθ g θ ⟨z, hz⟩ = θ ⟨g⁻¹ * z * g, hz'⟩ := rfl

omit [Finite V] in
private theorem cbj_stab {A : Type*} [Group A] {g : MulAut V}
    (hgY : Y.map (MulAut.conj g).toMonoidHom = Y) (θ : ↥X ≃* A) :
    (Y.subgroupOf (X.map (MulAut.conj g).toMonoidHom)).map (cbjθ g θ).toMonoidHom =
      (Y.subgroupOf X).map θ.toMonoidHom := by
  ext s
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨⟨z, hz⟩, hzY, rfl⟩
    exact ⟨⟨g⁻¹ * z * g, cbj_mem_map.mp hz⟩, (cbj_mem_Y hgY).mpr hzY, rfl⟩
  · rintro ⟨⟨x, hx⟩, hxY, rfl⟩
    have hx' : g * x * g⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom :=
      cbj_mem_map.mpr (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group])
    refine ⟨⟨g * x * g⁻¹, hx'⟩, ?_, ?_⟩
    · exact (cbj_mem_Y hgY).mp (by rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group])
    · exact congrArg θ (Subtype.ext (by simp [mul_assoc]))

omit [Finite V] in
private theorem cbj_nat {A M : Type*} [Group A] [Group M] {act : A → M → M} {g : MulAut V}
    (θ : ↥X ≃* A) (h : IsNatSectionWith act θ (commV X) ⊥) :
    IsNatSectionWith act (cbjθ g θ) (commV (X.map (MulAut.conj g).toMonoidHom)) ⊥ := by
  obtain ⟨hinv, β, hsurj, hker, hequiv⟩ := h
  have hmemU : ∀ p : V, p ∈ commV (X.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ p ∈ commV X := by
    intro p
    rw [B19.commV_map_conj, Subgroup.mem_map_equiv]
    rfl
  let ψ : ↥(commV (X.map (MulAut.conj g).toMonoidHom)) →* ↥(commV X) :=
    { toFun := fun p => ⟨g⁻¹ p, (hmemU p).mp p.2⟩
      map_one' := Subtype.ext (map_one _)
      map_mul' := fun p q => Subtype.ext (map_mul _ _ _) }
  have hψ : Function.Surjective ψ := by
    intro q
    refine ⟨⟨g q, (hmemU _).mpr (by simp)⟩, Subtype.ext ?_⟩
    show g⁻¹ (g (q : V)) = (q : V)
    exact MulAut.inv_apply_self V g _
  refine ⟨?_, β.comp ψ, hsurj.comp hψ, ?_, ?_⟩
  · intro x hx p hp
    refine (hmemU _).mpr ?_
    have := hinv _ (cbj_mem_map.mp hx) _ ((hmemU p).mp hp)
    simpa [MulAut.mul_apply] using this
  · ext p
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    rw [← MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf, Subgroup.mem_bot]
    exact map_eq_one_iff g⁻¹ (EquivLike.injective _)
  · rintro ⟨x, hx⟩ p hp
    have hx' : g⁻¹ * x * g ∈ X := cbj_mem_map.mp hx
    have hxp : (g⁻¹ * x * g) (g⁻¹ (p : V)) = g⁻¹ (x p) := by simp [MulAut.mul_apply]
    have hxp' : (g⁻¹ * x * g) (g⁻¹ (p : V)) ∈ commV X := by
      rw [hxp]
      exact (hmemU _).mp hp
    have h1 := hequiv ⟨g⁻¹ * x * g, hx'⟩ ⟨g⁻¹ p.1, (hmemU _).mp p.2⟩ hxp'
    simp only [MonoidHom.comp_apply]
    rw [cbjθ_apply θ hx hx']
    convert h1 using 2
    exact Subtype.ext hxp.symm

omit [Finite V] in
private theorem cbj_mem_fixV {g : MulAut V} (u : V) :
    u ∈ fixV (X.map (MulAut.conj g).toMonoidHom) ↔ g⁻¹ u ∈ fixV X :=
  CFSG.Quasithin.ConjTransport.mem_fixV_map_conj_iff

omit [Finite V] in
private theorem cbj_mem_commV {g : MulAut V} (hgt : g * t * g⁻¹ = t) (u : V) :
    u ∈ commV (Subgroup.zpowers t) ↔ g⁻¹ u ∈ commV (Subgroup.zpowers t) := by
  have h1 : (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers t := by
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply, hgt]
  have h2 := B19.commV_map_conj g (Subgroup.zpowers t)
  rw [h1] at h2
  have h3 : u ∈ (commV (Subgroup.zpowers t)).map g.toMonoidHom ↔
      g⁻¹ u ∈ commV (Subgroup.zpowers t) := Subgroup.mem_map_equiv
  rwa [← h2] at h3

omit [Finite V] in
private theorem cbj_subnormal {G : Subgroup (MulAut V)} {g : MulAut V} (hgG : g ∈ G) {u : V}
    (h : (X.subgroupOf (vecStab G u)).IsSubnormal) :
    ((X.map (MulAut.conj g).toMonoidHom).subgroupOf (vecStab G (g u))).IsSubnormal := by
  have hmem : ∀ z : ↥(vecStab G (g u)), g⁻¹ * (z : MulAut V) * g ∈ vecStab G u := by
    rintro ⟨z, hz⟩
    rw [mem_vecStab] at hz ⊢
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hgG) hz.1) hgG, ?_⟩
    simp [MulAut.mul_apply, hz.2]
  let ψ : ↥(vecStab G (g u)) →* ↥(vecStab G u) :=
    { toFun := fun z => ⟨g⁻¹ * (z : MulAut V) * g, hmem z⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have e : (X.map (MulAut.conj g).toMonoidHom).subgroupOf (vecStab G (g u)) =
      (X.subgroupOf (vecStab G u)).comap ψ := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact cbj_mem_map
  rw [e]
  exact h.comap ψ

set_option linter.unusedSectionVars false in
theorem CbAlg.conj {g : MulAut V} (hgY : Y.map (MulAut.conj g).toMonoidHom = Y)
    (hgt : g * t * g⁻¹ = t) (hX : CbAlg Y t m X) :
    CbAlg Y t m (X.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨θ, a, b, hn, hab, hstab, hnat, hswap⟩ := hX.alt
  have hgt' : g⁻¹ * t * g = t := by
    calc g⁻¹ * t * g = g⁻¹ * (g * t * g⁻¹) * g := by rw [hgt]
      _ = t := by group
  have hkey : ∀ x : MulAut V, g⁻¹ * (t * x * t⁻¹) * g = t * (g⁻¹ * x * g) * t⁻¹ := by
    intro x
    calc g⁻¹ * (t * x * t⁻¹) * g
        = (g⁻¹ * t * g) * (g⁻¹ * x * g) * (g⁻¹ * t * g)⁻¹ := by group
      _ = t * (g⁻¹ * x * g) * t⁻¹ := by rw [hgt']
  have hn' : ∀ x ∈ X.map (MulAut.conj g).toMonoidHom,
      t * x * t⁻¹ ∈ X.map (MulAut.conj g).toMonoidHom := by
    intro x hx
    rw [cbj_mem_map] at hx ⊢
    rw [hkey]
    exact hn _ hx
  refine ⟨?_, cbjθ g θ, a, b, hn', hab, ?_, cbj_nat θ hnat, ?_⟩
  · intro y hy
    rw [cbj_mem_map]
    exact hX.Y_le ((cbj_mem_Y hgY).mpr hy)
  · rw [cbj_stab hgY θ]
    exact hstab
  · intro x hx
    have hx₀ : g⁻¹ * x * g ∈ X := cbj_mem_map.mp hx
    have e1 : cbjθ g θ ⟨x, hx⟩ = θ ⟨g⁻¹ * x * g, hx₀⟩ := cbjθ_apply θ hx hx₀
    have e2 : cbjθ g θ ⟨t * x * t⁻¹, hn' x hx⟩ = θ ⟨t * (g⁻¹ * x * g) * t⁻¹, hn _ hx₀⟩ :=
      (cbjθ_apply θ _ (cbj_mem_map.mp (hn' x hx))).trans (congrArg θ (Subtype.ext (hkey x)))
    rw [e1, e2]
    exact hswap _ hx₀

theorem IsCbLift.conj {G : Subgroup (MulAut V)} {g : MulAut V} (hgG : g ∈ G)
    (hgY : Y.map (MulAut.conj g).toMonoidHom = Y) (hgt : g * t * g⁻¹ = t)
    (hX : IsCbLift G Y t m X) : IsCbLift G Y t m (X.map (MulAut.conj g).toMonoidHom) := by
  have hW : ∀ u : V,
      u ∈ fixV (X.map (MulAut.conj g).toMonoidHom) ⊓ commV (Subgroup.zpowers t) ↔
        g⁻¹ u ∈ fixV X ⊓ commV (Subgroup.zpowers t) := fun u => by
    rw [Subgroup.mem_inf, Subgroup.mem_inf, cbj_mem_fixV, ← cbj_mem_commV hgt]
  refine ⟨CbAlg.conj hgY hgt hX.toCbAlg, ?_, ?_, ?_⟩
  · intro z hz
    have h1 := G.mul_mem (G.mul_mem hgG (hX.le_G (cbj_mem_map.mp hz))) (G.inv_mem hgG)
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group] at h1
  · intro hbot
    apply hX.nontrivial
    rw [Subgroup.eq_bot_iff_forall]
    intro u hu
    have h1 : g u ∈ fixV (X.map (MulAut.conj g).toMonoidHom) ⊓ commV (Subgroup.zpowers t) :=
      (hW _).mpr (by rwa [MulAut.inv_apply_self])
    rw [hbot, Subgroup.mem_bot] at h1
    exact g.injective (h1.trans (map_one g).symm)
  · intro u' hu' hu'1
    obtain ⟨u, rfl⟩ : ∃ u, u' = g u := ⟨g⁻¹ u', (MulAut.apply_inv_self V g u').symm⟩
    have hu : u ∈ fixV X ⊓ commV (Subgroup.zpowers t) := by
      have := (hW _).mp hu'
      rwa [MulAut.inv_apply_self] at this
    have hu1 : u ≠ 1 := fun h => hu'1 (by rw [h, map_one])
    exact cbj_subnormal hgG (hX.subnormal u hu hu1)

end CFSG.CGT.PushingUpLit.CGT6
