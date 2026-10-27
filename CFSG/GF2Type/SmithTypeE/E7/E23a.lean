module

public import CFSG.GF2Type.SmithTypeE.E7.E23aStd
public import CFSG.GF2Type.SmithTypeE.E7.E23aCard
public import CFSG.GF2Type.SmithTypeE.E7.IdentLift
public import CFSG.GF2Type.SmithTypeE.E7.Compat
public import CFSG.LargeExtraspecial.S14SMHLevi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.SmithD6 (ea7InF0)
open CFSG.GF2Type.SmithTypeE.DMod

variable {G : Type} [Group G] [Finite G]

@[expose] def E23aConcl (S : Setting G) (t u : G) : Prop :=
  IsExtraspecialPGroup 2 ↥(S.QG ⊓ cent2 t u) ∧
  Nat.card ↥(S.QG ⊓ cent2 t u) = 2 ^ 17 ∧
  S.QG ⊓ cent2 t u ≤ closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u} ∧
  (∀ c ∈ cent2 t u, c ∈ S.M → (∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) → c ∈ S.QG) ∧
  (∀ P : Subgroup G, P ≤ cent2 t u ⊓ S.M →
    (∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) → IsPGroup 2 P → P ≤ S.QG)

theorem commute_conj_iff_E7 (g a b : G) :
    Commute (g * a * g⁻¹) (g * b * g⁻¹) ↔ Commute a b := by
  constructor
  · intro h
    simp only [Commute, SemiconjBy] at h ⊢
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h]
      _ = b * a := by group
  · intro h
    simp only [Commute, SemiconjBy] at h ⊢
    calc g * a * g⁻¹ * (g * b * g⁻¹) = g * (a * b) * g⁻¹ := by group
      _ = g * (b * a) * g⁻¹ := by rw [h]
      _ = g * b * g⁻¹ * (g * a * g⁻¹) := by group

theorem conj_mem_cent2_iff_E7 (g : G) {t u x : G} :
    g * x * g⁻¹ ∈ cent2 (g * t * g⁻¹) (g * u * g⁻¹) ↔ x ∈ cent2 t u := by
  rw [mem_cent2, mem_cent2, commute_conj_iff_E7, commute_conj_iff_E7]

theorem conj_mem_QG_iff_E7 (S : Setting G) {g : G} (hg : g ∈ S.M) {x : G} :
    g * x * g⁻¹ ∈ S.QG ↔ x ∈ S.QG := by
  refine ⟨fun h => ?_, S.conj_mem_QG hg⟩
  have := S.conj_mem_QG (S.M.inv_mem hg) h
  rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this

theorem conj_mem_M_iff_E7 (S : Setting G) {g : G} (hg : g ∈ S.M) {x : G} :
    g * x * g⁻¹ ∈ S.M ↔ x ∈ S.M := by
  refine ⟨fun h => ?_, fun h => S.M.mul_mem (S.M.mul_mem hg h) (S.M.inv_mem hg)⟩
  have := S.M.mul_mem (S.M.mul_mem (S.M.inv_mem hg) h) hg
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

theorem E23aConcl.of_conj (S : Setting G) {t u g : G} (hg : g ∈ S.M)
    (h : E23aConcl S (g * t * g⁻¹) (g * u * g⁻¹)) : E23aConcl S t u := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  set f : G ≃* G := MulAut.conj g with hf
  have hfapp : ∀ x, f x = g * x * g⁻¹ := fun x => by simp [hf, MulAut.conj_apply]
  have hfsymm : ∀ x, f.symm x = g⁻¹ * x * g := fun x => by
    rw [MulEquiv.symm_apply_eq, hfapp]; group
  have hE : (S.QG ⊓ cent2 t u).map f.toMonoidHom = S.QG ⊓ cent2 (g * t * g⁻¹) (g * u * g⁻¹) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyQ, hyH⟩ := mem_inf.mp hy
      exact mem_inf.mpr ⟨by rw [MulEquiv.coe_toMonoidHom, hfapp]; exact S.conj_mem_QG hg hyQ,
        by rw [MulEquiv.coe_toMonoidHom, hfapp]; exact (conj_mem_cent2_iff_E7 g).mpr hyH⟩
    · intro hx
      obtain ⟨hxQ, hxH⟩ := mem_inf.mp hx
      refine ⟨f.symm x, ?_, by simp⟩
      have e : g * f.symm x * g⁻¹ = x := by rw [hfsymm]; group
      have hxQ' : g * f.symm x * g⁻¹ ∈ S.QG := by rw [e]; exact hxQ
      have hxH' : g * f.symm x * g⁻¹ ∈ cent2 (g * t * g⁻¹) (g * u * g⁻¹) := by rw [e]; exact hxH
      exact mem_inf.mpr ⟨(conj_mem_QG_iff_E7 S hg).mp hxQ', (conj_mem_cent2_iff_E7 g).mp hxH'⟩
  let e : ↥(S.QG ⊓ cent2 t u) ≃* ↥(S.QG ⊓ cent2 (g * t * g⁻¹) (g * u * g⁻¹)) :=
    (Subgroup.equivMapOfInjective _ f.toMonoidHom f.injective).trans (MulEquiv.subgroupCongr hE)
  refine ⟨CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv e.symm h1,
    (Nat.card_congr e.toEquiv).trans h2, fun q hq => ?_, fun c hcH hcM hcq => ?_,
    fun P hPH hPn hP2 => ?_⟩
  ·
    have hq' : g * q * g⁻¹ ∈ S.QG ⊓ cent2 (g * t * g⁻¹) (g * u * g⁻¹) := by
      rw [← hE]; exact ⟨q, hq, by rw [MulEquiv.coe_toMonoidHom, hfapp]⟩
    have hc := h3 hq'
    have hmap : closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 (g * t * g⁻¹) (g * u * g⁻¹)}
        ≤ (closure {c : G | IsConj S.z c ∧ c ∈ S.QG ∧ c ∈ cent2 t u}).map f.toMonoidHom := by
      rw [closure_le]
      rintro c ⟨hcz, hcQ, hcH'⟩
      refine ⟨f.symm c, subset_closure ⟨?_, ?_, ?_⟩, by simp⟩
      · rw [hfsymm]; exact hcz.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
      · rw [hfsymm]
        exact (conj_mem_QG_iff_E7 S hg).mp (by rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group])
      · rw [hfsymm]
        exact (conj_mem_cent2_iff_E7 g).mp (by rwa [show g * (g⁻¹ * c * g) * g⁻¹ = c by group])
    obtain ⟨q', hq', hq'e⟩ := hmap hc
    rw [MulEquiv.coe_toMonoidHom, hfapp] at hq'e
    have : q' = q := by
      have := congrArg (fun x => g⁻¹ * x * g) hq'e
      rwa [show g⁻¹ * (g * q' * g⁻¹) * g = q' by group,
        show g⁻¹ * (g * q * g⁻¹) * g = q by group] at this
    rwa [this] at hq'
  ·
    refine (conj_mem_QG_iff_E7 S hg).mp (h4 _ ((conj_mem_cent2_iff_E7 g).mpr hcH)
      ((conj_mem_M_iff_E7 S hg).mpr hcM) fun q hq => ?_)
    rw [← hE] at hq
    obtain ⟨q₀, hq₀, rfl⟩ := hq
    rw [MulEquiv.coe_toMonoidHom, hfapp]
    have := hcq q₀ hq₀
    calc g * c * g⁻¹ * (g * q₀ * g⁻¹) = g * (c * q₀) * g⁻¹ := by group
      _ = g * (q₀ * c) * g⁻¹ := by rw [this]
      _ = g * q₀ * g⁻¹ * (g * c * g⁻¹) := by group
  ·
    set P' := P.map f.toMonoidHom with hP'
    have hmem : ∀ {x : G}, x ∈ P' ↔ g⁻¹ * x * g ∈ P := fun {x} => by
      rw [hP', Subgroup.mem_map]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hfapp]
        rwa [show g⁻¹ * (g * p * g⁻¹) * g = p by group]
      · intro hx
        exact ⟨_, hx, by rw [MulEquiv.coe_toMonoidHom, hfapp]; group⟩
    have hle := h5 P' (fun x hx => by
        have hp := hPH (hmem.mp hx)
        obtain ⟨hpH, hpM⟩ := mem_inf.mp hp
        have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
        refine mem_inf.mpr ⟨?_, ?_⟩
        · rw [← e]; exact (conj_mem_cent2_iff_E7 g).mpr hpH
        · rw [← e]; exact (conj_mem_M_iff_E7 S hg).mpr hpM)
      (fun c hc x hx => by
        apply hmem.mpr
        obtain ⟨hcH, hcM⟩ := mem_inf.mp hc
        have e : g * (g⁻¹ * c * g) * g⁻¹ = c := by group
        have hc' : g⁻¹ * c * g ∈ cent2 t u ⊓ S.M := by
          refine mem_inf.mpr ⟨(conj_mem_cent2_iff_E7 g).mp (by rwa [e]),
            (conj_mem_M_iff_E7 S hg).mp (by rwa [e])⟩
        have := hPn _ hc' _ (hmem.mp hx)
        rwa [show g⁻¹ * c * g * (g⁻¹ * x * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * x * c⁻¹) * g by
          group] at this)
      (hP2.map _)
    intro p hp
    apply (conj_mem_QG_iff_E7 S hg).mp
    exact hle (hmem.mpr (by rwa [show g⁻¹ * (g * p * g⁻¹) * g = p by group]))

section Mbar


theorem inv_mul_mem_QG_of_ρ_eq_E7 (S : Setting G) {a b : S.M} (h : S.ρ a = S.ρ b) :
    (a : G)⁻¹ * b ∈ S.QG := by
  have h1 : S.ρ (a⁻¹ * b) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  exact (S.ρ_eq_one_iff (a⁻¹ * b)).mp h1

theorem ρ_eq_of_inv_mul_mem_QG_E7 (S : Setting G) {a b : S.M} (h : (a : G)⁻¹ * b ∈ S.QG) :
    S.ρ a = S.ρ b := by
  have h1 := (S.ρ_eq_one_iff (a⁻¹ * b)).mpr h
  rwa [map_mul, map_inv, inv_mul_eq_one] at h1

theorem ρ_eq_of_ψ_eq {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) {c d : G} (hc : c ∈ S.M) (hd : d ∈ S.M)
    (h : ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ = ψ ⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩) :
    S.ρ ⟨c, hc⟩ = S.ρ ⟨d, hd⟩ :=
  congrArg (fun w : S.Mbar => (w : S.O)) (ψ.injective h)

theorem commute_tvP_of_commute {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) {c d : G} (hc : c ∈ S.M)
    (hd : d ∈ S.M) {kc kd : Fin 365211}
    (hψc : ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ = ⟨tvP kc, tvP_mem kc⟩)
    (hψd : ψ ⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ = ⟨tvP kd, tvP_mem kd⟩) (hcd : Commute c d) :
    Commute (tvP kc) (tvP kd) := by
  have h1 : (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) * ⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ =
      ⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ * ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ := by
    apply Subtype.ext
    show S.ρ ⟨c, hc⟩ * S.ρ ⟨d, hd⟩ = S.ρ ⟨d, hd⟩ * S.ρ ⟨c, hc⟩
    rw [← map_mul, ← map_mul]
    exact congrArg S.ρ (Subtype.ext hcd.eq)
  have h2 : (⟨tvP kc, tvP_mem kc⟩ : ↥TD6) * ⟨tvP kd, tvP_mem kd⟩ =
      ⟨tvP kd, tvP_mem kd⟩ * ⟨tvP kc, tvP_mem kc⟩ :=
    ((congrArg₂ (· * ·) hψc hψd).symm.trans (map_mul ψ _ _).symm).trans
      ((congrArg ψ h1).trans ((map_mul ψ _ _).trans (congrArg₂ (· * ·) hψd hψc)))
  exact congrArg Subtype.val h2

theorem mul_inv_mul_mem_QG_of_commute_tvP {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) {c d : G}
    (hc : c ∈ S.M) (hd : d ∈ S.M) {kc kd : Fin 365211}
    (hψc : ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ = ⟨tvP kc, tvP_mem kc⟩)
    (hψd : ψ ⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ = ⟨tvP kd, tvP_mem kd⟩)
    (hcd : Commute (tvP kc) (tvP kd)) : (c * d)⁻¹ * (d * c) ∈ S.QG := by
  have h1 : ψ (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ * ⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩) =
      ψ (⟨S.ρ ⟨d, hd⟩, ⟨⟨d, hd⟩, rfl⟩⟩ * ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) := by
    refine (map_mul ψ _ _).trans ((congrArg₂ (· * ·) hψc hψd).trans ?_)
    refine Eq.trans ?_ ((congrArg₂ (· * ·) hψd hψc).symm.trans (map_mul ψ _ _).symm)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcd.eq
  have h2 : S.ρ ⟨c, hc⟩ * S.ρ ⟨d, hd⟩ = S.ρ ⟨d, hd⟩ * S.ρ ⟨c, hc⟩ :=
    congrArg (fun w : S.Mbar => (w : S.O)) (ψ.injective h1)
  rw [← map_mul, ← map_mul] at h2
  exact inv_mul_mem_QG_of_ρ_eq_E7 S h2

theorem coe_ψ_symm_eq {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) {x : G} (hx : x ∈ S.M)
    {k : Fin 365211} (hψ : ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) :
    (ψ.symm ⟨tvP k, tvP_mem k⟩ : S.Mbar) = ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ := by
  rw [← hψ, MulEquiv.symm_apply_apply]

theorem mbar_conj (S : Setting G) {c x : G} (hc : c ∈ S.M) (hx : x ∈ S.M) :
    (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar) * ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ *
        (⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩ : S.Mbar)⁻¹ =
      ⟨S.ρ ⟨c * x * c⁻¹, S.M.mul_mem (S.M.mul_mem hc hx) (S.M.inv_mem hc)⟩,
        ⟨⟨c * x * c⁻¹, S.M.mul_mem (S.M.mul_mem hc hx) (S.M.inv_mem hc)⟩, rfl⟩⟩ := by
  apply Subtype.ext
  show S.ρ ⟨c, hc⟩ * S.ρ ⟨x, hx⟩ * (S.ρ ⟨c, hc⟩)⁻¹ = _
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem eq_one_of_centralizes {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) (m : S.Mbar)
    (h : ∀ k : Fin 365211, (k = 0 ∨ k = stdOpp ∨
        (Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP stdOpp))) →
      m * (ψ.symm ⟨tvP k, tvP_mem k⟩ : S.Mbar) * m⁻¹ = (ψ.symm ⟨tvP k, tvP_mem k⟩ : S.Mbar)) :
    m = 1 := by
  have hfix : ∀ k : Fin 365211, ea7InF0 k.val = true → (ψ m : Equiv.Perm (Fin 365211)) k = k := by
    intro k hk
    have hk' : k = 0 ∨ k = stdOpp ∨ (Commute (tvP k) (tvP 0) ∧ Commute (tvP k) (tvP stdOpp)) := by
      simp only [CFSG.SmithD6.ea7InF0, Bool.or_eq_true, beq_iff_eq] at hk
      rcases hk with (h0 | h1) | hX
      · exact Or.inl (Fin.ext (by rw [h0, fin_val_zero]))
      · exact Or.inr (Or.inl (Fin.ext (by rw [h1, stdOpp_val])))
      · exact Or.inr (Or.inr (ea7InX_iff.mp hX))
    have h2 := congrArg ψ (h k hk')
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h2
    have h3 := congrArg Subtype.val h2
    have h4 : (ψ m : Equiv.Perm (Fin 365211)) * tvP k * (ψ m : Equiv.Perm (Fin 365211))⁻¹ =
        tvP k := h3
    rw [mul_tvP_mul_inv (ψ m).2] at h4
    exact tvP_injective h4
  have hg : (ψ m : Equiv.Perm (Fin 365211)) = 1 := eq_one_of_fixes_F0 (ψ m).2 hfix
  exact ψ.injective ((Subtype.ext hg).trans (map_one ψ).symm)

end Mbar

section Lift


theorem exists_lift_tv (h34a : SmithE7E34a) (h34b : SmithE7E34b) (hLoc : SmithE7LocalInput)
    [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {ψ : S.Mbar ≃* ↥TD6}
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3) {kt ku : Fin 365211}
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP kt, tvP_mem kt⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP ku, tvP_mem ku⟩)
    (k : Fin 365211) (hkt : Commute (tvP k) (tvP kt)) (hku : Commute (tvP k) (tvP ku)) :
    ∃ (y : G) (hyM : y ∈ S.M), IsConj S.z y ∧ y ∉ S.QG ∧ Commute y t ∧ Commute y u ∧
      ψ ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ := by
  have hti : t⁻¹ = t := SME.inv_eq_of_isConj S ht
  have hui : u⁻¹ = u := SME.inv_eq_of_isConj S hu
  obtain ⟨x, hxM, hx, hxQ, hψx⟩ := h3' k
  have hxi : x⁻¹ = x := SME.inv_eq_of_isConj S hx
  have hxt := mul_inv_mul_mem_QG_of_commute_tvP ψ hxM htM hψx hψt hkt
  have hxu := mul_inv_mul_mem_QG_of_commute_tvP ψ hxM huM hψx hψu hku
  have hty : t * x * t⁻¹ * x⁻¹ ∈ S.QG := by
    have e1 : (x * t)⁻¹ * (t * x) = t * x * t * x := by rw [mul_inv_rev, hti, hxi]; group
    rw [hti, hxi]
    rwa [e1] at hxt
  have huy : u * x * u⁻¹ * x⁻¹ ∈ S.QG := by
    have e1 : (x * u)⁻¹ * (u * x) = u * x * u * x := by rw [mul_inv_rev, hui, hxi]; group
    rw [hui, hxi]
    rwa [e1] at hxu
  obtain ⟨y, hyD, hxy, hyt, hyu⟩ := exists_lift_commute h34a h34b hLoc S hw hU ht hu htM huM
    htQ htu hx hxM hxQ hty huy
  have hyM : y ∈ S.M := by
    have := S.M.mul_mem hxM (S.QG_le_M hxy)
    rwa [mul_inv_cancel_left] at this
  have hyQ : y ∉ S.QG := fun hyQ => hxQ (by
    have := S.QG.mul_mem hyQ (S.QG.inv_mem hxy)
    rwa [show y * (x⁻¹ * y)⁻¹ = x by group] at this)
  have hρy : S.ρ ⟨y, hyM⟩ = S.ρ ⟨x, hxM⟩ :=
    (ρ_eq_of_inv_mul_mem_QG_E7 S (a := ⟨x, hxM⟩) (b := ⟨y, hyM⟩) hxy).symm
  have hψy : ψ ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ := by
    have : (⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ : S.Mbar) = ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ :=
      Subtype.ext hρy
    exact (congrArg ψ this).trans hψx
  exact ⟨y, hyM, hyD, hyQ, hyt, hyu, hψy⟩

end Lift

section Std


theorem mem_QG_of_fix_lifts (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {ψ : S.Mbar ≃* ↥TD6}
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)
    {c : G} (hcM : c ∈ S.M) (hct : Commute c t) (hcu : Commute c u)
    (hfix : ∀ (y : G) (hyM : y ∈ S.M), IsConj S.z y → y ∉ S.QG → Commute y t → Commute y u →
      S.ρ ⟨c * y * c⁻¹, S.M.mul_mem (S.M.mul_mem hcM hyM) (S.M.inv_mem hcM)⟩ = S.ρ ⟨y, hyM⟩) :
    c ∈ S.QG := by
  have hm : (⟨S.ρ ⟨c, hcM⟩, ⟨⟨c, hcM⟩, rfl⟩⟩ : S.Mbar) = 1 := by
    apply eq_one_of_centralizes ψ
    intro k hk
    obtain ⟨x, hxM, hψx, hρ⟩ : ∃ (x : G) (hxM : x ∈ S.M),
        ψ ⟨S.ρ ⟨x, hxM⟩, ⟨⟨x, hxM⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩ ∧
        S.ρ ⟨c * x * c⁻¹, S.M.mul_mem (S.M.mul_mem hcM hxM) (S.M.inv_mem hcM)⟩ =
          S.ρ ⟨x, hxM⟩ := by
      rcases hk with rfl | rfl | ⟨hk0, hk1⟩
      · exact ⟨t, htM, hψt,
          congrArg S.ρ (Subtype.ext (show c * t * c⁻¹ = t by rw [hct.eq, mul_inv_cancel_right]))⟩
      · exact ⟨u, huM, hψu,
          congrArg S.ρ (Subtype.ext (show c * u * c⁻¹ = u by rw [hcu.eq, mul_inv_cancel_right]))⟩
      · obtain ⟨y, hyM, hyD, hyQ, hyt, hyu, hψy⟩ :=
          exists_lift_tv h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt hψu k hk0 hk1
        exact ⟨y, hyM, hψy, hfix y hyM hyD hyQ hyt hyu⟩
    rw [coe_ψ_symm_eq ψ hxM hψx, mbar_conj S hcM hxM]
    exact Subtype.ext hρ
  exact (S.ρ_eq_one_iff ⟨c, hcM⟩).mp (congrArg Subtype.val hm)

theorem mem_QG_of_centralizes_std (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {φ : S.Qt ≃ₗ[ZMod 2] V}
    {ψ : S.Mbar ≃* ↥TD6}
    (hcomp : ∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
      φ (S.cl (c * u * c⁻¹)) = rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u)))
    (h2' : ∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
      ∃ k : Fin 365211, ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)
    {c : G} (hcH : c ∈ cent2 t u) (hcM : c ∈ S.M)
    (hcq : ∀ q ∈ S.QG ⊓ cent2 t u, c * q = q * c) : c ∈ S.QG := by
  obtain ⟨hct, hcu⟩ := mem_cent2.mp hcH
  refine mem_QG_of_fix_lifts h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt hψu hcM hct hcu
    fun y hyM hyD hyQ hyt hyu => ?_
  obtain ⟨ky, hψy⟩ := h2' y hyM hyD hyQ
  have hwM : c * y * c⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hcM hyM) (S.M.inv_mem hcM)
  have hwD : IsConj S.z (c * y * c⁻¹) := hyD.trans (isConj_iff.mpr ⟨c, rfl⟩)
  have hwQ : c * y * c⁻¹ ∉ S.QG := fun h => hyQ ((conj_mem_QG_iff_E7 S hcM).mp h)
  have hwt : Commute (c * y * c⁻¹) t := (hct.mul_left hyt).mul_left hct.inv_left
  have hwu : Commute (c * y * c⁻¹) u := (hcu.mul_left hyu).mul_left hcu.inv_left
  obtain ⟨kw, hψw⟩ := h2' _ hwM hwD hwQ
  have hkw0 := commute_tvP_of_commute ψ hwM htM hψw hψt hwt
  have hkw31 := commute_tvP_of_commute ψ hwM huM hψw hψu hwu
  have hky0 := commute_tvP_of_commute ψ hyM htM hψy hψt hyt
  have hky31 := commute_tvP_of_commute ψ hyM huM hψy hψu hyu
  have hres : ∀ v ∈ C16, tvEquiv kw.val v = tvEquiv ky.val v := by
    intro v hv
    obtain ⟨q, hqQ, hqt, hqu, rfl⟩ := exists_cent2_of_mem_C16 hcomp htM huM hψt hψu h34a
      hw hU ht hu htQ huQ hv
    have e1 := actsV_of_compat hcomp hwM hψw hqQ
    have e2 := actsV_of_compat hcomp hyM hψy hqQ
    rw [← e1, ← e2]
    have hyq : y * q * y⁻¹ ∈ S.QG ⊓ cent2 t u :=
      mem_inf.mpr ⟨S.conj_mem_QG hyM hqQ, mem_cent2.mpr
        ⟨(hyt.mul_left hqt).mul_left hyt.inv_left, (hyu.mul_left hqu).mul_left hyu.inv_left⟩⟩
    have hc1 := hcq q (mem_inf.mpr ⟨hqQ, mem_cent2.mpr ⟨hqt, hqu⟩⟩)
    have hc2 := hcq _ hyq
    have hcq' : c⁻¹ * q * c = q := by rw [mul_assoc, ← hc1, inv_mul_cancel_left]
    have e : c * y * c⁻¹ * q * (c * y * c⁻¹)⁻¹ = y * q * y⁻¹ := by
      calc c * y * c⁻¹ * q * (c * y * c⁻¹)⁻¹ = c * y * (c⁻¹ * q * c) * y⁻¹ * c⁻¹ := by group
        _ = c * (y * q * y⁻¹) * c⁻¹ := by rw [hcq']; group
        _ = (y * q * y⁻¹) * c * c⁻¹ := by rw [hc2]
        _ = y * q * y⁻¹ := by group
    rw [e]
  have hkk : kw = ky := eq_of_restr_C16 (ea7InX_iff.mpr ⟨hkw0, hkw31⟩)
    (ea7InX_iff.mpr ⟨hky0, hky31⟩) hres
  exact ρ_eq_of_ψ_eq ψ hwM hyM (hψw.trans
    ((congrArg (fun k : Fin 365211 => (⟨tvP k, tvP_mem k⟩ : ↥TD6)) hkk).trans hψy.symm))

noncomputable abbrev mbarImage (S : Setting G) (P : Subgroup G) : Subgroup S.Mbar :=
  (P.comap S.M.subtype).map (SMH.toMbarM S)

theorem toMbarM_eq (S : Setting G) {y : G} (hyM : y ∈ S.M) :
    SMH.toMbarM S ⟨y, hyM⟩ = ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ :=
  Subtype.ext rfl

theorem conj_mem_mbarImage_std (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {ψ : S.Mbar ≃* ↥TD6}
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)
    {P : Subgroup G} (hPn : ∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P)
    (k : Fin 365211) (hk0 : Commute (tvP k) (tvP 0)) (hk1 : Commute (tvP k) (tvP stdOpp))
    {p : S.Mbar} (hp : p ∈ mbarImage S P) :
    (ψ.symm ⟨tvP k, tvP_mem k⟩ : S.Mbar) * p * (ψ.symm ⟨tvP k, tvP_mem k⟩ : S.Mbar)⁻¹ ∈
      mbarImage S P := by
  obtain ⟨y, hyM, hyD, hyQ, hyt, hyu, hψy⟩ :=
    exists_lift_tv h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt hψu k hk0 hk1
  rw [coe_ψ_symm_eq ψ hyM hψy]
  obtain ⟨p', hp', rfl⟩ := hp
  refine ⟨⟨y, hyM⟩ * p' * ⟨y, hyM⟩⁻¹, ?_, ?_⟩
  · show y * p' * y⁻¹ ∈ P
    exact hPn y (mem_inf.mpr ⟨mem_cent2.mpr ⟨hyt, hyu⟩, hyM⟩) p' hp'
  · apply Subtype.ext
    show S.ρ (⟨y, hyM⟩ * p' * ⟨y, hyM⟩⁻¹) = S.ρ ⟨y, hyM⟩ * S.ρ p' * (S.ρ ⟨y, hyM⟩)⁻¹
    rw [map_mul, map_mul, map_inv]

theorem conj_mem_mbarImage_of_mem_Lstd (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {ψ : S.Mbar ≃* ↥TD6}
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)
    {P : Subgroup G} (hPn : ∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P)
    (g : ↥TD6) (hg : (g : Equiv.Perm (Fin 365211)) ∈ Lstd) :
    ∀ p ∈ mbarImage S P, (ψ.symm g : S.Mbar) * p * (ψ.symm g : S.Mbar)⁻¹ ∈ mbarImage S P := by
  haveI : Finite S.Mbar := Bridge.finite_Mbar S
  have hle : Lstd ≤ ((Subgroup.normalizer ((mbarImage S P : Subgroup S.Mbar) : Set S.Mbar)).comap
      ψ.symm.toMonoidHom).map TD6.subtype := by
    rw [Subgroup.closure_le]
    rintro _ ⟨k, ⟨hk0, hk1⟩, rfl⟩
    refine ⟨⟨tvP k, tvP_mem k⟩, ?_, rfl⟩
    show (ψ.symm ⟨tvP k, tvP_mem k⟩ : S.Mbar) ∈ Subgroup.normalizer _
    exact mem_normalizer_fintype fun n hn =>
      conj_mem_mbarImage_std h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt hψu hPn k hk0 hk1
        hn
  obtain ⟨g', hg', hg'e⟩ := hle hg
  have e : g' = g := Subtype.ext hg'e
  rw [e] at hg'
  intro p hp
  exact (mem_normalizer_iff.mp hg' p).mp hp

theorem mem_mbarImage_conj {S : Setting G} {ψ : S.Mbar ≃* ↥TD6} {P : Subgroup G}
    (hPM : P ≤ S.M) {x y : G} (hx : x ∈ P) (hyP : y * x⁻¹ * y⁻¹ ∈ P) (hyD : IsConj S.z y)
    (hyM : y ∈ S.M) (hwM : x * y * x⁻¹ ∈ S.M) {kw ky : Fin 365211}
    (hψw : ψ ⟨S.ρ ⟨x * y * x⁻¹, hwM⟩, ⟨⟨x * y * x⁻¹, hwM⟩, rfl⟩⟩ = ⟨tvP kw, tvP_mem kw⟩)
    (hψy : ψ ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ = ⟨tvP ky, tvP_mem ky⟩) :
    (ψ.symm ⟨tvP kw * tvP ky, TD6.mul_mem (tvP_mem kw) (tvP_mem ky)⟩ : S.Mbar) ∈
      mbarImage S P := by
  have hyi : y⁻¹ = y := SME.inv_eq_of_isConj S hyD
  have hxyP : x * (y * x⁻¹ * y⁻¹) ∈ P := P.mul_mem hx hyP
  have e1 : (ψ.symm ⟨tvP kw * tvP ky, TD6.mul_mem (tvP_mem kw) (tvP_mem ky)⟩ : S.Mbar) =
      (ψ.symm ⟨tvP kw, tvP_mem kw⟩ : S.Mbar) * (ψ.symm ⟨tvP ky, tvP_mem ky⟩ : S.Mbar) := by
    have e : (⟨tvP kw * tvP ky, TD6.mul_mem (tvP_mem kw) (tvP_mem ky)⟩ : ↥TD6) =
        ⟨tvP kw, tvP_mem kw⟩ * ⟨tvP ky, tvP_mem ky⟩ := rfl
    exact (congrArg (fun w : ↥TD6 => (ψ.symm w : S.Mbar)) e).trans (map_mul ψ.symm _ _)
  rw [e1, coe_ψ_symm_eq ψ hwM hψw, coe_ψ_symm_eq ψ hyM hψy]
  have e2 : (⟨S.ρ ⟨x * y * x⁻¹, hwM⟩, ⟨⟨x * y * x⁻¹, hwM⟩, rfl⟩⟩ : S.Mbar) *
      ⟨S.ρ ⟨y, hyM⟩, ⟨⟨y, hyM⟩, rfl⟩⟩ = SMH.toMbarM S ⟨x * (y * x⁻¹ * y⁻¹), hPM hxyP⟩ := by
    rw [toMbarM_eq S (hPM hxyP)]
    apply Subtype.ext
    show S.ρ ⟨x * y * x⁻¹, hwM⟩ * S.ρ ⟨y, hyM⟩ = S.ρ ⟨x * (y * x⁻¹ * y⁻¹), hPM hxyP⟩
    rw [← map_mul]
    congr 1
    apply Subtype.ext
    show x * y * x⁻¹ * y = x * (y * x⁻¹ * y⁻¹)
    rw [hyi]
    group
  rw [e2]
  exact ⟨⟨_, hPM hxyP⟩, hxyP, rfl⟩

end Std

section Main


theorem eq_one_of_mem_mbarImage_std (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {ψ : S.Mbar ≃* ↥TD6}
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)
    {P : Subgroup G} (hPn : ∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) (g : ↥TD6) (hg : (g : Equiv.Perm (Fin 365211)) ∈ Lstd)
    (hmem : (ψ.symm g : S.Mbar) ∈ mbarImage S P) : g = 1 := by
  have hPbar2 : IsPGroup 2 (mbarImage S P) :=
    (hP2.comap_of_injective S.M.subtype Subtype.val_injective).map _
  obtain ⟨f, hfapp⟩ : ∃ f : ↥Lstd →* S.Mbar, ∀ x : ↥Lstd,
      f x = (ψ.symm (Subgroup.inclusion Lstd_le_TD6 x) : S.Mbar) :=
    ⟨ψ.symm.toMonoidHom.comp (Subgroup.inclusion Lstd_le_TD6), fun x => rfl⟩
  have hfinj : Function.Injective f := fun a b hab => by
    rw [hfapp, hfapp] at hab
    exact Subgroup.inclusion_injective Lstd_le_TD6 (ψ.symm.injective hab)
  have hnorm : ∀ x : ↥Lstd, ∀ p ∈ mbarImage S P, f x * p * (f x)⁻¹ ∈ mbarImage S P := by
    intro x p hp
    rw [hfapp]
    exact conj_mem_mbarImage_of_mem_Lstd h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt
      hψu hPn _ x.2 p hp
  have hincl : Subgroup.inclusion Lstd_le_TD6 (⟨g.1, hg⟩ : ↥Lstd) = g := Subtype.ext rfl
  have hmem' : f ⟨g.1, hg⟩ ∈ mbarImage S P := by rw [hfapp, hincl]; exact hmem
  have h1 := eq_one_of_normal_pgroup_std f hfinj hPbar2 hnorm hmem'
  have h2 : (g : Equiv.Perm (Fin 365211)) = 1 := congrArg Subtype.val h1
  exact Subtype.ext h2

theorem le_QG_of_normal_std (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {ψ : S.Mbar ≃* ↥TD6}
    (h2' : ∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
      ∃ k : Fin 365211, ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩)
    {P : Subgroup G} (hPH : P ≤ cent2 t u ⊓ S.M)
    (hPn : ∀ c ∈ cent2 t u ⊓ S.M, ∀ p ∈ P, c * p * c⁻¹ ∈ P) (hP2 : IsPGroup 2 P) :
    P ≤ S.QG := by
  have hPM : P ≤ S.M := fun p hp => (mem_inf.mp (hPH hp)).2
  intro x hx
  obtain ⟨hxH, hxM⟩ := mem_inf.mp (hPH hx)
  obtain ⟨hxt, hxu⟩ := mem_cent2.mp hxH
  refine mem_QG_of_fix_lifts h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt hψu hxM hxt hxu
    fun y hyM hyD hyQ hyt hyu => ?_
  obtain ⟨ky, hψy⟩ := h2' y hyM hyD hyQ
  have hwM : x * y * x⁻¹ ∈ S.M := S.M.mul_mem (S.M.mul_mem hxM hyM) (S.M.inv_mem hxM)
  have hwD : IsConj S.z (x * y * x⁻¹) := hyD.trans (isConj_iff.mpr ⟨x, rfl⟩)
  have hwQ : x * y * x⁻¹ ∉ S.QG := fun h => hyQ ((conj_mem_QG_iff_E7 S hxM).mp h)
  have hwt : Commute (x * y * x⁻¹) t := (hxt.mul_left hyt).mul_left hxt.inv_left
  have hwu : Commute (x * y * x⁻¹) u := (hxu.mul_left hyu).mul_left hxu.inv_left
  obtain ⟨kw, hψw⟩ := h2' _ hwM hwD hwQ
  have hℓ : tvP kw * tvP ky ∈ Lstd :=
    mul_mem (subset_closure ⟨kw, ⟨commute_tvP_of_commute ψ hwM htM hψw hψt hwt,
        commute_tvP_of_commute ψ hwM huM hψw hψu hwu⟩, rfl⟩)
      (subset_closure ⟨ky, ⟨commute_tvP_of_commute ψ hyM htM hψy hψt hyt,
        commute_tvP_of_commute ψ hyM huM hψy hψu hyu⟩, rfl⟩)
  have hyP : y * x⁻¹ * y⁻¹ ∈ P :=
    hPn y (mem_inf.mpr ⟨mem_cent2.mpr ⟨hyt, hyu⟩, hyM⟩) _ (P.inv_mem hx)
  have hmem := mem_mbarImage_conj hPM hx hyP hyD hyM hwM hψw hψy
  have hℓ1 := eq_one_of_mem_mbarImage_std h34a h34b hLoc hw hU h3' ht hu htM huM htQ htu hψt hψu
    hPn hP2 _ hℓ hmem
  have hℓ1' : tvP kw * tvP ky = 1 := congrArg Subtype.val hℓ1
  have hkk : kw = ky := by
    have h2 : tvP kw = tvP ky := by
      calc tvP kw = tvP kw * tvP ky * tvP ky := by rw [mul_assoc, tvP_mul_self, mul_one]
        _ = tvP ky := by rw [hℓ1', one_mul]
    exact tvP_injective h2
  exact ρ_eq_of_ψ_eq ψ hwM hyM (hψw.trans
    ((congrArg (fun k : Fin 365211 => (⟨tvP k, tvP_mem k⟩ : ↥TD6)) hkk).trans hψy.symm))

theorem orderOf_tvP_of_compat {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) {t u : G} (htM : t ∈ S.M)
    (huM : u ∈ S.M) {kt ku : Fin 365211}
    (hkt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP kt, tvP_mem kt⟩)
    (hku : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP ku, tvP_mem ku⟩)
    (htu : orderOf (t * u) = 3) : orderOf (tvP kt * tvP ku) = 3 := by
  let τ : S.Mbar := ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩
  let υ : S.Mbar := ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩
  have hψτυ : ψ (τ * υ) = ⟨tvP kt * tvP ku, TD6.mul_mem (tvP_mem kt) (tvP_mem ku)⟩ :=
    (map_mul ψ τ υ).trans ((congrArg₂ (· * ·) hkt hku).trans (Subtype.ext rfl))
  have e1 : orderOf (tvP kt * tvP ku) = orderOf (τ * υ) := by
    rw [← MulEquiv.orderOf_eq ψ, hψτυ, Subgroup.orderOf_mk]
  have e2 : ((τ * υ : S.Mbar) : S.O) = S.ρ (⟨t, htM⟩ * ⟨u, huM⟩) := by
    rw [map_mul]; rfl
  rw [e1, ← Subgroup.orderOf_coe (τ * υ), e2]
  have hdvd : orderOf (S.ρ (⟨t, htM⟩ * ⟨u, huM⟩)) ∣ 3 := by
    refine (orderOf_map_dvd S.ρ _).trans ?_
    rw [← Subgroup.orderOf_coe]
    exact htu.symm ▸ dvd_refl _
  have hne1 : S.ρ (⟨t, htM⟩ * ⟨u, huM⟩) ≠ 1 := fun h =>
    SMJ.mul_not_mem_QG S htu ((S.ρ_eq_one_iff _).mp h)
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne1
  · exact h

theorem exists_conj_tvP {S : Setting G} (ψ : S.Mbar ≃* ↥TD6) {m t : G} (hmM : m ∈ S.M)
    (htM : t ∈ S.M) {g : ↥TD6}
    (hm : (⟨S.ρ ⟨m, hmM⟩, ⟨⟨m, hmM⟩, rfl⟩⟩ : S.Mbar) = (ψ.symm g : S.Mbar)) {k : Fin 365211}
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩) :
    ψ ⟨S.ρ ⟨m * t * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)⟩,
        ⟨⟨m * t * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)⟩, rfl⟩⟩ =
      ⟨tvP ((g : Equiv.Perm (Fin 365211)) k), tvP_mem _⟩ := by
  have e : (⟨S.ρ ⟨m * t * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)⟩,
      ⟨⟨m * t * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)⟩, rfl⟩⟩ : S.Mbar) =
        ψ.symm g * ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ * (ψ.symm g)⁻¹ :=
    (mbar_conj S hmM htM).symm.trans
      (congrArg (fun w : S.Mbar => w * (⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ : S.Mbar) * w⁻¹) hm)
  have e2 : ψ (ψ.symm g * ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ * (ψ.symm g)⁻¹) =
      g * ⟨tvP k, tvP_mem k⟩ * g⁻¹ :=
    (map_mul ψ _ _).trans (congrArg₂ (· * ·)
      ((map_mul ψ _ _).trans (congrArg₂ (· * ·) (ψ.apply_symm_apply g) hψt))
      ((map_inv ψ _).trans (congrArg _ (ψ.apply_symm_apply g))))
  refine (congrArg ψ e).trans (e2.trans (Subtype.ext ?_))
  show (g : Equiv.Perm (Fin 365211)) * tvP k * (g : Equiv.Perm (Fin 365211))⁻¹ = _
  exact mul_tvP_mul_inv g.2 k

theorem e23aConcl_std (h25 : SmithE7E25) (h34a : SmithE7E34a) (h34b : SmithE7E34b)
    (hLoc : SmithE7LocalInput) [IsSimpleGroup G] {S : Setting G} (hw : S.width = 16)
    (hU : Nonempty (S.Mbar ≃* timmesfeldOmegaPlus 6)) {φ : S.Qt ≃ₗ[ZMod 2] V}
    {ψ : S.Mbar ≃* ↥TD6} (h1235 : SmithE7Clauses1235 S φ)
    (hcomp : ∀ (c : G) (hc : c ∈ S.M) (u : G), u ∈ S.QG →
      φ (S.cl (c * u * c⁻¹)) = rhoMod (ψ ⟨S.ρ ⟨c, hc⟩, ⟨⟨c, hc⟩, rfl⟩⟩) (φ (S.cl u)))
    (h2' : ∀ (x : G) (hx : x ∈ S.M), IsConj S.z x → x ∉ S.QG →
      ∃ k : Fin 365211, ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    (h3' : ∀ k : Fin 365211, ∃ (x : G) (hx : x ∈ S.M), IsConj S.z x ∧ x ∉ S.QG ∧
      ψ ⟨S.ρ ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩ = ⟨tvP k, tvP_mem k⟩)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3)
    (hψt : ψ ⟨S.ρ ⟨t, htM⟩, ⟨⟨t, htM⟩, rfl⟩⟩ = ⟨tvP 0, tvP_mem 0⟩)
    (hψu : ψ ⟨S.ρ ⟨u, huM⟩, ⟨⟨u, huM⟩, rfl⟩⟩ = ⟨tvP stdOpp, tvP_mem stdOpp⟩) :
    E23aConcl S t u := by
  have hcard := card_cent2_std hcomp htM huM hψt hψu h34a hw hU ht hu htQ huQ
  exact ⟨isExtraspecialPGroup_cent2_E7 h25 h34a S hw hU ht hu htM huM htQ huQ htu hcard.ge,
    hcard, cent2_le_closure_std hcomp htM huM hψt hψu h34a hw hU ht hu htQ huQ h1235,
    fun c hcH hcM hcq => mem_QG_of_centralizes_std h34a h34b hLoc hw hU hcomp h2' h3' ht hu htM
      huM htQ huQ htu hψt hψu hcH hcM hcq,
    fun P hPH hPn hP2 => le_QG_of_normal_std h34a h34b hLoc hw hU h2' h3' ht hu htM
      huM htQ htu hψt hψu hPH hPn hP2⟩

theorem smithE7E23a_of (h25 : SmithE7E25) (h34a : SmithE7E34a)
    (h34b : SmithE7E34b) (hLoc : SmithE7LocalInput) (hC : SmithE7Compat) : SmithE7E23a := by
  intro G _ _ _ S hw hU t u ht hu htM huM htQ huQ htu
  obtain ⟨φ, ψ, h1235, -, hcomp, h2', h3'⟩ := hC G S hw hU
  obtain ⟨kt, hψt⟩ := h2' t htM ht htQ
  obtain ⟨ku, hψu⟩ := h2' u huM hu huQ
  have hord := orderOf_tvP_of_compat ψ htM huM hψt hψu htu
  obtain ⟨g, hg, hg0, hg31⟩ := exists_mem_TD6_pair hord
  obtain ⟨⟨m, hmM⟩, hm'⟩ := (ψ.symm ⟨g⁻¹, TD6.inv_mem hg⟩ : S.Mbar).2
  have hm : (⟨S.ρ ⟨m, hmM⟩, ⟨⟨m, hmM⟩, rfl⟩⟩ : S.Mbar) = (ψ.symm ⟨g⁻¹, TD6.inv_mem hg⟩ : S.Mbar) :=
    Subtype.ext hm'
  have hψt' := exists_conj_tvP ψ hmM htM hm hψt
  have hψu' := exists_conj_tvP ψ hmM huM hm hψu
  have hg0' : (g⁻¹ : Equiv.Perm (Fin 365211)) kt = 0 := by rw [← hg0]; simp
  have hg31' : (g⁻¹ : Equiv.Perm (Fin 365211)) ku = stdOpp := by rw [← hg31]; simp
  have hψt'' : ψ ⟨S.ρ ⟨m * t * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)⟩,
      ⟨⟨m * t * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM)⟩, rfl⟩⟩ =
        ⟨tvP 0, tvP_mem 0⟩ :=
    hψt'.trans (congrArg (fun k : Fin 365211 => (⟨tvP k, tvP_mem k⟩ : ↥TD6)) hg0')
  have hψu'' : ψ ⟨S.ρ ⟨m * u * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM huM) (S.M.inv_mem hmM)⟩,
      ⟨⟨m * u * m⁻¹, S.M.mul_mem (S.M.mul_mem hmM huM) (S.M.inv_mem hmM)⟩, rfl⟩⟩ =
        ⟨tvP stdOpp, tvP_mem stdOpp⟩ :=
    hψu'.trans (congrArg (fun k : Fin 365211 => (⟨tvP k, tvP_mem k⟩ : ↥TD6)) hg31')
  have hconjQ : ∀ {x : G}, x ∉ S.QG → m * x * m⁻¹ ∉ S.QG := fun hx h =>
    hx ((conj_mem_QG_iff_E7 S hmM).mp h)
  have h3m : orderOf (m * t * m⁻¹ * (m * u * m⁻¹)) = 3 := by
    rw [show m * t * m⁻¹ * (m * u * m⁻¹) = MulAut.conj m (t * u) by
      rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact htu
  refine E23aConcl.of_conj S hmM (e23aConcl_std h25 h34a h34b hLoc hw hU h1235 hcomp h2' h3'
    (ht.trans (isConj_iff.mpr ⟨m, rfl⟩)) (hu.trans (isConj_iff.mpr ⟨m, rfl⟩))
    (S.M.mul_mem (S.M.mul_mem hmM htM) (S.M.inv_mem hmM))
    (S.M.mul_mem (S.M.mul_mem hmM huM) (S.M.inv_mem hmM)) (hconjQ htQ) (hconjQ huQ) h3m
    hψt'' hψu'')

end Main

end CFSG.GF2Type.SmithTypeE.E7
