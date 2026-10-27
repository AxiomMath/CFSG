module

public import CFSG.CGT.Foote82.T66.CaseIIU
import CFSG.LargeExtraspecial.S5Comp
import CFSG.HardMathSupport.Dickson.Bal207.D42Triality
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.Foote82.T66.CaseIIDim

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11 CFSG.RankThree.PartTwo CFSG.PGLModel

namespace CaseII

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {G L : Subgroup (GLV V)} {z : GLV V} {v : V} {H₁ : Subgroup (GLV V)}
  {ψ : ↥H₁ ≃* ↥(orthogonalMinus 2 (ZMod 2) 1 1)}

structure GD (c : Ctx G L z v H₁ ψ) (g : GLV V) : Prop where
  mem : g ∈ HH G L v
  comm : (g * z * g⁻¹) * z = z * (g * z * g⁻¹)
  ne : g * z * g⁻¹ ≠ z
  inf : LinearMap.range (Matrix.mulVecLin (mat (ψ ⟨z, c.z_mem⟩) - 1)) ⊓
    LinearMap.range (Matrix.mulVecLin
      (mat (ψ ⟨g, c.H_le mem⟩ * ψ ⟨z, c.z_mem⟩ * (ψ ⟨g, c.H_le mem⟩)⁻¹) - 1)) = ⊥

theorem Ctx.exists_gd (c : Ctx G L z v H₁ ψ) (hG1 : CaseIIG1) : ∃ g, GD c g := by
  obtain ⟨g, hg, h1, h2, h3⟩ := c.exists_g hG1
  exact ⟨g, hg, h1, h2, h3⟩

abbrev UU (z u : GLV V) : Submodule (ZMod 2) V :=
  commSpace (Subgroup.zpowers z) ⊤ ⊓ commSpace (Subgroup.zpowers u) ⊤

theorem sup_inf_sup_eq {V₀ V₁ A B C : Submodule (ZMod 2) V} (h01 : V₀ ⊓ V₁ = ⊥) (hA : A ≤ V₀)
    (hB : B ≤ V₀) (hC : C ≤ V₁) (hAB : A ⊓ B = ⊥) : (A ⊔ C) ⊓ (B ⊔ C) = C := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  rintro x ⟨hx1, hx2⟩
  obtain ⟨a, ha, c₁, hc₁, rfl⟩ := Submodule.mem_sup.1 hx1
  obtain ⟨b, hb, c₂, hc₂, hbc⟩ := Submodule.mem_sup.1 hx2
  have hab : a - b = c₂ - c₁ := by
    rw [sub_eq_sub_iff_add_eq_add, ← hbc]
    abel
  have h0 : a - b ∈ V₀ ⊓ V₁ :=
    ⟨V₀.sub_mem (hA ha) (hB hb), hab ▸ V₁.sub_mem (hC hc₂) (hC hc₁)⟩
  rw [h01, Submodule.mem_bot, sub_eq_zero] at h0
  subst h0
  have ha0 : a ∈ A ⊓ B := ⟨ha, hb⟩
  rw [hAB, Submodule.mem_bot] at ha0
  rw [ha0, zero_add]
  exact hc₁

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem g_mem_H₁ : g ∈ H₁ := c.H_le d.mem

theorem u_mem_H₁ : g * z * g⁻¹ ∈ H₁ :=
  H₁.mul_mem (H₁.mul_mem d.g_mem_H₁ c.z_mem) (H₁.inv_mem d.g_mem_H₁)

theorem u_mul_u : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := by
  have h := c.z_mul_z
  calc (g * z * g⁻¹) * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [h, mul_one, mul_inv_cancel]

theorem u_eq_z_mul : g * z * g⁻¹ = z * (z⁻¹ * (g * z * g⁻¹)) := by group

theorem zinv_u_mem_H : z⁻¹ * (g * z * g⁻¹) ∈ HH G L v := by
  have h1 : z⁻¹ * g * z ∈ HH G L v := by
    have := c.conj_mem_H (H₁.inv_mem c.z_mem) d.mem
    simpa [mul_assoc] using this
  have : z⁻¹ * (g * z * g⁻¹) = (z⁻¹ * g * z) * g⁻¹ := by group
  rw [this]
  exact (HH G L v).mul_mem h1 ((HH G L v).inv_mem d.mem)

theorem psi_u : mat (ψ ⟨g * z * g⁻¹, d.u_mem_H₁⟩) =
    mat (ψ ⟨g, c.H_le d.mem⟩ * ψ ⟨z, c.z_mem⟩ * (ψ ⟨g, c.H_le d.mem⟩)⁻¹) := by
  have e : (⟨g * z * g⁻¹, d.u_mem_H₁⟩ : ↥H₁) =
      ⟨g, c.H_le d.mem⟩ * ⟨z, c.z_mem⟩ * (⟨g, c.H_le d.mem⟩)⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]
  rfl

theorem inf_V₀ (hs : CaseIISplit) :
    (commSpace (HH G L v) ⊤).map (subOne z) ⊓
      (commSpace (HH G L v) ⊤).map (subOne (g * z * g⁻¹)) = ⊥ := by
  obtain ⟨β, hβ, hβe⟩ := c.exists_beta hs
  rw [eq_bot_iff]
  rintro x ⟨hx1, hx2⟩
  have hxW : x ∈ commSpace (HH G L v) ⊤ := c.map_V₀_le c.z_mem hx1
  have h1 := beta_mem_range β (c.invariant_V₀ z c.z_mem) _
    (fun w => hβe ⟨z, c.z_mem⟩ w ⟨z w, c.invariant_V₀ z c.z_mem w w.2⟩ rfl) hx1 hxW
  have h2 := beta_mem_range β (c.invariant_V₀ _ d.u_mem_H₁) _
    (fun w => hβe ⟨g * z * g⁻¹, d.u_mem_H₁⟩ w ⟨_, c.invariant_V₀ _ d.u_mem_H₁ w w.2⟩ rfl)
    hx2 hxW
  have h3 : β ⟨x, hxW⟩ ∈ LinearMap.range (Matrix.mulVecLin (mat (ψ ⟨z, c.z_mem⟩) - 1)) ⊓
      LinearMap.range (Matrix.mulVecLin
        (mat (ψ ⟨g, c.H_le d.mem⟩ * ψ ⟨z, c.z_mem⟩ * (ψ ⟨g, c.H_le d.mem⟩)⁻¹) - 1)) := by
    refine ⟨h1, ?_⟩
    have := d.psi_u
    rw [mat] at this
    rw [← this]
    exact h2
  rw [d.inf, Submodule.mem_bot] at h3
  have h4 : (⟨x, hxW⟩ : ↥(commSpace (HH G L v) ⊤)) = 0 := hβ.1 (h3.trans (map_zero β).symm)
  rw [Submodule.mem_bot]
  exact congrArg Subtype.val h4

theorem Vz_eq (hs : CaseIISplit) : commSpace (Subgroup.zpowers z) ⊤ =
    (commSpace (HH G L v) ⊤).map (subOne z) ⊔ (fixedSpace (HH G L v)).map (subOne z) := by
  rw [commSpace_zpowers_top_eq_range c.z_mul_z]
  exact range_eq_sup_of_isCompl (c.split hs) _

theorem U_eq (hs : CaseIISplit) :
    UU z (g * z * g⁻¹) = (fixedSpace (HH G L v)).map (subOne z) := by
  have hVu : commSpace (Subgroup.zpowers (g * z * g⁻¹)) ⊤ =
      (commSpace (HH G L v) ⊤).map (subOne (g * z * g⁻¹)) ⊔
        (fixedSpace (HH G L v)).map (subOne z) := by
    rw [commSpace_zpowers_top_eq_range d.u_mul_u, range_eq_sup_of_isCompl (c.split hs)]
    congr 1
    rw [d.u_eq_z_mul]
    exact c.map_V₁_eq d.zinv_u_mem_H
  rw [UU, d.Vz_eq hs, hVu]
  exact sup_inf_sup_eq (c.split hs).inf_eq_bot (c.map_V₀_le c.z_mem) (c.map_V₀_le d.u_mem_H₁)
    (c.map_V₁_le c.z_mem) (d.inf_V₀ hs)

theorem U_le_V₁ (hs : CaseIISplit) : UU z (g * z * g⁻¹) ≤ fixedSpace (HH G L v) := by
  rw [d.U_eq hs]
  exact c.map_V₁_le c.z_mem

theorem v_mem_V₁ : v ∈ fixedSpace (HH G L v) := fun h hh =>
  (c.data.component.1 hh).2

theorem v_mem_U (hs : CaseIISplit) : v ∈ UU z (g * z * g⁻¹) := by
  rw [d.U_eq hs]
  have hvz : v ∈ commSpace (Subgroup.zpowers z) ⊤ := c.hv
  rw [d.Vz_eq hs] at hvz
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hvz
  have h0 : a ∈ commSpace (HH G L v) ⊤ ⊓ fixedSpace (HH G L v) := by
    refine ⟨c.map_V₀_le c.z_mem ha, ?_⟩
    have : a = v - b := by rw [← hab]; abel
    rw [this]
    exact Submodule.sub_mem _ d.v_mem_V₁ (c.map_V₁_le c.z_mem hb)
  rw [(c.split hs).inf_eq_bot, Submodule.mem_bot] at h0
  have hvb : v = b := by rw [← hab, h0, zero_add]
  convert hb using 1

theorem U_le (hs : CaseIISplit) {h : GLV V} (hh : h ∈ HH G L v) :
    UU z (g * z * g⁻¹) ≤ commSpace (Subgroup.zpowers (h * z * h⁻¹)) ⊤ := by
  have hhz : (h * z * h⁻¹) * (h * z * h⁻¹) = 1 := by
    calc (h * z * h⁻¹) * (h * z * h⁻¹) = h * (z * z) * h⁻¹ := by group
      _ = 1 := by rw [c.z_mul_z, mul_one, mul_inv_cancel]
  have hmem : z⁻¹ * (h * z * h⁻¹) ∈ HH G L v := by
    have h1 : z⁻¹ * h * z ∈ HH G L v := by
      have := c.conj_mem_H (H₁.inv_mem c.z_mem) hh
      simpa [mul_assoc] using this
    have : z⁻¹ * (h * z * h⁻¹) = (z⁻¹ * h * z) * h⁻¹ := by group
    rw [this]
    exact (HH G L v).mul_mem h1 ((HH G L v).inv_mem hh)
  rw [d.U_eq hs, commSpace_zpowers_top_eq_range hhz]
  have e : h * z * h⁻¹ = z * (z⁻¹ * (h * z * h⁻¹)) := by group
  rw [show (fixedSpace (HH G L v)).map (subOne z) =
    (fixedSpace (HH G L v)).map (subOne (h * z * h⁻¹)) by
      rw [e]; exact (c.map_V₁_eq hmem).symm]
  exact LinearMap.map_le_range

theorem isComponentOf_H (hs : CaseIISplit) :
    IsComponentOf (HH G L v) (centralizerOn G (UU z (g * z * g⁻¹))) := by
  refine isComponentOf_of_le_of_le c.data.component ?_ ?_
  · intro h hh
    exact ⟨c.H_le_G hh, fun w hw => d.U_le_V₁ hs hw h hh⟩
  · intro k hk
    exact ⟨hk.1, hk.2 v (d.v_mem_U hs)⟩

theorem map_centralizerOn {x : GLV V} (hxG : x ∈ G)
    (hxU : ∀ w, w ∈ UU z (g * z * g⁻¹) ↔ x w ∈ UU z (g * z * g⁻¹)) :
    (centralizerOn G (UU z (g * z * g⁻¹))).map (MulAut.conj x).toMonoidHom =
      centralizerOn G (UU z (g * z * g⁻¹)) := by
  have hinv : ∀ w, w ∈ UU z (g * z * g⁻¹) → x⁻¹ w ∈ UU z (g * z * g⁻¹) := by
    intro w hw
    rw [hxU]
    simpa using hw
  apply le_antisymm
  · rintro _ ⟨k, hk, rfl⟩
    refine ⟨G.mul_mem (G.mul_mem hxG hk.1) (G.inv_mem hxG), fun w hw => ?_⟩
    show x (k (x⁻¹ w)) = w
    rw [hk.2 _ (hinv w hw)]
    simp
  · intro k hk
    refine ⟨x⁻¹ * k * x, ⟨G.mul_mem (G.mul_mem (G.inv_mem hxG) hk.1) hxG, fun w hw => ?_⟩, ?_⟩
    · show x⁻¹ (k (x w)) = w
      rw [hk.2 _ ((hxU w).1 hw)]
      simp
    · simp [MulAut.conj_apply, mul_assoc]

theorem mem_normalizer_H (hs : CaseIISplit) {x : GLV V} (hxG : x ∈ G)
    (hxU : ∀ w, w ∈ UU z (g * z * g⁻¹) ↔ x w ∈ UU z (g * z * g⁻¹)) :
    x ∈ Subgroup.normalizer (HH G L v : Set (GLV V)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : GLV V →* GLV V := (MulAut.conj x).toMonoidHom with hf
  have hfi : Function.Injective f := (MulAut.conj x).injective
  have hcomp := CFSG.HardMathSupport.Dickson.Bal207.D42Tri.isComponentOf_map_of_injective
    hfi (d.isComponentOf_H hs)
  rw [d.map_centralizerOn hxG hxU] at hcomp
  have heq : (HH G L v).map f = HH G L v := by
    by_contra hne
    have hle : (HH G L v).map f ≤ G ⊓ Subgroup.centralizer (L : Set (GLV V)) := by
      intro y hy
      refine ⟨(hcomp.1 hy).1, Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      exact (CFSG.LargeExtraspecial.S5.mul_comm_of_isComponentOf_ne hcomp
        (d.isComponentOf_H hs) hne hy (c.L_le_H hl)).symm
    have h1 : 2 ≤ CFSG.Open.pRank 2 ((HH G L v).map f) :=
      c.two_le_pRank_L.trans ((CFSG.SectionRank.pRank_le_map (by norm_num) f hfi L).trans
        (CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.map_mono c.L_le_H)))
    have h2 := CFSG.SectionRank.pRank_mono (p := 2) (by norm_num) hle
    rw [c.rank] at h2
    omega
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have : x * y * x⁻¹ ∈ (HH G L v).map f := ⟨y, hy, rfl⟩
    rwa [heq] at this
  · intro hy
    rw [← heq] at hy
    obtain ⟨y', hy', hyy⟩ := hy
    have : y' = y := by
      have h := hyy
      simp only [hf, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
      simpa using h
    rwa [← this]

end GD

namespace Ctx

variable (c : Ctx G L z v H₁ ψ)
include c

theorem exists_H₁_of_normalizer (haut : CaseIIAut) {x : GLV V}
    (hx : x ∈ Subgroup.normalizer (HH G L v : Set (GLV V))) :
    ∃ h₁ ∈ H₁, ∀ y ∈ HH G L v, x * y * x⁻¹ = h₁ * y * h₁⁻¹ := by
  have hx' : ∀ y, y ∈ HH G L v ↔ x * y * x⁻¹ ∈ HH G L v := Subgroup.mem_normalizer_iff.1 hx
  have hxi : ∀ y, y ∈ HH G L v → x⁻¹ * y * x ∈ HH G L v := by
    intro y hy
    rw [hx']
    simpa [mul_assoc] using hy
  let θ : MulAut ↥(HH G L v) :=
    { toFun := fun y => ⟨x * y * x⁻¹, (hx' y).1 y.2⟩
      invFun := fun y => ⟨x⁻¹ * y * x, hxi y y.2⟩
      left_inv := fun y => Subtype.ext (by simp [mul_assoc])
      right_inv := fun y => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  obtain ⟨o, ho, hθ⟩ := haut ((c.phi.symm.trans θ).trans c.phi)
  refine ⟨(ψ.symm ⟨o, ho⟩ : GLV V), (ψ.symm ⟨o, ho⟩).2, fun y hy => ?_⟩
  have hy₁ : y ∈ H₁ := c.H_le hy
  have key := hθ (c.phi ⟨y, hy⟩)
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at key
  have hxy₁ : x * y * x⁻¹ ∈ H₁ := c.H_le ((hx' y).1 hy)
  have hm : (ψ.symm ⟨o, ho⟩ : GLV V) * y * (ψ.symm ⟨o, ho⟩ : GLV V)⁻¹ ∈ H₁ :=
    H₁.mul_mem (H₁.mul_mem (ψ.symm ⟨o, ho⟩).2 hy₁) (H₁.inv_mem (ψ.symm ⟨o, ho⟩).2)
  have h1 : ψ ⟨x * y * x⁻¹, hxy₁⟩ =
      ψ ⟨(ψ.symm ⟨o, ho⟩ : GLV V) * y * (ψ.symm ⟨o, ho⟩ : GLV V)⁻¹, hm⟩ := by
    apply Subtype.ext
    have e : (⟨(ψ.symm ⟨o, ho⟩ : GLV V) * y * (ψ.symm ⟨o, ho⟩ : GLV V)⁻¹, hm⟩ : ↥H₁) =
        ψ.symm ⟨o, ho⟩ * ⟨y, hy₁⟩ * (ψ.symm ⟨o, ho⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [phi_coe, phi_coe] at key
    exact key
  exact congrArg Subtype.val (ψ.injective h1)

end Ctx

namespace GD

variable {c : Ctx G L z v H₁ ψ} {g : GLV V} (d : GD c g)
include d

theorem g_not_mem_normalizer (hG1 : CaseIIG1) :
    g ∉ Subgroup.normalizer (L : Set (GLV V)) := by
  intro hg
  have hgl : ∀ l ∈ L, g⁻¹ * l * g ∈ L := by
    intro l hl
    have := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * l * g)).2
    apply this
    simpa [mul_assoc] using hl
  have hcomm : ∀ l ∈ L, (g * z * g⁻¹) * l = l * (g * z * g⁻¹) := by
    intro l hl
    have h := c.comm_z (hgl l hl)
    calc (g * z * g⁻¹) * l = g * (z * (g⁻¹ * l * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * l * g) * z) * g⁻¹ := by rw [← h]
      _ = l * (g * z * g⁻¹) := by group
  rcases c.eq_one_or_eq_z hG1 d.u_mem_H₁ hcomm with h | h
  · have : z = 1 := by
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [mul_assoc] using this
    have h2 := c.orderOf_z
    rw [this, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · exact d.ne h

theorem odd_card_CH (hG1 : CaseIIG1) :
    Odd (Nat.card ↥(G ⊓ Subgroup.centralizer (HH G L v : Set (GLV V)))) := by
  have hgG : g ∈ G := c.H_le_G d.mem
  have ht := c.std.tight g hgG (d.g_not_mem_normalizer hG1)
  refine ht.of_dvd_nat (Subgroup.card_dvd_of_le ?_)
  intro k hk
  have hkK : k ∈ G ⊓ Subgroup.centralizer (L : Set (GLV V)) :=
    ⟨hk.1, Subgroup.mem_centralizer_iff.2 fun l hl =>
      Subgroup.mem_centralizer_iff.1 hk.2 l (c.L_le_H hl)⟩
  refine ⟨hkK, ⟨k, hkK, ?_⟩⟩
  have hgk : g * k = k * g := Subgroup.mem_centralizer_iff.1 hk.2 g d.mem
  show g * k * g⁻¹ = k
  rw [hgk, mul_inv_cancel_right]

end GD

end CaseII

end CFSG.CGT.Foote82
