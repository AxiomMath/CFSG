module

public import CFSG.LargeExtraspecial.S10EightM

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S10

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6

universe u

variable {G : Type u} [Group G] [Finite G] {S : Setting G} {g : G} {t : S.O}

theorem Lbar_apply_eq_or (haQ : g * S.z * g⁻¹ ∈ S.QG) {v : S.Qt}
    (hv : v ∈ S.clSub (S.QG ⊓ S.Qa g)) {s : S.O} (hs : s ∈ S.Lbar g) :
    (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v ∨
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v + S.cl (g * S.z * g⁻¹) := by
  rcases mem_span_cl_iff.mp (Lbar_apply_sub_mem_span' haQ hv hs) with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_iff_eq_add'.mp h)

theorem card_le_two_mul_vecFix {K : Subgroup S.O} {v w : S.Qt}
    (h : ∀ c ∈ K, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v ∨ (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w) :
    Nat.card K ≤ 2 * Nat.card (K ⊓ vecFix S v : Subgroup S.O) := by
  refine card_le_two_mul_of_mem fun a ha haH b hb hbH =>
    Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) hb, ?_⟩
  have ha' : (a : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w :=
    (h a ha).resolve_left fun h' => haH (Subgroup.mem_inf.mpr ⟨ha, h'⟩)
  have hb' : (b : S.Qt ≃ₗ[ZMod 2] S.Qt) v = w :=
    (h b hb).resolve_left fun h' => hbH (Subgroup.mem_inf.mpr ⟨hb, h'⟩)
  rw [mem_vecFix, coe_mul_apply, hb', ← ha']
  exact inv_apply_apply_O a v

theorem inv_apply_of_apply {x : S.O} {v : S.Qt} (hx : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    ((x⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  conv_lhs => rw [← hx]
  exact inv_apply_apply_O x v

namespace Dec108

variable {X : Hyp10 S g t} {Xb Yb : Subgroup S.O} (D : Dec108 X Xb Yb)
include D

theorem conj_mem_map_of_fix (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {k m : S.M}
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹))
    {c : S.O} (hc : c ∈ (S.Lbar g ⊓ Xb).map (cK S k)) :
    S.ρ m * c * (S.ρ m)⁻¹ ∈ (S.Lbar g ⊓ Xb).map (cK S k) := by
  have hL : S.Lbar (((m * k : S.M) : G) * g) = S.Lbar ((k : G) * g) := by
    refine Lbar_eq_of_cl_eq S (conj_mem_QG' S k.2 X.haQ) (conj_ne_z' S k.2 X.H.conj_ne)
      (conj_mem_QG' S (m * k).2 X.haQ) ?_
    rw [← ρ_cl_conj_z S (m * k) X.haQ, map_mul, coe_mul_apply, ρ_cl_conj_z S k X.haQ, hm]
  rw [← D.map_eq_of_Lbar_eq hCE hP hL]
  obtain ⟨e, he, rfl⟩ := hc
  refine ⟨e, he, ?_⟩
  simp only [cK_apply, map_mul, mul_inv_rev]
  group

theorem conj_mem_of_fix (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) {m : S.M}
    (hm : ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    {e : S.O} (he : e ∈ S.Lbar g ⊓ Xb) : S.ρ m * e * (S.ρ m)⁻¹ ∈ S.Lbar g ⊓ Xb := by
  have hL : S.Lbar ((m : G) * g) = S.Lbar g :=
    Lbar_eq_of_cl_eq S X.haQ X.H.conj_ne (conj_mem_QG' S m.2 X.haQ)
      (by rw [← ρ_cl_conj_z S m X.haQ, hm])
  have hle : (S.Lbar g ⊓ Xb).map (cK S m) ≤ S.Lbar g :=
    hL ▸ map_le_Lbar_mul (g := g) (Xb := Xb) m
  rw [← D.timmesfeld_10_8_two hCE hP hle]
  exact ⟨e, he, rfl⟩

variable {k : S.M}

theorem commute_of_fix (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥) {x b : S.O}
    (hx : x ∈ S.Lbar g ⊓ Xb)
    (hxf : (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) =
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹))
    (hb : b ∈ (S.Lbar g ⊓ Xb).map (cK S k))
    (hba : (b : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹)) :
    x * b = b * x := by
  obtain ⟨mx, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g hx.1)
  obtain ⟨mb, rfl⟩ := MonoidHom.mem_range.mp
    (S.Lbar_le_Mbar _ (map_le_Lbar_mul (g := g) (Xb := Xb) k hb))
  have h1 := D.conj_mem_map_of_fix hCE hP hxf hb
  have h2 := D.conj_mem_of_fix hCE hP hba (inv_mem hx)
  have hF : S.ρ mx * S.ρ mb * (S.ρ mx)⁻¹ * (S.ρ mb)⁻¹ ∈ (S.Lbar g ⊓ Xb).map (cK S k) :=
    mul_mem h1 (inv_mem hb)
  have hE : S.ρ mx * S.ρ mb * (S.ρ mx)⁻¹ * (S.ρ mb)⁻¹ ∈ S.Lbar g ⊓ Xb := by
    have e1 : S.ρ mx * S.ρ mb * (S.ρ mx)⁻¹ * (S.ρ mb)⁻¹ =
        S.ρ mx * (S.ρ mb * (S.ρ mx)⁻¹ * (S.ρ mb)⁻¹) := by group
    rw [e1]
    exact mul_mem hx h2
  have h0 : S.ρ mx * S.ρ mb * (S.ρ mx)⁻¹ * (S.ρ mb)⁻¹ ∈
      (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) := ⟨hE, hF⟩
  rw [hinf, Subgroup.mem_bot] at h0
  calc S.ρ mx * S.ρ mb = S.ρ mx * S.ρ mb * (S.ρ mx)⁻¹ * (S.ρ mb)⁻¹ * (S.ρ mb * S.ρ mx) := by
        group
    _ = S.ρ mb * S.ρ mx := by rw [h0, one_mul]

theorem exists_not_fix (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥) :
    ∃ x₀ ∈ S.Lbar g ⊓ Xb, (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt)
      (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) ≠
        S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) := by
  by_contra hcon
  push Not at hcon
  have hnorm : ∀ e ∈ S.Lbar g ⊓ Xb, ∀ c ∈ (S.Lbar g ⊓ Xb).map (cK S k),
      e * c * e⁻¹ ∈ (S.Lbar g ⊓ Xb).map (cK S k) := by
    intro e he c hc
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp (S.Lbar_le_Mbar g he.1)
    exact D.conj_mem_map_of_fix hCE hP (hcon _ he) hc
  have hkM : (S.ρ k)⁻¹ ∈ S.Mbar := inv_mem (MonoidHom.mem_range.mpr ⟨k, rfl⟩)
  have h3 := D.timmesfeld_10_8_three hCE hP h7 hkM (fun e he => by
    rw [mem_normalizer_iff]
    intro w
    rw [inv_inv]
    constructor
    · intro hw
      have hc : S.ρ k * w * (S.ρ k)⁻¹ ∈ (S.Lbar g ⊓ Xb).map (cK S k) := ⟨w, hw, rfl⟩
      have h1 := hnorm e he _ hc
      rw [mem_map_cK_iff] at h1
      have e1 : (S.ρ k)⁻¹ * e * S.ρ k * w * ((S.ρ k)⁻¹ * e * S.ρ k)⁻¹ =
          (S.ρ k)⁻¹ * (e * (S.ρ k * w * (S.ρ k)⁻¹) * e⁻¹) * S.ρ k := by group
      rw [e1]
      exact h1
    · intro hw
      have hc : S.ρ k * ((S.ρ k)⁻¹ * e * S.ρ k * w * ((S.ρ k)⁻¹ * e * S.ρ k)⁻¹) *
          (S.ρ k)⁻¹ ∈ (S.Lbar g ⊓ Xb).map (cK S k) := ⟨_, hw, rfl⟩
      have h1 := hnorm e⁻¹ (inv_mem he) _ hc
      rw [mem_map_cK_iff] at h1
      have e1 : (S.ρ k)⁻¹ * (e⁻¹ * (S.ρ k * ((S.ρ k)⁻¹ * e * S.ρ k * w *
          ((S.ρ k)⁻¹ * e * S.ρ k)⁻¹) * (S.ρ k)⁻¹) * e⁻¹⁻¹) * S.ρ k = w := by group
      rw [e1] at h1
      exact h1)
  have ht : t ∈ (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) := by
    refine Subgroup.mem_inf.mpr ⟨D.t_mem_Ebar hCE, ?_⟩
    rw [mem_map_cK_iff]
    have := h3 t (D.t_mem_Ebar hCE)
    rwa [inv_inv] at this
  rw [hinf, Subgroup.mem_bot] at ht
  exact X.ht1 ht

theorem eq_one_of_commute (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    {x₀ : S.O} (hx₀ : x₀ ∈ S.Lbar g ⊓ Xb)
    (hx₀f : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) ≠
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹))
    {c : S.O} (hc : c ∈ (S.Lbar g ⊓ Xb).map (cK S k))
    (hca : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹))
    (hcx : c * x₀ = x₀ * c) : c = 1 := by
  set fv := S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) with hfv
  have hx₀f' := (Lbar_apply_eq_or X.haQ hkP hx₀.1).resolve_left hx₀f
  have hcE : ∀ e ∈ S.Lbar g ⊓ Xb, c * e = e * c := by
    intro e he
    by_cases hef : (e : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv
    · exact (D.commute_of_fix hCE hP hinf he hef hc hca).symm
    · have hef' := (Lbar_apply_eq_or X.haQ hkP he.1).resolve_left hef
      have hfix : ((x₀⁻¹ * e : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) fv = fv := by
        rw [coe_mul_apply, hef', ← hx₀f']
        exact inv_apply_apply_O x₀ fv
      have h1 := D.commute_of_fix hCE hP hinf (mul_mem (inv_mem hx₀) he) hfix hc hca
      calc c * e = c * (x₀ * (x₀⁻¹ * e)) := by group
        _ = x₀ * (c * (x₀⁻¹ * e)) := by rw [← mul_assoc, hcx, mul_assoc]
        _ = x₀ * ((x₀⁻¹ * e) * c) := by rw [← h1]
        _ = e * c := by group
  have hc' := (mem_map_cK_iff k).mp hc
  have hcE' := D.conj_mem_Ebar_of_commute hCE hP h7 hc'
    (MonoidHom.mem_range.mpr ⟨k, rfl⟩) fun x hx => by
      rw [show S.ρ k * ((S.ρ k)⁻¹ * c * S.ρ k) * (S.ρ k)⁻¹ = c by group]
      exact hcE x hx
  rw [show S.ρ k * ((S.ρ k)⁻¹ * c * S.ρ k) * (S.ρ k)⁻¹ = c by group] at hcE'
  have h0 : c ∈ (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) := ⟨hcE', hc⟩
  rw [hinf, Subgroup.mem_bot] at h0
  exact h0

theorem injective_comm (hCE : CentralExtInput.{u}) (hP : NoPGL25 S g) (h7 : 7 ≤ S.width)
    (hinf : (S.Lbar g ⊓ Xb) ⊓ (S.Lbar g ⊓ Xb).map (cK S k) = ⊥)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    {x₀ : S.O} (hx₀ : x₀ ∈ S.Lbar g ⊓ Xb)
    (hx₀f : (x₀ : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) ≠
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) :
    Function.Injective fun b : ((S.Lbar g ⊓ Xb).map (cK S k) ⊓ vecFix S (S.cl (g * S.z * g⁻¹)) :
      Subgroup S.O) => x₀ * (b : S.O) * x₀⁻¹ * (b : S.O)⁻¹ := by
  intro b₁ b₂ h12
  have hc : ((b₂ : S.O)⁻¹ * b₁) ∈ (S.Lbar g ⊓ Xb).map (cK S k) ⊓
      vecFix S (S.cl (g * S.z * g⁻¹)) := mul_mem (inv_mem b₂.2) b₁.2
  have hcx : ((b₂ : S.O)⁻¹ * b₁) * x₀ = x₀ * ((b₂ : S.O)⁻¹ * b₁) := by
    have h12' : x₀ * (b₁ : S.O) * x₀⁻¹ * (b₁ : S.O)⁻¹ = x₀ * (b₂ : S.O) * x₀⁻¹ * (b₂ : S.O)⁻¹ :=
      h12
    have e1 : (b₁ : S.O) * x₀⁻¹ * (b₁ : S.O)⁻¹ = (b₂ : S.O) * x₀⁻¹ * (b₂ : S.O)⁻¹ := by
      calc (b₁ : S.O) * x₀⁻¹ * (b₁ : S.O)⁻¹ =
            x₀⁻¹ * (x₀ * (b₁ : S.O) * x₀⁻¹ * (b₁ : S.O)⁻¹) := by group
        _ = x₀⁻¹ * (x₀ * (b₂ : S.O) * x₀⁻¹ * (b₂ : S.O)⁻¹) := by rw [h12']
        _ = (b₂ : S.O) * x₀⁻¹ * (b₂ : S.O)⁻¹ := by group
    have e2 : ((b₂ : S.O)⁻¹ * b₁) * x₀⁻¹ * ((b₂ : S.O)⁻¹ * b₁)⁻¹ = x₀⁻¹ := by
      calc ((b₂ : S.O)⁻¹ * b₁) * x₀⁻¹ * ((b₂ : S.O)⁻¹ * b₁)⁻¹ =
            (b₂ : S.O)⁻¹ * ((b₁ : S.O) * x₀⁻¹ * (b₁ : S.O)⁻¹) * b₂ := by group
        _ = (b₂ : S.O)⁻¹ * ((b₂ : S.O) * x₀⁻¹ * (b₂ : S.O)⁻¹) * b₂ := by rw [e1]
        _ = x₀⁻¹ := by group
    calc ((b₂ : S.O)⁻¹ * b₁) * x₀ =
          (((b₂ : S.O)⁻¹ * b₁) * x₀⁻¹ * ((b₂ : S.O)⁻¹ * b₁)⁻¹)⁻¹ * ((b₂ : S.O)⁻¹ * b₁) := by
          group
      _ = x₀⁻¹⁻¹ * ((b₂ : S.O)⁻¹ * b₁) := by rw [e2]
      _ = x₀ * ((b₂ : S.O)⁻¹ * b₁) := by rw [inv_inv]
  have h1 := D.eq_one_of_commute hCE hP h7 hinf hkP hx₀ hx₀f hc.1 hc.2 hcx
  have h2 : (b₁ : S.O) = b₂ := by
    calc (b₁ : S.O) = b₂ * ((b₂ : S.O)⁻¹ * b₁) := by group
      _ = b₂ := by rw [h1, mul_one]
  exact Subtype.ext h2

theorem card_B0 (hCE : CentralExtInput.{u}) (h7 : 7 ≤ S.width)
    (hkP : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ∈ S.clSub (S.QG ⊓ S.Qa g))
    (hk1 : S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹) ≠ S.cl (g * S.z * g⁻¹)) :
    2 ^ (S.width - 3) ≤ Nat.card ((S.Lbar g ⊓ Xb).map (cK S k) ⊓
      vecFix S (S.cl (g * S.z * g⁻¹)) : Subgroup S.O) := by
  have haP := X.mem_clSub_symm hkP hk1
  have h1 := card_le_two_mul_vecFix (K := (S.Lbar g ⊓ Xb).map (cK S k))
    (v := S.cl (g * S.z * g⁻¹)) (w := S.cl (g * S.z * g⁻¹) +
      S.cl ((k : G) * g * S.z * ((k : G) * g)⁻¹)) fun c hc =>
    Lbar_apply_eq_or (conj_mem_QG' S k.2 X.haQ) haP
      (map_le_Lbar_mul (g := g) (Xb := Xb) k hc)
  rw [Subgroup.card_map_of_injective (cK_injective k), D.card_Ebar hCE h7] at h1
  have h2 : 2 ^ (S.width - 2) = 2 * 2 ^ (S.width - 3) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

end Dec108

end CFSG.LargeExtraspecial.S10
