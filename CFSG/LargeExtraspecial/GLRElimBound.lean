module

public import CFSG.LargeExtraspecial.GLRCentOrth
public import CFSG.LargeExtraspecial.GLRElimCent
public import CFSG.LargeExtraspecial.GLRElimSylow

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.GLR

open Subgroup Module QuadraticMap CFSG.GH74.GLS.Bg.Thompson
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {S : Setting G} {C : Config S}

namespace Config

variable (C)

theorem commutatorElement_mem_X {a b : G} (ha : a ∈ S.M) (hb : b ∈ S.M) : ⁅a, b⁆ ∈ C.X := by
  rw [commutatorElement_def]
  have hab := C.mul_mem_X_iff ha hb
  have hab' := C.mul_mem_X_iff (S.M.inv_mem ha) (S.M.inv_mem hb)
  have hinv : ∀ {g : G}, g⁻¹ ∈ C.X ↔ g ∈ C.X := fun {g} => ⟨fun h => by simpa using C.X.inv_mem h,
    fun h => C.X.inv_mem h⟩
  rw [hinv, hinv] at hab'
  have h := C.mul_mem_X_iff (S.M.mul_mem ha hb) (S.M.mul_mem (S.M.inv_mem ha) (S.M.inv_mem hb))
  rw [mul_assoc (a * b)]
  exact h.mpr (by rw [hab, hab'])

theorem commutator_le_X {T : Subgroup G} (hT : T ≤ S.M) : ⁅T, T⁆ ≤ C.X :=
  commutator_le.mpr fun _ ha _ hb => C.commutatorElement_mem_X (hT ha) (hT hb)

end Config

namespace Levi

variable (Λ : Levi C)

theorem centralizer_QG_le {τ : G} {T : Subgroup G} (hT : IsSylowIn 2 T (centralizer {τ} ⊓ S.M)) :
    S.QG ⊓ centralizer {τ} ≤ T := SylowIn.le_of_normal hT
  (fun q hq => ⟨hq.2, S.QG_le_M hq.1⟩) ((Config.isPGroup_QG S).to_le inf_le_left)
  (fun g hg q hq => mem_inf.mpr ⟨S.conj_mem_QG hg.2 hq.1, mem_centralizer_singleton_iff.mpr (by
    have h1 := mem_centralizer_singleton_iff.mp hg.1
    have h2 := mem_centralizer_singleton_iff.mp hq.2
    calc g * q * g⁻¹ * τ = g * q * (g⁻¹ * (τ * g)) * g⁻¹ := by group
      _ = g * q * (g⁻¹ * (g * τ)) * g⁻¹ := by rw [h1]
      _ = g * (q * τ) * g⁻¹ := by group
      _ = g * (τ * q) * g⁻¹ := by rw [h2]
      _ = (g * τ) * q * g⁻¹ := by group
      _ = (τ * g) * q * g⁻¹ := by rw [h1]
      _ = τ * (g * q * g⁻¹) := by group)⟩)

theorem mem_of_sylowIn {τ : G} (hτM : τ ∈ S.M) (hττ : τ * τ = 1) {T : Subgroup G}
    (hT : IsSylowIn 2 T (centralizer {τ} ⊓ S.M)) : τ ∈ T := by
  have hmem := fun {y : G} => Setting.mem_zpowers_iff_of_mul_self (x := y) hττ
  have hle := SylowIn.le_of_normal hT (N := zpowers τ)
    (zpowers_le.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, hτM⟩)
    (fun g => ⟨1, Subtype.ext (by
      rcases hmem.mp g.2 with h | h <;>
        simp only [pow_one, pow_two, Subgroup.coe_mul, h, mul_one, OneMemClass.coe_one, hττ])⟩)
    (fun g hg y hy => by
      have h1 := mem_centralizer_singleton_iff.mp hg.1
      rcases hmem.mp hy with rfl | rfl
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · rw [h1, mul_inv_cancel_right]
        exact mem_zpowers _)
  exact hle (mem_zpowers τ)

theorem sylowIn_centralizer {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X) (hττ : τ * τ = 1)
    (hβ : IsGoodForm (C.formOf (S.ρ ⟨τ, hτM⟩))) {T : Subgroup G}
    (hT : IsSylowIn 2 T (centralizer {τ} ⊓ S.M)) (hzT : S.z ∈ ⁅T, T⁆) :
    IsSylowIn 2 T (centralizer {τ}) := by
  refine SylowIn.of_normalizer hT inf_le_left fun P hP _ s hsP hsN => ?_
  have hsC : s ∈ centralizer {τ} := hP hsP
  have hTM : T ≤ S.M := fun t ht => (SylowIn.le hT ht).2
  have hsT : ∀ t ∈ T, s * t * s⁻¹ ∈ T := fun t ht => (mem_normalizer_iff.mp hsN t).mp ht
  have hsT' : ∀ t ∈ T, s⁻¹ * t * s ∈ T := fun t ht => by
    have := (mem_normalizer_iff.mp (inv_mem hsN) t).mp ht
    rwa [inv_inv] at this
  have hw : s * S.z * s⁻¹ ∈ ⁅T, T⁆ := by
    have hle : ⁅T, T⁆ ≤ (⁅T, T⁆).comap (MulAut.conj s).toMonoidHom :=
      commutator_le.mpr fun a ha b hb => by
        rw [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          show s * ⁅a, b⁆ * s⁻¹ = ⁅s * a * s⁻¹, s * b * s⁻¹⁆ by
            simp only [commutatorElement_def]; group]
        exact commutator_mem_commutator (hsT a ha) (hsT b hb)
    have := hle hzT
    rwa [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  have hwX : s * S.z * s⁻¹ ∈ C.X := C.commutator_le_X hTM hw
  have hwc : ∀ t ∈ T, (s * S.z * s⁻¹) * t = t * (s * S.z * s⁻¹) := by
    intro t ht
    have h1 := S.z_comm (hTM (hsT' t ht))
    calc s * S.z * s⁻¹ * t = s * (S.z * (s⁻¹ * t * s)) * s⁻¹ := by group
      _ = s * ((s⁻¹ * t * s) * S.z) * s⁻¹ := by rw [h1]
      _ = t * (s * S.z * s⁻¹) := by group
  have hwQ : s * S.z * s⁻¹ ∈ S.QG := Config.mem_QG_of_commute hτM hτX (Or.inl hττ) hβ hwX
    fun q hq hqτ => hwc q (centralizer_QG_le hT
      ⟨hq, mem_centralizer_singleton_iff.mpr hqτ.symm⟩)
  have hτT := mem_of_sylowIn hτM hττ hT
  have hwz := Config.conj_eq_z_of_commute hτM hτX hwQ (hwc τ hτT).symm
  refine ⟨hsC, S.mem_M_iff.mpr ?_⟩
  calc s * S.z = s * S.z * s⁻¹ * s := by group
    _ = S.z * s := by rw [hwz]

theorem card_centralizer_QG_le {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X) (hττ : τ * τ = 1) :
    Nat.card (S.QG ⊓ centralizer {τ} : Subgroup G) ≤
      2 * Nat.card {a : C.At // C.formOf (S.ρ ⟨τ, hτM⟩) a a = 0} := by
  classical
  set s := S.ρ ⟨τ, hτM⟩
  have hsM : s ∈ S.Mbar := Config.ρ_mem_Mbar _
  have hsX : s ∉ C.Xbar := Config.ρ_not_mem_Xbar hτM hτX
  let rep : S.Qt → G := fun v => Classical.choose (S.exists_cl v)
  have key : ∀ q : (S.QG ⊓ centralizer {τ} : Subgroup G),
      C.formOf s (C.projA (S.cl q)) (C.projA (S.cl q)) = 0 ∧
        S.cl q = C.projA (S.cl q) + (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (C.projA (S.cl q)) := by
    intro q
    obtain ⟨a, ha, haa, hcl⟩ := Config.exists_cl_eq_of_commute hτM hτX (Or.inl hττ) q.2.1
      (mem_centralizer_singleton_iff.mp q.2.2).symm
    have hp : C.projA (S.cl q) = ⟨a, ha⟩ := by
      rw [hcl, map_add, C.projA_of_mem_At ha,
        C.projA_of_mem_Bt (C.apply_mem_Bt_of_not_mem hsM hsX ha), add_zero]
    rw [hp]
    exact ⟨haa, hcl⟩
  let f : (S.QG ⊓ centralizer {τ} : Subgroup G) → {a : C.At // C.formOf s a a = 0} × Bool :=
    fun q => (⟨C.projA (S.cl q), (key q).1⟩, decide ((q : G) = rep (S.cl q)))
  have hf : Function.Injective f := by
    intro q q' hqq'
    have h1 : C.projA (S.cl q) = C.projA (S.cl q') := congrArg Subtype.val (congrArg Prod.fst hqq')
    have h2 := congrArg Prod.snd hqq'
    have hcl : S.cl q = S.cl q' := by rw [(key q).2, (key q').2, h1]
    have hrep : rep (S.cl q) ∈ S.QG ∧ S.cl (rep (S.cl q)) = S.cl q :=
      Classical.choose_spec (S.exists_cl (S.cl q))
    rcases (S.cl_eq_cl_iff q.2.1 q'.2.1).mp hcl with h | h
    · exact Subtype.ext h.symm
    · exfalso
      have hz1 : (q : G) * S.z ≠ q := fun he => S.z_ne_one (mul_eq_left.mp he)
      have h2' : decide ((q : G) = rep (S.cl q)) = decide ((q : G) * S.z = rep (S.cl q)) := by
        have := h2
        simp only [f] at this
        rwa [← hcl, h] at this
      generalize rep (S.cl q) = r at hrep h2'
      rcases (S.cl_eq_cl_iff q.2.1 hrep.1).mp hrep.2.symm with rfl | rfl
      · simp [hz1] at h2'
      · simp [hz1.symm] at h2'
  calc Nat.card (S.QG ⊓ centralizer {τ} : Subgroup G)
      ≤ Nat.card ({a : C.At // C.formOf s a a = 0} × Bool) := Nat.card_le_card_of_injective f hf
    _ = 2 * Nat.card {a : C.At // C.formOf s a a = 0} := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, mul_comm]

theorem card_le_of_sylowIn {τ : G} (hτM : τ ∈ S.M) (hτX : τ ∉ C.X) (hττ : τ * τ = 1)
    (hβ : IsGoodForm (C.formOf (S.ρ ⟨τ, hτM⟩))) {T : Subgroup G}
    (hT : IsSylowIn 2 T (centralizer {τ} ⊓ S.M)) :
    Nat.card T ≤ 2 ^ (2 + 2 * (S.width / 2) + (S.width / 2) ^ 2) := by
  set s := S.ρ ⟨τ, hτM⟩
  have hTM : T ≤ S.M := fun t ht => (SylowIn.le hT ht).2
  have hTC : T ≤ centralizer {τ} := fun t ht => (SylowIn.le hT ht).1
  have hτT := mem_of_sylowIn hτM hττ hT
  have hidx := C.relIndex_inf_X hTM hτT hτX
  have hcardT : Nat.card T = 2 * Nat.card (T ⊓ C.X : Subgroup G) := by
    have := relIndex_mul_card (T ⊓ C.X) T
    rw [hidx, inf_right_comm, inf_idem] at this
    exact this.symm
  set T₀ : Subgroup G := T ⊓ C.X with hT₀
  let f : T₀ →* (C.At ≃ₗ[ZMod 2] C.At) :=
    C.resAt.comp (C.xbarHom.comp (inclusion (inf_le_right : T₀ ≤ C.X)))
  have hcard0 : Nat.card T₀ = Nat.card f.range * Nat.card f.ker := by
    rw [card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
  have hker : Nat.card f.ker ≤ Nat.card (S.QG ⊓ centralizer {τ} : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun x => ⟨((x : T₀) : G), ?_, ?_⟩) ?_
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have h1 : C.xbarHom (inclusion (inf_le_right : T₀ ≤ C.X) x) = 1 :=
        C.resAt_injective (by rw [map_one]; exact hx)
      exact (S.ρ_eq_one_iff _).mp (congrArg Subtype.val h1)
    · exact hTC (x : T₀).2.1
    · intro a b hab
      have h : ((a : T₀) : G) = ((b : T₀) : G) :=
        congrArg (fun y : (S.QG ⊓ centralizer {τ} : Subgroup G) => (y : G)) hab
      exact Subtype.ext (Subtype.ext h)
  have hrange : Nat.card f.range ≤ 2 ^ ((S.width / 2) ^ 2) := by
    have hT₀2 : IsPGroup 2 T₀ := (SylowIn.isPGroup hT).to_le inf_le_left
    have h2 : IsPGroup 2 f.range := hT₀2.of_surjective f.rangeRestrict f.rangeRestrict_surjective
    have hiso : f.range ≤ TauCeti.BilinForm.isometryGroup (C.formOf s) := by
      rintro _ ⟨x, rfl⟩
      rw [TauCeti.BilinForm.mem_isometryGroup_iff]
      intro a a'
      have hxM := hTM (x : T₀).2.1
      have hxτ : S.ρ ⟨(x : G), hxM⟩ * s = s * S.ρ ⟨(x : G), hxM⟩ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (mem_centralizer_singleton_iff.mp (hTC (x : T₀).2.1))
      change polar S.q ((S.ρ ⟨(x : G), hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a)
        ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) ((S.ρ ⟨(x : G), hxM⟩ : S.Qt ≃ₗ[ZMod 2] S.Qt) a')) =
          polar S.q a ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) a')
      rw [← Config.mul_apply s, ← hxτ, Config.mul_apply, Config.polar_apply_apply]
    have := card_le_of_isPGroup hβ.isSymm hβ.nondegenerate h2 hiso
    rwa [C.finrank_At] at this
  have hCQ := card_centralizer_QG_le hτM hτX hττ
  have hW := hβ.card_le
  rw [C.finrank_At] at hW
  calc Nat.card T = 2 * (Nat.card f.range * Nat.card f.ker) := by rw [hcardT, hcard0]
    _ ≤ 2 * (2 ^ ((S.width / 2) ^ 2) * (2 * 2 ^ (2 * (S.width / 2)))) := by
        gcongr
        exact hker.trans (hCQ.trans (Nat.mul_le_mul_left 2 hW))
    _ = 2 ^ (2 + 2 * (S.width / 2) + (S.width / 2) ^ 2) := by ring

end Levi

end CFSG.LargeExtraspecial.GLR
