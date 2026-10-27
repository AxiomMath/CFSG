module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301BGenULin
public import CFSG.Sporadic.Co1Patterson.Defs
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.H301B

open CFSG.Open CFSG.Sporadic.Co1Patterson

private theorem cases_zmod_two (c : ZMod 2) : c = 0 ∨ c = 1 :=
  (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) c

section TypeSystem

variable {n : ℕ} {L : Type} [Group L]
  {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))}
  {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
  {H : Type} [Group H]

theorem typeSystem_bil_add_left (T : ExtraspecialTypeSystem n L act qf bil H)
    (u u' v : Fin n → ZMod 2) : bil (u + u') v = bil u v + bil u' v := by
  obtain ⟨p, hp, rfl⟩ := T.vec_surj u
  obtain ⟨p', hp', rfl⟩ := T.vec_surj u'
  obtain ⟨q, hq, rfl⟩ := T.vec_surj v
  have hpp : T.φ (p * p') = 1 := by rw [map_mul, hp, hp', one_mul]
  have hkey : p * p' * q * (p * p')⁻¹ * q⁻¹ =
      p * (p' * q * p'⁻¹ * q⁻¹) * p⁻¹ * (p * q * p⁻¹ * q⁻¹) := by group
  have hz : p * T.z * p⁻¹ = T.z := by rw [T.z_comm p, mul_inv_cancel_right]
  rw [← T.vec_mul p p' hp hp']
  rcases cases_zmod_two (bil (T.vec p) (T.vec q)) with h1 | h1 <;>
    rcases cases_zmod_two (bil (T.vec p') (T.vec q)) with h2 | h2
  · have c1 := (T.comm_eq_one_iff p q hp hq).2 h1
    have c2 := (T.comm_eq_one_iff p' q hp' hq).2 h2
    rw [h1, h2]
    refine ((T.comm_eq_one_iff _ _ hpp hq).1 ?_).trans (by decide)
    rw [hkey, c1, c2]
    simp only [mul_one, mul_inv_cancel]
  · have c1 := (T.comm_eq_one_iff p q hp hq).2 h1
    have c2 := (T.comm_eq_z_iff p' q hp' hq).2 h2
    rw [h1, h2]
    exact ((T.comm_eq_z_iff _ _ hpp hq).1 (by rw [hkey, c1, c2, hz, mul_one])).trans (by decide)
  · have c1 := (T.comm_eq_z_iff p q hp hq).2 h1
    have c2 := (T.comm_eq_one_iff p' q hp' hq).2 h2
    rw [h1, h2]
    refine ((T.comm_eq_z_iff _ _ hpp hq).1 ?_).trans (by decide)
    rw [hkey, c1, c2, mul_one, mul_inv_cancel, one_mul]
  · have c1 := (T.comm_eq_z_iff p q hp hq).2 h1
    have c2 := (T.comm_eq_z_iff p' q hp' hq).2 h2
    rw [h1, h2]
    refine ((T.comm_eq_one_iff _ _ hpp hq).1 ?_).trans (by decide)
    rw [hkey, c1, c2, hz, T.z_mul_self]

theorem typeSystem_bil_nondeg (T : ExtraspecialTypeSystem n L act qf bil H)
    (w : Fin n → ZMod 2) (hw : ∀ v, bil v w = 0) : w = 0 := by
  obtain ⟨q, hq, rfl⟩ := T.vec_surj w
  refine (T.vec_eq_zero q hq).2 (T.center_eq q hq fun p hp => ?_)
  have h := (T.comm_eq_one_iff p q hp hq).2 (hw _)
  calc p * q = (p * q * p⁻¹ * q⁻¹) * (q * p) := by group
    _ = q * p := by rw [h, one_mul]

theorem typeSystem_bil_act (T : ExtraspecialTypeSystem n L act qf bil H) (l : L)
    (v w : Fin n → ZMod 2) : bil (act l v) (act l w) = bil v w := by
  obtain ⟨c, rfl⟩ := T.φ_surj l
  obtain ⟨p, hp, rfl⟩ := T.vec_surj v
  obtain ⟨q, hq, rfl⟩ := T.vec_surj w
  have hc : ∀ r, T.φ r = 1 → T.φ (c * r * c⁻¹) = 1 := fun r hr => by
    rw [map_mul, map_mul, hr, mul_one, map_inv, mul_inv_cancel]
  have hkey : c * p * c⁻¹ * (c * q * c⁻¹) * (c * p * c⁻¹)⁻¹ * (c * q * c⁻¹)⁻¹ =
      c * (p * q * p⁻¹ * q⁻¹) * c⁻¹ := by group
  rw [← T.vec_conj c p hp, ← T.vec_conj c q hq]
  rcases cases_zmod_two (bil (T.vec p) (T.vec q)) with h | h
  · rw [h]
    refine (T.comm_eq_one_iff _ _ (hc p hp) (hc q hq)).1 ?_
    rw [hkey, (T.comm_eq_one_iff p q hp hq).2 h, mul_one, mul_inv_cancel]
  · rw [h]
    refine (T.comm_eq_z_iff _ _ (hc p hp) (hc q hq)).1 ?_
    rw [hkey, (T.comm_eq_z_iff p q hp hq).2 h, T.z_comm c, mul_inv_cancel_right]

private theorem typeSystem_eq_one_of_pow_three (T : ExtraspecialTypeSystem n L act qf bil H)
    {q : H} (hq : T.φ q = 1) (h3 : q ^ 3 = 1) : q = 1 := by
  have h4 : q ^ 4 = 1 := by
    rcases cases_zmod_two (qf (T.vec q)) with h | h
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, (T.mul_self_eq_one_iff q hq).2 h, one_mul]
    · rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq, (T.mul_self_eq_z_iff q hq).2 h,
        T.z_mul_self]
  calc q = q ^ 4 * (q ^ 3)⁻¹ := by group
    _ = 1 := by rw [h4, h3, inv_one, one_mul]

end TypeSystem

theorem le_ker_of_typeSystem {n k : ℕ} (hn : n = 2 * k) {L : Type} [Group L]
    {act : L →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2))} (hact : Function.Injective act)
    {qf : (Fin n → ZMod 2) → ZMod 2} {bil : (Fin n → ZMod 2) → (Fin n → ZMod 2) → ZMod 2}
    {H : Type} [Group H] (T : ExtraspecialTypeSystem n L act qf bil H)
    {F X : Subgroup H} (hF : IsElemAbelian 3 F) (hFc : Nat.card F = 3 ^ k)
    (hX : IsPGroup 2 X) (hFX : F ≤ Subgroup.normalizer (X : Set H)) : X ≤ T.φ.ker := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H →* ((Fin n → ZMod 2) ≃ₗ[ZMod 2] (Fin n → ZMod 2)),
      ∀ h, ψ h = act (T.φ h) := ⟨act.comp T.φ, fun _ => rfl⟩
  have hψker : ∀ h, ψ h = 1 → T.φ h = 1 := fun h hh => hact (by rw [← hψ h, hh, map_one])
  have hinjF : Function.Injective (ψ.comp F.subtype) := by
    rw [injective_iff_map_eq_one]
    intro f hf
    exact Subtype.ext (typeSystem_eq_one_of_pow_three T (hψker _ hf) (hF.2 f f.2))
  have hrange : (ψ.comp F.subtype).range = F.map ψ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hEc : Nat.card (F.map ψ) = 3 ^ k := by
    rw [← hrange, ← hFc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinjF).toEquiv).symm
  have hET : F.map ψ ≤ Subgroup.normalizer ((X.map ψ : Subgroup _) : Set _) :=
    (Subgroup.map_mono hFX).trans (Subgroup.le_normalizer_map ψ)
  have hbil : ∀ K : Subgroup H, ∀ g ∈ K.map ψ, ∀ v w, bil (g v) (g w) = bil v w := by
    intro K g hg v w
    obtain ⟨h, -, rfl⟩ := Subgroup.mem_map.1 hg
    rw [hψ]
    exact typeSystem_bil_act T (T.φ h) v w
  have hbot : X.map ψ = ⊥ := eq_bot_of_normalizes_isometry (by rw [Module.finrank_fin_fun, hn])
    bil (typeSystem_bil_add_left T) (typeSystem_bil_nondeg T) (hF.map ψ) hEc (hX.map ψ) hET
    (hbil F) (hbil X)
  intro x hx
  have h1 : ψ x ∈ X.map ψ := Subgroup.mem_map_of_mem ψ hx
  rw [hbot, Subgroup.mem_bot] at h1
  exact MonoidHom.mem_ker.2 (hψker x h1)

end CFSG.LocalAnalysis.GLTheoremA.H301B

end
