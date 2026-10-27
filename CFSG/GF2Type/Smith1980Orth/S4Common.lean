module

public import CFSG.GF2Type.Smith1980Orth.S4Types
public import CFSG.GF2Type.Smith1980Orth.S4Fixed
public import CFSG.GF2Type.Smith1980Orth.S3Bad
public import CFSG.GF2Type.Smith1980Orth.S3Good

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module QuadraticMap CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
  CFSG.LargeExtraspecial.S14 CFSG.RankThree.OrthogonalInvolutions
open CFSG.ClassicalGroups.Orthogonal (eichler HypPair)

variable {G : Type} [Group G] [Finite G]

structure SixAt (T : Setting G) : Prop where
  s2 : Nonempty (S2Data T)
  six_le : 6 ≤ T.width
  noBad : ∀ k : G, ¬ Bad T k
  e34a : OE34a T
  e34b : OE34b T
  local_ : OLocal T
  line : OE24Line T

namespace SixAt

variable {T : Setting G}

theorem types (H : SixAt T) (D : S2Data T) : D.OTypes := by
  intro x hx hxM hxQ
  obtain ⟨k, rfl⟩ := isConj_iff.mp hx
  exact D.types_of_good H.six_le hxM hxQ (exists_of_not_bad (H.noBad k) hxM hxQ)

theorem Dl_ne_bot (H : SixAt T) {k : G} (hxM : k * T.z * k⁻¹ ∈ T.M)
    (hxQ : k * T.z * k⁻¹ ∉ T.QG) : T.QG ⊓ T.Qa k ≠ ⊥ := by
  obtain ⟨a, ha, haΔ⟩ := exists_of_not_bad (H.noBad k) hxM hxQ
  intro h
  rw [h, Subgroup.mem_bot] at haΔ
  subst haΔ
  obtain ⟨g, hg⟩ := isConj_iff.mp ha
  apply T.z_ne_one
  calc T.z = g⁻¹ * (g * T.z * g⁻¹) * g := by group
    _ = 1 := by rw [hg]; group

theorem card_eq_of_orderOf_eq_three (H : SixAt T) {ka kb : G}
    (haM : ka * T.z * ka⁻¹ ∈ T.M) (hbM : kb * T.z * kb⁻¹ ∈ T.M)
    (h3 : orderOf (ka * T.z * ka⁻¹ * (kb * T.z * kb⁻¹)) = 3) :
    Nat.card (T.QG ⊓ T.Qa ka : Subgroup G) = Nat.card (T.QG ⊓ T.Qa kb : Subgroup G) := by
  obtain ⟨D⟩ := H.s2
  obtain ⟨haQ, hbQ, hab⟩ := D.types_of_orderOf_eq_three (H.types D)
    (isConj_iff.mpr ⟨ka, rfl⟩) (isConj_iff.mpr ⟨kb, rfl⟩) haM hbM h3
  have hza := H.e34a _ (isConj_iff.mpr ⟨ka, rfl⟩) haM haQ
  have hzb := H.e34a _ (isConj_iff.mpr ⟨kb, rfl⟩) hbM hbQ
  rcases hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [D.card_Dl_of_isTInv haM haQ hza (H.Dl_ne_bot haM haQ) ha,
      D.card_Dl_of_isTInv hbM hbQ hzb (H.Dl_ne_bot hbM hbQ) hb]
  · rw [D.card_Dl_of_isUInv haM haQ hza (H.Dl_ne_bot haM haQ) ha,
      D.card_Dl_of_isUInv hbM hbQ hzb (H.Dl_ne_bot hbM hbQ) hb]

theorem exists_of_not_three (H : SixAt T) {x w y v : G} (hx : IsConj T.z x)
    (hw : IsConj T.z w) (hy : IsConj T.z y) (hv : IsConj T.z v) (hwy : Commute w y)
    (hwv : Commute w v) (hvx : Commute v x) (h3 : orderOf (v * y) ≠ 3) :
    ∃ u : G, IsConj T.z u ∧ Commute x u ∧ Commute u y := by
  by_cases hvy : Commute v y
  · exact ⟨v, hv, hvx.symm, hvy⟩
  have hvv : v * v = 1 := by
    have := S14.SmithQ.mul_self_eq_one_of_isConj T hv
    exact this
  have hyy : y * y = 1 := S14.SmithQ.mul_self_eq_one_of_isConj T hy
  have hord := (SmithGraph.threeFour_of_common T (local_of_OLocal T H.local_) hv hy hw
    hwv.symm hwy).1
  have h4 : orderOf (v * y) = 4 := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hord
    rcases hord with h | h | h | h
    · exfalso
      apply hvy
      have e : v * y = 1 := orderOf_eq_one_iff.mp h
      have hv' : v = y⁻¹ := eq_inv_of_mul_eq_one_left e
      rw [hv']
      exact Commute.inv_left (Commute.refl y)
    · exfalso
      apply hvy
      have e : (v * y) ^ 2 = 1 := by rw [← h]; exact pow_orderOf_eq_one _
      have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
      have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
      have e' : v * y = (v * y)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_two]
        exact e
      show v * y = y * v
      rw [e', mul_inv_rev, hvi, hyi]
    · exact absurd h h3
    · exact h
  have h4' : orderOf (y * v) = 4 := by
    rw [show y * v = MulAut.conj y (v * y) by rw [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact h4
  have hyv : ¬ Commute y v := fun h => hvy h.symm
  obtain ⟨u, hu, hyu, hux⟩ := four_gen' T H.local_ H.e34a H.line hy hw hv hx hwy.symm hwv hvx
    hyv h4'
  exact ⟨u, hu, hux.symm, hyu.symm⟩

theorem _root_.CFSG.LargeExtraspecial.Setting.inv_mul_conj_mem_QG (T : Setting G) {a b : G}
    (haM : a ∈ T.M) (hbM : b ∈ T.M)
    (hab : T.ρ ⟨b, hbM⟩ * T.ρ ⟨a, haM⟩ = T.ρ ⟨a, haM⟩ * T.ρ ⟨b, hbM⟩) :
    a⁻¹ * (b * a * b⁻¹) ∈ T.QG := by
  have hM : a⁻¹ * (b * a * b⁻¹) ∈ T.M :=
    T.M.mul_mem (T.M.inv_mem haM) (T.M.mul_mem (T.M.mul_mem hbM haM) (T.M.inv_mem hbM))
  have e : (⟨a⁻¹ * (b * a * b⁻¹), hM⟩ : T.M) =
      (⟨a, haM⟩ : T.M)⁻¹ * ((⟨b, hbM⟩ : T.M) * ⟨a, haM⟩ * (⟨b, hbM⟩ : T.M)⁻¹) := rfl
  refine (T.ρ_eq_one_iff ⟨_, hM⟩).mp ?_
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hab]
  group

theorem exists_fixed_conj (H : SixAt T) {θ x y₀ : G} (hθM : θ ∈ T.M) (hθ3 : θ ^ 3 = 1)
    (hxM : x ∈ T.M) (hxθ : x * θ * x⁻¹ = θ⁻¹)
    (hy₀ : IsConj T.z y₀) (hy₀M : y₀ ∈ T.M) (hy₀Q : y₀ ∉ T.QG)
    (hθy : T.ρ ⟨θ, hθM⟩ * T.ρ ⟨y₀, hy₀M⟩ = T.ρ ⟨y₀, hy₀M⟩ * T.ρ ⟨θ, hθM⟩)
    (hxy : T.ρ ⟨x, hxM⟩ * T.ρ ⟨y₀, hy₀M⟩ = T.ρ ⟨y₀, hy₀M⟩ * T.ρ ⟨x, hxM⟩)
    (hC : ∀ q ∈ T.QG, θ * q * θ⁻¹ = q → ∀ q' ∈ T.QG,
      θ * (q' * y₀ * q'⁻¹) * θ⁻¹ = q' * y₀ * q'⁻¹ → q * (q' * y₀ * q'⁻¹) * q⁻¹ = q' * y₀ * q'⁻¹) :
    ∃ q ∈ T.QG, θ * (q * y₀ * q⁻¹) * θ⁻¹ = q * y₀ * q⁻¹ ∧
      x * (q * y₀ * q⁻¹) * x⁻¹ = q * y₀ * q⁻¹ := by
  have hcls : ∀ {b : G} (hbM : b ∈ T.M),
      T.ρ ⟨b, hbM⟩ * T.ρ ⟨y₀, hy₀M⟩ = T.ρ ⟨y₀, hy₀M⟩ * T.ρ ⟨b, hbM⟩ →
        ∃ q ∈ T.QG, b * y₀ * b⁻¹ = q * y₀ * q⁻¹ := by
    intro b hbM hb
    have hmem := T.inv_mul_conj_mem_QG hy₀M hbM hb
    have hconj : IsConj T.z (b * y₀ * b⁻¹) := hy₀.trans (isConj_iff.mpr ⟨b, rfl⟩)
    obtain ⟨q, hq, e⟩ := H.e34b y₀ _ hy₀ hconj hy₀M hy₀Q hmem
    exact ⟨q⁻¹, T.QG.inv_mem hq, by rw [e, inv_inv]⟩
  exact exists_unique_fixed_of_orbit (Q := T.QG) (Setting.isPGroup_QG T) hθ3
    (fun q hq => T.conj_mem_QG hθM hq) (hcls hθM hθy) hC hxθ (fun q hq => T.conj_mem_QG hxM hq)
    (hcls hxM hxy)

theorem orderOf_ne_three_of_card_ne {S : Setting G} (hS : ∀ g : G, SixAt (S.conjBy g))
    {gw kv ky : G} (hzw : Commute S.z (gw * S.z * gw⁻¹))
    (hwy : Commute (gw * S.z * gw⁻¹) (ky * S.z * ky⁻¹))
    (hwv : Commute (gw * S.z * gw⁻¹) (kv * S.z * kv⁻¹))
    (h3 : orderOf (S.z * (ky * S.z * ky⁻¹)) = 3)
    (hne : Nat.card (S.QG ⊓ S.Qa gw : Subgroup G) ≠ Nat.card (S.Qa kv ⊓ S.Qa gw : Subgroup G)) :
    orderOf (kv * S.z * kv⁻¹ * (ky * S.z * ky⁻¹)) ≠ 3 := by
  intro h3'
  have H := hS gw
  have e1 : gw⁻¹ * (S.conjBy gw).z * gw⁻¹⁻¹ = S.z := by
    show gw⁻¹ * (gw * S.z * gw⁻¹) * gw⁻¹⁻¹ = S.z
    group
  have e2 : ∀ k : G, k * gw⁻¹ * (S.conjBy gw).z * (k * gw⁻¹)⁻¹ = k * S.z * k⁻¹ := fun k => by
    show k * gw⁻¹ * (gw * S.z * gw⁻¹) * (k * gw⁻¹)⁻¹ = k * S.z * k⁻¹
    group
  have hmem : ∀ a : G, Commute (gw * S.z * gw⁻¹) a → a ∈ (S.conjBy gw).M := fun a ha =>
    mem_centralizer_singleton_iff.mpr ha.symm.eq
  have hz : gw⁻¹ * (S.conjBy gw).z * gw⁻¹⁻¹ ∈ (S.conjBy gw).M := by
    rw [e1]
    exact hmem _ hzw.symm
  have hy : ky * gw⁻¹ * (S.conjBy gw).z * (ky * gw⁻¹)⁻¹ ∈ (S.conjBy gw).M := by
    rw [e2]
    exact hmem _ hwy
  have hv : kv * gw⁻¹ * (S.conjBy gw).z * (kv * gw⁻¹)⁻¹ ∈ (S.conjBy gw).M := by
    rw [e2]
    exact hmem _ hwv
  have c1 := H.card_eq_of_orderOf_eq_three hz hy (by rw [e1, e2]; exact h3)
  have c2 := H.card_eq_of_orderOf_eq_three hv hy (by rw [e2, e2]; exact h3')
  rw [S.Qa_conjBy, S.Qa_conjBy, inv_mul_cancel, S.Qa_one] at c1
  rw [S.Qa_conjBy, S.Qa_conjBy, inv_mul_cancel_right] at c2
  apply hne
  have c3 : Nat.card ((S.conjBy gw).QG ⊓ S.QG : Subgroup G) =
      Nat.card ((S.conjBy gw).QG ⊓ S.Qa kv : Subgroup G) := c1.trans c2.symm
  rw [inf_comm (S.QG), inf_comm (S.Qa kv)]
  exact c3

end SixAt

namespace S2Data

variable {S : Setting G} (D : S2Data S)

theorem exists_siegel (hw6 : 6 ≤ S.width) :
    ∃ c : D.Cbar, IsTypeA D.QV (D.resC c) 2 := by
  have h5 : 5 ≤ finrank (ZMod 2) (Vt S D.g D.t) := by
    rw [D.finrank_Vt]
    omega
  obtain ⟨P₁, P₂, hO, -, -⟩ := S45Q.exists_two_hypPairs D.QV_nondegenerate h5
  have hli : LinearIndependent (ZMod 2) ![P₁.e, P₂.e] := by
    rw [LinearIndependent.pair_iff]
    intro a b hab
    have h1 := congrArg (fun v => polar D.QV v P₁.f) hab
    have h2 := congrArg (fun v => polar D.QV v P₂.f) hab
    simp only [polar_add_left, polar_smul_left, polar_zero_left, smul_eq_mul] at h1 h2
    rw [polar_comm D.QV P₂.e P₁.f, hO.fe, P₁.polar_ef, mul_one, mul_zero, add_zero] at h1
    rw [hO.ef, P₂.polar_ef, mul_zero, mul_one, zero_add] at h2
    exact ⟨h1, h2⟩
  obtain ⟨c, hc⟩ := D.exists_Cbar_resC_eq_eichler P₁.e P₂.e
  refine ⟨c, ?_⟩
  rw [hc]
  exact (eichler_isTypeA D.QV_nondegenerate P₁.Q_e hO.ee hli P₂.Q_e).1

end S2Data

end CFSG.GF2Type.Smith1980Orth
