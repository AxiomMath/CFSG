module

public import CFSG.LargeExtraspecial.AS62C36Rigid
public import CFSG.LargeExtraspecial.AS62C36Am
public import CFSG.LargeExtraspecial.AS62C36Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.U42

namespace AS62

variable {G : Type} [Group G] [Finite G] {S : Setting G} {H : Subgroup G}

namespace ConfHyp

theorem eq_one_of_commute_sup (hc : ConfHyp S H) {M₀ : Subgroup G} (hB : S.M ⊓ H ≤ M₀) {c : G}
    (h1 : ∀ m ∈ M₀, c * m = m * c) (h2 : ∀ h ∈ H, c * h = h * c) : c = 1 := by
  obtain ⟨g⟩ := hc.exists_gens
  have hQ : ∀ q ∈ S.QG, c * q = q * c := fun q hq => h1 q (hB ⟨S.QG_le_M hq, hc.QG_le hq⟩)
  have hcM : c ∈ S.M := S.mem_M_iff.mpr (hQ S.z S.z_mem_QG)
  rcases S.eq_one_or_z_of_commute (S.mem_QG_of_commute hcM hQ) hQ with h | h
  · exact h
  · refine absurd (S.mem_M_iff.mpr ?_) g.s_not_mem_M
    have h3 := h2 g.s (g.mem_H g.rep_s)
    rw [h] at h3
    exact h3.symm

section Acts

omit [Finite G]

private theorem mem_normalizer_of_relIndex_eq_two {K L : Subgroup G} (hKL : K ≤ L)
    (h : K.relIndex L = 2) {τ : G} (hτ : τ ∈ L) : τ ∈ normalizer (K : Set G) := by
  have hn : (K.subgroupOf L).Normal := Subgroup.normal_of_index_eq_two h
  have key : ∀ {σ : G}, σ ∈ L → ∀ k ∈ K, σ * k * σ⁻¹ ∈ K := fun {σ} hσ k hk =>
    mem_subgroupOf.mp (hn.conj_mem ⟨k, hKL hk⟩ (mem_subgroupOf.mpr hk) ⟨σ, hσ⟩)
  refine mem_normalizer_iff.mpr fun k => ⟨key hτ k, fun hk => ?_⟩
  have h1 := key (L.inv_mem hτ) _ hk
  rwa [show τ⁻¹ * (τ * k * τ⁻¹) * τ⁻¹⁻¹ = k by group] at h1

private theorem exists_mulEquiv_conj (K : Subgroup G) (τ : G) (h1 : ∀ k ∈ K, τ * k * τ⁻¹ ∈ K)
    (h2 : ∀ k ∈ K, τ⁻¹ * k * τ ∈ K) :
    ∃ c : K ≃* K, ∀ k : K, ((c k : K) : G) = τ * (k : G) * τ⁻¹ :=
  ⟨{ toFun := fun k => ⟨τ * k * τ⁻¹, h1 k k.2⟩
     invFun := fun k => ⟨τ⁻¹ * k * τ, h2 k k.2⟩
     left_inv := fun k => Subtype.ext (by simp [mul_assoc])
     right_inv := fun k => Subtype.ext (by simp [mul_assoc])
     map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun _ => rfl⟩

variable {M₀ : Subgroup G}
  (φ : (RankTwoAmalgam.ofSubgroups M₀ H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2))

private abbrev ActsAs (τ : G) (f : U42Aut.Ah) : Prop :=
  (∀ (m : G) (hm : m ∈ M₀) (hm' : τ * m * τ⁻¹ ∈ M₀),
    ((amPhi1 φ ⟨τ * m * τ⁻¹, hm'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
      (f : Equiv.Perm (Fin 45)) * ((amPhi1 φ ⟨m, hm⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
        (f : Equiv.Perm (Fin 45))⁻¹) ∧
  (∀ (h : G) (hh : h ∈ H) (hh' : τ * h * τ⁻¹ ∈ H),
    ((amPhi2 φ ⟨τ * h * τ⁻¹, hh'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
      (f : Equiv.Perm (Fin 45)) * ((amPhi2 φ ⟨h, hh⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
        (f : Equiv.Perm (Fin 45))⁻¹)

private theorem actsAs_one : ActsAs φ 1 1 := by
  refine ⟨fun m hm hm' => ?_, fun h hh hh' => ?_⟩
  · have e : (⟨1 * m * 1⁻¹, hm'⟩ : M₀) = ⟨m, hm⟩ := Subtype.ext (by simp)
    rw [e]
    simp
  · have e : (⟨1 * h * 1⁻¹, hh'⟩ : H) = ⟨h, hh⟩ := Subtype.ext (by simp)
    rw [e]
    simp

private theorem actsAs_mul {τ τ' : G} {g g' : U42Aut.Ah}
    (hτ' : τ' ∈ normalizer (M₀ : Set G) ⊓ normalizer (H : Set G))
    (h1 : ActsAs φ τ g) (h2 : ActsAs φ τ' g') : ActsAs φ (τ * τ') (g * g') := by
  refine ⟨fun m hm hm' => ?_, fun h hh hh' => ?_⟩
  · have hm1 : τ' * m * τ'⁻¹ ∈ M₀ := (mem_normalizer_iff.mp hτ'.1 m).mp hm
    have hm2 : τ * (τ' * m * τ'⁻¹) * τ⁻¹ ∈ M₀ := by
      rwa [show τ * (τ' * m * τ'⁻¹) * τ⁻¹ = τ * τ' * m * (τ * τ')⁻¹ by group]
    have e : (⟨τ * τ' * m * (τ * τ')⁻¹, hm'⟩ : M₀) = ⟨τ * (τ' * m * τ'⁻¹) * τ⁻¹, hm2⟩ :=
      Subtype.ext (by group)
    rw [e, h1.1 _ hm1 hm2, h2.1 m hm hm1]
    simp [mul_assoc]
  · have hh1 : τ' * h * τ'⁻¹ ∈ H := (mem_normalizer_iff.mp hτ'.2 h).mp hh
    have hh2 : τ * (τ' * h * τ'⁻¹) * τ⁻¹ ∈ H := by
      rwa [show τ * (τ' * h * τ'⁻¹) * τ⁻¹ = τ * τ' * h * (τ * τ')⁻¹ by group]
    have e : (⟨τ * τ' * h * (τ * τ')⁻¹, hh'⟩ : H) = ⟨τ * (τ' * h * τ'⁻¹) * τ⁻¹, hh2⟩ :=
      Subtype.ext (by group)
    rw [e, h1.2 _ hh1 hh2, h2.2 h hh hh1]
    simp [mul_assoc]

private theorem phi_agree (x : ↥(M₀ ⊓ H)) :
    ((amPhi1 φ ⟨x, x.2.1⟩ : U42.P1) : U42.Y) = ((amPhi2 φ ⟨x, x.2.2⟩ : U42.P2) : U42.Y) :=
  (congrArg Subtype.val (φ.comm1 x)).symm.trans (congrArg Subtype.val (φ.comm2 x))

private theorem exists_actsAs_incl {b : U42.Y} (hb : b ∈ U42.P1 ⊓ U42.P2) :
    ∃ x ∈ M₀ ⊓ H, ActsAs φ x (U42Aut.incl b) := by
  obtain ⟨x, hx⟩ : ∃ x : ↥(M₀ ⊓ H), φ.φ12 x = (⟨b, hb⟩ : ↥(U42.P1 ⊓ U42.P2)) :=
    φ.φ12.surjective _
  have c1 : amPhi1 φ ⟨x, x.2.1⟩ = ⟨b, hb.1⟩ := by
    have h3 := (φ.comm1 x).symm
    rw [hx] at h3
    exact h3
  have c2 : amPhi2 φ ⟨x, x.2.2⟩ = ⟨b, hb.2⟩ := by
    have h3 := (φ.comm2 x).symm
    rw [hx] at h3
    exact h3
  refine ⟨x, x.2, fun m hm hm' => ?_, fun h hh hh' => ?_⟩
  · have e : (⟨(x : G) * m * (x : G)⁻¹, hm'⟩ : M₀) = ⟨x, x.2.1⟩ * ⟨m, hm⟩ * ⟨x, x.2.1⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, c1]
    simp [mul_assoc, U42Aut.coe_incl]
  · have e : (⟨(x : G) * h * (x : G)⁻¹, hh'⟩ : H) = ⟨x, x.2.2⟩ * ⟨h, hh⟩ * ⟨x, x.2.2⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, c2]
    simp [mul_assoc, U42Aut.coe_incl]

private theorem exists_actsAs_Bh
    {τ : G} (hτ : τ ∈ normalizer (M₀ : Set G) ⊓ normalizer (H : Set G)) :
    ∃ g : U42Aut.Ah, g ∈ U42Aut.Bh ∧ ActsAs φ τ g := by
  have hM : ∀ m ∈ M₀, τ * m * τ⁻¹ ∈ M₀ := fun m hm => (mem_normalizer_iff.mp hτ.1 m).mp hm
  have hH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H := fun h hh => (mem_normalizer_iff.mp hτ.2 h).mp hh
  have hM' : ∀ m ∈ M₀, τ⁻¹ * m * τ ∈ M₀ := fun m hm => by
    simpa using (mem_normalizer_iff.mp (inv_mem hτ).1 m).mp hm
  have hH' : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H := fun h hh => by
    simpa using (mem_normalizer_iff.mp (inv_mem hτ).2 h).mp hh
  obtain ⟨cM, hcM⟩ := exists_mulEquiv_conj M₀ τ hM hM'
  obtain ⟨cH, hcH⟩ := exists_mulEquiv_conj H τ hH hH'
  obtain ⟨α₁, hα₁⟩ : ∃ α : U42.P1 ≃* U42.P1, ∀ (m : G) (hm : m ∈ M₀) (hm' : τ * m * τ⁻¹ ∈ M₀),
      α (amPhi1 φ ⟨m, hm⟩) = amPhi1 φ ⟨τ * m * τ⁻¹, hm'⟩ :=
    ⟨(amPhi1 φ).symm.trans (cM.trans (amPhi1 φ)), fun m hm hm' => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg (amPhi1 φ) (Subtype.ext (hcM _))⟩
  obtain ⟨α₂, hα₂⟩ : ∃ α : U42.P2 ≃* U42.P2, ∀ (h : G) (hh : h ∈ H) (hh' : τ * h * τ⁻¹ ∈ H),
      α (amPhi2 φ ⟨h, hh⟩) = amPhi2 φ ⟨τ * h * τ⁻¹, hh'⟩ :=
    ⟨(amPhi2 φ).symm.trans (cH.trans (amPhi2 φ)), fun h hh hh' => by
      rw [MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
      exact congrArg (amPhi2 φ) (Subtype.ext (hcH _))⟩
  obtain ⟨g, hgB, hg1, hg2⟩ := amalgamAut_eq_conj α₁ α₂ fun b h1 h2 => by
    obtain ⟨x, hx⟩ : ∃ x : ↥(M₀ ⊓ H), φ.φ12 x = (⟨b, h1, h2⟩ : ↥(U42.P1 ⊓ U42.P2)) :=
      φ.φ12.surjective _
    have c1 : amPhi1 φ ⟨x, x.2.1⟩ = ⟨b, h1⟩ := by
      have h3 := (φ.comm1 x).symm
      rw [hx] at h3
      exact h3
    have c2 : amPhi2 φ ⟨x, x.2.2⟩ = ⟨b, h2⟩ := by
      have h3 := (φ.comm2 x).symm
      rw [hx] at h3
      exact h3
    have hx' : τ * x * τ⁻¹ ∈ M₀ ⊓ H := ⟨hM x x.2.1, hH x x.2.2⟩
    rw [← c1, ← c2, hα₁ x x.2.1 (hM x x.2.1), hα₂ x x.2.2 (hH x x.2.2)]
    exact congrArg Subtype.val (phi_agree φ ⟨τ * x * τ⁻¹, hx'⟩)
  refine ⟨g, hgB, fun m hm hm' => ?_, fun h hh hh' => ?_⟩
  · have h3 := hg1 (amPhi1 φ ⟨m, hm⟩)
    rwa [hα₁ m hm hm'] at h3
  · have h3 := hg2 (amPhi2 φ ⟨h, hh⟩)
    rwa [hα₂ h hh hh'] at h3

end Acts

private theorem eq_of_actsAs (hc : ConfHyp S H) {M₀ : Subgroup G} (hB : S.M ⊓ H ≤ M₀)
    {φ : (RankTwoAmalgam.ofSubgroups M₀ H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2)}
    {τ τ' : G} {g : U42Aut.Ah}
    (hτ : τ ∈ normalizer (M₀ : Set G) ⊓ normalizer (H : Set G))
    (hτ' : τ' ∈ normalizer (M₀ : Set G) ⊓ normalizer (H : Set G))
    (h1 : ActsAs φ τ g) (h2 : ActsAs φ τ' g) : τ = τ' := by
  have key : τ'⁻¹ * τ = 1 := by
    refine hc.eq_one_of_commute_sup hB (fun m hm => ?_) (fun h hh => ?_)
    · have hm1 : τ * m * τ⁻¹ ∈ M₀ := (mem_normalizer_iff.mp hτ.1 m).mp hm
      have hm2 : τ' * m * τ'⁻¹ ∈ M₀ := (mem_normalizer_iff.mp hτ'.1 m).mp hm
      have e : τ * m * τ⁻¹ = τ' * m * τ'⁻¹ := by
        have h3 := (h1.1 m hm hm1).trans (h2.1 m hm hm2).symm
        exact congrArg Subtype.val ((amPhi1 φ).injective (Subtype.ext (Subtype.ext h3)))
      calc τ'⁻¹ * τ * m = τ'⁻¹ * (τ * m * τ⁻¹) * τ := by group
        _ = τ'⁻¹ * (τ' * m * τ'⁻¹) * τ := by rw [e]
        _ = m * (τ'⁻¹ * τ) := by group
    · have hh1 : τ * h * τ⁻¹ ∈ H := (mem_normalizer_iff.mp hτ.2 h).mp hh
      have hh2 : τ' * h * τ'⁻¹ ∈ H := (mem_normalizer_iff.mp hτ'.2 h).mp hh
      have e : τ * h * τ⁻¹ = τ' * h * τ'⁻¹ := by
        have h3 := (h1.2 h hh hh1).trans (h2.2 h hh hh2).symm
        exact congrArg Subtype.val ((amPhi2 φ).injective (Subtype.ext (Subtype.ext h3)))
      calc τ'⁻¹ * τ * h = τ'⁻¹ * (τ * h * τ⁻¹) * τ := by group
        _ = τ'⁻¹ * (τ' * h * τ'⁻¹) * τ := by rw [e]
        _ = h * (τ'⁻¹ * τ) := by group
  exact (inv_mul_eq_one.mp key).symm

theorem tauMatch
    (hc : ConfHyp S H) (h36 : Nat.card S.Mbar = 36)
    (h384 : Nat.card ↥(S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = 384)
    (h1920 : Nat.card (normalizer ((closure (S.zConj H) : Subgroup G) : Set G)) = 1920)
    (M₀ : Subgroup G) (hM₀ : M₀ ≤ S.M) (hB : S.M ⊓ H ≤ M₀) (hidx : M₀.relIndex S.M = 2)
    (φ : (RankTwoAmalgam.ofSubgroups M₀ H).Iso (RankTwoAmalgam.ofSubgroups U42.P1 U42.P2)) :
    ∃ τ : G, τ ∈ S.M ⊓ normalizer ((closure (S.zConj H) : Subgroup G) : Set G) ∧ τ ∉ M₀ ∧
      τ * τ = 1 ∧ τ ∈ normalizer (M₀ : Set G) ∧ τ ∈ normalizer (H : Set G) ∧
      ∃ f : U42Aut.Ah, f ∈ U42Aut.Bh ∧ f ∉ U42Aut.Yh ∧ f * f = 1 ∧
        (∀ (m : G) (hm : m ∈ M₀) (hm' : τ * m * τ⁻¹ ∈ M₀),
          ((amPhi1 φ ⟨τ * m * τ⁻¹, hm'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
            (f : Equiv.Perm (Fin 45)) * ((amPhi1 φ ⟨m, hm⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
              (f : Equiv.Perm (Fin 45))⁻¹) ∧
        (∀ (h : G) (hh : h ∈ H) (hh' : τ * h * τ⁻¹ ∈ H),
          ((amPhi2 φ ⟨τ * h * τ⁻¹, hh'⟩ : U42.Y) : Equiv.Perm (Fin 45)) =
            (f : Equiv.Perm (Fin 45)) * ((amPhi2 φ ⟨h, hh⟩ : U42.Y) : Equiv.Perm (Fin 45)) *
              (f : Equiv.Perm (Fin 45))⁻¹) := by
  set N := normalizer ((closure (S.zConj H) : Subgroup G) : Set G)
  have hHN : H ≤ N := hc.le_normalizer_V
  have hM1152 : Nat.card S.M = 1152 := by
    rw [card_M_eq_card_QG_mul S, hc.card_QG, h36]
  have hM₀card : Nat.card M₀ = 576 := by
    have h := Setting.card_eq_relIndex_mul S.M M₀
    rw [hidx, inf_eq_right.mpr hM₀, hM1152] at h
    omega
  have hHidx : H.relIndex N = 2 := by
    have h := Setting.card_eq_relIndex_mul N H
    rw [inf_eq_right.mpr hHN, h1920, hc.card_H] at h
    omega
  have hle : S.M ⊓ N ≤ normalizer (M₀ : Set G) ⊓ normalizer (H : Set G) := fun τ hτ =>
    ⟨mem_normalizer_of_relIndex_eq_two hM₀ hidx hτ.1,
      mem_normalizer_of_relIndex_eq_two hHN hHidx hτ.2⟩
  have hinf : M₀ ⊓ H ≤ S.M ⊓ N := fun x hx => ⟨hM₀ hx.1, hHN hx.2⟩
  obtain ⟨τ₀, hτ₀, hτ₀M₀⟩ : ∃ τ₀ ∈ S.M ⊓ N, τ₀ ∉ M₀ := by
    by_contra hcon
    have hdvd := Subgroup.card_dvd_of_le (show S.M ⊓ N ≤ M₀ from fun x hx =>
      not_not.mp fun hx' => hcon ⟨x, hx, hx'⟩)
    rw [h384, hM₀card] at hdvd
    omega
  obtain ⟨g₀, hg₀B, hg₀⟩ := exists_actsAs_Bh φ (hle hτ₀)
  have hg₀Y : g₀ ∉ U42Aut.Yh := by
    intro hY
    obtain ⟨b', hb'⟩ := (U42Aut.mem_Yh_iff_incl g₀).mp hY
    have hb'B : b' ∈ U42.P1 ⊓ U42.P2 := by
      have h3 : b' ∈ U42Aut.Bh.comap U42Aut.incl := by
        rw [Subgroup.mem_comap, hb']
        exact hg₀B
      rw [U42Aut.comap_Bh] at h3
      exact h3
    obtain ⟨x, hx, hxa⟩ := exists_actsAs_incl φ hb'B
    rw [hb'] at hxa
    exact hτ₀M₀ ((eq_of_actsAs hc hB (hle hτ₀) (hle (hinf hx)) hg₀ hxa) ▸ hx.1)
  have hY : g₀⁻¹ * U42Aut.fhatA ∈ U42Aut.Yh := by
    rw [← U42Aut.signA_eq_one_iff, map_mul, map_inv,
      (U42Aut.signA_eq_neg_one_iff g₀).mpr hg₀Y, U42Aut.signA_fhatA]
    decide
  obtain ⟨b₀, hb₀⟩ := (U42Aut.mem_Yh_iff_incl _).mp hY
  have hb₀B : b₀ ∈ U42.P1 ⊓ U42.P2 := by
    have h3 : b₀ ∈ U42Aut.Bh.comap U42Aut.incl := by
      rw [Subgroup.mem_comap, hb₀]
      exact U42Aut.Bh.mul_mem (U42Aut.Bh.inv_mem hg₀B) U42Aut.fhatA_mem_Bh
    rw [U42Aut.comap_Bh] at h3
    exact h3
  obtain ⟨x₀, hx₀, hx₀a⟩ := exists_actsAs_incl φ hb₀B
  rw [hb₀] at hx₀a
  have hτN : τ₀ * x₀ ∈ S.M ⊓ N := (S.M ⊓ N).mul_mem hτ₀ (hinf hx₀)
  have hτM₀ : τ₀ * x₀ ∉ M₀ := fun h => hτ₀M₀ (by
    simpa using M₀.mul_mem h (M₀.inv_mem hx₀.1))
  have hτa : ActsAs φ (τ₀ * x₀) U42Aut.fhatA := by
    have h3 := actsAs_mul φ (hle (hinf hx₀)) hg₀ hx₀a
    rwa [mul_inv_cancel_left] at h3
  have hf2 : U42Aut.fhatA * U42Aut.fhatA = 1 := by
    rw [← pow_two]
    exact U42Aut.fhatA_sq
  have hτ2 : (τ₀ * x₀) * (τ₀ * x₀) = 1 := by
    have h3 := actsAs_mul φ (hle hτN) hτa hτa
    rw [hf2] at h3
    exact eq_of_actsAs hc hB (mul_mem (hle hτN) (hle hτN)) (one_mem _) h3 (actsAs_one φ)
  exact ⟨τ₀ * x₀, hτN, hτM₀, hτ2, (hle hτN).1, (hle hτN).2, U42Aut.fhatA,
    U42Aut.fhatA_mem_Bh, U42Aut.fhatA_not_mem_Yh, hf2, hτa.1, hτa.2⟩

end ConfHyp

end AS62

end CFSG.LargeExtraspecial
