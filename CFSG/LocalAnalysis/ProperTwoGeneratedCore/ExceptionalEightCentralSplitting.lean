module

public import CFSG.GroupTheory.AbelianNormalCoprimeComplementLifting
public import CFSG.CharacterTheory.Semidihedral.Principal.DihedralCharacterFamily

public section

namespace CFSG.ProperTwoGeneratedCore.ExceptionalEight

theorem central_nonsquare_involution_dihedral_eight_sylow_quotient_splits
    {J : Type*} [Group J] [Finite J] {c : J} (hc : c ∈ Subgroup.center J)
    (hc2 : orderOf c = 2) (hsq : ∀ x : J, x ^ 2 ≠ c) [(Subgroup.zpowers c).Normal]
    (hP : ∃ P : Sylow 2 (J ⧸ Subgroup.zpowers c),
      Nonempty ((P : Subgroup (J ⧸ Subgroup.zpowers c)) ≃* DihedralGroup 4)) :
    ∃ D : Subgroup J, D.Normal ∧ (Subgroup.zpowers c).IsComplement' D ∧
      Function.Bijective (fun d : D => (QuotientGroup.mk (d : J) : J ⧸ Subgroup.zpowers c)) := by
  classical
  obtain ⟨P, ⟨e⟩⟩ := hP
  set Z := Subgroup.zpowers c with hZ
  have hmemZ : ∀ x : J, x ∈ Z → x = 1 ∨ x = c := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hmod := zpow_mod_orderOf c k
    rw [hc2] at hmod
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [← hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [← hmod, show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  have hkill : ∀ y : J, (QuotientGroup.mk y : J ⧸ Z) = 1 → (∃ w : J, w ^ 2 = y) → y = 1 := by
    intro y hy hw
    obtain ⟨w, hw⟩ := hw
    rcases hmemZ y ((QuotientGroup.eq_one_iff y).mp hy) with h | h
    · exact h
    · exact absurd (hw.trans h) (hsq w)
  let rbar : J ⧸ Z := (e.symm (DihedralGroup.r 1) : J ⧸ Z)
  let sbar : J ⧸ Z := (e.symm (DihedralGroup.sr 0) : J ⧸ Z)
  obtain ⟨r, hr⟩ := QuotientGroup.mk_surjective rbar
  obtain ⟨s, hs⟩ := QuotientGroup.mk_surjective sbar
  have hcoe : ∀ x y : DihedralGroup 4,
      ((e.symm x : J ⧸ Z) * (e.symm y : J ⧸ Z)) = (e.symm (x * y) : J ⧸ Z) := by
    intro x y
    rw [map_mul, Subgroup.coe_mul]
  have hcoepow : ∀ (x : DihedralGroup 4) (k : ℕ),
      ((e.symm x : J ⧸ Z) ^ k) = (e.symm (x ^ k) : J ⧸ Z) := by
    intro x k
    rw [map_pow, Subgroup.coe_pow]
  have hcoeone : ((e.symm 1 : P) : J ⧸ Z) = 1 := by
    rw [map_one, Subgroup.coe_one]
  have hr4 : r ^ 4 = 1 := by
    refine hkill _ ?_ ⟨r ^ 2, by rw [← pow_mul]⟩
    rw [QuotientGroup.mk_pow, hr, hcoepow, DihedralGroup.r_one_pow]
    exact hcoeone
  have hss : s * s = 1 := by
    refine hkill _ ?_ ⟨s, pow_two s⟩
    rw [QuotientGroup.mk_mul, hs, hcoe, DihedralGroup.sr_mul_sr]
    exact hcoeone
  have hsrsr : s * r * (s * r) = 1 := by
    refine hkill _ ?_ ⟨s * r, pow_two _⟩
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hr, hs, hcoe, hcoe,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    exact hcoeone
  have hrel : s * r * s = r⁻¹ := by
    rw [← mul_assoc] at hsrsr
    exact eq_inv_of_mul_eq_one_left hsrsr
  let φ := CFSG.Semidihedral.Principal.dihedralWordHom r s 4 hr4 hss hrel
  have hcomp : ∀ x : DihedralGroup 4,
      (QuotientGroup.mk (φ x) : J ⧸ Z) = (e.symm x : J ⧸ Z) := by
    intro x
    cases x with
    | r i =>
      change (QuotientGroup.mk (r ^ i.val) : J ⧸ Z) = _
      rw [QuotientGroup.mk_pow, hr, hcoepow, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    | sr i =>
      change (QuotientGroup.mk (s * r ^ i.val) : J ⧸ Z) = _
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_pow, hr, hs, hcoepow, hcoe,
        DihedralGroup.r_one_pow, ZMod.natCast_zmod_val, DihedralGroup.sr_mul_r, zero_add]
  have hφinj : Function.Injective φ := by
    intro x y hxy
    apply e.symm.injective
    apply Subtype.ext
    rw [← hcomp, ← hcomp, hxy]
  set K := φ.range with hK
  have hZK : Z ⊓ K = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgZ, x, rfl⟩
    have h1 : (e.symm x : J ⧸ Z) = 1 := by
      rw [← hcomp]
      exact (QuotientGroup.eq_one_iff _).mpr hgZ
    have hx : x = 1 := by
      apply e.symm.injective
      rw [map_one]
      exact Subtype.ext h1
    rw [Subgroup.mem_bot, hx, map_one]
  have hmapK : K.map (QuotientGroup.mk' Z) = (P : Subgroup (J ⧸ Z)) := by
    ext q
    constructor
    · rintro ⟨g, ⟨x, rfl⟩, rfl⟩
      change (QuotientGroup.mk (φ x) : J ⧸ Z) ∈ (P : Subgroup (J ⧸ Z))
      rw [hcomp]
      exact (e.symm x).2
    · intro hq
      refine ⟨φ (e ⟨q, hq⟩), ⟨_, rfl⟩, ?_⟩
      change (QuotientGroup.mk (φ (e ⟨q, hq⟩)) : J ⧸ Z) = q
      rw [hcomp, MulEquiv.symm_apply_apply]
  have hQ : Z ⊔ K = (P : Subgroup (J ⧸ Z)).comap (QuotientGroup.mk' Z) := by
    rw [← hmapK, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]
  have hQindex : (Z ⊔ K).index = (P : Subgroup (J ⧸ Z)).index := by
    rw [hQ, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective Z)]
  have hodd : ¬ 2 ∣ (Z ⊔ K).index := hQindex ▸ P.not_dvd_index
  have hZcard : Nat.card Z = 2 := by rw [Nat.card_zpowers, hc2]
  have hcop : Nat.Coprime (Z ⊔ K).index (Nat.card Z) := by
    rw [hZcard, Nat.coprime_two_right]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd)
  obtain ⟨D, hD, hZD, hZD'⟩ :=
    CFSG.GroupTheory.abelian_normal_coprime_index_complement_lifting Z (Z ⊔ K) K hcop hZK rfl
  have hZcenter : Z ≤ Subgroup.center J := Subgroup.zpowers_le.mpr hc
  have hdecomp : ∀ g : J, ∃ z ∈ Z, ∃ d ∈ D, z * d = g := by
    intro g
    have hg : g ∈ Z ⊔ D := by rw [hZD']; exact Subgroup.mem_top g
    exact Subgroup.mem_sup_of_normal_left.mp hg
  refine ⟨D, ⟨fun n hn g => ?_⟩, hD, ⟨?_, ?_⟩⟩
  · obtain ⟨z, hz, d, hd, rfl⟩ := hdecomp g
    have hzc := Subgroup.mem_center_iff.mp (hZcenter hz)
    have heq : z * d * n * (z * d)⁻¹ = d * n * d⁻¹ := by
      rw [mul_inv_rev, show z * d * n * (d⁻¹ * z⁻¹) = z * (d * n * d⁻¹) * z⁻¹ by group,
        ← hzc (d * n * d⁻¹), mul_inv_cancel_right]
    rw [heq]
    exact D.mul_mem (D.mul_mem hd hn) (D.inv_mem hd)
  · intro d₁ d₂ h
    have hmem : (d₁ : J)⁻¹ * d₂ ∈ Z := QuotientGroup.eq.mp h
    have hmemD : (d₁ : J)⁻¹ * d₂ ∈ D := D.mul_mem (D.inv_mem d₁.2) d₂.2
    have hone : (d₁ : J)⁻¹ * d₂ ∈ Z ⊓ D := ⟨hmem, hmemD⟩
    rw [hZD, Subgroup.mem_bot] at hone
    exact Subtype.ext (inv_mul_eq_one.mp hone)
  · intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hz, d, hd, rfl⟩ := hdecomp g
    refine ⟨⟨d, hd⟩, ?_⟩
    change (QuotientGroup.mk d : J ⧸ Z) = QuotientGroup.mk (z * d)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z).mpr hz, one_mul]

end CFSG.ProperTwoGeneratedCore.ExceptionalEight
