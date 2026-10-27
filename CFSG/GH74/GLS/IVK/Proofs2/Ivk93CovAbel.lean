module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93CovCfg

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open Equiv

@[expose] def ivk93cov_r6 : Perm (Fin 6) := (swap 0 1 * swap 1 2 * swap 2 3) * swap 4 5

@[expose] def ivk93cov_s6 : Perm (Fin 6) := swap 0 2 * swap 4 5

theorem ivk93cov_r6_pow4 : ivk93cov_r6 ^ 4 = 1 := by decide
theorem ivk93cov_r6_sq : ivk93cov_r6 ^ 2 ≠ 1 := by decide
theorem ivk93cov_s6_sq : ivk93cov_s6 * ivk93cov_s6 = 1 := by decide
theorem ivk93cov_s6_ne_one : ivk93cov_s6 ≠ 1 := by decide
theorem ivk93cov_s6_conj : ivk93cov_s6 * ivk93cov_r6 * ivk93cov_s6⁻¹ = ivk93cov_r6⁻¹ := by decide
theorem ivk93cov_sr_ne : ivk93cov_s6 * ivk93cov_r6 ≠ ivk93cov_r6 * ivk93cov_s6 := by decide
theorem ivk93cov_r6_sign : Perm.sign ivk93cov_r6 = 1 := by
  simp [ivk93cov_r6, Perm.sign_mul]
theorem ivk93cov_s6_sign : Perm.sign ivk93cov_s6 = 1 := by
  simp [ivk93cov_s6, Perm.sign_mul]

theorem ivk93cov_alt_nonabelian_two {n : ℕ} (hn : 6 ≤ n) :
    ∃ Q : Subgroup (alternatingGroup (Fin n)), IsPGroup 2 ↥Q ∧
      ∃ a ∈ Q, ∃ b ∈ Q, a * b ≠ b * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : Fin 6 ≃ {x : Fin n // x.val < 6} :=
    { toFun := fun i => ⟨⟨i.val, by omega⟩, i.isLt⟩
      invFun := fun x => ⟨x.1.val, x.2⟩
      left_inv := fun i => rfl
      right_inv := fun x => rfl }
  let ι : Perm (Fin 6) →* Perm (Fin n) := Equiv.Perm.extendDomainHom e
  have hι : Function.Injective ι := Equiv.Perm.extendDomainHom_injective e
  have hsign : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 → ι σ ∈ alternatingGroup (Fin n) := by
    intro σ hσ
    rw [Equiv.Perm.mem_alternatingGroup]
    have := Equiv.Perm.sign_extendDomain σ e
    exact this.trans hσ
  let r : alternatingGroup (Fin n) := ⟨ι ivk93cov_r6, hsign _ ivk93cov_r6_sign⟩
  let s : alternatingGroup (Fin n) := ⟨ι ivk93cov_s6, hsign _ ivk93cov_s6_sign⟩
  have hr4 : r ^ 4 = 1 := Subtype.ext (by
    show (ι ivk93cov_r6) ^ 4 = 1
    rw [← map_pow, ivk93cov_r6_pow4, map_one])
  have hr2 : r ^ 2 ≠ 1 := fun h => ivk93cov_r6_sq (hι (by
    have := congrArg Subtype.val h
    simpa [r, ← map_pow] using this))
  have hss : s * s = 1 := Subtype.ext (by
    show ι ivk93cov_s6 * ι ivk93cov_s6 = 1
    rw [← map_mul, ivk93cov_s6_sq, map_one])
  have hs1 : s ≠ 1 := fun h => ivk93cov_s6_ne_one (hι (by
    have := congrArg Subtype.val h
    simpa [s] using this))
  have hsr : s * r * s⁻¹ = r⁻¹ := Subtype.ext (by
    show ι ivk93cov_s6 * ι ivk93cov_r6 * (ι ivk93cov_s6)⁻¹ = (ι ivk93cov_r6)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul, ivk93cov_s6_conj, map_inv])
  have hnc : s * r ≠ r * s := fun h => ivk93cov_sr_ne (hι (by
    have := congrArg Subtype.val h
    simpa [r, s] using this))
  have hordr : orderOf r = 2 ^ 2 := orderOf_eq_prime_pow (by simpa using hr2) (by simpa using hr4)
  have hords : orderOf s = 2 := orderOf_eq_prime (by rw [pow_two]; exact hss) hs1
  have hPr : IsPGroup 2 ↥(zpowers r) := IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hordr])
  have hPs : IsPGroup 2 ↥(zpowers s) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hords]; norm_num)
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hnorm : s ∈ Subgroup.normalizer (zpowers r) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have key : ∀ k : ℤ, s * r ^ k * s⁻¹ = r ^ (-k) := by
      intro k
      rw [← conj_zpow, hsr, inv_zpow, zpow_neg]
    constructor
    · intro hh
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
      rw [key]
      exact Subgroup.zpow_mem_zpowers _ _
    · intro hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
      have : h = r ^ (-k) := by
        calc h = s⁻¹ * (s * h * s⁻¹) * s := by group
          _ = s⁻¹ * r ^ k * s := by rw [hk]
          _ = s * r ^ k * s⁻¹ := by rw [hsi]
          _ = r ^ (-k) := key k
      rw [this]
      exact Subgroup.zpow_mem_zpowers _ _
  refine ⟨zpowers s ⊔ zpowers r, hPs.to_sup_of_normal_right' hPr (Subgroup.zpowers_le.2 hnorm),
    s, Subgroup.mem_sup_left (Subgroup.mem_zpowers s), r,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers r), hnc⟩

theorem ivk93cov_exists_lift_pgroup {Y Q : Type} [Group Y] [Finite Y] [Group Q] (π : Y →* Q)
    (hπ : Function.Surjective π) {R : Subgroup Q} (hR : IsPGroup 2 ↥R) :
    ∃ P : Subgroup Y, IsPGroup 2 ↥P ∧ P.map π = R := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Y₁ : Subgroup Y := R.comap π
  let π₁ : ↥Y₁ →* ↥R := (π.comp Y₁.subtype).codRestrict R (fun y => y.2)
  have hπ₁ : Function.Surjective π₁ := by
    intro r
    obtain ⟨y, hy⟩ := hπ (r : Q)
    exact ⟨⟨y, by show π y ∈ R; rw [hy]; exact r.2⟩, Subtype.ext hy⟩
  obtain ⟨P₁⟩ : Nonempty (Sylow 2 ↥Y₁) := inferInstance
  have hRtop : IsPGroup 2 ↥(⊤ : Subgroup ↥R) := hR.of_equiv Subgroup.topEquiv.symm
  have hmap : (P₁ : Subgroup ↥Y₁).map π₁ = ⊤ := by
    have := (P₁.mapSurjective hπ₁).is_maximal' hRtop le_top
    rw [Sylow.coe_mapSurjective] at this
    exact this.symm
  refine ⟨(P₁ : Subgroup ↥Y₁).map Y₁.subtype, P₁.isPGroup'.map Y₁.subtype, ?_⟩
  have h1 : ((P₁ : Subgroup ↥Y₁).map π₁).map R.subtype = ((P₁ : Subgroup ↥Y₁).map Y₁.subtype).map π := by
    rw [Subgroup.map_map, Subgroup.map_map]
    rfl
  rw [← h1, hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

namespace Ivk93Cov

variable {J : Type} [Group J] [Finite J] {x : J} {n : ℕ} {B : Subgroup J}

theorem exists_nonabelian_two (h : Ivk93Cov x n B) :
    ∃ P : Subgroup J, P ≤ B ∧ IsPGroup 2 ↥P ∧ ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a := by
  obtain ⟨-, -, ⟨e⟩⟩ := h.cover
  let π : ↥B →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' (center (↥B ⧸ pPrimeCore 2 ↥B))).comp
      (QuotientGroup.mk' (pPrimeCore 2 ↥B)))
  have hπ : Function.Surjective π :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  obtain ⟨Q, hQ, a, ha, b, hb, hab⟩ := ivk93cov_alt_nonabelian_two (n := n) (by have := h.eight; omega)
  obtain ⟨P, hP, hPQ⟩ := ivk93cov_exists_lift_pgroup π hπ hQ
  have ha' : a ∈ P.map π := by rw [hPQ]; exact ha
  have hb' : b ∈ P.map π := by rw [hPQ]; exact hb
  obtain ⟨a', ha'P, rfl⟩ := ha'
  obtain ⟨b', hb'P, rfl⟩ := hb'
  refine ⟨P.map B.subtype, Subgroup.map_subtype_le P, hP.map B.subtype, (a' : J),
    ⟨a', ha'P, rfl⟩, (b' : J), ⟨b', hb'P, rfl⟩, fun hc => hab ?_⟩
  have : a' * b' = b' * a' := Subtype.ext hc
  rw [← map_mul, ← map_mul, this]

theorem false_of_abelian_sylow (h : Ivk93Cov x n B) (hab : CFSG.Walter.HasAbelianSylowTwo J) :
    False := by
  obtain ⟨H, -, hH2, a, ha, b, hb, hab'⟩ := h.exists_nonabelian_two
  obtain ⟨P, hP⟩ := hH2.exists_le_sylow
  apply hab'
  have hc := (hab P).is_comm.comm
  exact hc ⟨a, hP ha⟩ ⟨b, hP hb⟩ |> congrArg Subtype.val

end Ivk93Cov

end CFSG.GH74.GLS.IVK.Proofs2
