module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.G2Three.Q8Q8

public section

namespace CFSG.OddStandard.HigherRank.G2Three.Sec2

open Subgroup CFSG.OddStandard.HigherRank.G2Three.Sec1

private lemma Q_sq_eq_one_or (x : QuaternionGroup 2) :
    x ^ 2 = 1 ∨ x ^ 2 = QuaternionGroup.a 2 := by
  revert x; decide +kernel

private lemma Q_sq_eq_one_iff (x : QuaternionGroup 2) :
    x ^ 2 = 1 ↔ x = 1 ∨ x = QuaternionGroup.a 2 := by
  revert x; decide +kernel

private lemma Q_a2_ne_one : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
  decide +kernel

private lemma Q_a2_sq : (QuaternionGroup.a 2 : QuaternionGroup 2) ^ 2 = 1 := by
  decide +kernel

private lemma Q_xa_sq : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 = QuaternionGroup.a 2 := by
  decide +kernel

private lemma Q_card : Nat.card (QuaternionGroup 2) = 8 := by
  rw [Nat.card_eq_fintype_card, QuaternionGroup.card]

private lemma Q_commute (x y : QuaternionGroup 2)
    (hx : x ^ 2 = QuaternionGroup.a 2) (hy : y ^ 2 = QuaternionGroup.a 2)
    (hxy : x * y = y * x) : y = x ∨ y = x⁻¹ := by
  revert x y; decide +kernel

private lemma sq_mem_or {G : Type*} [Group G] {H : Subgroup G} (e : ↥H ≃* QuaternionGroup 2)
    (x : G) (hx : x ∈ H) :
    x ^ 2 = 1 ∨ x ^ 2 = (e.symm (QuaternionGroup.a 2) : G) := by
  have h := Q_sq_eq_one_or (e ⟨x, hx⟩)
  rw [← map_pow] at h
  rcases h with h | h
  · left
    have h1 : (⟨x, hx⟩ : ↥H) ^ 2 = 1 := e.injective (by rw [h, map_one])
    simpa using congrArg Subtype.val h1
  · right
    have h1 : (⟨x, hx⟩ : ↥H) ^ 2 = e.symm (QuaternionGroup.a 2) :=
      e.injective (by rw [h, e.apply_symm_apply])
    simpa using congrArg Subtype.val h1

private lemma eq_one_or_inv_of_iso {G : Type*} [Group G] {H : Subgroup G}
    (e : ↥H ≃* QuaternionGroup 2) (x : G) (hx : x ∈ H) (h2 : x ^ 2 = 1) :
    x = 1 ∨ x = (e.symm (QuaternionGroup.a 2) : G) := by
  have h := Q_sq_eq_one_iff (e ⟨x, hx⟩)
  rw [← map_pow] at h
  have hx' : (⟨x, hx⟩ : ↥H) ^ 2 = 1 := Subtype.ext (by simpa using h2)
  rcases h.mp (by rw [hx', map_one]) with h1 | h1
  · left
    have : (⟨x, hx⟩ : ↥H) = 1 := e.injective (by rw [h1, map_one])
    simpa using congrArg Subtype.val this
  · right
    have : (⟨x, hx⟩ : ↥H) = e.symm (QuaternionGroup.a 2) :=
      e.injective (by rw [h1, e.apply_symm_apply])
    simpa using congrArg Subtype.val this

private lemma mem_involution_of_card_two {G : Type*} [Group G] {H U : Subgroup G}
    (hH : H ≤ U) (hcard : Nat.card ↥H = 2) (e : ↥U ≃* QuaternionGroup 2) :
    (e.symm (QuaternionGroup.a 2) : G) ∈ H := by
  obtain ⟨y, hy_ne, _⟩ := (Nat.card_eq_two_iff' (1 : ↥H)).mp hcard
  have hy2 : (y : G) ^ 2 = 1 := by
    have h : y ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥H) (x := y)
      rwa [hcard] at this
    simpa using congrArg Subtype.val h
  rcases eq_one_or_inv_of_iso e (y : G) (hH y.2) hy2 with h | h
  · exact absurd (Subtype.ext (by simpa using h)) hy_ne
  · rw [← h]; exact y.2

private lemma commute_sq_eq {G : Type*} [Group G] {W : Subgroup G}
    (e : ↥W ≃* QuaternionGroup 2) {x y w : G} (hx : x ∈ W) (hy : y ∈ W)
    (hw : w = (e.symm (QuaternionGroup.a 2) : G))
    (hx2 : x ^ 2 = w) (hy2 : y ^ 2 = w)
    (hxy : x * y = y * x) : y = x ∨ y = x⁻¹ := by
  have hx2' : x ^ 2 = (e.symm (QuaternionGroup.a 2) : G) := by rw [hx2, hw]
  have hy2' : y ^ 2 = (e.symm (QuaternionGroup.a 2) : G) := by rw [hy2, hw]
  have hx' : e ⟨x, hx⟩ ^ 2 = QuaternionGroup.a 2 := by
    rw [← map_pow]
    have h : (⟨x, hx⟩ : ↥W) ^ 2 = e.symm (QuaternionGroup.a 2) :=
      Subtype.ext (by simpa using hx2')
    rw [h, e.apply_symm_apply]
  have hy' : e ⟨y, hy⟩ ^ 2 = QuaternionGroup.a 2 := by
    rw [← map_pow]
    have h : (⟨y, hy⟩ : ↥W) ^ 2 = e.symm (QuaternionGroup.a 2) :=
      Subtype.ext (by simpa using hy2')
    rw [h, e.apply_symm_apply]
  have hxy' : e ⟨x, hx⟩ * e ⟨y, hy⟩ = e ⟨y, hy⟩ * e ⟨x, hx⟩ := by
    have hsub : (⟨x, hx⟩ : ↥W) * ⟨y, hy⟩ = ⟨y, hy⟩ * ⟨x, hx⟩ := by
      ext
      simpa using hxy
    calc e ⟨x, hx⟩ * e ⟨y, hy⟩ = e ((⟨x, hx⟩ : ↥W) * ⟨y, hy⟩) := (map_mul e _ _).symm
      _ = e (⟨y, hy⟩ * (⟨x, hx⟩ : ↥W)) := by rw [hsub]
      _ = e ⟨y, hy⟩ * e ⟨x, hx⟩ := map_mul e _ _
  rcases Q_commute (e ⟨x, hx⟩) (e ⟨y, hy⟩) hx' hy' hxy' with h | h
  · left
    have : (⟨y, hy⟩ : ↥W) = ⟨x, hx⟩ := e.injective h
    simpa using congrArg Subtype.val this
  · right
    have : (⟨y, hy⟩ : ↥W) = (⟨x, hx⟩ : ↥W)⁻¹ := by
      apply e.injective
      rw [h, map_inv]
    simpa using congrArg Subtype.val this

theorem lemma22_1 : Lemma22_1 := by
  intro A _ _ hA
  unfold IsQ8StarQ8 at hA
  obtain ⟨U, V, hUe, hVe, hcomm, hsup, hcard⟩ := hA
  refine ⟨U, V, ⟨hUe, hVe, hcomm, hsup, hcard⟩, ?_⟩
  let eU : ↥U ≃* QuaternionGroup 2 := hUe.some
  let z : A := (eU.symm (QuaternionGroup.a 2) : ↥U)
  have hzU_mem : z ∈ U := (eU.symm (QuaternionGroup.a 2)).2
  have hzU_ne' : eU.symm (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    have h' : eU (eU.symm (QuaternionGroup.a 2)) = eU 1 := congrArg eU h
    rw [eU.apply_symm_apply, map_one] at h'
    exact Q_a2_ne_one h'
  have hzU_ne : z ≠ 1 := fun h => hzU_ne' (Subtype.coe_injective h)
  have hz_sq : z ^ 2 = 1 := by
    have h : (eU.symm (QuaternionGroup.a 2) : ↥U) ^ 2 = 1 := by
      apply eU.injective
      rw [map_pow, eU.apply_symm_apply, Q_a2_sq, map_one]
    simpa using congrArg Subtype.val h
  have hInter : ∀ x ∈ U ⊓ V, x = 1 ∨ x = z := by
    intro x hx
    have hxU : x ∈ U := hx.1
    have hx2 : x ^ 2 = 1 := by
      have h : (⟨x, hx⟩ : ↥(U ⊓ V)) ^ 2 = 1 := by
        have := pow_card_eq_one' (G := ↥(U ⊓ V)) (x := ⟨x, hx⟩)
        rwa [hcard] at this
      simpa using congrArg Subtype.val h
    exact eq_one_or_inv_of_iso eU x hxU hx2
  have hzV : z ∈ V :=
    (mem_involution_of_card_two (H := U ⊓ V) (U := U) inf_le_left hcard eU).2
  let eV : ↥V ≃* QuaternionGroup 2 := hVe.some
  have hzV_ne' : eV.symm (QuaternionGroup.a 2) ≠ 1 := by
    intro h
    have h' : eV (eV.symm (QuaternionGroup.a 2)) = eV 1 := congrArg eV h
    rw [eV.apply_symm_apply, map_one] at h'
    exact Q_a2_ne_one h'
  have hzV_ne : (eV.symm (QuaternionGroup.a 2) : A) ≠ 1 :=
    fun h => hzV_ne' (Subtype.coe_injective h)
  have hzV_eq : (eV.symm (QuaternionGroup.a 2) : A) = z := by
    have hmem := mem_involution_of_card_two (H := U ⊓ V) (U := V) inf_le_right hcard eV
    rcases hInter _ hmem with h | h
    · exact absurd h hzV_ne
    · exact h
  have hU_sq : ∀ u ∈ U, u ^ 2 = 1 ∨ u ^ 2 = z := fun u hu => sq_mem_or eU u hu
  have hV_sq : ∀ v ∈ V, v ^ 2 = 1 ∨ v ^ 2 = z := by
    intro v hv
    rcases sq_mem_or eV v hv with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hzV_eq)
  have hUnorm : U.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    apply sup_le
    · rw [Subgroup.le_normalizer_iff]
      intro u hu k hk
      exact U.mul_mem (U.mul_mem hu hk) (U.inv_mem hu)
    · rw [Subgroup.le_normalizer_iff]
      intro v hv u hu
      rw [← hcomm u hu v hv, mul_assoc, mul_inv_cancel, mul_one]
      exact hu
  have hVnorm : V.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup]
    apply sup_le
    · rw [Subgroup.le_normalizer_iff]
      intro u hu v hv
      rw [hcomm u hu v hv, mul_assoc, mul_inv_cancel, mul_one]
      exact hv
    · rw [Subgroup.le_normalizer_iff]
      intro v hv k hk
      exact V.mul_mem (V.mul_mem hv hk) (V.inv_mem hv)
  have hdecomp : ∀ x : A, ∃ u ∈ U, ∃ v ∈ V, u * v = x := by
    intro x
    have hx : x ∈ U ⊔ V := by rw [hsup]; exact Subgroup.mem_top x
    haveI : V.Normal := hVnorm
    exact (Subgroup.mem_sup_of_normal_right (s := U) (t := V)).mp hx
  have hsq_uv : ∀ u ∈ U, ∀ v ∈ V, (u * v) ^ 2 = u ^ 2 * v ^ 2 := by
    intro u hu v hv
    have huv : v * u = u * v := (hcomm u hu v hv).symm
    calc (u * v) ^ 2 = (u * v) * (u * v) := by rw [pow_two]
      _ = u * (v * (u * v)) := mul_assoc u v (u * v)
      _ = u * ((v * u) * v) := by rw [(mul_assoc v u v).symm]
      _ = u * ((u * v) * v) := by rw [huv]
      _ = u * (u * (v * v)) := by rw [mul_assoc]
      _ = (u * u) * (v * v) := (mul_assoc u u (v * v)).symm
      _ = u ^ 2 * v ^ 2 := by rw [pow_two, pow_two]
  have hsquare : ∀ x : A, x ^ 2 = 1 ∨ x ^ 2 = z := by
    intro x
    obtain ⟨u, hu, v, hv, rfl⟩ := hdecomp x
    rw [hsq_uv u hu v hv]
    rcases hU_sq u hu with hu2 | hu2 <;> rcases hV_sq v hv with hv2 | hv2
    · left; rw [hu2, hv2, one_mul]
    · right; rw [hu2, hv2, one_mul]
    · right; rw [hu2, hv2, mul_one]
    · left; rw [hu2, hv2]; simpa [pow_two] using hz_sq
  have hUV_sq : ∀ x : A, x ^ 2 = z → x ∈ U ∨ x ∈ V := by
    intro x hx
    obtain ⟨u, hu, v, hv, rfl⟩ := hdecomp x
    rw [hsq_uv u hu v hv] at hx
    rcases hU_sq u hu with hu2 | hu2 <;> rcases hV_sq v hv with hv2 | hv2
    · rw [hu2, hv2, one_mul] at hx
      exact absurd hx.symm hzU_ne
    · right
      have huV : u ∈ V := by
        rcases eq_one_or_inv_of_iso eU u hu hu2 with h | h
        · rw [h]; exact V.one_mem
        · rw [h]; exact hzV
      exact V.mul_mem huV hv
    · left
      have hvU : v ∈ U := by
        rcases eq_one_or_inv_of_iso eV v hv hv2 with h | h
        · rw [h]; exact U.one_mem
        · rw [h, hzV_eq]; exact hzU_mem
      exact U.mul_mem hu hvU
    · rw [hu2, hv2] at hx
      have h1 : z = 1 := by rw [← hx]; simpa [pow_two] using hz_sq
      exact absurd h1 hzU_ne
  have key : ∀ W : Subgroup A, Nonempty (↥W ≃* QuaternionGroup 2) → W = U ∨ W = V := by
    intro W hW
    obtain ⟨eW⟩ := hW
    have hzW : (eW.symm (QuaternionGroup.a 2) : A) = z := by
      have hx0sq : ((eW.symm (QuaternionGroup.xa 0) : ↥W) : A) ^ 2 =
          (eW.symm (QuaternionGroup.a 2) : A) := by
        have h : (eW.symm (QuaternionGroup.xa 0) : ↥W) ^ 2 = eW.symm (QuaternionGroup.a 2) := by
          rw [← map_pow eW.symm, Q_xa_sq]
        exact congrArg Subtype.val h
      have hne : (eW.symm (QuaternionGroup.a 2) : A) ≠ 1 := by
        intro h
        have h' : eW (eW.symm (QuaternionGroup.a 2)) = eW 1 :=
          congrArg eW (Subtype.ext (by simpa using h))
        rw [eW.apply_symm_apply, map_one] at h'
        exact Q_a2_ne_one h'
      rcases hsquare ((eW.symm (QuaternionGroup.xa 0) : ↥W) : A) with h | h
      · rw [hx0sq] at h; exact absurd h hne
      · rw [hx0sq] at h; exact h
    let x₁ : A := (eW.symm (QuaternionGroup.xa 0) : ↥W)
    have hx₁W : x₁ ∈ W := (eW.symm (QuaternionGroup.xa 0)).2
    have hx₁sq : x₁ ^ 2 = z := by
      have h : (eW.symm (QuaternionGroup.xa 0) : ↥W) ^ 2 = eW.symm (QuaternionGroup.a 2) := by
        rw [← map_pow eW.symm, Q_xa_sq]
      have h' := congrArg Subtype.val h
      rw [hzW] at h'
      simpa [x₁] using h'
    have hcardW : Nat.card ↥W = Nat.card (QuaternionGroup 2) := Nat.card_congr eW.toEquiv
    have hcardU : Nat.card ↥U = Nat.card (QuaternionGroup 2) := Nat.card_congr eU.toEquiv
    have hcardV : Nat.card ↥V = Nat.card (QuaternionGroup 2) := Nat.card_congr eV.toEquiv
    rcases hUV_sq x₁ hx₁sq with hx₁U | hx₁V
    · left
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro x hxW
        rcases sq_mem_or eW x hxW with hx2 | hx2
        · rcases eq_one_or_inv_of_iso eW x hxW hx2 with h | h
          · rw [h]; exact U.one_mem
          · rw [h, hzW]; exact hzU_mem
        · rw [hzW] at hx2
          rcases hUV_sq x hx2 with hxU | hxV
          · exact hxU
          · rcases commute_sq_eq eW hxW hx₁W hzW.symm hx2 hx₁sq
              (by rw [hcomm x₁ hx₁U x hxV]) with h | h
            · rw [← h]; exact hx₁U
            · have hx : x = x₁⁻¹ := by simpa using congrArg Inv.inv h.symm
              rw [hx]; exact U.inv_mem hx₁U
      · rw [hcardU, hcardW]
    · right
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · intro x hxW
        rcases sq_mem_or eW x hxW with hx2 | hx2
        · rcases eq_one_or_inv_of_iso eW x hxW hx2 with h | h
          · rw [h]; exact V.one_mem
          · rw [h, hzW]; exact hzV
        · rw [hzW] at hx2
          rcases hUV_sq x hx2 with hxU | hxV
          · rcases commute_sq_eq eW hxW hx₁W hzW.symm hx2 hx₁sq
              (by rw [hcomm x hxU x₁ hx₁V]) with h | h
            · rw [← h]; exact hx₁V
            · have hx : x = x₁⁻¹ := by simpa using congrArg Inv.inv h.symm
              rw [hx]; exact V.inv_mem hx₁V
          · exact hxV
      · rw [hcardV, hcardW]
  intro U' V' hUV'
  unfold IsQ8Decomp at hUV'
  obtain ⟨hU'e, hV'e, _, _, hcard'⟩ := hUV'
  have hU' : U' = U ∨ U' = V := key U' hU'e
  have hV' : V' = U ∨ V' = V := key V' hV'e
  have hcardU' : Nat.card ↥U' = 8 := by rw [Nat.card_congr hU'e.some.toEquiv, Q_card]
  have hcardV' : Nat.card ↥V' = 8 := by rw [Nat.card_congr hV'e.some.toEquiv, Q_card]
  have hcardU : Nat.card ↥U = 8 := by rw [Nat.card_congr eU.toEquiv, Q_card]
  have hcardV : Nat.card ↥V = 8 := by rw [Nat.card_congr eV.toEquiv, Q_card]
  rcases hU' with hU' | hU' <;> rcases hV' with hV' | hV'
  · exfalso
    have h8 : Nat.card ↥(U' ⊓ V') = 8 := by rw [hU', hV', inf_idem, hcardU]
    omega
  · exact Or.inl ⟨hU', hV'⟩
  · exact Or.inr ⟨hU', hV'⟩
  · exfalso
    have h8 : Nat.card ↥(U' ⊓ V') = 8 := by rw [hU', hV', inf_idem, hcardV]
    omega

end CFSG.OddStandard.HigherRank.G2Three.Sec2
