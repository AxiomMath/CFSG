module

public import CFSG.LargeExtraspecial.S14SMKModPhi

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup Module QuadraticMap CFSG.Open CFSG.Fischer CFSG.SmithE
  CFSG.LargeExtraspecial.SMod20 CFSG.RankThree.OrthogonalInvolutions

@[expose] def NoTwoSub (π : Equiv.Perm (Fin 693)) : Prop :=
  ∀ R : Subgroup (Equiv.Perm (Fin 693)), R ≤ T46 → IsPGroup 2 R →
    (∀ r ∈ R, r * π = π * r) →
    (∀ p : Fin 693, π p = p → ∀ r ∈ R, tvP p * r * (tvP p)⁻¹ ∈ R) → R = ⊥

structure InvHyp
    (A : V ≃ₗ[ZMod 2] V) (π : Equiv.Perm (Fin 693)) : Prop where
  norm : π ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693)))
  conj : ∀ p : Fin 693, A * tvEquiv p.val * A⁻¹ = tvEquiv (π p).val
  sq : A * A = 1
  ne : A ≠ 1

@[expose] def InvConcl (A : V ≃ₗ[ZMod 2] V)
    (π : Equiv.Perm (Fin 693)) : Prop :=
  5 ≤ finrank (ZMod 2) (commSpace A) ∧
    ∀ q : QuadraticForm (ZMod 2) V, (∀ u v, polar q u v = fModel u v) →
      (∀ i < 891, q (wtV i) = 0) → (∀ v ∈ commSpace A, q v = 0) →
      (∃ i < 891, π ∈ UA i) ∨ (finrank (ZMod 2) (commSpace A) ≤ 8 ∧ NoTwoSub π)

@[expose] def InvolutionFacts :
    Prop :=
  ∀ (A : V ≃ₗ[ZMod 2] V) (π : Equiv.Perm (Fin 693)), InvHyp A π → InvConcl A π

theorem wtV_ne_zero {i : ℕ} (hi : i < 891) : wtV i ≠ 0 := by
  intro h
  apply SMG.wt_ne_zero hi
  exact eq_of_decode_eq (wt_lt hi) (by norm_num) (h.trans decode_zero.symm)

theorem tvEquiv_inj {p q : Fin 693} (h : tvEquiv p.val = tvEquiv q.val) : p = q := by
  rw [← rhoMod_tvP, ← rhoMod_tvP] at h
  have h2 : (⟨tvP p, tvP_mem p⟩ : T46) = ⟨tvP q, tvP_mem q⟩ := rhoMod_injective h
  have h3 : tvP p = tvP q := by injection h2
  exact tvP_injective h3

@[expose] noncomputable def normAut (π : Equiv.Perm (Fin 693))
    (hπ : π ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693)))) : MulAut T46 where
  toFun g := ⟨π * g * π⁻¹, (mem_normalizer_iff.mp hπ g).mp g.2⟩
  invFun g := ⟨π⁻¹ * g * π, (mem_normalizer_iff.mp hπ (π⁻¹ * g * π)).mpr (by
    rw [show π * (π⁻¹ * g * π) * π⁻¹ = g by group]
    exact g.2)⟩
  left_inv g := Subtype.ext (show π⁻¹ * (π * (g : Equiv.Perm (Fin 693)) * π⁻¹) * π = g by group)
  right_inv g := Subtype.ext (show π * (π⁻¹ * (g : Equiv.Perm (Fin 693)) * π) * π⁻¹ = g by group)
  map_mul' g h := Subtype.ext (show π * ((g : Equiv.Perm (Fin 693)) * h) * π⁻¹ =
    π * g * π⁻¹ * (π * h * π⁻¹) by group)

theorem autPerm_normAut (π : Equiv.Perm (Fin 693))
    (hπ : π ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693)))) : autPerm (normAut π hπ) = π :=
  (isAutPerm_autPerm _).unique
    ⟨fun _ => rfl, fun p => (isPolarAut_of_mem_normalizer hπ).mul_tvP_mul_inv p⟩

theorem image_wPlane_normAut (π : Equiv.Perm (Fin 693))
    (hπ : π ∈ normalizer (T46 : Set (Equiv.Perm (Fin 693)))) (i : Fin 891) :
    ⇑π '' wPlane i = wPlane (autPlane (normAut π hπ) i) := by
  have hspec := autPlane_spec (normAut π hπ) i
  rw [autPerm_normAut] at hspec
  rw [wPlane_eq_planeSet i.2, wPlane_eq_planeSet (autPlane (normAut π hπ) i).2,
    ← planePoints_eq_planeSet i.2, ← planePoints_eq_planeSet (autPlane (normAut π hπ) i).2]
  ext q
  simp only [Set.mem_image, Finset.mem_coe]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (hspec p).1 hp
  · intro hq
    refine ⟨π⁻¹ q, (hspec _).2 ?_, perm_apply_inv_self _ q⟩
    rw [perm_apply_inv_self]
    exact hq

theorem linv_apply (A : V ≃ₗ[ZMod 2] V) (v : V) : A⁻¹ v = A.symm v := rfl

variable {A : V ≃ₗ[ZMod 2] V} {π : Equiv.Perm (Fin 693)}

theorem InvHyp.wtV_eq (h : InvHyp A π) {i j : ℕ} (hi : i < 891) (hj : j < 891)
    (hij : ⇑π '' wPlane i = wPlane j) : A (wtV i) = wtV j := by
  have hfix : ∀ q ∈ planeSet j, tvEquiv q.val (A (wtV i)) = A (wtV i) := by
    intro q hq
    have hq' : q ∈ wPlane j := by rw [wPlane_eq_planeSet hj]; exact hq
    rw [← hij] at hq'
    obtain ⟨p, hp, rfl⟩ := hq'
    have hp' : p ∈ planeSet i := by rw [← Finset.mem_coe, ← wPlane_eq_planeSet hi]; exact hp
    have e := h.conj p
    rw [← e, LinearEquiv.mul_apply, LinearEquiv.mul_apply, linv_apply,
      LinearEquiv.symm_apply_apply, tvEquiv_wtV_self hi hp']
  rcases (fixed_iff hj _).mp hfix with h0 | h1
  · exact absurd (A.injective (h0.trans A.map_zero.symm)) (wtV_ne_zero hi)
  · exact h1

theorem InvHyp.mul_self (h : InvHyp A π) : π * π = 1 := by
  have hA : A⁻¹ = A := inv_eq_of_mul_eq_one_right h.sq
  refine Equiv.ext fun p => ?_
  have e : tvEquiv (π (π p)).val = tvEquiv p.val := by
    rw [← h.conj, ← h.conj, hA, show A * (A * tvEquiv p.val * A) * A =
      (A * A) * tvEquiv p.val * (A * A) by group, h.sq, one_mul, mul_one]
  rw [Equiv.Perm.mul_apply, tvEquiv_inj e]
  rfl

theorem InvHyp.ne_one (h : InvHyp A π) : π ≠ 1 := by
  rintro rfl
  apply h.ne
  apply LinearEquiv.toLinearMap_injective
  refine ext_wtV fun i => ?_
  rw [LinearEquiv.coe_coe, h.wtV_eq i.2 i.2 (by simp)]
  rfl

theorem InvHyp.exists_fixed_plane (h : InvHyp A π) :
    ∃ i < 891, ⇑π '' wPlane i = wPlane i := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set α := normAut π h.norm with hα
  have hαα : α * α = 1 := by
    apply autPerm_injective
    rw [map_mul, map_one, hα, autPerm_normAut, h.mul_self]
  have hσ : autPlane α * autPlane α = 1 := by rw [← map_mul, hαα, map_one]
  have hP : IsPGroup 2 (zpowers (autPlane α)) := by
    have hd : Nat.card (zpowers (autPlane α)) ∣ 2 ^ 1 := by
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_dvd_of_pow_eq_one (by rw [pow_two, hσ])
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    exact IsPGroup.of_card hk
  obtain ⟨i, hi⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Fin 891)
    (by rw [Nat.card_fin]; decide)
  have hfix : autPlane α i = i := hi ⟨autPlane α, mem_zpowers _⟩
  refine ⟨i, i.2, ?_⟩
  have := image_wPlane_normAut π h.norm i
  rw [← hα, hfix] at this
  exact this

theorem InvHyp.conjT (h : InvHyp A π) (g : T46) :
    InvHyp (rhoMod g * A * (rhoMod g)⁻¹)
      ((g : Equiv.Perm (Fin 693)) * π * (g : Equiv.Perm (Fin 693))⁻¹) := by
  refine ⟨?_, fun p => ?_, ?_, ?_⟩
  · have hg := le_normalizer g.2
    exact mul_mem (mul_mem hg h.norm) (inv_mem hg)
  · have e1 : (rhoMod g)⁻¹ * tvEquiv p.val * rhoMod g =
        tvEquiv (((g⁻¹ : T46) : Equiv.Perm (Fin 693)) p).val := by
      rw [← rhoMod_conj_tvEquiv, map_inv, inv_inv]
    have e2 : rhoMod g * A * (rhoMod g)⁻¹ * tvEquiv p.val * (rhoMod g * A * (rhoMod g)⁻¹)⁻¹ =
        rhoMod g * (A * ((rhoMod g)⁻¹ * tvEquiv p.val * rhoMod g) * A⁻¹) * (rhoMod g)⁻¹ := by
      group
    rw [e2, e1, h.conj, rhoMod_conj_tvEquiv]
    congr 2
  · rw [show rhoMod g * A * (rhoMod g)⁻¹ * (rhoMod g * A * (rhoMod g)⁻¹) =
      rhoMod g * (A * A) * (rhoMod g)⁻¹ by group, h.sq, mul_one, mul_inv_cancel]
  · intro h1
    apply h.ne
    have := congrArg (fun B => (rhoMod g)⁻¹ * B * rhoMod g) h1
    simpa [mul_assoc] using this

theorem invConcl_of_conj (g : T46)
    (hc : InvConcl (rhoMod g * A * (rhoMod g)⁻¹)
      ((g : Equiv.Perm (Fin 693)) * π * (g : Equiv.Perm (Fin 693))⁻¹)) :
    InvConcl A π := by
  have hint : ∀ v, (rhoMod g * A * (rhoMod g)⁻¹) (rhoMod g v) = rhoMod g (A v) := fun v => by
    simp only [LinearEquiv.mul_apply, linv_apply, LinearEquiv.symm_apply_apply]
  have hdim := finrank_commSpace_of_intertwine (rhoMod g) hint
  obtain ⟨hl5, hts⟩ := hc
  refine ⟨hdim ▸ hl5, fun q hpol hwt hsing => ?_⟩
  have hpol' : ∀ u v, polar (q.comp ((rhoMod g)⁻¹ : V ≃ₗ[ZMod 2] V).toLinearMap) u v =
      fModel u v := by
    intro u v
    have e : polar (q.comp ((rhoMod g)⁻¹ : V ≃ₗ[ZMod 2] V).toLinearMap) u v =
        polar q ((rhoMod g)⁻¹ u) ((rhoMod g)⁻¹ v) := by
      simp only [polar, comp_apply, LinearEquiv.coe_coe, map_add]
    rw [e, hpol, ← map_inv, fModel_rhoMod]
  have hwt' : ∀ i < 891, q.comp ((rhoMod g)⁻¹ : V ≃ₗ[ZMod 2] V).toLinearMap (wtV i) = 0 := by
    intro i hi
    rw [comp_apply, LinearEquiv.coe_coe, ← map_inv]
    have := rhoMod_wtV g⁻¹ ⟨i, hi⟩
    rw [this]
    exact hwt _ (g⁻¹ • (⟨i, hi⟩ : Fin 891)).2
  have hsing' : ∀ v ∈ commSpace (rhoMod g * A * (rhoMod g)⁻¹),
      q.comp ((rhoMod g)⁻¹ : V ≃ₗ[ZMod 2] V).toLinearMap v = 0 := by
    intro v hv
    rw [commSpace_eq_map_of_intertwine (rhoMod g) hint] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    rw [comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, linv_apply,
      LinearEquiv.symm_apply_apply]
    exact hsing w hw
  rcases hts _ hpol' hwt' hsing' with ⟨i, hi, hU⟩ | ⟨hl8, hF⟩
  · left
    obtain ⟨j, hj, hjW⟩ := exists_image_wPlane (T46.inv_mem g.2) hi
    refine ⟨j, hj, ?_⟩
    have := conj_mem_UA (isPolarAut_of_mem (T46.inv_mem g.2)) hjW hU
    rwa [show (g : Equiv.Perm (Fin 693))⁻¹ *
      ((g : Equiv.Perm (Fin 693)) * π * (g : Equiv.Perm (Fin 693))⁻¹) *
      (g : Equiv.Perm (Fin 693))⁻¹⁻¹ = π by group] at this
  · right
    refine ⟨hdim ▸ hl8, fun R hRT hRp hRc hRn => ?_⟩
    have hR' := hF (R.map (MulAut.conj (g : Equiv.Perm (Fin 693))).toMonoidHom)
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact T46.mul_mem (T46.mul_mem g.2 (hRT hr)) (T46.inv_mem g.2))
      (hRp.map _)
      (by
        rintro _ ⟨r, hr, rfl⟩
        have := hRc r hr
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [show (g : Equiv.Perm (Fin 693)) * r * (g : Equiv.Perm (Fin 693))⁻¹ *
            ((g : Equiv.Perm (Fin 693)) * π * (g : Equiv.Perm (Fin 693))⁻¹) =
          (g : Equiv.Perm (Fin 693)) * (r * π) * (g : Equiv.Perm (Fin 693))⁻¹ by group, this]
        group)
      (by
        rintro p hp _ ⟨r, hr, rfl⟩
        have hp' : π ((g : Equiv.Perm (Fin 693))⁻¹ p) = (g : Equiv.Perm (Fin 693))⁻¹ p := by
          have := congrArg (fun x => (g : Equiv.Perm (Fin 693))⁻¹ x) hp
          simpa [Equiv.Perm.mul_apply] using this
        have hn := hRn _ hp' r hr
        refine ⟨_, hn, ?_⟩
        have e : tvP p = (g : Equiv.Perm (Fin 693)) * tvP ((g : Equiv.Perm (Fin 693))⁻¹ p) *
            (g : Equiv.Perm (Fin 693))⁻¹ := by
          rw [(isPolarAut_of_mem g.2).mul_tvP_mul_inv, perm_apply_inv_self]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        rw [e]
        group)
    rw [eq_bot_iff]
    intro r hr
    have : (g : Equiv.Perm (Fin 693)) * r * (g : Equiv.Perm (Fin 693))⁻¹ ∈
        R.map (MulAut.conj (g : Equiv.Perm (Fin 693))).toMonoidHom := ⟨r, hr, rfl⟩
    rw [hR', mem_bot] at this
    rw [mem_bot]
    have := congrArg (fun x => (g : Equiv.Perm (Fin 693))⁻¹ * x * (g : Equiv.Perm (Fin 693))) this
    simpa [mul_assoc] using this

end CFSG.LargeExtraspecial.S14.SMK
