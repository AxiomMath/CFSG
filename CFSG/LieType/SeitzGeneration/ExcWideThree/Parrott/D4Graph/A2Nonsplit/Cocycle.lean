module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit.Twist

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator CFSG.HardMathSupport.Seitz.Proving

section Tuples

variable {L : Type} [Field L]

@[expose] def pw (x : Lˣ) (v : Fin Tag.D4.rank → ℤ) : Fin Tag.D4.rank → Lˣ := fun j => x ^ v j

theorem pw_add (x : Lˣ) (v w : Fin Tag.D4.rank → ℤ) : pw x (v + w) = pw x v * pw x w := by
  funext j
  simp only [pw, Pi.add_apply, Pi.mul_apply, zpow_add]

theorem pw_zero (x : Lˣ) : pw x 0 = 1 := by
  funext j
  simp only [pw, Pi.zero_apply, zpow_zero, Pi.one_apply]

theorem tupAct_pw (M : Matrix (Fin Tag.D4.rank) (Fin Tag.D4.rank) ℤ) (x : Lˣ)
    (v : Fin Tag.D4.rank → ℤ) : tupAct M (pw x v) = pw x (M.mulVec v) :=
  tupAct_zpow M x v

@[expose] def vX : Fin Tag.D4.rank → ℤ := ![1, 1, 0, 1]

@[expose] def vZ : Fin Tag.D4.rank → ℤ := ![0, 0, 1, 0]

@[expose] def vChi : Fin Tag.D4.rank → ℤ := ![2, 2, 3, 2]

@[expose] def vTheta : Fin Tag.D4.rank → ℤ := ![1, 1, 2, 1]

theorem vX_vals : vX ⟨0, by decide⟩ = 1 ∧ vX ⟨1, by decide⟩ = 1 ∧ vX ⟨2, by decide⟩ = 0 ∧
    vX ⟨3, by decide⟩ = 1 := by
  decide

theorem vZ_vals : vZ ⟨0, by decide⟩ = 0 ∧ vZ ⟨1, by decide⟩ = 0 ∧ vZ ⟨2, by decide⟩ = 1 ∧
    vZ ⟨3, by decide⟩ = 0 := by
  decide

@[expose] def tupXZ (x z : Lˣ) : Fin Tag.D4.rank → Lˣ := pw x vX * pw z vZ

theorem tupXZ_apply (x z : Lˣ) (j : Fin Tag.D4.rank) : tupXZ x z j = x ^ vX j * z ^ vZ j :=
  rfl

theorem tupXZ_zero (x z : Lˣ) : tupXZ x z ⟨0, by decide⟩ = x := by
  rw [tupXZ_apply, vX_vals.1, vZ_vals.1, zpow_one, zpow_zero, mul_one]

theorem tupXZ_two (x z : Lˣ) : tupXZ x z ⟨2, by decide⟩ = z := by
  rw [tupXZ_apply, vX_vals.2.2.1, vZ_vals.2.2.1, zpow_zero, zpow_one, one_mul]

theorem tupXZ_mul (x z x' z' : Lˣ) : tupXZ x z * tupXZ x' z' = tupXZ (x * x') (z * z') := by
  funext j
  simp only [tupXZ, pw, Pi.mul_apply, mul_zpow]
  rw [mul_mul_mul_comm]

theorem map_tupXZ {L' : Type} [Field L'] (f : L →* L') (x z : Lˣ) :
    (fun j => Units.map f (tupXZ x z j)) = tupXZ (Units.map f x) (Units.map f z) := by
  funext j
  simp only [tupXZ, pw, Pi.mul_apply, map_mul, map_zpow]

theorem cartan_vX_vZ :
    (fun j => vChi ⟨0, by decide⟩ * Tag.D4.cartan ⟨0, by decide⟩ j +
        vChi ⟨1, by decide⟩ * Tag.D4.cartan ⟨1, by decide⟩ j +
        vChi ⟨2, by decide⟩ * Tag.D4.cartan ⟨2, by decide⟩ j +
        vChi ⟨3, by decide⟩ * Tag.D4.cartan ⟨3, by decide⟩ j) = vX ∧
    (fun j => vTheta ⟨0, by decide⟩ * Tag.D4.cartan ⟨0, by decide⟩ j +
        vTheta ⟨1, by decide⟩ * Tag.D4.cartan ⟨1, by decide⟩ j +
        vTheta ⟨2, by decide⟩ * Tag.D4.cartan ⟨2, by decide⟩ j +
        vTheta ⟨3, by decide⟩ * Tag.D4.cartan ⟨3, by decide⟩ j) = vZ := by
  decide

theorem vX_vZ_facts :
    vX + (weylG2M ^ 4).mulVec vX + (weylG2M ^ 8).mulVec vX = 0 ∧
    vZ + (weylG2M ^ 4).mulVec vZ + (weylG2M ^ 8).mulVec vZ = 0 ∧
    (∀ j, vX (rhoP.symm j) = vX j) ∧ (∀ j, vZ (rhoP.symm j) = vZ j) := by
  decide

theorem tupAct_permM_tupXZ (x z : Lˣ) : tupAct permM (tupXZ x z) = tupXZ x z := by
  rw [tupAct_permM]
  funext j
  simp only [tupXZ, pw, Pi.mul_apply, vX_vZ_facts.2.2.1 j, vX_vZ_facts.2.2.2 j]

theorem eq_tupXZ_of_tupAct_permM {e : Fin Tag.D4.rank → Lˣ} (h : tupAct permM e = e) :
    e = tupXZ (e ⟨0, by decide⟩) (e ⟨2, by decide⟩) := by
  rw [tupAct_permM] at h
  have h1 := congrFun h ⟨1, by decide⟩
  have h3 := congrFun h ⟨3, by decide⟩
  have h0 := congrFun h ⟨0, by decide⟩
  rw [show rhoP.symm ⟨1, by decide⟩ = ⟨0, by decide⟩ by decide] at h1
  rw [show rhoP.symm ⟨3, by decide⟩ = ⟨1, by decide⟩ by decide] at h3
  rw [show rhoP.symm ⟨0, by decide⟩ = ⟨3, by decide⟩ by decide] at h0
  funext j
  rw [tupXZ_apply]
  rcases fin_D4_cases j with rfl | rfl | rfl | rfl
  · rw [vX_vals.1, vZ_vals.1, zpow_one, zpow_zero, mul_one]
  · rw [vX_vals.2.1, vZ_vals.2.1, zpow_one, zpow_zero, mul_one]
    exact h1.symm
  · rw [vX_vals.2.2.1, vZ_vals.2.2.1, zpow_zero, zpow_one, one_mul]
  · rw [vX_vals.2.2.2, vZ_vals.2.2.2, zpow_one, zpow_zero, mul_one]
    exact h0

end Tuples

section Groups

variable {G : Type*} [Group G]

theorem inf_zpowers_eq_bot_of_pow_three {H : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hx : x ∉ H) : H ⊓ Subgroup.zpowers x = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨hyH, hyx⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hyx
  have hk : x ^ k = x ^ (k % 3) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 3]
    rw [zpow_add, zpow_mul, show x ^ (3 : ℤ) = 1 by exact_mod_cast hx3, one_zpow, mul_one]
  rw [hk] at hyH ⊢
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have h3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h | h | h
  · rw [h, zpow_zero]
    exact Subgroup.one_mem _
  · rw [h, zpow_one] at hyH
    exact absurd hyH hx
  · rw [h] at hyH
    exfalso
    apply hx
    have e : x = (x ^ (2 : ℤ))⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← zpow_one_add]
      exact_mod_cast hx3
    rw [e]
    exact H.inv_mem hyH

theorem exists_pow_eq_of_pow_eq_one {C : Type*} [CommGroup C] [Finite C] [IsCyclic C] {n m : ℕ}
    (hcard : Nat.card C = n * m) {x : C} (hx : x ^ m = 1) : ∃ t : C, t ^ n = x := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := C)
  have hord : orderOf g = n * m := (orderOf_eq_card_of_forall_mem_zpowers hg).trans hcard
  have hm : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card C := Nat.card_pos
    rw [hcard] at this
    simp at this
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hg x)
  have h1 : (orderOf g : ℤ) ∣ j * m := by
    rw [orderOf_dvd_iff_zpow_eq_one, zpow_mul, zpow_natCast]
    exact hx
  rw [hord] at h1
  push_cast at h1
  have h2 : (n : ℤ) ∣ j := by
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm
    rw [mul_comm (n : ℤ) m, mul_comm j m] at h1
    exact (mul_dvd_mul_iff_left hm').1 h1
  obtain ⟨k, rfl⟩ := h2
  exact ⟨g ^ k, by rw [← zpow_natCast, ← zpow_mul, mul_comm]⟩

theorem exists_pow_succ_eq {L : Type} [Field L] [Finite L] {q : ℕ} (hq : Nat.card L = q ^ 2)
    (hq1 : 1 ≤ q) {a : Lˣ} (ha : a ^ q = a) : ∃ t : Lˣ, t ^ (q + 1) = a := by
  refine exists_pow_eq_of_pow_eq_one (m := q - 1) ?_ ?_
  · rw [Nat.card_units, hq]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    have : (q' + 1) ^ 2 = (q' + 1 + 1) * (q' + 1 - 1) + 1 := by
      rw [Nat.add_sub_cancel]
      ring
    omega
  · have h : a ^ (q - 1) * a = a ^ q := by
      rw [← pow_succ, Nat.sub_add_cancel hq1]
    rw [ha] at h
    exact mul_eq_right.1 h

end Groups


variable {L : Type} [Field L]

@[expose] noncomputable def cochar (v : Fin Tag.D4.rank → ℤ) (t : Lˣ) :
    ↥(adjointGroup Tag.D4 L) :=
  torusElement Tag.D4 L ⟨0, by decide⟩ (t ^ v ⟨0, by decide⟩) *
    torusElement Tag.D4 L ⟨1, by decide⟩ (t ^ v ⟨1, by decide⟩) *
    torusElement Tag.D4 L ⟨2, by decide⟩ (t ^ v ⟨2, by decide⟩) *
    torusElement Tag.D4 L ⟨3, by decide⟩ (t ^ v ⟨3, by decide⟩)

theorem coe_cochar (v : Fin Tag.D4.rank → ℤ) (t : Lˣ) :
    ((cochar v t : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 (pw t (fun j => v ⟨0, by decide⟩ * Tag.D4.cartan ⟨0, by decide⟩ j +
        v ⟨1, by decide⟩ * Tag.D4.cartan ⟨1, by decide⟩ j +
        v ⟨2, by decide⟩ * Tag.D4.cartan ⟨2, by decide⟩ j +
        v ⟨3, by decide⟩ * Tag.D4.cartan ⟨3, by decide⟩ j)) := by
  simp only [cochar, Subgroup.coe_mul, coe_torusElement, ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, pw, ← zpow_mul, ← zpow_add]

theorem cochar_tupXZ (x z : Lˣ) :
    ((cochar vChi x * cochar vTheta z : ↥(adjointGroup Tag.D4 L)) :
      ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z) := by
  rw [Subgroup.coe_mul, coe_cochar, coe_cochar, ← rootDiagUnit_mul, cartan_vX_vZ.1,
    cartan_vX_vZ.2]
  rfl

@[expose] noncomputable def cocyc (c : Lˣ) : ↥(adjointGroup Tag.D4 L) :=
  gTw (nSL c) * (weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4 * (gTw (nSL c))⁻¹ *
    ((weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4)⁻¹

theorem cocyc_mem_torusGroup (c : Lˣ) :
    ((cocyc c : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) ∈ torusGroup Tag.D4 L := by
  have h := (((isMono_gTw_nSL (L := L) c).mul (isMono_weylG2.pow 4)).mul
    (isMono_gTw_nSL c).inv).mul (isMono_weylG2.pow 4).inv
  have hw : wN * wG ^ 4 * wN⁻¹ * (wG ^ 4)⁻¹ = 1 := by
    rw [wN_mul_wG_pow]
    group
  rw [hw] at h
  refine IsMono.mem_torusGroup ?_
  simpa only [cocyc, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using h

theorem d4Graph_cocyc (c : Lˣ) : d4Graph L 1 (cocyc c) = cocyc c := by
  rw [cocyc, map_mul, map_mul, map_mul, map_inv, map_inv, map_pow, d4Graph_gTw,
    d4Graph_one_weylG2]

theorem exists_cocyc_tupXZ (c : Lˣ) : ∃ a b : Lˣ,
    ((cocyc c : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ a b) := by
  obtain ⟨e, he⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (cocyc_mem_torusGroup c)
  have hγ := d4Graph_one_torusSub he
  rw [d4Graph_cocyc, he] at hγ
  have hfix : tupAct permM e = e := (rootDiagUnit_injective_D4 hγ).symm
  exact ⟨_, _, he.trans (congrArg _ (eq_tupXZ_of_tupAct_permM hfix))⟩

theorem bcAd_gTw_nSL (σ : L →+* L) {c : Lˣ} (hc : Units.map σ.toMonoidHom c = -c) :
    bcAd σ (gTw (nSL c)) = (gTw (nSL c))⁻¹ := by
  rw [bcAd_gTw, mapSL_nSL, hc, ← nSL_inv, gTw_inv]

theorem bcAd_cocyc (σ : L →+* L) {c : Lˣ} (hc : Units.map σ.toMonoidHom c = -c) :
    bcAd σ (cocyc c) = cocyc c := by
  obtain ⟨a, b, he⟩ := exists_cocyc_tupXZ c
  have h1 := gTw_nSL_inv_conj_diag c he
  have h2 : bcAd σ (cocyc c) = ((gTw (nSL c))⁻¹ * cocyc c * gTw (nSL c))⁻¹ := by
    simp only [cocyc, map_mul, map_inv, map_pow, bcAd_gTw_nSL σ hc, bcAd_weylG2]
    group
  rw [h2, h1, inv_inv]

section PiP

variable {ω : Lˣ} (hω3 : ω ^ 3 = 1)

include hω3 in
theorem mul_yP_pow_three [Finite L] {r : ↥(adjointGroup Tag.D4 L)} {x z : Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z)) : (r * yP hω3) ^ 3 = 1 := by
  have e : (r * yP hω3) ^ 3 = r * (yP hω3 ^ 1 * r * (yP hω3 ^ 1)⁻¹) *
      (yP hω3 ^ 2 * r * (yP hω3 ^ 2)⁻¹) * yP hω3 ^ 3 := by
    rw [show (r * yP hω3) ^ 3 = r * yP hω3 * (r * yP hω3) * (r * yP hω3) by
      rw [pow_succ, pow_two]]
    group
  rw [e, yP_pow_three hω3, mul_one]
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, yP_pow_conj_diag hω3 1 hr, yP_pow_conj_diag hω3 2 hr, hr,
    Subgroup.coe_one, ← rootDiagUnit_mul, ← rootDiagUnit_mul, ← rootDiagUnit_one]
  congr 1
  have key : tupXZ x z * tupAct (weylG2M ^ (4 * 1)) (tupXZ x z) *
      tupAct (weylG2M ^ (4 * 2)) (tupXZ x z) =
      pw x (vX + (weylG2M ^ 4).mulVec vX + (weylG2M ^ 8).mulVec vX) *
        pw z (vZ + (weylG2M ^ 4).mulVec vZ + (weylG2M ^ 8).mulVec vZ) := by
    simp only [tupXZ, tupAct_mul, tupAct_pw, pw_add, show 4 * 1 = 4 from rfl,
      show 4 * 2 = 8 from rfl]
    simp only [mul_assoc, mul_comm, mul_left_comm]
  rw [key, vX_vZ_facts.1, vX_vZ_facts.2.1, pw_zero, pw_zero, mul_one]

include hω3 in
theorem gammaP_HSL_mul_yP {r : ↥(adjointGroup Tag.D4 L)} {x z : Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z)) :
    gammaP L (HSL ω) (r * yP hω3) = r * yP hω3 := by
  have hγr : gammaP L (HSL ω) r = r := by
    apply Subtype.ext
    rw [gammaP_HSL_diag ω hr, tupAct_permM_tupXZ, hr]
  rw [map_mul, hγr, gammaP_HSL_yP]

include hω3 in
theorem mul_yP_commute_dTorus {r : ↥(adjointGroup Tag.D4 L)} {x z : Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z)) (l : Lˣ) :
    Commute (r * yP hω3)
      (torusElement Tag.D4 L ⟨0, by decide⟩ l * torusElement Tag.D4 L ⟨1, by decide⟩ l⁻¹) :=
  (Commute.mul_left (commute_of_diag hr (coe_dTorus l)) (yP_commute_dTorus hω3 l))

include hω3 in
theorem mul_yP_not_diag (hω : orderOf ω = 3) {r : ↥(adjointGroup Tag.D4 L)} {x z : Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z)) {b : Fin Tag.D4.rank → Lˣ}
    (hb : ((r * yP hω3 : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 b) :
    False := by
  refine yP_pow_not_diag hω3 hω (k := 1) (Or.inl rfl) (a := (tupXZ x z)⁻¹ * b) ?_
  rw [pow_one, show yP hω3 = r⁻¹ * (r * yP hω3) by group, Subgroup.coe_mul, Subgroup.coe_inv, hb,
    hr, rootDiagUnit_inv, ← rootDiagUnit_mul]

include hω3 in
theorem mul_yP_mem_normalizer_T3fix [Finite L] (μ : Subgroup Lˣ) {r : ↥(adjointGroup Tag.D4 L)}
    {x z : Lˣ} (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z)) :
    r * yP hω3 ∈
      Subgroup.normalizer (T3fix (ω := ω) (K := L) μ : Set ↥(adjointGroup Tag.D4 L)) := by
  refine mul_mem (Subgroup.centralizer_le_normalizer _ ?_) (yP_mem_normalizer_T3fix hω3 μ)
  rw [Subgroup.mem_centralizer_iff]
  rintro g ⟨⟨a, -, hga⟩, -⟩
  exact commute_of_diag hga hr

end PiP

theorem fixed_mul_yP {σ : L →+* L} {c ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hσω : Units.map σ.toMonoidHom ω = ω⁻¹) {r : ↥(adjointGroup Tag.D4 L)} {x z : Lˣ}
    (hr : (r : ModGL Tag.D4 L) = rootDiagUnit Tag.D4 (tupXZ x z))
    (hcr : cocyc c = r * bcAd σ r) :
    gTw (nSL c) * bcAd σ (r * yP hω3) * (gTw (nSL c))⁻¹ = r * yP hω3 := by
  have hr' : ((bcAd σ r : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 (tupXZ (Units.map σ.toMonoidHom x) (Units.map σ.toMonoidHom z)) := by
    rw [coe_bcAd_of_eq_rootDiagUnit σ hr, map_tupXZ]
  have hsc : ((sElt hω3 : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 (fun j => ω ^ vS j) := rfl
  have hs : bcAd σ (sElt hω3) = (sElt hω3)⁻¹ := by
    apply Subtype.ext
    rw [coe_bcAd_of_eq_rootDiagUnit σ hsc, Subgroup.coe_inv, hsc, rootDiagUnit_inv]
    congr 1
    funext j
    rw [map_zpow, hσω, Pi.inv_apply, inv_zpow]
  have hsinv : (((sElt hω3)⁻¹ : ↥(adjointGroup Tag.D4 L)) : ModGL Tag.D4 L) =
      rootDiagUnit Tag.D4 (fun j => ω ^ vS j)⁻¹ := by
    rw [Subgroup.coe_inv, hsc, rootDiagUnit_inv]
  have hW : bcAd σ ((weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4) = weylG2 ^ 4 := by
    rw [map_pow, bcAd_weylG2]
  have h1 := gTw_nSL_conj_diag c hr'
  have h2 := gTw_nSL_conj_diag c hsinv
  rw [inv_inv] at h2
  have h3 : gTw (nSL c) * (weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4 * (gTw (nSL c))⁻¹ =
      cocyc c * weylG2 ^ 4 := by
    rw [cocyc]
    group
  have hrs : sElt hω3 * r = r * sElt hω3 := commute_of_diag hsc hr
  have hr's : sElt hω3 * bcAd σ r = bcAd σ r * sElt hω3 := commute_of_diag hsc hr'
  have hrr' : r * bcAd σ r = bcAd σ r * r := commute_of_diag hr hr'
  have hsrr' : sElt hω3 * (r * bcAd σ r) = bcAd σ r * r * sElt hω3 := by
    rw [← mul_assoc, hrs, mul_assoc, hr's, ← mul_assoc, hrr']
  unfold yP
  rw [map_mul, map_mul, hs, hW]
  calc gTw (nSL c) * (bcAd σ r * ((sElt hω3)⁻¹ * (weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4)) *
        (gTw (nSL c))⁻¹ =
      (gTw (nSL c) * bcAd σ r * (gTw (nSL c))⁻¹) *
        (gTw (nSL c) * (sElt hω3)⁻¹ * (gTw (nSL c))⁻¹) *
        (gTw (nSL c) * (weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4 * (gTw (nSL c))⁻¹) := by group
    _ = (bcAd σ r)⁻¹ * (sElt hω3 * (r * bcAd σ r)) * (weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4 := by
      rw [h1, h2, h3, hcr]
      group
    _ = r * (sElt hω3 * (weylG2 : ↥(adjointGroup Tag.D4 L)) ^ 4) := by
      rw [hsrr']
      group

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph.A2Nonsplit
