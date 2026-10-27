module

public import CFSG.GH74.QTGen4.Recog.G23.P7.LeafWrappers
public import CFSG.GH74.QTGen4.Recog.G23.HLettersF
public import CFSG.GH74.QTGen4.Recog.G23.HLettersG
public import CFSG.GH74.QTGen4.Recog.G23.HLettersI
public import CFSG.GH74.QTGen4.Recog.G23.HLettersJ
public import CFSG.GH74.QTGen4.Recog.G23.HLettersD
public import CFSG.GH74.QTGen4.Recog.G23.HInv
public import CFSG.GH74.QTGen4.Recog.G23.MSylowE

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

open scoped MatrixGroups

theorem lettersH_pow12 : ∀ A : M2, A.det = 1 → A ^ 12 = 1 := by
  decide +kernel

theorem lettersH_mx_mxi : mx * mxi = 1 := by
  rw [mx_eq, mxi_eq]; decide +kernel

theorem lettersH_my_myi : my * myi = 1 := by
  rw [my_eq, myi_eq]; decide +kernel

theorem lettersH_mx_msig : mx * msig * mx * msig = 1 := by
  calc mx * msig * mx * msig = mx * (msig * mx * msig) := by simp only [mul_assoc]
    _ = mx * mxi := by rw [msig_mul_mx_mul_msig]
    _ = 1 := lettersH_mx_mxi

theorem lettersH_my_msig : my * msig * my * msig = 1 := by
  calc my * msig * my * msig = my * (msig * my * msig) := by simp only [mul_assoc]
    _ = my * myi := by rw [msig_mul_my_mul_msig]
    _ = 1 := lettersH_my_myi

theorem lettersH_conj_fin : ∀ g : M2, g.det = 1 →
    (g * mx * !![g 1 1, -g 0 1; -g 1 0, g 0 0] * mx) ^ 4 ≠ 1 := by
  rw [mx_eq]; decide +kernel

theorem lettersH_inv_eq_adj {g g' : M2} (h : g * g' = 1) (hd : g.det = 1) :
    g' = !![g 1 1, -g 0 1; -g 1 0, g 0 0] := by
  rw [show !![g 1 1, -g 0 1; -g 1 0, g 0 0] = Matrix.adjugate g from
    (Matrix.adjugate_fin_two g).symm]
  calc g' = (Matrix.adjugate g * g) * g' := by rw [Matrix.adjugate_mul, hd, one_smul, one_mul]
    _ = Matrix.adjugate g * (g * g') := by rw [mul_assoc]
    _ = Matrix.adjugate g := by rw [h, mul_one]

theorem lettersH_slZ_val : slZ.1 = -1 := by
  have h : (slX * slY * (slX * slY)).1 = slZ.1 := congrArg Subtype.val sl_letter_rels.2.2.2
  rw [← h, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, slX_val,
    slY_val]
  exact sl_xy_sq

theorem lettersH_slZ_sq : slZ * slZ = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, lettersH_slZ_val]
  simp

theorem lettersH_slZ_ne_one : slZ ≠ 1 := by
  intro h
  have h' := congrArg Subtype.val h
  rw [lettersH_slZ_val, Matrix.SpecialLinearGroup.coe_one] at h'
  exact absurd h' (by decide +kernel)

theorem lettersH_closure_eq {K : Subgroup G} (ψ : ↥K ≃* SL(2, ZMod 3)) {x y : ↥K}
    (h : Subgroup.closure ({ψ x, ψ y} : Set SL(2, ZMod 3)) = ⊤) :
    Subgroup.closure ({(x : G), (y : G)} : Set G) = K := by
  set S : Subgroup ↥K := Subgroup.closure ({x, y} : Set ↥K) with hS
  have hmap : S.map ψ.toMonoidHom = ⊤ := by
    rw [hS, MonoidHom.map_closure]
    have himg : ψ.toMonoidHom '' ({x, y} : Set ↥K) = {ψ x, ψ y} := by
      simp [Set.image_pair]
    rw [himg, h]
  have hS_top : S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : ψ z ∈ S.map ψ.toMonoidHom := by
      rw [hmap]; exact Subgroup.mem_top _
    obtain ⟨u, hu, huz⟩ := Subgroup.mem_map.mp hz
    have hEq : u = z := ψ.injective huz
    rw [← hEq]
    exact hu
  calc Subgroup.closure ({(x : G), (y : G)} : Set G) = S.map K.subtype := by
        rw [hS, MonoidHom.map_closure]
        simp
    _ = K := by
        rw [hS_top, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem lettersH_pow_four {X : Type*} [Group X] (x : X) (h12 : x ^ 12 = 1) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : x ^ 4 = 1 := by
  have h1 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf x ∣ 12 := orderOf_dvd_of_pow_eq_one h12
  obtain ⟨i, -, hoi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
  have h3 : 2 ^ i ∣ 12 := hoi ▸ h2
  have h4 : i ≤ 2 := by
    by_contra hc
    have h8 : 2 ^ 3 ∣ 12 := (pow_dvd_pow 2 (by omega : 3 ≤ i)).trans h3
    norm_num at h8
  have h5 : orderOf x ∣ 4 := by
    rw [hoi]
    exact (pow_dvd_pow 2 h4).trans (by norm_num)
  exact orderOf_dvd_iff_pow_eq_one.mp h5

theorem lettersH_pow_two_of_mem_pCore {H : Subgroup G} {g : G}
    (hg : g ∈ CFSG.Open.pCoreOf 2 H) : ∃ k : ℕ, g ^ 2 ^ k = 1 := by
  unfold CFSG.Open.pCoreOf at hg
  rw [open_pCore_eq, Subgroup.mem_map] at hg
  obtain ⟨x, hx, hxg⟩ := hg
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨x, hx⟩
  have h2 : x ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  refine ⟨k, ?_⟩
  have h1 : (x : G) ^ 2 ^ k = 1 := by
    rw [← Subgroup.coe_pow, h2, Subgroup.coe_one]
  rw [← hxg]
  exact h1

@[expose] def lettersHConj {K : Subgroup G} {w : G} (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) : K →* K where
  toFun u := ⟨w * u * w⁻¹, hw u u.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' u v := Subtype.ext (by simp [mul_assoc])

theorem lettersHConj_val {K : Subgroup G} {w : G} (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) (u : K) :
    ((lettersHConj hw u : K) : G) = w * u * w⁻¹ := rfl

theorem lettersHConj_conj {K : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) (u : K) : lettersHConj hw (lettersHConj hw u) = u := by
  apply Subtype.ext
  rw [lettersHConj_val, lettersHConj_val, inv_eq_of_mul_eq_one_right hw2]
  calc w * (w * u * w) * w = (w * w) * u * (w * w) := by group
    _ = u := by rw [hw2]; simp

@[expose] def lettersHAlpha {K : Subgroup G} {w : G} (ψ : ↥K ≃* SL(2, ZMod 3))
    (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) : SL(2, ZMod 3) →* SL(2, ZMod 3) :=
  ψ.toMonoidHom.comp ((lettersHConj hw).comp ψ.symm.toMonoidHom)

theorem lettersHAlpha_apply {K : Subgroup G} {w : G} (ψ : ↥K ≃* SL(2, ZMod 3))
    (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) (A : SL(2, ZMod 3)) :
    lettersHAlpha ψ hw A = ψ (lettersHConj hw (ψ.symm A)) := rfl

theorem lettersHAlpha_alpha {K : Subgroup G} {w : G} (ψ : ↥K ≃* SL(2, ZMod 3))
    (hw2 : w * w = 1) (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) (A : SL(2, ZMod 3)) :
    lettersHAlpha ψ hw (lettersHAlpha ψ hw A) = A := by
  rw [lettersHAlpha_apply, lettersHAlpha_apply, MulEquiv.symm_apply_apply,
    lettersHConj_conj hw2, MulEquiv.apply_symm_apply]

@[expose] def lettersHSlConj {g g' : M2} (h1 : g * g' = 1) (h2 : g' * g = 1) :
    SL(2, ZMod 3) ≃* SL(2, ZMod 3) where
  toFun M := ⟨g * M.1 * g', by rw [gap2_det_conj h1]; exact M.2⟩
  invFun M := ⟨g' * M.1 * g, by rw [gap2_det_conj h2]; exact M.2⟩
  left_inv M := Subtype.ext (by
    show g' * (g * M.1 * g') * g = M.1
    calc g' * (g * M.1 * g') * g = (g' * g) * M.1 * (g' * g) := by simp only [mul_assoc]
      _ = M.1 := by rw [h2, one_mul, mul_one])
  right_inv M := Subtype.ext (by
    show g * (g' * M.1 * g) * g' = M.1
    calc g * (g' * M.1 * g) * g' = (g * g') * M.1 * (g * g') := by simp only [mul_assoc]
      _ = M.1 := by rw [h1, one_mul, mul_one])
  map_mul' M N := Subtype.ext (by
    show g * (M.1 * N.1) * g' = (g * M.1 * g') * (g * N.1 * g')
    calc g * (M.1 * N.1) * g' = g * M.1 * (g' * g) * N.1 * g' := by
          rw [h2]; simp only [mul_one, mul_assoc]
      _ = (g * M.1 * g') * (g * N.1 * g') := by simp only [mul_assoc])

theorem lettersH_conj_key {k h A m : M2} (hkh : k * h = 1) (hhk : h * k = 1)
    (hA : A * m * A * m = 1) : (k * A * h) * (k * m * h * (k * A * h) * (k * m * h)) = 1 := by
  have hl : ∀ X : M2, h * (k * X) = X := fun X => by rw [← mul_assoc, hhk, one_mul]
  calc (k * A * h) * (k * m * h * (k * A * h) * (k * m * h))
      = k * (A * m * A * m) * h := by simp only [mul_assoc, hl]
    _ = 1 := by rw [hA, mul_one, hkh]

theorem lettersH_cancel {g g' : M2} (h2 : g' * g = 1) (X : M2) :
    (g * (g * X * g') * g') * (g * g) = g * g * X := by
  have e1 : ∀ Y : M2, g' * (g * Y) = Y := fun Y => by rw [← mul_assoc, h2, one_mul]
  simp only [mul_assoc, e1, h2, mul_one]

theorem lettersH_side {H K : Subgroup G} {w : G} (hw2 : w * w = 1)
    (hw : ∀ u ∈ K, w * u * w⁻¹ ∈ K) (ψ : ↥K ≃* SL(2, ZMod 3))
    {p q z : G} (hp : p ∈ K) (hq : q ∈ K) (hz : z ∈ K)
    (hψp : ψ ⟨p, hp⟩ = slX) (hψq : ψ ⟨q, hq⟩ = slY) (hψz : ψ ⟨z, hz⟩ = slZ)
    (hpin : w * p * w⁻¹ * p ∈ CFSG.Open.pCoreOf 2 H) :
    ∃ p' q' : G, p' ∈ K ∧ q' ∈ K ∧ Subgroup.closure ({p', q'} : Set G) = K ∧
      w * p' * w⁻¹ = p'⁻¹ ∧ w * q' * w⁻¹ = q'⁻¹ ∧
      p' * p' * p' = 1 ∧ q' * q' * q' = 1 ∧ q'⁻¹ * p'⁻¹ * q' * p'⁻¹ * q'⁻¹ * p' = 1 ∧
      p' * q' * (p' * q') = z := by
  obtain ⟨rX3, rY3, rC, rXY⟩ := sl_letter_rels
  obtain ⟨α, hα⟩ : ∃ α : SL(2, ZMod 3) →* SL(2, ZMod 3), α = lettersHAlpha ψ hw :=
    ⟨_, rfl⟩
  have hαapp : ∀ u : ↥K, ψ (lettersHConj hw u) = α (ψ u) := by
    intro u
    rw [hα, lettersHAlpha_apply, MulEquiv.symm_apply_apply]
  have hαinv : ∀ A, α (α A) = A := by
    intro A
    rw [hα]
    exact lettersHAlpha_alpha ψ hw2 hw A
  have hslZ_sq : slZ * slZ = 1 := lettersH_slZ_sq
  have hAZ : α slZ = slZ := by
    have h1 : α slZ * α slZ = 1 := by rw [← map_mul, hslZ_sq, map_one]
    have h2 : α slZ ≠ 1 := by
      intro h
      apply lettersH_slZ_ne_one
      rw [← hαinv slZ, h, map_one]
    apply Subtype.ext
    rw [lettersH_slZ_val]
    exact sl_unique_invol _ (α slZ).2
      (by
        have h1' := congrArg Subtype.val h1
        simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h1')
      (fun h' => h2 (Subtype.ext (by rw [h', Matrix.SpecialLinearGroup.coe_one])))
  have hAX : α slX * α slX * α slX = 1 := by rw [← map_mul, ← map_mul, rX3, map_one]
  have hAY : α slY * α slY * α slY = 1 := by rw [← map_mul, ← map_mul, rY3, map_one]
  have hiX : (α slX)⁻¹ = α slX * α slX :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hAX)
  have hiY : (α slY)⁻¹ = α slY * α slY :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact hAY)
  have hrelS : α slY * α slY * (α slX * α slX) * α slY * (α slX * α slX) *
      (α slY * α slY) * α slX = 1 := by
    have h := congrArg α rC
    simp only [map_mul, map_inv, map_one, hiX, hiY] at h
    exact h
  have hXX : (α slX).1 * (α slX).1 * (α slX).1 = 1 := by
    have h := congrArg Subtype.val hAX
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hYY : (α slY).1 * (α slY).1 * (α slY).1 = 1 := by
    have h := congrArg Subtype.val hAY
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hrelM : (α slY).1 * (α slY).1 * ((α slX).1 * (α slX).1) * (α slY).1 *
      ((α slX).1 * (α slX).1) * ((α slY).1 * (α slY).1) * (α slX).1 = 1 := by
    have h := congrArg Subtype.val hrelS
    simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one] using h
  have hXYZ : α slX * α slY * (α slX * α slY) = slZ := by
    have h := congrArg α rXY
    simp only [map_mul] at h
    exact h.trans hAZ
  have hXYM : (α slX).1 * (α slY).1 * ((α slX).1 * (α slY).1) = -1 := by
    have h := congrArg Subtype.val hXYZ
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      lettersH_slZ_val] at h
    exact h
  obtain ⟨g, hg0, hgx, hgy⟩ := gap2_conj_exists (α slX).1 (α slY).1 hXX hYY hrelM hXYM
  obtain ⟨g', hgg', hg'g⟩ := gap2_inv_exists g hg0
  have hαcg : α = (lettersHSlConj hgg' hg'g).toMonoidHom := by
    apply MonoidHom.eq_of_eqOn_dense sl_closure_top
    intro A hA
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hA
    rcases hA with rfl | rfl
    · apply Subtype.ext
      show (α slX).1 = g * slX.1 * g'
      rw [slX_val]
      calc (α slX).1 = (α slX).1 * (g * g') := by rw [hgg', mul_one]
        _ = (α slX).1 * g * g' := by rw [mul_assoc]
        _ = g * mx * g' := by rw [← hgx]
    · apply Subtype.ext
      show (α slY).1 = g * slY.1 * g'
      rw [slY_val]
      calc (α slY).1 = (α slY).1 * (g * g') := by rw [hgg', mul_one]
        _ = (α slY).1 * g * g' := by rw [mul_assoc]
        _ = g * my * g' := by rw [← hgy]
  have hαmat : ∀ A : SL(2, ZMod 3), (α A).1 = g * A.1 * g' := by
    intro A
    rw [hαcg]
    rfl
  rcases gap2_det_pm g.det hg0 with hd1 | hdm1
  ·
    exfalso
    obtain ⟨n, hn⟩ := lettersH_pow_two_of_mem_pCore hpin
    have hψt : ψ (lettersHConj hw ⟨p, hp⟩ * ⟨p, hp⟩) = α slX * slX := by
      rw [map_mul, hαapp, hψp]
    have hcoe : ((lettersHConj hw ⟨p, hp⟩ * ⟨p, hp⟩ : ↥K) : G) = w * p * w⁻¹ * p := by
      rw [Subgroup.coe_mul, lettersHConj_val]
    have hpowK : (lettersHConj hw ⟨p, hp⟩ * ⟨p, hp⟩) ^ 2 ^ n = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hcoe, Subgroup.coe_one]
      exact hn
    have hpowS : (α slX * slX) ^ 2 ^ n = 1 := by
      rw [← hψt, ← map_pow, hpowK, map_one]
    have h4 : (α slX * slX) ^ 4 = 1 := by
      apply lettersH_pow_four _ _ hpowS
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
      exact lettersH_pow12 _ (α slX * slX).2
    have hm : (g * mx * g' * mx) ^ 4 = 1 := by
      have h := congrArg Subtype.val h4
      rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_mul,
        hαmat, slX_val, Matrix.SpecialLinearGroup.coe_one] at h
      exact h
    rw [lettersH_inv_eq_adj hgg' hd1] at hm
    exact lettersH_conj_fin g hd1 hm
  ·
    have hX1 : g * (g * mx * g') * g' = mx := by
      have h := congrArg Subtype.val (hαinv slX)
      rw [hαmat, hαmat, slX_val] at h
      exact h
    have hY1 : g * (g * my * g') * g' = my := by
      have h := congrArg Subtype.val (hαinv slY)
      rw [hαmat, hαmat, slY_val] at h
      exact h
    have hNx : g * g * mx = mx * (g * g) := by
      rw [← lettersH_cancel hg'g mx, hX1]
    have hNy : g * g * my = my * (g * g) := by
      rw [← lettersH_cancel hg'g my, hY1]
    obtain ⟨c, hc⟩ := commutant_scalar (g * g) hNx hNy
    have hc1 : c = 1 := outer_square_scalar g hdm1 c hc
    have hgg : g * g = 1 := by rw [hc, hc1, one_smul]
    have hg'eq : g' = g := by
      calc g' = (g * g) * g' := by rw [hgg, one_mul]
        _ = g * (g * g') := by rw [mul_assoc]
        _ = g := by rw [hgg', mul_one]
    have hαmat' : ∀ A : SL(2, ZMod 3), (α A).1 = g * A.1 * g := fun A => by
      rw [hαmat, hg'eq]
    obtain ⟨h, hh0, hhg⟩ := outer_involution_conj g hdm1 hgg
    obtain ⟨k, hhk1, hkh1⟩ := gap2_inv_exists h hh0
    have hgk : g = k * msig * h := by
      calc g = (k * h) * g := by rw [hkh1, one_mul]
        _ = k * (h * g) := by rw [mul_assoc]
        _ = k * (msig * h) := by rw [hhg]
        _ = k * msig * h := by rw [mul_assoc]
    obtain ⟨β, hβ⟩ : ∃ β : SL(2, ZMod 3) ≃* SL(2, ZMod 3), β = lettersHSlConj hkh1 hhk1 :=
      ⟨_, rfl⟩
    have hβapp : ∀ A : SL(2, ZMod 3), (β A).1 = k * A.1 * h := by
      intro A
      rw [hβ]
      rfl
    have hkey : ∀ A : SL(2, ZMod 3), A.1 * msig * A.1 * msig = 1 → α (β A) = (β A)⁻¹ := by
      intro A hA
      symm
      apply inv_eq_of_mul_eq_one_right
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, hαmat', Matrix.SpecialLinearGroup.coe_one]
      simp only [hβapp]
      rw [hgk]
      exact lettersH_conj_key hkh1 hhk1 hA
    have hβX3 : β slX * β slX * β slX = 1 := by rw [← map_mul, ← map_mul, rX3, map_one]
    have hβY3 : β slY * β slY * β slY = 1 := by rw [← map_mul, ← map_mul, rY3, map_one]
    have hβrel : (β slY)⁻¹ * (β slX)⁻¹ * β slY * (β slX)⁻¹ * (β slY)⁻¹ * β slX = 1 := by
      simp only [← map_inv, ← map_mul, rC, map_one]
    have hβZ : β slZ = slZ := by
      apply Subtype.ext
      rw [hβapp, lettersH_slZ_val]
      simp [Matrix.mul_neg, Matrix.neg_mul, hkh1]
    have hβXY : β slX * β slY * (β slX * β slY) = slZ := by
      have h := congrArg β rXY
      simp only [map_mul] at h
      exact h.trans hβZ
    have hβtop : Subgroup.closure ({β slX, β slY} : Set SL(2, ZMod 3)) = ⊤ := by
      have h1 : Subgroup.closure ({β slX, β slY} : Set SL(2, ZMod 3)) =
          (Subgroup.closure ({slX, slY} : Set SL(2, ZMod 3))).map β.toMonoidHom := by
        rw [MonoidHom.map_closure, Set.image_pair]
        rfl
      rw [h1, sl_closure_top]
      exact Subgroup.map_top_of_surjective β.toMonoidHom β.surjective
    obtain ⟨P, hP⟩ : ∃ P : ↥K, ψ P = β slX := ⟨ψ.symm (β slX), ψ.apply_symm_apply _⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : ↥K, ψ Q = β slY := ⟨ψ.symm (β slY), ψ.apply_symm_apply _⟩
    have hconjP : lettersHConj hw P = P⁻¹ := by
      apply ψ.injective
      rw [hαapp, hP, map_inv, hP]
      exact hkey slX (by rw [slX_val]; exact lettersH_mx_msig)
    have hconjQ : lettersHConj hw Q = Q⁻¹ := by
      apply ψ.injective
      rw [hαapp, hQ, map_inv, hQ]
      exact hkey slY (by rw [slY_val]; exact lettersH_my_msig)
    have hPPP : P * P * P = 1 := ψ.injective (by
      rw [map_mul, map_mul, hP, map_one]; exact hβX3)
    have hQQQ : Q * Q * Q = 1 := ψ.injective (by
      rw [map_mul, map_mul, hQ, map_one]; exact hβY3)
    have hrelK : Q⁻¹ * P⁻¹ * Q * P⁻¹ * Q⁻¹ * P = 1 := ψ.injective (by
      simp only [map_mul, map_inv, map_one, hP, hQ]
      exact hβrel)
    have hPQ : P * Q * (P * Q) = ⟨z, hz⟩ := ψ.injective (by
      simp only [map_mul, hP, hQ, hψz]
      exact hβXY)
    refine ⟨(P : G), (Q : G), P.2, Q.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact lettersH_closure_eq ψ (x := P) (y := Q) (by rw [hP, hQ]; exact hβtop)
    · have h := congrArg Subtype.val hconjP
      rw [lettersHConj_val, Subgroup.coe_inv] at h
      exact h
    · have h := congrArg Subtype.val hconjQ
      rw [lettersHConj_val, Subgroup.coe_inv] at h
      exact h
    · have h := congrArg Subtype.val hPPP
      simpa using h
    · have h := congrArg Subtype.val hQQQ
      simpa using h
    · have h := congrArg Subtype.val hrelK
      simpa using h
    · have h := congrArg Subtype.val hPQ
      simpa using h

theorem leafLettersH [G23Leaf LeafHR] : LeafLettersH := by
  intro G _ _ T H H₁ H₂ M hctx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := hctx.sylow
  have hTM : T ≤ M := hctx.tM
  have hTdvd : (T.subgroupOf M).index ∣ T.index :=
    Dvd.intro _ (Subgroup.relIndex_mul_index hTM)
  have hTidx : ¬ 2 ∣ (T.subgroupOf M).index := fun h => hTs.2 (dvd_trans h hTdvd)
  have hR := exists_hR hctx
  have hcount : Nat.card {t : ↥T // orderOf t = 2} = 27 :=
    G23Two.card_involutions_sylow_of_hR hctx.two hTM hTs.1 hTidx hR
  obtain ⟨w, hwT, hwo, hwK⟩ := G23One.exists_invol_outside hctx.one
    (G23One.card_invol_sup_le hctx.one) (by rw [hcount]; norm_num)
  have hwH : w ∈ H := hctx.tH hwT
  have hw2 : w * w = 1 := by
    have h2 : w ^ orderOf w = 1 := pow_orderOf_eq_one w
    rw [hwo, pow_two] at h2
    exact h2
  have hn₁ : ∀ u ∈ H₁, w * u * w⁻¹ ∈ H₁ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hctx.one.normal_one hwH) u).mp hu
  have hn₂ : ∀ u ∈ H₂, w * u * w⁻¹ ∈ H₂ := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp (hctx.one.normal_two hwH) u).mp hu
  obtain ⟨z, hzI, hz1, -⟩ := G23One.exists_unique_inf hctx.one
  have hz2 : z ^ 2 = 1 := G23One.sq_inf hctx.one hzI
  have hzH₁ : z ∈ H₁ := (Subgroup.mem_inf.mp hzI).1
  have hzH₂ : z ∈ H₂ := (Subgroup.mem_inf.mp hzI).2
  obtain ⟨ψ₁⟩ := hctx.one.iso_one
  obtain ⟨ψ₂⟩ := hctx.one.iso_two
  have hzA : ψ₁ ⟨z, hzH₁⟩ = slZ := invol_eq_slZ ψ₁ hzH₁ hz2 hz1
  have hzB : ψ₂ ⟨z, hzH₂⟩ = slZ := invol_eq_slZ ψ₂ hzH₂ hz2 hz1
  obtain ⟨a, b, ha, hb, hab, hwa, hwb, ra3, rb3, rab3, rabz⟩ :=
    lettersH_side (p := ((ψ₁.symm slX : ↥H₁) : G)) (q := ((ψ₁.symm slY : ↥H₁) : G))
      (z := z) hw2 hn₁ ψ₁ (ψ₁.symm slX).2 (ψ₁.symm slY).2 hzH₁
      (ψ₁.apply_symm_apply slX) (ψ₁.apply_symm_apply slY) hzA
      (hctx.inv w hwH hwK _ (Subgroup.mem_sup_left (ψ₁.symm slX).2))
  obtain ⟨c, d, hc, hd, hcd, hwc, hwd, rc3, rd3, rcd3, rcdz⟩ :=
    lettersH_side (p := ((ψ₂.symm slX : ↥H₂) : G)) (q := ((ψ₂.symm slY : ↥H₂) : G))
      (z := z) hw2 hn₂ ψ₂ (ψ₂.symm slX).2 (ψ₂.symm slY).2 hzH₂
      (ψ₂.apply_symm_apply slX) (ψ₂.apply_symm_apply slY) hzB
      (hctx.inv w hwH hwK _ (Subgroup.mem_sup_right (ψ₂.symm slX).2))
  have hac : Commute a c := G23One.comm_one_two hctx.one ha hc
  have had : Commute a d := G23One.comm_one_two hctx.one ha hd
  have hbc : Commute b c := G23One.comm_one_two hctx.one hb hc
  have hbd : Commute b d := G23One.comm_one_two hctx.one hb hd
  have hG : a * b * (a * b) = c * d * (c * d) := rabz.trans rcdz.symm
  have hsat : SatisfiesWords g23WordsH (![a, b, c, d, w, 1] : Fin 6 → G) :=
    satisfiesWords_g23WordsH_of_relations (![a, b, c, d, w, 1] : Fin 6 → G) ra3 rb3 rab3
      rc3 rd3 rcd3 hG hac had hbc hbd hw2 (mul_self_eq_one_of_inv_conj hw2 hwa)
      (mul_self_eq_one_of_inv_conj hw2 hwb) (mul_self_eq_one_of_inv_conj hw2 hwc)
      (mul_self_eq_one_of_inv_conj hw2 hwd)
  have hset : Set.range (fun i : Fin 5 => (![a, b, c, d, w, 1] : Fin 6 → G) i.castSucc) =
      ({a, b, c, d, w} : Set G) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
      · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
      · exact Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
      · exact Set.mem_insert_of_mem _
          (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
            (Set.mem_insert_of_mem _ (Set.mem_singleton _))))
    · intro hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with h | h | h | h | h
      · exact ⟨0, h ▸ rfl⟩
      · exact ⟨1, h ▸ rfl⟩
      · exact ⟨2, h ▸ rfl⟩
      · exact ⟨3, h ▸ rfl⟩
      · exact ⟨4, h ▸ rfl⟩
  have hgen : Subgroup.closure (Set.range fun i : Fin 5 =>
      (![a, b, c, d, w, 1] : Fin 6 → G) i.castSucc) = H := by
    rw [hset]
    exact G23One.closure_letters_eq hctx.one hab hcd hwH hwK
  exact ⟨![a, b, c, d, w, 1], ⟨hsat, hgen, hab, hcd⟩⟩

end CFSG.GH74.QTGen4.Recog.G23.P7
