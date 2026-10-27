module

public import CFSG.CGT.PushingUpLit.BHS6.FaithfulSL

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open Matrix
open scoped MatrixGroups

section E9

variable {V : Type*} [Group V]

@[expose] def autFixSub (σ : MulAut V) : Subgroup V := MonoidHom.eqLocus (σ : V →* V) (MonoidHom.id V)

theorem mem_autFixSub {σ : MulAut V} {v : V} : v ∈ autFixSub σ ↔ σ v = v := Iff.rfl

theorem norm_mem_autFixSub (hc : ∀ a b : V, a * b = b * a) {σ : MulAut V} (h3 : σ ^ 3 = 1) (v : V) :
    v * σ v * (σ ^ 2) v ∈ autFixSub σ := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  rw [mem_autFixSub, map_mul, map_mul]
  have h : σ ((σ ^ 2) v) = v := by
    have : (σ ^ 3) v = v := by rw [h3]; rfl
    simpa [pow_succ, mul_comm] using this
  have h2 : σ (σ v) = (σ ^ 2) v := by simp [pow_two]
  rw [h2, h]
  simp only [mul_comm, mul_left_comm]

theorem e9_pair_eq (hc : ∀ a b : V, a * b = b * a) (σ : MulAut V) (v : V) :
    σ v * (σ ^ 2) v = (v * σ v * (σ ^ 2) v) * v⁻¹ := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  simp only [mul_comm, mul_left_comm, mul_inv_cancel_left]

theorem e9_fix (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1) {b x : MulAut V}
    (hb3 : b ^ 3 = 1) (hx3 : x ^ 3 = 1) (hbx : Commute b x) (F : Subgroup V) (hFb : autFixSub b = F) (hFx : autFixSub x = F)
    (hFbx : autFixSub (b * x) = F) (hFbx2 : autFixSub (b * x ^ 2) = F) : F = ⊤ := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hc }
  have hbx3 : (b * x) ^ 3 = 1 := by
    rw [(hbx.mul_pow 3), hb3, hx3, one_mul]
  have hbx23 : (b * x ^ 2) ^ 3 = 1 := by
    have hc : Commute b (x ^ 2) := hbx.pow_right 2
    rw [hc.mul_pow, hb3, ← pow_mul, show 2 * 3 = 3 * 2 by rfl, pow_mul, hx3, one_pow, one_mul]
  have hsq : ∀ w : V, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_right (hV w)
  rw [eq_top_iff]
  intro v _
  set n : V := v * x v * (x ^ 2) v with hn
  have hnF : n ∈ F := hFx ▸ norm_mem_autFixSub hc hx3 v
  have hbn : b n = n := (hFb ▸ hnF : n ∈ autFixSub b)
  have hb2n : (b ^ 2) n = n := by rw [pow_two, MulAut.mul_apply, hbn, hbn]
  have e1 : b n = b v * (b * x) v * (b * x ^ 2) v := by
    simp only [hn, map_mul, MulAut.mul_apply]
  have e2 : (b ^ 2) n = (b ^ 2) v * (b ^ 2 * x) v * (b ^ 2 * x ^ 2) v := by
    simp only [hn, map_mul, MulAut.mul_apply]
  have hbx2 : (b * x) ^ 2 = b ^ 2 * x ^ 2 := by
    rw [hbx.mul_pow]
  have hbx22 : (b * x ^ 2) ^ 2 = b ^ 2 * x := by
    have hc : Commute b (x ^ 2) := hbx.pow_right 2
    rw [hc.mul_pow, ← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_add, hx3, one_mul, pow_one]
  have key : (b v * (b ^ 2) v) * ((b * x) v * ((b * x) ^ 2) v) *
      ((b * x ^ 2) v * ((b * x ^ 2) ^ 2) v) = 1 := by
    have h1 : b n * (b ^ 2) n = 1 := by rw [hbn, hb2n]; exact hV n
    rw [e1, e2] at h1
    rw [hbx2, hbx22]
    rw [← h1]
    simp only [mul_comm, mul_left_comm]
  rw [e9_pair_eq hc b v, e9_pair_eq hc (b * x) v, e9_pair_eq hc (b * x ^ 2) v] at key
  have hABC : (v * b v * (b ^ 2) v) * (v * (b * x) v * ((b * x) ^ 2) v) *
      (v * (b * x ^ 2) v * ((b * x ^ 2) ^ 2) v) = v := by
    generalize v * b v * (b ^ 2) v = A at key ⊢
    generalize v * (b * x) v * ((b * x) ^ 2) v = B at key ⊢
    generalize v * (b * x ^ 2) v * ((b * x ^ 2) ^ 2) v = C at key ⊢
    simp only [hsq] at key
    have h4 : A * B * C * v = 1 := by
      have : A * B * C * (v * v * v) = 1 := by
        rw [← key]; simp only [mul_comm, mul_left_comm]
      rwa [show v * v * v = v by rw [hV v, one_mul]] at this
    exact (eq_inv_of_mul_eq_one_left h4).trans (hsq v)
  have h1 : v * b v * (b ^ 2) v ∈ F := hFb ▸ norm_mem_autFixSub hc hb3 v
  have h2 : v * (b * x) v * ((b * x) ^ 2) v ∈ F := hFbx ▸ norm_mem_autFixSub hc hbx3 v
  have h3 : v * (b * x ^ 2) v * ((b * x ^ 2) ^ 2) v ∈ F := hFbx2 ▸ norm_mem_autFixSub hc hbx23 v
  rw [← hABC]
  exact F.mul_mem (F.mul_mem h1 h2) h3

@[expose] def autFixGrp (Γ : Subgroup (MulAut V)) : Subgroup V := ⨅ g : Γ, autFixSub (g : MulAut V)

theorem mem_autFixGrp {Γ : Subgroup (MulAut V)} {v : V} : v ∈ autFixGrp Γ ↔ ∀ g ∈ Γ, g v = v := by
  simp only [autFixGrp, Subgroup.mem_iInf, Subtype.forall]
  rfl

theorem autFixSub_conj {Γ : Subgroup (MulAut V)} {b g : MulAut V} (hg : g ∈ Γ)
    (hF : autFixSub b = autFixGrp Γ) : autFixSub (g * b * g⁻¹) = autFixGrp Γ := by
  ext v
  rw [mem_autFixSub]
  constructor
  · intro h
    have h1 : b (g⁻¹ v) = g⁻¹ v := by
      have := congrArg (fun w => g⁻¹ w) h
      simpa [MulAut.mul_apply] using this
    have h2 : g⁻¹ v ∈ autFixGrp Γ := hF ▸ h1
    have h3 := (mem_autFixGrp.mp h2) g hg
    have h4 : g⁻¹ v = v := by
      have := congrArg (fun w => g⁻¹ w) h3
      simpa using this.symm
    rw [← h4]; exact h2
  · intro h
    have h3 := (mem_autFixGrp.mp h) g hg
    have h5 := (mem_autFixGrp.mp h) g⁻¹ (Γ.inv_mem hg)
    have h6 : b v = v := (hF ▸ h : v ∈ autFixSub b)
    simp [MulAut.mul_apply, h5, h6, h3]

theorem e9_count [Finite V] (hc : ∀ a b : V, a * b = b * a) (hV : ∀ v : V, v * v = 1)
    (Γ : Subgroup (MulAut V)) {b x : MulAut V}
    (hbΓ : b ∈ Γ) (hb3 : b ^ 3 = 1) (hx3 : x ^ 3 = 1) (hbx : Commute b x)
    (hxc : ∃ g ∈ Γ, x = g * b * g⁻¹) (hbxc : ∃ g ∈ Γ, b * x = g * b * g⁻¹)
    (hbx2c : ∃ g ∈ Γ, b * x ^ 2 = g * b * g⁻¹)
    (hidx : (autFixGrp Γ).index ≤ (autFixSub b).index) : autFixSub b = ⊤ := by
  have hle : autFixGrp Γ ≤ autFixSub b := fun v hv => (mem_autFixGrp.mp hv) b hbΓ
  have hfin : (autFixGrp Γ).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hrel := Subgroup.relIndex_mul_index hle
  have hF : autFixSub b = autFixGrp Γ := by
    have h1 : (autFixSub b).index ≤ (autFixGrp Γ).index := Subgroup.index_antitone hle
    have h2 : (autFixGrp Γ).index = (autFixSub b).index := le_antisymm hidx h1
    have h3 : (autFixGrp Γ).relIndex (autFixSub b) = 1 := by
      rw [h2] at hrel
      have hpos : 0 < (autFixSub b).index := Nat.pos_of_ne_zero (h2 ▸ hfin)
      exact (Nat.mul_eq_right hpos.ne').mp hrel
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h3) hle
  obtain ⟨g1, hg1, hx⟩ := hxc
  obtain ⟨g2, hg2, hbx'⟩ := hbxc
  obtain ⟨g3, hg3, hbx2'⟩ := hbx2c
  have hFx : autFixSub x = autFixGrp Γ := by rw [hx]; exact autFixSub_conj hg1 hF
  have hFbx : autFixSub (b * x) = autFixGrp Γ := by rw [hbx']; exact autFixSub_conj hg2 hF
  have hFbx2 : autFixSub (b * x ^ 2) = autFixGrp Γ := by rw [hbx2']; exact autFixSub_conj hg3 hF
  have := e9_fix hc hV hb3 hx3 hbx (autFixGrp Γ) hF hFx hFbx hFbx2
  rw [hF]; exact this


end E9

section NaturalSL

theorem fixed_vec_eq_zero_of_order_three {K : Type*} [Field K] [CharP K 2] {x : SL(2, K)}
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) (v : Fin 2 → K) (hv : (x : Matrix (Fin 2) (Fin 2) K).mulVec v = v) :
    v = 0 := by
  by_contra hv0
  set M : Matrix (Fin 2) (Fin 2) K := (x : Matrix (Fin 2) (Fin 2) K) with hM
  have hdet : M.det = 1 := x.2
  have hsing : (M - 1).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    exact ⟨v, hv0, by rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, sub_self]⟩
  rw [Matrix.det_fin_two] at hdet hsing
  simp only [Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hsing
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have htr : M 0 0 + M 1 1 = 0 := by
    have : (M 0 0 - 1) * (M 1 1 - 1) - M 0 1 * M 1 0 =
        (M 0 0 * M 1 1 - M 0 1 * M 1 0) - (M 0 0 + M 1 1) + 1 := by ring
    rw [this, hdet] at hsing
    linear_combination -hsing + h2
  have hd : M 1 1 = M 0 0 := by
    linear_combination htr + (-(M 0 0)) * h2
  rw [hd] at hdet htr
  have hMM : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hd]
    · linear_combination hdet + (M 0 1 * M 1 0) * h2
    · linear_combination (M 0 1) * htr
    · linear_combination (M 1 0) * htr
    · linear_combination hdet + (M 0 1 * M 1 0) * h2
  have hx2 : x * x = 1 := by
    apply Subtype.ext
    exact hMM
  apply hx1
  calc x = x * (x * x) := by rw [hx2, mul_one]
    _ = x ^ 3 := (pow_three x).symm
    _ = 1 := hx3


variable {K : Type*} [Field K]

@[expose] def slAut (g : SL(2, K)) : MulAut (Multiplicative (Fin 2 → K)) where
  toFun v := Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v))
  invFun v := Multiplicative.ofAdd
    (((g⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v))
  left_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    simp
  right_inv v := by
    simp only [toAdd_ofAdd, Matrix.mulVec_mulVec]
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel]
    simp
  map_mul' u v := by
    show Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K).mulVec
      (Multiplicative.toAdd u + Multiplicative.toAdd v)) = _
    rw [Matrix.mulVec_add, ofAdd_add]

theorem slAut_apply (g : SL(2, K)) (v : Multiplicative (Fin 2 → K)) :
    slAut g v = Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) K).mulVec (Multiplicative.toAdd v)) :=
  rfl

theorem slAut_mul (g h : SL(2, K)) : slAut (g * h) = slAut g * slAut h := by
  ext v
  simp only [slAut_apply, MulAut.mul_apply, toAdd_ofAdd, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mulVec_mulVec]

theorem slAut_one : slAut (1 : SL(2, K)) = 1 := by
  ext v
  simp [slAut_apply]




@[expose] def slAutHom (K : Type*) [Field K] : SL(2, K) →* MulAut (Multiplicative (Fin 2 → K)) where
  toFun := slAut
  map_one' := slAut_one
  map_mul' := slAut_mul

theorem card_sl2_gf8 : Nat.card SL(2, GaloisField 2 3) = 504 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.CGT.PushingUpLit.BHS6.card_SL2_eq, GaloisField.card 2 3 (by norm_num)]
  norm_num

theorem exists_orderOf_nine : ∃ c : SL(2, GaloisField 2 3), orderOf c = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 SL(2, GaloisField 2 3)) := inferInstance
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup SL(2, GaloisField 2 3), Q = (P : Subgroup _) := ⟨_, rfl⟩
  have hQcard : Nat.card Q = 3 ^ 2 := by
    rw [hQ]
    have := Sylow.card_eq_multiplicity P
    rw [card_sl2_gf8, Nat.factorization_def 504 Nat.prime_three] at this
    have h : (504 : ℕ) = 3 ^ 2 * 56 := by norm_num
    rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd (by norm_num)] at this
    simpa using this
  by_contra hno
  push Not at hno
  have hord : ∀ g : Q, g ^ 3 = 1 := by
    intro g
    have h9 : orderOf g ∣ 9 := by
      have := orderOf_dvd_natCard g
      rwa [hQcard] at this
    have hne : orderOf g ≠ 9 := by
      intro h
      apply hno (g : SL(2, GaloisField 2 3))
      rw [← h]
      exact Subgroup.orderOf_coe g
    have h3 : orderOf g ∣ 3 := by
      have : orderOf g ∣ 3 ^ 2 := by simpa using h9
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
      interval_cases k
      · simp [hk']
      · simp [hk']
      · exact absurd hk' hne
    exact orderOf_dvd_iff_pow_eq_one.mp h3
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hQcard
  have hnt : Nontrivial Q := Finite.one_lt_card_iff_nontrivial.mp (by rw [hQcard]; norm_num)
  obtain ⟨b, hb1⟩ : ∃ b : Q, b ≠ 1 := exists_ne 1
  obtain ⟨y, hy⟩ : ∃ y : Q, y ∉ Subgroup.zpowers b := by
    by_contra h
    push Not at h
    have htop : Subgroup.zpowers b = ⊤ := eq_top_iff.mpr fun z _ => h z
    have h1 := Nat.card_zpowers b
    rw [htop, Subgroup.card_top, hQcard] at h1
    have h2 : orderOf b ∣ 3 := orderOf_dvd_of_pow_eq_one (hord b)
    have h3 := Nat.le_of_dvd (by norm_num) h2
    omega
  have hy1 : y ≠ 1 := fun h => hy (h ▸ (Subgroup.zpowers b).one_mem)
  have hby1 : b * y ≠ 1 := by
    intro h
    apply hy
    have : y = b⁻¹ := eq_inv_of_mul_eq_one_right h
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)
  have hby2 : b * y ^ 2 ≠ 1 := by
    intro h
    apply hy
    have h2 : y ^ 2 = b⁻¹ := eq_inv_of_mul_eq_one_right h
    have h3 : y = (y ^ 2) ^ 2 := by
      calc y = y ^ 3 * y := by rw [hord y, one_mul]
        _ = (y ^ 2) ^ 2 := by group
    rw [h3, h2]
    exact Subgroup.pow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)) 2
  have hch : (2 : GaloisField 2 3) = 0 := CharP.cast_eq_zero (GaloisField 2 3) 2
  have hfix : ∀ e : Q, e ≠ 1 →
      autFixSub (slAutHom (GaloisField 2 3) (e : SL(2, GaloisField 2 3))) = ⊥ := by
    intro e he
    rw [eq_bot_iff]
    intro v hv
    rw [mem_autFixSub] at hv
    have hv' : (((e : SL(2, GaloisField 2 3)) : Matrix (Fin 2) (Fin 2) (GaloisField 2 3)).mulVec
        (Multiplicative.toAdd v)) = Multiplicative.toAdd v := by
      have := congrArg Multiplicative.toAdd hv
      exact this
    have hz := fixed_vec_eq_zero_of_order_three (K := GaloisField 2 3)
      (by rw [← Subgroup.coe_pow, hord e]; rfl) (fun h => he (Subtype.ext h)) _ hv'
    have : v = 1 := by
      have : Multiplicative.toAdd v = 0 := hz
      exact (toAdd_eq_zero).mp this
    rw [this]; exact Subgroup.one_mem _
  have hV : ∀ v : Multiplicative (Fin 2 → GaloisField 2 3), v * v = 1 := by
    intro v
    rw [← ofAdd_toAdd v, ← ofAdd_add, ← ofAdd_zero]
    congr 1
    ext i
    simp [CharTwo.add_self_eq_zero]
  have hbc : (b : SL(2, GaloisField 2 3)) * y = y * b := by
    have := hcomm.is_comm.comm b y
    have h := congrArg Subtype.val this
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h
    exact h
  have h1 := hfix b hb1
  have h2 := hfix y hy1
  have h3 := hfix (b * y) hby1
  have h4 := hfix (b * y ^ 2) hby2
  simp only [Subgroup.coe_mul, Subgroup.coe_pow, map_mul, map_pow] at h3 h4
  have hcomm' : Commute (slAutHom (GaloisField 2 3) (b : SL(2, GaloisField 2 3)))
      (slAutHom (GaloisField 2 3) (y : SL(2, GaloisField 2 3))) := by
    show _ * _ = _ * _
    rw [← map_mul, ← map_mul, hbc]
  have hb3 : slAutHom (GaloisField 2 3) (b : SL(2, GaloisField 2 3)) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hord b]; simp
  have hy3 : slAutHom (GaloisField 2 3) (y : SL(2, GaloisField 2 3)) ^ 3 = 1 := by
    rw [← map_pow, ← Subgroup.coe_pow, hord y]; simp
  have := e9_fix (fun a b => mul_comm a b) hV hb3 hy3 hcomm' ⊥ h1 h2 h3 h4
  have hv0 : (Multiplicative.ofAdd (![1, 0] : Fin 2 → GaloisField 2 3)) ∈ (⊤ : Subgroup _) :=
    Subgroup.mem_top _
  rw [← this] at hv0
  have h6 : (![1, 0] : Fin 2 → GaloisField 2 3) = 0 := ofAdd_eq_one.mp ((Subgroup.mem_bot).mp hv0)
  have h7 := congrFun h6 0
  simp at h7



end NaturalSL

end CFSG.CGT.PushingUpLit.CGT6
