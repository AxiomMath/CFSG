module

public import CFSG.CGT.PushingUpLit.A78S4.Side

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.QuasithinUnique.Setup.Offender (IsSemilinearWith aut_involution_unique
  card_eq_sq_of_involution)
open Matrix
open scoped commutatorElement

namespace NatCoordK

variable {G : Type} [Group G] {L V K : Subgroup G} {F : Type} [Field F]
  {D : NatCoordK G L V K F}

theorem act_pow {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G)) (n : ℕ)
    (w : Fin 2 → F) : D.act (x ^ n) w = (D.act x)^[n] w := by
  induction n generalizing w with
  | zero => rw [pow_zero, act_one]; rfl
  | succ n ih =>
    rw [pow_succ, act_mul (pow_mem hx n) hx, ih, ← Function.iterate_succ_apply]

end NatCoordK

namespace S4Side

variable {G : Type} [Group G] [Finite G] {L V W Z T : Subgroup G} {e : ℕ}

namespace Frame

variable {h : S4Side G L V W Z T e} {D : NatCoordK G L V Z (GaloisField 2 e)} (fr : Frame h D)

theorem act_n₀ {t : G} (ht : t ∈ T) :
    ∃ μ : GaloisField 2 e, D.act t (D.κ fr.n₀) = μ • D.κ fr.n₀ := by
  have htn : t * fr.n₀ * t⁻¹ ∈ V ⊓ W :=
    ⟨conj_mem_of_mem_normalizer (h.T_le_V ht) fr.hn₀.1,
      conj_mem_of_mem_normalizer (h.T_le_W ht) fr.hn₀.2⟩
  exact ⟨fr.c (t * fr.n₀ * t⁻¹), by
    rw [NatCoordK.act_κ (h.T_le_NVK ht) fr.hn₀.1]; exact fr.κ_eq_c htn⟩

end Frame

section Sig

variable (h : S4Side G L V W Z T e) (D : NatCoordK G L V Z (GaloisField 2 e))

include h

theorem mem_J_of_linear {t : G} (ht : t ∈ T)
    (hlin : ∀ (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e),
      D.act t (c • w) = c • D.act t w) : t ∈ V ⊔ W := by
  obtain ⟨fr⟩ := h.exists_frame D
  have hx₀ : D.κ fr.n₀ ≠ 0 := D.κ_ne_zero fr.hn₀.1 fr.hn₀Z
  have htK := h.T_le_NVK ht
  obtain ⟨μ, hact0⟩ := fr.act_n₀ ht
  obtain ⟨k, hk⟩ := h.pT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hiter : ∀ n : ℕ, (D.act t)^[n] (D.κ fr.n₀) = μ ^ n • D.κ fr.n₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, hlin, hact0, smul_smul, pow_succ]
  have hμ1 : μ = 1 := by
    have h1 := hiter (2 ^ k)
    rw [← NatCoordK.act_pow htK, htk, NatCoordK.act_one] at h1
    have h2 : (1 : GaloisField 2 e) • D.κ fr.n₀ = μ ^ 2 ^ k • D.κ fr.n₀ := by
      rw [one_smul]; exact h1
    exact L3Side.eq_one_of_pow_two_pow (smul_left_injective _ hx₀ h2).symm
  let M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e) :=
    Matrix.of fun i j => D.act t (Pi.single j 1) i
  have hM : ∀ w, D.act t w = M *ᵥ w := by
    intro w
    have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hw]
    rw [NatCoordK.act_add htK, hlin, hlin]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Fin.sum_univ_two,
      M, Matrix.of_apply]
    ring
  have hMpow : ∀ n : ℕ, ∀ w, (M ^ n) *ᵥ w = D.act (t ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, one_mulVec, pow_zero, NatCoordK.act_one]
    | succ n ih =>
      intro w
      rw [pow_succ, ← mulVec_mulVec, ← hM, ih, ← NatCoordK.act_mul (pow_mem htK n) htK,
        ← pow_succ]
  have hMk : M ^ 2 ^ k = 1 := by
    ext i j
    have := congrFun (hMpow (2 ^ k) (Pi.single j 1)) i
    rw [htk, NatCoordK.act_one, mulVec_single_one] at this
    rw [one_apply]
    simpa [Pi.single_apply, eq_comm] using this
  have hdet : M.det = 1 := by
    apply L3Side.eq_one_of_pow_two_pow (k := k)
    rw [← det_pow, hMk, det_one]
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj ⟨M, hdet⟩
  have hlM' : (D.ρ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hlM]
  have hlJ : l ∈ V ⊔ W := by
    rw [h.mem_J_iff D fr.hn₀ fr.hn₀Z hl, hlM', ← hM, hact0, hμ1, one_smul]
  have hlK := D.le_normVK hl
  have hlt : l⁻¹ * t ∈ V := by
    refine h.cent _ (mul_mem (inv_mem (h.J_le_T hlJ)) ht) fun v hv => ?_
    refine NatCoordK.comm_mem_of_act (D := D) (mul_mem (inv_mem hlK) htK) (fun w => ?_) hv
    rw [NatCoordK.act_mul (inv_mem hlK) htK, hM, ← hlM', ← NatCoordK.act_of_mem_L hl,
      ← NatCoordK.act_mul (inv_mem hlK) hlK, inv_mul_cancel, NatCoordK.act_one]
  have e1 : t = l * (l⁻¹ * t) := by group
  rw [e1]
  exact mul_mem hlJ (Subgroup.mem_sup_left hlt)

theorem linear_of_mem_J {j : G} (hj : j ∈ V ⊔ W) (c : GaloisField 2 e)
    (w : Fin 2 → GaloisField 2 e) : D.act j (c • w) = c • D.act j w := by
  rw [NatCoordK.act_of_mem_L (h.J_le_L hj), NatCoordK.act_of_mem_L (h.J_le_L hj), mulVec_smul]

theorem exists_sig {t : G} (ht : t ∈ T) :
    ∃ σ : GaloisField 2 e ≃+* GaloisField 2 e,
      IsSemilinearWith (D.actPerm t (h.T_le_NVK ht)) σ :=
  NatCoordK.exists_semilinear (h.T_le_L ht) (h.T_le_NVK ht)

omit h in
@[expose] noncomputable def sig (h : S4Side G L V W Z T e) (D : NatCoordK G L V Z (GaloisField 2 e))
    (t : ↥T) : GaloisField 2 e ≃+* GaloisField 2 e :=
  (h.exists_sig D t.2).choose

theorem sig_spec (t : ↥T) : IsSemilinearWith (D.actPerm t (h.T_le_NVK t.2)) (h.sig D t) :=
  (h.exists_sig D t.2).choose_spec

theorem sig_unique (t : ↥T) {σ : GaloisField 2 e ≃+* GaloisField 2 e}
    (hσ : IsSemilinearWith (D.actPerm t (h.T_le_NVK t.2)) σ) : h.sig D t = σ :=
  (h.sig_spec D t).unique hσ

omit h in
@[expose] noncomputable def sigHom (h : S4Side G L V W Z T e)
    (D : NatCoordK G L V Z (GaloisField 2 e)) : ↥T →* (GaloisField 2 e ≃+* GaloisField 2 e) where
  toFun := h.sig D
  map_one' := h.sig_unique D 1 fun c w => by
    show D.act 1 (c • w) = c • D.act 1 w
    rw [NatCoordK.act_one, NatCoordK.act_one]
  map_mul' s t := h.sig_unique D (s * t) fun c w => by
    show D.act ((s : G) * t) (c • w) = (h.sig D s) ((h.sig D t) c) • D.act ((s : G) * t) w
    rw [NatCoordK.act_mul (h.T_le_NVK s.2) (h.T_le_NVK t.2),
      NatCoordK.act_mul (h.T_le_NVK s.2) (h.T_le_NVK t.2)]
    exact ((h.sig_spec D s).mul (h.sig_spec D t)) c w

omit h in
theorem sigHom_apply (h : S4Side G L V W Z T e) (D : NatCoordK G L V Z (GaloisField 2 e))
    (t : ↥T) : h.sigHom D t = h.sig D t := rfl

theorem act_smul {t : G} (ht : t ∈ T) (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e) :
    D.act t (c • w) = h.sig D ⟨t, ht⟩ c • D.act t w :=
  h.sig_spec D ⟨t, ht⟩ c w

theorem sig_eq_one_iff (t : ↥T) : h.sig D t = 1 ↔ (t : G) ∈ V ⊔ W := by
  constructor
  · intro h1
    refine h.mem_J_of_linear D t.2 fun c w => ?_
    rw [h.act_smul D t.2, h1]
    rfl
  · intro hj
    exact h.sig_unique D t fun c w => h.linear_of_mem_J D hj c w

section Involution

variable {a : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W)

include haJ in
theorem sig_ne_one : h.sig D ⟨a, ha⟩ ≠ 1 := fun h1 => haJ ((h.sig_eq_one_iff D ⟨a, ha⟩).1 h1)

include haJ in
theorem exists_sig_ne : ∃ c, h.sig D ⟨a, ha⟩ c ≠ c := by
  by_contra hcon
  push Not at hcon
  exact h.sig_ne_one D ha haJ (RingEquiv.ext hcon)

theorem sig_sq_of_sq_mem (hsq : a * a ∈ V ⊔ W) :
    h.sig D ⟨a, ha⟩ * h.sig D ⟨a, ha⟩ = 1 := by
  have : (⟨a, ha⟩ : ↥T) * ⟨a, ha⟩ = ⟨a * a, mul_mem ha ha⟩ := rfl
  rw [← sigHom_apply, ← map_mul, this, sigHom_apply, h.sig_eq_one_iff D]
  exact hsq

include ha in
theorem act_act_of_sq_mem (hsq : a * a ∈ V) (w : Fin 2 → GaloisField 2 e) :
    D.act a (D.act a w) = w := by
  rw [← NatCoordK.act_mul (h.T_le_NVK ha) (h.T_le_NVK ha)]
  refine NatCoordK.act_of_mem_centralizer (Subgroup.mem_centralizer_iff.2 fun v hv => ?_) w
  exact (h.jst.abelian_V v hv _ hsq).eq

theorem semInv_of_sq_mem (hsq : a * a ∈ V) : SemInv (h.sig D ⟨a, ha⟩) (D.act a) :=
  ⟨fun w w' => NatCoordK.act_add (h.T_le_NVK ha) w w', fun c w => h.act_smul D ha c w,
    fun w => h.act_act_of_sq_mem D ha hsq w⟩

variable (haa : a * a = 1)

include haa in
theorem sig_sq : h.sig D ⟨a, ha⟩ * h.sig D ⟨a, ha⟩ = 1 :=
  h.sig_sq_of_sq_mem D ha (by rw [haa]; exact Subgroup.one_mem _)

include haa in
theorem semInv : SemInv (h.sig D ⟨a, ha⟩) (D.act a) :=
  h.semInv_of_sq_mem D ha (by rw [haa]; exact Subgroup.one_mem _)

include D ha haJ haa in
theorem even_of_involution : Even e := by
  obtain ⟨n, hn, -, -⟩ := card_eq_sq_of_involution (h.sig D ⟨a, ha⟩) (h.sig_ne_one D ha haJ)
    (h.sig_sq D ha haa)
  rw [h.card_F] at hn
  have h1 := congrArg (fun m => Nat.factorization m 2) hn
  simp only [Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul, mul_one] at h1
  exact ⟨n.factorization 2, by omega⟩

end Involution

include D in
theorem mul_mem_J_of_sq_mem {a b : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W) (haa : a * a ∈ V ⊔ W)
    (hb : b ∈ T) (hbJ : b ∉ V ⊔ W) (hbb : b * b ∈ V ⊔ W) : a * b ∈ V ⊔ W := by
  have heq := aut_involution_unique (h.sig D ⟨a, ha⟩) (h.sig D ⟨b, hb⟩)
    (h.sig_sq_of_sq_mem D ha haa) (h.sig_sq_of_sq_mem D hb hbb) (h.sig_ne_one D ha haJ)
    (h.sig_ne_one D hb hbJ)
  have h1 : h.sig D ⟨a * b, mul_mem ha hb⟩ = 1 := by
    have : (⟨a * b, mul_mem ha hb⟩ : ↥T) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, ← sigHom_apply, map_mul, sigHom_apply, sigHom_apply, heq,
      h.sig_sq_of_sq_mem D hb hbb]
  exact (h.sig_eq_one_iff D ⟨a * b, mul_mem ha hb⟩).1 h1

include D in
theorem mul_mem_J_of_involutions {a b : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W) (haa : a * a = 1)
    (hb : b ∈ T) (hbJ : b ∉ V ⊔ W) (hbb : b * b = 1) : a * b ∈ V ⊔ W :=
  h.mul_mem_J_of_sq_mem D ha haJ (by rw [haa]; exact Subgroup.one_mem _) hb hbJ
    (by rw [hbb]; exact Subgroup.one_mem _)

include D in
theorem fixN {x : G} (hx : x ∈ T) (hxJ : x ∉ V ⊔ W) : ∃ v ∈ V, ⁅x, v⁆ ∉ V ⊓ W := by
  by_contra hcon
  push Not at hcon
  obtain ⟨fr⟩ := h.exists_frame D
  have hxK := h.T_le_NVK hx
  obtain ⟨c, hc⟩ := h.exists_sig_ne D hx hxJ
  obtain ⟨v, hv, hvN⟩ : ∃ v ∈ V, v ∉ V ⊓ W := by
    by_contra hcon'
    push Not at hcon'
    exact h.jst.not_le_V₂ fun y hy => (hcon' y hy).2
  have hmod : ∀ u ∈ V, ∃ d : GaloisField 2 e, D.act x (D.κ u) = D.κ u + d • D.κ fr.n₀ := by
    intro u hu
    have h1 := hcon u hu
    obtain ⟨d, hd⟩ : ∃ d : GaloisField 2 e, D.κ ⁅x, u⁆ = d • D.κ fr.n₀ := ⟨_, fr.κ_eq_c h1⟩
    refine ⟨d, ?_⟩
    have e1 : ⁅x, u⁆ = (x * u * x⁻¹) * u⁻¹ := by simp [commutatorElement_def]
    rw [e1, D.κ_mul _ (conj_mem_of_mem_normalizer hxK.1 hu) _ (inv_mem hu), D.κ_inv hu] at hd
    rw [NatCoordK.act_κ hxK hu, ← hd]
    abel
  obtain ⟨d₁, hd₁⟩ := hmod v hv
  have hcv : D.sec (c • D.κ v) ∈ V := D.sec_mem _
  obtain ⟨d₂, hd₂⟩ := hmod _ hcv
  rw [D.κ_sec, h.act_smul D hx, hd₁] at hd₂
  have hline : (h.sig D ⟨x, hx⟩ c - c) • D.κ v = (d₂ - h.sig D ⟨x, hx⟩ c * d₁) • D.κ fr.n₀ := by
    linear_combination (norm := module) hd₂
  have hne : h.sig D ⟨x, hx⟩ c - c ≠ 0 := sub_ne_zero.2 hc
  apply hvN
  rw [fr.mem_N_iff hv]
  have hκv : D.κ v = ((h.sig D ⟨x, hx⟩ c - c)⁻¹ * (d₂ - h.sig D ⟨x, hx⟩ c * d₁)) • D.κ fr.n₀ := by
    rw [mul_smul, ← hline, smul_smul, inv_mul_cancel₀ hne, one_smul]
  rw [hκv, det2_smul_right, det2_self, mul_zero]

end Sig

namespace Frame

variable {h : S4Side G L V W Z T e} {D : NatCoordK G L V Z (GaloisField 2 e)} (fr : Frame h D)

theorem b_conj {t : G} (ht : t ∈ T) :
    ∃ ν, ∀ j ∈ V ⊔ W, fr.b (t * j * t⁻¹) = ν * h.sig D ⟨t, ht⟩ (fr.b j) := by
  obtain ⟨μ, hμ⟩ := fr.act_n₀ ht
  set u := D.act t⁻¹ fr.y₀ with hu
  have htK := h.T_le_NVK ht
  have htL := h.T_le_L ht
  refine ⟨h.sig D ⟨t, ht⟩ (det2 (D.κ fr.n₀) u) * μ, fun j hj => ?_⟩
  have hjL := h.J_le_L hj
  have h1 : (D.ρ (t * j * t⁻¹) : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ fr.y₀ =
      D.act t ((D.ρ j : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ u) := by
    rw [NatCoordK.act_twist htL htK hjL, hu, NatCoordK.act_act_inv htK]
  rw [fr.ρ_mulVec hj, NatCoordK.act_add htK, h.act_smul D ht, hμ, hu,
    NatCoordK.act_act_inv htK, smul_smul, ← hu, map_mul] at h1
  rw [b, h1, det2_add_left, det2_self, zero_add, det2_smul_left, fr.hdet, mul_one]
  ring

theorem c_conj {t : G} (ht : t ∈ T) {μ : GaloisField 2 e}
    (hμ : D.act t (D.κ fr.n₀) = μ • D.κ fr.n₀) {n : G} (hn : n ∈ V ⊓ W) :
    t * n * t⁻¹ ∈ V ⊓ W ∧ fr.c (t * n * t⁻¹) = μ * h.sig D ⟨t, ht⟩ (fr.c n) := by
  have htK := h.T_le_NVK ht
  refine ⟨⟨conj_mem_of_mem_normalizer (h.T_le_V ht) hn.1,
    conj_mem_of_mem_normalizer (h.T_le_W ht) hn.2⟩, ?_⟩
  rw [c, ← NatCoordK.act_κ htK hn.1, fr.κ_eq_c hn, h.act_smul D ht, hμ, smul_smul,
    det2_smul_left, fr.hdet, mul_one, mul_comm]

end Frame

end S4Side

end CFSG.CGT.PushingUpLit.A78S4
