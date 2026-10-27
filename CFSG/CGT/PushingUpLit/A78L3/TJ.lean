module

public import CFSG.CGT.PushingUpLit.A78L3.Side

public section

namespace CFSG.CGT.PushingUpLit.A78L3

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.QuasithinUnique.Setup.Offender (IsSemilinearWith aut_involution_unique
  card_eq_sq_of_involution)
open Matrix
open scoped commutatorElement

namespace L3Side

variable {G : Type} [Group G] [Finite G] {L V W T : Subgroup G} {e : ℕ}
  (h : L3Side G L V W T e) (D : NatCoord G L V (GaloisField 2 e))

include h in
theorem e_ne_zero : e ≠ 0 := by have := h.two_le; omega

omit [Finite G] in
theorem act_pow {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G)) (n : ℕ)
    (w : Fin 2 → GaloisField 2 e) : D.act (x ^ n) w = (D.act x)^[n] w := by
  induction n generalizing w with
  | zero => rw [pow_zero, NatCoord.act_one]; rfl
  | succ n ih =>
    rw [pow_succ, NatCoord.act_mul hx, ih, ← Function.iterate_succ_apply]

omit [Finite G] in
theorem eq_one_of_pow_two_pow {K : Type} [Field K] [CharP K 2] {lam : K} {k : ℕ}
    (h1 : lam ^ 2 ^ k = 1) : lam = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : (lam - 1) ^ 2 ^ k = 0 := by rw [sub_pow_char_pow, h1, one_pow, sub_self]
  exact sub_eq_zero.1 ((pow_eq_zero_iff (by positivity)).1 h2)

include h in
theorem mem_J_of_linear {t : G} (ht : t ∈ T)
    (hlin : ∀ (c : GaloisField 2 e) (w : Fin 2 → GaloisField 2 e),
      D.act t (c • w) = c • D.act t w) : t ∈ V ⊔ W := by
  obtain ⟨z₀, hz₀, hz₀1⟩ := h.exists_Z_ne_one
  have hx₀ : D.κ z₀ ≠ 0 := D.κ_ne_zero hz₀.1 hz₀1
  have htV := h.T_le_V ht
  have htW := h.T_le_W ht
  have htz : t * z₀ * t⁻¹ ∈ V ⊓ W :=
    ⟨conj_mem_of_mem_normalizer htV hz₀.1, conj_mem_of_mem_normalizer htW hz₀.2⟩
  obtain ⟨μ, hμ⟩ := (h.mem_Z_iff D hz₀ hz₀1 htz.1).1 htz
  have hact0 : D.act t (D.κ z₀) = μ • D.κ z₀ := by rw [NatCoord.act_κ hz₀.1]; exact hμ
  obtain ⟨k, hk⟩ := h.pT ⟨t, ht⟩
  have htk : t ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hiter : ∀ n : ℕ, (D.act t)^[n] (D.κ z₀) = μ ^ n • D.κ z₀ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply', ih, hlin, hact0, smul_smul, pow_succ]
  have hμ1 : μ = 1 := by
    have h1 := hiter (2 ^ k)
    rw [← act_pow D htV, htk, NatCoord.act_one] at h1
    have h2 : (1 : GaloisField 2 e) • D.κ z₀ = μ ^ 2 ^ k • D.κ z₀ := by rw [one_smul]; exact h1
    exact eq_one_of_pow_two_pow (smul_left_injective _ hx₀ h2).symm
  let M : Matrix (Fin 2) (Fin 2) (GaloisField 2 e) := Matrix.of fun i j => D.act t (Pi.single j 1) i
  have hM : ∀ w, D.act t w = M *ᵥ w := by
    intro w
    have hw : w = w 0 • Pi.single 0 1 + w 1 • Pi.single 1 1 := by
      ext i; fin_cases i <;> simp
    conv_lhs => rw [hw]
    rw [NatCoord.act_add htV, hlin, hlin]
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mulVec, dotProduct, Fin.sum_univ_two,
      M, Matrix.of_apply]
    ring
  have hMpow : ∀ n : ℕ, ∀ w, (M ^ n) *ᵥ w = D.act (t ^ n) w := by
    intro n
    induction n with
    | zero => intro w; rw [pow_zero, one_mulVec, pow_zero, NatCoord.act_one]
    | succ n ih =>
      intro w
      rw [pow_succ, ← mulVec_mulVec, ← hM, ih, ← NatCoord.act_mul htV, ← pow_succ]
  have hMk : M ^ 2 ^ k = 1 := by
    ext i j
    have := congrFun (hMpow (2 ^ k) (Pi.single j 1)) i
    rw [htk, NatCoord.act_one, mulVec_single_one] at this
    rw [one_apply]
    simpa [Pi.single_apply, eq_comm] using this
  have hdet : M.det = 1 := by
    apply eq_one_of_pow_two_pow (k := k)
    rw [← det_pow, hMk, det_one]
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj ⟨M, hdet⟩
  have hlM' : (D.ρ l : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) = M := by rw [hlM]
  have hlJ : l ∈ V ⊔ W := by
    rw [← h.cent_L hz₀ hz₀1]
    refine ⟨hl, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    have h1 : D.κ (l * z₀ * l⁻¹) = D.κ z₀ := by
      rw [D.conj l hl z₀ hz₀.1, hlM', ← hM, hact0, hμ1, one_smul]
    have h2 := D.κ_inj _ (D.norm l hl z₀ hz₀.1) z₀ hz₀.1 h1
    calc l * z₀ = l * z₀ * l⁻¹ * l := by group
      _ = z₀ * l := by rw [h2]
  have hlt : l⁻¹ * t ∈ T ⊓ Subgroup.centralizer (V : Set G) := by
    refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (h.J_le_T hlJ)) ht, ?_⟩
    refine D.mem_centralizer_of_act (mul_mem (inv_mem (D.le_normalizer hl)) htV) fun w => ?_
    rw [NatCoord.act_mul htV, hM, ← hlM', ← NatCoord.act_of_mem_L hl,
      ← NatCoord.act_mul (D.le_normalizer hl), inv_mul_cancel, NatCoord.act_one]
  have hltV := h.cent hlt
  have e1 : t = l * (l⁻¹ * t) := by group
  rw [e1]
  exact mul_mem hlJ (Subgroup.mem_sup_left hltV)

include h in
theorem linear_of_mem_J {j : G} (hj : j ∈ V ⊔ W) (c : GaloisField 2 e)
    (w : Fin 2 → GaloisField 2 e) : D.act j (c • w) = c • D.act j w := by
  rw [NatCoord.act_of_mem_L (h.J_le_L hj), NatCoord.act_of_mem_L (h.J_le_L hj), mulVec_smul]

include h in
theorem exists_sig {t : G} (ht : t ∈ T) :
    ∃ σ : GaloisField 2 e ≃+* GaloisField 2 e, IsSemilinearWith (D.actPerm t (h.T_le_V ht)) σ :=
  D.exists_semilinear (h.T_le_L ht) (h.T_le_V ht)

@[expose] noncomputable def sig (t : ↥T) : GaloisField 2 e ≃+* GaloisField 2 e :=
  (h.exists_sig D t.2).choose

theorem sig_spec (t : ↥T) : IsSemilinearWith (D.actPerm t (h.T_le_V t.2)) (h.sig D t) :=
  (h.exists_sig D t.2).choose_spec

theorem sig_unique (t : ↥T) {σ : GaloisField 2 e ≃+* GaloisField 2 e}
    (hσ : IsSemilinearWith (D.actPerm t (h.T_le_V t.2)) σ) : h.sig D t = σ :=
  (h.sig_spec D t).unique hσ

@[expose] noncomputable def sigHom : ↥T →* (GaloisField 2 e ≃+* GaloisField 2 e) where
  toFun := h.sig D
  map_one' := h.sig_unique D 1 fun c w => by
    show D.act 1 (c • w) = c • D.act 1 w
    rw [NatCoord.act_one, NatCoord.act_one]
  map_mul' s t := h.sig_unique D (s * t) fun c w => by
    show D.act ((s : G) * t) (c • w) = (h.sig D s) ((h.sig D t) c) • D.act ((s : G) * t) w
    rw [NatCoord.act_mul (h.T_le_V t.2), NatCoord.act_mul (h.T_le_V t.2)]
    exact ((h.sig_spec D s).mul (h.sig_spec D t)) c w

theorem sigHom_apply (t : ↥T) : h.sigHom D t = h.sig D t := rfl

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

theorem ker_sigHom : (h.sigHom D).ker = (V ⊔ W).subgroupOf T := by
  ext t
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, sigHom_apply, h.sig_eq_one_iff D t]

include h D in
theorem relIndex_le : (V ⊔ W).relIndex T ≤ e := by
  have hidx : (V ⊔ W).relIndex T = Nat.card (h.sigHom D).range := by
    rw [Subgroup.relIndex, ← h.ker_sigHom D, Subgroup.index_ker]
  obtain ⟨-, -, -, -, hcard, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      (F := GaloisField 2 e) Nat.prime_two (by have := h.two_le; omega)
      (GaloisField.card 2 e (h.e_ne_zero))
  rw [hidx]
  have : Finite (GaloisField 2 e ≃+* GaloisField 2 e) :=
    Finite.of_injective (fun σ : GaloisField 2 e ≃+* GaloisField 2 e => (σ : GaloisField 2 e →
      GaloisField 2 e)) fun _ _ hσ => RingEquiv.ext (congrFun hσ)
  calc Nat.card (h.sigHom D).range ≤ Nat.card (GaloisField 2 e ≃+* GaloisField 2 e) :=
        Subgroup.card_le_card_group _
    _ = e := hcard

section Involution

variable {a : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W) (haa : a * a = 1)

include haJ in
theorem sig_ne_one : h.sig D ⟨a, ha⟩ ≠ 1 := fun h1 => haJ ((h.sig_eq_one_iff D ⟨a, ha⟩).1 h1)

include haa in
theorem sig_sq : h.sig D ⟨a, ha⟩ * h.sig D ⟨a, ha⟩ = 1 := by
  have : (⟨a, ha⟩ : ↥T) * ⟨a, ha⟩ = 1 := Subtype.ext haa
  rw [← sigHom_apply, ← map_mul, this, map_one]

include h ha haa in
theorem act_act (w : Fin 2 → GaloisField 2 e) : D.act a (D.act a w) = w := by
  rw [← NatCoord.act_mul (h.T_le_V ha), haa, NatCoord.act_one]

include haa in
theorem semInv : SemInv (h.sig D ⟨a, ha⟩) (D.act a) :=
  ⟨fun w w' => NatCoord.act_add (h.T_le_V ha) w w', fun c w => h.act_smul D ha c w,
    fun w => h.act_act D ha haa w⟩

include haJ in
theorem exists_sig_ne : ∃ c, h.sig D ⟨a, ha⟩ c ≠ c := by
  by_contra hcon
  push Not at hcon
  exact h.sig_ne_one D ha haJ (RingEquiv.ext hcon)

include h D ha haJ haa in
theorem card_CV : Nat.card ↥(V ⊓ Subgroup.centralizer ({a} : Set G)) = 2 ^ e := by
  have hfix := card_fixSet (h.exists_sig_ne D ha haJ) (h.semInv D ha haa)
  rw [GaloisField.card 2 e h.e_ne_zero] at hfix
  rw [← hfix]
  refine Nat.card_congr (Equiv.ofBijective (fun v => ⟨D.κ v, ?_⟩) ⟨?_, ?_⟩)
  · have hv := v.2
    rw [mem_fixSet, NatCoord.act_κ hv.1]
    congr 1
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hv.2
    calc a * v * a⁻¹ = v * a * a⁻¹ := by rw [h1]
      _ = v := by group
  · intro v v' hvv
    exact Subtype.ext (D.κ_inj _ v.2.1 _ v'.2.1 (congrArg Subtype.val hvv))
  · rintro ⟨x, hx⟩
    refine ⟨⟨D.sec x, D.sec_mem x, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩,
      Subtype.ext (D.κ_sec x)⟩
    have h1 : D.act a x = x := hx
    have h2 : D.κ (a * D.sec x * a⁻¹) = D.κ (D.sec x) := by
      rw [← NatCoord.act_κ (D.sec_mem x), D.κ_sec, h1]
    have h3 := D.κ_inj _ (conj_mem_of_mem_normalizer (h.T_le_V ha) (D.sec_mem x)) _
      (D.sec_mem x) h2
    calc D.sec x * a = a * D.sec x * a⁻¹ * a := by rw [h3]
      _ = a * D.sec x := by group

include h D ha haJ in
theorem not_centralizes_Z : ∃ z ∈ V ⊓ W, a * z ≠ z * a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀, hz₀1⟩ := h.exists_Z_ne_one
  have hx₀ : D.κ z₀ ≠ 0 := D.κ_ne_zero hz₀.1 hz₀1
  obtain ⟨c, hc⟩ := h.exists_sig_ne D ha haJ
  have hfix : ∀ z ∈ V ⊓ W, D.act a (D.κ z) = D.κ z := by
    intro z hz
    rw [NatCoord.act_κ hz.1]
    congr 1
    rw [hcon z hz]
    group
  have hz : D.sec (c • D.κ z₀) ∈ V ⊓ W :=
    (h.mem_Z_iff D hz₀ hz₀1 (D.sec_mem _)).2 ⟨c, D.κ_sec _⟩
  have h1 := hfix _ hz
  rw [D.κ_sec, h.act_smul D ha, hfix z₀ hz₀] at h1
  exact hc (smul_left_injective _ hx₀ h1)

include h D ha haJ haa in
theorem even_of_involution : Even e := by
  obtain ⟨n, hn, -, -⟩ := card_eq_sq_of_involution (h.sig D ⟨a, ha⟩) (h.sig_ne_one D ha haJ)
    (h.sig_sq D ha haa)
  rw [GaloisField.card 2 e h.e_ne_zero] at hn
  have h1 := congrArg (fun m => Nat.factorization m 2) hn
  simp only [Nat.Prime.factorization_self Nat.prime_two, Nat.factorization_pow,
    Finsupp.smul_apply, smul_eq_mul, mul_one] at h1
  exact ⟨n.factorization 2, by omega⟩

end Involution

include h D in
theorem mul_mem_J_of_involutions {a b : G} (ha : a ∈ T) (haJ : a ∉ V ⊔ W) (haa : a * a = 1)
    (hb : b ∈ T) (hbJ : b ∉ V ⊔ W) (hbb : b * b = 1) : a * b ∈ V ⊔ W := by
  have heq := aut_involution_unique (h.sig D ⟨a, ha⟩) (h.sig D ⟨b, hb⟩) (h.sig_sq D ha haa)
    (h.sig_sq D hb hbb) (h.sig_ne_one D ha haJ) (h.sig_ne_one D hb hbJ)
  have h1 : h.sig D ⟨a * b, mul_mem ha hb⟩ = 1 := by
    have : (⟨a * b, mul_mem ha hb⟩ : ↥T) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
    rw [this, ← sigHom_apply, map_mul, sigHom_apply, sigHom_apply, heq, h.sig_sq D hb hbb]
  exact (h.sig_eq_one_iff D ⟨a * b, mul_mem ha hb⟩).1 h1

include h D in
theorem fixZ {x : G} (hx : x ∈ T) (hxJ : x ∉ V ⊔ W) : ∃ v ∈ V, ⁅x, v⁆ ∉ V ⊓ W := by
  by_contra hcon
  push Not at hcon
  obtain ⟨z₀, hz₀, hz₀1⟩ := h.exists_Z_ne_one
  have hxV := h.T_le_V hx
  obtain ⟨c, hc⟩ := h.exists_sig_ne D hx hxJ
  obtain ⟨v, hv, hvZ⟩ : ∃ v ∈ V, v ∉ V ⊓ W := by
    by_contra hcon'
    push Not at hcon'
    exact h.jst.not_le_V₂ fun y hy => (hcon' y hy).2
  have hmod : ∀ u ∈ V, ∃ d : GaloisField 2 e, D.act x (D.κ u) = D.κ u + d • D.κ z₀ := by
    intro u hu
    have h1 := hcon u hu
    obtain ⟨d, hd⟩ := (h.mem_Z_iff D hz₀ hz₀1 h1.1).1 h1
    refine ⟨d, ?_⟩
    have e1 : ⁅x, u⁆ = (x * u * x⁻¹) * u⁻¹ := by simp [commutatorElement_def]
    rw [e1, D.κ_mul _ (conj_mem_of_mem_normalizer hxV hu) _ (inv_mem hu), D.κ_inv hu] at hd
    rw [NatCoord.act_κ hu, ← hd]
    abel
  obtain ⟨d₁, hd₁⟩ := hmod v hv
  have hcv : D.sec (c • D.κ v) ∈ V := D.sec_mem _
  obtain ⟨d₂, hd₂⟩ := hmod _ hcv
  rw [D.κ_sec, h.act_smul D hx, hd₁] at hd₂
  have hline : (h.sig D ⟨x, hx⟩ c - c) • D.κ v = (d₂ - h.sig D ⟨x, hx⟩ c * d₁) • D.κ z₀ := by
    linear_combination (norm := module) hd₂
  have hne : h.sig D ⟨x, hx⟩ c - c ≠ 0 := sub_ne_zero.2 hc
  apply hvZ
  refine (h.mem_Z_iff D hz₀ hz₀1 hv).2 ⟨(h.sig D ⟨x, hx⟩ c - c)⁻¹ * (d₂ - h.sig D ⟨x, hx⟩ c * d₁),
    ?_⟩
  rw [mul_smul, ← hline, smul_smul, inv_mul_cancel₀ hne, one_smul]

end L3Side

end CFSG.CGT.PushingUpLit.A78L3
