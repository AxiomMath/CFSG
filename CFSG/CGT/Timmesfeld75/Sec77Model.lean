module

public import CFSG.CGT.Timmesfeld75.Sec74
public import CFSG.CGT.Timmesfeld75.Sec77Transv

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped MatrixGroups Matrix commutatorElement

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

section Ubar

variable {H : Subgroup G} [(T.subgroupOf H).Normal] {F : Type*} [Field F]

open Classical in
@[expose] noncomputable def ubar (ε : ↥H ⧸ T.subgroupOf H ≃* SL(n, F)) (a : G) : SL(n, F) :=
  if h : a ∈ H then ε (QuotientGroup.mk ⟨a, h⟩) else 1

variable (ε : ↥H ⧸ T.subgroupOf H ≃* SL(n, F))

theorem ubar_of_mem {a : G} (ha : a ∈ H) : ubar ε a = ε (QuotientGroup.mk ⟨a, ha⟩) := by
  simp [ubar, ha]

theorem ubar_mul {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ubar ε (a * b) = ubar ε a * ubar ε b := by
  rw [ubar_of_mem ε (H.mul_mem ha hb), ubar_of_mem ε ha, ubar_of_mem ε hb, ← map_mul,
    ← QuotientGroup.mk_mul]
  rfl

theorem ubar_inv {a : G} (ha : a ∈ H) : ubar ε a⁻¹ = (ubar ε a)⁻¹ := by
  rw [ubar_of_mem ε (H.inv_mem ha), ubar_of_mem ε ha, ← map_inv, ← QuotientGroup.mk_inv]
  rfl

theorem ubar_eq_one_iff {a : G} (ha : a ∈ H) : ubar ε a = 1 ↔ a ∈ T := by
  rw [ubar_of_mem ε ha]
  constructor
  · intro h
    have h1 : (QuotientGroup.mk ⟨a, ha⟩ : ↥H ⧸ T.subgroupOf H) = 1 :=
      ε.injective (by rw [h, map_one])
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff (N := T.subgroupOf H) _).1 h1)
  · intro hT
    have : (⟨a, ha⟩ : ↥H) ∈ T.subgroupOf H := Subgroup.mem_subgroupOf.2 hT
    rw [(QuotientGroup.eq_one_iff _).2 this, map_one]

theorem ubar_eq_iff {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ubar ε a = ubar ε b ↔ a⁻¹ * b ∈ T := by
  rw [← ubar_eq_one_iff ε (H.mul_mem (H.inv_mem ha) hb), ubar_mul ε (H.inv_mem ha) hb,
    ubar_inv ε ha, inv_mul_eq_one]

theorem ubar_of_mem_T (hTH : T ≤ H) {t : G} (ht : t ∈ T) : ubar ε t = 1 :=
  (ubar_eq_one_iff ε (hTH ht)).2 ht

end Ubar

section Model

structure TModel (T T₁ : Subgroup G) (n m : ℕ)
    [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] where
  ε : ↥(hSub T (normIn T₁ T)) ⧸ T.subgroupOf (hSub T (normIn T₁ T)) ≃*
    SL(n, GaloisField 2 m)
  φ : ↥T ≃* Multiplicative (Fin n → GaloisField 2 m)
  compat : ∀ (h : ↥(hSub T (normIn T₁ T))) (t : ↥T) (hmem : (h : G) * t * (h : G)⁻¹ ∈ T),
    φ ⟨(h : G) * t * (h : G)⁻¹, hmem⟩ =
      Multiplicative.ofAdd (((ε (QuotientGroup.mk h) : SL(n, GaloisField 2 m)) :
        Matrix (Fin n) (Fin n) (GaloisField 2 m)).mulVec (Multiplicative.toAdd (φ t)))
  transv : ∀ x ∈ normD T, x ∉ T → ∃ hxH : x ∈ hSub T (normIn T₁ T),
    IsTransvection (ε (QuotientGroup.mk (⟨x, hxH⟩ : ↥(hSub T (normIn T₁ T)))))

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] (M : TModel T T₁ n m)

include M

theorem TModel.mem_H {x : G} (hx : x ∈ normD T) : x ∈ hSub T (normIn T₁ T) := by
  by_cases hxT : x ∈ T
  · exact left_le_hSub hxT
  · exact (M.transv x hx hxT).1

theorem TModel.ubar_ne_one {x : G} (hx : x ∈ normD T) (hxT : x ∉ T) : ubar M.ε x ≠ 1 :=
  fun h => hxT ((ubar_eq_one_iff M.ε (M.mem_H hx)).1 h)

theorem TModel.exists_data {x : G} (hx : x ∈ normD T) (hxT : x ∉ T) :
    ∃ (f : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)) (v : Fin n → GaloisField 2 m),
      f v = 0 ∧ v ≠ 0 ∧ f ≠ 0 ∧ ∀ w, sact (ubar M.ε x) w = w + f w • v := by
  obtain ⟨hxH, htr⟩ := M.transv x hx hxT
  obtain ⟨f, v, hfv, hv, hact⟩ := htr.exists_data
  have hU : ubar M.ε x = M.ε (QuotientGroup.mk ⟨x, hxH⟩) := ubar_of_mem M.ε hxH
  refine ⟨f, v, hfv, hv, ?_, fun w => ?_⟩
  · rintro rfl
    apply M.ubar_ne_one hx hxT
    rw [hU]
    apply eq_of_sact
    intro w
    have := hact w
    simp only [LinearMap.zero_apply, zero_smul, add_zero] at this
    rw [sact_one]
    exact this
  · rw [hU]
    exact hact w

theorem TModel.toAdd_phi_conj {a : G} (ha : a ∈ hSub T (normIn T₁ T)) {t : G} (ht : t ∈ T)
    (hmem : a * t * a⁻¹ ∈ T) :
    Multiplicative.toAdd (M.φ ⟨a * t * a⁻¹, hmem⟩) =
      sact (ubar M.ε a) (Multiplicative.toAdd (M.φ ⟨t, ht⟩)) := by
  have h := M.compat ⟨a, ha⟩ ⟨t, ht⟩ hmem
  rw [h, ubar_of_mem M.ε ha]
  rfl

end Model

section Facts

variable [(T.subgroupOf (hSub T (normIn T₁ T))).Normal]

omit [(T.subgroupOf (hSub T (normIn T₁ T))).Normal] in
theorem Sec6Ctx.exists_normD_not_mem (hc : Sec6Ctx T T₁ n m) : ∃ e ∈ normD T, e ∉ T := by
  have hP := hc.hy.pair
  have hS3 := hc.sec3
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hS3.cfg.ne₁
  have hu1' : u ≠ 1 := fun h => hu1 (Subtype.ext h)
  obtain ⟨x₀, hx₀⟩ := hP.conj
  have huk : u ∈ conjSubgroup x₀ T := hx₀ ▸ normIn_le _ _ hu
  refine ⟨u, mem_normD_of_mem_conjSubgroup huk hu1' (hL₁N hu), fun huT => hu1' ?_⟩
  have : u ∈ T ⊓ T₁ := ⟨huT, normIn_le _ _ hu⟩
  rw [hS3.cfg.inf, Subgroup.mem_bot] at this
  exact this

theorem Sec6Ctx.exists_lift (hc : Sec6Ctx T T₁ n m) (M : TModel T T₁ n m)
    {u₀ : SL(n, GaloisField 2 m)} (hu₀ : IsTransvection u₀) :
    ∃ b ∈ normD T, b ∉ T ∧ ubar M.ε b = u₀ := by
  obtain ⟨e₀, he₀, he₀T⟩ := hc.exists_normD_not_mem
  obtain ⟨he₀H, he₀tr⟩ := M.transv e₀ he₀ he₀T
  obtain ⟨W, hW⟩ := exists_conj_of_isTransvection he₀tr hu₀
  obtain ⟨q, rfl⟩ := M.ε.surjective W
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
  have hL₁N : normIn T₁ T ≤ Subgroup.normalizer (T : Set G) := fun w hw => (mem_normIn.1 hw).2
  have hHN : hSub T (normIn T₁ T) ≤ Subgroup.normalizer (T : Set G) := hSub_le_normalizer hL₁N
  have hhH : (h : G) ∈ hSub T (normIn T₁ T) := h.2
  have hbH : (h : G) * e₀ * (h : G)⁻¹ ∈ hSub T (normIn T₁ T) :=
    (hSub T (normIn T₁ T)).mul_mem ((hSub T (normIn T₁ T)).mul_mem hhH he₀H)
      ((hSub T (normIn T₁ T)).inv_mem hhH)
  have hub : ubar M.ε ((h : G) * e₀ * (h : G)⁻¹) = u₀ := by
    rw [ubar_mul M.ε ((hSub T (normIn T₁ T)).mul_mem hhH he₀H)
        ((hSub T (normIn T₁ T)).inv_mem hhH), ubar_mul M.ε hhH he₀H,
      ubar_inv M.ε hhH, ubar_of_mem M.ε hhH, ubar_of_mem M.ε he₀H, ← hW]
  have hN : (h : G) * e₀ * (h : G)⁻¹ ∈ Subgroup.normalizer (T : Set G) :=
    (Subgroup.normalizer (T : Set G)).mul_mem
      ((Subgroup.normalizer (T : Set G)).mul_mem (hHN hhH) he₀.2)
      ((Subgroup.normalizer (T : Set G)).inv_mem (hHN hhH))
  refine ⟨(h : G) * e₀ * (h : G)⁻¹, ⟨classD_conj_mul he₀.1 h, hN⟩, fun hbT => ?_, hub⟩
  have h1 : ubar M.ε ((h : G) * e₀ * (h : G)⁻¹) = 1 := (ubar_eq_one_iff M.ε hbH).2 hbT
  rw [hub] at h1
  exact hu₀.1 h1

theorem Sec6Ctx.mem_classD_mul_iff (h62 : Sec62) (h63 : Sec63) (hc : Sec6Ctx T T₁ n m)
    (M : TModel T T₁ n m) {e : G} (he : e ∈ normD T) (heT : e ∉ T)
    {f : Module.Dual (GaloisField 2 m) (Fin n → GaloisField 2 m)}
    {v : Fin n → GaloisField 2 m} (hf : f ≠ 0)
    (hdata : ∀ w, sact (ubar M.ε e) w = w + f w • v) {t : G} (ht : t ∈ T) :
    e * t ∈ classD T ↔ ∃ r : GaloisField 2 m, Multiplicative.toAdd (M.φ ⟨t, ht⟩) = r • v := by
  have hTab := hc.hy.pair.wc.1
  have hee : e * e = 1 := mul_self_eq_one_of_mem_classD hTab he.1
  have he2 : e ^ 2 = 1 := by rw [pow_two]; exact hee
  have heH := M.mem_H he
  obtain ⟨hs1, hs2⟩ := hc.sec65 h62 h63 he heT
  have hcomm : ∀ s : G, ∀ hs : s ∈ T, Multiplicative.toAdd (M.φ ⟨⁅e, s⁆,
      comm_mem_of_mem_normalizer he.2 hs⟩) =
      (Multiplicative.toAdd (M.φ ⟨s, hs⟩)) + f (Multiplicative.toAdd (M.φ ⟨s, hs⟩)) • v -
        Multiplicative.toAdd (M.φ ⟨s, hs⟩) := by
    intro s hs
    have h := toAdd_phi_comm M.compat heH he.2 hs (comm_mem_of_mem_normalizer he.2 hs)
    rw [h]
    have h2 : ((M.ε (QuotientGroup.mk (⟨e, heH⟩ : ↥(hSub T (normIn T₁ T)))) :
        SL(n, GaloisField 2 m)) : Matrix (Fin n) (Fin n) (GaloisField 2 m)) *ᵥ
          Multiplicative.toAdd (M.φ ⟨s, hs⟩) = sact (ubar M.ε e)
            (Multiplicative.toAdd (M.φ ⟨s, hs⟩)) := by
      rw [ubar_of_mem M.ε heH]
      rfl
    rw [h2, hdata]
  constructor
  · intro hD
    have hmem1 : e * t ∈ {y | y ∈ classD T ∧ ∃ t' ∈ T, y = e * t'} := ⟨hD, t, ht, rfl⟩
    rw [hs1, hs2] at hmem1
    obtain ⟨c, hc', hct⟩ := hmem1
    have htc : t = c := mul_left_cancel hct
    obtain ⟨s, hs, hcs⟩ := (mem_commSub_iff hTab he2 he.2).1 hc'
    refine ⟨f (Multiplicative.toAdd (M.φ ⟨s, hs⟩)), ?_⟩
    have h3 := hcomm s hs
    have h4 : (⟨t, ht⟩ : ↥T) = ⟨⁅e, s⁆, comm_mem_of_mem_normalizer he.2 hs⟩ :=
      Subtype.ext (htc.trans hcs)
    rw [h4, h3]
    abel
  · rintro ⟨r, hr⟩
    obtain ⟨w₀, hw₀⟩ := exists_dual_apply_eq_one hf
    set s : ↥T := M.φ.symm (Multiplicative.ofAdd (r • w₀)) with hsdef
    have hφs : Multiplicative.toAdd (M.φ s) = r • w₀ := by
      rw [hsdef, M.φ.apply_symm_apply]
      rfl
    have h3 := hcomm (s : G) s.2
    have hs' : (⟨(s : G), s.2⟩ : ↥T) = s := rfl
    rw [hs', hφs] at h3
    have h5 : Multiplicative.toAdd (M.φ ⟨⁅e, (s : G)⁆, comm_mem_of_mem_normalizer he.2 s.2⟩) =
        r • v := by
      rw [h3, map_smul, hw₀, smul_eq_mul, mul_one]
      abel
    have h6 : (⟨⁅e, (s : G)⁆, comm_mem_of_mem_normalizer he.2 s.2⟩ : ↥T) = ⟨t, ht⟩ := by
      apply M.φ.injective
      apply Multiplicative.toAdd.injective
      rw [h5, hr]
    have h7 : t ∈ commSub e T := by
      refine (mem_commSub_iff hTab he2 he.2).2 ⟨(s : G), s.2, ?_⟩
      exact (congrArg Subtype.val h6).symm
    have hmem2 : e * t ∈ {y | ∃ c ∈ commSub e T, y = e * c} := ⟨t, h7, rfl⟩
    rw [← hs2, ← hs1] at hmem2
    exact hmem2.1

theorem Sec6Ctx.comm_of_ubar_comm (h66 : Sec66) (h1 : Sec4NoA) (h62 : Sec62) (h63 : Sec63)
    (hc : Sec6Ctx T T₁ n m) (hnat : NaturalSL T (hSub T (normIn T₁ T)) n m) (hn3 : 3 ≤ n)
    (hA8 : ¬ (n = 4 ∧ m = 1)) (M : TModel T T₁ n m) {a b : G} (ha : a ∈ normD T)
    (haT : a ∉ T) (hb : b ∈ normD T) (hbT : b ∉ T)
    (hcomm : ubar M.ε a * ubar M.ε b = ubar M.ε b * ubar M.ε a) : a * b = b * a := by
  have := hc.finite
  have hTwc := hc.hy.pair.wc
  have hTab := hTwc.1
  have haa : a * a = 1 := mul_self_eq_one_of_mem_classD hTab ha.1
  have hbb : b * b = 1 := mul_self_eq_one_of_mem_classD hTab hb.1
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
  have haH := M.mem_H ha
  have hbH := M.mem_H hb
  by_contra hne
  have hk : (a * b) ^ 2 = a * b * a⁻¹ * b⁻¹ := by
    rw [pow_two, hai, hbi]
    group
  have hkH : a * b * a⁻¹ * b⁻¹ ∈ hSub T (normIn T₁ T) :=
    (hSub T (normIn T₁ T)).mul_mem
      ((hSub T (normIn T₁ T)).mul_mem
        ((hSub T (normIn T₁ T)).mul_mem haH hbH) ((hSub T (normIn T₁ T)).inv_mem haH))
      ((hSub T (normIn T₁ T)).inv_mem hbH)
  have hkT : a * b * a⁻¹ * b⁻¹ ∈ T := by
    rw [← ubar_eq_one_iff M.ε hkH, ubar_mul M.ε
      ((hSub T (normIn T₁ T)).mul_mem ((hSub T (normIn T₁ T)).mul_mem haH hbH)
        ((hSub T (normIn T₁ T)).inv_mem haH)) ((hSub T (normIn T₁ T)).inv_mem hbH),
      ubar_mul M.ε ((hSub T (normIn T₁ T)).mul_mem haH hbH) ((hSub T (normIn T₁ T)).inv_mem haH),
      ubar_mul M.ε haH hbH, ubar_inv M.ε haH, ubar_inv M.ε hbH, hcomm]
    group
  have hk1 : (a * b) ^ 2 ≠ 1 := by
    intro h
    apply hne
    have h' : a * b * (a * b) = 1 := by rw [← pow_two]; exact h
    have e1 : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h').symm
    rw [e1, mul_inv_rev, hai, hbi]
  have hkk : (a * b) ^ 2 * (a * b) ^ 2 = 1 := by
    rw [hk]
    exact elemAbelian_mul_self hTab hkT
  have hord : orderOf (a * b) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h4 : (a * b) ^ 2 ^ (1 + 1) = 1 := by
      rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add]
      exact hkk
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (by simpa using hk1) h4
    simpa using this
  have hkT' : (a * b) ^ 2 ∈ T := by rw [hk]; exact hkT
  rcases sec74_of h66 h1 h62 h63 G T T₁ n m hc hnat hn3 hA8 a ha.1 b hb.1 hord with
    ⟨h, hah, hba⟩ | ⟨g, hbg, hab⟩
  · have hkh : (a * b) ^ 2 ∈ conjSubgroup h T := by
      have e1 : (a * b) ^ 2 = a * (b⁻¹ * a * b) := by rw [pow_two, hbi]; group
      rw [e1]
      exact (conjSubgroup h T).mul_mem hah hba
    have hinf : T ⊓ conjSubgroup h T ≠ ⊥ := fun h0 => hk1 (by
      have : (a * b) ^ 2 ∈ T ⊓ conjSubgroup h T := ⟨hkT', hkh⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this)
    have := hTwc.conj_eq_of_inf_ne_bot hinf
    exact haT (this ▸ hah)
  · have hkg : (a * b) ^ 2 ∈ conjSubgroup g T := by
      have e1 : (a * b) ^ 2 = (a⁻¹ * b * a) * b := by rw [pow_two, hai]; group
      rw [e1]
      exact (conjSubgroup g T).mul_mem hab hbg
    have hinf : T ⊓ conjSubgroup g T ≠ ⊥ := fun h0 => hk1 (by
      have : (a * b) ^ 2 ∈ T ⊓ conjSubgroup g T := ⟨hkT', hkg⟩
      rw [h0, Subgroup.mem_bot] at this
      exact this)
    have := hTwc.conj_eq_of_inf_ne_bot hinf
    exact hbT (this ▸ hbg)

end Facts

end CFSG.CGT.Timmesfeld75
