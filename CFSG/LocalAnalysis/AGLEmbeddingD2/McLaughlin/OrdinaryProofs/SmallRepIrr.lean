module

public import CFSG.Quasithin.Background.SmithB42U33Iso

public section

open CFSG.Quasithin

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

theorem natCard_eq_two_pow_of_exponent_two (J : Type) [CommGroup J] [Finite J]
    (hJ : ∀ v : J, v ^ 2 = 1) : ∃ k : ℕ, Nat.card J = 2 ^ k := by
  let _ : Module (ZMod 2) (Additive J) := AddCommGroup.zmodModule (n := 2) fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hJ _
  refine ⟨Module.finrank (ZMod 2) (Additive J), ?_⟩
  have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive J)
  rw [Nat.card_zmod] at h1
  exact (Nat.card_congr Additive.ofMul).trans h1

theorem comm_of_trivial_sub_quot {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    {J : Subgroup V} (hJ : ∀ l ∈ L, ∀ v ∈ J, l v = v) (hQ : ∀ l ∈ L, ∀ v : V, l v * v⁻¹ ∈ J) :
    ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
  intro x hx y hy
  ext v
  obtain ⟨w, hw, hyv⟩ : ∃ w ∈ J, y v = w * v := ⟨y v * v⁻¹, hQ y hy v, by group⟩
  obtain ⟨u, hu, hxv⟩ : ∃ u ∈ J, x v = u * v := ⟨x v * v⁻¹, hQ x hx v, by group⟩
  have e1 : (x * y) v = w * (u * v) := by
    rw [MulAut.mul_apply, hyv, map_mul, hJ x hx w hw, hxv]
  have e2 : (y * x) v = u * (w * v) := by
    rw [MulAut.mul_apply, hxv, map_mul, hJ y hy u hu, hyv]
  rw [e1, e2]
  ac_rfl

def quotMulEquiv {V : Type} [CommGroup V] (J : Subgroup V) (l : MulAut V)
    (hl : ∀ v ∈ J, l v ∈ J) (hl' : ∀ v ∈ J, l⁻¹ v ∈ J) : MulAut (V ⧸ J) where
  toFun := QuotientGroup.map J J (l : V →* V) (fun v hv => hl v hv)
  invFun := QuotientGroup.map J J ((l⁻¹ : MulAut V) : V →* V) (fun v hv => hl' v hv)
  left_inv q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      have h : (l⁻¹ : MulAut V) (l x) = x := by simp
      exact congrArg (fun y : V => (y : V ⧸ J)) h
  right_inv q := by
    induction q using QuotientGroup.induction_on with
    | H x =>
      have h : l ((l⁻¹ : MulAut V) x) = x := by simp
      exact congrArg (fun y : V => (y : V ⧸ J)) h
  map_mul' p q := by
    induction p using QuotientGroup.induction_on with
    | H x =>
      induction q using QuotientGroup.induction_on with
      | H y => simp

def restrictMulAut {V : Type} [CommGroup V] (J : Subgroup V) (l : MulAut V)
    (hl : ∀ v ∈ J, l v ∈ J) (hl' : ∀ v ∈ J, l⁻¹ v ∈ J) : MulAut J where
  toFun v := ⟨l v, hl v v.2⟩
  invFun v := ⟨l⁻¹ v, hl' v v.2⟩
  left_inv v := Subtype.ext (by simp)
  right_inv v := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

theorem eq_bot_or_eq_top_of_small {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)} (hnc : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x)
    (hsmall : ∀ (J : Type) [CommGroup J] [Finite J], (∀ v : J, v ^ 2 = 1) →
      Nat.card J < Nat.card V → ∀ φ : ↥L →* MulAut J, φ = 1)
    (J : Subgroup V) (hJ : ∀ l ∈ L, ∀ v ∈ J, l v ∈ J) : J = ⊥ ∨ J = ⊤ := by
  by_contra hne
  obtain ⟨h1, h2⟩ := not_or.mp hne
  have hidx : J.index ≠ 1 := fun h => h2 (Subgroup.index_eq_one.mp h)
  have hidx0 : J.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hmul : Nat.card J * J.index = Nat.card V := Subgroup.card_mul_index J
  have hcardJ : 1 < Nat.card J :=
    Finite.one_lt_card_iff_nontrivial.mpr ((Subgroup.nontrivial_iff_ne_bot J).mpr h1)
  have hJlt : Nat.card J < Nat.card V := by
    have : 2 ≤ J.index := by omega
    nlinarith
  have hQlt : Nat.card (V ⧸ J) < Nat.card V := by
    have hq : Nat.card (V ⧸ J) = J.index := rfl
    have : 2 ≤ Nat.card J := hcardJ
    have : 0 < J.index := Nat.pos_of_ne_zero hidx0
    rw [hq]
    nlinarith
  have hJV : ∀ v : J, v ^ 2 = 1 := fun v => by
    ext
    simpa using hV (v : V)
  let rJ : ↥L →* MulAut J :=
    { toFun := fun l => restrictMulAut J (l : MulAut V) (hJ l l.2)
        (fun v hv => hJ _ (L.inv_mem l.2) v hv)
      map_one' := by
        ext v
        simp [restrictMulAut]
      map_mul' := fun a b => by
        ext v
        simp [restrictMulAut] }
  have hrJ : rJ = 1 := hsmall J hJV hJlt rJ
  have hJfix : ∀ l ∈ L, ∀ v ∈ J, l v = v := by
    intro l hl v hv
    have h := congrArg (fun φ : ↥L →* MulAut J => ((φ ⟨l, hl⟩) ⟨v, hv⟩ : V)) hrJ
    simpa [rJ, restrictMulAut] using h
  have hVq : ∀ q : V ⧸ J, q ^ 2 = 1 := fun q => by
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, hV x, QuotientGroup.mk_one]
  let rQ : ↥L →* MulAut (V ⧸ J) :=
    { toFun := fun l => quotMulEquiv J (l : MulAut V) (hJ l l.2)
        (fun v hv => hJ _ (L.inv_mem l.2) v hv)
      map_one' := by
        ext q
        induction q using QuotientGroup.induction_on with
        | H x => rfl
      map_mul' := fun a b => by
        ext q
        induction q using QuotientGroup.induction_on with
        | H x => rfl }
  have hrQ : rQ = 1 := hsmall (V ⧸ J) hVq hQlt rQ
  have hQtriv : ∀ l ∈ L, ∀ v : V, l v * v⁻¹ ∈ J := by
    intro l hl v
    have h := congrArg (fun φ : ↥L →* MulAut (V ⧸ J) => (φ ⟨l, hl⟩) (QuotientGroup.mk v)) hrQ
    have h' : (QuotientGroup.mk (l v) : V ⧸ J) = QuotientGroup.mk v := h
    have h'' := QuotientGroup.eq.mp h'
    have := J.inv_mem h''
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  obtain ⟨x, hx, y, hy, hxy⟩ := hnc
  exact hxy (comm_of_trivial_sub_quot hJfix hQtriv x hx y hy)

theorem trivial_of_card_lt_two_pow_six {K : Type} [Group K] [IsSimpleGroup K]
    (hK : Nat.card K = 6048) (J : Type) [CommGroup J] [Finite J] (hJ : ∀ v : J, v ^ 2 = 1)
    (hcard : Nat.card J < 2 ^ 6) (φ : K →* MulAut J) : φ = 1 := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker) with hbot | htop
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
    obtain ⟨k, hk⟩ := natCard_eq_two_pow_of_exponent_two J hJ
    have hkl : k < 6 := by
      by_contra hc
      have h6 : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have hR : Nat.card φ.range = 6048 :=
      ((Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm).trans hK
    have h6 := CFSG.Quasithin.B42U33.six_le_of_card_dvd hJ hk φ.range hR
    omega
  · refine MonoidHom.ext fun g => ?_
    have hg : g ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top g
    rw [MonoidHom.one_apply]
    exact MonoidHom.mem_ker.mp hg

theorem alt7_trivial_of_card_lt_two_pow_four (J : Type) [CommGroup J] [Finite J]
    (hJ : ∀ v : J, v ^ 2 = 1) (hcard : Nat.card J < 2 ^ 4)
    (φ : alternatingGroup (Fin 7) →* MulAut J) : φ = 1 := by
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by simp)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker) with hbot | htop
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).mp hbot
    obtain ⟨k, hk⟩ := natCard_eq_two_pow_of_exponent_two J hJ
    have hkl : k < 4 := by
      by_contra hc
      have h4 : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have h3 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
      rfl
    have hR : Nat.card φ.range = 2520 :=
      ((Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm).trans h3
    have hdvd := Subgroup.card_subgroup_dvd_card φ.range
    rw [hR, CFSG.Quasithin.B42U33.card_mulAut_eq hJ hk] at hdvd
    interval_cases k <;> norm_num [Fin.prod_univ_succ] at hdvd
  · refine MonoidHom.ext fun g => ?_
    have hg : g ∈ φ.ker := by
      rw [htop]
      exact Subgroup.mem_top g
    rw [MonoidHom.one_apply]
    exact MonoidHom.mem_ker.mp hg

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
