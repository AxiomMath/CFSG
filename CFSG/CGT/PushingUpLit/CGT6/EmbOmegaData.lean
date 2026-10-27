module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAdm
public import CFSG.CGT.PushingUpLit.CGT6.EmbHolTop
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltSL
public import CFSG.CGT.PushingUpLit.CGT6.EmbOmega
public import CFSG.CGT.PushingUpLit.CGT6.TwoEightMinus

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6

section SL2

theorem not_isPGroup_sl2 {k : ℕ} (hk : 2 ≤ k) :
    ¬ IsPGroup 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) := by
  intro h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp h
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    GaloisField.card 2 k (by omega)] at hj
  have hdvd : (2 ^ k) ^ 2 - 1 ∣ 2 ^ j := ⟨2 ^ k, by rw [← hj]; ring⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hq4 : 4 ≤ 2 ^ k := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have hq16 : 16 ≤ (2 ^ k) ^ 2 := by nlinarith
  have h2 : 2 ∣ (2 ^ k) ^ 2 := dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp at hi
    omega
  · have : 2 ∣ (2 ^ k) ^ 2 - 1 := by
      rw [hi]
      exact dvd_pow_self 2 hpos.ne'
    omega

theorem sl2_order_strictMono {a b : ℕ} (hab : a < b) :
    2 ^ a * ((2 ^ a) ^ 2 - 1) < 2 ^ b * ((2 ^ b) ^ 2 - 1) := by
  have h1 : 2 ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : (2 ^ a) ^ 2 < (2 ^ b) ^ 2 := Nat.pow_lt_pow_left h1 (by norm_num)
  have h3 : 1 ≤ (2 ^ a) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Nat.mul_lt_mul'' h1 (by omega)

theorem sl2_card_inj {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (h : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 a)) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 b))) : a = b := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two,
    CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, GaloisField.card 2 a (by omega),
    GaloisField.card 2 b (by omega)] at h
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd h (sl2_order_strictMono hab).ne
  · exact hab
  · exact absurd h.symm (sl2_order_strictMono hab).ne

theorem pCore_sl2_eq_bot {k : ℕ} (hk : 2 ≤ k) :
    pCore 2 (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) = ⊥ := by
  have := isSimpleGroup_sl2_gf hk
  exact pCore_eq_bot_of_simple (not_isPGroup_sl2 hk)

theorem sl2_not_isSolvable {k : ℕ} (hk : 2 ≤ k) :
    ¬ Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) := by
  intro hsolv
  have hS := isSimpleGroup_sl2_gf hk
  have hcomm := (IsSimpleGroup.comm_iff_isSolvable
    (G := Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))).mpr hsolv
  have hc := center_sl2_eq_bot (GaloisField 2 k)
  obtain ⟨s, hs1⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))
  have : s ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) :=
    Subgroup.mem_center_iff.mpr fun g => hcomm g s
  rw [hc] at this
  exact hs1 (Subgroup.mem_bot.mp this)

theorem isPerfect_sl2 {k : ℕ} (hk : 2 ≤ k) :
    Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k)) := by
  have hS := isSimpleGroup_sl2_gf hk
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (commutator (Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 k))) with h | h
  · exact absurd ⟨⟨1, by rw [derivedSeries_succ, derivedSeries_zero]; exact h⟩⟩
      (sl2_not_isSolvable hk)
  · exact Group.isPerfect_def.mpr h

end SL2

section Prod

variable {S : Type} [Group S]

theorem pCore_prod_bot (h : pCore 2 S = ⊥) : pCore 2 (S × S) = ⊥ := by
  have hn : (pCore 2 (S × S)).Normal := inferInstance
  have hp : IsPGroup 2 (pCore 2 (S × S)) := pCore_isPGroup
  have h1 : (pCore 2 (S × S)).map (MonoidHom.fst S S) ≤ pCore 2 S :=
    le_sSup ⟨hn.map (MonoidHom.fst S S) (fun s => ⟨(s, 1), rfl⟩), hp.map (MonoidHom.fst S S)⟩
  have h2 : (pCore 2 (S × S)).map (MonoidHom.snd S S) ≤ pCore 2 S :=
    le_sSup ⟨hn.map (MonoidHom.snd S S) (fun s => ⟨(1, s), rfl⟩), hp.map (MonoidHom.snd S S)⟩
  rw [h] at h1 h2
  rw [eq_bot_iff]
  rintro ⟨a, b⟩ hx
  have ha : a ∈ (⊥ : Subgroup S) := h1 ⟨_, hx, rfl⟩
  have hb : b ∈ (⊥ : Subgroup S) := h2 ⟨_, hx, rfl⟩
  simp only [Subgroup.mem_bot] at ha hb ⊢
  simp [ha, hb]

theorem not_isSimpleGroup_prod [Nontrivial S] : ¬ IsSimpleGroup (S × S) := by
  intro hs
  obtain ⟨s, hs1⟩ := exists_ne (1 : S)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((⊤ : Subgroup S).prod (⊥ : Subgroup S)) with h | h
  · have : (s, (1 : S)) ∈ (⊤ : Subgroup S).prod (⊥ : Subgroup S) := ⟨trivial, Subgroup.one_mem _⟩
    rw [h] at this
    exact hs1 (by simpa using this)
  · have : ((1 : S), s) ∈ (⊤ : Subgroup S).prod (⊥ : Subgroup S) := by rw [h]; trivial
    exact hs1 (by simpa using this.2)

theorem isPerfect_prod {T : Type} [Group T] (hS : Group.IsPerfect S) (hT : Group.IsPerfect T) :
    Group.IsPerfect (S × T) := by
  have hS' : commutator S = ⊤ := Group.isPerfect_def.mp hS
  have hT' : commutator T = ⊤ := Group.isPerfect_def.mp hT
  rw [Group.isPerfect_def, eq_top_iff]
  rintro ⟨a, b⟩ -
  have hinl : (commutator S).map (MonoidHom.inl S T) ≤ commutator (S × T) := by
    unfold commutator
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have hinr : (commutator T).map (MonoidHom.inr S T) ≤ commutator (S × T) := by
    unfold commutator
    rw [Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  have h1 : (a, (1 : T)) ∈ commutator (S × T) := hinl ⟨a, by rw [hS']; trivial, rfl⟩
  have h2 : ((1 : S), b) ∈ commutator (S × T) := hinr ⟨b, by rw [hT']; trivial, rfl⟩
  simpa using Subgroup.mul_mem _ h1 h2

end Prod

section NatOmega

theorem card_multiplicative_hermSub {n : ℕ} (hn : n ≠ 0) :
    Nat.card (Multiplicative (hermSub n)) = 2 ^ (4 * n) := by
  have : NeZero n := ⟨hn⟩
  rw [Nat.card_congr (TwoEight.minusKappa n), Nat.card_prod, Nat.card_prod, TwoEight.card_Fz,
    GaloisField.card 2 (2 * n) (by omega)]
  ring

variable {V : Type} [CommGroup V]

theorem NatOmegaN.cases {n : ℕ} (hn : 2 ≤ n) {X : Subgroup (MulAut V)} (h : NatOmegaN n X) :
    (Nonempty (↥X ≃* SLq n × SLq n) ∧ Nat.card ↥(commV X) = 2 ^ (4 * n)) ∨
      (Nonempty (↥X ≃* SLq (2 * n)) ∧ Nat.card ↥(commV X) = 2 ^ (4 * n)) := by
  rcases h with h | h
  · obtain ⟨-, θ, β, -⟩ := TwoEight.natSection_equiv h
    refine Or.inl ⟨⟨θ⟩, ?_⟩
    rw [Nat.card_congr β.toEquiv, card_matrix_fq (by omega)]
  · obtain ⟨-, θ, β, -⟩ := TwoEight.natSection_equiv h
    refine Or.inr ⟨⟨θ⟩, ?_⟩
    rw [Nat.card_congr β.toEquiv, card_multiplicative_hermSub (by omega)]

theorem NatOmegaN.pCore_eq_bot {n : ℕ} (hn : 2 ≤ n) {X : Subgroup (MulAut V)} (h : NatOmegaN n X) :
    pCore 2 ↥X = ⊥ := by
  rcases h.cases hn with ⟨⟨θ⟩, -⟩ | ⟨⟨θ⟩, -⟩
  · exact pCore_eq_bot_of_equiv θ (pCore_prod_bot (pCore_sl2_eq_bot hn))
  · exact pCore_eq_bot_of_equiv θ (pCore_sl2_eq_bot (by omega))

theorem NatOmegaN.not_isPGroup {n : ℕ} (hn : 2 ≤ n) {X : Subgroup (MulAut V)}
    (h : NatOmegaN n X) : ¬ IsPGroup 2 ↥X := by
  intro hX
  rcases h.cases hn with ⟨⟨θ⟩, -⟩ | ⟨⟨θ⟩, -⟩
  · have h1 : IsPGroup 2 (SLq n × SLq n) := IsPGroup.of_surjective hX θ.toMonoidHom θ.surjective
    exact not_isPGroup_sl2 hn
      (IsPGroup.of_surjective h1 (MonoidHom.fst (SLq n) (SLq n)) fun s => ⟨(s, 1), rfl⟩)
  · exact not_isPGroup_sl2 (by omega) (IsPGroup.of_surjective hX θ.toMonoidHom θ.surjective)

theorem NatOmegaN.not_equiv_alt {n : ℕ} (hn : 2 ≤ n) {X : Subgroup (MulAut V)}
    (h : NatOmegaN n X) {b : ℕ} : ¬ Nonempty (↥X ≃* alternatingGroup (Fin (2 * b + 1))) := by
  rintro ⟨e⟩
  have hS := isSimpleGroup_sl2_gf hn
  by_cases hb : 5 ≤ 2 * b + 1
  · have hsimple : IsSimpleGroup (alternatingGroup (Fin (2 * b + 1))) :=
      alternatingGroup.isSimpleGroup (by simpa using hb)
    rcases h.cases hn with ⟨⟨θ⟩, -⟩ | ⟨⟨θ⟩, -⟩
    · have : IsSimpleGroup (SLq n × SLq n) := (θ.symm.trans e).isSimpleGroup
      exact not_isSimpleGroup_prod this
    · have := (alt_sl2_iso hb (by omega : 2 ≤ 2 * n) (e.symm.trans θ)).2
      omega
  · have hsolv : Group.IsSolvable (alternatingGroup (Fin (2 * b + 1))) :=
      alternatingGroup.isSolvable (by simp; omega)
    rcases h.cases hn with ⟨⟨θ⟩, -⟩ | ⟨⟨θ⟩, -⟩
    · have h1 : Group.IsSolvable (SLq n × SLq n) :=
        Group.isSolvable_of_surjective (f := (e.symm.trans θ).toMonoidHom)
          (e.symm.trans θ).surjective
      exact sl2_not_isSolvable hn
        (Group.isSolvable_of_surjective (f := MonoidHom.fst (SLq n) (SLq n))
          fun s => ⟨(s, 1), rfl⟩)
    · exact sl2_not_isSolvable (by omega : 2 ≤ 2 * n)
        (Group.isSolvable_of_surjective (f := (e.symm.trans θ).toMonoidHom)
          (e.symm.trans θ).surjective)

theorem NatOmegaN.false_of_sl2 {n k : ℕ} (hn : 2 ≤ n) (hk : 2 ≤ k) {X : Subgroup (MulAut V)}
    (h : NatOmegaN n X) (e : ↥X ≃* SLq k) (hcard : Nat.card ↥(commV X) = 2 ^ (3 * k)) : False := by
  have hSn := isSimpleGroup_sl2_gf hn
  have hSk := isSimpleGroup_sl2_gf hk
  rcases h.cases hn with ⟨⟨θ⟩, -⟩ | ⟨⟨θ⟩, hc⟩
  · have : IsSimpleGroup (SLq n × SLq n) := (θ.symm.trans e).isSimpleGroup
    exact not_isSimpleGroup_prod this
  · have h1 : Nat.card (SLq (2 * n)) = Nat.card (SLq k) := Nat.card_congr (θ.symm.trans e).toEquiv
    have h2 : 2 * n = k := sl2_card_inj (by omega) (by omega) h1
    subst h2
    rw [hc] at hcard
    have := Nat.pow_right_injective (le_refl 2) hcard
    omega

theorem NatOmegaN.commutator_eq_self {n : ℕ} (hn : 2 ≤ n) {X : Subgroup (MulAut V)}
    (h : NatOmegaN n X) : ⁅X, X⁆ = X := by
  have : Group.IsPerfect ↥X := by
    rcases h.cases hn with ⟨⟨θ⟩, -⟩ | ⟨⟨θ⟩, -⟩
    · have := isPerfect_prod (isPerfect_sl2 hn) (isPerfect_sl2 hn)
      exact Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
    · have := isPerfect_sl2 (by omega : 2 ≤ 2 * n)
      exact Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

end NatOmega

end CFSG.CGT.PushingUpLit.CGT6
