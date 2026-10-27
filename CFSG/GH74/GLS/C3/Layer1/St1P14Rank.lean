module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Final
public import CFSG.GH74.GLS.Stage1.Thm6.M12Type
public import CFSG.Foundations.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.P14

open Subgroup SemidirectProduct CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec13

section Model

theorem card_inv_N4 : Nat.card {n : N4 // n * n = 1} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_inv_swap_N4 : Nat.card {n : N4 // n * n = 1 ∧ n.swap = n} = 2 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_G2 : Nat.card G2 = 4 := by
  simp [G2, C2]

variable {S : Type} [Group S] {a b y x : S}

theorem swap_conj (h : M12Struct a b y x) (n : N4) : y * liftN h n * y⁻¹ = liftN h n.swap := by
  have hh : (MulAut.conj y).toMonoidHom.comp (liftN h) =
      (liftN h).comp (MulEquiv.prodComm : N4 ≃* N4).toMonoidHom := by
    apply ext_N4
    · simp [liftN_e1, liftN_1e, h.hya]
    · simp [liftN_e1, liftN_1e, h.hyb]
  have := DFunLike.congr_fun hh n
  simpa using this

theorem liftN_eq_toGroup_inl (h : M12Struct a b y x) (n : N4) :
    liftN h n = toGroup h (SemidirectProduct.inl n) := by
  simp [Stage1.Thm6.toGroup]

theorem liftG_eq_toGroup_inr (h : M12Struct a b y x) (g : G2) :
    liftG h g = toGroup h (SemidirectProduct.inr g) := by
  simp [Stage1.Thm6.toGroup]

theorem liftN_injective [Finite S] (hcard : Nat.card S = 64) (h : M12Struct a b y x) :
    Function.Injective (liftN h) := by
  intro n n' hn
  have h1 : toGroup h (SemidirectProduct.inl n) = toGroup h (SemidirectProduct.inl n') := by
    rwa [← liftN_eq_toGroup_inl, ← liftN_eq_toGroup_inl]
  exact SemidirectProduct.inl_injective ((toGroup_bijective hcard h).1 h1)

theorem rank_le_of_M12Struct [Finite S] (hcard : Nat.card S = 64) (h : M12Struct a b y x)
    (E : Subgroup S) (hE : ∀ e ∈ E, e * e = 1 ∧ ∀ e' ∈ E, e * e' = e' * e) :
    Nat.card E ≤ 8 := by
  classical
  have hbij := toGroup_bijective hcard h
  let eq : (N4 ⋊[phi] G2) ≃* S := MulEquiv.ofBijective (toGroup h) hbij
  let π : S →* G2 := (SemidirectProduct.rightHom (φ := phi)).comp eq.symm.toMonoidHom
  let f : ↥E →* G2 := π.domRestrict E
  have hcardE : Nat.card E = Nat.card f.range * Nat.card f.ker := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker] at h1
    rw [← h1, mul_comm]
  have hker_right : ∀ k : ↥f.ker, (eq.symm ((k : ↥E) : S)).right = 1 := by
    intro k
    have hk : (SemidirectProduct.rightHom (φ := phi)) (eq.symm ((k : ↥E) : S)) = 1 := k.2
    rwa [rightHom_eq_right] at hk
  have hker_eq : ∀ k : ↥f.ker, ((k : ↥E) : S) =
      liftN h (eq.symm ((k : ↥E) : S)).left := by
    intro k
    have hm : eq.symm ((k : ↥E) : S) = SemidirectProduct.inl (eq.symm ((k : ↥E) : S)).left :=
      SemidirectProduct.ext (by simp) (by simp [hker_right k])
    calc ((k : ↥E) : S) = eq (eq.symm ((k : ↥E) : S)) := (eq.apply_symm_apply _).symm
      _ = toGroup h (SemidirectProduct.inl (eq.symm ((k : ↥E) : S)).left) := by
          rw [← hm]; rfl
      _ = liftN h (eq.symm ((k : ↥E) : S)).left := (liftN_eq_toGroup_inl h _).symm
  have hker_sq : ∀ k : ↥f.ker, (eq.symm ((k : ↥E) : S)).left * (eq.symm ((k : ↥E) : S)).left = 1 := by
    intro k
    have h1 := (hE _ (k : ↥E).2).1
    rw [hker_eq k, ← map_mul] at h1
    apply liftN_injective hcard h
    rw [h1, map_one]
  have hker_inj : Function.Injective (fun k : ↥f.ker =>
      (⟨(eq.symm ((k : ↥E) : S)).left, hker_sq k⟩ : {n : N4 // n * n = 1})) := by
    intro k k' hk
    have hl : (eq.symm ((k : ↥E) : S)).left = (eq.symm ((k' : ↥E) : S)).left :=
      congrArg Subtype.val hk
    apply Subtype.ext
    apply Subtype.ext
    rw [hker_eq k, hker_eq k', hl]
  have hker4 : Nat.card f.ker ≤ 4 := by
    have := Nat.card_le_card_of_injective _ hker_inj
    rwa [card_inv_N4] at this
  have hdvd : Nat.card f.range ∣ 4 := by
    have := Subgroup.card_subgroup_dvd_card f.range
    rwa [card_G2] at this
  have hrange : Nat.card f.range = 1 ∨ Nat.card f.range = 2 ∨ Nat.card f.range = 4 := by
    have hle : Nat.card f.range ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < Nat.card f.range := Nat.card_pos
    generalize Nat.card f.range = c at hdvd hle hpos ⊢
    interval_cases c <;> omega
  rcases hrange with hr | hr | hr
  · rw [hcardE, hr]; omega
  · rw [hcardE, hr]; omega
  ·
    have htop : f.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hr, card_G2]
    have hmem : ((Multiplicative.ofAdd (1 : ZMod 2), 1) : G2) ∈ f.range := by
      rw [htop]; trivial
    obtain ⟨s1, hs1⟩ := hmem
    have hs1r : (eq.symm ((s1 : ↥E) : S)).right = (Multiplicative.ofAdd (1 : ZMod 2), 1) := by
      have hs1' : (SemidirectProduct.rightHom (φ := phi)) (eq.symm ((s1 : ↥E) : S)) =
          (Multiplicative.ofAdd (1 : ZMod 2), 1) := hs1
      rwa [rightHom_eq_right] at hs1'
    set m1 := eq.symm ((s1 : ↥E) : S) with hm1
    have hs1eq : ((s1 : ↥E) : S) = liftN h m1.left * y := by
      calc ((s1 : ↥E) : S) = eq m1 := (eq.apply_symm_apply _).symm
        _ = eq (SemidirectProduct.inl m1.left * SemidirectProduct.inr m1.right) := by
            rw [SemidirectProduct.inl_left_mul_inr_right]
        _ = liftN h m1.left * liftG h m1.right := by
            rw [map_mul, liftN_eq_toGroup_inl, liftG_eq_toGroup_inr]; rfl
        _ = liftN h m1.left * y := by rw [hs1r, liftG_e1]
    have hswap : ∀ k : ↥f.ker, (eq.symm ((k : ↥E) : S)).left.swap =
        (eq.symm ((k : ↥E) : S)).left := by
      intro k
      set n := (eq.symm ((k : ↥E) : S)).left with hn
      have hc := (hE _ (s1 : ↥E).2).2 _ (k : ↥E).2
      rw [hs1eq, hker_eq k, ← hn] at hc
      have hy : y * liftN h n = liftN h n.swap * y := by
        have := swap_conj h n
        calc y * liftN h n = (y * liftN h n * y⁻¹) * y := by group
          _ = liftN h n.swap * y := by rw [this]
      have h2 : liftN h m1.left * (liftN h n.swap * y) = liftN h n * liftN h m1.left * y := by
        calc liftN h m1.left * (liftN h n.swap * y)
            = liftN h m1.left * (y * liftN h n) := by rw [hy]
          _ = liftN h m1.left * y * liftN h n := by group
          _ = liftN h n * (liftN h m1.left * y) := hc
          _ = liftN h n * liftN h m1.left * y := by group
      have h3 : liftN h m1.left * liftN h n.swap = liftN h n * liftN h m1.left := by
        have := h2
        rw [← mul_assoc] at this
        exact mul_right_cancel this
      rw [← map_mul, ← map_mul] at h3
      have h4 := liftN_injective hcard h h3
      have h5 : m1.left * n.swap = m1.left * n := by rw [h4]; exact mul_comm _ _
      exact mul_left_cancel h5
    have hker_inj' : Function.Injective (fun k : ↥f.ker =>
        (⟨(eq.symm ((k : ↥E) : S)).left, hker_sq k, hswap k⟩ :
          {n : N4 // n * n = 1 ∧ n.swap = n})) := by
      intro k k' hk
      have hl : (eq.symm ((k : ↥E) : S)).left = (eq.symm ((k' : ↥E) : S)).left :=
        congrArg Subtype.val hk
      apply Subtype.ext
      apply Subtype.ext
      rw [hker_eq k, hker_eq k', hl]
    have hker2 : Nat.card f.ker ≤ 2 := by
      have := Nat.card_le_card_of_injective _ hker_inj'
      rwa [card_inv_swap_N4] at this
    rw [hcardE, hr]; omega

end Model

section Transport

variable {G : Type} [Group G]

theorem rank2LE_of_M12Data [Finite G] {S : Subgroup G} {a b y x : G} (h : M12Data S a b y x) :
    Rank2LE S 3 := by
  classical
  intro E hES hEel
  have hmem : ∀ z ∈ ({a, b, y, x} : Set G), z ∈ S := fun z hz =>
    h.gen ▸ Subgroup.subset_closure hz
  have haS : a ∈ S := hmem a (by simp)
  have hbS : b ∈ S := hmem b (by simp)
  have hyS : y ∈ S := hmem y (by simp)
  have hxS : x ∈ S := hmem x (by simp)
  let a' : ↥S := ⟨a, haS⟩
  let b' : ↥S := ⟨b, hbS⟩
  let y' : ↥S := ⟨y, hyS⟩
  let x' : ↥S := ⟨x, hxS⟩
  have hst : M12Struct a' b' y' x' := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact Subtype.ext h.ha
    · exact Subtype.ext h.hb
    · exact Subtype.ext h.hab
    · apply Subtype.ext
      simpa [pow_two] using h.hy
    · apply Subtype.ext
      simpa [pow_two] using h.hx
    · exact Subtype.ext h.hyx
    · exact Subtype.ext h.hya
    · exact Subtype.ext h.hyb
    · exact Subtype.ext h.hxa
    · exact Subtype.ext h.hxb
    · have hmap : (Subgroup.closure ({a', b', y', x'} : Set ↥S)).map S.subtype = S := by
        rw [MonoidHom.map_closure]
        have : S.subtype '' ({a', b', y', x'} : Set ↥S) = ({a, b, y, x} : Set G) := by
          ext z
          simp [a', b', y', x']
        rw [this]
        exact h.gen
      rw [eq_top_iff]
      intro t _
      have ht : (t : G) ∈ (Subgroup.closure ({a', b', y', x'} : Set ↥S)).map S.subtype := by
        rw [hmap]; exact t.2
      obtain ⟨u, hu, hut⟩ := ht
      have : u = t := Subtype.ext hut
      exact this ▸ hu
  have hcard : Nat.card ↥S = 64 := h.card
  let E1 : Subgroup ↥S := E.subgroupOf S
  have hE1 : ∀ e ∈ E1, e * e = 1 ∧ ∀ e' ∈ E1, e * e' = e' * e := by
    intro e he
    have he1 : (e : G) ∈ E := he
    refine ⟨?_, fun e' he' => ?_⟩
    · exact Subtype.ext (hEel _ he1).1
    · have he1' : (e' : G) ∈ E := he'
      exact Subtype.ext ((hEel _ he1).2 _ he1')
  have hcardE : Nat.card E1 = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hES).toEquiv
  have := rank_le_of_M12Struct hcard hst E1 hE1
  rw [hcardE] at this
  simpa using this

omit [Group G] in
theorem elemAb2_of_isElementaryAbelian {G : Type} [Group G] {A : Subgroup G}
    (h : CFSG.IsElementaryAbelian 2 ↥A) : IsElemAb2 A := by
  intro a ha
  refine ⟨?_, fun b hb => ?_⟩
  · have h2 : (⟨a, ha⟩ : ↥A) ^ 2 = 1 :=
      (Monoid.exponent_dvd_iff_forall_pow_eq_one.1 h.exponent_dvd_p) ⟨a, ha⟩
    have := congrArg Subtype.val h2
    simpa [pow_two] using this
  · have := h.toIsMulCommutative.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    exact congrArg Subtype.val this

theorem exists_conj_le_of_sylow2In [Finite G] {S P : Subgroup G} (hS : Sylow2In S ⊤)
    (hP : IsPGroup 2 P) : ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ S := by
  have := Fact.mk Nat.prime_two
  obtain ⟨-, hS2, hidx⟩ := hS
  rw [relIndex_top_right] at hidx
  set R : Sylow 2 G := hS2.toSylow hidx with hR
  obtain ⟨R', hR'⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R' R
  refine ⟨g, ?_⟩
  have h1 : ((g • R' : Sylow 2 G) : Subgroup G) = S := by rw [hg, hR, IsPGroup.toSylow_coe]
  rw [Sylow.coe_subgroup_smul] at h1
  rw [← h1]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.smul_mem_pointwise_smul _ _ _ (hR' hx)

theorem pRank_le_of_rank2LE [Finite G] {S : Subgroup G} (hS : Sylow2In S ⊤) {n : ℕ}
    (hR : Rank2LE S n) : CFSG.pRank 2 G ≤ n := by
  unfold CFSG.pRank
  apply csSup_le'
  rintro r ⟨A, hA, hAr⟩
  have hAp : IsPGroup 2 A := IsPGroup.of_card hAr
  obtain ⟨g, hg⟩ := exists_conj_le_of_sylow2In hS hAp
  have hel := elemAb2_of_isElementaryAbelian hA
  let A' : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hel' : IsElemAb2 A' := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨?_, ?_⟩
    · have := (hel u hu).1
      show (MulAut.conj g) u * (MulAut.conj g) u = 1
      rw [← map_mul, this, map_one]
    · rintro _ ⟨v, hv, rfl⟩
      show (MulAut.conj g) u * (MulAut.conj g) v = (MulAut.conj g) v * (MulAut.conj g) u
      rw [← map_mul, ← map_mul, (hel u hu).2 v hv]
  have hcard : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have := hR A' hg hel'
  rw [hcard, hAr] at this
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this

theorem pRank_le_three_of_M12Data [Finite G] {S : Subgroup G} {a b y x : G} (hS : Sylow2In S ⊤)
    (h : M12Data S a b y x) : CFSG.pRank 2 G ≤ 3 :=
  pRank_le_of_rank2LE hS (rank2LE_of_M12Data h)

theorem not_sylow_card_eight [Finite G] {S : Subgroup G} (hS : Sylow2In S ⊤) (h8 : Nat.card S = 8)
    (hr : CFSG.pRank 2 G = 4) : False := by
  have hR : Rank2LE S 3 := fun E hES _ => by
    have := Subgroup.card_le_of_le hES
    rw [h8] at this
    simpa using this
  have := pRank_le_of_rank2LE hS hR
  omega

end Transport

end CFSG.GH74.GLS.C3.Layer1.P14
