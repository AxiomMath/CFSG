module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.HNFiveNoComp

public section

namespace CFSG.HardMathSupport.Dickson.I271

open CFSG.Open

private theorem card_quaternionGroup_four : Nat.card (QuaternionGroup 4) = 16 := by
  simp [Nat.card_eq_fintype_card, QuaternionGroup.card]

section Quat

variable {G : Type*} [Group G]

private def quatMap (A X : G) : QuaternionGroup 4 → G
  | .a i => A ^ i.val
  | .xa i => X * A ^ i.val

theorem tabMSeven_exists_quat {A X : G} (hA : orderOf A = 8) (hX : X ^ 2 = A ^ 4)
    (hXA : X * A * X⁻¹ = A⁻¹) :
    ∃ S : Subgroup G, Nonempty (↥S ≃* QuaternionGroup 4) ∧ A ∈ S ∧ X ∈ S ∧ Nat.card S = 16 := by
  have hadd : ∀ i j : ZMod (2 * 4), A ^ (i + j).val = A ^ i.val * A ^ j.val := by
    intro i j
    rw [← pow_add, ZMod.val_add]
    have h := pow_mod_orderOf A (i.val + j.val)
    rw [hA] at h
    exact h
  have hsub : ∀ i j : ZMod (2 * 4), A ^ (j - i).val = A⁻¹ ^ i.val * A ^ j.val := by
    intro i j
    have h := hadd (j - i) i
    rw [sub_add_cancel] at h
    rw [h, inv_pow]
    group
  have hAX : ∀ k : ℕ, A ^ k * X = X * A⁻¹ ^ k := by
    have h1 : A * X = X * A⁻¹ :=
      calc A * X = (X * A * X⁻¹)⁻¹ * X := by rw [hXA, inv_inv]
        _ = X * A⁻¹ := by group
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_assoc, h1, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have h4 : ((4 : ℕ) : ZMod (2 * 4)).val = 4 := rfl
  have hmul : ∀ x y : QuaternionGroup 4,
      quatMap A X (x * y) = quatMap A X x * quatMap A X y := by
    rintro (i | i) (j | j)
    · simp only [QuaternionGroup.a_mul_a, quatMap, hadd]
    · simp only [QuaternionGroup.a_mul_xa, quatMap]
      rw [hsub, ← mul_assoc (A ^ i.val), hAX, mul_assoc]
    · simp only [QuaternionGroup.xa_mul_a, quatMap]
      rw [hadd, mul_assoc]
    · simp only [QuaternionGroup.xa_mul_xa, quatMap]
      rw [add_sub_assoc, hadd, hsub, h4, ← hX,
        show X * A ^ i.val * (X * A ^ j.val) = X * (A ^ i.val * X) * A ^ j.val by group, hAX]
      simp only [pow_two, mul_assoc]
  let f : QuaternionGroup 4 →* G := MonoidHom.mk' (quatMap A X) hmul
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    rintro (i | i) h
    · change A ^ i.val = 1 at h
      rw [← orderOf_dvd_iff_pow_eq_one, hA] at h
      have hi : i.val = 0 := Nat.eq_zero_of_dvd_of_lt h (by have := ZMod.val_lt i; omega)
      rw [ZMod.val_eq_zero] at hi
      rw [hi, QuaternionGroup.a_zero]
    · change X * A ^ i.val = 1 at h
      exfalso
      rw [eq_inv_of_mul_eq_one_left h] at hXA
      have hAinv : A = A⁻¹ := by
        rw [← hXA]
        group
      have h2 : A ^ 2 = 1 := by
        rw [pow_two]
        nth_rw 2 [hAinv]
        exact mul_inv_cancel A
      have := orderOf_le_of_pow_eq_one (by norm_num) h2
      omega
  refine ⟨f.range, ⟨(MonoidHom.ofInjective hf).symm⟩, MonoidHom.mem_range.2 ⟨.a 1, ?_⟩,
    MonoidHom.mem_range.2 ⟨.xa 0, ?_⟩, ?_⟩
  · change A ^ (1 : ZMod (2 * 4)).val = A
    rw [show (1 : ZMod (2 * 4)).val = 1 from rfl, pow_one]
  · change X * A ^ (0 : ZMod (2 * 4)).val = X
    rw [ZMod.val_zero, pow_zero, mul_one]
  · rw [← Nat.card_congr (MonoidHom.ofInjective hf).toEquiv, card_quaternionGroup_four]

end Quat

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem tabMSeven_not_dvd_of_involutions {C : Subgroup G} {n : ℕ} (hn : 1 ≤ n)
    (h : ∀ v ∈ C, orderOf v = 2 →
      ¬ 2 ^ n ∣ Nat.card ↥(C ⊓ Subgroup.centralizer ({v} : Set G))) :
    ¬ 2 ^ n ∣ Nat.card ↥C := by
  intro hdvd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥C) := inferInstance
  have hP : 2 ^ n ∣ Nat.card (P : Subgroup ↥C) := P.pow_dvd_card_of_pow_dvd_card hdvd
  haveI : Nontrivial (P : Subgroup ↥C) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    have h2 : 2 ∣ Nat.card (P : Subgroup ↥C) := (dvd_pow_self 2 (by omega)).trans hP
    have := Nat.card_pos (α := (P : Subgroup ↥C))
    omega
  have hZ : IsPGroup 2 (Subgroup.center (P : Subgroup ↥C)) := P.isPGroup'.to_subgroup _
  haveI : Nontrivial (Subgroup.center (P : Subgroup ↥C)) := P.isPGroup'.center_nontrivial
  obtain ⟨k, hk, hcard⟩ := hZ.nontrivial_iff_card.1 inferInstance
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center (P : Subgroup ↥C)) 2
    (by rw [hcard]; exact dvd_pow_self 2 hk.ne')
  set v : G := (((z : (P : Subgroup ↥C)) : ↥C) : G) with hvdef
  have hv : orderOf v = 2 := by
    rw [hvdef, Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz]
  apply h v ((z : (P : Subgroup ↥C)) : ↥C).2 hv
  have hle : (P : Subgroup ↥C).map C.subtype ≤ C ⊓ Subgroup.centralizer ({v} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    refine Subgroup.mem_inf.2 ⟨x.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hzx := Subgroup.mem_center_iff.1 z.2 ⟨x, hx⟩
    have := congrArg (fun y : (P : Subgroup ↥C) => ((y : ↥C) : G)) hzx
    simpa [hvdef] using this
  refine hP.trans ?_
  rw [← Subgroup.card_map_of_injective C.subtype_injective]
  exact Subgroup.card_dvd_of_le hle

theorem tabMSeven_sylow_quat {C S : Subgroup G} (hSC : S ≤ C) (e : ↥S ≃* QuaternionGroup 4)
    (h32 : ¬ 32 ∣ Nat.card ↥C) :
    ∃ P : Sylow 2 ↥C, Nonempty ((P : Subgroup ↥C) ≃* QuaternionGroup 4) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : Nat.card (S.subgroupOf C) = 16 := by
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe hSC).trans e).toEquiv,
      card_quaternionGroup_four]
  have hC0 : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have h16 : 2 ^ 4 ∣ Nat.card ↥C := by
    rw [show 2 ^ 4 = 16 by norm_num, ← hS]
    exact Subgroup.card_subgroup_dvd_card _
  have hfac : (Nat.card ↥C).factorization 2 = 4 := by
    have h1 := (Nat.prime_two.pow_dvd_iff_le_factorization hC0).1 h16
    have h2 : ¬ 5 ≤ (Nat.card ↥C).factorization 2 := fun h5 =>
      h32 (by simpa using (Nat.prime_two.pow_dvd_iff_le_factorization hC0).2 h5)
    omega
  exact ⟨Sylow.ofCard (S.subgroupOf C) (by rw [hS, hfac]; norm_num),
    ⟨(Subgroup.subgroupOfEquivOfLe hSC).trans e⟩⟩

end Sylow

section NoComp

variable {G : Type} [Group G] [Finite G]

private theorem odd_card_oddCore_of_finite (H : Type*) [Group H] [Finite H] :
    Odd (Nat.card (CFSG.oddCore H)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : CFSG.oddCore H ≤ CFSG.pPrimeCore 2 H :=
    sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  exact Nat.coprime_two_left.mp
    ((CFSG.pPrimeCore_coprime_card (p := 2) (G := H)).of_dvd_right
      (Subgroup.card_dvd_of_le hle))

private theorem factorization_seven_le_of_le_centralizer
    (hinv : ∀ v : G, orderOf v = 2 → ∀ R : Subgroup G, IsPGroup 7 R →
      R ≤ Subgroup.centralizer ({v} : Set G) → Nat.card R ≤ 7 ^ 2)
    {v : G} (hv : orderOf v = 2) {L : Subgroup G}
    (hL : L ≤ Subgroup.centralizer ({v} : Set G)) : (Nat.card L).factorization 7 ≤ 2 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨T⟩ : Nonempty (Sylow 7 ↥L) := inferInstance
  have h := hinv v hv ((T : Subgroup ↥L).map L.subtype) (T.isPGroup'.map L.subtype)
    ((Subgroup.map_subtype_le _).trans hL)
  rw [Subgroup.card_map_of_injective L.subtype_injective, Sylow.card_eq_multiplicity] at h
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h

private theorem mul_comm_of_mem_normalizer_zpowers {H : Type*} [Group H] {u g : H}
    (hu : orderOf u = 2) (hg : g ∈ Subgroup.normalizer (Subgroup.zpowers u : Set H)) :
    g * u = u * g := by
  have h1 : g * u * g⁻¹ ∈ Subgroup.zpowers u :=
    (Subgroup.mem_normalizer_iff.1 hg u).1 (Subgroup.mem_zpowers u)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  rw [← zpow_mod_orderOf, hu, Nat.cast_ofNat] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h0
  · rw [h0, zpow_zero] at hk
    have hu1 : u = 1 := by
      have := congrArg (fun x => g⁻¹ * x * g) hk
      simpa [mul_assoc] using this.symm
    rw [hu1, orderOf_one] at hu
    exact absurd hu (by norm_num)
  · rw [h0, zpow_one] at hk
    calc g * u = g * u * g⁻¹ * g := by group
      _ = u * g := by rw [← hk]

theorem tabMSeven_noComp {C : Subgroup G} (hO : GLAPPrimeCoreOf 7 C = ⊥)
    (hQ : ∃ P : Sylow 2 ↥C, Nonempty ((P : Subgroup ↥C) ≃* QuaternionGroup 4))
    (h7 : 7 ^ 5 ∣ Nat.card ↥C)
    (hinv : ∀ v : G, orderOf v = 2 → ∀ R : Subgroup G, IsPGroup 7 R →
      R ≤ Subgroup.centralizer ({v} : Set G) → Nat.card R ≤ 7 ^ 2)
    (J : Subgroup G) : ¬ GLAPComponent 7 C J := by
  intro hJ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJC : J ≤ C := hJ.1
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    CFSG.HardMathSupport.Solomon.Coordinator.isQuasisimple_of_glaPComponent_of_comm
      (by norm_num) hJ
      (fun g _ o ho => by
        rw [hO, Subgroup.mem_bot] at ho
        rw [ho, one_mul, mul_one])
  have hcomp : CFSG.Assembly.IsComponentOf J C :=
    CFSG.Assembly.isComponentOf_iff_open.2 ⟨hJC, hJ.2.1, hJq⟩
  haveI : Group.IsPerfect ↥J := ⟨hJq.1⟩
  haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJq.2
  haveI : Nontrivial ↥J := (QuotientGroup.mk'_surjective (Subgroup.center ↥J)).nontrivial
  have hJodd : ¬ Odd (Nat.card ↥J) := fun h =>
    Group.IsPerfect.not_isSolvable (↥J) (CFSG.FeitThompson.isSolvable_of_odd_natCard _ h)
  set O : Subgroup ↥C := CFSG.oddCore ↥C
  haveI hOn : O.Normal := CFSG.oddCore_normal _
  have hOodd : Odd (Nat.card O) := odd_card_oddCore_of_finite ↥C
  set OG : Subgroup G := O.map C.subtype
  have hOGcard : Nat.card OG = Nat.card O := Subgroup.card_map_of_injective C.subtype_injective
  have hOGC : OG ≤ C := Subgroup.map_subtype_le O
  have hNOG : C ≤ Subgroup.normalizer (OG : Set G) := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hOGC).1 ?_
    have h : OG.subgroupOf C = O :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective O
    rw [h]
    exact hOn
  have hJOG : ⁅J, OG⁆ = ⊥ := by
    rcases hnComp_le_or_commute hcomp hOGC hNOG with h | h
    · have hOGodd : Odd (Nat.card OG) := by rw [hOGcard]; exact hOodd
      exact absurd (hOGodd.of_dvd_nat (Subgroup.card_dvd_of_le h)) hJodd
    · exact h
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥J) 2
    (even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hJodd))
  have hsv : orderOf (s : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hs
  have hOGs : OG ≤ Subgroup.centralizer ({(s : G)} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.1
      ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hJOG) s.2) q hq
  have hfO : (Nat.card O).factorization 7 ≤ 2 := by
    have := factorization_seven_le_of_le_centralizer hinv hsv hOGs
    rwa [hOGcard] at this
  obtain ⟨P, ⟨eP⟩⟩ := hQ
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(P : Subgroup ↥C)) 2
    (by rw [Nat.card_congr eP.toEquiv, card_quaternionGroup_four]; norm_num)
  set u : ↥C := (t : ↥C) with hudef
  have hu : orderOf u = 2 := by rw [hudef, Subgroup.orderOf_coe]; exact ht
  have hBS : (QuotientGroup.mk u : ↥C ⧸ O) ∈ Subgroup.center (↥C ⧸ O) :=
    CFSG.BrauerSuzuki.brauer_suzuki 4 (by norm_num) P ⟨eP⟩ u t.2 hu
  have hub : orderOf (QuotientGroup.mk u : ↥C ⧸ O) = 2 := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hu, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      have h2 := orderOf_dvd_natCard (⟨u, (QuotientGroup.eq_one_iff u).1 h1⟩ : O)
      rw [Subgroup.orderOf_mk, hu] at h2
      exact Nat.not_even_iff_odd.2 hOodd (even_iff_two_dvd.2 h2)
  set Z : Subgroup (↥C ⧸ O) := Subgroup.zpowers (QuotientGroup.mk u) with hZdef
  have hZn : Z.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [Subgroup.mem_center_iff.1 (Subgroup.zpow_mem _ hBS k) g, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers _ k
  set K : Subgroup ↥C := Z.comap (QuotientGroup.mk' O) with hKdef
  haveI : K.Normal := hZn.comap _
  have hKcard : Nat.card K = Nat.card O * 2 := by
    rw [← hub, ← Nat.card_zpowers]
    exact QuotientGroup.card_preimage_mk O (Z : Set (↥C ⧸ O))
  have huK : u ∈ K := Subgroup.mem_zpowers _
  have hfacK : (Nat.card K).factorization 2 = 1 := by
    rw [hKcard, Nat.factorization_mul (Nat.card_pos (α := ↥O)).ne' two_ne_zero,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd fun h =>
        Nat.not_even_iff_odd.2 hOodd (even_iff_two_dvd.2 h), Nat.prime_two.factorization_self]
  have hFr := Sylow.normalizer_sup_eq_top (p := 2) (N := K)
    (Sylow.ofCard (Subgroup.zpowers ⟨u, huK⟩)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hu, hfacK, pow_one]))
  rw [Sylow.coe_ofCard, MonoidHom.map_zpowers] at hFr
  set N : Subgroup ↥C := Subgroup.normalizer (Subgroup.zpowers u : Set ↥C)
  have hFr' : N ⊔ K = ⊤ := hFr
  have hsurj : N.map (QuotientGroup.mk' O) = ⊤ := by
    have h1 := congrArg (Subgroup.map (QuotientGroup.mk' O)) hFr'
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O),
      hKdef, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)] at h1
    rw [← h1]
    refine (sup_eq_left.2 ?_).symm
    rw [hZdef, Subgroup.zpowers_le]
    exact Subgroup.mem_map_of_mem _ (Subgroup.le_normalizer (Subgroup.mem_zpowers u))
  have hCdvd : Nat.card ↥C ∣ Nat.card N * Nat.card O := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup O]
    refine Nat.mul_dvd_mul_right ?_ _
    have := Subgroup.card_map_dvd (H := N) (QuotientGroup.mk' O)
    rwa [hsurj, Subgroup.card_top] at this
  have hNG : N.map C.subtype ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
    rintro _ ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (mul_comm_of_mem_normalizer_zpowers hu hg)
  have huG : orderOf (u : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hu
  have hfN : (Nat.card N).factorization 7 ≤ 2 := by
    have := factorization_seven_le_of_le_centralizer hinv huG hNG
    rwa [Subgroup.card_map_of_injective C.subtype_injective] at this
  have hC0 : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
  have h5 : 5 ≤ (Nat.card ↥C).factorization 7 :=
    ((by norm_num : Nat.Prime 7).pow_dvd_iff_le_factorization hC0).1 h7
  have hle := (Nat.factorization_le_iff_dvd hC0
    (Nat.mul_ne_zero (Nat.card_pos (α := ↥N)).ne' (Nat.card_pos (α := ↥O)).ne')).2 hCdvd 7
  rw [Nat.factorization_mul (Nat.card_pos (α := ↥N)).ne' (Nat.card_pos (α := ↥O)).ne',
    Finsupp.add_apply] at hle
  omega

end NoComp

section Lift

variable {H : Type*} [Group H] [Finite H]

theorem tabMSeven_isConj_zpowers_of_quot {E : Subgroup H} [E.Normal] {p : ℕ} (hp : p.Prime)
    (hE : Nat.Coprime (Nat.card E) p) {y w : H} (hy : orderOf y = p) (hw : orderOf w = p)
    {c : H} {k : ℕ}
    (hck : (QuotientGroup.mk (c * y * c⁻¹) : H ⧸ E) = (QuotientGroup.mk w : H ⧸ E) ^ k) :
    ∃ g : H, ∃ m : ℕ, g * y * g⁻¹ = w ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpE : ¬ p ∣ Nat.card E := fun h => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hE.symm h)
  have hy' : orderOf (c * y * c⁻¹) = p := by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  have hwb : orderOf (QuotientGroup.mk w : H ⧸ E) = p := by
    apply orderOf_eq_prime
    · rw [← QuotientGroup.mk_pow, ← hw, pow_orderOf_eq_one, QuotientGroup.mk_one]
    · intro h1
      have h2 := orderOf_dvd_natCard (⟨w, (QuotientGroup.eq_one_iff w).1 h1⟩ : E)
      rw [Subgroup.orderOf_mk, hw] at h2
      exact hpE h2
  set L : Subgroup H :=
    (Subgroup.zpowers (QuotientGroup.mk w : H ⧸ E)).comap (QuotientGroup.mk' E)
  have hL : Nat.card L = Nat.card E * p := by
    rw [← hwb, ← Nat.card_zpowers]
    exact QuotientGroup.card_preimage_mk E (Subgroup.zpowers (QuotientGroup.mk w : H ⧸ E) : Set _)
  have hfac : (Nat.card L).factorization p = 1 := by
    rw [hL, Nat.factorization_mul (Nat.card_pos (α := ↥E)).ne' hp.ne_zero, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hpE, hp.factorization_self]
  have hwL : w ∈ L := Subgroup.mem_zpowers _
  have hyL : c * y * c⁻¹ ∈ L := by
    change (QuotientGroup.mk (c * y * c⁻¹) : H ⧸ E) ∈ Subgroup.zpowers (QuotientGroup.mk w)
    rw [hck]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k
  let Pw : Sylow p L := Sylow.ofCard (Subgroup.zpowers ⟨w, hwL⟩)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hw, hfac, pow_one])
  let Py : Sylow p L := Sylow.ofCard (Subgroup.zpowers ⟨c * y * c⁻¹, hyL⟩)
    (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hy', hfac, pow_one])
  obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L Py Pw
  have hmem : l * ⟨c * y * c⁻¹, hyL⟩ * l⁻¹ ∈ Subgroup.zpowers (⟨w, hwL⟩ : L) := by
    have h1 : l * ⟨c * y * c⁻¹, hyL⟩ * l⁻¹ ∈ ((l • Py : Sylow p L) : Subgroup L) := by
      rw [Sylow.coe_subgroup_smul]
      exact (Subgroup.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨⟨c * y * c⁻¹, hyL⟩, Subgroup.mem_zpowers _, rfl⟩
    rw [hl] at h1
    exact h1
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hmem)
  refine ⟨(l : H) * c, m, ?_⟩
  have h2 := congrArg Subtype.val hm
  simp only [SubmonoidClass.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  rw [h2]
  group

end Lift

end CFSG.HardMathSupport.Dickson.I271
