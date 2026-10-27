module

public import CFSG.LocalAnalysis.RankTwoShapes.HomocyclicSubgroup
public import CFSG.LocalAnalysis.RankTwoShapes.ClassTwo

public section

namespace CFSG.RankTwoShapes

open scoped commutatorElement

universe u

variable {Q : Type u} [Group Q]

@[expose] def omegaSub (A : Subgroup Q) (hA : IsMulCommutative A) (k : ℕ) : Subgroup Q where
  carrier := {a | a ∈ A ∧ a ^ (2 ^ k) = 1}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨A.mul_mem ha hb, ?_⟩
    have hc : Commute a b := congrArg Subtype.val (hA.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    rw [hc.mul_pow, ha', hb', one_mul]
  one_mem' := ⟨A.one_mem, one_pow _⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨A.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩

theorem mem_omegaSub {A : Subgroup Q} {hA : IsMulCommutative A} {k : ℕ} {a : Q} :
    a ∈ omegaSub A hA k ↔ a ∈ A ∧ a ^ (2 ^ k) = 1 := Iff.rfl

theorem omegaSub_le (A : Subgroup Q) (hA : IsMulCommutative A) (k : ℕ) : omegaSub A hA k ≤ A :=
  fun _ ha => ha.1

theorem omegaSub_mono (A : Subgroup Q) (hA : IsMulCommutative A) {k l : ℕ} (hkl : k ≤ l) :
    omegaSub A hA k ≤ omegaSub A hA l := by
  rintro a ⟨ha, ha'⟩
  refine ⟨ha, ?_⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, pow_mul, ha', one_pow]

theorem omegaSub_isMulCommutative (A : Subgroup Q) (hA : IsMulCommutative A) (k : ℕ) :
    IsMulCommutative (omegaSub A hA k) :=
  ⟨⟨fun a b => Subtype.ext (show (a : Q) * b = b * a from
    congrArg (fun z : A => (z : Q)) (hA.is_comm.comm ⟨a, a.2.1⟩ ⟨b, b.2.1⟩))⟩⟩

theorem card_multiplicative_zmod (n : ℕ) [NeZero n] :
    Nat.card (Multiplicative (ZMod n)) = n := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

@[expose] noncomputable def restrictAut (α : MulAut Q) (B : Subgroup Q)
    (h : B.map α.toMonoidHom = B) : MulAut B :=
  (α.subgroupMap B).trans (MulEquiv.subgroupCongr h)

theorem restrictAut_apply (α : MulAut Q) (B : Subgroup Q) (h : B.map α.toMonoidHom = B)
    (b : B) : ((restrictAut α B h b : B) : Q) = α b := rfl

variable [Finite Q]

theorem map_eq_of_invariant (α : MulAut Q) (B : Subgroup Q) (hB : ∀ b ∈ B, α b ∈ B) :
    B.map α.toMonoidHom = B := by
  have hle : B.map α.toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact hB b hb
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [Subgroup.card_map_of_injective α.injective]

theorem pow_two_pow_eq_one_of_orderOf_le {G : Type*} [Group G] (hG : IsPGroup 2 G) {k : ℕ}
    (g : G) (hg : orderOf g ≤ 2 ^ k) : g ^ (2 ^ k) = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hG g
  rw [hm] at hg
  have hmk : m ≤ k := (Nat.pow_le_pow_iff_right (by norm_num)).mp hg
  rw [← orderOf_dvd_iff_pow_eq_one, hm]
  exact Nat.pow_dvd_pow 2 hmk

theorem invariant_eq_omegaSub (hQ : IsPGroup 2 Q) (hrank : TwoRankLeTwo Q) (α : MulAut Q)
    (hα : α ^ 3 = 1) (hfpf : ∀ q : Q, α q = q → q = 1) (A : Subgroup Q)
    (hA : IsMulCommutative A) (B : Subgroup Q) (hBA : B ≤ A) (hB : ∀ b ∈ B, α b ∈ B) :
    ∃ k : ℕ, B = omegaSub A hA k ∧ Nat.card B = 4 ^ k ∧ ∃ b ∈ B, orderOf b = 2 ^ k := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hbot : B = ⊥
  · refine ⟨0, ?_, by simp [hbot], 1, B.one_mem, by simp⟩
    rw [hbot]
    ext a
    simp only [Subgroup.mem_bot, mem_omegaSub, pow_zero, pow_one]
    constructor
    · rintro rfl; exact ⟨A.one_mem, rfl⟩
    · exact fun h => h.2
  have hmap := map_eq_of_invariant α B hB
  set β := restrictAut α B hmap with hβ
  have hβ3 : β ^ 3 = 1 := by
    ext b
    have h := congrArg (fun γ : MulAut Q => γ (b : Q)) hα
    simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.one_apply] at h ⊢
    exact h
  have hβfpf : ∀ b : B, β b = b → b = 1 := by
    intro b hb
    have h : α (b : Q) = b := congrArg Subtype.val hb
    exact Subtype.ext (hfpf _ h)
  have hBp : IsPGroup 2 B := hQ.to_subgroup B
  have hBrank : TwoRankLeTwo B := by
    intro E hEcomm hEexp
    let E' : Subgroup Q := E.map B.subtype
    have hcard : Nat.card E' = Nat.card E :=
      Nat.card_congr (Subgroup.equivMapOfInjective _ _ B.subtype_injective).symm.toEquiv
    rw [← hcard]
    apply hrank E'
    · refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← ha, ← hb]
      exact congrArg (fun z : B => (z : Q)) (congrArg Subtype.val
        (hEcomm.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
    · rintro _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hEexp b hb)
  obtain ⟨b, hbmax⟩ := Finite.exists_max (fun c : B => orderOf c)
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hBp b
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    apply hbot
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc
    have hle := hbmax ⟨c, hc⟩
    rw [hk, hk0', pow_zero] at hle
    have h1 : orderOf (⟨c, hc⟩ : B) = 1 := le_antisymm hle (orderOf_pos _)
    have := orderOf_eq_one_iff.mp h1
    exact congrArg Subtype.val this
  have hBcomm : ∀ c d : B, c * d = d * c := fun c d =>
    Subtype.ext (show (c : Q) * d = d * c from
      congrArg (fun z : A => (z : Q)) (hA.is_comm.comm ⟨c, hBA c.2⟩ ⟨d, hBA d.2⟩))
  obtain ⟨-, -, ⟨eq⟩, -, -, -, htop⟩ :=
    three_automorphism_homocyclic_subgroup hBp hBrank β hβ3 hβfpf b hbmax hk hk1
  have hcardB : Nat.card B = 4 ^ k := by
    have h1 := Nat.card_congr eq.toEquiv
    rw [htop hBcomm, Subgroup.card_top, Nat.card_prod, card_multiplicative_zmod] at h1
    rw [h1, ← mul_pow]
    norm_num
  have hle : B ≤ omegaSub A hA k := by
    intro c hc
    refine ⟨hBA hc, ?_⟩
    have h := pow_two_pow_eq_one_of_orderOf_le hBp ⟨c, hc⟩ (hk ▸ hbmax ⟨c, hc⟩)
    exact congrArg Subtype.val h
  have hge : Nat.card (omegaSub A hA k) ≤ 4 ^ k :=
    card_le_four_pow_of_commutative hrank k _ (omegaSub_isMulCommutative A hA k)
      (fun c hc => hc.2)
  refine ⟨k, Subgroup.eq_of_le_of_card_ge hle (hcardB ▸ hge), hcardB, b, b.2, ?_⟩
  rw [← hk, Subgroup.orderOf_coe]

theorem card_omegaSub (hQ : IsPGroup 2 Q) (hrank : TwoRankLeTwo Q) (α : MulAut Q)
    (hα : α ^ 3 = 1) (hfpf : ∀ q : Q, α q = q → q = 1) (A : Subgroup Q)
    (hA : IsMulCommutative A) (hAinv : ∀ a ∈ A, α a ∈ A) {x : Q} (hxA : x ∈ A) {e : ℕ}
    (hx : orderOf x = 2 ^ e) {k : ℕ} (hk : k ≤ e) : Nat.card (omegaSub A hA k) = 4 ^ k := by
  have hinv : ∀ a ∈ omegaSub A hA k, α a ∈ omegaSub A hA k := by
    rintro a ⟨ha, ha'⟩
    exact ⟨hAinv a ha, by rw [← map_pow, ha', map_one]⟩
  obtain ⟨k', hk', hcard, b, hb, hbord⟩ := invariant_eq_omegaSub hQ hrank α hα hfpf A hA
    (omegaSub A hA k) (omegaSub_le A hA k) hinv
  have h1 : k' ≤ k := by
    have hdvd : orderOf b ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hb.2
    rw [hbord] at hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  have h2 : k ≤ k' := by
    have hmem : x ^ (2 ^ (e - k)) ∈ omegaSub A hA k := by
      refine ⟨A.pow_mem hxA _, ?_⟩
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hk, ← hx, pow_orderOf_eq_one]
    rw [hk'] at hmem
    have hdvd : orderOf x ∣ 2 ^ (e - k) * 2 ^ k' := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]; exact hmem.2
    rw [hx, ← pow_add] at hdvd
    have := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    omega
  rw [hcard, le_antisymm h1 h2]

@[expose] def commMap (hcen : CentralCommutators Q) (A : Subgroup Q) (s : Q) : A →* Q where
  toFun a := rcomm (a : Q) s
  map_one' := rcomm_one_left s
  map_mul' a b := rcomm_mul_left_central hcen a b s

omit [Finite Q] in
theorem commMap_apply (hcen : CentralCommutators Q) (A : Subgroup Q) (s : Q) (a : A) :
    commMap hcen A s a = rcomm (a : Q) s := rfl

omit [Finite Q] in
theorem mem_map_ker_commMap (hcen : CentralCommutators Q) (A : Subgroup Q) (s a : Q) :
    a ∈ (commMap hcen A s).ker.map A.subtype ↔ a ∈ A ∧ rcomm a s = 1 := by
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.2, hb⟩
  · rintro ⟨ha, h⟩
    exact ⟨⟨a, ha⟩, h, rfl⟩

omit [Finite Q] in
theorem rcomm_eq_one_iff (a s : Q) : rcomm a s = 1 ↔ a * s = s * a := by
  rw [rcomm]
  constructor
  · intro h
    have h' : a⁻¹ * (s⁻¹ * a * s) = 1 := by rw [← h]; group
    have h2 : s⁻¹ * a * s = a := by
      have := congrArg (a * ·) h'
      simpa [← mul_assoc] using this
    calc a * s = s * (s⁻¹ * a * s) := by group
      _ = s * a := by rw [h2]
  · intro h
    calc a⁻¹ * s⁻¹ * a * s = a⁻¹ * s⁻¹ * (a * s) := by group
      _ = 1 := by rw [h]; group

theorem mem_of_card_eq_four {H : Subgroup Q} (hH : Nat.card H = 4) {a b c d : Q} (ha : a ∈ H)
    (hb : b ∈ H) (hc : c ∈ H) (hd : d ∈ H) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) {v : Q} (hv : v ∈ H) :
    v = a ∨ v = b ∨ v = c ∨ v = d := by
  classical
  by_contra hne
  push Not at hne
  obtain ⟨hva, hvb, hvc, hvd⟩ := hne
  have hsub : ({v, a, b, c, d} : Set Q) ⊆ H := by
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl <;> assumption
  have hcard5 : ({v, a, b, c, d} : Set Q).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hva, hvb, hvc, hvd]),
      Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]),
      Set.ncard_pair hcd]
  have hncard : (H : Set Q).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hH
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard5, hncard] at hle
  omega

theorem free_three_action_order_sixty_four (hQ : IsPGroup 2 Q) (hrank : TwoRankLeTwo Q)
    (hnonab : ∃ a b : Q, a * b ≠ b * a) (α : MulAut Q) (hα : α ^ 3 = 1)
    (hfpf : ∀ q : Q, α q = q → q = 1) :
    Nat.card Q = 64 ∧ (∀ q : Q, q ^ 4 = 1) ∧
      Nat.card (Subgroup.center Q) = 4 ∧
      (∀ z : Q, z ∈ Subgroup.center Q ↔ z ^ 2 = 1) ∧
      ⁅(⊤ : Subgroup Q), ⊤⁆ = Subgroup.center Q ∧
      ∃ x y g h : Q, y = α x ∧ h = α g ∧
        x ^ 4 = 1 ∧ y ^ 4 = 1 ∧ rcomm x y = 1 ∧ rcomm g h = 1 ∧
        g ^ 2 = y ^ 2 ∧ h ^ 2 = x ^ 2 * y ^ 2 ∧ rcomm x g = x ^ 2 ∧
        rcomm y g = x ^ 2 * y ^ 2 ∧ rcomm x h = x ^ 2 * y ^ 2 ∧ rcomm y h = y ^ 2 ∧
        Subgroup.closure ({x, y, g, h} : Set Q) = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcen : CentralCommutators Q := centralCommutators_of_fpfThree α hα hfpf
  obtain ⟨hcz, hbal, hαleft, hcommα, hnorm⟩ := fixedPointFree_three_class_two α hα hfpf
  have hcube : ∀ q : Q, α (α (α q)) = q := fpfThree_cube α hα
  obtain ⟨x, hxmax⟩ := Finite.exists_max (fun q : Q => orderOf q)
  obtain ⟨e, he⟩ := IsPGroup.iff_orderOf.mp hQ x
  have hnontriv : ∃ q : Q, q ≠ 1 := by
    obtain ⟨a, b, hab⟩ := hnonab
    by_contra h
    push Not at h
    exact hab (by rw [h a, h b])
  have he1 : 1 ≤ e := by
    by_contra h0
    have he0 : e = 0 := by omega
    obtain ⟨q, hq⟩ := hnontriv
    have hle := hxmax q
    rw [he, he0, pow_zero] at hle
    exact hq (orderOf_eq_one_iff.mp (le_antisymm hle (orderOf_pos q)))
  set y := α x with hy
  obtain ⟨hAinv, hAcomm, ⟨eqA⟩, hZA, hAnormal, hAcent, -⟩ :=
    three_automorphism_homocyclic_subgroup hQ hrank α hα hfpf x hxmax he he1
  set A := Subgroup.closure ({x, α x} : Set Q) with hA
  have hxA : x ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyA : y ∈ A := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hcardA : Nat.card A = 4 ^ e := by
    rw [Nat.card_congr eqA.toEquiv, Nat.card_prod, card_multiplicative_zmod, ← mul_pow]
    norm_num
  set Z := Subgroup.center Q with hZ
  have hZcomm : IsMulCommutative Z := inferInstance
  have hZinv : ∀ z ∈ Z, α z ∈ Z := by
    intro z hz
    rw [hZ, Subgroup.mem_center_iff] at hz ⊢
    intro g
    have h := hz (α.symm g)
    have h' := congrArg α h
    simpa using h'
  obtain ⟨κ, hZκ, hZcard, z0, hz0, hz0ord⟩ :=
    invariant_eq_omegaSub hQ hrank α hα hfpf A hAcomm Z hZA hZinv
  have hAexp : ∀ q : Q, q ^ (2 ^ e) = 1 := fun q =>
    pow_two_pow_eq_one_of_orderOf_le hQ q (he ▸ hxmax q)
  have hnotab : ¬ ∀ a b : Q, a * b = b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    exact fun h => hab (h a b)
  have hκ1 : 1 ≤ κ := by
    by_contra h0
    have hκ0 : κ = 0 := by omega
    obtain ⟨q, hq⟩ := hnontriv
    have : Nontrivial Q := ⟨⟨q, 1, hq⟩⟩
    have hZnt : Nontrivial Z := IsPGroup.center_nontrivial hQ
    have hZ1 : Nat.card Z = 1 := by rw [hZcard, hκ0, pow_zero]
    rw [Nat.card_eq_one_iff_unique] at hZ1
    exact not_nontrivial_iff_subsingleton.mpr hZ1.1 hZnt
  have hκe : κ < e := by
    by_contra hge
    push Not at hge
    apply hnotab
    have hAZ : A ≤ Z := by
      intro a ha
      rw [hZκ]
      exact omegaSub_mono A hAcomm hge ⟨ha, hAexp a⟩
    have htop : A = ⊤ := by
      rw [← hAcent, eq_top_iff]
      intro q _
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_center_iff.mp (hAZ ha) q).symm
    intro a b
    have ha : a ∈ Z := hAZ (htop ▸ Subgroup.mem_top a)
    exact (Subgroup.mem_center_iff.mp ha b).symm
  set V := omegaSub A hAcomm 1 with hV
  have hVcard : Nat.card V = 4 := by
    rw [card_omegaSub hQ hrank α hα hfpf A hAcomm hAinv hxA he he1, pow_one]
  have hVZ : V ≤ Z := hZκ ▸ omegaSub_mono A hAcomm hκ1
  have hinvol : ∀ t : Q, t ^ 2 = 1 → t ∈ V := by
    intro t ht
    by_contra htV
    let E := Subgroup.closure ((V : Set Q) ∪ {t})
    have hpair : ((V : Set Q) ∪ {t}).Pairwise Commute := by
      intro a ha b hb _
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact congrArg (fun z : Z => (z : Q)) (hZcomm.is_comm.comm ⟨a, hVZ ha⟩ ⟨b, hVZ hb⟩)
      · rw [Set.mem_singleton_iff] at hb; subst hb
        exact (Subgroup.mem_center_iff.mp (hVZ ha) b).symm
      · rw [Set.mem_singleton_iff] at ha; subst ha
        exact Subgroup.mem_center_iff.mp (hVZ hb) a
      · rw [Set.mem_singleton_iff] at ha hb; subst ha; subst hb; exact Commute.refl _
    have hEcomm : IsMulCommutative E := Subgroup.isMulCommutative_closure hpair
    have hEexp : ∀ w ∈ E, w ^ 2 = 1 := by
      intro w hw
      induction hw using Subgroup.closure_induction with
      | mem w hw =>
        rcases hw with hw | hw
        · rw [hV] at hw
          simpa using hw.2
        · rw [Set.mem_singleton_iff] at hw; rw [hw]; exact ht
      | one => exact one_pow 2
      | mul a b ha hb pa pb =>
        have hc : Commute a b :=
          congrArg (fun z : E => (z : Q)) (hEcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
        rw [hc.mul_pow, pa, pb, one_mul]
      | inv a ha pa => rw [inv_pow, pa, inv_one]
    have hVE : V < E := by
      refine lt_of_le_of_ne (fun v hv => Subgroup.subset_closure (Or.inl hv)) ?_
      intro hVeq
      exact htV (hVeq ▸ Subgroup.subset_closure (Or.inr rfl))
    have hlt : Nat.card V < Nat.card E := Subgroup.card_lt_of_lt hVE
    have hle := hrank E hEcomm hEexp
    omega
  set K : Q → Subgroup Q := fun s => (commMap hcen A s).ker.map A.subtype with hK
  set R : Q → Subgroup Q := fun s => (commMap hcen A s).range with hR
  have hmemK : ∀ s a, a ∈ K s ↔ a ∈ A ∧ rcomm a s = 1 := fun s a =>
    mem_map_ker_commMap hcen A s a
  have hKle : ∀ s, K s ≤ A := fun s a ha => ((hmemK s a).mp ha).1
  have hKinv : ∀ s, ∀ a ∈ K s, α a ∈ K s := by
    intro s a ha
    obtain ⟨ha, h1⟩ := (hmemK s a).mp ha
    refine (hmemK s _).mpr ⟨hAinv a ha, ?_⟩
    rw [hαleft, h1, map_one, map_one]
  have hRZ : ∀ s, R s ≤ Z := by
    rintro s _ ⟨a, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    exact (hcen (a : Q) s g).symm.eq
  have hRle : ∀ s, R s ≤ A := fun s => (hRZ s).trans hZA
  have hRinv : ∀ s, ∀ c ∈ R s, α c ∈ R s := by
    rintro s _ ⟨a, rfl⟩
    refine ⟨⟨α (α (a : Q)), hAinv _ (hAinv _ a.2)⟩, ?_⟩
    change rcomm (α (α (a : Q))) s = α (rcomm (a : Q) s)
    rw [hαleft, hαleft, hcube]
  have hZK : ∀ s, Z ≤ K s := by
    intro s z hz
    refine (hmemK s z).mpr ⟨hZA hz, ?_⟩
    rw [rcomm_eq_one_iff]
    exact (Subgroup.mem_center_iff.mp hz s).symm
  have hKRcard : ∀ s, Nat.card (K s) * Nat.card (R s) = 4 ^ e := by
    intro s
    rw [← hcardA, ← Subgroup.card_ker_mul_card_range (commMap hcen A s)]
    congr 1
    exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ A.subtype_injective).symm.toEquiv
  have hKomega : ∀ s, ∃ k, K s = omegaSub A hAcomm k ∧ Nat.card (K s) = 4 ^ k := by
    intro s
    obtain ⟨k, h1, h2, -⟩ := invariant_eq_omegaSub hQ hrank α hα hfpf A hAcomm (K s) (hKle s)
      (hKinv s)
    exact ⟨k, h1, h2⟩
  have hRomega : ∀ s, ∃ l, R s = omegaSub A hAcomm l ∧ Nat.card (R s) = 4 ^ l ∧
      ∃ c ∈ R s, orderOf c = 2 ^ l := fun s =>
    invariant_eq_omegaSub hQ hrank α hα hfpf A hAcomm (R s) (hRle s) (hRinv s)
  obtain ⟨g, hgmin⟩ := Finite.exists_min (fun s : Q => Nat.card (K s))
  have hKgZ : K g = Z := by
    apply le_antisymm _ (hZK g)
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨kg, hkg, hkgc⟩ := hKomega g
    obtain ⟨ks, hks, hksc⟩ := hKomega s
    have hle : kg ≤ ks := by
      have h := hgmin s
      rw [hkgc, hksc] at h
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h
    have has : a ∈ K s := by
      rw [hks]; rw [hkg] at ha; exact omegaSub_mono A hAcomm hle ha
    exact ((rcomm_eq_one_iff a s).mp ((hmemK s a).mp has).2).symm
  have hKgcard : Nat.card (K g) = 4 ^ κ := by rw [hKgZ, hZcard]
  obtain ⟨l, hRg, hRgcard, c0, hc0, hc0ord⟩ := hRomega g
  have hle : e - κ = l := by
    have h := hKRcard g
    rw [hKgcard, hRgcard, ← pow_add] at h
    have := Nat.pow_right_injective (by norm_num : 2 ≤ 4) h
    omega
  have h2κ : e ≤ 2 * κ := by
    have h := Subgroup.card_le_of_le (hRZ g)
    rw [hRgcard, hZcard] at h
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h
    omega
  have hl1 : 1 ≤ l := by omega
  have hRgmem : ∀ a : Q, a ∈ A → rcomm a g ^ (2 ^ l) = 1 := by
    intro a ha
    have hc : rcomm a g ∈ R g := ⟨⟨a, ha⟩, rfl⟩
    rw [hRg] at hc
    exact hc.2
  have hAab : ∀ a b : Q, a ∈ A → b ∈ A → a * b = b * a := fun a b ha hb =>
    congrArg (fun z : A => (z : Q)) (hAcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hκle : κ ≤ 1 := by
    by_contra hκ2
    push Not at hκ2
    set n := 2 ^ l with hn
    have hgpowA : ∀ m : ℕ, g ^ m ∈ A → n ∣ m := by
      intro m hm
      obtain ⟨b0, hb0c⟩ := hc0
      have hcm : c0 ^ m = 1 := by
        rw [← hb0c]
        change rcomm (b0 : Q) g ^ m = 1
        rw [← rcomm_pow_right_central hcen, rcomm_eq_one_iff]
        exact hAab _ _ b0.2 hm
      rw [← hc0ord]
      exact orderOf_dvd_of_pow_eq_one hcm
    have hgA : g ^ n ∈ A := by
      rw [← hAcent, Subgroup.mem_centralizer_iff]
      intro a ha
      have h := hRgmem a ha
      rw [← rcomm_pow_right_central hcen, rcomm_eq_one_iff] at h
      exact h
    have hgZ : g ^ n ∈ Z := by
      rw [← hKgZ]
      refine (hmemK g _).mpr ⟨hgA, ?_⟩
      rw [rcomm_eq_one_iff]
      exact (Commute.pow_left (Commute.refl g) n).eq
    set N := n.choose 2 with hN
    let T : A →* Q :=
      { toFun := fun a => (a : Q) ^ n * rcomm (a : Q) g ^ N
        map_one' := by simp [rcomm_one_left]
        map_mul' := fun a b => by
          simp only [Subgroup.coe_mul]
          rw [rcomm_mul_left_central hcen, (Commute.mul_pow (hAab _ _ a.2 b.2) n)]
          have hc1 : Commute (rcomm (a : Q) g ^ N) ((b : Q) ^ n) := (hcen _ _ _).pow_left N
          have hc2 : Commute (rcomm (a : Q) g) (rcomm (b : Q) g) := hcen _ _ _
          rw [hc2.mul_pow]
          simp only [mul_assoc]
          rw [← mul_assoc (rcomm (a : Q) g ^ N), hc1.eq]
          simp only [mul_assoc] }
    have hTapply : ∀ a : A, T a = (a : Q) ^ n * rcomm (a : Q) g ^ N := fun a => rfl
    have hTZ : T.range ≤ Z := by
      rintro _ ⟨a, rfl⟩
      rw [hTapply]
      apply Z.mul_mem
      · rw [hZκ]
        refine ⟨A.pow_mem a.2 _, ?_⟩
        rw [← pow_mul, ← pow_add, show l + κ = e by omega]
        exact hAexp _
      · rw [Subgroup.mem_center_iff]
        intro q
        exact ((hcen _ _ q).pow_left N).symm.eq
    have hNval : N = 2 ^ (l - 1) * (2 ^ l - 1) := by
      rw [hN, Nat.choose_two_right, hn]
      have h2 : 2 ^ l = 2 * 2 ^ (l - 1) := by
        rw [← pow_succ']; congr 1; omega
      rw [h2, mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]
    let P : A →* Q :=
      { toFun := fun b => (b : Q) ^ (2 ^ (κ - 1))
        map_one' := by simp
        map_mul' := fun a b => by
          simp only [Subgroup.coe_mul]
          exact Commute.mul_pow (hAab _ _ a.2 b.2) _ }
    have hPrange : P.range = omegaSub A hAcomm (l + 1) := by
      have hle1 : P.range ≤ omegaSub A hAcomm (l + 1) := by
        rintro _ ⟨b, rfl⟩
        refine ⟨A.pow_mem b.2 _, ?_⟩
        change ((b : Q) ^ 2 ^ (κ - 1)) ^ 2 ^ (l + 1) = 1
        rw [← pow_mul, ← pow_add, show κ - 1 + (l + 1) = e by omega]
        exact hAexp _
      apply Subgroup.eq_of_le_of_card_ge hle1
      have hker : Nat.card P.ker = 4 ^ (κ - 1) := by
        have hmap : P.ker.map A.subtype = omegaSub A hAcomm (κ - 1) := by
          ext a
          constructor
          · rintro ⟨b, hb, rfl⟩
            exact ⟨b.2, hb⟩
          · rintro ⟨ha, h⟩
            exact ⟨⟨a, ha⟩, h, rfl⟩
        rw [← card_omegaSub hQ hrank α hα hfpf A hAcomm hAinv hxA he (k := κ - 1) (by omega),
          ← hmap]
        exact Nat.card_congr (Subgroup.equivMapOfInjective _ _ A.subtype_injective).toEquiv
      have htot := Subgroup.card_ker_mul_card_range P
      rw [hker, hcardA] at htot
      rw [card_omegaSub hQ hrank α hα hfpf A hAcomm hAinv hxA he (k := l + 1) (by omega)]
      have h4 : (4 : ℕ) ^ e = 4 ^ (κ - 1) * 4 ^ (l + 1) := by
        rw [← pow_add]; congr 1; omega
      rw [h4] at htot
      exact (Nat.eq_of_mul_eq_mul_left (by positivity) htot).ge
    have hTker : ∀ a : A, T a = 1 → (a : Q) ^ n = 1 := by
      intro a haT
      rw [hTapply] at haT
      have han : (a : Q) ^ n = (rcomm (a : Q) g ^ N)⁻¹ := eq_inv_of_mul_eq_one_left haT
      have hsq : ((a : Q) ^ n) ^ 2 = 1 := by
        rw [han, inv_pow, ← pow_mul, hNval]
        have : 2 ^ (l - 1) * (2 ^ l - 1) * 2 = 2 ^ l * (2 ^ l - 1) := by
          rw [mul_comm _ 2, ← mul_assoc, ← pow_succ']; congr 2; omega
        rw [this, pow_mul, hRgmem _ a.2, one_pow, inv_one]
      have hmem : (a : Q) ∈ omegaSub A hAcomm (l + 1) := by
        refine ⟨a.2, ?_⟩
        rw [pow_succ, pow_mul]; exact hsq
      rw [← hPrange] at hmem
      obtain ⟨b, hb⟩ := hmem
      have hab : (a : Q) = (b : Q) ^ (2 ^ (κ - 1)) := hb.symm
      have hcN : rcomm (a : Q) g ^ N = 1 := by
        rw [hab, rcomm_pow_left_central hcen, ← pow_mul, hNval]
        have : 2 ^ (κ - 1) * (2 ^ (l - 1) * (2 ^ l - 1)) = 2 ^ l * (2 ^ (κ - 2) * (2 ^ l - 1)) := by
          rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
        rw [this, pow_mul, hRgmem _ b.2, one_pow]
      rw [han, hcN, inv_one]
    have hTrange : T.range = Z := by
      apply Subgroup.eq_of_le_of_card_ge hTZ
      have htot := Subgroup.card_ker_mul_card_range T
      rw [hcardA] at htot
      have hkerle : Nat.card T.ker ≤ 4 ^ l := by
        have hle2 : T.ker.map A.subtype ≤ omegaSub A hAcomm l := by
          rintro _ ⟨a, ha, rfl⟩
          exact ⟨a.2, hTker a ha⟩
        have h1 := Subgroup.card_le_of_le hle2
        rw [card_omegaSub hQ hrank α hα hfpf A hAcomm hAinv hxA he (k := l) (by omega)] at h1
        calc Nat.card T.ker = Nat.card (T.ker.map A.subtype) :=
              Nat.card_congr (Subgroup.equivMapOfInjective _ _ A.subtype_injective).toEquiv
          _ ≤ 4 ^ l := h1
      rw [hZcard]
      have h4 : (4 : ℕ) ^ e = 4 ^ l * 4 ^ κ := by rw [← pow_add]; congr 1; omega
      rw [h4] at htot
      by_contra hlt
      push Not at hlt
      have : Nat.card T.ker * Nat.card T.range < 4 ^ l * 4 ^ κ :=
        Nat.mul_lt_mul_of_le_of_lt hkerle hlt (by positivity)
      omega
    obtain ⟨a, ha⟩ : (g ^ n)⁻¹ ∈ T.range := hTrange ▸ Z.inv_mem hgZ
    have hgan : (g * (a : Q)) ^ n = 1 := by
      rw [mul_pow_central hcen, mul_assoc, ← hTapply, ha, mul_inv_cancel]
    set w := (g * (a : Q)) ^ (2 ^ (l - 1)) with hw
    have hw2 : w ^ 2 = 1 := by
      rw [hw, ← pow_mul, ← pow_succ, show l - 1 + 1 = l by omega]; exact hgan
    have hwA : w ∈ A := hVZ.trans hZA (hinvol w hw2)
    have hgmA : g ^ (2 ^ (l - 1)) ∈ A := by
      rw [hw, mul_pow_central hcen] at hwA
      have h1 : (a : Q) ^ (2 ^ (l - 1)) * rcomm (a : Q) g ^ ((2 ^ (l - 1)).choose 2) ∈ A :=
        A.mul_mem (A.pow_mem a.2 _) (A.pow_mem (hZA (hRZ g ⟨a, rfl⟩)) _)
      have h2 := A.mul_mem hwA (A.inv_mem h1)
      simpa [mul_assoc] using h2
    have hdvd := hgpowA _ hgmA
    have := Nat.le_of_dvd (by positivity) hdvd
    rw [hn] at this
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    omega
  have hκ : κ = 1 := le_antisymm hκle hκ1
  have he2 : e = 2 := by
    have hle2 : e ≤ 2 := by omega
    by_contra hne
    have he' : e = 1 := by omega
    apply hnotab
    intro a b
    have ha : a ∈ Z := hVZ (hinvol a (by have := hAexp a; rwa [he', pow_one] at this))
    exact (Subgroup.mem_center_iff.mp ha b).symm
  subst hκ
  subst he2
  have hZV : Z = V := hZκ
  have h4 : ∀ q : Q, q ^ 4 = 1 := hAexp
  let φ : Q →* Q :=
    { toFun := fun s => rcomm x s
      map_one' := rcomm_one_right x
      map_mul' := fun s t => rcomm_mul_right_central hcen x s t }
  have hφ : ∀ s, φ s = rcomm x s := fun s => rfl
  have hyφ : ∀ s, rcomm y s = α (α (φ s)) := fun s => by rw [hy, hαleft]; rfl
  have hφker : φ.ker = A := by
    ext s
    rw [MonoidHom.mem_ker, hφ]
    constructor
    · intro h1
      have h2 : rcomm y s = 1 := by rw [hyφ, hφ, h1, map_one, map_one]
      rw [← hAcent, Subgroup.mem_centralizer_iff]
      have hle : A ≤ Subgroup.centralizer ({s} : Set Q) := by
        rw [hA, Subgroup.closure_le]
        intro a ha
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        rcases ha with rfl | rfl
        · exact (rcomm_eq_one_iff a s).mp h1
        · exact (rcomm_eq_one_iff _ s).mp h2
      intro a ha
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle ha))
    · intro hs
      rw [rcomm_eq_one_iff]
      exact hAab _ _ hxA hs
  have hφZ : φ.range ≤ Z := by
    rintro _ ⟨s, rfl⟩
    rw [hφ, Subgroup.mem_center_iff]
    intro q
    exact (hcen x s q).symm.eq
  have hφinv : ∀ c ∈ φ.range, α c ∈ φ.range := by
    rintro _ ⟨s, rfl⟩
    refine ⟨α (α s), ?_⟩
    rw [hφ, hφ, hbal]
    simp [rcomm]
  obtain ⟨k, hk, hkcard, -⟩ := invariant_eq_omegaSub hQ hrank α hα hfpf A hAcomm φ.range
    (hφZ.trans hZA) hφinv
  have hφne : φ.range ≠ ⊥ := by
    intro hbot
    apply hnotab
    have htop : A = ⊤ := by
      rw [← hφker, eq_top_iff]
      intro s _
      rw [MonoidHom.mem_ker]
      have : φ s ∈ φ.range := ⟨s, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    intro a b
    exact hAab a b (htop ▸ Subgroup.mem_top a) (htop ▸ Subgroup.mem_top b)
  have hk1 : k = 1 := by
    have hle : Nat.card φ.range ≤ 4 := by
      have := Subgroup.card_le_of_le hφZ
      rwa [hZcard] at this
    rw [hkcard] at hle
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hφne
      rw [← Subgroup.card_eq_one, hkcard, pow_zero]
    have : k ≤ 1 := by
      by_contra h
      push Not at h
      have : 4 ^ 2 ≤ 4 ^ k := Nat.pow_le_pow_right (by norm_num) h
      omega
    omega
  have hφV : φ.range = V := by rw [hk, hk1]
  have hcardQ : Nat.card Q = 64 := by
    have htot := Subgroup.card_ker_mul_card_range φ
    rw [hφker, hcardA, hφV, hVcard] at htot
    omega
  have hxy : Commute x y := hAab x y hxA hyA
  have hx4 : x ^ 4 = 1 := h4 x
  have hy4 : y ^ 4 = 1 := h4 y
  have hsq22 : (x ^ 2 * y ^ 2) * (x ^ 2 * y ^ 2) = 1 := by
    rw [← sq, (hxy.pow_pow 2 2).mul_pow, ← pow_mul, ← pow_mul]
    simp [hx4, hy4]
  have hinv22 : (x ^ 2 * y ^ 2)⁻¹ = x ^ 2 * y ^ 2 := (eq_inv_of_mul_eq_one_left hsq22).symm
  have hαy : α y = (x * y)⁻¹ := by
    have h := hnorm x
    rw [← hy] at h
    exact eq_inv_of_mul_eq_one_right h
  have hαy2 : (α y) ^ 2 = x ^ 2 * y ^ 2 := by
    rw [hαy, inv_pow, hxy.mul_pow, hinv22]
  have hx2V : x ^ 2 ∈ V := ⟨A.pow_mem hxA 2, by rw [← pow_mul]; exact hx4⟩
  have hy2V : y ^ 2 ∈ V := ⟨A.pow_mem hyA 2, by rw [← pow_mul]; exact hy4⟩
  have hx2ne : x ^ 2 ≠ 1 := by
    intro h
    have := orderOf_dvd_of_pow_eq_one h
    rw [he] at this
    norm_num at this
  have hy2ne : y ^ 2 ≠ 1 := by
    intro h
    apply hx2ne
    have : α (x ^ 2) = α 1 := by rw [map_pow, ← hy, h, map_one]
    exact α.injective (by rw [this])
  have hx2y2 : x ^ 2 ≠ y ^ 2 := by
    intro h
    apply hx2ne
    apply hfpf
    rw [map_pow, ← hy, ← h]
  have h1xy : (1 : Q) ≠ x ^ 2 * y ^ 2 := by
    intro h
    apply hx2y2
    have : x ^ 2 = (y ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left h.symm
    rw [this]
    exact (eq_inv_of_mul_eq_one_left (by rw [← sq, ← pow_mul]; exact hy4)).symm
  have hxxy : x ^ 2 ≠ x ^ 2 * y ^ 2 := by
    intro h
    exact hy2ne (mul_left_cancel (h.symm.trans (mul_one _).symm))
  have hyxy : y ^ 2 ≠ x ^ 2 * y ^ 2 := by
    intro h
    exact hx2ne (mul_right_cancel (h.symm.trans (one_mul _).symm))
  have hVmem : ∀ v ∈ V, v = 1 ∨ v = x ^ 2 ∨ v = y ^ 2 ∨ v = x ^ 2 * y ^ 2 := fun v hv =>
    mem_of_card_eq_four hVcard V.one_mem hx2V hy2V (V.mul_mem hx2V hy2V) hx2ne.symm
      hy2ne.symm h1xy hx2y2 hxxy hyxy hv
  obtain ⟨g0, hg0⟩ : x ^ 2 ∈ φ.range := hφV ▸ hx2V
  rw [hφ] at hg0
  have hg0y : rcomm y g0 = x ^ 2 * y ^ 2 := by
    rw [hyφ, hφ, hg0, map_pow, map_pow, ← hy, hαy2]
  have hg0A : g0 ∉ A := by
    intro h
    rw [← hφker, MonoidHom.mem_ker, hφ, hg0] at h
    exact hx2ne h
  have hsq : ∀ s a : Q, (s * a) ^ 2 = s ^ 2 * a ^ 2 * rcomm a s := by
    intro s a
    rw [mul_pow_central hcen]
    simp
  have hg0sq : g0 ^ 2 ∈ V := hinvol _ (by rw [← pow_mul]; exact h4 g0)
  obtain ⟨g, hg2, hgx, hgy⟩ : ∃ g : Q, g ^ 2 = y ^ 2 ∧ rcomm x g = x ^ 2 ∧
      rcomm y g = x ^ 2 * y ^ 2 := by
    rcases hVmem _ hg0sq with h | h | h | h
    · exfalso
      exact hg0A (hVZ.trans hZA (hinvol g0 h))
    · exfalso
      have h' : (g0 * y) ^ 2 = 1 := by
        rw [hsq, h, hg0y]
        simpa [mul_assoc] using hsq22
      have hA' := hVZ.trans hZA (hinvol _ h')
      exact hg0A (by simpa using A.mul_mem hA' (A.inv_mem hyA))
    · exact ⟨g0, h, hg0, hg0y⟩
    · refine ⟨g0 * y, ?_, ?_, ?_⟩
      · rw [hsq, h, hg0y]
        have huv : Commute (x ^ 2 * y ^ 2) (y ^ 2) :=
          (hxy.pow_pow 2 2).mul_left (Commute.refl (y ^ 2))
        rw [mul_assoc (x ^ 2 * y ^ 2) (y ^ 2), ← huv.eq, ← mul_assoc, hsq22, one_mul]
      · rw [rcomm_mul_right_central hcen, hg0, (rcomm_eq_one_iff x y).mpr hxy, mul_one]
      · rw [rcomm_mul_right_central hcen, hg0y, (rcomm_eq_one_iff y y).mpr rfl, mul_one]
  set h := α g with hh
  have hh2 : h ^ 2 = x ^ 2 * y ^ 2 := by rw [hh, ← map_pow, hg2, map_pow, hαy2]
  have hgh : rcomm g h = 1 := hcommα g
  have hxh : rcomm x h = x ^ 2 * y ^ 2 := by rw [hh, hbal, ← hy, hgy]
  have hyh : rcomm y h = y ^ 2 := by
    rw [hh, hbal, hαy, rcomm_inv_left_central hcen, rcomm_mul_left_central hcen, hgx, hgy]
    have : x ^ 2 * (x ^ 2 * y ^ 2) = y ^ 2 := by
      rw [← mul_assoc, ← pow_add, show 2 + 2 = 4 by norm_num, hx4, one_mul]
    rw [this]
    exact (eq_inv_of_mul_eq_one_left (by rw [← sq, ← pow_mul]; exact hy4)).symm
  have hxyc : rcomm x y = 1 := (rcomm_eq_one_iff x y).mpr hxy
  have hgen : Subgroup.closure ({x, y, g, h} : Set Q) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    set C := Subgroup.closure ({x, y, g, h} : Set Q)
    have hxC : x ∈ C := Subgroup.subset_closure (by simp)
    have hyC : y ∈ C := Subgroup.subset_closure (by simp)
    have hgC : g ∈ C := Subgroup.subset_closure (by simp)
    have hhC : h ∈ C := Subgroup.subset_closure (by simp)
    have hAC : A ≤ C := by
      rw [hA, Subgroup.closure_le]
      intro a ha
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hxC
      · exact hyC
    have hred : ∀ w ∈ C, φ q = φ w → q ∈ C := by
      intro w hw hqw
      have hker : q * w⁻¹ ∈ A := by
        rw [← hφker, MonoidHom.mem_ker, map_mul, map_inv, hqw, mul_inv_cancel]
      have := C.mul_mem (hAC hker) hw
      simpa using this
    have hφq : φ q ∈ V := hφV ▸ ⟨q, rfl⟩
    rcases hVmem _ hφq with hq | hq | hq | hq
    · exact hred 1 C.one_mem (by rw [hq, map_one])
    · exact hred g hgC (by rw [hq, hφ, hgx])
    · refine hred (g * h) (C.mul_mem hgC hhC) ?_
      rw [hq, map_mul, hφ, hφ, hgx, hxh, ← mul_assoc, ← pow_add,
        show 2 + 2 = 4 by norm_num, hx4, one_mul]
    · exact hred h hhC (by rw [hq, hφ, hxh])
  have hZmem : ∀ z : Q, z ∈ Z ↔ z ^ 2 = 1 := by
    intro z
    constructor
    · intro hz
      rw [hZV] at hz
      simpa using hz.2
    · intro hz
      exact hVZ (hinvol z hz)
  have hcomm_mem : ∀ a b : Q, rcomm a b ∈ ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
    intro a b
    have : rcomm a b = ⁅a⁻¹, b⁻¹⁆ := by simp [rcomm, commutatorElement_def]
    rw [this]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (a⁻¹ : Q))
      (Subgroup.mem_top (b⁻¹ : Q))
  have hderived : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = Z := by
    apply le_antisymm hcz
    intro z hz
    rw [hZV] at hz
    rcases hVmem z hz with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · rw [← hgx]; exact hcomm_mem x g
    · rw [← hyh]; exact hcomm_mem y h
    · rw [← hxh]; exact hcomm_mem x h
  refine ⟨hcardQ, h4, by rw [hZcard, pow_one], hZmem, hderived, x, y, g, h, hy, hh, hx4, hy4,
    hxyc, hgh, hg2, hh2, hgx, hgy, hxh, hyh, hgen⟩

end CFSG.RankTwoShapes
