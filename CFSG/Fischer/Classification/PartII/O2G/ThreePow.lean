module

public import CFSG.Fischer.Classification.PartII.O2G.Three

public section

namespace CFSG.Fischer.Classification

open CFSG.Blueprint.Fischer CFSG.Fischer LocalU O2Twin

namespace O2G

variable {G : Type} [Group G] {D : Set G}

theorem exists_ncard_twinClass_eq_two_pow (hP : Pair G D) (hZ : Subgroup.center G = ⊥)
    (hS : IsSimpleGroup (commutator G)) {d a a' f : G} (hd : d ∈ D)
    (h : IsTwin (LocalClass D d) a a') (hf : f ∈ LocalClass D d) :
    ∃ n : ℕ, (twinClass (LocalClass D d) f).ncard = 2 ^ n := by
  have := Pair.finite hP
  have ha := h.1
  obtain ⟨b, hb, hba⟩ := Pair.exists_not_commute_of_mem_localClass hP hZ hS hd ha
  have hab : a * b ≠ b * a := fun e => hba e.symm
  rw [ncard_twinClass_eq hP hZ hS hd hf hb]
  set S : Set G := {u | ∃ t ∈ twinClass (LocalClass D d) a, u = a * t} with hSdef
  have hScomm : S.Pairwise Commute := by
    rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ -
    have htt' : t * t' = t' * t := (isTwin_of_mem ht ht').2.2.1
    have hat : a * t = t * a := ht.2.2.1
    have hat' : a * t' = t' * a := ht'.2.2.1
    show a * t * (a * t') = a * t' * (a * t)
    calc a * t * (a * t') = a * a * (t * t') := by rw [mul_assoc a t, ← mul_assoc t a, ← hat]; group
      _ = a * a * (t' * t) := by rw [htt']
      _ = a * t' * (a * t) := by rw [mul_assoc a t', ← mul_assoc t' a, ← hat']; group
  have hSsq : ∀ u ∈ S, u * u = 1 := by
    rintro _ ⟨t, ht, rfl⟩
    exact mul_mul_mul_self hP ha.1 ht.2.1.1 ht.2.2.1
  set Q := Subgroup.closure S with hQ
  have hQc := Subgroup.isMulCommutative_closure hScomm
  have hQsq : ∀ g ∈ Q, g * g = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu => exact hSsq u hu
    | one => exact mul_one 1
    | mul x y hx hy ihx ihy =>
      have hxy : x * y = y * x := by
        have := congrArg Subtype.val (hQc.is_comm.comm (⟨x, hx⟩ : Q) ⟨y, hy⟩)
        simpa using this
      calc x * y * (x * y) = x * x * (y * y) := by rw [mul_assoc x y, ← mul_assoc y x, ← hxy]; group
        _ = 1 := by rw [ihx, ihy, one_mul]
    | inv x hx ihx => rw [← mul_inv_rev, ihx, inv_one]
  have hQp : IsPGroup 2 Q := fun g => ⟨1, by
    rw [pow_one, sq]
    exact Subtype.ext (hQsq g g.2)⟩
  have hpres : ∀ g ∈ Q, ∀ y ∈ twinClass (LocalClass D d) b,
      g * y * g⁻¹ ∈ twinClass (LocalClass D d) b := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem u hu =>
      intro y hy
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hSsq u hu)
      obtain ⟨t, ht, rfl⟩ := hu
      have hay : a * y ≠ y * a := fun e => hab ((hy.2.2.2 a ha).2 e)
      have h1 := isTwin_conj_mul hP (isTwin_of_mem (self_mem_twinClass ha) ht) hy.2.1 hay
      rw [hui]
      exact isTwin_trans hy h1
    | one => intro y hy; simpa using hy
    | mul x z hx hz ihx ihz =>
      intro y hy
      rw [show x * z * y * (x * z)⁻¹ = x * (z * y * z⁻¹) * x⁻¹ by group]
      exact ihx _ (ihz y hy)
    | inv x hx ihx =>
      intro y hy
      have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hQsq x hx)
      rw [hxi]
      exact ihx y hy
  let Q' : Subgroup (ConjAct G) := Q.map (ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom
  have hQ'p : IsPGroup 2 Q' :=
    hQp.of_equiv (Q.equivMapOfInjective _ (ConjAct.toConjAct : G ≃* ConjAct G).injective)
  have horb : MulAction.orbit Q' b = twinClass (LocalClass D d) b := by
    ext y
    constructor
    · rintro ⟨⟨_, g, hg, rfl⟩, rfl⟩
      show ConjAct.toConjAct g • b ∈ _
      rw [ConjAct.toConjAct_smul]
      exact hpres g hg b (self_mem_twinClass hb)
    · intro hy
      have hmaps : Set.MapsTo (fun t => a * t * b * (a * t)) (twinClass (LocalClass D d) a)
          (twinClass (LocalClass D d) b) := fun t ht => by
        have h1 := isTwin_conj_mul hP (isTwin_of_mem (self_mem_twinClass ha) ht) hb hab
        exact h1
      have hinj : Set.InjOn (fun t => a * t * b * (a * t)) (twinClass (LocalClass D d) a) := by
        intro t ht t' ht' heq
        simp only at heq
        rw [mul_mul_mul_mul_eq ht.2.2.1, mul_mul_mul_mul_eq ht'.2.2.1] at heq
        have h12 : t * b * t = t' * b * t' := by
          rw [← Pair.mul_mul_mul_mul hP ha.1 (t * b * t), heq, Pair.mul_mul_mul_mul hP ha.1]
        have htb' : t * b ≠ b * t := fun e => hab ((ht.2.2.2 b hb).2 e.symm).symm
        have ht'b : t' * b ≠ b * t' := fun e => hab ((ht'.2.2.2 b hb).2 e.symm).symm
        have h2 : b * t * b = b * t' * b := by
          rw [← Pair.mul_mul_eq hP ht.2.1.1 hb.1 htb', h12,
            Pair.mul_mul_eq hP ht'.2.1.1 hb.1 ht'b]
        exact mul_left_cancel (mul_right_cancel h2)
      have himg : (fun t => a * t * b * (a * t)) '' twinClass (LocalClass D d) a =
          twinClass (LocalClass D d) b := by
        refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps) ?_ (Set.toFinite _)
        rw [hinj.ncard_image, ncard_twinClass_eq hP hZ hS hd hb ha]
      rw [← himg] at hy
      obtain ⟨t, ht, rfl⟩ := hy
      have hu : a * t ∈ Q := Subgroup.subset_closure ⟨t, ht, rfl⟩
      refine ⟨⟨ConjAct.toConjAct (a * t), ⟨a * t, hu, rfl⟩⟩, ?_⟩
      show ConjAct.toConjAct (a * t) • b = _
      rw [ConjAct.toConjAct_smul, inv_eq_of_mul_eq_one_right (hQsq _ hu)]
  have : Finite (MulAction.orbit Q' b) := by rw [horb]; exact Set.toFinite _
  obtain ⟨n, hn⟩ := hQ'p.card_orbit b
  refine ⟨n, ?_⟩
  rw [← hn, horb, Nat.card_coe_set_eq]

end O2G

open O2G

theorem o2_four_or_sixteen_le {G : Type} [Group G] {D : Set G} (hH : Hyp G D)
    (hna : NonabelianCommutator G) (hs : ¬ IsSymplecticType D) {d : G} (hd : d ∈ D)
    (h2 : HasNormalPSubgroup 2 (LocalQuotient D d)) {a : G} (ha : a ∈ LocalClass D d) :
    {b | LocalU.IsTwin (LocalClass D d) a b}.ncard = 4 ∨
      16 ≤ {b | LocalU.IsTwin (LocalClass D d) a b}.ncard := by
  obtain ⟨x, y, hxy, hne⟩ := exists_isTwin_ne hH.pair hH.center hH.simple hna hd h2
  obtain ⟨n, hn⟩ := exists_ncard_twinClass_eq_two_pow hH.pair hH.center hH.simple hd hxy ha
  have h3 := o2_four_or_three_dvd hH hna hs hd h2 ha
  have hne2 := o2_r_ne_two hH hna hs hd h2 ha
  have hev := even_ncard_twinClass hH.pair hH.center hH.simple hd hxy hne ha
  change (twinClass (LocalClass D d) a).ncard = 4 ∨
    16 ≤ (twinClass (LocalClass D d) a).ncard
  change (twinClass (LocalClass D d) a).ncard = 4 ∨
    3 ∣ (twinClass (LocalClass D d) a).ncard - 1 at h3
  change (twinClass (LocalClass D d) a).ncard ≠ 2 at hne2
  rw [hn] at h3 hne2 hev ⊢
  rcases h3 with h | h
  · exact Or.inl h
  ·
    rcases Nat.lt_or_ge n 4 with hlt | hge
    · interval_cases n <;> simp_all
    · right
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hge

end CFSG.Fischer.Classification
