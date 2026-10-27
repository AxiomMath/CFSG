module

public import CFSG.Fischer.Classification.Basic.RankReduced
public import CFSG.Fischer.Classification.Basic.Local
public import CFSG.Fischer.Classification.Skeleton
public import CFSG.GroupTheory.LocalCores.MinimalNormal
public import CFSG.CharacterTheory.Burnside

public section

open CFSG.Blueprint.Fischer CFSG.Fischer
open scoped commutatorElement

namespace CFSG.Fischer.Classification

variable {X : Type} [Group X] {E : Set X}

theorem isSolvable_of_forall_orderOf_le_three {G : Type} [Group G] [Finite G]
    (h : ∀ g : G, orderOf g ≤ 3) : Group.IsSolvable G := by
  classical
  let := Fintype.ofFinite G
  have hsupp : (Nat.card G).factorization.support ⊆ {2, 3} := by
    intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have := Fact.mk hpp
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have h1 := h g
    rw [hg] at h1
    have := hpp.two_le
    interval_cases p <;> simp_all
  have hcard :
      Nat.card G = 2 ^ (Nat.card G).factorization 2 * 3 ^ (Nat.card G).factorization 3 := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self Nat.card_pos.ne']
    rw [Finsupp.prod_of_support_subset _ hsupp _ fun _ _ => pow_zero _]
    simp
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hcard)

theorem Pair.not_isSolvable_of_minimal (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) {N : Subgroup X} (hN : N.Normal)
    (hNbot : N ≠ ⊥) (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K ≠ ⊥ → K = N) :
    ¬ Group.IsSolvable N := by
  intro hsol
  have := Pair.finite hP
  have : N.Normal := hN
  have : CFSG.IsMinimalNormal N := ⟨fun K _ hKle => by
    by_cases hK : K = ⊥
    · exact Or.inl hK
    · exact Or.inr (hmin K inferInstance hKle hK)⟩
  obtain ⟨p, hp, hpN⟩ := CFSG.minimalNormal_solvable_exists_isElementaryAbelian N
  have hNp := CFSG.IsElementaryAbelian.isPGroup p N
  have hp4 : p ≠ 4 := by
    rintro rfl
    norm_num at hp
  have := hp.two_le
  rcases (show p = 2 ∨ p = 3 ∨ 5 ≤ p by omega) with rfl | rfl | hp5
  · exact hNbot (h2 N hN hNp)
  · exact hNbot (h3 N hN hNp)
  · exact hNbot (Pair.eq_bot_of_isPGroup hP hZ hp hp5 hN hNp)

theorem Pair.isSimpleGroup_of_minimal (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥) {N : Subgroup X} (hN : N.Normal)
    (hNbot : N ≠ ⊥) (hmin : ∀ K : Subgroup X, K.Normal → K ≤ N → K ≠ ⊥ → K = N) :
    IsSimpleGroup N := by
  have := Pair.finite hP
  have hNsol := Pair.not_isSolvable_of_minimal hP hZ h2 h3 hN hNbot hmin
  obtain ⟨r, S, hr, hSN, hSsimple, hSconj, hSnormal, e, -⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hN hNbot fun M hM hle =>
      (em (M = ⊥)).imp id fun h => hmin M hM hle h
  set i₀ : Fin r := ⟨0, hr⟩
  have hS := hSsimple i₀
  have := hS
  have hSna : ¬ ∀ a b : S i₀, a * b = b * a := by
    intro hcomm
    apply hNsol
    have hSj : ∀ j, ∀ a b : S j, a * b = b * a := by
      intro j a b
      obtain ⟨g, hg⟩ := hSconj i₀ j
      have ha : (a : X) ∈ CFSG.conjugate (S i₀) g := by rw [← hg]; exact a.2
      have hb : (b : X) ∈ CFSG.conjugate (S i₀) g := by rw [← hg]; exact b.2
      rw [CFSG.conjugate, Subgroup.mem_map] at ha hb
      obtain ⟨a', ha', haa⟩ := ha
      obtain ⟨b', hb', hbb⟩ := hb
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← haa, ← hbb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hcomm ⟨a', ha'⟩ ⟨b', hb'⟩)
    have hcommN : ∀ a b : N, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := e.surjective a
      obtain ⟨y, rfl⟩ := e.surjective b
      rw [← map_mul, ← map_mul]
      congr 1
      funext j
      exact hSj j (x j) (y j)
    exact Group.isSolvable_of_comm hcommN
  have hSn : ∀ n ∈ N, ∀ s ∈ S i₀, n * s * n⁻¹ ∈ S i₀ := by
    intro n hn s hs
    have := (hSnormal i₀).conj_mem ⟨s, hSN i₀ hs⟩ (Subgroup.mem_subgroupOf.2 hs) ⟨n, hn⟩
    rwa [Subgroup.mem_subgroupOf] at this
  have hnorm : ∀ f ∈ E, ∀ s ∈ S i₀, f * s * f⁻¹ ∈ S i₀ := by
    intro f hf
    by_contra! hmove
    obtain ⟨s₀, hs₀, hs₀'⟩ := hmove
    set T : Subgroup X := (S i₀).map (MulAut.conj f).toMonoidHom with hTdef
    have hmemT : ∀ s ∈ S i₀, f * s * f⁻¹ ∈ T := fun s hs => ⟨s, hs, rfl⟩
    have hTN : ∀ t ∈ T, t ∈ N := by
      rintro _ ⟨s, hs, rfl⟩
      exact hN.conj_mem s (hSN i₀ hs) f
    have hTn : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T := by
      rintro n hn _ ⟨s, hs, rfl⟩
      have hn' : f⁻¹ * n * f ∈ N := by
        simpa using hN.conj_mem n hn f⁻¹
      have := hmemT _ (hSn _ hn' s hs)
      simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
      convert this using 1
      group
    have hcardT : Nat.card T = Nat.card (S i₀) :=
      Subgroup.card_map_of_injective (MulAut.conj f).injective
    have hinf : ∀ x ∈ S i₀, x ∈ T → x = 1 := by
      have hIn : (((S i₀) ⊓ T).subgroupOf (S i₀)).Normal := ⟨fun n hn s => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact ⟨hSn _ (hSN i₀ s.2) _ hn.1, hTn _ (hSN i₀ s.2) _ hn.2⟩⟩
      have := hIn
      rcases hS.eq_bot_or_eq_top_of_normal (((S i₀) ⊓ T).subgroupOf (S i₀)) with hbot | htop
      · intro x hx hxT
        have : (⟨x, hx⟩ : S i₀) ∈ ((S i₀) ⊓ T).subgroupOf (S i₀) :=
          Subgroup.mem_subgroupOf.2 ⟨hx, hxT⟩
        rw [hbot, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      · exfalso
        have hle : S i₀ ≤ T := fun x hx => by
          have : (⟨x, hx⟩ : S i₀) ∈ ((S i₀) ⊓ T).subgroupOf (S i₀) := htop ▸ Subgroup.mem_top _
          exact (Subgroup.mem_subgroupOf.1 this).2
        have heq := Subgroup.eq_of_le_of_card_ge hle hcardT.le
        apply hs₀'
        rw [heq]
        exact hmemT s₀ hs₀
    have hST : ∀ x ∈ S i₀, ∀ t ∈ T, x * t = t * x := by
      intro x hx t ht
      have h1 : x * t * x⁻¹ * t⁻¹ ∈ S i₀ := by
        have h := mul_mem hx (hSn t (hTN t ht) x⁻¹ (inv_mem hx))
        simpa [mul_assoc] using h
      have h2 : x * t * x⁻¹ * t⁻¹ ∈ T := mul_mem (hTn x (hSN i₀ hx) t ht) (inv_mem ht)
      have h3 := hinf _ h1 h2
      calc x * t = x * t * x⁻¹ * t⁻¹ * (t * x) := by group
        _ = t * x := by rw [h3, one_mul]
    have hord : ∀ x : S i₀, orderOf x ≤ 3 := by
      intro x
      rw [← Subgroup.orderOf_coe]
      have hx := x.2
      have hmul : f * ((x : X) * f * (x : X)⁻¹) = f * x * f⁻¹ * (x : X)⁻¹ := by
        rw [Pair.inv_eq hP hf]
        group
      have hmem := Pair.orderOf_mul_mem hP hf (Pair.conj_mem hP hf x)
      have hO : orderOf (f * (x : X) * f⁻¹ * (x : X)⁻¹) = orderOf (x : X) := by
        rw [orderOf_eq_orderOf_iff]
        intro n
        have hc : Commute (f * (x : X) * f⁻¹) (x : X)⁻¹ :=
          (hST _ (inv_mem hx) _ (hmemT _ hx)).symm
        rw [hc.mul_pow, conj_pow, inv_pow]
        constructor
        · intro h
          have h' : f * (x : X) ^ n * f⁻¹ = (x : X) ^ n := mul_inv_eq_one.1 h
          have hxS : (x : X) ^ n ∈ S i₀ := pow_mem hx n
          have hxT : (x : X) ^ n ∈ T := h' ▸ hmemT _ hxS
          exact hinf _ hxS hxT
        · intro h
          rw [h]
          group
      rw [← hO, ← hmul]
      rcases hmem with h | h | h <;> rw [h] <;> norm_num
    exact hSna (IsSimpleGroup.comm_iff_isSolvable.2 (isSolvable_of_forall_orderOf_le_three hord))
  have hSnX : (S i₀).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← Pair.closure_eq hP, Subgroup.closure_le]
    intro f hf
    rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨hnorm f hf s, fun h => ?_⟩
    have := hnorm f hf _ h
    rwa [Pair.inv_eq hP hf, Pair.mul_mul_mul_mul hP hf] at this
  have hSbot : S i₀ ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hSeq : S i₀ = N := hmin _ hSnX (hSN i₀) hSbot
  rw [← hSeq]
  exact hS

theorem Pair.normal_le_center_of_commute (hP : Pair X E) {N : Subgroup X} (hN : N.Normal)
    (hNs : IsSimpleGroup N) {a b : X} (ha : a ∈ E) (hb : b ∈ E) (hab : a * b = b * a)
    (hcomm : ∀ n ∈ N, a * (n * b * n⁻¹) = n * b * n⁻¹ * a) : N ≤ Subgroup.center X := by
  set K : Subgroup X := Subgroup.closure {x | ∃ n ∈ N, b * n * b⁻¹ * n⁻¹ = x} with hKdef
  have hKN : K ≤ N := by
    rw [Subgroup.closure_le]
    rintro _ ⟨n, hn, rfl⟩
    exact mul_mem (hN.conj_mem n hn b) (inv_mem hn)
  have haK : ∀ k ∈ K, a * k = k * a := by
    intro k hk
    induction hk using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨n, hn, rfl⟩ := hx
      have hc : Commute a (b * (n * b * n⁻¹)⁻¹) := Commute.mul_right (hab : Commute a b)
        (Commute.inv_right (hcomm n hn : Commute a (n * b * n⁻¹)))
      have : b * n * b⁻¹ * n⁻¹ = b * (n * b * n⁻¹)⁻¹ := by group
      rw [this]
      exact hc.eq
    | one => rw [mul_one, one_mul]
    | mul x y _ _ hx hy => rw [← mul_assoc, hx, mul_assoc, hy, mul_assoc]
    | inv x _ hx => exact (Commute.inv_right (hx : Commute a x)).eq
  have hKn : (K.subgroupOf N).Normal := by
    refine ⟨fun k hk m => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have key : ∀ x ∈ K, ∀ m ∈ N, m * x * m⁻¹ ∈ K := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨n, hn, rfl⟩ := hx
        intro m hm
        have h1 : b * m * b⁻¹ * m⁻¹ ∈ K := Subgroup.subset_closure ⟨m, hm, rfl⟩
        have h2 : b * (m * n) * b⁻¹ * (m * n)⁻¹ ∈ K :=
          Subgroup.subset_closure ⟨m * n, mul_mem hm hn, rfl⟩
        have := mul_mem (inv_mem h1) h2
        convert this using 1
        group
      | one => intro m _; rw [mul_one, mul_inv_cancel]; exact one_mem _
      | mul x y _ _ hx hy =>
        intro m hm
        rw [show m * (x * y) * m⁻¹ = m * x * m⁻¹ * (m * y * m⁻¹) by group]
        exact mul_mem (hx m hm) (hy m hm)
      | inv x _ hx =>
        intro m hm
        rw [show m * x⁻¹ * m⁻¹ = (m * x * m⁻¹)⁻¹ by group]
        exact inv_mem (hx m hm)
    exact key _ hk _ m.2
  have hcent : ∀ c ∈ E, (∀ n ∈ N, c * n = n * c) → N ≤ Subgroup.center X := by
    intro c hc hcN n hn
    refine (Pair.mem_center_iff hP).2 fun e he => ?_
    obtain ⟨g, rfl⟩ := isConj_iff.1 (Pair.isConj hP hc he)
    have hn' : g⁻¹ * n * g ∈ N := by simpa using hN.conj_mem n hn g⁻¹
    have := hcN _ hn'
    calc g * c * g⁻¹ * n = g * (c * (g⁻¹ * n * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * n * g) * c) * g⁻¹ := by rw [this]
      _ = n * (g * c * g⁻¹) := by group
  have := hKn
  rcases hNs.eq_bot_or_eq_top_of_normal (K.subgroupOf N) with hK | hK
  ·
    refine hcent b hb fun n hn => ?_
    have hmem : b * n * b⁻¹ * n⁻¹ ∈ K := Subgroup.subset_closure ⟨n, hn, rfl⟩
    have h1 : (⟨_, hKN hmem⟩ : N) ∈ K.subgroupOf N := Subgroup.mem_subgroupOf.2 hmem
    rw [hK, Subgroup.mem_bot] at h1
    have h2 : b * n * b⁻¹ * n⁻¹ = 1 := congrArg Subtype.val h1
    calc b * n = b * n * b⁻¹ * n⁻¹ * (n * b) := by group
      _ = n * b := by rw [h2, one_mul]
  ·
    refine hcent a ha fun n hn => haK n ?_
    have : (⟨n, hn⟩ : N) ∈ K.subgroupOf N := hK ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

theorem Pair.isSimpleGroup_commutator_of_connected (hP : Pair X E)
    (hZ : Subgroup.center X = ⊥) (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥)
    (hconn : (commGraph E).Connected) : IsSimpleGroup (commutator X) := by
  have := Pair.finite hP
  obtain ⟨e₀, he₀⟩ := Pair.nonempty hP
  have htop : (⊤ : Subgroup X) ≠ ⊥ := by
    intro h
    have := Subgroup.mem_top e₀
    rw [h, Subgroup.mem_bot] at this
    exact Pair.ne_one hP he₀ this
  obtain ⟨N, hNn, -, hNbot, hmin⟩ := CFSG.exists_minimal_normal_le ⊤ inferInstance htop
  have hNs := Pair.isSimpleGroup_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have hNsol := Pair.not_isSolvable_of_minimal hP hZ h2 h3 hNn hNbot hmin
  have := hNn
  have hNZ : ¬ N ≤ Subgroup.center X := fun h => hNbot (by rw [← le_bot_iff, ← hZ]; exact h)
  have hNle : N ≤ commutator X := by
    have hcN : commutator N = ⊤ := by
      rcases hNs.eq_bot_or_eq_top_of_normal (commutator N) with h | h
      · exfalso
        apply hNsol
        refine Group.isSolvable_of_comm fun a b => ?_
        have hc : ⁅a, b⁆ ∈ commutator N := by
          rw [commutator_def]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
        rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      · exact h
    intro n hn
    have hmem : (⟨n, hn⟩ : N) ∈ commutator N := hcN ▸ Subgroup.mem_top _
    have h1 : n ∈ (commutator N).map N.subtype := ⟨⟨n, hn⟩, hmem, rfl⟩
    rw [Subgroup.map_subtype_commutator] at h1
    exact Subgroup.commutator_mono le_top le_top h1
  have hcong : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a → a⁻¹ * b ∈ N := by
    intro a ha b hb hab
    by_contra hne
    refine hNZ (Pair.normal_le_center_of_commute hP hNn hNs ha hb hab fun n hn => ?_)
    by_contra hc
    apply hne
    have hb' := Pair.conj_mem hP hb n
    have h1 := Pair.mul_conj_left_eq hP ha hb' hc
    have hπ : (QuotientGroup.mk (n * b * n⁻¹) : X ⧸ N) = QuotientGroup.mk b := by
      rw [QuotientGroup.eq]
      have := mul_mem hn (hNn.conj_mem _ (inv_mem hn) b⁻¹)
      convert this using 1
      group
    generalize n * b * n⁻¹ = b' at h1 hπ
    have key : (QuotientGroup.mk b : X ⧸ N) = QuotientGroup.mk a := by
      rw [← hπ]
      conv_lhs => rw [← h1]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hπ]
      have hab' : (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b =
          QuotientGroup.mk b * QuotientGroup.mk a := by
        rw [← QuotientGroup.mk_mul, hab, QuotientGroup.mk_mul]
      calc (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b * QuotientGroup.mk a *
            (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹
          = QuotientGroup.mk a * (QuotientGroup.mk b * QuotientGroup.mk a) *
            (QuotientGroup.mk a * QuotientGroup.mk b)⁻¹ := by group
        _ = QuotientGroup.mk a := by rw [← hab']; group
    exact QuotientGroup.eq.1 key.symm
  have hall : ∀ e ∈ E, e₀⁻¹ * e ∈ N := fun e he =>
    reachable_induction (G := commGraph E) (p := fun x : E => e₀⁻¹ * (x : X) ∈ N)
      (fun x y hxy hx => by
        rw [show e₀⁻¹ * (y : X) = (e₀⁻¹ * x) * ((x : X)⁻¹ * y) by group]
        exact mul_mem hx (hcong x x.2 y y.2 hxy.2))
      (hconn ⟨e₀, he₀⟩ ⟨e, he⟩) (by
        show e₀⁻¹ * e₀ ∈ N
        rw [inv_mul_cancel]
        exact one_mem _)
  have hle : commutator X ≤ N := by
    rw [← Subgroup.Normal.quotient_commutative_iff_commutator_le]
    have hpow : ∀ g : X, (QuotientGroup.mk g : X ⧸ N) ∈
        Subgroup.zpowers (QuotientGroup.mk e₀ : X ⧸ N) := by
      intro g
      have hg : g ∈ Subgroup.closure E := (Pair.closure_eq hP).symm ▸ Subgroup.mem_top g
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        rw [(QuotientGroup.eq.2 (hall x hx)).symm]
        exact Subgroup.mem_zpowers _
      | one => exact one_mem _
      | mul x y _ _ hx hy => rw [QuotientGroup.mk_mul]; exact mul_mem hx hy
      | inv x _ hx => rw [QuotientGroup.mk_inv]; exact inv_mem hx
    refine ⟨⟨fun q₁ q₂ => ?_⟩⟩
    obtain ⟨g₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨g₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    obtain ⟨k₁, hk₁⟩ := Subgroup.mem_zpowers_iff.1 (hpow g₁)
    obtain ⟨k₂, hk₂⟩ := Subgroup.mem_zpowers_iff.1 (hpow g₂)
    rw [← hk₁, ← hk₂, ← zpow_add, ← zpow_add, add_comm]
  rw [le_antisymm hle hNle]
  exact hNs

theorem Pair.exists_not_commute_commutator (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (h2 : ∀ N : Subgroup X, N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup X, N.Normal → IsPGroup 3 N → N = ⊥)
    (hs : IsSimpleGroup (commutator X)) : ∃ a b : commutator X, a * b ≠ b * a := by
  by_contra! hcomm
  have := Pair.finite hP
  have : IsMulCommutative (commutator X) := ⟨⟨hcomm⟩⟩
  have hp := (Group.is_simple_iff_prime_card (α := commutator X)).1 hs
  have hpg : IsPGroup (Nat.card (commutator X)) (commutator X) :=
    IsPGroup.of_card (n := 1) (pow_one _).symm
  have hne : commutator X ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hp4 : Nat.card (commutator X) ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
  have := hp.two_le
  rcases (show Nat.card (commutator X) = 2 ∨ Nat.card (commutator X) = 3 ∨
      5 ≤ Nat.card (commutator X) by omega) with h | h | h5
  · exact hne (h2 _ inferInstance (h ▸ hpg))
  · exact hne (h3 _ inferInstance (h ▸ hpg))
  · exact hne (Pair.eq_bot_of_isPGroup hP hZ hp h5 inferInstance hpg)

theorem Pair.connected_commGraph_localImages (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {d : X}
    (hd : d ∈ E)
    (h2 : ∀ N : Subgroup (LocalQuotient E d), N.Normal → IsPGroup 2 N → N = ⊥)
    (h3 : ∀ N : Subgroup (LocalQuotient E d), N.Normal → IsPGroup 3 N → N = ⊥) :
    (commGraph (LocalImages E d)).Connected := by
  have hPH := Pair.pair_localQuotient hP hZ hS hna hd
  have hZH := Pair.center_localQuotient hP hZ hS hd
  have hinj := Pair.starImage_injective_of_simple hP hZ hS hd
  have hmemF : ∀ f : LocalClass E d, starImage E d f ∈ LocalImages E d := fun f => by
    rw [← range_starImage]
    exact ⟨f, rfl⟩
  have hsurj : ∀ q ∈ LocalImages E d, ∃ f : LocalClass E d, starImage E d f = q := by
    intro q hq
    rw [← range_starImage] at hq
    exact hq
  have hedge : ∃ u ∈ LocalClass E d, ∃ v ∈ LocalClass E d, u ≠ v ∧ u * v = v * u := by
    obtain ⟨p, hp, q, hq, hpq, hpqc⟩ := Pair.exists_ne_commute_of_three hPH hZH h3
    obtain ⟨u, rfl⟩ := hsurj p hp
    obtain ⟨v, rfl⟩ := hsurj q hq
    refine ⟨u, u.2, v, v.2, fun h => hpq (congrArg _ (Subtype.ext h)), ?_⟩
    exact (Pair.starImage_commute_iff hP u v).1 hpqc
  have hV : ∀ u ∈ LocalClass E d, ∀ v ∈ LocalClass E d,
      (∀ w ∈ LocalClass E d, w * u = u * w ↔ w * v = v * w) → u = v := by
    intro u hu v hv huv
    have h := Pair.eq_of_forall_commute_iff_of_two hPH h2 (hmemF ⟨u, hu⟩) (hmemF ⟨v, hv⟩)
      fun w hw => by
        obtain ⟨w, rfl⟩ := hsurj w hw
        have e1 := Pair.starImage_commute_iff hP w ⟨u, hu⟩
        have e2 := Pair.starImage_commute_iff hP w ⟨v, hv⟩
        exact (e1.trans ((huv w w.2).trans e2.symm))
    exact congrArg Subtype.val (hinj h)
  have hconnD := Pair.connected_commGraph_localClass hP hZ hS hna hd hedge hV
  let φ : commGraph (LocalClass E d) →g commGraph (LocalImages E d) :=
    { toFun := fun f => ⟨starImage E d f, hmemF f⟩
      map_rel' := fun {a b} hab => by
        refine commGraph_adj_iff.2 ⟨fun h => ?_, ?_⟩
        · exact (commGraph_adj_iff.1 hab).1 (congrArg Subtype.val (hinj h))
        · exact (Pair.starImage_commute_iff hP a b).2 (commGraph_adj_iff.1 hab).2 }
  refine (SimpleGraph.connected_iff _).2 ⟨fun p q => ?_, ⟨⟨_, hmemF ⟨_, hedge.choose_spec.1⟩⟩⟩⟩
  obtain ⟨u, hu⟩ := hsurj p p.2
  obtain ⟨v, hv⟩ := hsurj q q.2
  have h := (hconnD u v).map φ
  have hu' : φ u = p := Subtype.ext hu
  have hv' : φ v = q := Subtype.ext hv
  rwa [hu', hv'] at h

theorem Pair.local_trichotomy (hP : Pair X E) (hZ : Subgroup.center X = ⊥)
    (hS : IsSimpleGroup (commutator X)) (hna : ∃ a b : commutator X, a * b ≠ b * a) {d : X}
    (hd : d ∈ E) :
    (∃ N : Subgroup (LocalQuotient E d), N.Normal ∧ N ≠ ⊥ ∧ IsPGroup 3 N) ∨
    (∃ N : Subgroup (LocalQuotient E d), N.Normal ∧ N ≠ ⊥ ∧ IsPGroup 2 N) ∨
    (Pair (LocalQuotient E d) (LocalImages E d) ∧ Subgroup.center (LocalQuotient E d) = ⊥ ∧
      IsSimpleGroup (commutator (LocalQuotient E d)) ∧
      (∃ a b : commutator (LocalQuotient E d), a * b ≠ b * a) ∧
      Nat.card (LocalQuotient E d) < Nat.card X) := by
  by_cases h3' : ∃ N : Subgroup (LocalQuotient E d), N.Normal ∧ N ≠ ⊥ ∧ IsPGroup 3 N
  · exact Or.inl h3'
  by_cases h2' : ∃ N : Subgroup (LocalQuotient E d), N.Normal ∧ N ≠ ⊥ ∧ IsPGroup 2 N
  · exact Or.inr (Or.inl h2')
  right; right
  have h3 : ∀ N : Subgroup (LocalQuotient E d), N.Normal → IsPGroup 3 N → N = ⊥ :=
    fun N hN hp => by_contra fun h => h3' ⟨N, hN, h, hp⟩
  have h2 : ∀ N : Subgroup (LocalQuotient E d), N.Normal → IsPGroup 2 N → N = ⊥ :=
    fun N hN hp => by_contra fun h => h2' ⟨N, hN, h, hp⟩
  have hPH := Pair.pair_localQuotient hP hZ hS hna hd
  have hZH := Pair.center_localQuotient hP hZ hS hd
  have hconnF := Pair.connected_commGraph_localImages hP hZ hS hna hd h2 h3
  have hsimple := Pair.isSimpleGroup_commutator_of_connected hPH hZH h2 h3 hconnF
  exact ⟨hPH, hZH, hsimple, Pair.exists_not_commute_commutator hPH hZH h2 h3 hsimple,
    Pair.card_localQuotient_lt hP hZ hd⟩

theorem trichotomyInput : TrichotomyInput := by
  intro G _ D hHyp hna
  obtain ⟨d, hd⟩ := Pair.nonempty hHyp.pair
  refine ⟨d, hd, Pair.localClass_nonempty hHyp.pair hHyp.simple hna hd, ?_⟩
  rcases Pair.local_trichotomy hHyp.pair hHyp.center hHyp.simple hna hd with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨⟨h.1, h.2.1, h.2.2.1⟩, h.2.2.2.2⟩)

end CFSG.Fischer.Classification
