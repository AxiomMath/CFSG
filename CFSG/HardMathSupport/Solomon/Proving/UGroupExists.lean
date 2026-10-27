module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Basic

public section

namespace CFSG.HardMathSupport.Solomon.Proving

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G]

theorem klein_table {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    a * a = 1 ∧ b * b = 1 ∧ a * (a * b) = b ∧ b * (a * b) = a ∧ a * b * a = b ∧
      a * b * b = a ∧ a * b * (a * b) = 1 := by
  have haa : a * a = 1 := by rw [← pow_two]; exact ha
  have hbb : b * b = 1 := by rw [← pow_two]; exact hb
  refine ⟨haa, hbb, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← mul_assoc, haa, one_mul]
  · rw [← mul_assoc, ← hab, mul_assoc, hbb, mul_one]
  · rw [mul_assoc, ← hab, ← mul_assoc, haa, one_mul]
  · rw [mul_assoc, hbb, mul_one]
  · calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [haa, hbb, one_mul]

@[expose] def kleinOf {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    Subgroup G where
  carrier := {1, a, b, a * b}
  mul_mem' := by
    obtain ⟨haa, hbb, h1, h2, h3, h4, h5⟩ := klein_table ha hb hab
    intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      simp only [mul_one, one_mul, haa, hbb, h1, h2, h3, h4, h5, ← hab, true_or, or_true,
        ]
  one_mem' := by simp
  inv_mem' := by
    obtain ⟨haa, hbb, -, -, -, -, h5⟩ := klein_table ha hb hab
    have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    have ib : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have iab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h5
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl <;> simp [ia, ib, iab]

variable {a b : G}

theorem mem_kleinOf {ha : a ^ 2 = 1} {hb : b ^ 2 = 1} {hab : a * b = b * a} {x : G} :
    x ∈ kleinOf ha hb hab ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  change x ∈ ({1, a, b, a * b} : Set G) ↔ _
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem isPPlane_kleinOf [Finite G] {ha : a ^ 2 = 1} {hb : b ^ 2 = 1} {hab : a * b = b * a}
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    IsPPlane 2 (kleinOf ha hb hab) := by
  obtain ⟨haa, hbb, h1, h2, h3, h4, h5⟩ := klein_table ha hb hab
  have ia : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have hcomm : ∀ x ∈ kleinOf ha hb hab, ∀ y ∈ kleinOf ha hb hab, x * y = y * x := by
    intro x hx y hy
    rw [mem_kleinOf] at hx hy
    rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
      (try simp only [mul_one, one_mul, haa, hbb, h1, h2, h3, h4, h5]) <;>
      first | rfl | exact hab | exact hab.symm
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (hcomm x.1 x.2 y.1 y.2)⟩⟩, ?_⟩, ?_⟩
  · intro x hx
    rw [mem_kleinOf] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp
    · exact ha
    · exact hb
    · rw [pow_two]; exact h5
  · have hiab : a * b ≠ 1 := by
      intro h
      apply hne
      rw [← inv_eq_of_mul_eq_one_right h, ia]
    have n1 : (1 : G) ∉ ({a, b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hiab.symm⟩
    have n2 : a ∉ ({b, a * b} : Set G) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨hne, fun h => hb1 ?_⟩
      have : a * b = a * 1 := by rw [mul_one]; exact h.symm
      exact mul_left_cancel this
    have n3 : b ∉ ({a * b} : Set G) := by
      simp only [Set.mem_singleton_iff]
      intro h
      have : a * b = 1 * b := by rw [one_mul]; exact h.symm
      exact ha1 (mul_right_cancel this)
    have hc : Nat.card (kleinOf ha hb hab) =
        Set.ncard ((kleinOf ha hb hab : Subgroup G) : Set G) := Nat.card_coe_set_eq _
    have hset : ((kleinOf ha hb hab : Subgroup G) : Set G) = {1, a, b, a * b} := rfl
    rw [hc, hset, Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
      Set.ncard_insert_of_notMem n3, Set.ncard_singleton]
    norm_num

theorem exists_ne_fixed_of_even {P α : Type} [Group P] [MulAction P α] [Finite α]
    (hP : IsPGroup 2 P) (o : α) (ho : ∀ t : P, t • o = o) (heven : Even (Nat.card α)) :
    ∃ x : α, x ≠ o ∧ ∀ t : P, t • x = x := by
  by_contra hcon
  push Not at hcon
  have hmem : MulAction.fixedPoints P α = {o} := by
    ext x
    constructor
    · intro hx
      by_contra hxo
      obtain ⟨t, ht⟩ := hcon x hxo
      exact ht ((MulAction.mem_fixedPoints.1 hx) t)
    · intro hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact MulAction.mem_fixedPoints.2 ho
  have hfix : Nat.card (MulAction.fixedPoints P α) = 1 := by
    rw [hmem]
    simp
  have hcong := hP.card_modEq_card_fixedPoints α
  rw [hfix] at hcong
  obtain ⟨r, hr⟩ := heven
  unfold Nat.ModEq at hcong
  omega

theorem exists_fixed_coset {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (hT : IsPGroup 2 T) (hMn : T ≤ Subgroup.normalizer (M : Set G))
    (hM : CFSG.Open.IsElemAbelian 2 M) (hM4 : 4 ≤ Nat.card M)
    {z : G} (hzM : z ∈ M) (hz2 : z ^ 2 = 1) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t) :
    ∃ m ∈ M, m ≠ 1 ∧ m ≠ z ∧ ∀ t ∈ T, t * m * t⁻¹ = m ∨ t * m * t⁻¹ = m * z := by
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz2
  let zM : M := ⟨z, hzM⟩
  let N : Subgroup M := Subgroup.zpowers zM
  have hzM2 : zM ^ 2 = 1 := Subtype.ext (by simp [zM, hz2])
  have hzM1 : zM ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hord : orderOf zM = 2 := orderOf_eq_prime hzM2 hzM1
  have hN2 : Nat.card N = 2 := by
    show Nat.card (Subgroup.zpowers zM) = 2
    rw [Nat.card_zpowers, hord]
  have hNnorm : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute g zM := hM.1.is_comm.comm g zM
    rw [(hc.zpow_right k).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers zM) k
  have hconj : ∀ t : T, ∀ x : M, (t : G) * (x : G) * (t : G)⁻¹ ∈ M := fun t x =>
    (Subgroup.mem_normalizer_iff.1 (hMn t.2) (x : G)).1 x.2
  let φ : T → (M →* M) := fun t =>
    { toFun := fun x => ⟨(t : G) * (x : G) * (t : G)⁻¹, hconj t x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hφfix : ∀ t : T, φ t zM = zM := fun t => Subtype.ext (by
    show (t : G) * z * (t : G)⁻¹ = z
    rw [hzc (t : G) t.2, mul_assoc, mul_inv_cancel, mul_one])
  have hφN : ∀ t : T, N ≤ N.comap (φ t) := fun t =>
    Subgroup.zpowers_le.2 (by
      rw [Subgroup.mem_comap, hφfix t]
      exact Subgroup.mem_zpowers zM)
  let _instAct : MulAction T (M ⧸ N) :=
    { smul := fun t q => QuotientGroup.map N N (φ t) (hφN t) q
      one_smul := fun q => by
        refine QuotientGroup.induction_on q (fun x => ?_)
        show QuotientGroup.map N N (φ 1) (hφN 1) (x : M ⧸ N) = x
        rw [QuotientGroup.map_mk]
        congr 1
        apply Subtype.ext
        show ((1 : T) : G) * (x : G) * ((1 : T) : G)⁻¹ = x
        simp
      mul_smul := fun t s q => by
        refine QuotientGroup.induction_on q (fun x => ?_)
        show QuotientGroup.map N N (φ (t * s)) (hφN (t * s)) (x : M ⧸ N) =
          QuotientGroup.map N N (φ t) (hφN t) (QuotientGroup.map N N (φ s) (hφN s) (x : M ⧸ N))
        rw [QuotientGroup.map_mk, QuotientGroup.map_mk, QuotientGroup.map_mk]
        congr 1
        apply Subtype.ext
        show ((t * s : T) : G) * (x : G) * ((t * s : T) : G)⁻¹ =
          (t : G) * ((s : G) * (x : G) * (s : G)⁻¹) * (t : G)⁻¹
        simp only [Subgroup.coe_mul]
        group }
  have hMp : IsPGroup 2 M := by
    refine IsPGroup.iff_orderOf.2 (fun g => ?_)
    have hg2 : g ^ 2 = 1 := Subtype.ext (by simpa using hM.2 (g : G) g.2)
    rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hg2) with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hMp
  have hn2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have hle : 2 ^ n ≤ 2 := by interval_cases n <;> norm_num
    omega
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn2
  have hQ : Nat.card (M ⧸ N) * 2 = 4 * 2 ^ j := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hN2, hn, pow_add] at h1
    norm_num at h1
    omega
  have heven : Even (Nat.card (M ⧸ N)) := ⟨2 ^ j, by omega⟩
  obtain ⟨x, hx1, hxfix⟩ := exists_ne_fixed_of_even hT (1 : M ⧸ N)
    (fun t => map_one (QuotientGroup.map N N (φ t) (hφN t))) heven
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  have hm1 : m ≠ 1 := fun h => hx1 (by rw [h]; rfl)
  have hmz : m ≠ zM := fun h => hx1 ((QuotientGroup.eq_one_iff m).2 (by
    rw [h]
    exact Subgroup.mem_zpowers zM))
  refine ⟨(m : G), m.2, fun h => hm1 (Subtype.ext h), fun h => hmz (Subtype.ext h), ?_⟩
  intro t ht
  have hfix := hxfix ⟨t, ht⟩
  have hq : QuotientGroup.map N N (φ ⟨t, ht⟩) (hφN ⟨t, ht⟩) (m : M ⧸ N) = (m : M ⧸ N) := hfix
  rw [QuotientGroup.map_mk, QuotientGroup.eq] at hq
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hq
  have hk' : zM ^ (k % (2 : ℤ)) = zM ^ k := by
    have := zpow_mod_orderOf zM k
    rw [hord] at this
    exact_mod_cast this
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero] at hk'
    rw [← hk'] at hk
    have h2 : (((φ ⟨t, ht⟩ m) : M) : G)⁻¹ * (m : G) = 1 := (congrArg Subtype.val hk).symm
    exact (inv_mul_eq_one.1 h2)
  · right
    rw [h1, zpow_one] at hk'
    rw [← hk'] at hk
    have h2 : (((φ ⟨t, ht⟩ m) : M) : G)⁻¹ * (m : G) = z := (congrArg Subtype.val hk).symm
    have h3 : (m : G) = (((φ ⟨t, ht⟩ m) : M) : G) * z := inv_mul_eq_iff_eq_mul.1 h2
    calc (t : G) * (m : G) * (t : G)⁻¹ = ((φ ⟨t, ht⟩ m) : M) := rfl
      _ = ((φ ⟨t, ht⟩ m) : M) * (z * z) := by rw [hzz, mul_one]
      _ = (m : G) * z := by rw [← mul_assoc, ← h3]

theorem normal_klein_of_normal_elemAbelian [Finite G] {T M : Subgroup G} (hT : IsPGroup 2 T)
    (hMT : M ≤ T) (hMn : T ≤ Subgroup.normalizer (M : Set G))
    (hM : CFSG.Open.IsElemAbelian 2 M) (hM4 : 4 ≤ Nat.card M)
    {z : G} (hzM : z ∈ M) (hz1 : z ≠ 1) (hzc : ∀ t ∈ T, t * z = z * t) :
    ∃ U : Subgroup G, IsPPlane 2 U ∧ U ≤ T ∧ T ≤ Subgroup.normalizer (U : Set G) := by
  obtain ⟨m, hmM, hm1, hmz, hfix⟩ :=
    exists_fixed_coset hT hMn hM hM4 hzM (hM.2 z hzM) hz1 hzc
  have hzz : z * z = 1 := by rw [← pow_two]; exact hM.2 z hzM
  have ha : m ^ 2 = 1 := hM.2 m hmM
  have hb : z ^ 2 = 1 := hM.2 z hzM
  have hab : m * z = z * m := hzc m (hMT hmM)
  refine ⟨kleinOf ha hb hab, isPPlane_kleinOf hm1 hz1 hmz, ?_, ?_⟩
  · intro x hx
    rw [mem_kleinOf] at hx
    rcases hx with h1 | h1 | h1 | h1 <;> rw [h1]
    · exact T.one_mem
    · exact hMT hmM
    · exact hMT hzM
    · exact T.mul_mem (hMT hmM) (hMT hzM)
  · have hz' : ∀ t ∈ T, t * z * t⁻¹ = z := fun t ht => by
      rw [hzc t ht, mul_assoc, mul_inv_cancel, mul_one]
    have key : ∀ t ∈ T, ∀ h ∈ kleinOf ha hb hab, t * h * t⁻¹ ∈ kleinOf ha hb hab := by
      intro t ht h hh
      rw [mem_kleinOf] at hh ⊢
      rcases hh with h1 | h1 | h1 | h1
      · rw [h1]
        left
        simp
      · rw [h1]
        rcases hfix t ht with e | e
        · right; left; exact e
        · right; right; right; exact e
      · rw [h1, hz' t ht]
        right; right; left; rfl
      · have e2 : t * (m * z) * t⁻¹ = (t * m * t⁻¹) * (t * z * t⁻¹) := by group
        rw [h1, e2, hz' t ht]
        rcases hfix t ht with e | e
        · rw [e]; right; right; right; rfl
        · rw [e]; right; left; rw [mul_assoc, hzz, mul_one]
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => key t ht h hh
    · intro hh
      have h2 := key t⁻¹ (T.inv_mem ht) (t * h * t⁻¹) hh
      have e : t⁻¹ * (t * h * t⁻¹) * t⁻¹⁻¹ = h := by group
      rw [e] at h2
      exact h2

end CFSG.HardMathSupport.Solomon.Proving

end
