module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup

theorem subsingleton_of_perfect_of_solvable {X : Type*} [Group X] [Group.IsSolvable X]
    (h : Group.IsPerfect X) : Subsingleton X := by
  by_contra hne
  have : Nontrivial X := not_subsingleton_iff_nontrivial.mp hne
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial X
  rw [Group.isPerfect_def] at h
  exact h1.ne h

theorem NoPQuotient.of_isPerfect {p : ℕ} [Fact p.Prime] {X : Type*} [Group X] [Finite X]
    (h : Group.IsPerfect X) : NoPQuotient p X := by
  intro N _ hN
  have hperf : Group.IsPerfect (X ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have := hN.isNilpotent
  have : Group.IsSolvable (X ⧸ N) := inferInstance
  have hsub := subsingleton_of_perfect_of_solvable hperf
  rw [eq_top_iff]
  intro x _
  have : (QuotientGroup.mk x : X ⧸ N) = 1 := Subsingleton.elim _ _
  exact (QuotientGroup.eq_one_iff x).mp this

private theorem orderOf_conj' {G : Type*} [Group G] (g x : G) :
    orderOf (g * x * g⁻¹) = orderOf x := by
  have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa [MulAut.conj_apply] using this

private theorem mem_of_pPrime {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    {X Y : Subgroup H} (hXY : X ≤ Y) (hXn : (X.subgroupOf Y).Normal)
    (hp : ∀ y ∈ Y, ∃ a ∈ X, ∃ k : ℕ, (a⁻¹ * y) ^ (p ^ k) = 1) {y : H} (hy : y ∈ Y)
    (hy' : ¬ p ∣ orderOf y) : y ∈ X := by
  obtain ⟨a, ha, k, hk⟩ := hp y hy
  set Xy : Subgroup Y := X.subgroupOf Y
  have hry : a⁻¹ * y ∈ Y := mul_mem (inv_mem (hXY ha)) hy
  have hmk : QuotientGroup.mk (s := Xy) ⟨y, hy⟩ = QuotientGroup.mk (s := Xy) ⟨a⁻¹ * y, hry⟩ := by
    rw [QuotientGroup.eq]
    show (⟨y, hy⟩ : Y)⁻¹ * ⟨a⁻¹ * y, hry⟩ ∈ Xy
    rw [Subgroup.mem_subgroupOf]
    have : y⁻¹ * (a⁻¹ * y) = y⁻¹ * a⁻¹ * y := by group
    show y⁻¹ * (a⁻¹ * y) ∈ X
    rw [this]
    have hconj := hXn.conj_mem (⟨a⁻¹, inv_mem (hXY ha)⟩ : Y)
      (Subgroup.mem_subgroupOf.mpr (inv_mem ha)) (⟨y⁻¹, inv_mem hy⟩ : Y)
    have := Subgroup.mem_subgroupOf.mp hconj
    simpa using this
  have h1 : orderOf (QuotientGroup.mk (s := Xy) ⟨y, hy⟩) ∣ p ^ k := by
    apply orderOf_dvd_of_pow_eq_one
    rw [hmk, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    have : (⟨a⁻¹ * y, hry⟩ : Y) ^ (p ^ k) = 1 := by
      apply Subtype.ext; simpa using hk
    rw [this]; exact one_mem _
  have h2 : orderOf (QuotientGroup.mk (s := Xy) ⟨y, hy⟩) ∣ orderOf y := by
    have := orderOf_map_dvd (QuotientGroup.mk' Xy) (⟨y, hy⟩ : Y)
    rw [Subgroup.orderOf_mk] at this
    exact this
  have hcop : Nat.Coprime (orderOf y) (p ^ k) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hy').symm
  have h3 : orderOf (QuotientGroup.mk (s := Xy) ⟨y, hy⟩) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h2 h1
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact Subgroup.mem_subgroupOf.mp h3

theorem normal_of_subnormal_of_noPQuotient {H : Type*} [Group H] [Finite H] {p : ℕ}
    [Fact p.Prime] {X R : Subgroup H} [R.Normal] (hR : IsPGroup p R) (hXR : X ⊔ R = ⊤)
    (hX : X.IsSubnormal) (hno : NoPQuotient p X) : X.Normal := by
  obtain ⟨n, f, hmono, hnorm, h0, hn⟩ := Subgroup.IsSubnormal.isSubnormal_iff.mp hX
  have hp : ∀ y : H, ∃ a ∈ X, ∃ k : ℕ, (a⁻¹ * y) ^ (p ^ k) = 1 := by
    intro y
    have hy : y ∈ X ⊔ R := hXR ▸ mem_top y
    obtain ⟨a, ha, r, hr, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hy
    obtain ⟨k, hk⟩ := hR ⟨r, hr⟩
    exact ⟨a, ha, k, by simpa using congrArg Subtype.val hk⟩
  have hXcl : Subgroup.closure {x : H | x ∈ X ∧ ¬ p ∣ orderOf x} = X := hno.closure_eq_ambient
  have key : ∀ i : ℕ, X ≤ f i ∧ (X.subgroupOf (f i)).Normal := by
    intro i
    induction i with
    | zero =>
      rw [h0]
      exact ⟨le_rfl, by rw [Subgroup.subgroupOf_self]; infer_instance⟩
    | succ i ih =>
      obtain ⟨hXle, hXn⟩ := ih
      have hXi : Subgroup.closure {y : H | y ∈ f i ∧ ¬ p ∣ orderOf y} = X := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          intro y hy
          exact mem_of_pPrime hXle hXn (fun y _ => hp y) hy.1 hy.2
        · rw [← hXcl]
          exact Subgroup.closure_mono fun x hx => ⟨hXle hx.1, hx.2⟩
      refine ⟨hXle.trans (hmono (Nat.le_succ i)), ?_⟩
      refine ⟨fun x hx g => ?_⟩
      have hx' : (x : H) ∈ X := Subgroup.mem_subgroupOf.mp hx
      have hconj : ∀ y ∈ f i, (g : H) * y * (g : H)⁻¹ ∈ f i := by
        intro y hy
        have := (hnorm i).conj_mem ⟨y, hmono (Nat.le_succ i) hy⟩
          (Subgroup.mem_subgroupOf.mpr hy) g
        exact Subgroup.mem_subgroupOf.mp this
      rw [Subgroup.mem_subgroupOf]
      rw [← hXi] at hx' ⊢
      have hcl : ∀ z ∈ Subgroup.closure {y : H | y ∈ f i ∧ ¬ p ∣ orderOf y},
          (g : H) * z * (g : H)⁻¹ ∈ Subgroup.closure {y : H | y ∈ f i ∧ ¬ p ∣ orderOf y} := by
        intro z hz
        induction hz using Subgroup.closure_induction with
        | mem y hy =>
          apply Subgroup.subset_closure
          refine ⟨hconj y hy.1, ?_⟩
          rw [orderOf_conj']; exact hy.2
        | one => simp
        | mul a b _ _ iha ihb =>
          have := mul_mem iha ihb
          simpa [mul_assoc] using this
        | inv a _ ih =>
          have := inv_mem ih
          simpa [mul_assoc] using this
      exact hcl _ hx'
  have := (key n).2
  rw [hn] at this
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top, top_le_iff,
    Subgroup.normalizer_eq_top_iff] at this
  exact this

theorem mem_normalizer_commutator {G : Type*} [Group G] {x : G} {A B : Subgroup G}
    (hA : x ∈ normalizer (A : Set G)) (hB : x ∈ normalizer (B : Set G)) :
    x ∈ normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ x : G, x ∈ normalizer (A : Set G) → x ∈ normalizer (B : Set G) →
      ∀ y ∈ (⁅A, B⁆ : Subgroup G), x * y * x⁻¹ ∈ (⁅A, B⁆ : Subgroup G) := by
    intro x hA hB y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hy
      have h1 : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hA a).mp ha
      have h2 : x * b * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hB b).mp hb
      have := Subgroup.commutator_mem_commutator h1 h2
      convert this using 1
      simp only [commutatorElement_def]; group
    | one => simp
    | mul a b _ _ iha ihb =>
      have := mul_mem iha ihb
      simpa [mul_assoc] using this
    | inv a _ ih =>
      have := inv_mem ih
      simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hA hB y, fun hy => ?_⟩
  have := key x⁻¹ (inv_mem hA) (inv_mem hB) _ hy
  simpa [mul_assoc] using this

theorem pCoreOf_eq {E : Type*} [Group E] (p : ℕ) (X : Subgroup E) :
    CFSG.Open.pCoreOf p X = (CFSG.pCore p X).map X.subtype := by
  unfold CFSG.Open.pCoreOf
  try with_reducible rfl

theorem prime_residual_subnormal_p_signalizer_action {E : Type*} [Group E] [Finite E] {p : ℕ}
    [Fact p.Prime] {X R : Subgroup E} (hX : X.IsSubnormal) (hno : NoPQuotient p X)
    (hR : IsPGroup p R) (hXR : X ≤ normalizer (R : Set E)) :
    R ≤ normalizer (X : Set E) ∧ ⁅X, R⁆ ≤ CFSG.Open.pCoreOf p X := by
  set H : Subgroup E := X ⊔ R with hH
  have hXH : X ≤ H := le_sup_left
  have hRH : R ≤ H := le_sup_right
  have hHN : H ≤ normalizer (R : Set E) := sup_le hXR Subgroup.le_normalizer
  have hRn : (R.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRH).mpr hHN
  have hsup : X.subgroupOf H ⊔ R.subgroupOf H = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hXH,
      Subgroup.map_subgroupOf_eq_of_le hRH, Subgroup.map_top, Subgroup.range_subtype]
  have hsub : (X.subgroupOf H).IsSubnormal := hX.comap H.subtype
  have hnoX : NoPQuotient p (X.subgroupOf H) :=
    NoPQuotient.of_surjective (Subgroup.subgroupOfEquivOfLe hXH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXH).symm.surjective hno
  have hpR : IsPGroup p (R.subgroupOf H) :=
    hR.of_surjective (Subgroup.subgroupOfEquivOfLe hRH).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRH).symm.surjective
  have hXn : (X.subgroupOf H).Normal :=
    normal_of_subnormal_of_noPQuotient hpR hsup hsub hnoX
  have hHX : H ≤ normalizer (X : Set E) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mp hXn
  refine ⟨hRH.trans hHX, ?_⟩
  have hC1 : ⁅X, R⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have h1 : r * x⁻¹ * r⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hRH.trans hHX hr) x⁻¹).mp
      (inv_mem hx)
    have := mul_mem hx h1
    simpa [commutatorElement_def, mul_assoc] using this
  have hC2 : ⁅X, R⁆ ≤ R := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    have h1 : x * r * x⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hXR hx) r).mp hr
    have := mul_mem h1 (inv_mem hr)
    simpa [commutatorElement_def, mul_assoc] using this
  have hCn : (⁅X, R⁆.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hC1]
    intro x hx
    exact mem_normalizer_commutator (Subgroup.le_normalizer hx) (hXR hx)
  have hCp : IsPGroup p (⁅X, R⁆.subgroupOf X) :=
    (hR.to_le hC2).of_surjective (Subgroup.subgroupOfEquivOfLe hC1).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hC1).symm.surjective
  have hle : ⁅X, R⁆.subgroupOf X ≤ CFSG.pCore p X := le_sSup ⟨hCn, hCp⟩
  calc ⁅X, R⁆ = (⁅X, R⁆.subgroupOf X).map X.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hC1).symm
    _ ≤ CFSG.Open.pCoreOf p X := by rw [pCoreOf_eq]; exact Subgroup.map_mono hle

theorem quasisimple_pKernel_residual_isCComponent {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {L Q : Subgroup G} (hL : L.IsSubnormal) (hQL : Q ≤ L)
    (hQn : (Q.subgroupOf L).Normal) (hQp : IsPGroup p Q)
    (hq : CFSG.IsQuasisimple (L ⧸ Q.subgroupOf L)) (hno : NoPQuotient p L) :
    CFSG.IsCComponent L := by
  have hQp' : IsPGroup p (Q.subgroupOf L) :=
    hQp.of_surjective (Subgroup.subgroupOfEquivOfLe hQL).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hQL).symm.surjective
  have hperfL : Group.IsPerfect L := isPerfect_of_quotient _ hQp' hno hq.1
  have hnt : Nontrivial (L ⧸ Q.subgroupOf L) := CFSG.LocalCores.isQuasisimple_nontrivial hq
  refine ⟨?_, Subgroup.isPerfect_iff.mp hperfL, hL, ?_⟩
  · intro hbot
    obtain ⟨a, b, hab⟩ := exists_pair_ne (L ⧸ Q.subgroupOf L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have h1 : (a : G) = 1 := (Subgroup.eq_bot_iff_forall L).mp hbot a a.2
    have h2 : (b : G) = 1 := (Subgroup.eq_bot_iff_forall L).mp hbot b b.2
    have : a = b := Subtype.ext (h1.trans h2.symm)
    rw [this]
  · intro K hKL hK1 hKperf hKsub
    have hKLle : K ≤ L := hKL.le
    set Q' : Subgroup L := Q.subgroupOf L with hQ'
    set K₁ : Subgroup L := K.subgroupOf L with hK₁
    have hK₁sub : K₁.IsSubnormal := hKsub.comap L.subtype
    have hK : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hKperf
    have hK₁perf : Group.IsPerfect K₁ :=
      Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKLle).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hKLle).symm.surjective
    have hKbarsub : (K₁.map (QuotientGroup.mk' Q')).IsSubnormal :=
      hK₁sub.map (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_subnormal_subgroups hq hKbarsub with
      h | h
    · have hsup : K₁ ⊔ Q' = ⊤ := by
        have := Subgroup.comap_map_eq (QuotientGroup.mk' Q') K₁
        rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
        exact this.symm
      have hnoK : NoPQuotient p K₁ := NoPQuotient.of_isPerfect hK₁perf
      have hK₁n : K₁.Normal := normal_of_subnormal_of_noPQuotient hQp' hsup hK₁sub hnoK
      have hK₁top : K₁ = ⊤ := by
        refine hno K₁ ?_
        intro g
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
        have hx : x ∈ K₁ ⊔ Q' := hsup ▸ mem_top x
        obtain ⟨a, ha, q, hq', rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
        obtain ⟨k, hk⟩ := hQp' ⟨q, hq'⟩
        refine ⟨k, ?_⟩
        have hqk : q ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
        rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff a).mpr ha, one_mul,
          ← QuotientGroup.mk_pow, hqk]
        rfl
      apply hKL.ne
      apply le_antisymm hKLle
      intro x hx
      have : (⟨x, hx⟩ : L) ∈ K₁ := hK₁top ▸ mem_top _
      exact this
    · have hperfbar : ⁅K₁.map (QuotientGroup.mk' Q'), K₁.map (QuotientGroup.mk' Q')⁆ =
          K₁.map (QuotientGroup.mk' Q') := by
        rw [← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hK₁perf]
      have hbar : K₁.map (QuotientGroup.mk' Q') = ⊥ := by
        rw [eq_bot_iff]
        conv_lhs => rw [← hperfbar]
        rw [Subgroup.commutator_le]
        intro x hx y hy
        have := Subgroup.mem_center_iff.mp (h hx) y
        rw [Subgroup.mem_bot, commutatorElement_def]
        calc x * y * x⁻¹ * y⁻¹ = (y * x) * x⁻¹ * y⁻¹ := by rw [this]
          _ = 1 := by group
      have hKQ : K ≤ Q := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbar
        intro x hx
        have := hbar (show (⟨x, hKLle hx⟩ : L) ∈ K₁ from hx)
        exact this
      have hKp : IsPGroup p K := hQp.to_le hKQ
      have := hKp.isNilpotent
      have : Group.IsSolvable K := inferInstance
      have hsub := subsingleton_of_perfect_of_solvable hK
      apply hK1
      rw [eq_bot_iff_forall]
      intro x hx
      exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : K) 1)

theorem frattini_specialLinear_two_eq_bot (F : Type*) [Field F] [Finite F] [CharP F 2] :
    frattini (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  classical
  have hnt : Nontrivial (Projectivization F (Fin 2 → F)) := by
    refine ⟨⟨Projectivization.mk F (Pi.single 0 1) ?_, Projectivization.mk F (Pi.single 1 1) ?_,
      ?_⟩⟩
    · simp [Pi.single_eq_zero_iff]
    · simp [Pi.single_eq_zero_iff]
    · rw [Ne, Projectivization.mk_eq_mk_iff]
      rintro ⟨c, hc⟩
      have := congrFun hc 0
      simp at this
  have h1 : frattini (Matrix.SpecialLinearGroup (Fin 2) F) ≤
      (MulAction.toPermHom (Matrix.SpecialLinearGroup (Fin 2) F)
        (Projectivization F (Fin 2 → F))).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    ext p
    have := frattini_le_coatom (MulAction.IsPreprimitive.isCoatom_stabilizer_of_isPreprimitive
      (Matrix.SpecialLinearGroup (Fin 2) F) p) hx
    simpa using this
  rw [Projectivization.SL_mulAction_ker] at h1
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨r, hr, hrx⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (h1 hx)
  have hr2 : r ^ 2 = 1 := by simpa using hr
  have hr1 : r = 1 := by
    have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    have : (r - 1) ^ 2 = 0 := by linear_combination hr2 + (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
  rw [hr1] at hrx
  have : x = 1 := by
    ext i j
    have := congrArg (fun m => m i j) hrx
    simpa using this.symm
  rw [this]; exact one_mem _

end CFSG.QuasithinUnique.Setup.Campbell
