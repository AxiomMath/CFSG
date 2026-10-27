module

public import CFSG.LocalAnalysis.AGLEmbedding.OneLieReduced

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers

section NormalClosure

variable {Y : Type} [Group Y] {p : ℕ}

theorem eq_top_of_coprime_card_quotient_of_nclIn_eq {Jt Xt : Subgroup Y} (hX : IsPGroup p Xt)
    (hncl : nclIn Jt Xt = Jt) (V : Subgroup Jt) [V.Normal]
    (hV : p.Coprime (Nat.card (Jt ⧸ V))) : V = ⊤ := by
  have hXV : ∀ x : Jt, (x : Y) ∈ Xt → x ∈ V := by
    intro x hxX
    obtain ⟨k, hk⟩ := hX ⟨x, hxX⟩
    have hxk : x ^ p ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have h1 : orderOf (x : Jt ⧸ V) ∣ p ^ k := orderOf_dvd_of_pow_eq_one (by
      rw [← QuotientGroup.mk_pow, hxk, QuotientGroup.mk_one])
    have h3 : orderOf (x : Jt ⧸ V) = 1 :=
      Nat.eq_one_of_dvd_coprimes (hV.pow_left k) h1 (orderOf_dvd_natCard _)
    rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  have hVJ : V.map Jt.subtype ≤ Jt := Subgroup.map_subtype_le V
  have hJV : Jt ≤ Subgroup.normalizer ((V.map Jt.subtype : Subgroup Y) : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVJ).mp (by
      rw [Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective Jt.subtype_injective]
      infer_instance)
  have hXV' : Xt ⊓ Jt ≤ V.map Jt.subtype := fun x hx => ⟨⟨x, hx.2⟩, hXV ⟨x, hx.2⟩ hx.1, rfl⟩
  have h1 : nclIn Jt (Xt ⊓ Jt) = nclIn Jt Xt := by
    simp only [nclIn, Subgroup.inf_subgroupOf_right]
  have heq : Jt ≤ V.map Jt.subtype := by
    calc Jt = nclIn Jt (Xt ⊓ Jt) := by rw [h1, hncl]
      _ ≤ V.map Jt.subtype := nclIn_le hXV' hVJ hJV
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hy, hyx⟩ := heq x.2
  rwa [Subtype.ext hyx] at hy

theorem eq_top_of_map_eq_top_of_nclIn_eq {L : Type} [Group L] {Jt Xt : Subgroup Y}
    (hX : IsPGroup p Xt) (hncl : nclIn Jt Xt = Jt) (φ : Jt →* L)
    (hcop : p.Coprime (Nat.card φ.ker)) (V : Subgroup Jt) [V.Normal] (hV : V.map φ = ⊤) :
    V = ⊤ := by
  refine eq_top_of_coprime_card_quotient_of_nclIn_eq hX hncl V
    (Nat.Coprime.coprime_dvd_right ?_ hcop)
  refine Subgroup.card_dvd_of_surjective (f := (QuotientGroup.mk' V).comp φ.ker.subtype) ?_
  intro q
  obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨v, hv, hvj⟩ : φ j ∈ V.map φ := hV ▸ Subgroup.mem_top _
  refine ⟨⟨v⁻¹ * j, by rw [MonoidHom.mem_ker, map_mul, map_inv, hvj, inv_mul_cancel]⟩, ?_⟩
  simp only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
    QuotientGroup.mk'_apply]
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff v).mpr hv, inv_one,
    one_mul]

theorem eq_top_or_le_ker_of_nclIn_eq {L : Type} [Group L] (hL : IsSimpleGroup L)
    {Jt Xt : Subgroup Y} (hX : IsPGroup p Xt) (hncl : nclIn Jt Xt = Jt) (φ : Jt →* L)
    (hφ : Function.Surjective φ) (hcop : p.Coprime (Nat.card φ.ker)) (V : Subgroup Jt)
    [hV : V.Normal] : V = ⊤ ∨ V ≤ φ.ker := by
  have := hV.map φ hφ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.map φ) with hbot | htop
  · exact Or.inr ((Subgroup.map_eq_bot_iff _).mp hbot)
  · exact Or.inl (eq_top_of_map_eq_top_of_nclIn_eq hX hncl φ hcop V htop)

theorem isPerfect_of_nclIn_eq {L : Type} [Group L] (hL : IsSimpleGroup L)
    (hLnab : ∃ a b : L, a * b ≠ b * a) {Jt Xt : Subgroup Y} (hX : IsPGroup p Xt)
    (hncl : nclIn Jt Xt = Jt) (φ : Jt →* L) (hφ : Function.Surjective φ)
    (hcop : p.Coprime (Nat.card φ.ker)) : Group.IsPerfect Jt := by
  have hLp : commutator L = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator L) with hbot | htop
    · exfalso
      obtain ⟨a, b, hab⟩ := hLnab
      have h1 : (⊤ : Subgroup L) ≤ Subgroup.centralizer ((⊤ : Subgroup L) : Set L) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [← commutator_def]; exact hbot)
      exact hab (Subgroup.mem_centralizer_iff.mp (h1 (Subgroup.mem_top b)) a trivial)
    · exact htop
  refine ⟨eq_top_of_map_eq_top_of_nclIn_eq hX hncl φ hcop _ ?_⟩
  rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
    ← commutator_def]
  exact hLp

end NormalClosure

section Normal

variable {Y : Type} [Group Y] {p : ℕ}

open CFSG.ComponentClassification.OuterAutomorphisms in
theorem le_sup_centralizer_of_isPerfect {K J : Subgroup Y} [K.Normal] (hJ : Group.IsPerfect J)
    (hout : Group.IsSolvable (Outer K)) : J ≤ K ⊔ Subgroup.centralizer (K : Set Y) := by
  intro j hj
  let f : Y →* Outer K := (QuotientGroup.mk' (inner K)).comp MulAut.conjNormal
  obtain ⟨n, hn⟩ := hout.solvable
  have h1 : f j = 1 := by
    have hmem : (⟨j, hj⟩ : J) ∈ derivedSeries J n := by
      rw [Group.IsPerfect.derivedSeries_eq_top]
      exact Subgroup.mem_top _
    have h2 := map_derivedSeries_le_derivedSeries (f.comp J.subtype) n ⟨_, hmem, rfl⟩
    rwa [hn, Subgroup.mem_bot] at h2
  have h1' : (MulAut.conjNormal j : MulAut K) ∈ inner K := (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨k, hk⟩ := h1'
  have e : j = (k : Y) * ((k : Y)⁻¹ * j) := by group
  rw [e]
  exact Subgroup.mul_mem_sup k.2 (inv_mul_mem_centralizer_of_conjNormal_eq hk.symm)

theorem isCyclic_of_inf_eq_bot_of_le_sup {K Xt : Subgroup Y} [K.Normal]
    (hZ : Subgroup.center K = ⊥) (hX : IsPGroup p Xt) (hXK : Xt ⊓ K = ⊥)
    (hXle : Xt ≤ K ⊔ Subgroup.centralizer (K : Set Y))
    (hcyc : ∀ A : Subgroup Y, IsPGroup p A → A ≤ Subgroup.centralizer (K : Set Y) →
      IsCyclic A) : IsCyclic Xt := by
  set π := QuotientGroup.mk' K
  have hKC : ∀ y ∈ K, y ∈ Subgroup.centralizer (K : Set Y) → y = 1 := by
    intro y hyK hyC
    have hy : (⟨y, hyK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro k
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC k k.2)
    rw [hZ, Subgroup.mem_bot] at hy
    exact congrArg Subtype.val hy
  set A := Subgroup.centralizer (K : Set Y) ⊓ (Xt ⊔ K)
  have hAX : ∀ a ∈ A, ∃ x ∈ Xt, π a = π x := by
    intro a ha
    obtain ⟨x, hx, k, hk, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp ha.2
    have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    exact ⟨x, hx, by rw [map_mul, hk1, mul_one]⟩
  have hXA : ∀ x ∈ Xt, ∃ a ∈ A, π x = π a := by
    intro x hx
    obtain ⟨k, hk, c, hc, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp (hXle hx)
    have e : c = k⁻¹ * (k * c) := by group
    have hk1 : π k = 1 := (QuotientGroup.eq_one_iff k).mpr hk
    refine ⟨c, ⟨hc, ?_⟩, by rw [map_mul, hk1, one_mul]⟩
    rw [e]
    exact (Xt ⊔ K).mul_mem (Subgroup.mem_sup_right (K.inv_mem hk)) (Subgroup.mem_sup_left hx)
  have hA : IsPGroup p A := by
    intro a
    obtain ⟨x, hx, hax⟩ := hAX a a.2
    obtain ⟨n, hn⟩ := hX ⟨x, hx⟩
    have hxn : x ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine ⟨n, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    refine hKC _ ?_ ((Subgroup.centralizer (K : Set Y)).pow_mem a.2.1 _)
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_pow]
    change π a ^ p ^ n = 1
    rw [hax, ← map_pow, hxn, map_one]
  have : IsCyclic A := hcyc A hA inf_le_left
  have : IsCyclic (A.map π) := isCyclic_of_surjective _ (π.subgroupMap_surjective A)
  have hle : Xt.map π ≤ A.map π := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨a, ha, hxa⟩ := hXA x hx
    exact ⟨a, ha, hxa.symm⟩
  have : IsCyclic (Xt.map π) := Subgroup.isCyclic_of_le hle
  have hinj : Function.Injective (π.subgroupMap Xt) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (x : Y) = 1 := congrArg Subtype.val hx
    have h2 : (x : Y) ∈ Xt ⊓ K := ⟨x.2, (QuotientGroup.eq_one_iff _).mp h1⟩
    rw [hXK, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  let e := MulEquiv.ofBijective _ ⟨hinj, π.subgroupMap_surjective Xt⟩
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end Normal

section Reduced

open CFSG.ComponentClassification.OuterAutomorphisms

variable {Y : Type} [Group Y] [Finite Y] {p : ℕ} {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem ReducedNongeneration.le_of_rankOne_of_surjective (h : ReducedNongeneration p Y Rb Y₀)
    {L : Type} [Group L] [Finite L] (hL : IsSimpleGroup L) (hLnab : ∃ a b : L, a * b ≠ b * a)
    {Jt Xt : Subgroup Y} (φ : Jt →* L) (hφ : Function.Surjective φ)
    (hcop : p.Coprime (Nat.card φ.ker)) (hXR : Xt ≤ Rb) (hncl : nclIn Jt Xt = Jt)
    (hXJ : Xt ≤ Jt) (hXnc : ¬ IsCyclic Xt) {K : Subgroup Y} (hK : IsComponentOf K ⊤)
    (hZ : Subgroup.center K = ⊥) (hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ K : Subgroup Y))
    (hz : ∃ z ∈ (Rb : Subgroup Y), z ∉ K ∧ orderOf z = p ∧
      z ∈ Subgroup.centralizer (K : Set Y))
    (hout : Group.IsSolvable (Outer K)) : Jt ≤ K := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hKn : K.Normal := h.normal_of_rankOne hK hnc
  obtain ⟨z, hzR, hzK, hzp, hzc⟩ := hz
  have hKY₀ : ¬ K ≤ Y₀ := h.not_le_of_rankOne hK hnc hzR hzK hzp hzc
  have hX : IsPGroup p Xt := Rb.isPGroup'.to_le hXR
  have hJ : Group.IsPerfect Jt := isPerfect_of_nclIn_eq hL hLnab hX hncl φ hφ hcop
  rcases eq_top_or_le_ker_of_nclIn_eq hL hX hncl φ hφ hcop (K.subgroupOf Jt) with htop | hker
  · exact Subgroup.subgroupOf_eq_top.mp htop
  exfalso
  have hXK : Xt ⊓ K = ⊥ := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hX
    have hdisj : Disjoint (Xt.subgroupOf Jt) φ.ker := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXJ).toEquiv, hm]
      exact hcop.pow_left m
    rw [eq_bot_iff]
    intro y hy
    have h1 := Subgroup.disjoint_def.mp hdisj (x := ⟨y, hXJ hy.1⟩)
      (Subgroup.mem_subgroupOf.mpr hy.1) (hker (Subgroup.mem_subgroupOf.mpr hy.2))
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val h1)
  exact hXnc (isCyclic_of_inf_eq_bot_of_le_sup hZ hX hXK
    (hXJ.trans (le_sup_centralizer_of_isPerfect hJ hout))
    fun A hA hAC => h.isCyclic_of_le_centralizer hK hKY₀ hA hAC)

end Reduced

end CFSG.AGLEmbedding
