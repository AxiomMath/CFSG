module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.QuasithinUnique.Setup.Offender

open scoped commutatorElement

@[expose] def NoPQuotient (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ (N : Subgroup H) [N.Normal], IsPGroup p (H ⧸ N) → N = ⊤

@[expose] def CentralPChief (p : ℕ) (H : Type*) [Group H] : Prop :=
  ∀ K X : Subgroup H, CFSG.IsChiefFactor K X → (∃ n : ℕ, K.relIndex X = p ^ n) → ⁅X, ⊤⁆ ≤ K

theorem isPGroup_quotient_normalClosure_coprime {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y]
    [Finite Y] :
    IsPGroup p (Y ⧸ Subgroup.normalClosure {x : Y | Nat.Coprime (orderOf x) p}) := by
  have : Fact p.Prime := ⟨hp⟩
  intro g
  induction g using QuotientGroup.induction_on with | _ y =>
  obtain ⟨e, m, hm, hord⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y).ne' p hp.ne_one
  refine ⟨e, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  apply Subgroup.subset_normalClosure
  show Nat.Coprime (orderOf (y ^ p ^ e)) p
  rw [orderOf_pow' _ (pow_ne_zero e hp.ne_zero), hord]
  have : Nat.gcd (p ^ e * m) (p ^ e) = p ^ e := Nat.gcd_mul_right_left _ _
  rw [this, Nat.mul_div_cancel_left _ (pow_pos hp.pos e)]
  exact (Nat.Prime.coprime_iff_not_dvd hp).2 hm |>.symm

theorem coprime_commute_of_commutator_mem {p : ℕ} {Y : Type*} [Group Y]
    {x y : Y} (hx : Nat.Coprime (orderOf x) p) {M : Subgroup Y} (hMp : IsPGroup p M)
    (hcent : ∀ z ∈ M, x * z = z * x) (hc : ⁅x, y⁆ ∈ M) : x * y = y * x := by
  set c := ⁅x, y⁆ with hc_def
  have hxc : Commute x c := hcent c hc
  have hxy : x * y = c * y * x := by
    simp [hc_def, commutatorElement_def, mul_assoc]
  have hpow : ∀ j : ℕ, x ^ j * y = c ^ j * y * x ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ihj =>
      have h1 : x * c ^ j = c ^ j * x := (hxc.pow_right j).eq
      calc x ^ (j + 1) * y = x * (x ^ j * y) := by rw [pow_succ', mul_assoc]
        _ = x * (c ^ j * y * x ^ j) := by rw [ihj]
        _ = (x * c ^ j) * y * x ^ j := by simp only [mul_assoc]
        _ = c ^ j * (x * y) * x ^ j := by rw [h1]; simp only [mul_assoc]
        _ = c ^ j * (c * y * x) * x ^ j := by rw [hxy]
        _ = c ^ (j + 1) * y * x ^ (j + 1) := by rw [pow_succ, pow_succ']; simp only [mul_assoc]
  have hcm : c ^ orderOf x = 1 := by
    have := hpow (orderOf x)
    rw [pow_orderOf_eq_one, one_mul, mul_one] at this
    have h2 : c ^ orderOf x * y = 1 * y := by rw [one_mul]; exact this.symm
    exact mul_right_cancel h2
  obtain ⟨e, he⟩ := hMp ⟨c, hc⟩
  have hce : c ^ p ^ e = 1 := by simpa using congrArg Subtype.val he
  have hcop : Nat.Coprime (orderOf x) (p ^ e) := Nat.Coprime.pow_right e hx
  have hc1 : c = 1 := by
    have := (pow_gcd_eq_one (a := c)).2 ⟨hcm, hce⟩
    rwa [hcop, pow_one] at this
  rw [hc1, one_mul] at hxy
  exact hxy

theorem pCore_le_center_of_central_chief {p : ℕ} (hp : p.Prime) {Y : Type*} [Group Y] [Finite Y]
    (hno : NoPQuotient p Y) (hch : CentralPChief p Y) : CFSG.pCore p Y ≤ Subgroup.center Y := by
  have : Fact p.Prime := ⟨hp⟩
  set P := CFSG.pCore p Y with hP
  have hPn : P.Normal := CFSG.pCore_normal
  have hPp : IsPGroup p P := CFSG.pCore_isPGroup
  have key : ∀ n : ℕ, ∀ N : Subgroup Y, Nat.card N = n → N.Normal → N ≤ P →
      ∀ x : Y, Nat.Coprime (orderOf x) p → ∀ y ∈ N, x * y = y * x := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro N hn hNn hNP x hx y hy
    by_cases hbot : N = ⊥
    · subst hbot
      have : y = 1 := by simpa using hy
      subst this
      simp
    · have hne : Nonempty {M : Subgroup Y // M.Normal ∧ M < N} :=
        ⟨⟨⊥, inferInstance, bot_lt_iff_ne_bot.2 hbot⟩⟩
      obtain ⟨⟨M, hMn, hMlt⟩, hMmax⟩ := Finite.exists_max
        (fun M : {M : Subgroup Y // M.Normal ∧ M < N} => Nat.card M.1)
      have hcard : Nat.card M < n := by
        rw [← hn]; exact Subgroup.card_lt_of_lt hMlt
      have hMP : M ≤ P := hMlt.le.trans hNP
      have hcent := ih _ hcard M rfl hMn hMP x hx
      have hchief : CFSG.IsChiefFactor M N := by
        refine ⟨hMn, hNn, hMlt, fun Q hQ hMQ hQN => ?_⟩
        by_cases hQN' : Q = N
        · exact Or.inr hQN'
        · left
          have hQlt : Q < N := lt_of_le_of_ne hQN hQN'
          have := hMmax ⟨Q, hQ, hQlt⟩
          exact (Subgroup.eq_of_le_of_card_ge hMQ this).symm
      have hNp : IsPGroup p N := hPp.of_injective (Subgroup.inclusion hNP)
        (Subgroup.inclusion_injective hNP)
      have hMp : IsPGroup p M := hPp.of_injective (Subgroup.inclusion hMP)
        (Subgroup.inclusion_injective hMP)
      have hidx : ∃ e : ℕ, M.relIndex N = p ^ e := hNp.index (M.subgroupOf N)
      have hcomm : ⁅N, ⊤⁆ ≤ M := hch M N hchief hidx
      have hc : ⁅x, y⁆ ∈ M := by
        have h1 : ⁅y, x⁆ ∈ ⁅N, ⊤⁆ := Subgroup.commutator_mem_commutator hy (Subgroup.mem_top x)
        have h2 := M.inv_mem (hcomm h1)
        rwa [commutatorElement_inv] at h2
      exact coprime_commute_of_commutator_mem hx hMp hcent hc
  set D := Subgroup.normalClosure {x : Y | Nat.Coprime (orderOf x) p} with hD
  have hDtop : D = ⊤ := hno D (isPGroup_quotient_normalClosure_coprime hp)
  have hDle : D ≤ Subgroup.centralizer (P : Set Y) := by
    have hcn : (Subgroup.centralizer (P : Set Y)).Normal := ⟨fun x hx g => by
      rw [Subgroup.mem_centralizer_iff] at hx ⊢
      intro q hq
      have h1 : g⁻¹ * q * g ∈ P := by simpa using hPn.conj_mem q hq g⁻¹
      have h2 := hx _ h1
      calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [h2]
        _ = g * x * g⁻¹ * q := by group⟩
    refine Subgroup.normalClosure_le_normal (fun x hx q hq => ?_)
    exact (key _ P rfl hPn le_rfl x hx q hq).symm
  intro q hq
  rw [Subgroup.mem_center_iff]
  intro y
  have : y ∈ D := by rw [hDtop]; trivial
  exact (hDle this q hq).symm

theorem noPQuotient_of_surjective {p : ℕ} {H H' : Type*} [Group H] [Group H'] (φ : H →* H')
    (hφ : Function.Surjective φ) (h : NoPQuotient p H) : NoPQuotient p H' := by
  intro N' _ hpg
  have hpg' : IsPGroup p (H ⧸ N'.comap φ) := by
    intro g
    induction g using QuotientGroup.induction_on with | _ x =>
    obtain ⟨n, hn⟩ := hpg (φ x)
    refine ⟨n, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at hn
    simpa using hn
  have htop := h (N'.comap φ) hpg'
  rw [eq_top_iff]
  intro y _
  obtain ⟨x, rfl⟩ := hφ y
  have : x ∈ N'.comap φ := by rw [htop]; trivial
  exact this

theorem centralPChief_of_surjective {p : ℕ} {H H' : Type*} [Group H] [Group H'] (φ : H →* H')
    (hφ : Function.Surjective φ) (h : CentralPChief p H) : CentralPChief p H' := by
  intro K' X' hc hpow
  have hKn := hc.normal_K
  have hXn := hc.normal_H
  have hK : (K'.comap φ).Normal := inferInstance
  have hX : (X'.comap φ).Normal := inferInstance
  have hchief : CFSG.IsChiefFactor (K'.comap φ) (X'.comap φ) := by
    refine ⟨hK, hX, ?_, fun Q hQ hKQ hQX => ?_⟩
    · exact (Subgroup.comap_lt_comap_of_surjective hφ).2 hc.lt
    · have hQm : (Q.map φ).Normal := hQ.map φ hφ
      have hker : φ.ker ≤ Q := le_trans (by
        intro x hx
        show φ x ∈ K'
        rw [MonoidHom.mem_ker.1 hx]; exact K'.one_mem) hKQ
      have h1 : K' ≤ Q.map φ := by
        calc K' = (K'.comap φ).map φ := (Subgroup.map_comap_eq_self_of_surjective hφ K').symm
          _ ≤ Q.map φ := Subgroup.map_mono hKQ
      have h2 : Q.map φ ≤ X' := by
        calc Q.map φ ≤ (X'.comap φ).map φ := Subgroup.map_mono hQX
          _ = X' := Subgroup.map_comap_eq_self_of_surjective hφ X'
      have hQeq : Q = (Q.map φ).comap φ := by
        rw [Subgroup.comap_map_eq, sup_eq_left.2 hker]
      rcases hc.is_maximal (Q.map φ) hQm h1 h2 with h3 | h3
      · left; rw [hQeq, h3]
      · right; rw [hQeq, h3]
  have hidx : (K'.comap φ).relIndex (X'.comap φ) = K'.relIndex X' := by
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hφ]
  have := h _ _ hchief ⟨hpow.choose, by rw [hidx]; exact hpow.choose_spec⟩
  have h4 := Subgroup.map_mono (f := φ) this
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hφ,
    Subgroup.map_top_of_surjective φ hφ, Subgroup.map_comap_eq_self_of_surjective hφ] at h4
  exact h4

theorem noPQuotient_of_perfect {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    (hH : Group.IsPerfect H) : NoPQuotient p H := by
  have : Fact p.Prime := ⟨hp⟩
  intro N _ hpg
  have hQ : Group.IsPerfect (H ⧸ N) := by
    rw [Group.isPerfect_def, commutator_def]
    have h1 := Subgroup.map_commutator (⊤ : Subgroup H) (⊤ : Subgroup H) (QuotientGroup.mk' N)
    rw [← commutator_def, hH.commutator_eq_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)] at h1
    exact h1.symm
  have hnil : Group.IsNilpotent (H ⧸ N) := hpg.isNilpotent
  by_contra hne
  have hnt : Nontrivial (H ⧸ N) := QuotientGroup.nontrivial_iff.2 hne
  have := Group.IsSolvable.commutator_lt_top_of_nontrivial (H ⧸ N)
  exact absurd hQ.commutator_eq_top this.ne

theorem isPerfect_of_quasisimple_iSup {H : Type*} [Group H] {ι : Type*} (L : ι → Subgroup H)
    (hq : ∀ i, CFSG.IsQuasisimple (L i)) (hgen : ⨆ i, L i = ⊤) : Group.IsPerfect H := by
  rw [Group.isPerfect_def, commutator_def, eq_top_iff, ← hgen]
  refine iSup_le fun i => ?_
  have h1 : ⁅L i, L i⁆ = L i := Subgroup.isPerfect_iff.mp (hq i).1
  exact h1.symm.le.trans (Subgroup.commutator_mono (le_iSup L i) (le_iSup L i))

theorem normal_of_commuting {H : Type*} [Group H] {ι : Type*} (L : ι → Subgroup H)
    (hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥) (hgen : ⨆ i, L i = ⊤) (i : ι) : (L i).Normal := by
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen]
  refine iSup_le fun j => ?_
  by_cases hij : j = i
  · subst hij; exact Subgroup.le_normalizer
  · have : ⁅L j, L i⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact hcomm i j (Ne.symm hij)
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 this).trans
      (Subgroup.centralizer_le_normalizer _)

theorem commutator_eq_bot_of_quasisimple {G : Type*} [Group G] {R X : Subgroup G} [R.Normal]
    [X.Normal] (hR : CFSG.IsQuasisimple R) (hX : ⁅X, X⁆ = ⊥) : ⁅R, X⁆ = ⊥ := by
  have hN : (X.subgroupOf R).Normal := inferInstance
  have hnt : Nontrivial R := CFSG.LocalCores.isQuasisimple_nontrivial hR
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hR hN with htop | hcen
  · exfalso
    have hRX : R ≤ X := by
      intro r hr
      have : (⟨r, hr⟩ : R) ∈ X.subgroupOf R := by rw [htop]; trivial
      exact this
    have hRR : ⁅R, R⁆ = ⊥ := le_bot_iff.1 (hX ▸ Subgroup.commutator_mono hRX hRX)
    have hperf : ⁅R, R⁆ = R := Subgroup.isPerfect_iff.mp hR.1
    have : (R : Subgroup G) = ⊥ := by rw [← hperf, hRR]
    exact (Subgroup.nontrivial_iff_ne_bot R).1 hnt this
  · have hinf : ⁅R, X⁆ ≤ R ⊓ X := Subgroup.commutator_le_inf R X
    have hcomm : ⁅R ⊓ X, R⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro r' hr'
      have hc := hcen (show (⟨r, hr.1⟩ : R) ∈ X.subgroupOf R from hr.2)
      rw [Subgroup.mem_center_iff] at hc
      have := hc ⟨r', hr'⟩
      exact congrArg Subtype.val this
    have h2 : ⁅⁅R, X⁆, R⁆ = ⊥ :=
      le_bot_iff.1 (hcomm ▸ Subgroup.commutator_mono hinf le_rfl)
    exact CFSG.LocalCores.perfect_double_commutator hR.1 h2

theorem commutator_le_of_abelian_section {H : Type*} [Group H] {ι : Type*} (L : ι → Subgroup H)
    (hq : ∀ i, CFSG.IsQuasisimple (L i)) (hn : ∀ i, (L i).Normal) (hgen : ⨆ i, L i = ⊤)
    {X Y : Subgroup H} [X.Normal] [Y.Normal] (hab : ⁅X, X⁆ ≤ Y) : ⁅X, ⊤⁆ ≤ Y := by
  set π := QuotientGroup.mk' Y with hπ
  have hXb : ⁅X.map π, X.map π⁆ = ⊥ := by
    rw [← Subgroup.map_commutator]
    have := Subgroup.map_mono (f := π) hab
    rw [show Y.map π = ⊥ by rw [hπ, QuotientGroup.map_mk'_self]] at this
    exact le_bot_iff.1 this
  have hXn : (X.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Y)
  have hLi : ∀ i, (L i).map π ≤ Subgroup.centralizer (X.map π : Set (H ⧸ Y)) := by
    intro i
    have := hn i
    have hRn : ((L i).map π).Normal :=
      Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective Y)
    have hR : (π.comp (L i).subtype).range = (L i).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images (hq i)
      (π.comp (L i).subtype) with h | h
    · rw [hR] at h
      rw [h]; exact Subgroup.commutator_bot_left _
    · rw [hR] at h
      exact commutator_eq_bot_of_quasisimple h hXb
  have hall : ⨆ i, (L i).map π ≤ Subgroup.centralizer (X.map π : Set (H ⧸ Y)) := iSup_le hLi
  rw [← Subgroup.map_iSup, hgen,
    Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Y)] at hall
  rw [Subgroup.commutator_le]
  intro x hx h _
  have h1 : π h ∈ Subgroup.centralizer (X.map π : Set (H ⧸ Y)) := hall (Subgroup.mem_top _)
  rw [Subgroup.mem_centralizer_iff] at h1
  have h2 := h1 (π x) (Subgroup.mem_map_of_mem π hx)
  have h3 : π ⁅x, h⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def, h2]; group
  rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3

theorem commutator_le_of_chiefFactor {p : ℕ} (hp : p.Prime) {H : Type*} [Group H] [Finite H]
    {X Y : Subgroup H} (hc : CFSG.IsChiefFactor Y X) (hpow : ∃ n : ℕ, Y.relIndex X = p ^ n) :
    ⁅X, X⁆ ≤ Y := by
  have : Fact p.Prime := ⟨hp⟩
  have hYn := hc.normal_K
  have hXn := hc.normal_H
  obtain ⟨n, hn⟩ := hpow
  have hmin := CFSG.chiefFactor_quotient_minimal (⟨Y, X, hc⟩ : CFSG.ChiefFactor H)
  obtain ⟨hUn, hUbot, hUmin⟩ := hmin
  set π : H →* H ⧸ Y := QuotientGroup.mk' Y with hπ
  set U : Subgroup (H ⧸ Y) := X.map π with hU
  have hcard : Nat.card U = p ^ n := by
    have h1 := Subgroup.relIndex_ker π (K := X)
    rw [hπ, QuotientGroup.ker_mk'] at h1
    rw [← hn, h1]
  have hUp : IsPGroup p U := IsPGroup.of_card hcard
  have hUnt : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).2 hUbot
  have hcn : Nontrivial (Subgroup.center U) := hUp.center_nontrivial
  set Z : Subgroup (H ⧸ Y) := (Subgroup.center U).map U.subtype with hZ
  have hZn : Z.Normal := ⟨fun z hz g => by
    obtain ⟨z', hz', rfl⟩ := hz
    have hgz : g * (z' : H ⧸ Y) * g⁻¹ ∈ U := hUn.conj_mem _ z'.2 g
    refine ⟨⟨_, hgz⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have hu : g⁻¹ * (u : H ⧸ Y) * g ∈ U := by simpa using hUn.conj_mem _ u.2 g⁻¹
    have hzc := Subgroup.mem_center_iff.1 hz' ⟨_, hu⟩
    have := congrArg Subtype.val hzc
    simp only [Subgroup.coe_mul] at this ⊢
    calc (u : H ⧸ Y) * (g * z' * g⁻¹) = g * ((g⁻¹ * u * g) * z') * g⁻¹ := by group
      _ = g * (z' * (g⁻¹ * u * g)) * g⁻¹ := by rw [this]
      _ = g * z' * g⁻¹ * u := by group⟩
  have hZle : Z ≤ U := by
    rintro _ ⟨z', _, rfl⟩; exact z'.2
  have hZbot : Z ≠ ⊥ := by
    obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center U)
    intro hbot
    apply hz
    have : (z : U) ∈ (Subgroup.center U) := z.2
    have h1 : ((z : U) : H ⧸ Y) ∈ Z := ⟨z, z.2, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hZU : Z = U := hUmin Z hZn hZle hZbot
  have hUab : ⁅U, U⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu v hv
    have : (⟨v, hv⟩ : U) ∈ Subgroup.center U := by
      have : v ∈ Z := hZU ▸ hv
      obtain ⟨z', hz', hzv⟩ := this
      have : z' = ⟨v, hv⟩ := Subtype.ext hzv
      exact this ▸ hz'
    have h2 := Subgroup.mem_center_iff.1 this ⟨u, hu⟩
    exact (congrArg Subtype.val h2).symm
  have h3 : (⁅X, X⁆).map π = ⊥ := by rw [Subgroup.map_commutator]; exact hUab
  have h4 := (Subgroup.map_eq_bot_iff _).1 h3
  rwa [hπ, QuotientGroup.ker_mk'] at h4

theorem closure_commutators_eq_top {H : Type*} [Group H] {ι : Type*} (L : ι → Subgroup H)
    (hgen : ⨆ i, L i = ⊤) (hperf : Group.IsPerfect H)
    {i j : ι} (hcomm : ⁅L i, L j⁆ = ⊥)
    (A : Subgroup (MulAut H)) (htrans : ∀ i j, ∃ a ∈ A, (L i).map a.toMonoidHom = L j) :
    Subgroup.closure {x : H | ∃ h : H, ∃ a ∈ A, x = h⁻¹ * a h} = ⊤ := by
  set S : Set H := {x : H | ∃ h : H, ∃ a ∈ A, x = h⁻¹ * a h} with hS
  set D := Subgroup.closure S with hD
  have hconj : ∀ x ∈ D, ∀ g : H, g⁻¹ * x * g ∈ D := by
    intro x hx g
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, a, ha, rfl⟩ := hx
      have h1 : (h * g)⁻¹ * a (h * g) ∈ D := Subgroup.subset_closure ⟨h * g, a, ha, rfl⟩
      have h2 : g⁻¹ * a g ∈ D := Subgroup.subset_closure ⟨g, a, ha, rfl⟩
      have := D.mul_mem h1 (D.inv_mem h2)
      convert this using 1
      simp [map_mul]; group
    | one => simp
    | mul x y _ _ hx hy => simpa [mul_assoc] using D.mul_mem hx hy
    | inv x _ hx => simpa [mul_assoc] using D.inv_mem hx
  have hDn : D.Normal := ⟨fun x hx g => by simpa using hconj x hx g⁻¹⟩
  set π := QuotientGroup.mk' D with hπ
  have hπa : ∀ a ∈ A, ∀ h : H, π h = π (a h) := by
    intro a ha h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    exact Subgroup.subset_closure ⟨h, a, ha, rfl⟩
  have hπcomp : ∀ a ∈ A, π.comp a.toMonoidHom = π :=
    fun a ha => MonoidHom.ext fun h => (hπa a ha h).symm
  have hR : ∀ k, (L k).map π = (L i).map π := by
    intro k
    obtain ⟨a, ha, hLa⟩ := htrans i k
    rw [← hLa, Subgroup.map_map, hπcomp a ha]
  have htop : (⊤ : Subgroup (H ⧸ D)) = (L i).map π := by
    rw [← Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective D), ← hgen,
      Subgroup.map_iSup]
    exact le_antisymm (iSup_le fun k => (hR k).le) (le_iSup (fun k => (L k).map π) i)
  have hcomm' : ⁅(L i).map π, (L i).map π⁆ = ⊥ := by
    have h1 : ⁅(L i).map π, (L j).map π⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
    rwa [hR j] at h1
  by_contra hne
  have hnt : Nontrivial (H ⧸ D) := QuotientGroup.nontrivial_iff.2 hne
  have hperf' : Group.IsPerfect (H ⧸ D) := by
    rw [Group.isPerfect_def, commutator_def]
    have h1 := Subgroup.map_commutator (⊤ : Subgroup H) (⊤ : Subgroup H) π
    rw [← commutator_def, hperf.commutator_eq_top,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective D)] at h1
    exact h1.symm
  have h2 := hperf'.commutator_eq_top
  have h3 : ⁅(⊤ : Subgroup (H ⧸ D)), (⊤ : Subgroup (H ⧸ D))⁆ = ⊥ := by rw [htop]; exact hcomm'
  rw [commutator_def, h3] at h2
  exact (Subgroup.nontrivial_iff_ne_bot (⊤ : Subgroup (H ⧸ D))).1 inferInstance h2.symm

theorem quasisimple_product {H : Type*} [Group H] [Finite H] {s : ℕ} (L : Fin s → Subgroup H)
    (hq : ∀ i, CFSG.IsQuasisimple (L i)) (hcomm : ∀ i j, i ≠ j → ⁅L i, L j⁆ = ⊥)
    (hgen : ⨆ i, L i = ⊤) :
    Group.IsPerfect H ∧ (∀ p : ℕ, p.Prime → NoPQuotient p H) ∧
    (∀ (X Y : Subgroup H) [X.Normal] [Y.Normal], Y ≤ X → ⁅X, X⁆ ≤ Y → ⁅X, ⊤⁆ ≤ Y) ∧
    (∀ p : ℕ, p.Prime → CentralPChief p H) ∧
    (2 ≤ s → Function.Injective L → ∀ A : Subgroup (MulAut H),
      (∀ a ∈ A, ∀ i, ∃ j, (L i).map a.toMonoidHom = L j) →
      (∀ i j, ∃ a ∈ A, (L i).map a.toMonoidHom = L j) →
        Subgroup.closure {x : H | ∃ h : H, ∃ a ∈ A, x = h⁻¹ * a h} = ⊤) := by
  have hperf : Group.IsPerfect H := isPerfect_of_quasisimple_iSup L hq hgen
  have hn : ∀ i, (L i).Normal := normal_of_commuting L hcomm hgen
  have h3 : ∀ (X Y : Subgroup H) [X.Normal] [Y.Normal], Y ≤ X → ⁅X, X⁆ ≤ Y → ⁅X, ⊤⁆ ≤ Y :=
    fun X Y _ _ _ hab => commutator_le_of_abelian_section L hq hn hgen hab
  refine ⟨hperf, fun p hp => noPQuotient_of_perfect hp hperf, h3, fun p hp K X hc hpow => ?_,
    fun h2 _ A _ htrans => ?_⟩
  · have := hc.normal_K
    have := hc.normal_H
    exact h3 X K hc.lt.le (commutator_le_of_chiefFactor hp hc hpow)
  · exact closure_commutators_eq_top L hgen hperf
      (hcomm ⟨0, by omega⟩ ⟨1, by omega⟩ (by simp [Fin.ext_iff])) A htrans

end CFSG.QuasithinUnique.Setup.Offender
