module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop121

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims121

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped commutatorElement

section Input2027

variable {G : Type} [Group G]

theorem card_map_mk_of_coprime [Finite G] {J E : Subgroup G} (N : Subgroup ↥J) [N.Normal]
    (hEJ : E ≤ J) (hcop : Nat.Coprime (Nat.card E) (Nat.card N)) :
    Nat.card ((E.subgroupOf J).map (QuotientGroup.mk' N)) = Nat.card E := by
  have hEc : Nat.card (E.subgroupOf J) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEJ).toEquiv
  have hcop' : Nat.Coprime (Nat.card (E.subgroupOf J)) (Nat.card N) := by rwa [hEc]
  have hdisj := Subgroup.disjoint_of_coprime_natCard hcop'
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp (E.subgroupOf J).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have h1 : (s : ↥J) ∈ E.subgroupOf J ⊓ N := ⟨s.2, hs⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
    exact (Subgroup.mem_bot).2 (Subtype.ext h1)
  have hrange : (E.subgroupOf J).map (QuotientGroup.mk' N) =
      ((QuotientGroup.mk' N).comp (E.subgroupOf J).subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange, ← hEc]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem input2027L34_holds : Prop121.Input2027L34 := by
  intro G _ _ J B T hJ hBJ hB hBc hTJ hT hBT
  set N : Subgroup ↥J := CFSG.pCore 2 ↥J with hN
  haveI : N.Normal := CFSG.pCore_normal
  set π : ↥J →* ↥J ⧸ N := QuotientGroup.mk' N with hπ
  have hTb : IsPGroup 2 ((T.subgroupOf J).map π) := (hT.comap_subtype).map π
  have hBb : IsElemAbelian 3 ((B.subgroupOf J).map π) :=
    CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hB J) π
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have hcop : Nat.Coprime (Nat.card B) (Nat.card N) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := hN2.exists_card_eq
    rw [hBc, hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have hBbc : Nat.card ((B.subgroupOf J).map π) = 9 := by
    rw [card_map_mk_of_coprime N hBJ hcop, hBc]
  have hBTb : (B.subgroupOf J).map π ≤
      Subgroup.normalizer (((T.subgroupOf J).map π : Subgroup (↥J ⧸ N)) : Set (↥J ⧸ N)) := by
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map π)
    rw [normalizer_subgroupOf_eq hTJ]
    intro x hx
    exact (Subgroup.mem_subgroupOf).2 (hBT ((Subgroup.mem_subgroupOf).1 hx))
  have hbot := CFSG.HardMathSupport.Solomon.UniquenessMaximal.eq_bot_of_two_group_normalized_by_nine
    hJ hBb hBbc hTb hBTb
  intro t ht
  have hmem : π ⟨t, hTJ ht⟩ ∈ (T.subgroupOf J).map π :=
    Subgroup.mem_map_of_mem π ((Subgroup.mem_subgroupOf).2 ht)
  rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨⟨t, hTJ ht⟩, hmem, rfl⟩

end Input2027

section Mod

theorem inv_mul_mem_of_commutator_mem {H : Type*} [Group H] {N : Subgroup H} [N.Normal] {x y : H}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hxy : x * y * x⁻¹ * y⁻¹ ∈ N) {k : ℕ}
    (hs : (x⁻¹ * y) ^ (2 ^ k) = 1) : x⁻¹ * y ∈ N := by
  have h1 : ((x * y * x⁻¹ * y⁻¹ : H) : H ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).2 hxy
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
  have hac : Commute (x : H ⧸ N) (y : H ⧸ N) := by
    show (x : H ⧸ N) * y = y * x
    calc (x : H ⧸ N) * y = ((x : H ⧸ N) * y * (x : H ⧸ N)⁻¹ * (y : H ⧸ N)⁻¹) * (y * x) := by
          group
      _ = y * x := by rw [h1, one_mul]
  have h3 : ((x : H ⧸ N)⁻¹ * y) ^ 3 = 1 := by
    rw [(hac.inv_left).mul_pow, inv_pow, ← QuotientGroup.mk_pow, hx, ← QuotientGroup.mk_pow, hy]
    simp
  have h2 : ((x : H ⧸ N)⁻¹ * y) ^ (2 ^ k) = 1 := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_pow, hs]
    rfl
  have hord : orderOf ((x : H ⧸ N)⁻¹ * y) = 1 := by
    have hg : Nat.gcd 3 (2 ^ k) = 1 := Nat.Coprime.pow_right k (by norm_num)
    have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [hg] at hd
    exact Nat.dvd_one.1 hd
  rw [orderOf_eq_one_iff, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul] at hord
  exact (QuotientGroup.eq_one_iff _).1 hord

theorem commutator_mem_of_inv_mul_mem {H : Type*} [Group H] {N : Subgroup H} [N.Normal]
    {x y j : H} (hxy : x⁻¹ * y ∈ N) (hyj : y * j * y⁻¹ * j⁻¹ ∈ N) :
    x * j * x⁻¹ * j⁻¹ ∈ N := by
  have h1 : (x : H ⧸ N) = (y : H ⧸ N) := QuotientGroup.eq.2 hxy
  rw [← QuotientGroup.eq_one_iff] at hyj ⊢
  simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at hyj ⊢
  rw [h1]
  exact hyj

end Mod

section Core

variable {G : Type} [Group G]

theorem eq_one_of_pow_three_of_coprime [Finite G] {O : Subgroup G}
    (hO : Nat.Coprime 3 (Nat.card O)) {b : G} (hbO : b ∈ O) (hb3 : b ^ 3 = 1) : b = 1 := by
  have h1 : orderOf (⟨b, hbO⟩ : O) ∣ 3 := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simp [hb3]))
  have h2 : orderOf (⟨b, hbO⟩ : O) ∣ Nat.card O := orderOf_dvd_natCard _
  have hd := Nat.dvd_gcd h1 h2
  rw [hO] at hd
  have := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  simpa using congrArg Subtype.val this

theorem coprime_three_of_isPGroup_two {H : Type*} [Group H] [Finite H] {T : Subgroup H}
    (hT : IsPGroup 2 T) :
    Nat.Coprime 3 (Nat.card T) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hT.exists_card_eq
  rw [hk]
  exact Nat.Coprime.pow_right k (by norm_num)

theorem center_eq_bot_of_simple {Q : Type*} [Group Q] (hs : IsSimpleGroup Q)
    (hna : ∃ a b : Q, a * b ≠ b * a) : Subgroup.center Q = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Q) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center Q := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.1 ha) b).symm

theorem eq_one_of_commutator_mem [Finite G] {X J : Subgroup G} (hJX : J ≤ X)
    (hJ : IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J)) {b : G} (hbJ : b ∈ J) (hb3 : b ^ 3 = 1)
    (hc : ∀ j ∈ J, b * j * b⁻¹ * j⁻¹ ∈ pCoreOf 2 X) : b = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup ↥J := GLAPPrimeCore 3 ↥J with hOdef
  have hY : (pCoreOf 2 X).subgroupOf J ≤ O := by
    refine CFSG.le_pPrimeCore_of_normal_coprime ?_ ?_
    · refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 X (hJX g.2)) n).1 hn
      simpa using this
    · exact coprime_three_of_isPGroup_two
        ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_subtype)
  obtain ⟨hsimple, hna⟩ :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hJ
  have hcen : (QuotientGroup.mk' O ⟨b, hbJ⟩) ∈ Subgroup.center (↥J ⧸ O) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨j, rfl⟩ := QuotientGroup.mk_surjective q
    have hmem : (⟨b, hbJ⟩ * j * (⟨b, hbJ⟩ : ↥J)⁻¹ * j⁻¹ : ↥J) ∈ O :=
      hY (by simpa [Subgroup.mem_subgroupOf] using hc j j.2)
    have h1 := (QuotientGroup.eq_one_iff _).2 hmem
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] at h1
    rw [QuotientGroup.mk'_apply]
    calc (j : ↥J ⧸ O) * (⟨b, hbJ⟩ : ↥J) =
        ((⟨b, hbJ⟩ : ↥J) * (j : ↥J ⧸ O) * ((⟨b, hbJ⟩ : ↥J) : ↥J ⧸ O)⁻¹ * (j : ↥J ⧸ O)⁻¹)⁻¹ *
          ((⟨b, hbJ⟩ : ↥J) * (j : ↥J ⧸ O)) := by group
      _ = ((⟨b, hbJ⟩ : ↥J) : ↥J ⧸ O) * (j : ↥J ⧸ O) := by rw [h1, inv_one, one_mul]
  rw [center_eq_bot_of_simple hsimple hna, Subgroup.mem_bot, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hcen
  have hb : (⟨b, hbJ⟩ : ↥J) = 1 :=
    eq_one_of_pow_three_of_coprime CFSG.pPrimeCore_coprime_card hcen
      (Subtype.ext (by simp [hb3]))
  simpa using congrArg Subtype.val hb

theorem isTwoPrimeComponent_of_comp {X J : Subgroup G} (h : IsTwoPrimeComp X J) :
    CFSG.AGLEmbedding.IsTwoPrimeComponent X J :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩

theorem exists_ne_one_of_card_nine {E : Subgroup G} (hE : Nat.card E = 9) : ∃ b ∈ E, b ≠ 1 := by
  by_contra hno
  push Not at hno
  have : E = ⊥ := (Subgroup.eq_bot_iff_forall _).2 hno
  rw [this, Subgroup.card_bot] at hE
  norm_num at hE

theorem eq_of_le_twoPrimeComp [Finite G] {X J Js Js' : Subgroup G} (hJX : J ≤ X)
    (hJ : IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J)) (hJs : IsTwoPrimeComp X Js)
    (hJs' : IsTwoPrimeComp X Js') (hJJs : J ≤ Js) (hJJs' : J ≤ Js') {b : G} (hbJ : b ∈ J)
    (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1) : Js = Js' := by
  by_contra hne
  have hc :=
    (isTwoPrimeComponent_of_comp hJs).commutator_le (isTwoPrimeComponent_of_comp hJs') hne
  exact hb1 (eq_one_of_commutator_mem hJX hJ hbJ hb3 fun j hj => by
    have := hc (Subgroup.commutator_mem_commutator (hJJs hbJ) (hJJs' hj))
    simpa [commutatorElement_def] using this)

end Core

section Norm

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_twoPrimeComp {X J Js P : Subgroup G} (hJX : J ≤ X)
    (hJ : IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J)) (hJs : IsTwoPrimeComp X Js) (hJJs : J ≤ Js)
    (hPX : P ≤ X) (hP : IsPGroup 2 P) {b : G} (hbJ : b ∈ J) (hb1 : b ≠ 1) (hb3 : b ^ 3 = 1)
    (hbP : b ∈ Subgroup.normalizer (P : Set G)) : P ≤ Subgroup.normalizer (Js : Set G) := by
  have hJsX := isTwoPrimeComponent_of_comp hJs
  intro u hu
  by_contra hnot
  set L' : Subgroup G := Js.map (MulAut.conj u).toMonoidHom with hL'def
  have hL' : CFSG.AGLEmbedding.IsTwoPrimeComponent X L' := hJsX.map_conj (hPX hu)
  have hne : Js ≠ L' := fun he => hnot (Subgroup.mem_normalizer_iff_map_conj_eq.2 he.symm)
  have hcomm := hJsX.commutator_le hL' hne
  have hbX : b ∈ X := hJX hbJ
  have hb'L : u * b * u⁻¹ ∈ L' := ⟨b, hJJs hbJ, by simp [MulAut.conj_apply]⟩
  have hb'X : u * b * u⁻¹ ∈ X := X.mul_mem (X.mul_mem (hPX hu) hbX) (X.inv_mem (hPX hu))
  have hw : b⁻¹ * (u * b * u⁻¹) ∈ P := by
    have h1 : b⁻¹ * u * b⁻¹⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hbP) u).1 hu
    have h2 : b⁻¹ * (u * b * u⁻¹) = (b⁻¹ * u * b⁻¹⁻¹) * u⁻¹ := by group
    rw [h2]
    exact P.mul_mem h1 (P.inv_mem hu)
  obtain ⟨k, hk⟩ := hP ⟨_, hw⟩
  set N : Subgroup ↥X := CFSG.pCore 2 ↥X with hNdef
  haveI : N.Normal := CFSG.pCore_normal
  have memN : ∀ z : ↥X, (z : G) ∈ pCoreOf 2 X → z ∈ N := by
    rintro z ⟨z', hz', hzz⟩
    rwa [show z = z' from Subtype.ext hzz.symm]
  set x : ↥X := ⟨b, hbX⟩
  set y : ↥X := ⟨u * b * u⁻¹, hb'X⟩
  have hx : x ^ 3 = 1 := Subtype.ext (by simp [x, hb3])
  have hy : y ^ 3 = 1 := Subtype.ext (by simp [y, conj_pow, hb3])
  have hxy : x * y * x⁻¹ * y⁻¹ ∈ N := by
    apply memN
    have := hcomm (Subgroup.commutator_mem_commutator (hJJs hbJ) hb'L)
    simpa [x, y, commutatorElement_def] using this
  have hs : (x⁻¹ * y) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    simpa [x, y] using congrArg Subtype.val hk
  have hxyN := inv_mul_mem_of_commutator_mem hx hy hxy hs
  exact hb1 (eq_one_of_commutator_mem hJX hJ hbJ hb3 fun j hj => by
    have hjX : j ∈ X := hJX hj
    have hyj : y * ⟨j, hjX⟩ * y⁻¹ * (⟨j, hjX⟩ : ↥X)⁻¹ ∈ N := by
      apply memN
      have h1 := hcomm (Subgroup.commutator_mem_commutator (hJJs hj) hb'L)
      have h2 : (u * b * u⁻¹) * j * (u * b * u⁻¹)⁻¹ * j⁻¹ = (⁅j, u * b * u⁻¹⁆)⁻¹ := by
        rw [commutatorElement_def]; group
      simp only [y, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h2]
      exact (pCoreOf 2 X).inv_mem h1
    exact ⟨_, commutator_mem_of_inv_mul_mem hxyN hyj, rfl⟩)

end Norm

open Prop121 in
theorem printedOJNorm_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement) :
    PrintedOJNorm := by
  intro G _ _ m p B M E A a h K hK hK3 hKM hu₀ hA0 Js hJs hJJs
  have hPW := Sec12b.core_le_W_of_inputs h123 h124 h hK hK3 hKM hu₀ hA0
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  obtain ⟨⟨-, -, -, -, hcard, -, -⟩, -, ⟨hJL3, -⟩, -⟩ := h124 h hK hK3 hKM hu₀ hA0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  have hcard' : Nat.card ↥(A ⊓ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G))) = 9 :=
    hcard
  obtain ⟨b, hbB, hb1⟩ := exists_ne_one_of_card_nine hcard'
  have hbA : b ∈ A := hbB.1
  exact le_normalizer_of_twoPrimeComp le_sup_left hJL3 hJs hJJs (hPW.trans le_sup_right)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hbB.2 hb1 (hAel.2 b hbA)
    (le_normalizer_pCoreOf 2 M (hAM hbA))

section Constrained

variable {G : Type} [Group G]

theorem isPGroup_zpowers_of_pow_eq_one {p : ℕ} {g : G} (hg : g ^ p = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  rintro ⟨y, hy⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  refine ⟨1, Subtype.ext ?_⟩
  have h1 : (g ^ n) ^ p = 1 := by
    calc (g ^ n) ^ p = (g ^ n) ^ (p : ℤ) := (zpow_natCast _ _).symm
      _ = g ^ (n * (p : ℤ)) := (zpow_mul _ _ _).symm
      _ = g ^ ((p : ℤ) * n) := by rw [mul_comm]
      _ = (g ^ (p : ℤ)) ^ n := zpow_mul _ _ _
      _ = 1 := by rw [zpow_natCast, hg, one_zpow]
  simpa using h1

theorem eq_closure_of_isElemAbelian_three {Q : Subgroup G} (hQ : IsElemAbelian 3 Q) :
    Q = Subgroup.closure {c : G | c ∈ Q ∧ IsPGroup 3 (Subgroup.zpowers c)} := by
  apply le_antisymm
  · intro c hc
    exact Subgroup.subset_closure ⟨hc, isPGroup_zpowers_of_pow_eq_one (hQ.2 c hc)⟩
  · rw [Subgroup.closure_le]
    exact fun c hc => hc.1

theorem le_normalizer_commutator_right {P Q : Subgroup G}
    (hQP : Q ≤ Subgroup.normalizer (P : Set G)) :
    Q ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact fun hx =>
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.conj_mem_commutator_of_mem_right hQP hg hx
  · intro hx
    have := CFSG.HardMathSupport.Solomon.UniquenessMaximal.conj_mem_commutator_of_mem_right hQP
      (Q.inv_mem hg) hx
    simpa [mul_assoc] using this

theorem mem_normalizer_centralizer {R : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ c ∈ Subgroup.centralizer (R : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro r hr
    have hr' : g⁻¹ * r * g⁻¹⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hg) r).1 hr
    have h1 := hc _ hr'
    calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * r := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key g hg c, fun hc => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hc
  simpa [mul_assoc] using this

theorem centralizer_pCoreOf_le [Finite G] {L : Subgroup G}
    (hL : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) {q : G} (hqL : q ∈ L) (hq3 : q ^ 3 = 1)
    (hq : q ∉ Subgroup.centralizer (pCoreOf 2 L : Set G)) :
    Subgroup.centralizer (pCoreOf 2 L : Set G) ⊓ L ≤ pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro d₀ hd₀
  by_contra hd₀O
  set D := Subgroup.centralizer (pCoreOf 2 L : Set G) ⊓ L with hDdef
  set N : Subgroup ↥L := CFSG.pCore 2 ↥L with hNdef
  haveI : N.Normal := CFSG.pCore_normal
  have hDn : (D.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro l hl
    exact Prop121.normalizer_inf_mem
      (mem_normalizer_centralizer (le_normalizer_pCoreOf 2 L hl)) (Subgroup.le_normalizer hl)
  have himg : (D.subgroupOf L).map (QuotientGroup.mk' N) = ⊤ := by
    haveI : ((D.subgroupOf L).map (QuotientGroup.mk' N)).Normal :=
      hDn.map _ (QuotientGroup.mk'_surjective N)
    rcases hL.eq_bot_or_eq_top_of_normal ((D.subgroupOf L).map (QuotientGroup.mk' N)) with h | h
    · exfalso
      apply hd₀O
      have hm : QuotientGroup.mk' N ⟨d₀, hd₀.2⟩ ∈ (D.subgroupOf L).map (QuotientGroup.mk' N) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hd₀)
      rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hm
      exact ⟨_, hm, rfl⟩
    · exact h
  have hqm : QuotientGroup.mk' N ⟨q, hqL⟩ ∈ (D.subgroupOf L).map (QuotientGroup.mk' N) := by
    rw [himg]; exact Subgroup.mem_top _
  obtain ⟨d, hd, hdq⟩ := hqm
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hdq
  have hdo : d⁻¹ * ⟨q, hqL⟩ ∈ N := QuotientGroup.eq.1 hdq
  have hoO : (d : G)⁻¹ * q ∈ pCoreOf 2 L := ⟨_, hdo, rfl⟩
  have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.1 hd
  have hcomm : Commute (d : G) ((d : G)⁻¹ * q) :=
    ((Subgroup.mem_centralizer_iff.1 hdD.1) _ hoO).symm
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hoO⟩
  have hk' : ((d : G)⁻¹ * q) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hq2k : q ^ (2 ^ k) = (d : G) ^ (2 ^ k) := by
    have hq : q = (d : G) * ((d : G)⁻¹ * q) := by group
    rw [hq, hcomm.mul_pow, hk', mul_one]
  have hmod : (2 ^ k * 2 ^ k) % 3 = 1 := by
    rw [← mul_pow]; norm_num [Nat.pow_mod]
  have hqq : q = (q ^ (2 ^ k)) ^ (2 ^ k) := by
    rw [← pow_mul, ← Nat.mod_add_div (2 ^ k * 2 ^ k) 3, pow_add, pow_mul, hq3, one_pow, mul_one,
      hmod, pow_one]
  have hqD : q ∈ D := by
    rw [hqq, hq2k]
    exact D.pow_mem (D.pow_mem hdD _) _
  exact hq hqD.1

theorem isPGroup_two_of_le_sup [Finite G] {P L C R : Subgroup G} (hP : IsPGroup 2 P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G)) (hCY : C ≤ P ⊔ L) (hR : IsPGroup 2 R)
    (hCL : ∀ c ∈ C, c ∈ L → c ∈ R) : IsPGroup 2 C := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := P ⊔ L with hYdef
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := sup_le hPL Subgroup.le_normalizer
  have hLY : L ≤ Y := le_sup_right
  haveI : (L.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).2 hYN
  let φ : ↥C →* ↥Y ⧸ L.subgroupOf Y :=
    (QuotientGroup.mk' (L.subgroupOf Y)).comp (Subgroup.inclusion hCY)
  have hker : IsPGroup 2 φ.ker := by
    rintro ⟨c, hc⟩
    have hc' : (Subgroup.inclusion hCY c : ↥Y) ∈ L.subgroupOf Y := by
      have := (MonoidHom.mem_ker).1 hc
      simpa [φ, QuotientGroup.eq_one_iff] using this
    have hcL : ((c : ↥C) : G) ∈ L := Subgroup.mem_subgroupOf.1 hc'
    obtain ⟨k, hk⟩ := hR ⟨_, hCL _ c.2 hcL⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
  have htop : IsPGroup 2 (⊤ : Subgroup (↥Y ⧸ L.subgroupOf Y)) := by
    rintro ⟨z, -⟩
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨t, ht, l, hl, hty⟩ := Prop121.mem_sup_decomp hPL y.2
    obtain ⟨k, hk⟩ := hP ⟨t, ht⟩
    refine ⟨k, Subtype.ext ?_⟩
    have hyt : (QuotientGroup.mk y : ↥Y ⧸ L.subgroupOf Y) =
        QuotientGroup.mk (⟨t, le_sup_left (a := P) ht⟩ : ↥Y) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have e : ((y : G))⁻¹ * t = l⁻¹ := by rw [hty]; group
      simpa [e] using L.inv_mem hl
    have ht1 : (⟨t, le_sup_left (a := P) ht⟩ : ↥Y) ^ (2 ^ k) = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    show (QuotientGroup.mk y : ↥Y ⧸ L.subgroupOf Y) ^ (2 ^ k) = 1
    rw [hyt, ← QuotientGroup.mk_pow, ht1, QuotientGroup.mk_one]
  have h1 := htop.comap_of_ker_isPGroup φ hker
  rw [Subgroup.comap_top] at h1
  exact h1.of_equiv Subgroup.topEquiv

theorem centralizer_pCoreOf_sup_le [Finite G] {P L : Subgroup G} (hP : IsPGroup 2 P)
    (hPL : P ≤ Subgroup.normalizer (L : Set G))
    (hL : Subgroup.centralizer (pCoreOf 2 L : Set G) ⊓ L ≤ pCoreOf 2 L) :
    Subgroup.centralizer (pCoreOf 2 (P ⊔ L) : Set G) ⊓ (P ⊔ L) ≤ pCoreOf 2 (P ⊔ L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := P ⊔ L with hYdef
  have hYN : Y ≤ Subgroup.normalizer (L : Set G) := sup_le hPL Subgroup.le_normalizer
  have hLY : L ≤ Y := le_sup_right
  have hOL : pCoreOf 2 L ≤ pCoreOf 2 Y :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLY)
      (hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hC2 : IsPGroup 2 ↥(Subgroup.centralizer (pCoreOf 2 Y : Set G) ⊓ Y) :=
    isPGroup_two_of_le_sup hP hPL inf_le_right (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      fun c hc hcL => hL ⟨Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hOL) hc.1, hcL⟩
  have hCN : Y ≤ Subgroup.normalizer
      ((Subgroup.centralizer (pCoreOf 2 Y : Set G) ⊓ Y : Subgroup G) : Set G) := fun y hy =>
    Prop121.normalizer_inf_mem (mem_normalizer_centralizer (le_normalizer_pCoreOf 2 Y hy))
      (Subgroup.le_normalizer hy)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hCN hC2

end Constrained

open Prop121 in
theorem printedY2c_of_inputs (h123 : Lemma123Statement) (h124 : Lemma124Statement)
    (h125 : Lemma125Statement) : PrintedY2c := by
  intro G _ _ m p B M E A a h K hK hK3 hKM hu₀ hA0 Js hJs hJJs
  have hPN : pCoreOf 2 M ≤ Subgroup.normalizer (Js : Set G) :=
    printedOJNorm_of_inputs h123 h124 h hK hK3 hKM hu₀ hA0 hJs hJJs
  obtain ⟨x, hxF, -, b, hbB, s, hs, hbs⟩ := Sec12b.noncommute_of_inputs h123 h124 h hK hK3 hKM hu₀ hA0
  obtain ⟨-, -, Js₀, hJs₀, hJJs₀, hJs₀L3⟩ := h125 h hK hK3 hKM hu₀ hA0
  obtain ⟨hp3, -⟩ := h123 h
  subst hp3
  obtain ⟨⟨-, -, -, -, hcard, -, -⟩, -, ⟨hJL3, -⟩, -⟩ := h124 h hK hK3 hKM hu₀ hA0
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ M := h.pair.1.2.1.1.1.1
  have hAel : IsElemAbelian 3 A := h.pair.1.2.1.1.1.2.1
  set Q : Subgroup G := A ⊓ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G)) with hQdef
  have hcard' : Nat.card ↥Q = 9 := hcard
  have hQJ : Q ≤ GLAPLayer 3 (K ⊓ Subgroup.centralizer (centBar 3 A K : Set G)) := inf_le_right
  have hQA : Q ≤ A := inf_le_left
  have hQel : IsElemAbelian 3 Q := Sec12b.isElemAbelian_mono hQA hAel
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hbs (by rw [one_mul, mul_one])
  have hJseq : Js = Js₀ := eq_of_le_twoPrimeComp le_sup_left hJL3 hJs hJs₀ hJJs hJJs₀ (hQJ hbB)
    hb1 (hAel.2 b (hQA hbB))
  subst hJseq
  have hxA : x ∈ A := (inf_le_right : centBar 3 A K ≤ A) hxF
  set P : Subgroup G := pCoreOf 2 M ⊓ Cg x with hPdef
  have hP2 : IsPGroup 2 P := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left
  have hQP : Q ≤ Subgroup.normalizer (P : Set G) := by
    intro q hq
    have hqx : q ∈ Cg x := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact congrArg Subtype.val (hAel.1.is_comm.comm ⟨y, hxA⟩ ⟨q, hQA hq⟩)
    exact normalizer_inf_mem (le_normalizer_pCoreOf 2 M (hAM (hQA hq))) (Subgroup.le_normalizer hqx)
  set S : Subgroup G := ⁅P, Q⁆ with hSdef
  have hP3 : ¬ 3 ∣ Nat.card P :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (coprime_three_of_isPGroup_two hP2)
  have hSS : ⁅S, Q⁆ = S :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.commutator_commutator_eq hP3 hQP
      (eq_closure_of_isElemAbelian_three hQel)
  have hSP : S ≤ P := CFSG.HardMathSupport.Solomon.UniquenessMaximal.commutator_le_left hQP
  have hS2 : IsPGroup 2 S := hP2.to_le hSP
  have hSJs : S ≤ Js := by
    rw [← hSS, Subgroup.commutator_le]
    intro s' hs' q hq
    have h1 : s' * q * s'⁻¹ ∈ Js :=
      (Subgroup.mem_normalizer_iff.1 (hPN (hSP hs').1) q).1 (hJJs (hQJ hq))
    rw [commutatorElement_def]
    exact Js.mul_mem h1 (Js.inv_mem (hJJs (hQJ hq)))
  have hQS : Q ≤ Subgroup.normalizer (S : Set G) := le_normalizer_commutator_right hQP
  have hSO : S ≤ pCoreOf 2 Js :=
    input2027L34_holds G Js Q S hJs₀L3 (hQJ.trans hJJs) hQel hcard' hSJs hS2 hQS
  obtain ⟨q, hq, hqnc⟩ : ∃ q ∈ Q, q ∉ Subgroup.centralizer (pCoreOf 2 Js : Set G) := by
    by_contra hno
    push Not at hno
    have hbot : ⁅S, Q⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro s' hs' q hq
      have := Subgroup.mem_centralizer_iff.1 (hno q hq) s' (hSO hs')
      rw [commutatorElement_def, Subgroup.mem_bot, this]
      group
    have hsb : ⁅s, b⁆ ∈ S := Subgroup.commutator_mem_commutator hs hbB
    rw [← hSS, hbot, Subgroup.mem_bot, commutatorElement_def] at hsb
    apply hbs
    calc b * s = (s * b * s⁻¹ * b⁻¹)⁻¹ * (s * b) := by group
      _ = s * b := by rw [hsb, inv_one, one_mul]
  have hJs2c : Subgroup.centralizer (pCoreOf 2 Js : Set G) ⊓ Js ≤ pCoreOf 2 Js :=
    centralizer_pCoreOf_le
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hJs₀L3).1
      (hJJs (hQJ hq)) (hAel.2 q (hQA hq)) hqnc
  exact centralizer_pCoreOf_sup_le (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M) hPN hJs2c

section Pushing

variable {G : Type} [Group G]

theorem isCharIn_jOf [Finite G] (T : Subgroup G) :
    IsCharIn (CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOf T) T := by
  refine ⟨CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.jOf_le T, fun ψ x hx => ?_⟩
  set W : Subgroup G := (((CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOf T).subgroupOf T).comap
    ψ.toMonoidHom).map T.subtype with hWdef
  have hle : CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOf T ≤ W := by
    refine iSup₂_le fun E hE => ?_
    intro e he
    refine ⟨⟨e, hE.1 he⟩, ?_, rfl⟩
    show ψ ⟨e, hE.1 he⟩ ∈ (CFSG.HardMathSupport.Solomon.UniquenessMaximal.jOf T).subgroupOf T
    rw [Subgroup.mem_subgroupOf]
    set E' : Subgroup G := ((E.subgroupOf T).map ψ.toMonoidHom).map T.subtype with hE'def
    have hE' : E' ≤ T ∧ IsElemAbelian 2 E' ∧ Nat.card E' = 2 ^ CFSG.Open.pRank 2 T := by
      refine ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
      · exact CFSG.SectionRank.isElemAbelian_map
          (CFSG.SectionRank.isElemAbelian_map (isElemAbelian_subgroupOf hE.2.1 T) _) _
      · rw [Subgroup.card_map_of_injective T.subtype_injective,
          Subgroup.card_map_of_injective ψ.injective,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE.1).toEquiv]
        exact hE.2.2
    have hmem : ((ψ ⟨e, hE.1 he⟩ : ↥T) : G) ∈ E' :=
      ⟨_, ⟨⟨e, hE.1 he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩, rfl⟩
    exact (le_iSup₂ (f := fun (E : Subgroup G) (_ : E ≤ T ∧ IsElemAbelian 2 E ∧
      Nat.card E = 2 ^ CFSG.Open.pRank 2 T) => E) E' hE') hmem
  obtain ⟨w, hw, hwx⟩ := hle hx
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

theorem isCharIn_omegaOneZ (T : Subgroup G) :
    IsCharIn (CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ T) T := by
  refine ⟨CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.omegaOneZ_le T, fun ψ x hx => ?_⟩
  set W : Subgroup G := (((CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ T).subgroupOf
    T).comap ψ.toMonoidHom).map T.subtype with hWdef
  have hle : CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ T ≤ W := by
    refine (Subgroup.closure_le _).2 fun z hz => ?_
    obtain ⟨hzc, hz2⟩ := hz
    obtain ⟨hzT, hzcomm⟩ :=
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_centerOf_iff'.1 hzc
    refine ⟨⟨z, hzT⟩, ?_, rfl⟩
    show ψ ⟨z, hzT⟩ ∈ (CFSG.HardMathSupport.Solomon.UniquenessMaximal.omegaOneZ T).subgroupOf T
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · refine CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.mem_centerOf_iff'.2
        ⟨(ψ ⟨z, hzT⟩).2, fun y hy => ?_⟩
      obtain ⟨t, ht⟩ := ψ.surjective ⟨y, hy⟩
      have hcomm : (⟨z, hzT⟩ : ↥T) * t = t * ⟨z, hzT⟩ := Subtype.ext (hzcomm t t.2)
      have h1 := congrArg (fun w : ↥T => ((ψ w : ↥T) : G)) hcomm
      simp only [map_mul, ht, Subgroup.coe_mul] at h1
      exact h1
    · have h1 : (⟨z, hzT⟩ : ↥T) ^ 2 = 1 := Subtype.ext (by simpa using hz2)
      have h2 : (ψ ⟨z, hzT⟩) ^ 2 = 1 := by rw [← map_pow, h1, map_one]
      simpa using congrArg Subtype.val h2
  obtain ⟨w, hw, hwx⟩ := hle hx
  obtain rfl : w = x := Subtype.ext hwx
  exact hw

theorem coe_mem_normalizer_map {W : Subgroup G} {K : Subgroup W} {n : W}
    (hn : n ∈ Subgroup.normalizer (K : Set W)) :
    (n : G) ∈ Subgroup.normalizer ((K.map W.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨n * k * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn k).1 hk, rfl⟩
  · rintro ⟨k', hk', hk'x⟩
    have hxW : x ∈ W := by
      have h1 : x = (n : G)⁻¹ * (k' : G) * n := by
        rw [show (k' : G) = (n : G) * x * (n : G)⁻¹ from hk'x]; group
      rw [h1]
      exact W.mul_mem (W.mul_mem (W.inv_mem n.2) k'.2) n.2
    refine ⟨⟨x, hxW⟩, (Subgroup.mem_normalizer_iff.1 hn ⟨x, hxW⟩).2 ?_, rfl⟩
    have : n * ⟨x, hxW⟩ * n⁻¹ = k' := Subtype.ext (by simpa using hk'x.symm)
    rw [this]
    exact hk'

theorem glaPPrimeCore_eq_pCore_two_of_L34 [Finite G] {J : Subgroup G}
    (hJ : IsLThreeFour (↥J ⧸ CFSG.pCore 2 ↥J)) : GLAPPrimeCore 3 ↥J = CFSG.pCore 2 ↥J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle1 : CFSG.pCore 2 ↥J ≤ GLAPPrimeCore 3 ↥J :=
    CFSG.le_pPrimeCore_of_normal_coprime CFSG.pCore_normal
      (coprime_three_of_isPGroup_two CFSG.pCore_isPGroup)
  refine le_antisymm (fun x hx => ?_) hle1
  set f : ↥J →* ↥J ⧸ CFSG.pCore 2 ↥J := QuotientGroup.mk' (CFSG.pCore 2 ↥J) with hf
  haveI : ((GLAPPrimeCore 3 ↥J).map f).Normal :=
    Subgroup.Normal.map inferInstance f (QuotientGroup.mk'_surjective _)
  obtain ⟨hs, -⟩ := CFSG.HardMathSupport.Solomon.UniquenessMaximal.isSimpleGroup_of_isLThreeFour hJ
  rcases hs.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore 3 ↥J).map f) with h | h
  · have h1 : f x ∈ ((GLAPPrimeCore 3 ↥J).map f) := Subgroup.mem_map_of_mem f hx
    rw [h, Subgroup.mem_bot] at h1
    exact (QuotientGroup.eq_one_iff x).1 h1
  · exfalso
    have hc := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hJ
    have hdvd : Nat.card ((GLAPPrimeCore 3 ↥J).map f) ∣ Nat.card (GLAPPrimeCore 3 ↥J) :=
      Subgroup.card_map_dvd _ _
    rw [h, Subgroup.card_top, hc] at hdvd
    have hcop : Nat.Coprime 3 (Nat.card (GLAPPrimeCore 3 ↥J)) := CFSG.pPrimeCore_coprime_card
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hcop
      ((by norm_num : (3 : ℕ) ∣ 20160).trans hdvd)

theorem exists_mul_of_barX_le {p : ℕ} {C K N : Subgroup G} (hle : barX p C K ≤ barX p C N)
    {k : G} (hk : k ∈ K) (hkC : k ∈ C) :
    ∃ n ∈ N, ∃ o ∈ GLAPPrimeCoreOf p C, k = n * o := by
  have hmem : QuotientGroup.mk' (GLAPPrimeCore p ↥C) ⟨k, hkC⟩ ∈ barX p C N :=
    hle (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hk))
  obtain ⟨y, hy, hyk⟩ := hmem
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hyk
  have hos : y⁻¹ * ⟨k, hkC⟩ ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hyk
  refine ⟨y, Subgroup.mem_subgroupOf.1 hy, ((y⁻¹ * ⟨k, hkC⟩ : ↥C) : G), ⟨_, hos, rfl⟩, ?_⟩
  simp

theorem exists_threeComponent [Finite G] {Y J : Subgroup G} (hJY : J ≤ Y)
    (hYJ : Y ≤ Subgroup.normalizer (J : Set G)) (hJ : IsLThreeFour (↥J ⧸ CFSG.pCore 2 ↥J)) :
    ∃ K : Subgroup ↥Y, GLAPComponent 3 (⊤ : Subgroup ↥Y) K ∧
      IsLThreeFour (↥K ⧸ GLAPPrimeCore 3 ↥K) ∧
      barX 3 (⊤ : Subgroup ↥Y) K = barX 3 (⊤ : Subgroup ↥Y) (J.subgroupOf Y) := by
  have hJ3 : IsLThreeFour (↥J ⧸ GLAPPrimeCore 3 ↥J) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
      (QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two_of_L34 hJ).symm) hJ
  have hJ'3 : IsLThreeFour (↥(J.subgroupOf Y) ⧸ GLAPPrimeCore 3 ↥(J.subgroupOf Y)) := by
    let e : ↥(J.subgroupOf Y) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJY
    exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
      (QuotientGroup.congr _ _ e (glaPPrimeCore_map_iso 3 e)).symm hJ3
  have hJ'n : (J.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJY).2 hYJ
  have hJ'sn : IsSubnormal (J.subgroupOf Y) (⊤ : Subgroup ↥Y) :=
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.isSubnormal_of_le_normalizer' le_top
      (by rw [Subgroup.normalizer_eq_top_iff.2 hJ'n])
  have e4 := quotEquivBarX Nat.prime_three (le_top : J.subgroupOf Y ≤ ⊤) hJ'sn
  have hIbn : (barX 3 (⊤ : Subgroup ↥Y) (J.subgroupOf Y)).Normal :=
    (hJ'n.subgroupOf ⊤).map _ (QuotientGroup.mk'_surjective _)
  have hcomp : IsComponentOf (barX 3 (⊤ : Subgroup ↥Y) (J.subgroupOf Y)) ⊤ := by
    refine ⟨le_top,
      CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.isSubnormal_of_le_normalizer' le_top
        (by rw [Subgroup.normalizer_eq_top_iff.2 hIbn]), ?_⟩
    exact CFSG.SignalizerFunctorTheorem.TransportA.isQuasisimple_of_mulEquiv e4
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.isQuasisimple_of_isLThreeFour' hJ'3)
  obtain ⟨K, hK, hKb⟩ := exists_glaPComponent_barX_eq (⊤ : Subgroup ↥Y) hcomp
  refine ⟨K, hK, ?_, hKb⟩
  have e1 := quotEquivBarX Nat.prime_three (le_top : K ≤ ⊤) hK.2.1
  exact CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsLThreeFour.of_mulEquiv
    (e4.trans ((MulEquiv.subgroupCongr hKb.symm).trans e1.symm)) hJ'3

end Pushing

theorem input28_8Cons_of_inputs (h28 : CFSG.HardMathSupport.Solomon.UniquenessMaximal.Input28_8) :
    Prop121.Input28_8Cons := by
  intro G _ _ Y J T B hKP hYtop hJY hYJ hJL3 hBJ hB hBc hTY hT hBT hTmax hYJT hOT hY2c
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hTY.trans hYJ
  have hYTJ : Y ≤ T ⊔ J := hYJT.trans (le_of_eq (sup_comm J T))
  have hBY : B ≤ Y := hBJ.trans hJY
  have hTmapT : (T.subgroupOf Y).map Y.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTY
  have hTne : T ≠ ⊥ := by
    intro hT0
    have hO0 : pCoreOf 2 Y = ⊥ := le_bot_iff.1 (hT0 ▸ hOT)
    have hY0 : Y = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      have hyc : y ∈ Subgroup.centralizer (pCoreOf 2 Y : Set G) := by
        rw [hO0, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [SetLike.mem_coe, Subgroup.mem_bot] at hh
        rw [hh, one_mul, mul_one]
      have := hY2c ⟨hyc, hy⟩
      rwa [hO0] at this
    have hJ0 : J = ⊥ := le_bot_iff.1 (hY0 ▸ hJY)
    have hc := CFSG.HardMathSupport.Solomon.UniquenessMaximal.card_eq_of_isLThreeFour hJL3
    have h1 : Nat.card ↥J = 1 := by rw [hJ0]; exact Subgroup.card_bot
    have h2 : Nat.card (↥J ⧸ CFSG.pCore 2 ↥J) ∣ Nat.card ↥J := Subgroup.card_quotient_dvd_card _
    rw [hc, h1] at h2
    norm_num at h2
  have hKX : CFSG.Open.IsKGroup ↥Y := isKGroup_of_isKProper hKP hYtop
  have hX2c : Subgroup.centralizer (CFSG.Open.pCore 2 ↥Y : Set ↥Y) ≤ CFSG.Open.pCore 2 ↥Y := by
    intro c hc
    have hcG : (c : G) ∈ Subgroup.centralizer (pCoreOf 2 Y : Set G) ⊓ Y := by
      refine ⟨Subgroup.mem_centralizer_iff.2 ?_, c.2⟩
      rintro _ ⟨z, hz, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc z hz)
    obtain ⟨c', hc', hcc⟩ := hY2c hcG
    rwa [show c = c' from Subtype.ext hcc.symm]
  obtain ⟨K, hK, hKL3, hKb⟩ := exists_threeComponent hJY hYJ hJL3
  have hB'el : IsElemAbelian 3 (B.subgroupOf Y) := isElemAbelian_subgroupOf hB Y
  have hT'2 : IsPGroup 2 (T.subgroupOf Y) := hT.comap_subtype
  have hB'T' : B.subgroupOf Y ≤ Subgroup.normalizer ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [normalizer_subgroupOf_eq hTY]
    intro x hx
    exact (Subgroup.mem_subgroupOf).2 (hBT ((Subgroup.mem_subgroupOf).1 hx))
  have hT'max : CFSG.HardMathSupport.Solomon.UniquenessMaximal.IsMaxBInvariantTwo (B.subgroupOf Y)
      (T.subgroupOf Y) := by
    refine ⟨hT'2, hB'T', fun T'' h2 hBT'' hle => ?_⟩
    have hmap : T''.map Y.subtype = T := by
      refine hTmax _ (Subgroup.map_subtype_le _) (h2.map _) ?_ ?_
      · intro b hb
        exact coe_mem_normalizer_map (n := ⟨b, hBY hb⟩) (hBT'' (Subgroup.mem_subgroupOf.2 hb))
      · rw [← hTmapT]; exact Subgroup.map_mono hle
    have h3 : (T''.map Y.subtype).subgroupOf Y = T'' :=
      Subgroup.comap_map_eq_self_of_injective Y.subtype_injective T''
    rw [← h3, hmap]
  have hgen : barX 3 (⊤ : Subgroup ↥Y) K ⊔ barX 3 (⊤ : Subgroup ↥Y) (T.subgroupOf Y) ⊔
      barX 3 (⊤ : Subgroup ↥Y) (B.subgroupOf Y) = ⊤ := by
    rw [hKb]
    refine eq_top_iff.2 fun z _ => ?_
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨t, ht, j, hj, htj⟩ := Prop121.mem_sup_decomp hTN (hYTJ (w : ↥Y).2)
    have hw : w = ⟨⟨t, hTY ht⟩, Subgroup.mem_top _⟩ * ⟨⟨j, hJY hj⟩, Subgroup.mem_top _⟩ :=
      Subtype.ext (Subtype.ext htj)
    rw [hw, QuotientGroup.mk_mul]
    refine Subgroup.mem_sup_left (Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_)
      (Subgroup.mem_sup_left ?_))
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 ht))
    · exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hj))
  have hcard : Nat.card ↥(barX 3 (⊤ : Subgroup ↥Y) (B.subgroupOf Y) ⊓
      barX 3 (⊤ : Subgroup ↥Y) K) = 9 := by
    have hle : barX 3 (⊤ : Subgroup ↥Y) (B.subgroupOf Y) ≤ barX 3 (⊤ : Subgroup ↥Y) K := by
      rw [hKb]
      refine Subgroup.map_mono fun x hx => ?_
      exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2
        (hBJ (Subgroup.mem_subgroupOf.1 (Subgroup.mem_subgroupOf.1 hx))))
    rw [inf_eq_left.2 hle]
    have hBc' : Nat.card (B.subgroupOf Y) = 9 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBY).toEquiv, hBc]
    have hcop : Nat.Coprime (Nat.card (B.subgroupOf Y))
        (Nat.card (GLAPPrimeCore 3 ↥(⊤ : Subgroup ↥Y))) := by
      rw [hBc', show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact Nat.Coprime.pow_left 2 CFSG.pPrimeCore_coprime_card
    have := card_map_mk_of_coprime (GLAPPrimeCore 3 ↥(⊤ : Subgroup ↥Y))
      (le_top : B.subgroupOf Y ≤ ⊤) hcop
    rw [hBc'] at this
    exact this
  obtain ⟨s, hs2, hsi⟩ := h28 ↥Y hKX hX2c K (T.subgroupOf Y) (B.subgroupOf Y) hK hKL3 hB'el hT'max
    hgen hcard
  obtain ⟨i, his, hi1⟩ : ∃ i ∈ s, i ≠ 1 := by
    by_contra hno
    push Not at hno
    have hsub : s ⊆ {1} := fun i hi => Finset.mem_singleton.2 (hno i hi)
    have := Finset.card_le_card hsub
    rw [Finset.card_singleton] at this
    omega
  have hchar : IsCharIn (CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf T i) T := by
    rcases CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.fin_three_cases i with
      rfl | rfl | rfl
    · exact isCharIn_jOf T
    · exact absurd rfl hi1
    · exact isCharIn_omegaOneZ T
  have hT₀ : CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf T i ≠ ⊥ ∧
      IsCharIn (CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf T i) T :=
    ⟨CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.tripleOf_ne_bot hT hTne i, hchar⟩
  have hT₀map : (CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf (T.subgroupOf Y) i).map
      Y.subtype = CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf T i := by
    rw [← CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7L710.tripleOf_map
      (fun x _ hx => Subtype.ext (by simpa using hx)) i, hTmapT]
  have hO3 : GLAPPrimeCoreOf 3 (⊤ : Subgroup ↥Y) ≤ T.subgroupOf Y := by
    set O3G : Subgroup G := (GLAPPrimeCoreOf 3 (⊤ : Subgroup ↥Y)).map Y.subtype with hO3Gdef
    have hO3GY : O3G ≤ Y := Subgroup.map_subtype_le _
    have hO3GN : Y ≤ Subgroup.normalizer (O3G : Set G) := fun y hy =>
      coe_mem_normalizer_map (n := ⟨y, hy⟩)
        (le_normalizer_glaPPrimeCoreOf 3 (⊤ : Subgroup ↥Y) (Subgroup.mem_top _))
    have hO3Gc : Nat.Coprime 3 (Nat.card O3G) := by
      rw [Subgroup.card_map_of_injective Y.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2
        (not_dvd_card_glaPPrimeCoreOf Nat.prime_three _)
    have hJcore := glaPPrimeCore_eq_pCore_two_of_L34 hJL3
    have hR : ∀ c ∈ O3G, c ∈ J → c ∈ pCoreOf 2 J := by
      intro c hc hcJ
      have hle : (O3G ⊓ J).subgroupOf J ≤ GLAPPrimeCore 3 ↥J := by
        refine CFSG.le_pPrimeCore_of_normal_coprime ?_ ?_
        · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
          intro j hj
          exact Prop121.normalizer_inf_mem (hO3GN (hJY hj)) (Subgroup.le_normalizer hj)
        · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv]
          exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hO3Gc
      have hmem : (⟨c, hcJ⟩ : ↥J) ∈ (O3G ⊓ J).subgroupOf J := Subgroup.mem_subgroupOf.2 ⟨hc, hcJ⟩
      have hmem' := hle hmem
      rw [hJcore] at hmem'
      exact ⟨_, hmem', rfl⟩
    have hO3G2 : IsPGroup 2 O3G := isPGroup_two_of_le_sup hT hTN (hO3GY.trans hYTJ)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J) hR
    have hO3GO : O3G ≤ pCoreOf 2 Y :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hO3GY hO3GN hO3G2
    intro o ho
    exact Subgroup.mem_subgroupOf.2 (hOT (hO3GO ⟨o, ho, rfl⟩))
  set N' : Subgroup ↥Y := Subgroup.normalizer
    ((CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf (T.subgroupOf Y) i : Subgroup ↥Y) :
      Set ↥Y) with hN'def
  have hT'N' : T.subgroupOf Y ≤ N' := fun t ht =>
    CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec7.normalizer_le_normalizer_tripleOf
      (T.subgroupOf Y) i (Subgroup.le_normalizer ht)
  have hJ'N' : J.subgroupOf Y ≤ N' := by
    intro j hj
    have hcov := hsi i his
    rw [hKb] at hcov
    obtain ⟨n, hn, o, ho, rfl⟩ := exists_mul_of_barX_le hcov hj (Subgroup.mem_top j)
    exact N'.mul_mem hn (hT'N' (hO3 ho))
  have hYN' : ∀ y : ↥Y, y ∈ N' := by
    intro y
    obtain ⟨t, ht, j, hj, htj⟩ := Prop121.mem_sup_decomp hTN (hYTJ y.2)
    have hy : y = ⟨t, hTY ht⟩ * ⟨j, hJY hj⟩ := Subtype.ext htj
    rw [hy]
    exact N'.mul_mem (hT'N' (Subgroup.mem_subgroupOf.2 ht)) (hJ'N' (Subgroup.mem_subgroupOf.2 hj))
  intro y hy
  have hyN : y ∈ Subgroup.normalizer
      (CFSG.HardMathSupport.Solomon.UniquenessMaximal.tripleOf T i : Set G) := by
    have := coe_mem_normalizer_map (hYN' ⟨y, hy⟩)
    rwa [hT₀map] at this
  exact (le_iSup₂ (f := fun (T₀ : Subgroup G) (_ : T₀ ≠ ⊥ ∧ IsCharIn T₀ T) =>
    Subgroup.normalizer (T₀ : Set G) ⊓ Y) _ hT₀) ⟨hyN, hy⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims121

end
