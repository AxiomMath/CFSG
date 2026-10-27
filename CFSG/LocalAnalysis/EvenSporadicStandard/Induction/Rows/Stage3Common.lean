module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.PairShape
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Stage3Defs

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.Solomon78
  CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog

theorem three_le_pRank_of_elemAbelian {X : Type} [Group X] [Finite X] (E : Subgroup X)
    (hsq : ∀ x ∈ E, x * x = 1) (hc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (h8 : 8 ≤ Nat.card E) :
    3 ≤ CFSG.pRank 2 X := by
  have hcomm : IsMulCommutative ↥E := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  have hexp : Monoid.exponent ↥E ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    apply Subtype.ext
    simpa [pow_two] using hsq x x.2
  have : CFSG.IsElementaryAbelian 2 ↥E := ⟨hexp⟩
  have hP : IsPGroup 2 ↥E := CFSG.IsElementaryAbelian.isPGroup 2 ↥E
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hbdd : BddAbove {r : ℕ | ∃ A : Subgroup X, CFSG.IsElementaryAbelian 2 A ∧
      Nat.card A = 2 ^ r} := by
    refine ⟨Nat.card X, fun r ⟨A, _, hA⟩ => ?_⟩
    have h1 : 2 ^ r ≤ Nat.card X := hA ▸ Subgroup.card_le_card_group A
    exact (Nat.lt_two_pow_self.le).trans h1
  exact hk3.trans (le_csSup hbdd ⟨E, inferInstance, hk⟩)

theorem exists_involutory_aut_of_even {X : Type} [Group X] [Finite X]
    (h : Even (Nat.card (X ⧸ center X))) : ∃ α : MulAut X, α ≠ 1 ∧ α * α = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 h)
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hq1 : (QuotientGroup.mk g : X ⧸ center X) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hq
    omega
  have hq2 : (QuotientGroup.mk g : X ⧸ center X) ^ 2 = 1 := by
    rw [← hq]
    exact pow_orderOf_eq_one _
  have hg1 : g ∉ center X := fun hg => hq1 ((QuotientGroup.eq_one_iff g).2 hg)
  have hg2 : g ^ 2 ∈ center X := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hq2
  refine ⟨MulAut.conj g, fun h1 => hg1 ?_, ?_⟩
  · rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut X => f x) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  · ext x
    have hx := Subgroup.mem_center_iff.1 hg2 x
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply]
    calc g * (g * x * g⁻¹) * g⁻¹ = (g * g) * x * (g * g)⁻¹ := by group
      _ = x := by rw [← pow_two, ← hx]; group

theorem three_le_pRank_of_fixesElem {X : Type} [Group X] [Finite X] {n : ℕ} (hn : 8 ≤ n)
    (h : InvolutionFixesElem X n) (hev : Even (Nat.card (X ⧸ center X))) :
    3 ≤ CFSG.pRank 2 X := by
  obtain ⟨α, hα1, hα2⟩ := exists_involutory_aut_of_even hev
  obtain ⟨E, -, hsq, hc, hcard⟩ := h α hα1 hα2
  exact three_le_pRank_of_elemAbelian E hsq hc (hn.trans hcard)

theorem three_le_pRank_of_fixesElem_iso {X K : Type} [Group X] [Group K] [Finite X] [Finite K]
    (e : X ≃* K) {n : ℕ} (hn : 8 ≤ n) (h : InvolutionFixesElem K n)
    (hev : Even (Nat.card (K ⧸ center K))) : 3 ≤ CFSG.pRank 2 X := by
  obtain ⟨α, hα1, hα2⟩ := exists_involutory_aut_of_even hev
  obtain ⟨E, -, hsq, hc, hcard⟩ := h α hα1 hα2
  refine three_le_pRank_of_elemAbelian (E.map e.symm.toMonoidHom) ?_ ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    show e.symm y * e.symm y = 1
    rw [← map_mul, hsq y hy, map_one]
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    show e.symm y * e.symm z = e.symm z * e.symm y
    rw [← map_mul, ← map_mul, hc y hy z hz]
  · rw [Subgroup.card_map_of_injective e.symm.injective]
    exact hn.trans hcard

theorem no_cubic_root (N c : ℕ) (h1 : c * (c ^ 2 - 1) < 2 * N)
    (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1)) (q : ℕ) : q * (q ^ 2 - 1) ≠ 2 * N := by
  intro h
  rcases Nat.lt_or_ge c q with hq | hq
  · have : (c + 1) * ((c + 1) ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega
  · have : q * (q ^ 2 - 1) ≤ c * (c ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    omega

theorem two_mul_card_of_lieModel_psl_two {G : Type} [Group G] {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (h : CFSG.Blueprint.LieModel G .PSL 2 p f) :
    2 * Nat.card G = p ^ f * ((p ^ f) ^ 2 - 1) := by
  rcases h with ⟨-, hadm, K, hK, hKfin, hKcard, ⟨e⟩⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · have hf : 1 ≤ f := hadm.2.1
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card K) :=
      ⟨p, f, hp, hp.odd_of_ne_two hp2, hf, hKcard⟩
    have h1 := CFSG.GorensteinWalter.psl2_card_formula K hodd
    have h2 : Nat.card G = Nat.card (CFSG.GorensteinWalter.PSL2 K) :=
      Nat.card_congr (e.toEquiv.trans
        (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.toEquiv)
    rw [h2, h1, hKcard]
    have hq : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
    have h3 : 2 ∣ p ^ f * ((p ^ f) ^ 2 - 1) := by
      refine Dvd.dvd.mul_left ?_ _
      have : Odd ((p ^ f) ^ 2) := hq.pow
      obtain ⟨m, hm⟩ := this
      omega
    exact Nat.mul_div_cancel' h3
  · omega
  · omega
  · omega

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem kNotExc_of_card {X : Type} [Group X] {N c : ℕ} (hX : Nat.card (X ⧸ center X) = N)
    (h1 : c * (c ^ 2 - 1) < 2 * N) (h2 : 2 * N < (c + 1) * ((c + 1) ^ 2 - 1))
    (hA7 : N ≠ 2520) :
    ¬ Nonempty ((X ⧸ center X) ≃* alternatingGroup (Fin 7)) ∧
      ¬ ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ CFSG.Blueprint.LieModel (X ⧸ center X) .PSL 2 p f := by
  constructor
  · rintro ⟨e⟩
    have h := Nat.card_congr e.toEquiv
    rw [hX, card_alternatingGroup_seven] at h
    exact hA7 h
  · rintro ⟨p, f, hp, hp2, hm⟩
    have h := two_mul_card_of_lieModel_psl_two hp hp2 hm
    rw [hX] at h
    exact no_cubic_root N c h1 h2 (p ^ f) h.symm

theorem oddCore_le_center_of_simple_quotient {Y : Type} [Group Y]
    [Finite (Y ⧸ center Y)] [IsSimpleGroup (Y ⧸ center Y)]
    (hev : Even (Nat.card (Y ⧸ center Y))) : CFSG.oddCore Y ≤ center Y := by
  refine sSup_le fun N hN => ?_
  have hmap : (N.map (QuotientGroup.mk' (center Y))).Normal :=
    hN.1.map _ QuotientGroup.mk_surjective
  have hodd : Odd (Nat.card (N.map (QuotientGroup.mk' (center Y)))) :=
    Odd.of_dvd_nat hN.2 (Subgroup.card_map_dvd _ _)
  have hle : N.map (QuotientGroup.mk' (center Y)) ≤ CFSG.oddCore (Y ⧸ center Y) :=
    le_oddCore_of_normal hmap hodd
  rw [oddCore_eq_bot_of_isSimpleGroup hev, le_bot_iff] at hle
  intro x hx
  have : QuotientGroup.mk' (center Y) x ∈ N.map (QuotientGroup.mk' (center Y)) := ⟨x, hx, rfl⟩
  rw [hle, Subgroup.mem_bot] at this
  exact (QuotientGroup.eq_one_iff x).1 this

theorem kNeL_of_card {X Y : Type} [Group X] [Group Y] {cardS cardK : ℕ}
    [Finite (X ⧸ center X)] [IsSimpleGroup (X ⧸ center X)]
    (hX : Nat.card (X ⧸ center X) = cardS) (hev : Even cardS)
    [Finite (Y ⧸ CFSG.oddCore Y)] (hY : Nat.card (Y ⧸ CFSG.oddCore Y) = cardK)
    (hlt : cardK < cardS) : ¬ Nonempty ((X ⧸ center X) ≃* (Y ⧸ center Y)) := by
  rintro ⟨e⟩
  have : Finite (Y ⧸ center Y) := Finite.of_equiv _ e.toEquiv
  have : IsSimpleGroup (Y ⧸ center Y) := e.symm.isSimpleGroup
  have hcard : Nat.card (Y ⧸ center Y) = cardS := (Nat.card_congr e.toEquiv.symm).trans hX
  have hO : CFSG.oddCore Y ≤ center Y := oddCore_le_center_of_simple_quotient (hcard ▸ hev)
  have hsurj : Function.Surjective (QuotientGroup.map (CFSG.oddCore Y) (center Y)
      (MonoidHom.id Y) (fun x hx => hO hx)) := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨QuotientGroup.mk g, rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  omega

theorem card_center_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    Nat.card (center A) = Nat.card (center B) := by
  rw [← Subgroup.map_center_eq e]
  exact Nat.card_congr ((center A).equivMapOfInjective _ e.injective).toEquiv

noncomputable def quotientCenterEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    A ⧸ center A ≃* B ⧸ center B :=
  QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)

theorem isLS_of_mulEquiv {S : List TauCeti.SporadicName} {X Y : Type} [Group X] [Group Y]
    (e : X ≃* Y) (h : IsLS S X) : IsLS S Y := by
  obtain ⟨s, hs, hq, hodd, ⟨f⟩⟩ := h
  refine ⟨s, hs, CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_,
    ⟨(quotientCenterEquiv' e).symm.trans f⟩⟩
  rw [← card_center_of_mulEquiv' e]
  exact hodd

theorem oddCover_top_of_cover {s : TauCeti.SporadicName} {H : Type} [Group H] {L : Subgroup H}
    (h : OddCover s L) : OddCover s (⊤ : Subgroup ↥L) := by
  have : IsLS [s] ↥L := ⟨s, List.mem_singleton_self s, h⟩
  obtain ⟨s', hs', h'⟩ := isLS_of_mulEquiv (Subgroup.topEquiv (G := ↥L)).symm this
  rcases List.mem_singleton.1 hs' with rfl
  exact h'

theorem oddCore_le_center_of_quasisimple {K : Type} [Group K] (hKq : CFSG.IsQuasisimple K)
    (hnc : ¬ IsMulCommutative (K ⧸ CFSG.oddCore K)) : CFSG.oddCore K ≤ center K := by
  have : IsSimpleGroup (K ⧸ center K) := hKq.2.1
  have hmap : ((CFSG.oddCore K).map (QuotientGroup.mk' (center K))).Normal :=
    (inferInstance : (CFSG.oddCore K).Normal).map _ QuotientGroup.mk_surjective
  have := hmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((CFSG.oddCore K).map (QuotientGroup.mk' (center K))) with h | h
  · intro x hx
    have : QuotientGroup.mk' (center K) x ∈ (CFSG.oddCore K).map (QuotientGroup.mk' (center K)) :=
      ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).1 this
  · exfalso
    apply hnc
    have key : ∀ k : K, ∃ z ∈ center K, (QuotientGroup.mk k : K ⧸ CFSG.oddCore K) =
        QuotientGroup.mk z := by
      intro k
      have hk : QuotientGroup.mk' (center K) k ∈
          (CFSG.oddCore K).map (QuotientGroup.mk' (center K)) := by rw [h]; trivial
      obtain ⟨n, hn, hnk⟩ := hk
      have hz : n⁻¹ * k ∈ center K := QuotientGroup.eq.1 hnk
      refine ⟨n⁻¹ * k, hz, ?_⟩
      rw [QuotientGroup.eq]
      have := (inferInstance : (CFSG.oddCore K).Normal).conj_mem n⁻¹ ((CFSG.oddCore K).inv_mem hn)
        k⁻¹
      simpa [mul_assoc] using this
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨z, hz, hza⟩ := key a
    obtain ⟨w, hw, hwb⟩ := key b
    rw [hza, hwb, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      (Subgroup.mem_center_iff.1 hz w).symm]

theorem exists_central_lift {K : Type} [Group K] [Group.IsPerfect K]
    (hO : CFSG.oddCore K ≤ center K) {y : K ⧸ CFSG.oddCore K}
    (hy : y ∈ center (K ⧸ CFSG.oddCore K)) :
    ∃ x ∈ center K, (QuotientGroup.mk x : K ⧸ CFSG.oddCore K) = y := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  have hc : ∀ k : K, g⁻¹ * k⁻¹ * g * k ∈ center K := by
    intro k
    apply hO
    have h1 := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk k)
    have h2 : (QuotientGroup.mk (k * g) : K ⧸ CFSG.oddCore K) = QuotientGroup.mk (g * k) := h1
    have := QuotientGroup.eq.1 h2
    simpa [mul_assoc] using this
  let φ : K →* center K :=
    { toFun := fun k => ⟨g⁻¹ * k⁻¹ * g * k, hc k⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro k l
        apply Subtype.ext
        have h := Subgroup.mem_center_iff.1 (hc k) (g⁻¹ * l⁻¹ * g * l)
        have hl := Subgroup.mem_center_iff.1 (hc k) l
        have e1 : l⁻¹ * (g⁻¹ * k⁻¹ * g * k) * l = g⁻¹ * k⁻¹ * g * k := by
          calc l⁻¹ * (g⁻¹ * k⁻¹ * g * k) * l = l⁻¹ * ((g⁻¹ * k⁻¹ * g * k) * l) := by group
            _ = l⁻¹ * (l * (g⁻¹ * k⁻¹ * g * k)) := by rw [hl]
            _ = g⁻¹ * k⁻¹ * g * k := by group
        show g⁻¹ * (k * l)⁻¹ * g * (k * l) = (g⁻¹ * k⁻¹ * g * k) * (g⁻¹ * l⁻¹ * g * l)
        calc g⁻¹ * (k * l)⁻¹ * g * (k * l)
            = (g⁻¹ * l⁻¹ * g * l) * (l⁻¹ * (g⁻¹ * k⁻¹ * g * k) * l) := by group
          _ = (g⁻¹ * l⁻¹ * g * l) * (g⁻¹ * k⁻¹ * g * k) := by rw [e1]
          _ = (g⁻¹ * k⁻¹ * g * k) * (g⁻¹ * l⁻¹ * g * l) := h }
  have hφ : φ = 1 := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative φ
  refine ⟨g, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro k
  have h := congrArg (fun f : K →* center K => (f k : K)) hφ
  simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, OneMemClass.coe_one] at h
  have h3 : k⁻¹ * g * k = g := by
    calc k⁻¹ * g * k = g * (g⁻¹ * k⁻¹ * g * k) := by group
      _ = g := by rw [h, mul_one]
  calc k * g = k * (k⁻¹ * g * k) := by rw [h3]
    _ = g * k := by group

theorem exists_central_involution {K : Type} [Group K] [Finite K] [Group.IsPerfect K]
    (hO : CFSG.oddCore K ≤ center K) (hZ2 : Nat.card (center (K ⧸ CFSG.oddCore K)) = 2) :
    ∃ u : K, u ∈ center K ∧ orderOf u = 2 := by
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ center (K ⧸ CFSG.oddCore K), y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : Subsingleton (center (K ⧸ CFSG.oddCore K)) :=
      ⟨fun a b => Subtype.ext ((hcon a a.2).trans (hcon b b.2).symm)⟩
    have h1 := Nat.card_unique (α := center (K ⧸ CFSG.oddCore K))
    omega
  obtain ⟨x, hx, hxy⟩ := exists_central_lift hO hy
  have hy2 : y ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := ↥(center (K ⧸ CFSG.oddCore K))) (x := ⟨y, hy⟩)
    rw [hZ2] at h
    simpa using congrArg Subtype.val h
  have hodd : Odd (Nat.card (CFSG.oddCore K)) := odd_card_oddCore
  have hx2 : x ^ 2 ∈ CFSG.oddCore K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hxy]
    exact hy2
  have h1 : (x ^ 2) ^ Nat.card (CFSG.oddCore K) = 1 := by
    have := pow_card_eq_one' (G := ↥(CFSG.oddCore K)) (x := ⟨x ^ 2, hx2⟩)
    have h := congrArg Subtype.val this
    exact h
  have hu2 : (x ^ Nat.card (CFSG.oddCore K)) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, h1]
  have hu1 : x ^ Nat.card (CFSG.oddCore K) ≠ 1 := by
    intro h
    apply hy1
    have h' := congrArg (QuotientGroup.mk (s := CFSG.oddCore K)) h
    obtain ⟨m, hm⟩ := hodd
    rw [QuotientGroup.mk_pow, hxy, hm, pow_succ, pow_mul, hy2, one_pow, one_mul] at h'
    simpa using h'
  exact ⟨x ^ Nat.card (CFSG.oddCore K), pow_mem hx _, orderOf_eq_prime hu2 hu1⟩

theorem isKPinned_isoInv (s : TauCeti.SporadicName) (P : ℕ → Prop) :
    (IsKPinned s P).IsoInv := by
  intro X Y _ _ e ⟨u, K, hQ, ⟨f⟩⟩
  exact ⟨u, K, hQ, ⟨e.symm.trans f⟩⟩

noncomputable def quotientCenterOddCoreEquiv {K : Type} [Group K] [Group.IsPerfect K]
    (hO : CFSG.oddCore K ≤ center K) :
    (K ⧸ CFSG.oddCore K) ⧸ center (K ⧸ CFSG.oddCore K) ≃* K ⧸ center K := by
  let π : K →* (K ⧸ CFSG.oddCore K) ⧸ center (K ⧸ CFSG.oddCore K) :=
    (QuotientGroup.mk' (center (K ⧸ CFSG.oddCore K))).comp (QuotientGroup.mk' (CFSG.oddCore K))
  have hπ : Function.Surjective π :=
    (QuotientGroup.mk_surjective (s := center (K ⧸ CFSG.oddCore K))).comp
      (QuotientGroup.mk_surjective (s := CFSG.oddCore K))
  have hker : π.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      have hy : (QuotientGroup.mk x : K ⧸ CFSG.oddCore K) ∈ center (K ⧸ CFSG.oddCore K) :=
        (QuotientGroup.eq_one_iff _).1 hx
      obtain ⟨x', hx', hxx'⟩ := exists_central_lift hO hy
      have h1 : x'⁻¹ * x ∈ CFSG.oddCore K := QuotientGroup.eq.1 hxx'
      have := mul_mem hx' (hO h1)
      simpa using this
    · intro hx
      refine (QuotientGroup.eq_one_iff _).2 ?_
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
      show (QuotientGroup.mk g : K ⧸ CFSG.oddCore K) * QuotientGroup.mk x =
        QuotientGroup.mk x * QuotientGroup.mk g
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hx g]
  exact (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)

end CFSG.EvenSporadicStandard.Induction
