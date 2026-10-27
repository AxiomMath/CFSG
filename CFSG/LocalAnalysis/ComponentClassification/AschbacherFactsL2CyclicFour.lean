module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherFactsL2Dichotomy

public section

namespace CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2

open CFSG.Open CFSG.GorensteinWalter

theorem eq_top_or_le_center_of_isQuasisimple {Q : Type*} [Group Q] (hQ : Open.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp, hs⟩ := hQ
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center Q)))
    with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hab : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ N := by
      intro x y
      have hx : x ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top x
      have hy : y ∈ N ⊔ Subgroup.center Q := hsup ▸ Subgroup.mem_top y
      obtain ⟨n₁, hn₁, z₁, hz₁, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hx
      obtain ⟨n₂, hn₂, z₂, hz₂, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
      rw [← QuotientGroup.eq_one_iff (N := N)]
      have e1 : ((n₁ : Q) : Q ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hn₁
      have e2 : ((n₂ : Q) : Q ⧸ N) = 1 := (QuotientGroup.eq_one_iff _).mpr hn₂
      have e3 : ((z₁ : Q) : Q ⧸ N) * z₂ = z₂ * z₁ := by
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          (Subgroup.mem_center_iff.mp hz₂ z₁)]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, e1, e2, one_mul]
      rw [e3]
      group
    rw [eq_top_iff, ← hp, _root_.commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def]
    exact hab x y

theorem odd_card_center_of_quasisimple_dihedral {L : Type} [Group L] [Finite L]
    (hq : Open.IsQuasisimple L) (hL : HasDihedralSylowTwo L) :
    Odd (Nat.card (Subgroup.center L)) := by
  classical
  have hGW : GorensteinWalter.HasDihedralSylowTwo L := by
    obtain ⟨S, n, hn, ⟨eS⟩⟩ := hL
    intro T
    exact ⟨n - 1, by omega, ⟨(Sylow.equiv T S).trans eS⟩⟩
  have hD : IsDGroup L := GorensteinWalter.gorensteinWalter L hGW
  have hnt : Nontrivial L := by
    obtain ⟨-, hs⟩ := hq
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have : Subsingleton (L ⧸ Subgroup.center L) := by
      constructor
      intro x y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [Subsingleton.elim x y]
    exact not_subsingleton _ this
  have hqGW : GorensteinWalter.IsQuasisimple L := ⟨hnt, hq.1, hq.2⟩
  have hOn : (pPrimeCore 2 L).Normal := pPrimeCore_normal
  have hOodd : Odd (Nat.card (pPrimeCore 2 L)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := L))
  have hZQ : Subgroup.center (L ⧸ pPrimeCore 2 L) = ⊥ := by
    cases hD with
    | quotientIsTwoGroup _ h => exact (quasisimple_not_quotient_isTwoGroup hqGW h).elim
    | quotientIsASeven _ e =>
      obtain ⟨e⟩ := e
      exact center_eq_bot_of_mulEquiv e (alternatingGroup.center_eq_bot (by simp))
    | quotientHasLinearNormalSubgroup _ K hKpp M hMn hMidx hModel =>
      have hMt : M = ⊤ := by
        rcases eq_top_or_le_center_of_isQuasisimple hq
            (hMn.comap (QuotientGroup.mk' (pPrimeCore 2 L))) with h | h
        · rw [eq_top_iff]
          intro x _
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) x
          have : y ∈ M.comap (QuotientGroup.mk' (pPrimeCore 2 L)) := h ▸ Subgroup.mem_top y
          exact this
        · exfalso
          have hMab : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x := by
            intro x hx y hy
            obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) x
            obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective (pPrimeCore 2 L) y
            have hx' := Subgroup.mem_center_iff.mp (h hx) y'
            rw [← map_mul, ← map_mul, hx']
          have hcen : ∀ x : M, x ∈ Subgroup.center M := by
            intro x
            rw [Subgroup.mem_center_iff]
            intro y
            exact Subtype.ext (hMab _ y.2 _ x.2)
          have hKodd : Odd (Nat.card K) := odd_card_of_isOddPrimePower hKpp
          have hK3 : 3 ≤ Nat.card K := by
            obtain ⟨p, n, hp, hpodd, hn, hcard⟩ := hKpp
            have : p ≤ p ^ n := Nat.le_self_pow (by omega) p
            have : 3 ≤ p := by
              have := hp.two_le
              rcases hpodd with ⟨k, hk⟩
              omega
            omega
          have htriv : ∀ (H : Type) [Group H], Nonempty (M ≃* H) →
              Subgroup.center H = ⊥ → Nat.card H = 1 := by
            intro H _ he hZ
            obtain ⟨e⟩ := he
            have hZM : Subgroup.center M = ⊥ := center_eq_bot_of_mulEquiv e hZ
            have hall : ∀ x : M, x = 1 := fun x => by
              have := hcen x
              rw [hZM] at this
              exact Subgroup.mem_bot.mp this
            rw [← Nat.card_congr e.toEquiv, Nat.card_eq_one_iff_unique]
            exact ⟨⟨fun x y => by rw [hall x, hall y]⟩, ⟨1⟩⟩
          have h24 : 24 ≤ Nat.card K * (Nat.card K ^ 2 - 1) := by
            have : 9 ≤ Nat.card K ^ 2 := by nlinarith
            have : 8 ≤ Nat.card K ^ 2 - 1 := by omega
            nlinarith
          rcases hModel with h | h
          · have := psl2_card_formula K hKpp
            rw [htriv _ h (psl2_center_eq_bot K)] at this
            omega
          · have := pgl2_card_formula K
            rw [htriv _ h (pgl2_center_eq_bot K)] at this
            omega
      rcases hModel with h | h
      · obtain ⟨e⟩ := h
        exact center_eq_bot_of_mulEquiv
          ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hMt.symm)).trans e)
          (psl2_center_eq_bot K)
      · obtain ⟨e⟩ := h
        exact center_eq_bot_of_mulEquiv
          ((Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hMt.symm)).trans e)
          (pgl2_center_eq_bot K)
  have hZO : Subgroup.center L ≤ pPrimeCore 2 L := by
    intro z hz
    have hmk : (QuotientGroup.mk z : L ⧸ pPrimeCore 2 L) ∈
        Subgroup.center (L ⧸ pPrimeCore 2 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hZQ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmk
    exact hmk
  exact Odd.of_dvd_nat hOodd (Subgroup.card_dvd_of_le hZO)

theorem odd_orderOf_of_mem_center {L : Type*} [Group L] [Finite L]
    (hZ : Odd (Nat.card (Subgroup.center L))) {c : L} (hc : c ∈ Subgroup.center L) :
    Odd (orderOf c) := by
  have h := orderOf_dvd_natCard (⟨c, hc⟩ : Subgroup.center L)
  rw [Subgroup.orderOf_mk] at h
  exact Odd.of_dvd_nat hZ h

theorem eq_one_of_sq_eq_one_of_mem_center {L : Type*} [Group L] [Finite L]
    (hZ : Odd (Nat.card (Subgroup.center L))) {c : L} (hc : c ∈ Subgroup.center L)
    (hc2 : c ^ 2 = 1) : c = 1 := by
  have h1 := orderOf_dvd_of_pow_eq_one hc2
  have h2 := odd_orderOf_of_mem_center hZ hc
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact orderOf_eq_one_iff.mp h
  · rw [h] at h2
    exact absurd h2 (by decide)

theorem exists_fixed_of_fixed_mod_center {L : Type*} [Group L] [Finite L]
    (hZ : Odd (Nat.card (Subgroup.center L))) (β : MulAut L) (hβ : ∀ x, β (β x) = x) (x : L)
    (hx : x⁻¹ * β x ∈ Subgroup.center L) :
    ∃ z ∈ Subgroup.center L, β (x * z) = x * z := by
  set c := x⁻¹ * β x with hcdef
  have hβx : β x = x * c := by rw [hcdef]; group
  have hβc : β c = c⁻¹ := by
    have h1 : β (β x) = x * c * β c := by rw [hβx, map_mul, hβx]
    rw [hβ] at h1
    have h2 : c * β c = 1 := by
      have := congrArg (fun y => x⁻¹ * y) h1
      simp only [inv_mul_cancel, ← mul_assoc] at this
      rw [this]
      group
    exact eq_inv_of_mul_eq_one_right h2
  have hk := odd_orderOf_of_mem_center hZ hx
  obtain ⟨m, hm⟩ := hk
  refine ⟨c ^ (m + 1), Subgroup.pow_mem _ hx _, ?_⟩
  rw [map_mul, map_pow, hβc, hβx, inv_pow]
  have hc : c ^ (2 * m + 1) = 1 := by rw [← hm]; exact pow_orderOf_eq_one c
  have hcomm : ∀ y : L, c * y = y * c := fun y => (Subgroup.mem_center_iff.mp hx y).symm
  calc x * c * (c ^ (m + 1))⁻¹ = x * (c * (c ^ (m + 1))⁻¹) := by group
    _ = x * c ^ (m + 1) := by
      congr 1
      have h1 : c ^ (2 * m + 1) = c ^ (m + 1) * c ^ m := by rw [← pow_add]; ring_nf
      rw [hc] at h1
      have h2 : (c ^ (m + 1))⁻¹ = c ^ m := (eq_inv_of_mul_eq_one_right h1.symm).symm
      rw [h2, ← pow_succ']

theorem dihedral_no_cyclic_four_holds : ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G)
    (a : G), Open.IsQuasisimple L → HasDihedralSylowTwo L →
    a ∈ Subgroup.normalizer (L : Set G) → a ^ 2 = 1 →
    ∀ P : Sylow 2 ↥(L ⊓ Subgroup.centralizer ({a} : Set G)),
      ¬ (IsCyclic (P : Subgroup ↥(L ⊓ Subgroup.centralizer ({a} : Set G))) ∧ Nat.card P = 4)
    := by
  intro G _ _ L a hq hLd haN ha2 P ⟨hPc, hP4⟩
  classical
  have hZ := odd_card_center_of_quasisimple_dihedral hq hLd
  set Z := Subgroup.center L with hZdef
  have hφL : ∀ x, x ∈ L ↔ MulAut.conj a x ∈ L := by
    intro x
    rw [MulAut.conj_apply]
    exact Subgroup.mem_normalizer_iff.mp haN x
  let β : MulAut L := restrictMulAut (MulAut.conj a) L hφL
  have hβ : ∀ x : L, (β x : G) = a * x * a⁻¹ := fun x => rfl
  have hββ : ∀ x, β (β x) = x := by
    intro x
    apply Subtype.ext
    rw [hβ, hβ]
    calc a * (a * (x : G) * a⁻¹) * a⁻¹ = (a * a) * x * (a * a)⁻¹ := by group
      _ = x := by rw [← pow_two, ha2]; group
  have hβfix : ∀ x : L, β x = x ↔ (x : G) * a = a * x := by
    intro x
    rw [Subtype.ext_iff, hβ]
    constructor
    · intro h
      calc (x : G) * a = a * x * a⁻¹ * a := by rw [h]
        _ = a * x := by group
    · intro h
      rw [← h]
      group
  have hβZ : Z.map (β : L →* L) = Z := Subgroup.map_center_eq β
  let α : MulAut (L ⧸ Z) := QuotientGroup.congr Z Z β hβZ
  have hα : ∀ x : L, α (x : L ⧸ Z) = ((β x : L) : L ⧸ Z) := fun x => rfl
  have hαα : ∀ q, α (α q) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hα, hα, hββ]
  have : IsSimpleGroup (L ⧸ Z) := hq.2
  have hQd : HasDihedralSylowTwo (L ⧸ Z) := by
    obtain ⟨S, n, hn, ⟨eS⟩⟩ := hLd
    let π : L →* L ⧸ Z := QuotientGroup.mk' Z
    have hinj : Function.Injective (π.comp (S : Subgroup L).subtype) := by
      rw [injective_iff_map_eq_one]
      intro s hs
      have hsZ : (s : L) ∈ Z := (QuotientGroup.eq_one_iff _).mp hs
      have h2 : IsPGroup 2 (S : Subgroup L) := S.isPGroup'
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp h2) s
      have hodd := odd_orderOf_of_mem_center hZ hsZ
      rw [Subgroup.orderOf_coe, hk] at hodd
      rcases k with _ | k
      · rw [pow_zero] at hk
        exact orderOf_eq_one_iff.mp hk
      · exact absurd hodd (by rw [pow_succ]; simp)
    refine ⟨S.mapSurjective (f := π) (QuotientGroup.mk'_surjective Z), n, hn, ⟨?_⟩⟩
    have hrange : (π.comp (S : Subgroup L).subtype).range = (S : Subgroup L).map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact (((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)).symm).trans eS
  rcases mulAut_involution_dichotomy hQd α hαα with
    ⟨ub, wb, hu, hw, hu1, hw1, huw, hc, hαu, hαw⟩ | hII
  ·
    have hlift : ∀ q : L ⧸ Z, q ^ 2 = 1 → q ≠ 1 → α q = q →
        ∃ x : L, (x : L ⧸ Z) = q ∧ x ^ 2 = 1 ∧ β x = x := by
      intro q hq2 hq1 hαq
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : (x₀ : L)⁻¹ * β x₀ ∈ Z := by
        rw [← QuotientGroup.eq, ← hα]
        exact hαq.symm
      obtain ⟨z, hz, hfix⟩ := exists_fixed_of_fixed_mod_center hZ β hββ x₀ h1
      set x₁ := x₀ * z
      have hx₁ : ((x₁ : L) : L ⧸ Z) = (x₀ : L ⧸ Z) := by
        rw [QuotientGroup.eq]
        simpa [x₁] using hz
      obtain ⟨k, hk⟩ := hZ
      refine ⟨x₁ ^ (2 * k + 1), ?_, ?_, ?_⟩
      · rw [QuotientGroup.mk_pow, hx₁, pow_succ, pow_mul, hq2, one_pow, one_mul]
      · have hsq : x₁ ^ 2 ∈ Z := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hx₁, hq2]
        have hpow : (x₁ ^ 2) ^ Nat.card Z = 1 := by
          have := pow_card_eq_one' (G := Z) (x := ⟨x₁ ^ 2, hsq⟩)
          exact congrArg Subtype.val this
        rw [← pow_mul, mul_comm, pow_mul, ← hk, hpow]
      · rw [map_pow, hfix]
    obtain ⟨u, hub, hu2, hβu⟩ := hlift ub hu hu1 hαu
    obtain ⟨w, hwb, hw2, hβw⟩ := hlift wb hw hw1 hαw
    have hu1' : u ≠ 1 := fun h => hu1 (by rw [← hub, h, QuotientGroup.mk_one])
    have hw1' : w ≠ 1 := fun h => hw1 (by rw [← hwb, h, QuotientGroup.mk_one])
    have huw' : u ≠ w := fun h => huw (by rw [← hub, ← hwb, h])
    have hc' : u * w = w * u := by
      set d := u * w * u⁻¹ * w⁻¹ with hd
      have hdZ : d ∈ Z := by
        rw [← QuotientGroup.eq_one_iff]
        simp only [hd, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hub, hwb]
        rw [hc]
        group
      have hcomm : ∀ y : L, d * y = y * d := fun y => (Subgroup.mem_center_iff.mp hdZ y).symm
      have hd2 : d ^ 2 = 1 := by
        have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hu2)
        have h1 : u * w * u⁻¹ = d * w := by rw [hd]; group
        have h2 : w = u * (u * w * u⁻¹) * u⁻¹ := by
          calc w = (u * u) * w * (u * u)⁻¹ := by rw [← pow_two, hu2]; group
            _ = u * (u * w * u⁻¹) * u⁻¹ := by group
        rw [h1] at h2
        have h3 : w = d * (u * w * u⁻¹) := by
          calc w = u * (d * w) * u⁻¹ := h2
            _ = u * d * w * u⁻¹ := by group
            _ = d * u * w * u⁻¹ := by rw [← hcomm u]
            _ = d * (u * w * u⁻¹) := by group
        rw [h1] at h3
        have : d * d * w = 1 * w := by
          calc d * d * w = d * (d * w) := by group
            _ = w := h3.symm
            _ = 1 * w := by group
        rw [pow_two]
        exact mul_right_cancel this
      have hd1 := eq_one_of_sq_eq_one_of_mem_center hZ hdZ hd2
      calc u * w = d * w * u := by rw [hd]; group
        _ = w * u := by rw [hd1, one_mul]
    have hmem : ∀ x : L, β x = x → (x : G) ∈ L ⊓ Subgroup.centralizer ({a} : Set G) :=
      fun x hx => Subgroup.mem_inf.mpr ⟨x.2,
        Subgroup.mem_centralizer_singleton_iff.mpr ((hβfix x).mp hx)⟩
    apply not_isCyclic_sylow_of_commuting_involutions (u := ⟨u, hmem u hβu⟩)
      (w := ⟨w, hmem w hβw⟩) _ _ _ _ _ _ P hPc
    · exact Subtype.ext (by simpa using congrArg Subtype.val hu2)
    · exact Subtype.ext (by simpa using congrArg Subtype.val hw2)
    · exact fun h => hu1' (Subtype.ext (by simpa using congrArg Subtype.val h))
    · exact fun h => hw1' (Subtype.ext (by simpa using congrArg Subtype.val h))
    · exact fun h => huw' (Subtype.ext (by simpa using congrArg Subtype.val h))
    · exact Subtype.ext (by simpa using congrArg Subtype.val hc')
  ·
    obtain ⟨y, hy⟩ := hPc.exists_generator
    have hyord : orderOf y = 4 := by rw [orderOf_eq_card_of_forall_mem_zpowers hy, hP4]
    set yC : ↥(L ⊓ Subgroup.centralizer ({a} : Set G)) := y.1 with hyC
    set yG : G := (yC : G) with hyG
    have hyL : yG ∈ L := (Subgroup.mem_inf.mp yC.2).1
    have hya : yG * a = a * yG :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp yC.2).2
    set yL : L := ⟨yG, hyL⟩
    have hyLord : orderOf yL = 4 := by
      show orderOf (⟨yG, hyL⟩ : L) = 4
      rw [Subgroup.orderOf_mk]
      show orderOf (yC : G) = 4
      rw [Subgroup.orderOf_coe, hyC, Subgroup.orderOf_coe, hyord]
    apply hII (yL : L ⧸ Z) _ (by rw [hα, (hβfix yL).mpr hya])
    have h4 : (yL : L ⧸ Z) ^ 4 = 1 := by
      rw [← QuotientGroup.mk_pow, ← hyLord, pow_orderOf_eq_one, QuotientGroup.mk_one]
    have h2 : (yL : L ⧸ Z) ^ 2 ≠ 1 := by
      intro h
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h
      have h' : (yL ^ 2) ^ 2 = 1 := by
        have h4' : yL ^ 4 = 1 := by rw [← hyLord]; exact pow_orderOf_eq_one yL
        calc (yL ^ 2) ^ 2 = yL ^ 4 := by rw [← pow_mul]
          _ = 1 := h4'
      have := eq_one_of_sq_eq_one_of_mem_center hZ h h'
      have := orderOf_dvd_of_pow_eq_one this
      rw [hyLord] at this
      omega
    have hdvd := orderOf_dvd_of_pow_eq_one h4
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf (yL : L ⧸ Z)
    · rw [orderOf_eq_zero_iff'] at h
      exact absurd (h 4 (by norm_num)) (by simpa using h4)
    · exact absurd (by rw [orderOf_eq_one_iff.mp h, one_pow]) h2
    · exact absurd (by rw [← h]; exact pow_orderOf_eq_one _) h2
    · omega
    · rfl

end CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2
