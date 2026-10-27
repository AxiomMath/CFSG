module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I141FAt

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I141F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4

section Ranks

variable {H : Type} [Group H] [Finite H]

theorem card_le_of_elemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup H} {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ Nat.card H := by
  have h1 : Nat.card E ≤ Nat.card H := Subgroup.card_le_card_group E
  have h2 : k < p ^ k := Nat.lt_pow_self hp.one_lt
  rw [← hk] at h2
  exact le_trans h2.le h1

theorem pRank_bddAbove (p : ℕ) (hp : p.Prime) (K : Subgroup H) :
    BddAbove {k | ∃ E : Subgroup H, E ≤ K ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card H, ?_⟩
  rintro k ⟨E, -, -, hE⟩
  exact card_le_of_elemAbelian hp hE

theorem le_pRank (p : ℕ) (hp : p.Prime) {K E : Subgroup H} (hEK : E ≤ K)
    (hE : CFSG.Open.IsElemAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) :
    k ≤ CFSG.Open.pRank p K := by
  unfold CFSG.Open.pRank
  exact le_csSup (pRank_bddAbove p hp K) ⟨E, hEK, hE, hk⟩

theorem pRank_le_card (p : ℕ) (hp : p.Prime) (K : Subgroup H) :
    CFSG.Open.pRank p K ≤ Nat.card H := by
  unfold CFSG.Open.pRank
  rcases Set.eq_empty_or_nonempty
      {k | ∃ E : Subgroup H, E ≤ K ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k} with h | h
  · rw [h, csSup_empty]
    exact bot_le
  · refine csSup_le h ?_
    rintro k ⟨E, -, -, hE⟩
    exact card_le_of_elemAbelian hp hE

theorem le_twoLocalPrimeRank (p : ℕ) (hp : p.Prime) {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hM : CFSG.Open.IsTwoLocal M) {k : ℕ} (hk : k ≤ CFSG.Open.pRank p M) :
    k ≤ CFSG.Open.twoLocalPrimeRank p G := by
  unfold CFSG.Open.twoLocalPrimeRank
  refine le_trans hk (le_csSup ?_ ⟨M, hM, rfl⟩)
  refine ⟨Nat.card G, ?_⟩
  rintro _ ⟨L, -, rfl⟩
  exact pRank_le_card p hp L


theorem two_card_le {Y : Type} [Group Y] [Finite Y] (Q : Subgroup Y) (hQ : IsPGroup 2 Q) :
    Nat.card Q ≤ 2 ^ (Nat.card Y).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hQ
  have hdvd : Nat.card Q ∣ Nat.card Y := Subgroup.card_subgroup_dvd_card Q
  rw [ha] at hdvd ⊢
  have hY : Nat.card Y ≠ 0 := Nat.card_pos.ne'
  have : a ≤ (Nat.card Y).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hY).1 hdvd
  exact Nat.pow_le_pow_right (by norm_num) this

theorem card_sylow_two {Y : Type} [Group Y] [Finite Y] (Q : Sylow 2 Y) :
    Nat.card Q = 2 ^ (Nat.card Y).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Sylow.card_eq_multiplicity Q

def sylowOfCard {Y : Type} [Group Y] [Finite Y] (S : Subgroup Y) (hS : IsPGroup 2 S)
    (hcard : Nat.card S = 2 ^ (Nat.card Y).factorization 2) : Sylow 2 Y :=
  { toSubgroup := S
    isPGroup' := hS
    is_maximal' := fun {Q} hQ hle => by
      have hle' : Nat.card Q ≤ Nat.card S := by
        rw [hcard]
        exact two_card_le Q hQ
      exact (Subgroup.eq_of_le_of_card_ge hle hle').symm }


theorem factorization_two_mul_pow (j n : ℕ) (hn : n ≠ 0) :
    (2 ^ j * n).factorization 2 = j + n.factorization 2 := by
  rw [Nat.factorization_mul (pow_ne_zero _ two_ne_zero) hn, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two]
  simp

theorem exists_sylow_lift {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (P : Subgroup (Y ⧸ N)) (hP : IsPGroup 2 P) :
    ∃ S : Subgroup Y, S ≤ P.comap (QuotientGroup.mk' N) ∧ IsPGroup 2 S ∧
      Nat.card S = 2 ^ (Nat.card (P.comap (QuotientGroup.mk' N))).factorization 2 ∧
      S.map (QuotientGroup.mk' N) = P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  set X : Subgroup Y := P.comap π with hX
  have hNX : N ≤ X := by
    intro n hn
    show π n ∈ P
    have h1 : π n = 1 := (QuotientGroup.eq_one_iff n).2 hn
    rw [h1]
    exact P.one_mem
  obtain ⟨Q⟩ : Nonempty (Sylow 2 ↥N) := Sylow.nonempty
  set Q₀ : Subgroup Y := (Q : Subgroup ↥N).map N.subtype with hQ₀
  have hQ₀N : Q₀ ≤ N := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQ₀X : Q₀ ≤ X := hQ₀N.trans hNX
  have hQ₀2 : IsPGroup 2 Q₀ := Q.isPGroup'.map N.subtype
  have hQX : IsPGroup 2 (Q₀.subgroupOf X) := IsPGroup.comap_subtype hQ₀2
  obtain ⟨SX, hSX⟩ := hQX.exists_le_sylow
  set S : Subgroup Y := (SX : Subgroup ↥X).map X.subtype with hS
  have hS2 : IsPGroup 2 S := SX.isPGroup'.map X.subtype
  have hSX_le : S ≤ X := Subgroup.map_subtype_le _
  have hcardS : Nat.card S = 2 ^ (Nat.card X).factorization 2 := by
    rw [hS, Subgroup.card_map_of_injective X.subtype_injective, card_sylow_two SX]
  have hQ₀S : Q₀ ≤ S := by
    have h1 : (Q₀.subgroupOf X).map X.subtype ≤ S :=
      Subgroup.map_mono (hSX : Q₀.subgroupOf X ≤ (SX : Subgroup ↥X))
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hQ₀X] at h1
    exact h1
  have hR2 : IsPGroup 2 ↥(N ⊓ S) := IsPGroup.to_le hS2 inf_le_right
  have hRN : (N ⊓ S) ≤ N := inf_le_left
  have hRcard : Nat.card ↥(N ⊓ S) ≤ 2 ^ (Nat.card N).factorization 2 := by
    have h1 := two_card_le ((N ⊓ S).subgroupOf N) (IsPGroup.comap_subtype hR2)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv] at h1
  have hQcard : Nat.card ↥Q₀ = 2 ^ (Nat.card N).factorization 2 := by
    rw [hQ₀, Subgroup.card_map_of_injective N.subtype_injective, card_sylow_two Q]
  have hRcard' : Nat.card ↥(N ⊓ S) = 2 ^ (Nat.card N).factorization 2 := by
    apply le_antisymm hRcard
    rw [← hQcard]
    exact Subgroup.card_le_of_le (le_inf hQ₀N hQ₀S)
  have hrel : N.relIndex S * Nat.card ↥(N ⊓ S) = Nat.card S := Subgroup.relIndex_mul_card N S
  have hkerπ : N.relIndex S = Nat.card ↥(S.map π) := by
    have h := Subgroup.relIndex_ker S π
    rw [QuotientGroup.ker_mk'] at h
    exact h
  have hXcard : Nat.card X = Nat.card P * Nat.card N := by
    have h1 : N.relIndex X * Nat.card ↥(N ⊓ X) = Nat.card X := Subgroup.relIndex_mul_card N X
    have h2 : N.relIndex X = Nat.card ↥(X.map π) := by
      have h := Subgroup.relIndex_ker X π
      rw [QuotientGroup.ker_mk'] at h
      exact h
    have h3 : X.map π = P := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) P
    rw [inf_of_le_left hNX, h2, h3] at h1
    exact h1.symm
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hP
  have hNne : Nat.card N ≠ 0 := Nat.card_pos.ne'
  have hSexp : Nat.card S = Nat.card P * 2 ^ (Nat.card N).factorization 2 := by
    rw [hcardS, hXcard, hj, factorization_two_mul_pow j _ hNne, pow_add]
  have hmapeq : Nat.card ↥(S.map π) = Nat.card P := by
    have h := hrel
    rw [hkerπ, hRcard', hSexp] at h
    exact Nat.eq_of_mul_eq_mul_right (pow_pos two_pos _) h
  have hPS : S.map π ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact hSX_le hx
  have hSP : S.map π = P := Subgroup.eq_of_le_of_card_ge hPS (le_of_eq hmapeq.symm)
  exact ⟨S, hSX_le, hS2, hcardS, hSP⟩


theorem frattini_step {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (P : Subgroup (Y ⧸ N)) (S : Subgroup Y) (hSX : S ≤ P.comap (QuotientGroup.mk' N))
    (hS2 : IsPGroup 2 S)
    (hcardS : Nat.card S = 2 ^ (Nat.card ↥(P.comap (QuotientGroup.mk' N))).factorization 2)
    (m : Y) (hm : QuotientGroup.mk' N m ∈ Subgroup.normalizer (P : Set (Y ⧸ N))) :
    ∃ n x : Y, x ∈ P.comap (QuotientGroup.mk' N) ∧ m = n * x ∧
      n ∈ Subgroup.normalizer (S : Set Y) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  set X : Subgroup Y := P.comap π with hX
  set Mπ : Subgroup Y := (Subgroup.normalizer (P : Set (Y ⧸ N))).comap π with hMπ
  have hXM : X ≤ Mπ := by
    intro x hx
    exact Subgroup.le_normalizer hx
  have hSM : S ≤ Mπ := hSX.trans hXM
  have hXn : (X.subgroupOf Mπ).Normal := by
    constructor
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hg : π (g : Y) ∈ Subgroup.normalizer (P : Set (Y ⧸ N)) := g.2
    have hx' : π (x : Y) ∈ P := hx
    have key := (Subgroup.mem_normalizer_iff.1 hg (π x)).1 hx'
    show π ((g : Y) * (x : Y) * (g : Y)⁻¹) ∈ P
    rw [map_mul, map_mul, map_inv]
    exact key
  set X' : Subgroup Mπ := X.subgroupOf Mπ with hX'
  haveI : X'.Normal := hXn
  set S'' : Subgroup Mπ := S.subgroupOf Mπ with hS''
  have hS''X : S'' ≤ X' := by
    intro s hs
    rw [hX', Subgroup.mem_subgroupOf]
    exact hSX (Subgroup.mem_subgroupOf.1 hs)
  have hS''2 : IsPGroup 2 S'' := IsPGroup.comap_subtype hS2
  set SS' : Subgroup ↥X' := S''.subgroupOf X' with hSS'
  have hSS'2 : IsPGroup 2 SS' := IsPGroup.comap_subtype hS''2
  have hcardX' : Nat.card ↥X' = Nat.card ↥X := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXM).toEquiv
  have hcardSS' : Nat.card ↥SS' = Nat.card ↥S := by
    rw [hSS', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS''X).toEquiv]
    rw [hS'', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSM).toEquiv]
  let SS : Sylow 2 ↥X' := sylowOfCard SS' hSS'2 (by rw [hcardSS', hcardX']; exact hcardS)
  have hsup := Sylow.normalizer_sup_eq_top SS
  have hSSmap : (SS.toSubgroup).map X'.subtype = S'' := by
    show (SS' : Subgroup ↥X').map X'.subtype = S''
    rw [hSS', Subgroup.subgroupOf_map_subtype, inf_of_le_left hS''X]
  have hmM : m ∈ Mπ := hm
  have hg_top : (⟨m, hmM⟩ : Mπ) ∈ Subgroup.normalizer ((SS.toSubgroup).map X'.subtype : Set Mπ) ⊔ X' := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨h, hh, z, hz, hhz⟩ := Subgroup.mem_sup_of_normal_right.1 hg_top
  rw [hSSmap] at hh
  refine ⟨(h : Y), (z : Y), ?_, ?_, ?_⟩
  · have := hz
    rw [hX', Subgroup.mem_subgroupOf] at this
    exact this
  · have := congrArg Subtype.val hhz
    simp only [Subgroup.coe_mul] at this
    exact this.symm
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    by_cases hy : y ∈ Mπ
    · have key := Subgroup.mem_normalizer_iff.1 hh ⟨y, hy⟩
      have key2 := key
      rw [hS'', Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at key2
      simpa using key2
    · constructor
      · intro hyS
        exact absurd (hSM hyS) hy
      · intro hyS
        exfalso
        apply hy
        have hh' : (h : Y) ∈ Mπ := h.2
        have : y = (h : Y)⁻¹ * ((h : Y) * y * (h : Y)⁻¹) * (h : Y) := by group
        rw [this]
        exact Mπ.mul_mem (Mπ.mul_mem (Mπ.inv_mem hh') (hSM hyS)) hh'


theorem factorization_prime_pow_mul {p : ℕ} (hp : p.Prime) (k m : ℕ) (hm : ¬ p ∣ m) (hm0 : m ≠ 0) :
    (p ^ k * m).factorization p = k := by
  rw [Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow hp]
  simp [Nat.factorization_eq_zero_of_not_dvd hm]

theorem core_lift {Y : Type} [Group Y] [Finite Y] (N : Subgroup Y) [N.Normal]
    (h3 : ¬ 3 ∣ Nat.card ↥N) (P : Subgroup (Y ⧸ N)) (hP : IsPGroup 2 P) (hP1 : P ≠ ⊥)
    (E : Subgroup (Y ⧸ N)) (hEP : E ≤ Subgroup.normalizer (P : Set (Y ⧸ N)))
    (hE : CFSG.Open.IsElemAbelian 3 E) (k : ℕ) (hk : Nat.card ↥E = 3 ^ k) :
    ∃ S T : Subgroup Y, IsPGroup 2 S ∧ S ≠ ⊥ ∧ T ≤ Subgroup.normalizer (S : Set Y) ∧
      CFSG.Open.IsElemAbelian 3 T ∧ Nat.card ↥T = 3 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π : Y →* Y ⧸ N := QuotientGroup.mk' N with hπ
  obtain ⟨S₀, hS₀X, hS₀2, hS₀card, hS₀P⟩ := exists_sylow_lift N P hP
  set Mπ : Subgroup Y := (Subgroup.normalizer (P : Set (Y ⧸ N))).comap π with hMπ
  have hS₀M : S₀ ≤ Mπ := hS₀X.trans (Subgroup.comap_mono (Subgroup.le_normalizer))
  set M₁ : Subgroup Y := Subgroup.normalizer (S₀ : Set Y) ⊓ Mπ with hM₁
  have hPM : P ≤ M₁.map π := by
    intro q hq
    rw [← hS₀P] at hq
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hq
    refine Subgroup.mem_map.2 ⟨s, ⟨?_, hS₀M hs⟩, rfl⟩
    exact Subgroup.le_normalizer hs
  have hEM : E ≤ M₁.map π := by
    intro e he
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective N e
    have hm : π m ∈ Subgroup.normalizer (P : Set (Y ⧸ N)) := hEP he
    obtain ⟨n, x, hx, hmnx, hn⟩ := frattini_step N P S₀ hS₀X hS₀2 hS₀card m hm
    have hxP : π x ∈ P := hx
    have hnN : π n ∈ Subgroup.normalizer (P : Set (Y ⧸ N)) := by
      have : π n = π m * (π x)⁻¹ := by
        rw [hmnx, map_mul, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.mul_mem _ hm (Subgroup.inv_mem _ (Subgroup.le_normalizer hxP))
    have hnM₁ : n ∈ M₁ := ⟨hn, hnN⟩
    have hPx : π x ∈ M₁.map π := hPM hxP
    have hen : π m = π n * π x := by rw [hmnx, map_mul]
    rw [hen]
    exact Subgroup.mul_mem _ (Subgroup.mem_map_of_mem π hnM₁) hPx
  set P₀ : Subgroup Y := M₁ ⊓ E.comap π with hP₀
  have hP₀map : P₀.map π = E := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_comap.1 (Subgroup.mem_inf.1 hy).2)
    · intro e he
      obtain ⟨n, hn, hne⟩ := Subgroup.mem_map.1 (hEM he)
      refine Subgroup.mem_map.2 ⟨n, Subgroup.mem_inf.2 ⟨hn, ?_⟩, hne⟩
      show π n ∈ E
      rw [hne]
      exact he
  have hrelP : N.relIndex P₀ * Nat.card ↥(N ⊓ P₀) = Nat.card ↥P₀ := Subgroup.relIndex_mul_card N P₀
  have hrelP' : N.relIndex P₀ = Nat.card ↥(P₀.map π) := by
    have h := Subgroup.relIndex_ker P₀ π
    rw [QuotientGroup.ker_mk'] at h
    exact h
  rw [hP₀map, hk] at hrelP'
  have hm3 : ¬ 3 ∣ Nat.card ↥(N ⊓ P₀) := fun h => h3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hm0 : Nat.card ↥(N ⊓ P₀) ≠ 0 := Nat.card_pos.ne'
  have hP₀card : Nat.card ↥P₀ = 3 ^ k * Nat.card ↥(N ⊓ P₀) := by
    rw [← hrelP, hrelP']
  obtain ⟨T₀⟩ : Nonempty (Sylow 3 ↥P₀) := Sylow.nonempty
  have hT₀card : Nat.card ↥(T₀ : Subgroup ↥P₀) = 3 ^ k := by
    rw [Sylow.card_eq_multiplicity, hP₀card, factorization_prime_pow_mul Nat.prime_three k _ hm3 hm0]
  set T : Subgroup Y := (T₀ : Subgroup ↥P₀).map P₀.subtype with hT
  have hTcard : Nat.card ↥T = 3 ^ k := by
    rw [hT, Subgroup.card_map_of_injective P₀.subtype_injective, hT₀card]
  have hT3 : IsPGroup 3 T := T₀.isPGroup'.map P₀.subtype
  have hTP₀ : T ≤ P₀ := by
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hTN : T ⊓ N = ⊥ := by
    have h1 : IsPGroup 3 ↥(T ⊓ N) := IsPGroup.to_inf_left hT3
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 h1
    have hdvd : Nat.card ↥(T ⊓ N) ∣ Nat.card ↥N := Subgroup.card_dvd_of_le inf_le_right
    have ha0 : a = 0 := by
      by_contra hne
      have : 3 ∣ Nat.card ↥N := by
        rw [ha] at hdvd
        exact (dvd_pow_self 3 hne).trans hdvd
      exact h3 this
    rw [ha0, pow_zero] at ha
    exact Subgroup.eq_bot_of_card_eq _ ha
  have hinj : ∀ t ∈ T, π t = 1 → t = 1 := by
    intro t ht h1
    have hmem : t ∈ T ⊓ N := ⟨ht, (QuotientGroup.eq_one_iff t).1 h1⟩
    rw [hTN] at hmem
    exact (Subgroup.mem_bot.1 hmem)
  have hTE : ∀ t ∈ T, π t ∈ E := by
    intro t ht
    exact Subgroup.mem_comap.1 (Subgroup.mem_inf.1 (hTP₀ ht)).2
  have hTab : CFSG.Open.IsElemAbelian 3 T := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun t ht => ?_⟩
    · have hkey : π ((a : Y) * b) = π ((b : Y) * a) := by
        rw [map_mul, map_mul]
        have hc := hE.1.is_comm.comm (⟨π a, hTE a a.2⟩ : ↥E) ⟨π b, hTE b b.2⟩
        exact congrArg Subtype.val hc
      have hab : ((a : Y) * b) * ((b : Y) * a)⁻¹ = 1 := by
        apply hinj
        · exact T.mul_mem (T.mul_mem a.2 b.2) (T.inv_mem (T.mul_mem b.2 a.2))
        · rw [map_mul, map_inv, hkey, mul_inv_cancel]
      apply Subtype.ext
      exact (mul_inv_eq_one.1 hab)
    · apply hinj
      · exact T.pow_mem ht 3
      · rw [map_pow]
        exact hE.2 (π t) (hTE t ht)
  have hTnorm : T ≤ Subgroup.normalizer (S₀ : Set Y) := by
    intro t ht
    exact (Subgroup.mem_inf.1 (hTP₀ ht)).1.1
  have hS₀ne : S₀ ≠ ⊥ := by
    intro h
    apply hP1
    rw [← hS₀P, h, Subgroup.map_bot]
  exact ⟨S₀, T, hS₀2, hS₀ne, hTnorm, hTab, hTcard⟩


theorem exists_elemAbelian_of_pRank_ge {H : Type} [Group H] [Finite H] (M : Subgroup H)
    (h5 : 5 ≤ CFSG.Open.pRank 3 M) :
    ∃ E : Subgroup H, E ≤ M ∧ CFSG.Open.IsElemAbelian 3 E ∧ ∃ k : ℕ, 5 ≤ k ∧ Nat.card E = 3 ^ k := by
  have hbdd := pRank_bddAbove 3 Nat.prime_three M
  have hne : {k | ∃ E : Subgroup H, E ≤ M ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}.Nonempty := by
    by_contra hem
    rw [Set.not_nonempty_iff_eq_empty] at hem
    have h0 : CFSG.Open.pRank 3 M = 0 := by
      unfold CFSG.Open.pRank
      rw [hem, csSup_empty]
      rfl
    omega
  have hmem := Nat.sSup_mem hne hbdd
  obtain ⟨E, hEM, hE, hcard⟩ := hmem
  refine ⟨E, hEM, hE, sSup {k | ∃ E : Subgroup H, E ≤ M ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k}, ?_, hcard⟩
  have : CFSG.Open.pRank 3 M = sSup {k | ∃ E : Subgroup H, E ≤ M ∧ CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} := rfl
  omega

theorem lift_twoLocal_rank {G : Type} [Group G] [Finite G] {C K : Subgroup G} (hKC : K ≤ C)
    (M : Subgroup (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 K)) (hM : CFSG.Open.IsTwoLocal M)
    (h5 : 5 ≤ CFSG.Open.pRank 3 M) : 5 ≤ CFSG.Open.twoLocalPrimeRank 3 ↥C := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : (CFSG.pPrimeCore 3 ↥K).Normal := CFSG.pPrimeCore_normal
  obtain ⟨P, hP1, hP2, hMP⟩ := hM
  obtain ⟨E, hEM, hE, k, hk5, hkcard⟩ := exists_elemAbelian_of_pRank_ge M h5
  have hN3 : ¬ 3 ∣ Nat.card ↥(CFSG.pPrimeCore 3 ↥K) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 CFSG.pPrimeCore_coprime_card
  have hEP : E ≤ Subgroup.normalizer (P : Set (CFSG.Yardstones.Md0ec50421ce4.PQuot 3 K)) := by
    rw [← hMP]
    exact hEM
  obtain ⟨S, T, hS2, hSne, hTnorm, hTab, hTcard⟩ :=
    core_lift (CFSG.pPrimeCore 3 ↥K) hN3 P hP2 hP1 E hEP hE k hkcard
  let inc : ↥K →* ↥C := Subgroup.inclusion hKC
  have hinc : Function.Injective inc := Subgroup.inclusion_injective hKC
  set SC : Subgroup ↥C := S.map inc with hSC
  set TC : Subgroup ↥C := T.map inc with hTC
  have hSC2 : IsPGroup 2 SC := hS2.map inc
  have hSCne : SC ≠ ⊥ := by
    intro h
    apply hSne
    ext x
    constructor
    · intro hx
      have h1 : inc x ∈ SC := Subgroup.mem_map_of_mem inc hx
      rw [h, Subgroup.mem_bot] at h1
      exact Subgroup.mem_bot.2 (hinc (h1.trans (map_one inc).symm))
    · intro hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact S.one_mem
  have hTCnorm : TC ≤ Subgroup.normalizer (SC : Set ↥C) := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hn := Subgroup.mem_normalizer_iff.1 (hTnorm ht')
    constructor
    · intro hg
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hg
      refine Subgroup.mem_map.2 ⟨t' * s * t'⁻¹, (hn s).1 hs, ?_⟩
      simp [map_mul, map_inv]
    · intro hg
      obtain ⟨s', hs', hs'g⟩ := Subgroup.mem_map.1 hg
      have hgeq : g = (inc t')⁻¹ * inc s' * inc t' := by
        rw [hs'g]
        group
      refine Subgroup.mem_map.2 ⟨t'⁻¹ * s' * t', ?_, ?_⟩
      · refine (hn (t'⁻¹ * s' * t')).2 ?_
        simpa [mul_assoc] using hs'
      · rw [hgeq]
        simp [map_mul, map_inv]
  have hTCab : CFSG.Open.IsElemAbelian 3 TC := isElemAbelian_map inc hTab
  have hTCcard : Nat.card ↥TC = 3 ^ k := by
    rw [hTC, Subgroup.card_map_of_injective hinc, hTcard]
  have hMC : CFSG.Open.IsTwoLocal (Subgroup.normalizer (SC : Set ↥C)) :=
    ⟨SC, hSCne, hSC2, rfl⟩
  have hk : k ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (SC : Set ↥C)) :=
    le_pRank 3 Nat.prime_three hTCnorm hTCab hTCcard
  exact le_twoLocalPrimeRank 3 Nat.prime_three hMC (le_trans hk5 hk)

end Ranks

end CFSG.LocalAnalysis.GLTheoremA.I141F
