module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Lemma86Aux1
public import CFSG.LocalAnalysis.GLTheoremB.PQuotientTools

public section

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type} [Group G] [Finite G]

namespace LinPkg

variable {Q N : Subgroup G} (P : LinPkg Q N)

theorem not_dvd_card_ker {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) :
    ¬ p ∣ Nat.card P.ρ.ker := by
  obtain ⟨k, hk⟩ := (P.isPGroup_ker hQ2).exists_card_eq
  rw [hk]
  intro h
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))

theorem pRank_range_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) :
    CFSG.Open.pRank p P.ρ.range ≤ CFSG.Open.pRank p N := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : 1 < p := hp.one_lt
  have e1 := pRank_eq_pRank_top_subtype h1 P.ρ.range
  have e2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := p) h1
    (QuotientGroup.quotientKerEquivRange P.ρ).symm
  have e3 := CFSG.SectionRank.pRank_quotient_eq (p := p) P.ρ.ker (P.not_dvd_card_ker hp hp2 hQ2)
  have e4 := pRank_eq_pRank_top_subtype h1 N
  omega

@[expose] def rB {B : Subgroup G} (hBN : B ≤ N) : ↥B →* MulAut P.V :=
  P.ρ.comp (Subgroup.inclusion hBN)

omit [Finite G] in
theorem rB_apply {B : Subgroup G} (hBN : B ≤ N) (b : B) : P.rB hBN b = P.ρ ⟨b, hBN b.2⟩ := rfl

omit [Finite G] in
theorem rB_injective {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q) {B : Subgroup G}
    (hBN : B ≤ N) (hBel : IsElemAbelian p B) : Function.Injective (P.rB hBN) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro b hb
  rw [MonoidHom.mem_ker, rB_apply] at hb
  have h1 : (⟨(b : G), hBN b.2⟩ : N) ^ p = 1 := Subtype.ext (hBel.2 b b.2)
  have := P.eq_one_of_pow_eq_one hQ2 hp hp2 h1 hb
  exact Subgroup.mem_bot.2 (Subtype.ext (by simpa using congrArg Subtype.val this))

@[expose] def liftB {B : Subgroup G} (hBN : B ≤ N) (F' : Subgroup (MulAut P.V)) : Subgroup G :=
  (F'.comap (P.rB hBN)).map B.subtype

omit [Finite G] in
theorem liftB_le {B : Subgroup G} (hBN : B ≤ N) (F' : Subgroup (MulAut P.V)) :
    P.liftB hBN F' ≤ B := Subgroup.map_subtype_le _

omit [Finite G] in
theorem card_liftB {B : Subgroup G} (hBN : B ≤ N) (hinj : Function.Injective (P.rB hBN))
    {F' : Subgroup (MulAut P.V)} (hF' : F' ≤ (P.rB hBN).range) :
    Nat.card (P.liftB hBN F') = Nat.card F' := by
  unfold liftB
  rw [Subgroup.card_map_of_injective B.subtype_injective]
  have h1 : (F'.comap (P.rB hBN)).map (P.rB hBN) = F' :=
    Subgroup.map_comap_eq_self (by simpa using hF')
  have h2 := Subgroup.card_map_of_injective (f := P.rB hBN) (K := F'.comap (P.rB hBN)) hinj
  rw [h1] at h2
  exact h2.symm

omit [Finite G] in
theorem map_liftB {B : Subgroup G} (hBN : B ≤ N) {F' : Subgroup (MulAut P.V)}
    (hF' : F' ≤ (P.rB hBN).range) :
    ((P.liftB hBN F').subgroupOf N).map P.ρ = F' := by
  ext y
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain ⟨b, hb, hbn⟩ := Subgroup.mem_subgroupOf.1 hn
    have : P.ρ n = P.rB hBN b := by
      rw [rB_apply]
      congr 1
      exact Subtype.ext hbn.symm
    rw [this]
    exact hb
  · intro hy
    obtain ⟨b, rfl⟩ := hF' hy
    refine ⟨⟨b, hBN b.2⟩, ?_, rfl⟩
    exact Subgroup.mem_subgroupOf.2 ⟨b, hy, rfl⟩

omit [Finite G] in
theorem liftB_isElemAbelian {p : ℕ} {B : Subgroup G} (hBN : B ≤ N) (hBel : IsElemAbelian p B)
    (F' : Subgroup (MulAut P.V)) : IsElemAbelian p (P.liftB hBN F') :=
  isElemAbelian_mono hBel (P.liftB_le hBN F')

theorem exists_mem_normalizer_mul {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q)
    {E : Subgroup G} (hEN : E ≤ N) (hE : IsPGroup p E) {n : N}
    (hn : P.ρ n ∈ Subgroup.normalizer
      (((E.subgroupOf N).map P.ρ : Subgroup (MulAut P.V)) : Set (MulAut P.V))) :
    ∃ n₁ ∈ Subgroup.normalizer (E : Set G), (n₁⁻¹ * (n : G)) ∈ Q := by
  have : Fact p.Prime := ⟨hp⟩
  set K : Subgroup ↥N := P.ρ.ker with hK
  set Es : Subgroup ↥N := E.subgroupOf N with hEs
  have hEsp : IsPGroup p Es :=
    IsPGroup.of_equiv hE (Subgroup.subgroupOfEquivOfLe hEN).symm
  set Eb : Subgroup (↥N ⧸ K) := Es.map (QuotientGroup.mk' K) with hEb
  have hmem : ∀ w : N, QuotientGroup.mk' K w ∈ Eb ↔ P.ρ w ∈ Es.map P.ρ := by
    intro w
    constructor
    · rintro ⟨s, hs, hsw⟩
      have h1 : s⁻¹ * w ∈ K := (QuotientGroup.eq).1 hsw
      have h2 : P.ρ s = P.ρ w := by
        have := (MonoidHom.mem_ker).1 h1
        rw [map_mul, map_inv, inv_mul_eq_one] at this
        exact this
      exact ⟨s, hs, h2⟩
    · rintro ⟨s, hs, hsw⟩
      refine ⟨s, hs, (QuotientGroup.eq).2 ?_⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsw, inv_mul_cancel]
  have hnb : QuotientGroup.mk' K n ∈ Subgroup.normalizer (Eb : Set (↥N ⧸ K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
    have e1 : QuotientGroup.mk' K n * QuotientGroup.mk' K w * (QuotientGroup.mk' K n)⁻¹ =
        QuotientGroup.mk' K (n * w * n⁻¹) := by simp
    have e2 : (w : ↥N ⧸ K) = QuotientGroup.mk' K w := rfl
    rw [e2, e1, hmem, hmem]
    have := Subgroup.mem_normalizer_iff.1 hn (P.ρ w)
    rw [map_mul, map_mul, map_inv]
    exact this
  have hcop : ¬ p ∣ Nat.card K := P.not_dvd_card_ker hp hp2 hQ2
  obtain ⟨n₁, hn₁, hn₁e⟩ := normalizer_map_quotient_le K hcop hEsp hnb
  refine ⟨(n₁ : G), ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    have hn1 := Subgroup.mem_normalizer_iff.1 hn₁
    constructor
    · intro hh
      have := (hn1 ⟨h, hEN hh⟩).1 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
    · intro hh
      have hhN : h ∈ N := by
        have h1 : (n₁ : G)⁻¹ * ((n₁ : G) * h * (n₁ : G)⁻¹) * (n₁ : G) ∈ N :=
          N.mul_mem (N.mul_mem (N.inv_mem n₁.2) (hEN hh)) n₁.2
        simpa [mul_assoc] using h1
      have := (hn1 ⟨h, hhN⟩).2 (Subgroup.mem_subgroupOf.2 hh)
      exact Subgroup.mem_subgroupOf.1 this
  · have h1 : n₁⁻¹ * n ∈ K := (QuotientGroup.eq).1 hn₁e
    exact (P.ker_iff _).1 ((MonoidHom.mem_ker).1 h1)

theorem coreIn_le_map {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ2 : IsPGroup 2 Q)
    {B M₀ : Subgroup G} (hBN : B ≤ N) (hBel : IsElemAbelian p B) (hQM : Q ≤ M₀)
    (hnorm : ∀ E : Subgroup G, E ≤ B → 3 ≤ CFSG.Open.pRank p E →
      Subgroup.normalizer (E : Set G) ≤ M₀) (hk : 3 ≤ k) :
    Coordinator.coreIn p k (P.rB hBN).range P.ρ.range ≤ (M₀.subgroupOf N).map P.ρ := by
  have hp1 : 1 < p := hp.one_lt
  have hinj := P.rB_injective hp hp2 hQ2 hBN hBel
  refine iSup₂_le fun E' hE' => ?_
  rintro x ⟨hxX, hxN⟩
  obtain ⟨n, rfl⟩ := hxX
  set E := P.liftB hBN E' with hE
  have hEB : E ≤ B := P.liftB_le hBN E'
  have hEel : IsElemAbelian p E := P.liftB_isElemAbelian hBN hBel E'
  have hEp : IsPGroup p E := fun g => ⟨1, by rw [pow_one]; exact Subtype.ext (hEel.2 g.1 g.2)⟩
  have hmap : (E.subgroupOf N).map P.ρ = E' := P.map_liftB hBN hE'.1
  have hrk : 3 ≤ CFSG.Open.pRank p E := by
    refine hk.trans (hE'.2.trans ?_)
    obtain ⟨F', hF'E', hF'el, hF'card⟩ := CFSG.SectionRank.exists_pRank hp1 E'
    have hF'r : F' ≤ (P.rB hBN).range := hF'E'.trans hE'.1
    refine CFSG.SectionRank.le_pRank hp1 (E := P.liftB hBN F') ?_
      (P.liftB_isElemAbelian hBN hBel F') ?_
    · exact Subgroup.map_mono (Subgroup.comap_mono hF'E')
    · rw [P.card_liftB hBN hinj hF'r, hF'card]
  have hn : P.ρ n ∈ Subgroup.normalizer
      (((E.subgroupOf N).map P.ρ : Subgroup (MulAut P.V)) : Set (MulAut P.V)) := by
    rw [hmap]; exact hxN
  obtain ⟨n₁, hn₁, hk₁⟩ := P.exists_mem_normalizer_mul hp hp2 hQ2 (hEB.trans hBN) hEp hn
  have hn₁M : n₁ ∈ M₀ := hnorm E hEB hrk hn₁
  have : (n : G) ∈ M₀ := by
    have h2 : (n : G) = n₁ * (n₁⁻¹ * (n : G)) := by group
    rw [h2]
    exact M₀.mul_mem hn₁M (hQM hk₁)
  exact ⟨n, Subgroup.mem_subgroupOf.2 this, rfl⟩

omit [Finite G] in
theorem mem_of_mem_map {M₀ : Subgroup G} (hQM : Q ≤ M₀) {n : N}
    (hn : P.ρ n ∈ (M₀.subgroupOf N).map P.ρ) : (n : G) ∈ M₀ := by
  obtain ⟨m₀, hm₀, hm₀n⟩ := hn
  have h1 : m₀⁻¹ * n ∈ P.ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hm₀n, inv_mul_cancel]
  have h2 : ((m₀⁻¹ * n : N) : G) ∈ Q := (P.ker_iff _).1 ((MonoidHom.mem_ker).1 h1)
  have h3 : (n : G) = (m₀ : G) * (((m₀⁻¹ * n : N)) : G) := by simp
  rw [h3]
  exact M₀.mul_mem (Subgroup.mem_subgroupOf.1 hm₀) (hQM h2)

end LinPkg

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
