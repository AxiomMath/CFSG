module

public import CFSG.LocalAnalysis.GH72.Sec5CBar
public import CFSG.LocalAnalysis.ABGTheoremB.V4Hall
public import CFSG.GroupTheory.SylowNormalIndex
public import CFSG.GroupTheory.CoprimeCosetFixed
public import CFSG.LocalAnalysis.GH72.Sec5DBasic

public section

namespace CFSG.GH72

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

section Preimage

variable {G : Type} [Group G] [Finite G] {H : Subgroup G} (Tb : Subgroup (Bar H))

omit [Finite G] in
theorem mem_comap_map_of_mk_mem {g : G} (hg : g ∈ H)
    (h : (QuotientGroup.mk (⟨g, hg⟩ : H) : Bar H) ∈ Tb) :
    g ∈ (Tb.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype :=
  ⟨⟨g, hg⟩, h, rfl⟩

omit [Finite G] in
theorem bar_comap_map :
    bar H ((Tb.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype) = Tb := by
  rw [bar, Subgroup.subgroupOf, comap_map_eq_self_of_injective H.subtype_injective,
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]

theorem odd_card_comap_map (hTb : Odd (Nat.card Tb)) :
    Odd (Nat.card ((Tb.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card'
    (G := ((Tb.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype)) 2 h2
  have hx2 : (x : G) * x = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx, pow_two] at this
    exact congrArg Subtype.val this
  obtain ⟨y, hy, hyx⟩ := x.2
  have hyx' : (y : G) = x := hyx
  have hy2 : y * y = 1 := Subtype.ext (by
    show (y : G) * y = 1
    rw [hyx']
    exact hx2)
  have hπy : QuotientGroup.mk' (CFSG.oddCore H) y = 1 :=
    eq_one_of_mul_self_of_odd hTb hy (by rw [← map_mul, hy2, map_one])
  have hyO : (y : G) ∈ O H := (mk_eq_one_iff y).mp hπy
  have hy1 : (y : G) = 1 := eq_one_of_mul_self_of_odd (card_O_odd H) hyO
    (congrArg Subtype.val hy2)
  have : x = 1 := Subtype.ext (by rw [← hyx]; exact hy1)
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

theorem le_normalizer_comap_map {L : Subgroup G} (hLH : L ≤ H)
    (hL : bar H L ≤ normalizer (Tb : Set (Bar H))) :
    L ≤ normalizer (((Tb.comap (QuotientGroup.mk' (CFSG.oddCore H))).map H.subtype :
      Subgroup G) : Set G) := by
  intro l hl
  apply mem_normalizer_of_forall_conj_mem
  rintro _ ⟨r, hr, rfl⟩
  refine ⟨⟨l, hLH hl⟩ * r * (⟨l, hLH hl⟩ : H)⁻¹, ?_, rfl⟩
  have hlb : QuotientGroup.mk' (CFSG.oddCore H) ⟨l, hLH hl⟩ ∈ bar H L := ⟨⟨l, hLH hl⟩, hl, rfl⟩
  show QuotientGroup.mk' (CFSG.oddCore H) (⟨l, hLH hl⟩ * r * (⟨l, hLH hl⟩ : H)⁻¹) ∈ Tb
  rw [map_mul, map_mul, map_inv]
  exact (mem_normalizer_iff.mp (hL hlb) _).mp hr

omit [Finite G] in
theorem bar_zpowers_le {x : G} (hx : x ∈ H) :
    bar H (zpowers x) ≤ zpowers (QuotientGroup.mk (⟨x, hx⟩ : H) : Bar H) := by
  rintro _ ⟨⟨g, hgH⟩, hg, rfl⟩
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp (show g ∈ zpowers x from hg)
  refine mem_zpowers_iff.mpr ⟨n, ?_⟩
  have e : (⟨g, hgH⟩ : H) = (⟨x, hx⟩ : H) ^ n :=
    Subtype.ext (by rw [Subgroup.coe_zpow]; exact hn.symm)
  rw [e, map_zpow]
  rfl

end Preimage

section Sylow

variable {G : Type} [Group G] [Finite G]

theorem le_of_isPGroup_of_le_sup {N P R : Subgroup G} {p t : ℕ} (hp : p.Prime) (ht : t.Prime)
    (htp : t ≠ p) (hP : IsPGroup p P) (hPN : P ≤ normalizer (N : Set G)) (hR : IsPGroup t R)
    (hRN : R ≤ N ⊔ P) : R ≤ N := by
  have : Fact t.Prime := ⟨ht⟩
  have : Fact p.Prime := ⟨hp⟩
  refine le_of_isPGroup_of_not_dvd_relIndex hR hRN le_sup_left (sup_le le_normalizer hPN) ?_
  intro hdvd
  have h1 := Subgroup.relIndex_mul_card N (N ⊔ P)
  rw [inf_eq_left.mpr le_sup_left] at h1
  have h2 := CFSG.ABGTheoremB.card_sup_mul_card_inf_of_le_normalizer hPN
  have h3 : N.relIndex (N ⊔ P) * Nat.card (N ⊓ P : Subgroup G) = Nat.card P := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := N))
    calc Nat.card N * (N.relIndex (N ⊔ P) * Nat.card (N ⊓ P : Subgroup G))
        = N.relIndex (N ⊔ P) * Nat.card N * Nat.card (N ⊓ P : Subgroup G) := by ring
      _ = Nat.card N * Nat.card P := by rw [h1, h2]
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have h4 : t ∣ p ^ n := by
    rw [← hn, ← h3]
    exact hdvd.mul_right _
  exact htp ((Nat.prime_dvd_prime_iff_eq ht hp).mp (ht.dvd_of_dvd_pow h4))

end Sylow

section Hall

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowOf_mul_comm {A L P T₀ : Subgroup G} {p t : ℕ} (hp : p.Prime)
    (ht : t.Prime) (htp : t ≠ p) (hA : IsPGroup 2 A) (hAL : A ≤ normalizer (L : Set G))
    (hL : Odd (Nat.card L)) (hP : IsSylowOf p P L) (hAP : A ≤ normalizer (P : Set G))
    (hT₀ : IsPGroup t T₀) (hT₀L : T₀ ≤ L) (hPT₀ : P ≤ normalizer (T₀ : Set G))
    (hAT₀ : A ≤ normalizer (T₀ : Set G)) :
    ∃ T K : Subgroup G, IsSylowOf t T L ∧ T₀ ≤ T ∧ A ≤ normalizer (T : Set G) ∧
      (T : Set G) * (P : Set G) = (P : Set G) * (T : Set G) ∧ T ≤ K ∧ P ≤ K ∧ K ≤ L ∧
      ∀ d : ℕ, d.Prime → d ∣ Nat.card K → d = t ∨ d = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact t.Prime := ⟨ht⟩
  have hUL : T₀ ⊔ P ≤ L := sup_le hT₀L hP.le
  have hAU : A ≤ normalizer ((T₀ ⊔ P : Subgroup G) : Set G) :=
    (le_inf hAT₀ hAP).trans (CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _)
  have hUcard : Nat.card (T₀ ⊔ P : Subgroup G) ∣ Nat.card T₀ * Nat.card P :=
    Dvd.intro _ (CFSG.ABGTheoremB.card_sup_mul_card_inf_of_le_normalizer hPT₀)
  obtain ⟨n₁, hn₁⟩ := hT₀.exists_card_eq
  obtain ⟨n₂, hn₂⟩ := hP.isPGroup.exists_card_eq
  have hUπ : ∀ q : Nat.Primes, (q : ℕ) ∣ Nat.card (T₀ ⊔ P : Subgroup G) →
      q ∈ {q : Nat.Primes | (q : ℕ) = t ∨ (q : ℕ) = p} := by
    intro q hq
    have h := hq.trans hUcard
    rw [hn₁, hn₂] at h
    rcases (Nat.Prime.dvd_mul q.2).mp h with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq q.2 ht).mp (q.2.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq q.2 hp).mp (q.2.dvd_of_dvd_pow h))
  obtain ⟨K, hKL, hUK, hAK, hKπ, hKidx⟩ :=
    CFSG.ABGTheoremB.V4.exists_invariant_hall hA hAL hL hUL hAU _ hUπ
  have hKodd : Odd (Nat.card K) := hL.of_dvd_nat (card_dvd_of_le hKL)
  obtain ⟨T, hT, hT₀T, hAT⟩ := CFSG.ABGTheoremB.exists_isSylowOf_normalized_ge_of_odd ht hA hAK
    hKodd (le_sup_left.trans hUK) hT₀ hAT₀
  have hPK : P ≤ K := le_sup_right.trans hUK
  have hKprimes : ∀ d : ℕ, d.Prime → d ∣ Nat.card K → d = t ∨ d = p :=
    fun d hd hdK => hKπ ⟨d, hd⟩ hdK
  obtain ⟨h1, h2⟩ :=
    CFSG.ABGTheoremB.V4.coe_eq_mul_of_isSylowOf htp hT (hP.of_le hPK hKL) hKprimes
  refine ⟨T, K, ?_, hT₀T, hAT, h1.symm.trans h2, hT.le, hPK, hKL, hKprimes⟩
  rw [isSylowOf_iff] at hT ⊢
  refine ⟨hT.1.trans hKL, hT.2.1, ?_⟩
  rw [← relIndex_mul_relIndex T K L hT.1 hKL]
  exact ht.not_dvd_mul hT.2.2 (hKidx ⟨t, ht⟩ (Or.inl rfl))

end Hall

section Involution

variable {G : Type} [Group G] [Finite G]

theorem O_C_inf_le_O {H : Subgroup G} {x : G} (hxH : x ∈ H) (hx : x * x = 1)
    (hHx : ∀ h ∈ H, h * x * h⁻¹ * x⁻¹ ∈ O H) : O (C x) ⊓ H ≤ O H := by
  have hfix : ∀ h ∈ H, ∃ n ∈ O H, h * n ∈ C x := by
    intro h hh
    have hN : ∀ n ∈ O H, x * n * x⁻¹ ∈ O H := fun n hn =>
      (mem_normalizer_iff.mp (le_normalizer_O H hxH) n).mp hn
    have hg : h⁻¹ * (x * h * x⁻¹) ∈ O H := by
      have := hHx h⁻¹ (inv_mem hh)
      simpa [mul_assoc] using this
    have hcop : Nat.Coprime (orderOf x) (Nat.card (O H)) :=
      (Nat.coprime_two_left.mpr (card_O_odd H)).coprime_dvd_left
        (orderOf_dvd_of_pow_eq_one (by rw [pow_two, hx]))
    obtain ⟨n, hn, hfx⟩ := CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime (O H) hN hg hcop
    refine ⟨n, hn, mem_centralizer_singleton_iff.mpr ?_⟩
    calc h * n * x = x * (h * n) * x⁻¹ * x := by rw [hfx]
      _ = x * (h * n) := by group
  set D : Subgroup G := O (C x) ⊓ H with hDdef
  set N : Subgroup G := O H ⊔ D with hNdef
  have hDH : D ≤ H := inf_le_right
  have hNodd : Odd (Nat.card N) :=
    CFSG.ABGTheoremB.odd_card_sup_of_le_normalizer_of_odd (hDH.trans (le_normalizer_O H))
      (card_O_odd H) ((card_O_odd _).of_dvd_nat (card_dvd_of_le inf_le_left))
  have hNH : N ≤ H := sup_le (O_le H) hDH
  have hHN : H ≤ normalizer (N : Set G) := by
    intro h hh
    obtain ⟨n, hn, hc⟩ := hfix h hh
    have hcH : h * n ∈ H := mul_mem hh (O_le H hn)
    have hcD : h * n ∈ normalizer (D : Set G) :=
      inf_normalizer_le_normalizer_inf ⟨le_normalizer_O _ hc, le_normalizer hcH⟩
    have hcN : h * n ∈ normalizer (N : Set G) :=
      CFSG.ABGTheoremB.normalizer_inf_normalizer_le_normalizer_sup _ _
        ⟨le_normalizer_O H hcH, hcD⟩
    have hnN : n⁻¹ ∈ normalizer (N : Set G) := le_normalizer (inv_mem (mem_sup_left hn))
    have e : h = h * n * n⁻¹ := by group
    rw [e]
    exact mul_mem hcN hnN
  exact le_sup_right.trans (G5d.le_O_of_le_normalizer hNH hHN hNodd)

end Involution

end CFSG.GH72
