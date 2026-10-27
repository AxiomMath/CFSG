module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.RationalBound.DegreeTwelve
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.TwelveClassesThreeCentralizer
public import CFSG.CharacterTheory.Semidihedral.GL2Recognition.SevenCharacterSylowSupport
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Cyclotomic.GaloisBlockStability

public section

open scoped BigOperators Classical

namespace CFSG.Semidihedral.GL2Recognition

open CFSG.TwoRankLowerBound.Helpers CFSG.LyonsUnitaryFour IntermediateField
  CFSG.Semidihedral.Principal.GL2Columns
  CFSG.Semidihedral.Principal

section Galois

variable {G : Type*} [Group G] [Fintype G] (basis : FiniteIrreducibleCharacterBasis G)

theorem character_pow_eq_of_unique_degree {a : basis.index}
    (huniq : ∀ b, Module.finrank ℂ (basis.representation b).vector =
      Module.finrank ℂ (basis.representation a).vector → b = a)
    {k : ℕ} (hk : (Nat.card G).Coprime k) (g : G) :
    (basis.representation a).character (g ^ k) = (basis.representation a).character g := by
  obtain ⟨π, hπ⟩ := exists_perm_character_pow basis hk
  have hπa : π a = a := huniq _ (finrank_perm_eq basis hπ a)
  rw [← hπ a g, hπa]

theorem character_rat_of_unique_degree {a : basis.index}
    (huniq : ∀ b, Module.finrank ℂ (basis.representation b).vector =
      Module.finrank ℂ (basis.representation a).vector → b = a)
    (g : G) : ∃ q : ℚ, (basis.representation a).character g = q := by
  have hN : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hζ := Complex.isPrimitiveRoot_exp (Nat.card G) Nat.card_pos.ne'
  have : IsCyclotomicExtension {Nat.card G} ℚ
      ℚ⟮Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))⟯ :=
    isCyclotomicExtension_adjoin_primitiveRoot hζ
  have : NumberField ℚ⟮Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))⟯ :=
    IsCyclotomicExtension.numberField {Nat.card G} ℚ _
  have : IsGalois ℚ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))⟯ :=
    IsCyclotomicExtension.isGalois {Nat.card G} ℚ _
  have hgN : g ^ Nat.card G = 1 := pow_card_eq_one'
  set F' : IntermediateField ℚ ℚ⟮Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))⟯ :=
    IntermediateField.restrict (bot_le : (⊥ : IntermediateField ℚ ℂ) ≤ _)
  have hmem : (⟨(basis.representation a).character g, character_mem_adjoin hζ _ hgN⟩ :
      ℚ⟮Complex.exp (2 * Real.pi * Complex.I / (Nat.card G))⟯) ∈ F' := by
    rw [← IsGalois.fixedField_fixingSubgroup F', IntermediateField.mem_fixedField_iff]
    intro σ _
    obtain ⟨k, hk, hσ⟩ := exists_galois_gen_eq_pow_coprime hζ σ
    apply Subtype.ext
    rw [galois_character_eq hζ hσ (basis.representation a).representation hgN]
    exact character_pow_eq_of_unique_degree basis huniq hk.symm g
  have h := (IntermediateField.mem_restrict _ _).mp hmem
  obtain ⟨q, hq⟩ := IntermediateField.mem_bot.mp h
  exact ⟨q, hq.symm⟩

end Galois

section Sums

variable {G : Type*} [Group G] [Fintype G]

theorem sum_conjClass {f : G → ℂ} (hf : ∀ g h : G, f (h * g * h⁻¹) = f g) (x : G) :
    ∑ g ∈ Finset.univ.filter (fun g => IsConj g x), f g =
      (Nat.card (ConjClasses.mk x).carrier : ℂ) * f x := by
  have hcard : (Finset.univ.filter fun g => IsConj g x).card =
      Nat.card (ConjClasses.mk x).carrier := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
    congr 1
    ext g
    simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  rw [Finset.sum_congr rfl fun g hg => ?_, Finset.sum_const, nsmul_eq_mul, hcard]
  obtain ⟨c, hc⟩ := isConj_iff.mp (Finset.mem_filter.mp hg).2
  rw [← hc]
  exact (hf g c).symm

end Sums

section Values

theorem sum_filter_const {A : Type*} {s : Finset A} {F : A → ℚ} {c : ℚ}
    (h : ∀ g ∈ s, F g = c) : ∑ g ∈ s, F g = s.card * c := by
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]


theorem sum_split_orders {G : Type*} [Group G] [Fintype G] (F : G → ℚ)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ)) :
    ∑ g, F g = F 1 + ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 2), F g +
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 3), F g +
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 4), F g +
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 6), F g +
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 8), F g +
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 13), F g := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := orderOf) (t := ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ))
    (fun g _ => horders g)]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h1 : Finset.univ.filter (fun g : G => orderOf g = 1) = {1} := by
    ext g
    simp [orderOf_eq_one_iff]
  rw [h1, Finset.sum_singleton]
  ring

theorem card_filter_isConj {G : Type*} [Group G] [Fintype G] (x : G) :
    (Finset.univ.filter fun g => IsConj g x).card = Nat.card (ConjClasses.mk x).carrier := by
  rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]
  congr 1
  ext g
  simp [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]

theorem card_filter_orderOf {G : Type*} [Group G] [Fintype G] (d : ℕ) :
    (Finset.univ.filter fun g : G => orderOf g = d).card = Nat.card {g : G // orderOf g = d} := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

set_option maxHeartbeats 1000000 in
theorem unique_degree_twelve_values_core {G : Type} [Group G] [Fintype G] [IsSimpleGroup G]
    (hG : Nat.card G = 5616)
    (horders : ∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ))
    (h2c : Nat.card {g : G // orderOf g = 2} = 117)
    (h2conj : ∀ u v : G, orderOf u = 2 → orderOf v = 2 → IsConj u v)
    (h4c : Nat.card {g : G // orderOf g = 4} = 702)
    (h4conj : ∀ u v : G, orderOf u = 4 → orderOf v = 4 → IsConj u v)
    (h6c : Nat.card {g : G // orderOf g = 6} = 936)
    (h6conj : ∀ u v : G, orderOf u = 6 → orderOf v = 6 → IsConj u v)
    (h8c : Nat.card {g : G // orderOf g = 8} = 1404)
    (h8cls : ∀ g : G, orderOf g = 8 → Nat.card (ConjClasses.mk g).carrier = 702)
    (h13c : Nat.card {g : G // orderOf g = 13} = 1728)
    (x y : G) (hx : orderOf x = 3) (hy : orderOf y = 3)
    (hxc : Nat.card (ConjClasses.mk x).carrier = 104)
    (hyc : Nat.card (ConjClasses.mk y).carrier = 624)
    (h3 : ∀ z : G, orderOf z = 3 → IsConj z x ∨ IsConj z y)
    (χ : G → ℂ) (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 12)
    (huniq : ∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 12 → ψ = χ) :
    (∀ g, ∃ q : ℚ, χ g = q) ∧ (∀ g, χ g = 12 → g = 1) ∧
    χ x = 3 ∧ χ y = 0 ∧ (∀ g, orderOf g = 2 → χ g = 4) ∧
    (∀ g, orderOf g = 4 ∨ orderOf g = 8 → χ g = 0) ∧ (∀ g, orderOf g = 6 → χ g = 1) ∧
    (∀ g, orderOf g = 13 → χ g = -1) := by
  obtain ⟨basis⟩ := finiteIrreducibleCharacterBasis_exists (G := G)
  obtain ⟨a, ha⟩ := exists_label_of_mem_blocksIrr basis hχ
  have hdeg : Module.finrank ℂ (basis.representation a).vector = 12 := by
    have h := label_character_one basis a
    rw [ha, hχ1] at h
    exact_mod_cast h.symm
  have huniqb : ∀ b, Module.finrank ℂ (basis.representation b).vector =
      Module.finrank ℂ (basis.representation a).vector → b = a := by
    intro b hb
    apply basis.distinct
    show (basis.representation b).character = (basis.representation a).character
    rw [ha]
    refine huniq _ (label_mem_blocksIrr basis b) ?_
    rw [label_character_one, hb, hdeg]
    norm_num
  have hrat : ∀ g, ∃ q : ℚ, χ g = q := fun g => by
    rw [← ha]
    exact character_rat_of_unique_degree basis huniqb g
  have hpow : ∀ k : ℕ, (Nat.card G).Coprime k → ∀ g, χ (g ^ k) = χ g := fun k hk g => by
    rw [← ha]
    exact character_pow_eq_of_unique_degree basis huniqb hk g
  have hcls : ∀ g h : G, χ (h * g * h⁻¹) = χ g := fun g h => by
    rw [← ha]
    exact Representation.char_conj _ g h
  have hconjval : ∀ u v : G, IsConj u v → χ u = χ v := fun u v huv => by
    obtain ⟨c, hc⟩ := isConj_iff.mp huv
    rw [← hc, hcls]
  choose q hq using hrat
  have hqconj : ∀ u v : G, IsConj u v → q u = q v := fun u v huv => by
    have h := hconjval u v huv
    rw [hq, hq] at h
    exact_mod_cast h
  have hinj : Function.Injective (basis.representation a).representation :=
    injective_of_isIrreducible_of_isSimpleGroup _ (basis.irreducible a) (by rw [hdeg]; norm_num)
  have hpowone : ∀ g : G, (basis.representation a).representation g ^ orderOf g = 1 :=
    fun g => by rw [← map_pow, pow_orderOf_eq_one, map_one]
  have htrace : ∀ g, LinearMap.trace ℂ (basis.representation a).vector
      ((basis.representation a).representation g) = ((q g : ℚ) : ℂ) := fun g => by
    rw [← hq g, ← ha]
    rfl
  have hfaith : ∀ g, χ g = 12 → g = 1 := by
    intro g hg
    apply hinj
    rw [map_one]
    refine CFSG.Section1.finite_order_eq_one_of_trace_eq_finrank _ (orderOf_pos g).ne'
      (hpowone g) ?_
    rw [hdeg, Nat.cast_ofNat, ← hg, ← ha]
    rfl
  have hgap : ∀ (p e : ℕ), p.Prime → ∀ g : G, orderOf g = p ^ e →
      (∃ z : ℤ, (z : ℚ) = q g) ∧ (∃ k : ℕ, (12 : ℚ) - q g = p * k) ∧
        -((12 : ℚ) / (p - 1)) ≤ q g ∧ (g ≠ 1 → q g < 12) := by
    intro p e hp g hge
    have hf : (basis.representation a).representation g ^ (p ^ e) = 1 := hge ▸ hpowone g
    obtain ⟨h1, h2, h3', -, h5⟩ := trace_gap_of_pow_prime_pow_eq_one hp hf (htrace g)
    rw [hdeg] at h2 h3' h5
    push_cast at h2 h3' h5
    exact ⟨h1, h2, h3', fun hg1 => h5 fun h => hg1 (hinj (by rw [h, map_one]))⟩
  have hv13 : ∀ g, orderOf g = 13 → q g = -1 := by
    intro g hg
    have hg1 : g ≠ 1 := fun h => by rw [h, orderOf_one] at hg; norm_num at hg
    obtain ⟨-, ⟨k, hk⟩, hlow, hlt⟩ := hgap 13 1 (by norm_num) g (by rw [hg]; norm_num)
    have hlt' := hlt hg1
    push_cast at hk hlow
    norm_num at hlow
    have hk1 : (k : ℚ) = 1 := by
      have h1 : (0 : ℚ) < k := by
        have : (0 : ℚ) < 13 * k := by linarith
        linarith
      have h2 : (k : ℚ) ≤ 1 := by
        have : (13 : ℚ) * k ≤ 13 := by linarith
        linarith
      have hk' : 0 < k := by exact_mod_cast h1
      have hk'' : k ≤ 1 := by exact_mod_cast h2
      have : k = 1 := by omega
      rw [this]
      norm_num
    rw [hk1] at hk
    linarith
  have hne : ∀ d, 0 < Nat.card {g : G // orderOf g = d} → ∃ g : G, orderOf g = d := by
    intro d hd
    obtain ⟨⟨g, hg⟩⟩ := Nat.card_pos_iff.mp hd |>.1
    exact ⟨g, hg⟩
  obtain ⟨t0, ht0⟩ := hne 2 (by rw [h2c]; norm_num)
  obtain ⟨g4, hg4⟩ := hne 4 (by rw [h4c]; norm_num)
  obtain ⟨g6, hg6⟩ := hne 6 (by rw [h6c]; norm_num)
  obtain ⟨h8, hh8⟩ := hne 8 (by rw [h8c]; norm_num)
  set s := q t0 with hsdef
  set w := q g4 with hwdef
  set r := q g6 with hrdef
  have hv2 : ∀ g, orderOf g = 2 → q g = s := fun g hg => hqconj _ _ (h2conj g t0 hg ht0)
  have hv4 : ∀ g, orderOf g = 4 → q g = w := fun g hg => hqconj _ _ (h4conj g g4 hg hg4)
  have hv6 : ∀ g, orderOf g = 6 → q g = r := fun g hg => hqconj _ _ (h6conj g g6 hg hg6)
  have hs8 : ∃ m : ℕ, s = 12 - 8 * m := by
    have hζ := cyclicRoot_isPrimitiveRoot (M := 8) (by norm_num)
    have hζ8 : cyclicRoot 8 ^ 8 = 1 := cyclicRoot_pow_self 8
    have hζ4 : cyclicRoot 8 ^ 4 = -1 := by
      have := cyclicRoot_pow_half (M := 8) (by norm_num) (by decide)
      simpa using this
    let ev : ℂˣ := Units.mk0 (cyclicRoot 8) (cyclicRoot_ne_zero 8)
    have hev : ev ^ 8 = 1 := by
      ext
      simp [ev, hζ8]
    have hρ8 : (basis.representation a).representation h8 ^ 8 = 1 := hh8 ▸ hpowone h8
    obtain ⟨m, hm⟩ := character_fourier_natural (basis.representation a) h8 8 (by norm_num) hρ8 ev
      hev
    refine ⟨m, ?_⟩
    set u : ℂ := ((ev⁻¹ : ℂˣ) : ℂ) with hu
    have hu4 : u ^ 4 = -1 := by
      rw [hu, Units.val_inv_eq_inv_val, inv_pow]
      simp [ev, hζ4]
    rw [ha] at hm
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, pow_zero, one_mul,
      pow_one] at hm
    have hcop : ∀ k : ℕ, k ∈ ({5, 7, 11} : Finset ℕ) → (Nat.card G).Coprime k := by
      intro k hk
      rw [hG]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl | rfl <;> norm_num
    have h3' : χ (h8 ^ 3) = χ h8 := by
      have h := hpow 11 (hcop 11 (by simp)) h8
      rwa [show h8 ^ 11 = h8 ^ 3 by
        rw [show 11 = 8 + 3 by rfl, pow_add, ← hh8, pow_orderOf_eq_one, one_mul]] at h
    have h5' : χ (h8 ^ 5) = χ h8 := hpow 5 (hcop 5 (by simp)) h8
    have h7' : χ (h8 ^ 7) = χ h8 := hpow 7 (hcop 7 (by simp)) h8
    have h6' : χ (h8 ^ 6) = χ (h8 ^ 2) := by
      have h := hpow 11 (hcop 11 (by simp)) (h8 ^ 2)
      rwa [← pow_mul, show 2 * 11 = 16 + 6 by rfl, pow_add,
        show h8 ^ 16 = 1 by rw [show 16 = 8 * 2 by rfl, pow_mul, ← hh8, pow_orderOf_eq_one,
          one_pow], one_mul] at h
    have h4' : χ (h8 ^ 4) = s := by
      have hord : orderOf (h8 ^ 4) = 2 := by
        rw [orderOf_pow' h8 (by norm_num), hh8]
        norm_num
      rw [hq, hv2 _ hord]
    rw [hχ1, h3', h5', h7', h6', h4'] at hm
    rw [show u ^ 5 = u * u ^ 4 by ring, show u ^ 6 = u ^ 2 * u ^ 4 by ring,
      show u ^ 7 = u ^ 3 * u ^ 4 by ring, hu4] at hm
    have hm' : ((12 - s : ℚ) : ℂ) = (8 * m : ℚ) := by
      push_cast
      linear_combination 8 * hm
    have hm'' : (12 - s : ℚ) = 8 * m := by exact_mod_cast hm'
    linarith
  obtain ⟨m, hm⟩ := hs8
  have hwg : ∃ k : ℕ, (12 : ℚ) - w = 2 * k := by
    obtain ⟨-, ⟨k, hk⟩, -, -⟩ := hgap 2 2 Nat.prime_two g4 (by rw [hg4]; norm_num)
    exact ⟨k, by push_cast at hk; exact hk⟩
  have h8g : ∀ g, orderOf g = 8 → ∃ k : ℕ, (12 : ℚ) - q g = 2 * k := by
    intro g hg
    obtain ⟨-, ⟨k, hk⟩, -, -⟩ := hgap 2 3 Nat.prime_two g (by rw [hg]; norm_num)
    exact ⟨k, by push_cast at hk; exact hk⟩
  have hxg : ∃ k : ℕ, (12 : ℚ) - q x = 3 * k := by
    obtain ⟨-, ⟨k, hk⟩, -, -⟩ := hgap 3 1 Nat.prime_three x (by rw [hx]; norm_num)
    exact ⟨k, by push_cast at hk; exact hk⟩
  have hyg : ∃ k : ℕ, (12 : ℚ) - q y = 3 * k := by
    obtain ⟨-, ⟨k, hk⟩, -, -⟩ := hgap 3 1 Nat.prime_three y (by rw [hy]; norm_num)
    exact ⟨k, by push_cast at hk; exact hk⟩
  have hχ1' : χ ≠ 1 := fun h => by
    have := congrFun h 1
    rw [hχ1, Pi.one_apply] at this
    norm_num at this
  obtain ⟨horth, -, -, -⟩ := CFSG.irreducible_character_basis G
  have hnormC := horth χ hχ χ hχ
  have horthC := horth χ hχ 1 (principal_mem_blocksIrr G)
  rw [ite_eq_left rfl] at hnormC
  rw [ite_eq_right hχ1'] at horthC
  have hGc : (Nat.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hnorm : ∑ g, q g ^ 2 = 5616 := by
    rw [CFSG.BlocksInnerProduct] at hnormC
    have h : ∑ g, χ g * starRingEnd ℂ (χ g) = (Nat.card G : ℂ) := by
      field_simp at hnormC
      linear_combination hnormC
    rw [hG] at h
    have h' : ((∑ g, q g ^ 2 : ℚ) : ℂ) = ((5616 : ℚ) : ℂ) := by
      push_cast
      rw [show (5616 : ℂ) = ((5616 : ℕ) : ℂ) by norm_num, ← h]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [hq, map_ratCast]
      ring
    exact_mod_cast h'
  have hsum : ∑ g, q g = 0 := by
    rw [CFSG.BlocksInnerProduct] at horthC
    have h : ∑ g, χ g = 0 := by
      have h' := horthC
      simp only [Pi.one_apply, map_one, mul_one] at h'
      rcases mul_eq_zero.mp h' with h | h
      · exact absurd h (inv_ne_zero hGc)
      · exact h
    have h'' : ((∑ g, q g : ℚ) : ℂ) = 0 := by
      push_cast
      rw [← h]
      exact Finset.sum_congr rfl fun g _ => (hq g).symm
    exact_mod_cast h''
  have hxy : ¬ IsConj x y := fun h => by
    have := congrArg (fun c => Nat.card c.carrier) (ConjClasses.mk_eq_mk_iff_isConj.mpr h)
    rw [hxc, hyc] at this
    norm_num at this
  have hsplit3 : ∀ F : G → ℚ, (∀ g h : G, F (h * g * h⁻¹) = F g) →
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 3), F g = 104 * F x + 624 * F y := by
    intro F hF
    have hFconj : ∀ u v : G, IsConj u v → F u = F v := fun u v huv => by
      obtain ⟨c, hc⟩ := isConj_iff.mp huv
      rw [← hc, hF]
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun g => IsConj g x)]
    have hA : (Finset.univ.filter fun g : G => orderOf g = 3).filter (fun g => IsConj g x) =
        Finset.univ.filter fun g => IsConj g x := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨by rw [orderOf_eq_of_isConj h, hx], h⟩
    have hB : (Finset.univ.filter fun g : G => orderOf g = 3).filter (fun g => ¬ IsConj g x) =
        Finset.univ.filter fun g => IsConj g y := by
      ext g
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h3g, hnx⟩
        exact (h3 g h3g).resolve_left hnx
      · intro h
        refine ⟨by rw [orderOf_eq_of_isConj h, hy], fun hgx => hxy ?_⟩
        exact (hgx.symm.trans h)
    rw [hA, hB, sum_filter_const (c := F x) fun g hg => hFconj _ _ (Finset.mem_filter.mp hg).2,
      sum_filter_const (c := F y) fun g hg => hFconj _ _ (Finset.mem_filter.mp hg).2,
      card_filter_isConj, card_filter_isConj, hxc, hyc]
    push_cast
    ring
  have hqcls : ∀ g h : G, q (h * g * h⁻¹) = q g := fun g h =>
    hqconj _ _ (isConj_iff.mpr ⟨h, rfl⟩).symm
  have hsum8 : ∀ g0, orderOf g0 = 8 →
      702 * q g0 ^ 2 ≤ ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 8), q g ^ 2 := by
    intro g0 hg0
    have hsub : (Finset.univ.filter fun g => IsConj g g0) ⊆
        Finset.univ.filter fun g : G => orderOf g = 8 := fun g hg => by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
      rw [orderOf_eq_of_isConj hg, hg0]
    have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun g => q g ^ 2)
      (fun g _ _ => sq_nonneg _)
    rw [sum_filter_const (c := q g0 ^ 2) fun g hg => by
      rw [hqconj _ _ (Finset.mem_filter.mp hg).2], card_filter_isConj, h8cls g0 hg0] at h
    push_cast at h
    exact h
  have hnorm' := hnorm
  rw [sum_split_orders _ horders] at hnorm'
  rw [hsplit3 (fun g => q g ^ 2) (fun g h => by rw [hqcls])] at hnorm'
  rw [sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 2) (c := s ^ 2)
      fun g hg => by rw [hv2 g (Finset.mem_filter.mp hg).2],
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 4) (c := w ^ 2)
      fun g hg => by rw [hv4 g (Finset.mem_filter.mp hg).2],
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 6) (c := r ^ 2)
      fun g hg => by rw [hv6 g (Finset.mem_filter.mp hg).2],
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 13) (c := (-1) ^ 2)
      fun g hg => by rw [hv13 g (Finset.mem_filter.mp hg).2],
    card_filter_orderOf, card_filter_orderOf, card_filter_orderOf, card_filter_orderOf,
    h2c, h4c, h6c, h13c] at hnorm'
  have hq1 : q 1 = 12 := by
    have h := hq 1
    rw [hχ1] at h
    exact_mod_cast h.symm
  rw [hq1] at hnorm'
  push_cast at hnorm'
  have hN8nn : 0 ≤ ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 8), q g ^ 2 :=
    Finset.sum_nonneg fun g _ => sq_nonneg _
  have hs_pm : s = 4 ∨ s = -4 := by
    have hbound : 117 * s ^ 2 ≤ 3744 := by
      nlinarith [sq_nonneg (q x), sq_nonneg (q y), sq_nonneg w, sq_nonneg r]
    rw [hm] at hbound ⊢
    have hm3 : m ≤ 2 := by
      by_contra hc
      push Not at hc
      have : (3 : ℚ) ≤ m := by exact_mod_cast hc
      nlinarith
    have hm1 : 1 ≤ m := by
      by_contra hc
      push Not at hc
      have : m = 0 := by omega
      rw [this] at hbound
      norm_num at hbound
    interval_cases m <;> norm_num
  have hs2 : s ^ 2 = 16 := by rcases hs_pm with h | h <;> rw [h] <;> norm_num
  have hrest : 104 * q x ^ 2 + 624 * q y ^ 2 + 702 * w ^ 2 + 936 * r ^ 2 +
      ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 8), q g ^ 2 = 1872 := by
    nlinarith [hs2]
  have hw0 : w = 0 := by
    obtain ⟨k, hk⟩ := hwg
    by_contra hw
    have hk6 : k ≠ 6 := fun h => hw (by rw [h] at hk; push_cast at hk; linarith)
    have hsq : 4 ≤ w ^ 2 := by
      have hw' : w = 12 - 2 * k := by linarith
      rw [hw']
      rcases Nat.lt_or_gt_of_ne hk6 with h | h
      · have : (k : ℚ) ≤ 5 := by exact_mod_cast Nat.lt_succ_iff.mp h
        nlinarith
      · have : (7 : ℚ) ≤ k := by exact_mod_cast h
        nlinarith
    nlinarith [sq_nonneg (q x), sq_nonneg (q y), sq_nonneg r]
  have h8zero : ∀ g, orderOf g = 8 → q g = 0 := by
    intro g hg
    obtain ⟨k, hk⟩ := h8g g hg
    by_contra hne0
    have hk6 : k ≠ 6 := fun h => hne0 (by rw [h] at hk; push_cast at hk; linarith)
    have hsq : 4 ≤ q g ^ 2 := by
      have hq' : q g = 12 - 2 * k := by linarith
      rw [hq']
      rcases Nat.lt_or_gt_of_ne hk6 with h | h
      · have : (k : ℚ) ≤ 5 := by exact_mod_cast Nat.lt_succ_iff.mp h
        nlinarith
      · have : (7 : ℚ) ≤ k := by exact_mod_cast h
        nlinarith
    have := hsum8 g hg
    nlinarith [sq_nonneg (q x), sq_nonneg (q y), sq_nonneg r, sq_nonneg w]
  have hN8 : ∑ g ∈ Finset.univ.filter (fun g : G => orderOf g = 8), q g ^ 2 = 0 :=
    Finset.sum_eq_zero fun g hg => by rw [h8zero g (Finset.mem_filter.mp hg).2]; ring
  have hy0 : q y = 0 := by
    obtain ⟨k, hk⟩ := hyg
    by_contra hne0
    have hk4 : k ≠ 4 := fun h => hne0 (by rw [h] at hk; push_cast at hk; linarith)
    have hsq : 9 ≤ q y ^ 2 := by
      have hq' : q y = 12 - 3 * k := by linarith
      rw [hq']
      rcases Nat.lt_or_gt_of_ne hk4 with h | h
      · have : (k : ℚ) ≤ 3 := by exact_mod_cast Nat.lt_succ_iff.mp h
        nlinarith
      · have : (5 : ℚ) ≤ k := by exact_mod_cast h
        nlinarith
    nlinarith [sq_nonneg (q x), sq_nonneg r, sq_nonneg w]
  rw [hw0, hy0, hN8] at hrest
  have hsum' := hsum
  rw [sum_split_orders _ horders] at hsum'
  rw [hsplit3 q hqcls] at hsum'
  rw [sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 2) (c := s)
      fun g hg => hv2 g (Finset.mem_filter.mp hg).2,
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 4) (c := w)
      fun g hg => hv4 g (Finset.mem_filter.mp hg).2,
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 6) (c := r)
      fun g hg => hv6 g (Finset.mem_filter.mp hg).2,
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 13) (c := -1)
      fun g hg => hv13 g (Finset.mem_filter.mp hg).2,
    sum_filter_const (s := Finset.univ.filter fun g : G => orderOf g = 8) (c := 0)
      fun g hg => h8zero g (Finset.mem_filter.mp hg).2,
    card_filter_orderOf, card_filter_orderOf, card_filter_orderOf, card_filter_orderOf,
    card_filter_orderOf, h2c, h4c, h6c, h13c, hq1, hw0, hy0] at hsum'
  push_cast at hsum'
  have hrest' : 104 * q x ^ 2 + 936 * r ^ 2 = 1872 := by linarith [hrest]
  have horth' : 117 * s + 104 * q x + 936 * r = 1716 := by linarith [hsum']
  obtain ⟨kx, hkx⟩ := hxg
  have hkx' : q x = 12 - 3 * kx := by linarith
  have hx2 : q x ^ 2 ≤ 18 := by nlinarith [sq_nonneg r]
  have hk3 : kx = 3 ∨ kx = 4 ∨ kx = 5 := by
    have h1 : 3 ≤ kx := by
      by_contra hc
      push Not at hc
      have hc' : (kx : ℚ) ≤ 2 := by exact_mod_cast Nat.lt_succ_iff.mp hc
      nlinarith
    have h2 : kx ≤ 5 := by
      by_contra hc
      push Not at hc
      have hc' : (6 : ℚ) ≤ kx := by exact_mod_cast hc
      nlinarith
    omega
  have hxval : q x = 3 ∧ r = 1 ∧ s = 4 := by
    rcases hk3 with hk | hk | hk <;> rw [hk] at hkx' <;> push_cast at hkx' <;> norm_num at hkx'
    · rcases hs_pm with hs | hs
      · refine ⟨hkx', ?_, hs⟩
        rw [hkx', hs] at horth'
        linarith
      · exfalso
        rw [hkx', hs] at horth'
        have hr : r = 2 := by linarith
        rw [hkx', hr] at hrest'
        norm_num at hrest'
    · exfalso
      rcases hs_pm with hs | hs
      · rw [hkx', hs] at horth'
        have hr : r = 4 / 3 := by linarith
        rw [hkx', hr] at hrest'
        norm_num at hrest'
      · rw [hkx', hs] at horth'
        have hr : r = 7 / 3 := by linarith
        rw [hkx', hr] at hrest'
        norm_num at hrest'
    · exfalso
      rcases hs_pm with hs | hs
      · rw [hkx', hs] at horth'
        have hr : r = 5 / 3 := by linarith
        rw [hkx', hr] at hrest'
        norm_num at hrest'
      · rw [hkx', hs] at horth'
        have hr : r = 8 / 3 := by linarith
        rw [hkx', hr] at hrest'
        norm_num at hrest'
  obtain ⟨hx3, hr1, hs4⟩ := hxval
  refine ⟨fun g => ⟨q g, hq g⟩, hfaith, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq, hx3]; norm_num
  · rw [hq, hy0]; norm_num
  · intro g hg; rw [hq, hv2 g hg, hs4]; norm_num
  · rintro g (hg | hg)
    · rw [hq, hv4 g hg, hw0]; norm_num
    · rw [hq, h8zero g hg]; norm_num
  · intro g hg; rw [hq, hv6 g hg, hr1]; norm_num
  · intro g hg; rw [hq, hv13 g hg]; norm_num

theorem unique_degree_twelve_character_value_production {G : Type} [Group G] [Fintype G]
    (hG : Nat.card G = 5616) (hperf : commutator G = ⊤) (h12 : Nat.card (ConjClasses G) = 12)
    (hinv : ∀ a b : G, orderOf a = 2 → orderOf b = 2 → IsConj a b) {t : G} (ht : orderOf t = 2)
    (hC : Nonempty (Subgroup.centralizer ({t} : Set G) ≃* GL (Fin 2) (ZMod 3)))
    (χ : G → ℂ) (hχ : χ ∈ CFSG.BlocksIrr G) (hχ1 : χ 1 = 12)
    (huniq : ∀ ψ ∈ CFSG.BlocksIrr G, ψ 1 = 12 → ψ = χ) :
    (∀ g, ∃ q : ℚ, χ g = q) ∧ (∀ g, χ g = 12 → g = 1) ∧
    (∀ g : G, orderOf g ≠ 9 ∧ orderOf g ≠ 27) ∧
    (∀ g : G, orderOf g ∈ ({1, 2, 3, 4, 6, 8, 13} : Finset ℕ)) ∧
    ∃ x y : G, orderOf x = 3 ∧ orderOf y = 3 ∧ Nat.card (ConjClasses.mk x).carrier = 104 ∧
      Nat.card (ConjClasses.mk y).carrier = 624 ∧
      (∀ z : G, orderOf z = 3 → IsConj z x ∨ IsConj z y) ∧
      χ x = 3 ∧ χ y = 0 ∧ (∀ g, orderOf g = 2 → χ g = 4) ∧
      (∀ g, orderOf g = 4 ∨ orderOf g = 8 → χ g = 0) ∧ (∀ g, orderOf g = 6 → χ g = 1) ∧
      (∀ g, orderOf g = 13 → χ g = -1) := by
  obtain ⟨h2c, h2conj, -, h4c, h4conj, -, h6c, h6conj, -, h8c, -, h8cls, h13c, -, -, -, -, -⟩ :=
    perfect_order5616_GL2_centralizer_element_profile hG hperf hinv ht hC
  obtain ⟨hsimple, -, -⟩ := perfect_order5616_GL2_centralizer_simplicity hG hperf hinv ht hC
  obtain ⟨h927, horders, -, -, -, ⟨x, y, hx, hy, hxc, hyc, -, -, h3⟩, -⟩ :=
    twelve_classes_produce_exponent_three_centralizer_data hG hperf h12 hinv ht hC
  obtain ⟨hrat, hfaith, hx3, hy0, hv2, hv48, hv6, hv13⟩ :=
    unique_degree_twelve_values_core hG horders h2c h2conj h4c h4conj h6c h6conj h8c h8cls h13c
      x y hx hy hxc hyc h3 χ hχ hχ1 huniq
  exact ⟨hrat, hfaith, h927, horders, x, y, hx, hy, hxc, hyc, h3, hx3, hy0, hv2, hv48, hv6, hv13⟩

end Values

end CFSG.Semidihedral.GL2Recognition
