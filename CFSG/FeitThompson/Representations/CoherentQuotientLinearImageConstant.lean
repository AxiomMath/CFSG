module

public import CFSG.FeitThompson.Representations.CoprimePowerInducedLinearFamily
public import CFSG.FeitThompson.Representations.CoherentCoprimePowerEquivariance
public import CFSG.FeitThompson.Representations.InductionIntegerIsometryTISupport
public import CFSG.FeitThompson.Representations.TIDadeMapEqualsInduction
import Mathlib.Combinatorics.Matroid.Init
import Mathlib.MeasureTheory.Integral.Bochner.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

namespace NormalLinearInduced

variable {G : Type*} [Group G] {L : Subgroup G} {K : Subgroup ↥L}

def puncturedAmbient (K : Subgroup ↥L) : Set G :=
  ((K.map L.subtype : Subgroup G) : Set G) \ {1}

theorem mem_puncturedAmbient_iff {x : ↥L} :
    (x : G) ∈ puncturedAmbient K ↔ x ∈ K ∧ x ≠ 1 := by
  have h1 : (x : G) ∈ (K.map L.subtype : Subgroup G) ↔ x ∈ K :=
    Subgroup.mem_map_iff_mem L.subtype_injective
  simp only [puncturedAmbient, Set.mem_sdiff, Set.mem_singleton_iff, SetLike.mem_coe, h1]
  refine and_congr_right fun _ => ?_
  exact ⟨fun h hx => h (by rw [hx]; simp), fun h hx => h (by exact_mod_cast hx)⟩

@[simp] theorem one_notMem_puncturedAmbient : (1 : G) ∉ puncturedAmbient K := by
  simp [puncturedAmbient]

theorem nonempty_puncturedAmbient (hK : K ≠ ⊥) : (puncturedAmbient K : Set G).Nonempty := by
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hK
  exact ⟨((y : ↥L) : G), mem_puncturedAmbient_iff.2 ⟨y.2, fun h => hy1 (Subtype.ext h)⟩⟩

theorem puncturedAmbient_subset : (puncturedAmbient K : Set G) ⊆ (L : Set G) := by
  intro g hg
  obtain ⟨x, -, hxg⟩ := Subgroup.mem_map.1 hg.1
  exact hxg ▸ x.2

theorem isTIWithNormalizer_puncturedAmbient (hK : K ≠ ⊥)
    (hN : Subgroup.normalizer (puncturedAmbient K) = L)
    (hdisj : ∀ g : G, g ∉ L →
      puncturedAmbient K ∩ (fun x => g⁻¹ * x * g) '' puncturedAmbient K = ∅) :
    IsTIWithNormalizer (puncturedAmbient K) L where
  nonempty := nonempty_puncturedAmbient hK
  one_notMem := one_notMem_puncturedAmbient
  normalizer_eq := hN
  disjoint_conj_image g hg := by
    have hg' : g⁻¹ ∉ L := fun h => hg (by simpa using inv_mem h)
    refine (Set.disjoint_iff_inter_eq_empty.2 (hdisj g⁻¹ hg')).mono_right (le_of_eq ?_)
    exact (Set.image_congr' fun x => by simp).symm

theorem exists_one_le_coprime_modEq {p a N : ℕ} (hp : p.Prime) (ha : ¬ p ∣ a) (hN : N ≠ 0) :
    ∃ k : ℕ, 1 ≤ k ∧ k.Coprime N ∧ k ≡ a [MOD p] := by
  classical
  set m : ℕ := ∏ q ∈ N.primeFactors.erase p, q with hm
  have hpm : p.Coprime m := Nat.Coprime.prod_right fun q hq =>
    (Nat.coprime_primes hp (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hq))).2
      (Ne.symm (Finset.ne_of_mem_erase hq))
  obtain ⟨k, hka, hk1⟩ := Nat.chineseRemainder hpm a 1
  have hkN : k.Coprime N := by
    refine Nat.coprime_of_dvd fun q hq hqk hqN => ?_
    have hk0 : k ≡ 0 [MOD q] := Nat.modEq_zero_iff_dvd.2 hqk
    by_cases hqp : q = p
    · subst hqp
      exact ha (Nat.modEq_zero_iff_dvd.1 (hka.symm.trans hk0))
    · have hqm : q ∣ m := Finset.dvd_prod_of_mem _
        (Finset.mem_erase.2 ⟨hqp, Nat.mem_primeFactors.2 ⟨hq, hqN, hN⟩⟩)
      exact hq.one_lt.ne'
        (Nat.dvd_one.1 (Nat.modEq_zero_iff_dvd.1 ((hk1.of_dvd hqm).symm.trans hk0)))
  refine ⟨k, ?_, hkN, hka⟩
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk] at hka
    exact absurd (Nat.modEq_zero_iff_dvd.1 hka.symm) ha
  · exact hk

theorem exists_pow_eq_of_prime_card {X : Type*} [Group X] {Z : Subgroup X} {p : ℕ} (hp : p.Prime)
    (hZ : Nat.card ↥Z = p) {z z₀ : X} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz₀ : z₀ ∈ Z)
    (hz₀1 : z₀ ≠ 1) : ∃ a : ℕ, ¬ p ∣ a ∧ z₀ ^ a = z ∧ z₀ ^ p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hz₀' : (⟨z₀, hz₀⟩ : ↥Z) ≠ 1 := fun h => hz₀1 (by simpa using congrArg Subtype.val h)
  obtain ⟨a, ha⟩ := mem_powers_of_prime_card hZ (g' := (⟨z, hz⟩ : ↥Z)) hz₀'
  have hord : orderOf (⟨z₀, hz₀⟩ : ↥Z) = p := by
    rcases hp.eq_one_or_self_of_dvd _ (hZ ▸ orderOf_dvd_natCard (⟨z₀, hz₀⟩ : ↥Z)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz₀'
    · exact h
  have hp1 : z₀ ^ p = 1 := by
    have h := pow_orderOf_eq_one (⟨z₀, hz₀⟩ : ↥Z)
    rw [hord] at h
    simpa using congrArg Subtype.val h
  have haz : z₀ ^ a = z := by simpa using congrArg Subtype.val ha
  refine ⟨a, ?_, haz, hp1⟩
  rintro ⟨c, rfl⟩
  rw [pow_mul, hp1, one_pow] at haz
  exact hz1 haz.symm

theorem apply_eq_zero_of_mem_span {X : Type*} {S : Set (X → ℂ)} {x : X}
    (h : ∀ s ∈ S, s x = 0) {f : X → ℂ} (hf : f ∈ Submodule.span ℤ S) : f x = 0 := by
  induction hf using Submodule.span_induction with
  | mem s hs => exact h s hs
  | zero => rfl
  | add a b _ _ ha hb => simp [ha, hb]
  | smul c a _ ha => simp [ha]

theorem isClassFun_of_mem_span {X : Type*} [Monoid X] {S : Set (X → ℂ)}
    (h : ∀ s ∈ S, IsClassFun s) {f : X → ℂ} (hf : f ∈ Submodule.span ℤ S) : IsClassFun f :=
  mem_classFunctions.1 (Submodule.span_le.2 (fun s hs => mem_classFunctions.2 (h s hs)) hf)

variable [Fintype ↥L]

theorem isClassFun_of_mem_span_indFamLinear {f : ↥L → ℂ}
    (hf : f ∈ Submodule.span ℤ (indFamLinear K)) : IsClassFun f :=
  isClassFun_of_mem_span (fun _ hs => isClassFun_iff.2 (conj_eq_of_mem_indFamLinear K hs)) hf

variable [K.Normal]

theorem mem_dadeZDomain_of_mem_charSpanZero (hYIrr : indFamLinear K ⊆ Irr ↥L)
    {f : ↥L → ℂ} (hf : f ∈ charSpanZero (indFamLinear K)) :
    f ∈ dadeZDomain L (puncturedAmbient K) := by
  obtain ⟨hspan, hf1⟩ := mem_charSpanZero.1 hf
  refine mem_dadeZDomain.2 ⟨mem_virtualChars_of_mem_span_Irr (Submodule.span_mono hYIrr hspan),
    fun x hx => ?_⟩
  rw [mem_puncturedAmbient_iff, not_and_or, not_not] at hx
  rcases hx with hxK | hx1
  · exact apply_eq_zero_of_mem_span
      (fun s hs => eq_zero_of_mem_indFamLinear_of_notMem K hs hxK) hspan
  · rw [hx1, hf1]

variable [Fintype G]

noncomputable def indTau (hTI : IsTIWithNormalizer (puncturedAmbient K) L)
    (hYIrr : indFamLinear K ⊆ Irr ↥L) :
    charSpanZero (indFamLinear K) →+ virtualChars G where
  toFun f := ⟨indClassFun L (f : ↥L → ℂ),
    hTI.indClassFun_mem_virtualChars (mem_dadeZDomain_of_mem_charSpanZero hYIrr f.2)⟩
  map_zero' := Subtype.ext (indClassFun_zero L)
  map_add' _ _ := Subtype.ext (indClassFun_add L _ _)

@[simp] theorem coe_indTau (hTI : IsTIWithNormalizer (puncturedAmbient K) L)
    (hYIrr : indFamLinear K ⊆ Irr ↥L) (f : charSpanZero (indFamLinear K)) :
    ((indTau hTI hYIrr f : virtualChars G) : G → ℂ) = indClassFun L (f : ↥L → ℂ) := (rfl)

theorem indTau_apply_one (hTI : IsTIWithNormalizer (puncturedAmbient K) L)
    (hYIrr : indFamLinear K ⊆ Irr ↥L) (f : charSpanZero (indFamLinear K)) :
    ((indTau hTI hYIrr f : virtualChars G) : G → ℂ) 1 = 0 := by
  rw [coe_indTau]
  exact hTI.indClassFun_apply_one
    (mem_dadeZDomain.1 (mem_dadeZDomain_of_mem_charSpanZero hYIrr f.2)).2

variable {ν : Submodule.span ℤ (indFamLinear K) →+ virtualChars G}

theorem isCoherentWith_of_apply_eq_indClassFun
    (hTI : IsTIWithNormalizer (puncturedAmbient K) L) (hYIrr : indFamLinear K ⊆ Irr ↥L)
    (hνinner : ∀ f h : Submodule.span ℤ (indFamLinear K),
      cfInner ((ν f : virtualChars G) : G → ℂ) ((ν h : virtualChars G) : G → ℂ)
        = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
    (hν0 : ∀ f : charSpanZero (indFamLinear K),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ)) :
    IsCoherentWith (indFamLinear K) (indTau hTI hYIrr) ν :=
  ⟨hνinner, fun f => Subtype.ext (hν0 f)⟩

theorem coherentVal_powOp_apply (hodd : Odd (Nat.card G))
    (hTI : IsTIWithNormalizer (puncturedAmbient K) L)
    (hYne : (indFamLinear K).Nonempty) (hYIrr : indFamLinear K ⊆ Irr ↥L)
    (hνinner : ∀ f h : Submodule.span ℤ (indFamLinear K),
      cfInner ((ν f : virtualChars G) : G → ℂ) ((ν h : virtualChars G) : G → ℂ)
        = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
    (hν0 : ∀ f : charSpanZero (indFamLinear K),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear K) (x : G) :
    coherentVal ν ⟨powOp k η, (powOp_bijOn_indFamLinear_of_dvd K
        (Subgroup.card_subgroup_dvd_card L) hk1 hk).mapsTo hη⟩ x
      = coherentVal ν ⟨η, hη⟩ (x ^ k) := by
  have hdvd : Nat.card ↥L ∣ Nat.card G := Subgroup.card_subgroup_dvd_card L
  have hkL : k.Coprime (Nat.card ↥L) := hk.coprime_dvd_right hdvd
  have hSpow := powOp_bijOn_indFamLinear_of_dvd K hdvd hk1 hk
  have hτpow : ∀ f : charSpanZero (indFamLinear K),
      ((indTau hTI hYIrr (charSpanZeroPowOp hSpow.mapsTo f) : virtualChars G) : G → ℂ)
        = powOp k ((indTau hTI hYIrr f : virtualChars G) : G → ℂ) := fun f => by
    rw [coe_indTau, coe_indTau, powOp_indClassFun L (hk.symm : (Nat.card G).Coprime k),
      coe_charSpanZeroPowOp_apply]
  have hI2 : 2 ≤ (indFamLinear K ∩ Irr ↥L).ncard := by
    rw [Set.inter_eq_self_of_subset_left hYIrr]
    exact two_le_ncard_indFamLinear K (hodd.of_dvd_nat hdvd) hYne hYIrr
  have h := coherentVal_powOp_of_mem_Irr hk1 (Nat.Coprime.mul_right hk hkL) hSpow hI2
    (indTau_apply_one hTI hYIrr) hτpow
    (isCoherentWith_of_apply_eq_indClassFun hTI hYIrr hνinner hν0) (χ := η) ⟨hη, hYIrr hη⟩
  simpa using congrFun h x

theorem coherentVal_powOp_apply_eq_of_mem_commutator
    (hTI : IsTIWithNormalizer (puncturedAmbient K) L)
    (hYIrr : indFamLinear K ⊆ Irr ↥L)
    (hν0 : ∀ f : charSpanZero (indFamLinear K),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ))
    {k : ℕ} (hk1 : 1 ≤ k) (hk : k.Coprime (Nat.card G))
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear K)
    {z₀ : ↥L} (hz₀ : z₀ ∈ (⁅K, K⁆ : Subgroup ↥L)) (hz₀1 : z₀ ≠ 1) :
    coherentVal ν ⟨powOp k η, (powOp_bijOn_indFamLinear_of_dvd K
        (Subgroup.card_subgroup_dvd_card L) hk1 hk).mapsTo hη⟩ (z₀ : G)
      = coherentVal ν ⟨η, hη⟩ (z₀ : G) := by
  have hPη : powOp k η ∈ indFamLinear K :=
    (powOp_bijOn_indFamLinear_of_dvd K (Subgroup.card_subgroup_dvd_card L) hk1 hk).mapsTo hη
  have hfmem : (powOp k η - η) ∈ charSpanZero (indFamLinear K) := by
    refine mem_charSpanZero.2 ⟨Submodule.sub_mem _ (Submodule.subset_span hPη)
      (Submodule.subset_span hη), ?_⟩
    rw [Pi.sub_apply, apply_one_of_mem_indFamLinear K hPη,
      apply_one_of_mem_indFamLinear K hη, sub_self]
  have hincl : Submodule.inclusion (charSpanZero_le (indFamLinear K)) ⟨_, hfmem⟩
      = (⟨powOp k η, Submodule.subset_span hPη⟩ : Submodule.span ℤ (indFamLinear K))
        - ⟨η, Submodule.subset_span hη⟩ := Subtype.ext rfl
  have hz₀K : (z₀ : G) ∈ puncturedAmbient K :=
    mem_puncturedAmbient_iff.2 ⟨Subgroup.commutator_le_self K hz₀, hz₀1⟩
  have hfz : (powOp k η - η) z₀ = 0 := by
    rw [Pi.sub_apply, apply_eq_index_of_mem_commutator K hPη hz₀,
      apply_eq_index_of_mem_commutator K hη hz₀, sub_self]
  have hcf := isClassFun_of_mem_span_indFamLinear (mem_charSpanZero.1 hfmem).1
  have hdz := mem_dadeZDomain_of_mem_charSpanZero hYIrr hfmem
  have hind : indClassFun L (powOp k η - η) (z₀ : G) = 0 := by
    rw [← tiDadeMap_eq_indClassFun hTI hcf (mem_dadeZDomain.1 hdz).2,
      tiDadeMap_apply_mem hTI hcf z₀ hz₀K, hfz]
  have hνf := hν0 ⟨_, hfmem⟩
  rw [hincl, map_sub] at hνf
  have h := congrFun hνf (z₀ : G)
  rw [hind] at h
  simp only [Submodule.coe_sub, Pi.sub_apply] at h
  simp only [coherentVal_apply]
  linear_combination h

theorem coherentVal_apply_eq_of_mem_prime_subgroup_commutator {Z : Subgroup ↥L} {p : ℕ}
    (hodd : Odd (Nat.card G)) (hK : K ≠ ⊥)
    (hN : Subgroup.normalizer (puncturedAmbient K) = L)
    (hdisj : ∀ g : G, g ∉ L →
      puncturedAmbient K ∩ (fun x => g⁻¹ * x * g) '' puncturedAmbient K = ∅)
    (hp : p.Prime) (hZ : Nat.card ↥Z = p) (hZK : Z ≤ (⁅K, K⁆ : Subgroup ↥L))
    (hYne : (indFamLinear K).Nonempty) (hYIrr : indFamLinear K ⊆ Irr ↥L)
    (hνinner : ∀ f h : Submodule.span ℤ (indFamLinear K),
      cfInner ((ν f : virtualChars G) : G → ℂ) ((ν h : virtualChars G) : G → ℂ)
        = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
    (hν0 : ∀ f : charSpanZero (indFamLinear K),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ))
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear K)
    {z z₀ : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    coherentVal ν ⟨η, hη⟩ (z : G) = coherentVal ν ⟨η, hη⟩ (z₀ : G) := by
  have hTI := isTIWithNormalizer_puncturedAmbient hK hN hdisj
  obtain ⟨a, hpa, haz, hp1⟩ := exists_pow_eq_of_prime_card hp hZ hz hz1 hz₀ hz₀1
  obtain ⟨k, hk1, hkG, hka⟩ :=
    exists_one_le_coprime_modEq hp hpa (Nat.card_pos (α := G)).ne'
  have hzk : z₀ ^ k = z := by rw [pow_eq_pow_of_modEq hka hp1, haz]
  have hcast : ((z₀ : G)) ^ k = (z : G) := by
    rw [← hzk]; exact (SubmonoidClass.coe_pow z₀ k).symm
  have h1 := coherentVal_powOp_apply hodd hTI hYne hYIrr hνinner hν0 hk1 hkG hη (z₀ : G)
  rw [hcast] at h1
  rw [← h1, coherentVal_powOp_apply_eq_of_mem_commutator hTI hYIrr hν0 hk1 hkG hη (hZK hz₀) hz₀1]

theorem apply_eq_of_mem_prime_subgroup_commutator {Z : Subgroup ↥L} {p : ℕ}
    (hodd : Odd (Nat.card G)) (hK : K ≠ ⊥)
    (hN : Subgroup.normalizer (puncturedAmbient K) = L)
    (hdisj : ∀ g : G, g ∉ L →
      puncturedAmbient K ∩ (fun x => g⁻¹ * x * g) '' puncturedAmbient K = ∅)
    (hp : p.Prime) (hZ : Nat.card ↥Z = p) (hZK : Z ≤ (⁅K, K⁆ : Subgroup ↥L))
    (hYne : (indFamLinear K).Nonempty) (hYIrr : indFamLinear K ⊆ Irr ↥L)
    (hνinner : ∀ f h : Submodule.span ℤ (indFamLinear K),
      cfInner ((ν f : virtualChars G) : G → ℂ) ((ν h : virtualChars G) : G → ℂ)
        = cfInner (f : ↥L → ℂ) (h : ↥L → ℂ))
    (hν0 : ∀ f : charSpanZero (indFamLinear K),
      ((ν (Submodule.inclusion (charSpanZero_le _) f) : virtualChars G) : G → ℂ)
        = indClassFun L (f : ↥L → ℂ))
    {η : ↥L → ℂ} (hη : η ∈ indFamLinear K) (hηspan : η ∈ Submodule.span ℤ (indFamLinear K))
    {z z₀ : ↥L} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz₀ : z₀ ∈ Z) (hz₀1 : z₀ ≠ 1) :
    ((ν ⟨η, hηspan⟩ : virtualChars G) : G → ℂ) (z : G)
      = ((ν ⟨η, hηspan⟩ : virtualChars G) : G → ℂ) (z₀ : G) := by
  have h := coherentVal_apply_eq_of_mem_prime_subgroup_commutator hodd hK hN hdisj hp hZ hZK
    hYne hYIrr hνinner hν0 hη hz hz1 hz₀ hz₀1
  rw [coherentVal_apply] at h
  convert h using 3

end NormalLinearInduced

end CFSG.FeitThompson
