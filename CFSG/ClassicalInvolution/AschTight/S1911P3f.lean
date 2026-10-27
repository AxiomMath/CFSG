module

public import CFSG.ClassicalInvolution.AschTight.S1911P3b
public import CFSG.ClassicalInvolution.AschTight.S1911SecC

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1911

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.RankThreeCoreUniqueness CFSG.RankThreeCoreUniqueness.Helpers

section Generic

variable {Y₀ : Type} [Group Y₀]

theorem conjInvariant_conjFamily (L : Subgroup Y₀) : ConjInvariant (conjFamily L) := by
  rintro n _ ⟨g, rfl⟩
  exact ⟨n * g, conjSub_mul _ _ _⟩

theorem conjGen_normal (L : Subgroup Y₀) : (conjGen L).Normal :=
  omegaGen_normal (conjInvariant_conjFamily L)

theorem isUniqueInvolution_map_mk {Y : Type} [Group Y] [Finite Y] {N : Subgroup Y} [N.Normal]
    (hN : Odd (Nat.card N)) {M : Subgroup Y} {u : Y} (hu : IsUniqueInvolution M u) :
    IsUniqueInvolution (M.map (QuotientGroup.mk' N)) (QuotientGroup.mk' N u) := by
  have h2 : ∀ (x : Y) (n : ℕ), orderOf x ∣ 2 ^ n → x ∈ N → x = 1 := by
    intro x n hx hxN
    refine eq_one_of_isPGroup_of_mem_odd hN hxN ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hx
    exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  refine ⟨⟨u, hu.mem, rfl⟩, fun h => hu.ne_one ?_, by rw [← map_mul, hu.sq, map_one], ?_⟩
  · refine h2 u 1 (orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hu.sq)) ?_
    exact (QuotientGroup.eq_one_iff _).mp h
  · rintro _ ⟨m, hm, rfl⟩ hm2
    obtain ⟨k, r, hr, hkr⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos m).ne'
    obtain ⟨j, hj⟩ := hr
    have himg : QuotientGroup.mk' N (m ^ r) = QuotientGroup.mk' N m := by
      rw [map_pow, hj, pow_succ, pow_mul, sq, hm2, one_pow, one_mul]
    have hord : orderOf (m ^ r) = 2 ^ k := by
      rw [orderOf_pow_of_dvd (by omega) (hkr ▸ dvd_mul_left r (2 ^ k)), hkr,
        Nat.mul_div_cancel _ (by omega)]
    have hsq : m ^ r * m ^ r = 1 := by
      have hN2 : m ^ r * m ^ r ∈ N := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
        have : (QuotientGroup.mk (m ^ r) : Y ⧸ N) = QuotientGroup.mk' N m := himg
        rw [this, hm2]
      refine h2 _ k ?_ hN2
      rw [← sq, ← hord]
      exact orderOf_pow_dvd 2
    rcases hu.unique _ (M.pow_mem hm r) hsq with h | h
    · left
      rw [← himg, h, map_one]
    · right
      rw [← himg, h]

end Generic

section Img

variable {Y₀ : Type} [Group Y₀] (Y₁ : Subgroup Y₀)

abbrev secImg (M : Subgroup Y₀) : Subgroup (↥Y₁ ⧸ classicalInvolutionOddCore ↥Y₁) :=
  (M.subgroupOf Y₁).map (QuotientGroup.mk' _)

variable [Y₁.Normal]

theorem secAct_secImg (s : Y₀) {M : Subgroup Y₀} (hM : M ≤ Y₁) :
    (secImg Y₁ M).map (secAct Y₁ s).toMonoidHom = secImg Y₁ (conjSub s M) := by
  ext x
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    refine ⟨MulAut.conjNormal s m, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    rw [MulAut.conjNormal_apply]
    exact conj_mem_conjSub (Subgroup.mem_subgroupOf.mp hm)
  · rintro ⟨m, hm, rfl⟩
    have hn := mem_conjSub_iff.mp (Subgroup.mem_subgroupOf.mp hm)
    have hnY : s⁻¹ * (m : Y₀) * s ∈ Y₁ := hM hn
    refine ⟨QuotientGroup.mk' _ ⟨s⁻¹ * (m : Y₀) * s, hnY⟩, ⟨⟨_, hnY⟩, hn, rfl⟩, ?_⟩
    change secAct Y₁ s (QuotientGroup.mk _) = QuotientGroup.mk' _ m
    rw [secAct_mk]
    congr 1
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    change s * (s⁻¹ * (m : Y₀) * s) * s⁻¹ = m
    group

end Img

section Members

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {K : Subgroup G} {z : G} {S : Sylow 2 G} {W : Subgroup G}

theorem isUniqueInvolution_conjSub_perfectCoreIn (hd : Sec19Data p f K z S W) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G))
    (hzKa : z ∈ perfectResidualOf (K ⊓ Subgroup.centralizer ({a} : Set G)))
    (c : ↥(Subgroup.centralizer ({a} : Set G))) :
    IsUniqueInvolution (conjSub c (perfectCoreIn K a)) (c * ⟨z, hzA⟩ * c⁻¹) := by
  have hI := (isUniqueInvolution_of_tight hd.tight.toTightBranch).conj (c : G)
  refine ⟨conj_mem_conjSub (Subgroup.mem_subgroupOf.mpr hzKa),
    fun h => hI.ne_one (congrArg Subtype.val h), Subtype.ext hI.sq, fun y hy hy2 => ?_⟩
  rcases hI.unique _ (le_conjSub_of_mem c hy) (congrArg Subtype.val hy2) with h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Subtype.ext h)

theorem conjSub_eq_of_conj_eq (hd : Sec19Data p f K z S W) {a : G}
    (hzA : z ∈ Subgroup.centralizer ({a} : Set G)) {c₁ c₂ : ↥(Subgroup.centralizer ({a} : Set G))}
    (h : c₁ * ⟨z, hzA⟩ * c₁⁻¹ = c₂ * ⟨z, hzA⟩ * c₂⁻¹) :
    conjSub c₁ (perfectCoreIn K a) = conjSub c₂ (perfectCoreIn K a) := by
  have h' : (c₁ : G) * z * (c₁ : G)⁻¹ = (c₂ : G) * z * (c₂ : G)⁻¹ := congrArg Subtype.val h
  have hK := conjSub_eq_conjSub_of_tight hd.tight.toTightBranch h'
  apply Subgroup.map_injective (Subgroup.centralizer ({a} : Set G)).subtype_injective
  rw [map_conjSub_perfectCore, map_conjSub_perfectCore, conjSub_perfectCore_eq c₁.2 c₂.2 hK]

end Members

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1911
