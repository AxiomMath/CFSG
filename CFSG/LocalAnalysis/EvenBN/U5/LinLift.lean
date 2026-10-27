module

public import CFSG.LocalAnalysis.EvenBN.U5.PrelimModules

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

namespace LinCase

theorem linlift_ker_inf_eq_bot {M Λ : Type} [Group M] [Group Λ] [Finite M] (π : M →* Λ)
    {R : Subgroup M} (hR : CFSG.ABGLocalTools.IsSylowOf 2 R ⊤) (hker : Odd (Nat.card π.ker)) :
    π.ker ⊓ R = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRcard : Nat.card R = 2 ^ (Nat.card M).factorization 2 := by
    have h := hR.card_eq
    rwa [Subgroup.card_top] at h
  have hKdvd : Nat.card (π.ker ⊓ R : Subgroup M) ∣ 2 ^ (Nat.card M).factorization 2 := by
    rw [← hRcard]
    exact Subgroup.card_dvd_of_le inf_le_right
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hKdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2 : 2 ∣ Nat.card (π.ker ⊓ R : Subgroup M) := by
      rw [hk]
      exact dvd_pow_self 2 hk0
    exact hker.not_two_dvd_nat (h2.trans (Subgroup.card_dvd_of_le inf_le_left))
  exact Subgroup.card_eq_one.1 (by rw [hk, hk0, pow_zero])

theorem linlift_image_mem {M Λ : Type} [Group M] [Group Λ] (π : M →* Λ) {R : Subgroup M}
    {x : M} (hx : x ∈ R ⊓ Subgroup.centralizer (R : Set M)) :
    π x ∈ R.map π ⊓ Subgroup.centralizer ((R.map π : Subgroup Λ) : Set Λ) := by
  obtain ⟨hxR, hxC⟩ := Subgroup.mem_inf.1 hx
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map_of_mem π hxR, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 (SetLike.mem_coe.1 hg)
  have hcomm : r * x = x * r := Subgroup.mem_centralizer_iff.1 hxC r (SetLike.mem_coe.2 hr)
  rw [← map_mul, ← map_mul, hcomm]

theorem linlift_exists_mem_normalizer {M Λ : Type} [Group M] [Group Λ] [Finite M] (π : M →* Λ)
    (hπ : Function.Surjective π) {R : Subgroup M} (hR : CFSG.ABGLocalTools.IsSylowOf 2 R ⊤)
    {j : Λ} (hj : j ∈ Subgroup.normalizer ((R.map π : Subgroup Λ) : Set Λ)) :
    ∃ m ∈ Subgroup.normalizer (R : Set M), π m = j := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m₀, hm₀⟩ := hπ j
  obtain ⟨R₁, hR₁⟩ : ∃ R₁ : Subgroup M, R₁ = R.map (MulAut.conj m₀).toMonoidHom := ⟨_, rfl⟩
  have hR₁mem : ∀ g : M, g ∈ R₁ ↔ (MulAut.conj m₀).symm g ∈ R := fun g => by
    rw [hR₁, Subgroup.mem_map_equiv]
  obtain ⟨T, hT⟩ : ∃ T : Subgroup M, T = (R.map π).comap π := ⟨_, rfl⟩
  have hTmem : ∀ g : M, g ∈ T ↔ π g ∈ R.map π := fun g => by
    rw [hT, Subgroup.mem_comap]
  have hRT : R ≤ T := by
    intro r hr
    exact (hTmem r).2 (Subgroup.mem_map_of_mem π hr)
  have hcardR : Nat.card R = 2 ^ (Nat.card M).factorization 2 := by
    have h := hR.card_eq
    rwa [Subgroup.card_top] at h
  have hcardR₁ : Nat.card R₁ = Nat.card R := by
    rw [hR₁]
    exact Subgroup.card_map_of_injective (f := (MulAut.conj m₀).toMonoidHom)
      (MulAut.conj m₀).injective
  have hR₁S : CFSG.ABGLocalTools.IsSylowOf 2 R₁ ⊤ :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_top
      (by rw [Subgroup.card_top]; exact hcardR₁.trans hcardR)
  have hgeq : ∀ g : M, π g = j * π ((MulAut.conj m₀).symm g) * j⁻¹ := by
    intro g
    rw [MulAut.conj_symm_apply, ← hm₀]
    simp only [map_mul, map_inv]
    group
  have hR₁T : R₁ ≤ T := by
    intro g hg
    have hr : (MulAut.conj m₀).symm g ∈ R := (hR₁mem g).1 hg
    rw [hTmem, hgeq g]
    exact SetLike.mem_coe.1 ((Subgroup.mem_normalizer_iff.1 hj
      (π ((MulAut.conj m₀).symm g))).1 (SetLike.mem_coe.2 (Subgroup.mem_map_of_mem π hr)))
  have hR₁Tt : CFSG.ABGLocalTools.IsSylowOf 2 R₁ T := hR₁S.of_le hR₁T le_top
  have hRTt : CFSG.ABGLocalTools.IsSylowOf 2 R T := hR.of_le hRT le_top
  obtain ⟨t, htT, hRt⟩ :=
    CFSG.LocalAnalysis.EvenBN.U5.Prelim.exists_conj_of_isSylowOf hR₁Tt hRTt
  have hkey : ∀ h : M, h ∈ R ↔ (MulAut.conj t).symm h ∈ R₁ := fun h => by
    rw [hRt, Subgroup.mem_map_equiv]
  have hn : t * m₀ ∈ Subgroup.normalizer (R : Set M) := by
    rw [Subgroup.mem_normalizer_iff'']
    intro h
    change h ∈ R ↔ (t * m₀)⁻¹ * h * (t * m₀) ∈ R
    rw [hkey h, hR₁mem]
    have e : (MulAut.conj m₀).symm ((MulAut.conj t).symm h) = (t * m₀)⁻¹ * h * (t * m₀) := by
      simp only [MulAut.conj_symm_apply, mul_inv_rev, mul_assoc]
    rw [e]
  obtain ⟨r, hr, hrt⟩ := Subgroup.mem_map.1 ((hTmem t).1 htT)
  refine ⟨r⁻¹ * (t * m₀), mul_mem (inv_mem (Subgroup.le_normalizer hr)) hn, ?_⟩
  rw [map_mul, map_inv, map_mul, hm₀, hrt, inv_mul_cancel_left]

theorem exists_odd_normalizer_transitive {M Λ : Type} [Group M] [Group Λ] [Finite M] [Finite Λ]
    (π : M →* Λ) (hπ : Function.Surjective π) (hker : Odd (Nat.card π.ker))
    {R : Subgroup M} (hR : CFSG.ABGLocalTools.IsSylowOf 2 R ⊤)
    {J' : Subgroup Λ} (hJ'N : J' ≤ Subgroup.normalizer ((R.map π : Subgroup Λ) : Set Λ))
    (hJ'odd : Odd (Nat.card J'))
    (htrans : ∀ x ∈ R.map π ⊓ Subgroup.centralizer ((R.map π : Subgroup Λ) : Set Λ), x ≠ 1 →
      ∀ y ∈ R.map π ⊓ Subgroup.centralizer ((R.map π : Subgroup Λ) : Set Λ), y ≠ 1 →
        ∃ j ∈ J', j * x * j⁻¹ = y) :
    ∃ J : Subgroup M, J ≤ Subgroup.normalizer (R : Set M) ∧ Odd (Nat.card J) ∧
      ∀ x ∈ R ⊓ Subgroup.centralizer (R : Set M), x ≠ 1 →
        ∀ y ∈ R ⊓ Subgroup.centralizer (R : Set M), y ≠ 1 → ∃ j ∈ J, j * x * j⁻¹ = y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK := linlift_ker_inf_eq_bot π hR hker
  have hker1 : ∀ a ∈ R, π a = 1 → a = 1 := by
    intro a ha h
    have hmem : a ∈ π.ker ⊓ R := Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 h, ha⟩
    rw [hK, Subgroup.mem_bot] at hmem
    exact hmem
  have hinjR : ∀ a ∈ R, ∀ b ∈ R, π a = π b → a = b := by
    intro a ha b hb hab
    have h1 : π (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hker1 _ (R.mul_mem ha (R.inv_mem hb)) h1)
  obtain ⟨J₀, hJ₀⟩ : ∃ J₀ : Subgroup M,
      J₀ = Subgroup.normalizer (R : Set M) ⊓ J'.comap π := ⟨_, rfl⟩
  have hJmem : ∀ g : M, g ∈ J₀ ↔ g ∈ Subgroup.normalizer (R : Set M) ∧ π g ∈ J' := by
    intro g
    rw [hJ₀, Subgroup.mem_inf, Subgroup.mem_comap]
  refine ⟨J₀, ?_, ?_, ?_⟩
  · intro g hg
    exact ((hJmem g).1 hg).1
  ·
    have hrangeLe : (π.comp J₀.subtype).range ≤ J' := by
      intro y hy
      obtain ⟨g, rfl⟩ := MonoidHom.mem_range.1 hy
      exact ((hJmem g.1).1 g.2).2
    have hkerLe : (π.comp J₀.subtype).ker.map J₀.subtype ≤ π.ker := by
      intro z hz
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hz
      exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hg)
    have hdvdker : Nat.card (π.comp J₀.subtype).ker ∣ Nat.card π.ker := by
      have h1 := Subgroup.card_map_of_injective (K := (π.comp J₀.subtype).ker)
        J₀.subtype_injective
      rw [← h1]
      exact Subgroup.card_dvd_of_le hkerLe
    have hdvdrange : Nat.card (π.comp J₀.subtype).range ∣ Nat.card J' :=
      Subgroup.card_dvd_of_le hrangeLe
    have hsplit := (Subgroup.card_ker_mul_card_range (π.comp J₀.subtype)).symm
    rw [hsplit]
    exact (Odd.of_dvd_nat hker hdvdker).mul (Odd.of_dvd_nat hJ'odd hdvdrange)
  ·
    intro x hx hx1 y hy hy1
    have hxR : x ∈ R := (Subgroup.mem_inf.1 hx).1
    have hyR : y ∈ R := (Subgroup.mem_inf.1 hy).1
    obtain ⟨j, hjJ', hjeq⟩ := htrans (π x) (linlift_image_mem π hx)
      (fun h => hx1 (hker1 x hxR h)) (π y) (linlift_image_mem π hy)
      (fun h => hy1 (hker1 y hyR h))
    obtain ⟨m, hmN, hmπ⟩ := linlift_exists_mem_normalizer π hπ hR (hJ'N hjJ')
    refine ⟨m, (hJmem m).2 ⟨hmN, by rw [hmπ]; exact hjJ'⟩, ?_⟩
    have hmx : m * x * m⁻¹ ∈ R :=
      SetLike.mem_coe.1 ((Subgroup.mem_normalizer_iff.1 hmN x).1 (SetLike.mem_coe.2 hxR))
    apply hinjR (m * x * m⁻¹) hmx y hyR
    rw [map_mul, map_mul, map_inv, hmπ]
    exact hjeq

end LinCase

end CFSG.LocalAnalysis.EvenBN.U5
