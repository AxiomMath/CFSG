module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.Hyp
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.GL32Facts
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell.SmallSimple
public import CFSG.Quasithin.EmptyFaithfulMultiple.CatalogNative

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem sqtkRank_exp_le_one {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ^ m ∣ 168) : m ≤ 1 := by
  by_contra hm
  have h2 : p ^ 2 ∣ 168 := (pow_dvd_pow p (by omega : 2 ≤ m)).trans h
  have hle : p ^ 2 ≤ 168 := Nat.le_of_dvd (by norm_num) h2
  have hp12 : p ≤ 12 := by nlinarith
  interval_cases p <;> first | omega | exact absurd hp (by norm_num)

theorem sqtkRank_card_pow {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {E : Subgroup G} (hE : IsElemAbelian p E) : ∃ m : ℕ, Nat.card E = p ^ m := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine IsPGroup.exists_card_eq ?_
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hE.2 g g.2

theorem CampbellHyp.stronglyQuasithin (h : CampbellHyp X K R P) :
    CFSG.Open.SQTKTauCeti.StronglyQuasithin ↥X := by
  intro p hp hp2
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  obtain ⟨m, hm⟩ := sqtkRank_card_pow hp hE
  obtain ⟨a, ha⟩ := (isPGroup_pCoreOf X).exists_card_eq
  have hdvd : Nat.card E ∣ Nat.card ↥X := Subgroup.card_subgroup_dvd_card E
  rw [h.card_X, ha, hm] at hdvd
  have hcop : Nat.Coprime (p ^ m) (2 ^ a) := Nat.coprime_pow_primes m a hp Nat.prime_two hp2
  have hm1 : m ≤ 1 := sqtkRank_exp_le_one hp hp2 (hcop.dvd_of_dvd_mul_left hdvd)
  rw [hm]
  exact Nat.pow_le_pow_right hp.pos (by omega)
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem simpleImage_isSolvable_of_card_dvd_two_seven {H : Type*} [Group H] [Finite H] {a b : ℕ}
    (h : Nat.card H ∣ 2 ^ a * 7 ^ b) : Group.IsSolvable H := by
  obtain ⟨k₁, k₂, hk₁, hk₂, hk⟩ := Nat.dvd_mul.1 h
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hk₁
  obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 7)).1 hk₂
  have : Fintype H := Fintype.ofFinite H
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    (by norm_num : Nat.Prime 7) (by norm_num) (by rw [← Nat.card_eq_fintype_card, ← hk])

theorem simpleImage_isSolvable_of_card_dvd_168 {S : Type*} [Group S] [Finite S]
    (hd : Nat.card S ∣ 168) (h3 : ¬ 3 ∣ Nat.card S) : Group.IsSolvable S := by
  have hcop : Nat.Coprime (Nat.card S) 3 :=
    (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3))
  have h56 : Nat.card S ∣ 56 :=
    hcop.dvd_of_dvd_mul_right (by simpa using hd)
  exact simpleImage_isSolvable_of_card_dvd_two_seven (a := 3) (b := 1) (by simpa using h56)

theorem nonempty_mulEquiv_GL32_of_simple_image (H₁ : Subgroup GL32) {S : Type} [Group S]
    [Finite S] [IsSimpleGroup S] (hnab : ∃ a b : S, a * b ≠ b * a) (φ : ↥H₁ →* S)
    (hφ : Function.Surjective φ) : Nonempty (S ≃* GL32) := by
  have hH : Nat.card ↥H₁ ∣ 168 :=
    CFSG.ComponentClassification.GHarris.card_GL32_gh ▸ Subgroup.card_subgroup_dvd_card H₁
  have hS : Nat.card S ∣ Nat.card ↥H₁ := Subgroup.card_dvd_of_surjective hφ
  have hS168 : Nat.card S ∣ 168 := hS.trans hH
  have h3 : 3 ∣ Nat.card S := by
    by_contra h3
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := S)).mpr
      (simpleImage_isSolvable_of_card_dvd_168 hS168 h3) a b)
  have hcard : Nat.card S = 168 :=
    card_eq_168_of_simple hnab hS168 h3
  have hHcard : Nat.card ↥H₁ = 168 :=
    Nat.dvd_antisymm hH (hcard ▸ hS)
  have htop : H₁ = ⊤ :=
    Subgroup.eq_top_of_card_eq H₁
      (hHcard.trans CFSG.ComponentClassification.GHarris.card_GL32_gh.symm)
  have hbij : Function.Bijective φ :=
    (Nat.bijective_iff_surjective_and_card φ).2 ⟨hφ, hHcard.trans hcard.symm⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm.trans
    ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv)⟩
end

section
open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem kGroup_ker_pow (ψ : ↥X →* GL32) (hψ : ψ.ker = (pCoreOf 2 X).subgroupOf X)
    (H : Subgroup ↥X) (x : ↥H) (hx : x ∈ (ψ.comp H.subtype).ker) :
    ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  have hx' : H.subtype x ∈ ψ.ker := hx
  rw [hψ] at hx'
  have hmem : (((x : ↥X)) : A) ∈ pCoreOf 2 X := hx'
  obtain ⟨k, hk⟩ := isPGroup_pCoreOf X ⟨((x : ↥X) : A), hmem⟩
  refine ⟨k, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  have := congrArg (fun y : ↥(pCoreOf 2 X) => (y : A)) hk
  simpa using this

theorem kGroup_ker_le {G S : Type*} [Group G] [Group S] [Finite S] [IsSimpleGroup S] (π : G →* S)
    (hπ : Function.Surjective π) (T : Subgroup G) [T.Normal]
    (hT : ∀ x ∈ T, ∃ k : ℕ, x ^ (2 ^ k) = 1) (hab : ∃ a b : S, a * b ≠ b * a) :
    T ≤ π.ker := by
  haveI : (T.map π).Normal := Subgroup.Normal.map ‹T.Normal› π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (T.map π) with h | h
  · intro x hx
    have hx' : π x ∈ T.map π := ⟨x, hx, rfl⟩
    rw [h] at hx'
    exact Subgroup.mem_bot.1 hx'
  · exfalso
    have h2 : IsPGroup 2 S := by
      intro s
      have hs : s ∈ T.map π := by rw [h]; trivial
      obtain ⟨x, hx, rfl⟩ := hs
      obtain ⟨k, hk⟩ := hT x hx
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    haveI : Group.IsNilpotent S := h2.isNilpotent
    obtain ⟨a, b, hab⟩ := hab
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 (inferInstance : Group.IsSolvable S) a b)

theorem kGroup_exists_factor {G Q S : Type*} [Group G] [Group Q] [Group S] (θ : G →* Q)
    (π : G →* S) (hπ : Function.Surjective π) (hle : θ.ker ≤ π.ker) :
    ∃ φ : ↥θ.range →* S, Function.Surjective φ ∧ ∀ g, φ (θ.rangeRestrict g) = π g := by
  have hsurj : Function.Surjective θ.rangeRestrict := MonoidHom.rangeRestrict_surjective θ
  have hker : θ.rangeRestrict.ker ≤ π.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hle
  have hcomp : ∀ g, (θ.rangeRestrict.liftOfSurjective hsurj ⟨π, hker⟩) (θ.rangeRestrict g) =
      π g := fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  refine ⟨θ.rangeRestrict.liftOfSurjective hsurj ⟨π, hker⟩, ?_, hcomp⟩
  intro s
  obtain ⟨g, rfl⟩ := hπ s
  exact ⟨θ.rangeRestrict g, hcomp g⟩

theorem CampbellHyp.isKGroupCat (h : CampbellHyp X K R P) : CFSG.SectionRank.IsKGroupCat ↥X := by
  intro H N _ hS
  by_cases hab : ∀ a b : ↥H ⧸ N, a * b = b * a
  · exact CFSG.SectionRank.catalog_containsAbelianSimple _ hab
  · push_neg at hab
    obtain ⟨ψ, -, hψ⟩ := h.exists_psi
    have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
    have hle : (ψ.comp H.subtype).ker ≤ (QuotientGroup.mk' N).ker :=
      kGroup_ker_le (QuotientGroup.mk' N) hπ _ (kGroup_ker_pow ψ hψ H) hab
    obtain ⟨φ, hφs, -⟩ := kGroup_exists_factor (ψ.comp H.subtype) (QuotientGroup.mk' N) hπ hle
    obtain ⟨e₁⟩ := nonempty_mulEquiv_GL32_of_simple_image (ψ.comp H.subtype).range hab φ hφs
    obtain ⟨e₂⟩ := nonempty_mulEquiv_GL32_psl
    exact CFSG.Quasithin.EmptyFaithfulMultiple.catalog_of_mulEquiv_psl_three_zmod_two
      (e₁.trans e₂)
end

section
variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem CampbellHyp.isSQTKIn (h : CampbellHyp X K R P) : CFSG.Quasithin.IsSQTKIn X :=
  ⟨h.stronglyQuasithin, h.isKGroupCat⟩
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Campbell
