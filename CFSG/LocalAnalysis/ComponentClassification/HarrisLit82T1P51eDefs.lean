module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Props

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.P51e

open CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

@[expose] def NoSpin7 (p : ℕ) (L : Type) [Group L] : Prop :=
  ∀ r : ℕ, 1 ≤ r → (Nat.card (center L)).factorization 2 = 1 →
    ¬ Blueprint.LieModel (L ⧸ center L) .POmegaOdd 3 p r

theorem NoSpin7.of_mulEquiv {L M : Type} [Group L] [Group M] {p : ℕ} (e : L ≃* M)
    (h : NoSpin7 p M) : NoSpin7 p L := by
  intro r hr hZ hL
  have hc : Nat.card (center M) = Nat.card (center L) :=
    (Nat.card_congr ((MulEquiv.subgroupCongr (Subgroup.map_center_eq e)).symm.trans
      ((center L).equivMapOfInjective e.toMonoidHom e.injective).symm).toEquiv)
  exact h r hr (hc ▸ hZ) (LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)) hL)

theorem noSpin7_of_odd_card_center {L : Type} [Group L] {p : ℕ}
    (h : Odd (Nat.card (center L))) : NoSpin7 p L := by
  intro r _ hZ _
  have h2 : ¬ 2 ∣ Nat.card (center L) := Nat.not_even_iff_odd.2 h ∘ even_iff_two_dvd.2
  rw [Nat.factorization_eq_zero_of_not_dvd h2] at hZ
  exact absurd hZ (by norm_num)

theorem center_quotient_eq_map_center {G : Type*} [Group G] [Group.IsPerfect G]
    (A : Subgroup G) [A.Normal] (hA : A ≤ center G) :
    center (G ⧸ A) = (center G).map (QuotientGroup.mk' A) := by
  refine le_antisymm (fun y hy => ?_) (map_center_le_center (QuotientGroup.mk'_surjective A))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A y
  let π : G ⧸ A →* G ⧸ center G :=
    QuotientGroup.map A (center G) (MonoidHom.id G) fun a ha => hA ha
  have hπ : Function.Surjective π := fun z => by
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (center G) z
    exact ⟨QuotientGroup.mk' A w, rfl⟩
  have h1 : π (QuotientGroup.mk' A x) ∈ center (G ⧸ center G) := by
    rw [mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := hπ z
    rw [← map_mul, ← map_mul, (mem_center_iff.1 hy) w]
  rw [Group.IsPerfect.center_quotient_center_eq_bot G, mem_bot] at h1
  have h2 : QuotientGroup.mk' (center G) x = 1 := h1
  exact ⟨x, (QuotientGroup.eq_one_iff x).1 h2, rfl⟩

def quotientCenterEquiv {G : Type*} [Group G] [Group.IsPerfect G] (A : Subgroup G) [A.Normal]
    (hA : A ≤ center G) : (G ⧸ A) ⧸ center (G ⧸ A) ≃* G ⧸ center G :=
  (QuotientGroup.quotientMulEquivOfEq (center_quotient_eq_map_center A hA)).trans
    (QuotientGroup.quotientQuotientEquivQuotient A (center G) hA)

theorem card_center_eq {G : Type*} [Group G] [Group.IsPerfect G] (A : Subgroup G) [A.Normal]
    (hA : A ≤ center G) : Nat.card (center G) = Nat.card (center (G ⧸ A)) * Nat.card A := by
  have h1 := Subgroup.relIndex_mul_card A (center G)
  have h2 := Subgroup.relIndex_ker (center G) (QuotientGroup.mk' A)
  rw [QuotientGroup.ker_mk'] at h2
  rw [inf_eq_left.2 hA, h2, ← center_quotient_eq_map_center A hA] at h1
  exact h1.symm

theorem not_isCoverOf_of_noSpin7 {J : Type} [Group J] [Finite J] (hq : IsQuasisimple J)
    {p : ℕ} (h : NoSpin7 p J) {r : ℕ} (hr : 1 ≤ r) :
    ¬ IsCoverOf .POmegaOdd 3 p r 2 (J ⧸ pPrimeCore 2 J) := by
  rintro ⟨hq', hZ, hLM⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect J := hq.1
  have hne : pPrimeCore 2 J ≠ ⊤ := by
    intro htop
    have : Subsingleton (J ⧸ pPrimeCore 2 J) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have := LocalCores.isQuasisimple_nontrivial hq'
    exact false_of_nontrivial_of_subsingleton (J ⧸ pPrimeCore 2 J)
  have hOZ : pPrimeCore 2 J ≤ center J :=
    (LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq _).resolve_right hne
  have hcard := card_center_eq (pPrimeCore 2 J) hOZ
  rw [hZ] at hcard
  have hcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 J)) :=
    pPrimeCore_coprime_card (p := 2) (G := J)
  have hO0 : Nat.card (pPrimeCore 2 J) ≠ 0 := Nat.card_pos.ne'
  have hv : (Nat.card (center J)).factorization 2 = 1 := by
    rw [hcard, Nat.factorization_mul two_ne_zero hO0, Finsupp.add_apply,
      Nat.Prime.factorization_self Nat.prime_two,
      Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hcop)]
  exact h r hr hv (LieType.CurtisTits.lieModel_of_mulEquiv
    (quotientCenterEquiv (pPrimeCore 2 J) hOZ) hLM)

@[expose] def FamNoSpin7 (t : StatedLieTag) : Prop :=
  ∀ (X : Type) [Group X] (n p f : ℕ), p.Prime → p ≠ 2 → StatedLieAdmissible t n p f →
    Blueprint.LieModel X t n p f → ∀ g : X, orderOf (MulAut.conj g) = 2 →
      ∀ L : Subgroup (fixedSubgroup (MulAut.conj g)), IsComponent L → NoSpin7 p L

end CFSG.ComponentClassification.HarrisLit.T1.P51e
