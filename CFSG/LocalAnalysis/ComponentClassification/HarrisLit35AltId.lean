module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35AltLarge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitLemma47Lift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalSmallStandardSource

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.L35

open CFSG Subgroup Equiv Equiv.Perm GrSLit.L34Facts CFSG.ComponentClassification.GSThmB.Catalog82A10

@[expose] noncomputable def hatHom {G : Type} [Group G] {K J : Subgroup G} (hJK : J ≤ K) :
    ↥J →* ↥(hatOf K J) where
  toFun x := ⟨QuotientGroup.mk (QuotientGroup.mk (⟨x, hJK x.2⟩ : ↥K)),
    ⟨_, ⟨⟨x, hJK x.2⟩, x.2, rfl⟩, rfl⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem hatHom_surjective {G : Type} [Group G] {K J : Subgroup G} (hJK : J ≤ K) :
    Function.Surjective (hatHom hJK) := by
  rintro ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩⟩
  exact ⟨⟨k, hk⟩, rfl⟩

namespace Config

variable {G : Type} [Group G] [Finite G] {p : ℕ} {w v : G} {L K : Subgroup G}

theorem lieModel_hat (h : Config G p w v L K) {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)} (hππ : π * π = 1) (hmemC : ∀ y, y ∈ fixedPoints (quotAut h.tau) ↔
      (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m))) {k : ℕ} (hk : 1 ≤ k)
    (hs5 : 5 ≤ p ^ k) (hLsl : IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L)) :
    Blueprint.LieModel ↥(hatOf K L) .PSL 2 p k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLeq, hT5⟩ := h.map_hat_eq_altOn e' hππ hmemC
  set T := π.supportᶜ with hTdef
  have hs : IsSimpleGroup ↥(altOn T) := isSimpleGroup_altOn T hT5
  let eL : ↥(hatOf K L) ≃* ↥(altOn T) :=
    ((hatOf K L).equivMapOfInjective _ (iota_injective e')).trans (MulEquiv.subgroupCongr hLeq)
  have hsL : IsSimpleGroup ↥(hatOf K L) := eL.isSimpleGroup
  have hLq2 : IsTwoQuasisimple ↥(hatOf K L) := (h.isTwoComponentIn_hat h.compLK).2.2
  have hnab : ∃ a b : ↥(hatOf K L), a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have hss := subsingleton_of_isPerfect_of_isSolvable hLq2.1 (Group.isSolvable_of_comm hc)
    exact (not_nontrivial_iff_subsingleton.mpr hss) hsL.toNontrivial
  obtain ⟨hQq, hQZ, hQm, -⟩ := Lemma47.sl2_facts h.prime h.ne_two hk hs5 hLsl
  set φ := hatHom h.L_le with hφdef
  have hφ : Function.Surjective φ := hatHom_surjective h.L_le
  have hOker : pPrimeCore 2 ↥L ≤ φ.ker := by
    have hn : ((pPrimeCore 2 ↥L).map φ).Normal :=
      (inferInstance : (pPrimeCore 2 ↥L).Normal).map φ hφ
    rcases hn.eq_bot_or_eq_top with hb | ht
    · exact (Subgroup.map_eq_bot_iff _).mp hb
    · exfalso
      apply not_odd_card_of_isTwoQuasisimple hLq2
      rw [← card_top, ← ht]
      exact Odd.of_dvd_nat (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp
        (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card)))
        (Subgroup.card_map_dvd _ _)
  set ψ : ↥L ⧸ pPrimeCore 2 ↥L →* ↥(hatOf K L) := QuotientGroup.lift _ φ hOker with hψdef
  have hψ : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hφ y
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hQo : Open.IsQuasisimple (↥L ⧸ pPrimeCore 2 ↥L) :=
    (AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQq)
  have hker : ψ.ker = center (↥L ⧸ pPrimeCore 2 ↥L) := by
    rcases Quasisimple.normal_le_center_or_eq_top hQo ψ.ker with hc | ht
    · have hdvd : Nat.card ↥ψ.ker ∣ 2 := by
        have h0 := Subgroup.card_dvd_of_le hc
        rwa [hQZ] at h0
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exfalso
        have hinj : Function.Injective ψ := by
          rw [← MonoidHom.ker_eq_bot_iff]
          exact Subgroup.eq_bot_of_card_eq _ h1
        have hZ := CatLeaf.center_eq_bot_of_simple hnab
        let e₀ := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
        have h3 : (center (↥L ⧸ pPrimeCore 2 ↥L)).map e₀.toMonoidHom = center ↥(hatOf K L) :=
          Subgroup.map_center_eq e₀
        rw [hZ, Subgroup.map_eq_bot_iff_of_injective (f := e₀.toMonoidHom) _ e₀.injective] at h3
        have h4 := hQZ
        rw [h3, card_bot] at h4
        exact absurd h4 (by norm_num)
      · exact Subgroup.eq_of_le_of_card_ge hc (by rw [hQZ, h2])
    · exfalso
      have hss : Subsingleton ↥(hatOf K L) := ⟨fun a b => by
        obtain ⟨x, rfl⟩ := hψ a
        obtain ⟨y, rfl⟩ := hψ b
        have hx : x ∈ ψ.ker := ht ▸ mem_top x
        have hy : y ∈ ψ.ker := ht ▸ mem_top y
        rw [MonoidHom.mem_ker] at hx hy
        rw [hx, hy]⟩
      exact (not_nontrivial_iff_subsingleton.mpr hss) hsL.toNontrivial
  let e₂ : (↥L ⧸ pPrimeCore 2 ↥L) ⧸ center (↥L ⧸ pPrimeCore 2 ↥L) ≃* ↥(hatOf K L) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  exact GSThmB.OddQuot.lieModel_of_equiv e₂ hQm

theorem params (h : Config G p w v L K) {m : ℕ}
    (e' : (↥K ⧸ pPrimeCore 2 ↥K) ⧸ center (↥K ⧸ pPrimeCore 2 ↥K) ≃* alternatingGroup (Fin m))
    {π : Perm (Fin m)} (hππ : π * π = 1) (hmemC : ∀ y, y ∈ fixedPoints (quotAut h.tau) ↔
      (e' y : Perm (Fin m)) * π = π * (e' y : Perm (Fin m))) {k : ℕ} (hk : 1 ≤ k)
    (hs5 : 5 ≤ p ^ k) (hLsl : IsSLTwoOver (p ^ k) (↥L ⧸ pPrimeCore 2 ↥L)) :
    ((π.supportᶜ).card = 5 ∧ p = 5 ∧ k = 1) ∨ ((π.supportᶜ).card = 6 ∧ p = 3 ∧ k = 2) := by
  obtain ⟨hLeq, hT5⟩ := h.map_hat_eq_altOn e' hππ hmemC
  set T := π.supportᶜ with hTdef
  have hlie := h.lieModel_hat e' hππ hmemC hk hs5 hLsl
  let eL : ↥(hatOf K L) ≃* alternatingGroup ↥T :=
    (((hatOf K L).equivMapOfInjective _ (iota_injective e')).trans
      (MulEquiv.subgroupCongr hLeq)).trans (altOnEquiv T).symm
  have hcard : Fintype.card ↥T = T.card := Fintype.card_coe T
  have h1 := (SymmetricLocal.alternating_psl_two_parameters_and_degree_seven_stated
    (hcard ▸ hT5) ⟨eL⟩).1 p k h.ne_two (N36.statedClassicalModel_of_lieModel' (Or.inl rfl) hlie)
  rwa [hcard] at h1

end Config

end CFSG.ComponentClassification.HarrisLit.L35
