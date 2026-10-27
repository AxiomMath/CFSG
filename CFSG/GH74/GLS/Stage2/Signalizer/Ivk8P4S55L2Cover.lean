module

public import CFSG.GH74.GLS.Classes
import CFSG.CGT.PushingUpLit.CGT6.EmbModule.SL2Alt5
import CFSG.LieType.Steinberg.CentralExt.PSLSmall

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Cover

open Subgroup

theorem eq_top_of_perfect_two_quotient {E : Type} [Group E] [Finite E] [Group.IsPerfect E]
    (I : Subgroup E) [I.Normal] (h : ∀ e : E, ∃ n : ℕ, e ^ 2 ^ n ∈ I) : I = ⊤ := by
  have hp : IsPGroup 2 (E ⧸ I) := fun x => by
    obtain ⟨e, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨n, hn⟩ := h e
    exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hn⟩
  have : Group.IsNilpotent (E ⧸ I) := hp.isNilpotent
  have : Group.IsSolvable (E ⧸ I) := inferInstance
  by_contra hne
  have hnt : Nontrivial (E ⧸ I) := by
    have h1 : 1 < I.index := Subgroup.one_lt_index_of_ne_top hne
    rw [Subgroup.index_eq_card] at h1
    exact Finite.one_lt_card_iff_nontrivial.mp h1
  exact Group.IsPerfect.not_isSolvable (E ⧸ I) inferInstance

theorem hasSL2Model_five_of_even_center
    {K : Type} [Group K] [Finite K]
    (hK : CFSG.IsQuasisimple K) {F₀ : Type} [Field F₀] [Finite F₀] (hF₀ : Nat.card F₀ = 5)
    (e0 : (K ⧸ Subgroup.center K) ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)
    (h2 : 2 ∣ Nat.card (Subgroup.center K)) :
    CFSG.GH74.GLS.HasSL2Model K (fun q => q = 5) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Group.IsPerfect K := hK.1
  have : IsSimpleGroup (K ⧸ center K) := hK.2.1
  have : Group.IsPerfect (K ⧸ center K) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective (center K))
  have hS60 : Nat.card (K ⧸ center K) = 60 := by
    have hodd : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F₀) :=
      ⟨5, 1, by norm_num, by decide, le_rfl, by rw [hF₀]; norm_num⟩
    have h := CFSG.GorensteinWalter.psl2_card_formula F₀ hodd
    rw [hF₀] at h
    rw [Nat.card_congr e0.toEquiv]
    exact h.trans (by norm_num)
  have : Fintype F₀ := Fintype.ofFinite F₀
  have hk5 : 5 ≤ Fintype.card F₀ := by rw [Fintype.card_eq_nat_card, hF₀]
  have hk9 : Fintype.card F₀ ≠ 9 := by rw [Fintype.card_eq_nat_card, hF₀]; norm_num
  obtain ⟨-, ⟨eM⟩⟩ :=
    CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_two_hopfMultiplier_of_mulEquiv hk5 hk9 e0.symm
  obtain ⟨-, -, -, f, hf⟩ :=
    CFSG.RankThree.PerfectCover.perfect_central_kernel_quotient_of_schur_multiplier
      (QuotientGroup.mk' (center K)) (QuotientGroup.mk'_surjective _)
      (by rw [QuotientGroup.ker_mk'])
  obtain ⟨F⟩ := (CFSG.RankThree.PerfectCover.hopf_formula_hopfMultiplier (S := K ⧸ center K)).2
  have hM2 :
      Nat.card (Multiplicative (groupHomology.H2 (Rep.trivial ℤ (K ⧸ center K) ℤ))) = 2 := by
    rw [Nat.card_congr (F.trans eM).toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod,
      Fintype.card_eq_nat_card, hF₀]
    rfl
  have : Finite (Multiplicative (groupHomology.H2 (Rep.trivial ℤ (K ⧸ center K) ℤ))) :=
    Nat.finite_of_card_ne_zero (by rw [hM2]; norm_num)
  have hle : Nat.card f.range ≤ 2 := by
    rw [← hM2]
    exact Nat.card_le_card_of_surjective f.rangeRestrict f.rangeRestrict_surjective
  rw [hf, QuotientGroup.ker_mk'] at hle
  have hZ2 : Nat.card (center K) = 2 := le_antisymm hle (Nat.le_of_dvd Nat.card_pos h2)
  have hZp : IsPGroup 2 (center K) := IsPGroup.of_card (n := 1) (by rw [hZ2, pow_one])
  obtain ⟨eA⟩ := CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty hS60
  let ρ : K →* alternatingGroup (Fin 5) := eA.toMonoidHom.comp (QuotientGroup.mk' (center K))
  have hρs : Function.Surjective ρ := eA.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerρ : ρ.ker = center K := by
    ext x
    rw [MonoidHom.mem_ker]
    change eA (QuotientGroup.mk' (center K) x) = 1 ↔ x ∈ center K
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hno2 : ∀ I : Subgroup K, I.Normal → (∀ e : K, ∃ n : ℕ, e ^ 2 ^ n ∈ I) → I = ⊤ :=
    fun I _ h => eq_top_of_perfect_two_quotient I h
  rcases CFSG.CGT.PushingUpLit.CGT6.alt5_cover_cases' ρ hρs (hkerρ ▸ le_rfl) (hkerρ ▸ hZp)
      hno2 with hinj | ⟨⟨hiso⟩, -⟩
  · exfalso
    have hbot : ρ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ρ).mpr hinj
    rw [hkerρ] at hbot
    rw [hbot, Subgroup.card_bot] at hZ2
    exact absurd hZ2 (by norm_num)
  · exact ⟨ZMod 5, inferInstance, inferInstance, Nat.card_zmod 5,
      ⟨hiso.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 5))⟩⟩

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.L2Cover
