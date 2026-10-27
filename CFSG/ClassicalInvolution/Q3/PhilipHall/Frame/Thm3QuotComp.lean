module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotStab
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf16Thm3
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3QuotLift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.T3
  CFSG.ClassicalInvolution.Asc77.T3Typed CFSG.ClassicalInvolution.Asc77.T3Core
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {Y : Type} [Group Y] [Finite Y] {Φ : Set (Subgroup Y)} {X : Subgroup Y} [X.Normal]

theorem exists_conj_aSet_of_map (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {M J : Subgroup Y}
    (hM : M ∈ Φ) (hJ : J ∈ Φ)
    (h : J.map (QuotientGroup.mk' X) ∈ aSet (quotFamily Φ X) (M.map (QuotientGroup.mk' X))) :
    ∃ n ∈ X, conjSub n J ∈ aSet Φ M := by
  obtain ⟨zb, jb, hvb⟩ := h
  have hne : J.map (QuotientGroup.mk' X) ≠ M.map (QuotientGroup.mk' X) := hvb.ne
  obtain ⟨n, hn, hstar⟩ := (omegaStarNbr_map_iff hΦ hX hJ hM hne).mp hvb.star
  set J₁ : Subgroup Y := conjSub n⁻¹ J with hJ₁def
  have hJ₁Φ : J₁ ∈ Φ := hΦ.conjInvariant _ _ hJ
  have himg : J₁.map (QuotientGroup.mk' X) = J.map (QuotientGroup.mk' X) :=
    OddQuot.map_conjSub_of_mem (X.inv_mem hn) J
  have hstar₁ : J₁ ∈ omegaStarNbr Φ M := by
    have := omegaStarNbr_conj hΦ.conjInvariant hstar n⁻¹
    rwa [conjSub_inv_conjSub, ← hJ₁def] at this
  have hnbr₁ : J₁ ∉ omegaNbr Φ M := by
    intro h1
    apply hvb.not_nbr
    rw [← himg]
    exact (omegaNbr_map_iff hΦ hX hJ₁Φ hM (himg ▸ hne)).mpr ⟨1, X.one_mem, by rwa [conjSub_one]⟩
  obtain ⟨z, hz⟩ := Sec6Gen.exists_uniqueInvolution hΦ hM
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΦ hJ₁Φ
  have e1 : QuotientGroup.mk' X z = zb :=
    (isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX M) hz).eq hvb.hzK
  have e2 : QuotientGroup.mk' X j = jb := by
    have h1 := isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX J₁) hj
    rw [himg] at h1
    exact h1.eq hvb.hzJ
  refine ⟨n⁻¹, X.inv_mem hn, z, j, ⟨hstar₁, hnbr₁, hz, hj, fun g hg hgM => ?_⟩⟩
  have h2 := map_pairNormalizers_le (N := X) M J₁ z j (Subgroup.mem_map_of_mem _ hg)
  rw [himg, e1, e2] at h2
  apply hvb.no_conj _ h2
  have h3 := congrArg (Subgroup.map (QuotientGroup.mk' X)) hgM
  rw [AscQuot.map_conjSub, himg] at h3
  exact h3

theorem aStar_map_eq (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K : Subgroup Y}
    (hK : K ∈ Φ) :
    (fun L : Subgroup Y => L.map (QuotientGroup.mk' X)) '' aStar Φ K =
      aStar (quotFamily Φ X) (K.map (QuotientGroup.mk' X)) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨L, hL, rfl⟩
    induction hL with
    | refl => exact Relation.ReflTransGen.refl
    | tail hab hbc ih =>
      rename_i b c
      have hbΦ : b ∈ Φ := mem_of_mem_aStar hK hab
      have hcΦ : c ∈ Φ := hbc.1
      refine ih.tail ⟨map_mem_quotFamily hcΦ, ?_⟩
      obtain ⟨-, hA | hA | ⟨htw, hne⟩⟩ := hbc
      · exact Or.inl (aSet_map hΦ hX hbΦ hA)
      · exact Or.inr (Or.inl (aSet_map hΦ hX hcΦ hA))
      · obtain ⟨-, z, hzb, hzc⟩ := htw
        exact Or.inr (Or.inr ⟨⟨map_mem_quotFamily hcΦ, QuotientGroup.mk' X z,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX b) hzb,
          isUniqueInvolution_map_mk_of_odd (odd_natCard_inf hX c) hzc⟩,
          fun h => hne (eq_of_map_eq_of_inv_eq hΦ hX hcΦ hbΦ hzc hzb h)⟩)
  · intro Lb hLb
    induction hLb with
    | refl => exact ⟨K, Relation.ReflTransGen.refl, rfl⟩
    | tail _ hbc ih =>
      rename_i bb cb
      obtain ⟨b, hb, rfl⟩ := ih
      have hbΦ : b ∈ Φ := mem_of_mem_aStar hK hb
      obtain ⟨⟨c₀, hc₀, rfl⟩, hA | hA | ⟨htw, hne⟩⟩ := hbc
      · obtain ⟨n, hn, hnA⟩ := exists_conj_aSet_of_map hΦ hX hbΦ hc₀ hA
        refine ⟨conjSub n c₀, hb.tail ⟨hΦ.conjInvariant n c₀ hc₀, Or.inl hnA⟩, ?_⟩
        exact OddQuot.map_conjSub_of_mem hn c₀
      · obtain ⟨n, hn, hnA⟩ := exists_conj_aSet_of_map hΦ hX hc₀ hbΦ hA
        have hbA : b ∈ aSet Φ (conjSub n⁻¹ c₀) := by
          have := aSet_conj hΦ.conjInvariant hnA n⁻¹
          rwa [conjSub_inv_conjSub] at this
        refine ⟨conjSub n⁻¹ c₀, hb.tail ⟨hΦ.conjInvariant n⁻¹ c₀ hc₀, Or.inr (Or.inl hbA)⟩, ?_⟩
        exact OddQuot.map_conjSub_of_mem (X.inv_mem hn) c₀
      · obtain ⟨K', hK', hK'ne, hK'map⟩ := OddQuot.exists_twin_of_map hΦ hX hbΦ htw hne
        exact ⟨K', hb.tail ⟨hK'.1, Or.inr (Or.inr ⟨hK', hK'ne⟩)⟩, hK'map⟩

theorem map_mem_aStar (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K L : Subgroup Y}
    (hK : K ∈ Φ) (hL : L ∈ aStar Φ K) :
    L.map (QuotientGroup.mk' X) ∈ aStar (quotFamily Φ X) (K.map (QuotientGroup.mk' X)) := by
  rw [← aStar_map_eq hΦ hX hK]
  exact ⟨L, hL, rfl⟩

theorem map_mem_aStar_iff (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K : Subgroup Y}
    (hK : K ∈ Φ) (hA : ¬ AEmpty Φ K) {L : Subgroup Y} (hL : L ∈ Φ) :
    L.map (QuotientGroup.mk' X) ∈ aStar (quotFamily Φ X) (K.map (QuotientGroup.mk' X)) ↔
      L ∈ aStar Φ K := by
  refine ⟨fun h => ?_, map_mem_aStar hΦ hX hK⟩
  rw [← aStar_map_eq hΦ hX hK] at h
  obtain ⟨L', hL', heq⟩ := h
  obtain ⟨n, hn, rfl⟩ := exists_conj_of_map_eq hΦ hX (mem_of_mem_aStar hK hL') hL heq
  exact (mem_conjStab_iff.mp (le_conjStab_aStar_of_normal hΦ hX hK hA hn) L').mpr hL'

theorem omegaGen_aStar_map (hΦ : HypOmegaGen Φ) (hX : Odd (Nat.card X)) {K : Subgroup Y}
    (hK : K ∈ Φ) :
    (omegaGen (aStar Φ K)).map (QuotientGroup.mk' X) =
      omegaGen (aStar (quotFamily Φ X) (K.map (QuotientGroup.mk' X))) := by
  rw [← aStar_map_eq hΦ hX hK]
  unfold omegaGen
  simp only [Subgroup.map_iSup, iSup_image]

theorem closure_twoElts_eq_of_typeRHyp (hΦ : FrameAEmptyPf.TypeRHyp Φ) {K : Subgroup Y}
    (hK : K ∈ Φ) : Subgroup.closure {x : Y | x ∈ K ∧ IsPGroup 2 (Subgroup.zpowers x)} = K := by
  rcases hΦ.hyp.omega2 K hK with h1 | hne
  · exact h1
  · exfalso
    obtain ⟨e⟩ := hne
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp ((hΦ.twoGroup K hK).of_equiv e)
    rw [natCard_sl2Three] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm3Quot
