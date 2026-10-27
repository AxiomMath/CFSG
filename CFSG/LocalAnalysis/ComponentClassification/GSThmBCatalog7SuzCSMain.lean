module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSZero
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7SuzCSThree
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4InputsCenter
public import CFSG.LocalAnalysis.OddStandard.GlueL34
public import CFSG.Sporadic.SmallOddCore.Assembly
public import CFSG.Sporadic.SuzOddCore.CTIComponents
public import CFSG.Sporadic.SuzOddCore.SmallAut

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace SuzCS

open CFSG CFSG.LocalCores CFSG.Sporadic.SuzOddCore CFSG.Monster.B.Co2 CFSG.Certificates Subgroup

theorem suzAutModel :
    CFSG.Sporadic.SmallOddCore.AutModel suzM suzT where
  le := suzM_le_suzT
  conj_mem := fun _ hx _ hp => suzT_conj_mem_suzM hx hp
  surj := fun α => by
    obtain ⟨t, ht⟩ := suzConjT_bijective.2 α
    refine ⟨t, t.2, fun p => ?_⟩
    rw [← ht, suzConjT_apply]
  inj := fun x hx hc => by
    have h1 : suzConjT ⟨x, hx⟩ = suzConjT 1 := by
      refine MulEquiv.ext fun m => Subtype.ext ?_
      rw [suzConjT_apply, map_one, MulAut.one_apply]
      show x * (m : Equiv.Perm (Fin 1782)) * x⁻¹ = m
      rw [hc m m.2]
      group
    exact congrArg Subtype.val (suzConjT_injective h1)

theorem model
    {i : ℕ} (hi : i < 4) {G' J R : Subgroup (Equiv.Perm (Fin 1782))} {τ : Equiv.Perm (Fin 1782)}
    (hG'T : G' ≤ suzT) (hMG' : suzM ≤ G') (hJq : IsQuasisimple J)
    (hJcard : Nat.card (J ⧸ center J) = 20160) (hJY : J ≤ G' ⊓ centralizer {suzInv i})
    (hJc : IsComponent (J.subgroupOf (G' ⊓ centralizer {suzInv i})))
    (hRM : R ≤ suzM) (hRt : R ≤ centralizer {suzInv i}) (hR2 : IsPGroup 2 R)
    (hRmax : ∀ H : Subgroup (Equiv.Perm (Fin 1782)), H ≤ suzM ⊓ normalizer (J : Set _) →
      IsPGroup 2 H → Nat.card H ≤ Nat.card R)
    (hτG : τ ∈ G') (hτt : τ * suzInv i = suzInv i * τ) (hτJ : ∀ x ∈ J, τ * x = x * τ)
    (hτR : ∀ r ∈ R, τ * r = r * τ) : τ = 1 ∨ τ = suzInv i := by
  have hJp : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJq.1
  have hJM : J ≤ suzM :=
    le_of_perfect_of_index_two suzM_index_T ((hJY.trans inf_le_left).trans hG'T) hJp
  have hJE : J ≤ invE i := by
    rw [invE_eq_centM hi]
    exact fun x hx => ⟨(hJY hx).2, hJM hx⟩
  have hEY : invE i ≤ G' ⊓ centralizer {suzInv i} := by
    rw [invE_eq_centM hi]
    exact fun x hx => ⟨hMG' hx.2, hx.1⟩
  have hB := isComponent_subgroupOf_of_le hJE hEY hJc
  have hBcard : Nat.card (J.subgroupOf (invE i) ⧸ center (J.subgroupOf (invE i))) = 20160 := by
    rw [card_quotient_center_equiv (Subgroup.subgroupOfEquivOfLe hJE)]
    exact hJcard
  have hEM : invE i ≤ suzM := by
    rw [invE_eq_centM hi]
    exact inf_le_right
  interval_cases i
  ·
    obtain ⟨hn, hz⟩ := zero_model hB
    have hEN : invE 0 ≤ normalizer (J : Set (Equiv.Perm (Fin 1782))) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJE).mp hn
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 (invE 0)))
    have hE0 : Nat.card (invE 0) = 161280 := by
      rw [card_invE (i := 0) (by norm_num)]
      rfl
    have hS : Nat.card S = 2 ^ 9 := by
      rw [Sylow.card_eq_multiplicity, hE0, factorization_eq_of Nat.prime_two
        (show 161280 = 2 ^ 9 * 315 by norm_num) (by norm_num)]
    set S' := (S : Subgroup (invE 0)).map (invE 0).subtype
    have hS'c : Nat.card S' = 2 ^ 9 := by
      rw [Subgroup.card_map_of_injective (invE 0).subtype_injective]
      exact hS
    have hS'le : S' ≤ suzM ⊓ normalizer (J : Set (Equiv.Perm (Fin 1782))) := by
      rintro _ ⟨s, -, rfl⟩
      exact ⟨hEM s.2, hEN s.2⟩
    have h9 := hRmax S' hS'le (IsPGroup.of_card hS'c)
    rw [hS'c] at h9
    have hRE : R ≤ invE 0 := by
      rw [invE_eq_centM (i := 0) (by norm_num)]
      exact fun r hr => ⟨hRt hr, hRM hr⟩
    exact hz τ R (hG'T hτG) hτt hτJ hRE hR2 h9 hτR
  ·
    exact absurd hB (CTI_Suz_second_involution_centralizer_has_no_components.2 _)
  ·
    exfalso
    have hd : Nat.card (J.subgroupOf (invE 2)) ∣ 190080 := by
      have h := Subgroup.card_subgroup_dvd_card (J.subgroupOf (invE 2))
      rwa [card_invE (i := 2) (by norm_num)] at h
    have h7 : 7 ∣ Nat.card (J.subgroupOf (invE 2)) := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center _), hBcard]
      exact (show 7 ∣ 20160 by norm_num).mul_right _
    have := h7.trans hd
    norm_num at this
  ·
    exact (three_model _ hB hBcard).elim

end SuzCS

open CFSG CFSG.LocalCores SuzCS CFSG.Sporadic.SuzOddCore Subgroup in
theorem centerSylowSuz :
    OutInv.CenterSylowSuz := by
  intro G _ _ N α J R τ hcfg hN hJ
  obtain ⟨hNn, hC, hα2, hJα, hJc, hstd, hRN, hRα, hRS, hτα, hτJ, hτR, -⟩ := hcfg
  have : N.Normal := hNn
  obtain ⟨e⟩ := hN
  set θ : N ≃* suzM := e.trans suzEquivM
  have hM := suzAutModel
  set ι := hM.embed N θ
  have hι : Function.Injective ι := hM.embed_injective N θ hC
  have hιT : ∀ g, ι g ∈ suzT := hM.embed_mem N θ
  have hιN : ∀ n : N, ι n = θ n := hM.embed_coe N θ
  have ha2 : orderOf (ι α) = 2 := by rw [orderOf_injective ι hι, hα2]
  obtain ⟨i, ⟨hi, c, hc, hca⟩, -⟩ := suzT_involution_class (hιT α) ha2
  set κ : G →* Equiv.Perm (Fin 1782) := (MulAut.conj c⁻¹).toMonoidHom.comp ι with hκ
  have hκa : ∀ g, κ g = c⁻¹ * ι g * c := fun g => by
    simp [hκ]
  have hκinj : Function.Injective κ := (MulAut.conj c⁻¹).injective.comp hι
  have hκα : κ α = suzInv i := by
    rw [hκa, ← hca]
    group
  have hκT : ∀ g, κ g ∈ suzT := fun g => by
    rw [hκa]
    exact suzT.mul_mem (suzT.mul_mem (suzT.inv_mem hc) (hιT g)) hc
  have hκN : ∀ n ∈ N, κ n ∈ suzM := by
    intro n hn
    rw [hκa, show ι n = θ ⟨n, hn⟩ from hιN ⟨n, hn⟩]
    have := suzT_conj_mem_suzM (suzT.inv_mem hc) (θ ⟨n, hn⟩).2
    rwa [inv_inv] at this
  have hMκ : ∀ m ∈ suzM, ∃ n ∈ N, κ n = m := by
    intro m hm
    have hm' : c * m * c⁻¹ ∈ suzM := suzT_conj_mem_suzM hc hm
    refine ⟨(θ.symm ⟨_, hm'⟩ : G), (θ.symm ⟨_, hm'⟩).2, ?_⟩
    rw [hκa, hιN, MulEquiv.apply_symm_apply]
    group
  have hcomm : ∀ {x y : G}, x * y = y * x → κ x * κ y = κ y * κ x := fun h => by
    rw [← map_mul, h, map_mul]
  set G' := κ.range
  have hG'T : G' ≤ suzT := by
    rintro _ ⟨g, rfl⟩
    exact hκT g
  have hMG' : suzM ≤ G' := by
    intro m hm
    obtain ⟨n, -, hn⟩ := hMκ m hm
    exact ⟨n, hn⟩
  have eJ : J ≃* J.map κ := J.equivMapOfInjective κ hκinj
  have hJq : IsQuasisimple (J.map κ) := isQuasisimple_of_mulEquiv eJ hstd.1
  have hJcard : Nat.card (J.map κ ⧸ center (J.map κ)) = 20160 := by
    rw [← card_quotient_center_equiv eJ]
    exact CFSG.OddStandard.GlueL34.card_eq_of_lieModel_psl34 hJ
  have hJY : J.map κ ≤ G' ⊓ centralizer {suzInv i} := by
    rintro _ ⟨j, hj, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨⟨j, rfl⟩, ?_⟩
    rw [mem_centralizer_singleton_iff, ← hκα]
    exact hcomm (mem_centralizer_singleton_iff.mp (hJα hj))
  have hmapC : (centralizer ({α} : Set G)).map κ = G' ⊓ centralizer {suzInv i} := by
    ext x
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨⟨g, rfl⟩, ?_⟩
      rw [mem_centralizer_singleton_iff, ← hκα]
      exact hcomm (mem_centralizer_singleton_iff.mp hg)
    · intro hx
      obtain ⟨⟨g, rfl⟩, hg⟩ := Subgroup.mem_inf.mp hx
      refine ⟨g, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      rw [mem_centralizer_singleton_iff] at hg
      apply hκinj
      rw [map_mul, map_mul, hκα]
      exact hg
  set φ : centralizer ({α} : Set G) ≃* ↥(G' ⊓ centralizer {suzInv i}) :=
    ((centralizer ({α} : Set G)).equivMapOfInjective κ hκinj).trans
      (MulEquiv.subgroupCongr hmapC)
  have hJc' : IsComponent ((J.map κ).subgroupOf (G' ⊓ centralizer {suzInv i})) := by
    have h1 := isComponent_map_mulEquiv φ hJc
    have h2 : (J.subgroupOf (centralizer ({α} : Set G))).map φ.toMonoidHom =
        (J.map κ).subgroupOf (G' ⊓ centralizer {suzInv i}) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x, hx, rfl⟩
      · intro hy
        obtain ⟨g, hg, hgy⟩ := hy
        refine ⟨⟨g, hJα hg⟩, hg, Subtype.ext ?_⟩
        exact hgy
    rwa [h2] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := hRS
  have hR2 : IsPGroup 2 R := by
    have h := S.isPGroup'
    rw [hS] at h
    exact h.of_equiv (Subgroup.subgroupOfEquivOfLe hRN)
  have hRM' : R.map κ ≤ suzM := by
    rintro _ ⟨r, hr, rfl⟩
    exact hκN r (hRN hr).1
  have hRt' : R.map κ ≤ centralizer {suzInv i} := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_centralizer_singleton_iff, ← hκα]
    exact hcomm (mem_centralizer_singleton_iff.mp (hRα hr))
  have hR2' : IsPGroup 2 (R.map κ) := hR2.of_equiv (R.equivMapOfInjective κ hκinj)
  have hRmax : ∀ H : Subgroup (Equiv.Perm (Fin 1782)),
      H ≤ suzM ⊓ normalizer ((J.map κ : Subgroup _) : Set _) → IsPGroup 2 H →
        Nat.card H ≤ Nat.card (R.map κ) := by
    intro H hH hH2
    set H₀ := H.comap κ
    have hH₀map : H₀.map κ = H :=
      Subgroup.map_comap_eq_self ((hH.trans inf_le_left).trans hMG')
    have hcardH : Nat.card H₀ = Nat.card H := by
      rw [← hH₀map]
      exact (Subgroup.card_map_of_injective hκinj).symm
    have hH₀N : H₀ ≤ N ⊓ normalizer (J : Set G) := by
      intro g hg
      have hgH : κ g ∈ H := hg
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨n, hn, hnk⟩ := hMκ (κ g) (hH hgH).1
        rw [← hκinj hnk]
        exact hn
      · rw [mem_normalizer_iff]
        intro h
        have hn := mem_normalizer_iff.mp (hH hgH).2 (κ h)
        rw [Subgroup.mem_map_iff_mem hκinj, ← map_inv, ← map_mul, ← map_mul,
          Subgroup.mem_map_iff_mem hκinj] at hn
        exact hn
    have hH₀2 : IsPGroup 2 H₀ := by
      have h := hH2
      rw [← hH₀map] at h
      exact h.of_equiv (H₀.equivMapOfInjective κ hκinj).symm
    have hP : IsPGroup 2 (H₀.subgroupOf (N ⊓ normalizer (J : Set G))) :=
      hH₀2.of_equiv (Subgroup.subgroupOfEquivOfLe hH₀N).symm
    obtain ⟨S', hS'⟩ := hP.exists_le_sylow
    have h1 := Subgroup.card_le_of_le hS'
    have h2 : Nat.card (S' : Subgroup ↥(N ⊓ normalizer (J : Set G))) =
        Nat.card (S : Subgroup ↥(N ⊓ normalizer (J : Set G))) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
    rw [h2, hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRN).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hH₀N).toEquiv, hcardH] at h1
    rw [Subgroup.card_map_of_injective hκinj]
    exact h1
  have hτt : κ τ * suzInv i = suzInv i * κ τ := by
    rw [← hκα]
    exact hcomm hτα
  have hτJ' : ∀ x ∈ J.map κ, κ τ * x = x * κ τ := by
    rintro _ ⟨j, hj, rfl⟩
    exact hcomm (hτJ j hj)
  have hτR' : ∀ r ∈ R.map κ, κ τ * r = r * κ τ := by
    rintro _ ⟨r, hr, rfl⟩
    exact hcomm (hτR r hr)
  rcases model hi hG'T hMG' hJq hJcard hJY hJc' hRM' hRt' hR2' hRmax ⟨τ, rfl⟩ hτt hτJ' hτR' with
    h | h
  · rw [← map_one κ] at h
    rw [hκinj h]
    exact one_mem _
  · rw [← hκα] at h
    rw [hκinj h]
    exact mem_zpowers α

end CFSG.ComponentClassification.CatFactsL4U4
