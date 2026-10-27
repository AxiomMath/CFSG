module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Fusion
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeSylowIso
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicHe
public import CFSG.Sporadic.HeldB.InnerClass
public import CFSG.Sporadic.HeldB.OuterCentQS

public section

namespace CFSG.ComponentClassification.AS81

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Sporadic.HeldB CFSG.Sporadic.Schreier

section General

variable {Ω : Type} [Group Ω] [Finite Ω]

omit [Finite Ω] in
theorem le_centerIn_of_normal_odd {C D N' : Subgroup Ω} (hDC : D ≤ C)
    (hD2 : D.relIndex C = 2) (hs : IsSimpleGroup (↥D ⧸ center ↥D))
    (he : Even (Nat.card (↥D ⧸ center ↥D))) (hN'C : N' ≤ C)
    (hN'n : C ≤ normalizer (N' : Set Ω)) (hN'o : Odd (Nat.card N')) : N' ≤ centerIn D := by
  have hN'D : N' ≤ D := by
    intro n hn
    have h2 : (⟨n, hN'C hn⟩ : ↥C) ^ 2 ∈ D.subgroupOf C := Subgroup.sq_mem_of_index_two hD2 _
    have h2' : n ^ 2 ∈ D := by simpa [mem_subgroupOf] using h2
    obtain ⟨k, hk⟩ : Odd (orderOf n) := hN'o.of_dvd_nat (Subgroup.orderOf_dvd_natCard N' hn)
    have e : n = (n ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf n + 1 by omega, pow_succ, pow_orderOf_eq_one,
        one_mul]
    rw [e]
    exact pow_mem h2' _
  have hKn : (N'.subgroupOf D).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hN'n (hDC g.2)) n).mp hn
    simpa using this⟩
  have hKo : Odd (Nat.card (N'.subgroupOf D)) := by
    rwa [Nat.card_congr (subgroupOfEquivOfLe hN'D).toEquiv]
  have hKZ : N'.subgroupOf D ≤ center ↥D := by
    have hmap := hKn.map (QuotientGroup.mk' (center ↥D)) (QuotientGroup.mk'_surjective _)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((N'.subgroupOf D).map (QuotientGroup.mk' (center ↥D))) with h | h
    · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    · exfalso
      have h1 : Nat.card ((N'.subgroupOf D).map (QuotientGroup.mk' (center ↥D))) ∣
          Nat.card (N'.subgroupOf D) := card_map_dvd _ _
      rw [h, card_top] at h1
      exact (Nat.not_even_iff_odd.mpr (hKo.of_dvd_nat h1)) he
  intro n hn
  have := hKZ (show (⟨n, hN'D hn⟩ : ↥D) ∈ N'.subgroupOf D from hn)
  exact ⟨hN'D hn, mem_centralizer_iff.mpr fun d hd =>
    congrArg Subtype.val (mem_center_iff.mp this ⟨d, hd⟩)⟩

theorem relIndex_centralizer_conj {Y : Subgroup Ω} {c : Ω} (hc : c ∈ normalizer (Y : Set Ω))
    (t : Ω) : (centralizer ({c * t * c⁻¹} : Set Ω)).relIndex Y =
      (centralizer ({t} : Set Ω)).relIndex Y := by
  have h1 := relIndex_centralizer_mul_card Y (c * t * c⁻¹)
  have h2 := relIndex_centralizer_mul_card Y t
  rw [card_inf_centralizer_conj_of_mem_normalizer hc] at h1
  have hpos : 0 < Nat.card (Y ⊓ centralizer ({t} : Set Ω) : Subgroup Ω) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)

theorem card_inf_centralizer_eq_mul {P Y : Subgroup Ω} (hPY : P ≤ Y) (hidx : P.relIndex Y ≤ 2)
    (t : Ω) : ∃ r : ℕ, (r = 1 ∨ r = 2) ∧
      Nat.card (Y ⊓ centralizer ({t} : Set Ω) : Subgroup Ω) =
        r * Nat.card (P ⊓ centralizer ({t} : Set Ω) : Subgroup Ω) := by
  refine ⟨P.relIndex (Y ⊓ centralizer ({t} : Set Ω)), ?_, ?_⟩
  · have hne : ∀ K : Subgroup Ω, P.relIndex K ≠ 0 := fun K h0 => by
      have h := relIndex_mul_card P K
      rw [h0, zero_mul] at h
      exact (Nat.card_pos (α := K)).ne h
    have h1 : P.relIndex (Y ⊓ centralizer ({t} : Set Ω)) ≤ P.relIndex Y :=
      relIndex_le_of_le_right inf_le_left (hne Y)
    have := hne (Y ⊓ centralizer ({t} : Set Ω))
    omega
  · rw [← relIndex_mul_card P (Y ⊓ centralizer ({t} : Set Ω)),
      show P ⊓ (Y ⊓ centralizer ({t} : Set Ω)) = P ⊓ centralizer ({t} : Set Ω) by
        rw [← inf_assoc, inf_eq_left.mpr hPY]]

end General

section Classes

theorem he_outer_not_mem
    {c : Equiv.Perm (Fin 8330)} (hc : c ∈ heP) {x : Equiv.Perm (Fin 8330)} (hx : orderOf x = 5)
    (N' : Subgroup (Equiv.Perm (Fin 8330)))
    (hN'C : N' ≤ heP ⊓ centralizer ({c * heAutU * c⁻¹} : Set (Equiv.Perm (Fin 8330))))
    (hN'n : heP ⊓ centralizer ({c * heAutU * c⁻¹} : Set (Equiv.Perm (Fin 8330))) ≤
      normalizer (N' : Set (Equiv.Perm (Fin 8330))))
    (hN'o : Odd (Nat.card N')) : x ∉ N' := by
  have hinj : Function.Injective (MulAut.conj c).toMonoidHom := (MulAut.conj c).injective
  have hC : heP ⊓ centralizer ({c * heAutU * c⁻¹} : Set (Equiv.Perm (Fin 8330))) =
      heOuterC.map (MulAut.conj c).toMonoidHom := by
    rw [heOuterC_eq, map_conj_inf_centralizer_of_mem_normalizer (le_normalizer hc)]
  rw [hC] at hN'C hN'n
  have hCD : heOuterC ≤ normalizer (heOuterD : Set (Equiv.Perm (Fin 8330))) := by
    intro y hy
    refine AS76b.mem_normalizer_of_map_conj_le ?_
    have hmap : heOuterC.map (MulAut.conj y).toMonoidHom = heOuterC := by
      refine eq_of_le_of_card_ge ?_ ?_
      · rintro _ ⟨w, hw, rfl⟩
        exact heOuterC.mul_mem (heOuterC.mul_mem hy hw) (heOuterC.inv_mem hy)
      · rw [card_map_of_injective (MulAut.conj y).injective]
    rw [heOuterD_eq_commutator, Subgroup.map_commutator, hmap]
  have hD2 : (heOuterD.map (MulAut.conj c).toMonoidHom).relIndex
      (heOuterC.map (MulAut.conj c).toMonoidHom) = 2 := by
    rw [relIndex_map_map_of_injective _ _ hinj]
    exact heOuterD_relIndex
  let eD : ↥heOuterD ≃* ↥(heOuterD.map (MulAut.conj c).toMonoidHom) :=
    heOuterD.equivMapOfInjective _ hinj
  let eQ : ↥heOuterD ⧸ center ↥heOuterD ≃*
      ↥(heOuterD.map (MulAut.conj c).toMonoidHom) ⧸
        center ↥(heOuterD.map (MulAut.conj c).toMonoidHom) :=
    QuotientGroup.congr _ _ eD (map_center_eq eD)
  have hs : IsSimpleGroup (↥(heOuterD.map (MulAut.conj c).toMonoidHom) ⧸
      center ↥(heOuterD.map (MulAut.conj c).toMonoidHom)) :=
    (MulEquiv.isSimpleGroup_congr eQ).mp heOuterQuot_simple
  have he : Even (Nat.card (↥(heOuterD.map (MulAut.conj c).toMonoidHom) ⧸
      center ↥(heOuterD.map (MulAut.conj c).toMonoidHom))) := by
    rw [← Nat.card_congr eQ.toEquiv, card_heOuterD_quot]
    decide
  have hle := le_centerIn_of_normal_odd (map_mono heOuterD_le_C) hD2 hs he hN'C hN'n hN'o
  have hZ3 : Nat.card (centerIn (heOuterD.map (MulAut.conj c).toMonoidHom)) = 3 := by
    rw [← card_centerIn_eq_of_mulEquiv eD, centerIn_eq_map_center',
      card_map_of_injective heOuterD.subtype_injective, card_center_heOuterD]
  intro hxN
  have h := Subgroup.orderOf_dvd_natCard _ (hle hxN)
  rw [hx, hZ3] at h
  exact absurd h (by decide)

theorem he_involution_class
    {w : Equiv.Perm (Fin 8330)} (hwR : w ∈ heAutGroup) (hw2 : orderOf w = 2) :
    ∃ c ∈ heP, (w ∈ heP ∧ w = c * heGenPerm 0 * c⁻¹) ∨ (w ∈ heP ∧ w = c * heT1P * c⁻¹) ∨
      (w ∉ heP ∧ w = c * heAutU * c⁻¹) := by
  by_cases hwP : w ∈ heP
  · rcases involution_conj_cases hwP hw2 with ⟨c, hc, h⟩ | ⟨c, hc, h⟩
    · exact ⟨c, hc, Or.inl ⟨hwP, h⟩⟩
    · exact ⟨c, hc, Or.inr (Or.inl ⟨hwP, h⟩)⟩
  · obtain ⟨c, hc, h⟩ := exists_conj_heAutU hwR hwP hw2
    exact ⟨c, hc, Or.inr (Or.inr ⟨hwP, h⟩)⟩

theorem he_two_dvd_relIndex
    {Y : Subgroup (Equiv.Perm (Fin 8330))} (hPY : heP ≤ Y) (hYR : Y ≤ heAutGroup) :
    2 ∣ (centralizer ({heGenPerm 0} : Set (Equiv.Perm (Fin 8330)))).relIndex Y ∧
      2 ∣ (centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330)))).relIndex Y := by
  have hidx : heP.relIndex heAutGroup ≤ 2 := heP_relIndex_heAutGroup.le
  have h0 : Nat.card (heP ⊓ centralizer ({heGenPerm 0} : Set (Equiv.Perm (Fin 8330))) :
      Subgroup (Equiv.Perm (Fin 8330))) = 161280 := card_heP_cent0
  have hu : Nat.card (heP ⊓ centralizer ({heAutU} : Set (Equiv.Perm (Fin 8330))) :
      Subgroup (Equiv.Perm (Fin 8330))) = 15120 := card_heP_centralizer_heAutU
  have h1 := relIndex_centralizer_mul_card Y (heGenPerm 0)
  have h2 := relIndex_centralizer_mul_card Y heAutU
  rcases eq_or_eq_of_card_le_two_mul hPY hYR (by rw [card_heAutGroup, card_heP]) with rfl | rfl
  · rw [h0, card_heP] at h1
    rw [hu, card_heP] at h2
    constructor <;> omega
  · obtain ⟨r, hr, hrc⟩ := card_inf_centralizer_eq_mul heP_le_heAutGroup hidx (heGenPerm 0)
    obtain ⟨s, hs, hsc⟩ := card_inf_centralizer_eq_mul heP_le_heAutGroup hidx heAutU
    rw [hrc, h0, card_heAutGroup] at h1
    rw [hsc, hu, card_heAutGroup] at h2
    constructor
    · rcases hr with rfl | rfl <;> omega
    · rcases hs with rfl | rfl <;> omega

end Classes

theorem he_fusion :
    ∀ Y : Subgroup (Equiv.Perm (Fin 8330)), heP ≤ Y → Y ≤ heAutGroup →
      ∀ σ ∈ Y, ∀ τ ∈ Y, orderOf σ = 2 → orderOf τ = 2 →
        ¬ 2 ∣ (centralizer ({σ} : Set (Equiv.Perm (Fin 8330)))).relIndex Y →
        2 ∣ (centralizer ({τ} : Set (Equiv.Perm (Fin 8330)))).relIndex Y →
        ∃ p : ℕ, p.Prime ∧ p ≠ 3 ∧
          ¬ p ∣ Nat.card (heAutGroup ⊓ centralizer ({σ} : Set (Equiv.Perm (Fin 8330))) :
            Subgroup (Equiv.Perm (Fin 8330))) ∧
          ∃ x ∈ heP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 8330))), x ≠ 1 ∧ x ^ p = 1 ∧
            ∀ N' : Subgroup (Equiv.Perm (Fin 8330)),
              N' ≤ heP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 8330))) →
              heP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 8330))) ≤
                normalizer (N' : Set (Equiv.Perm (Fin 8330))) →
              Odd (Nat.card N') → x ∉ N' := by
  intro Y hPY hYR σ hσ τ hτ hσ2 hτ2 hσc hτc
  have hidx : heP.relIndex heAutGroup ≤ 2 := heP_relIndex_heAutGroup.le
  have hYn : heP ≤ normalizer (Y : Set (Equiv.Perm (Fin 8330))) := by
    rcases eq_or_eq_of_card_le_two_mul hPY hYR (by rw [card_heAutGroup, card_heP]) with rfl | rfl
    · exact le_normalizer
    · exact heP_le_heAutGroup.trans le_normalizer
  obtain ⟨hev0, hevu⟩ := he_two_dvd_relIndex hPY hYR
  obtain ⟨c, hc, hσcls⟩ := he_involution_class (hYR hσ) hσ2
  have hσ1 : σ = c * heT1P * c⁻¹ := by
    rcases hσcls with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · exact absurd (by rw [h, relIndex_centralizer_conj (hYn hc)]; exact hev0) hσc
    · exact h
    · exact absurd (by rw [h, relIndex_centralizer_conj (hYn hc)]; exact hevu) hσc
  subst hσ1
  obtain ⟨d, hd, hτcls⟩ := he_involution_class (hYR hτ) hτ2
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨5, by norm_num, by norm_num, ?_, ?_⟩
  · rw [card_inf_centralizer_conj_of_mem_normalizer (heP_le_heAutGroup.trans le_normalizer hc)]
    obtain ⟨r, hr, hrc⟩ := card_inf_centralizer_eq_mul heP_le_heAutGroup hidx heT1P
    have h1 : Nat.card (heP ⊓ centralizer ({heT1P} : Set (Equiv.Perm (Fin 8330))) :
        Subgroup (Equiv.Perm (Fin 8330))) = 21504 := card_heP_cent1
    rw [hrc, h1]
    rcases hr with rfl | rfl <;> decide
  · have hx5 : ∀ {C : Subgroup (Equiv.Perm (Fin 8330))}, 5 ∣ Nat.card C →
        ∃ x ∈ C, x ≠ 1 ∧ x ^ 5 = 1 ∧ orderOf x = 5 := by
      intro C hC
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥C) 5 hC
      refine ⟨x, x.2, fun h => ?_, ?_, by rw [Subgroup.orderOf_coe, hx]⟩
      · have : x = 1 := Subtype.ext h
        rw [this, orderOf_one] at hx
        exact absurd hx (by norm_num)
      · have := pow_orderOf_eq_one x
        rw [hx] at this
        exact congrArg Subtype.val this
    rcases hτcls with ⟨hτP, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    ·
      subst h
      have hcard : Nat.card (heP ⊓ centralizer ({d * heGenPerm 0 * d⁻¹} : Set _) :
          Subgroup (Equiv.Perm (Fin 8330))) = 161280 := by
        rw [card_inf_centralizer_conj_of_mem_normalizer (le_normalizer hd)]
        exact card_heP_cent0
      obtain ⟨x, hx, hx1, hxp, -⟩ := hx5 (by rw [hcard]; norm_num)
      exact ⟨x, hx, hx1, hxp, fun N' h1 h2 h3 =>
        not_mem_of_oddCore_eq_bot (heP_centralizerIn_oddCore hτP hτ2) hx1 N' h1 h2 h3⟩
    ·
      subst h
      exfalso
      rw [relIndex_centralizer_conj (hYn hd)] at hτc
      rw [relIndex_centralizer_conj (hYn hc)] at hσc
      exact hσc hτc
    ·
      subst h
      have hcard : Nat.card (heP ⊓ centralizer ({d * heAutU * d⁻¹} : Set _) :
          Subgroup (Equiv.Perm (Fin 8330))) = 15120 := by
        rw [card_inf_centralizer_conj_of_mem_normalizer (le_normalizer hd)]
        exact card_heP_centralizer_heAutU
      obtain ⟨x, hx, hx1, hxp, hxo⟩ := hx5 (by rw [hcard]; norm_num)
      exact ⟨x, hx, hx1, hxp, fun N' h1 h2 h3 => he_outer_not_mem hd hxo N' h1 h2 h3⟩

theorem he_center :
    ∀ Y Q : Subgroup (Equiv.Perm (Fin 8330)), heP ≤ Y → Y ≤ heAutGroup →
      IsSylowOf 2 Q Y → Nat.card (centerIn Q) = 2 := by
  intro Y Q hPY hYR hQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h16 : Nat.card (centerIn HeSylow.X16) = 2 := by
    rw [HeSylow.sylModel16.center_X, Nat.card_zpowers, HeSylow.sylModel16.order_z]
  have h32 : Nat.card (centerIn HeSylow.Y32) = 2 := by
    rw [HeSylow.sylModel32.center_X, Nat.card_zpowers, HeSylow.sylModel32.order_z]
  rcases eq_or_eq_of_card_le_two_mul hPY hYR (by rw [card_heAutGroup, card_heP]) with rfl | rfl
  · obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
    let θ : Blueprint.NativeSporadic.Carrier .He ≃* ↥heP := heEquivP
    let f : ↥heP →* Blueprint.NativeSporadic.Carrier .He := θ.symm.toMonoidHom
    have hf : Function.Surjective f := θ.symm.surjective
    obtain ⟨e⟩ := HeSylow.nonempty_sylow_he_equiv (Sylow.mapSurjective hf S)
    rw [← h16]
    exact card_centerIn_eq_of_mulEquiv
      (((subgroupOfEquivOfLe hQ.le).symm.trans (MulEquiv.subgroupCongr hS.symm)).trans
        (((S : Subgroup ↥heP).equivMapOfInjective f θ.symm.injective).trans
          ((MulEquiv.subgroupCongr (Sylow.coe_mapSurjective hf S).symm).trans e)))
  · obtain ⟨S, hS⟩ := hQ.exists_sylow_eq_subgroupOf
    obtain ⟨e⟩ := HeSylow.nonempty_sylow_aut_equiv heP_normal_heAutGroup
      ⟨(subgroupOfEquivOfLe heP_le_heAutGroup).trans
        (heEquivP : Blueprint.NativeSporadic.Carrier .He ≃* ↥heP).symm⟩ heP_relIndex_heAutGroup
      RankTwoSporadic.He.heAutModel.centralizer_eq_bot S
    rw [← h32]
    exact card_centerIn_eq_of_mulEquiv
      (((subgroupOfEquivOfLe hQ.le).symm.trans (MulEquiv.subgroupCongr hS.symm)).trans e)

theorem he_fusionModel :
    FusionModel heP heAutGroup where
  le := heP_le_heAutGroup
  normal := heAutGroup_le_normalizer
  index := by rw [card_heAutGroup, card_heP]
  even := by
    rw [card_heP]
    decide
  center := he_center
  fusion := he_fusion

end CFSG.ComponentClassification.AS81
