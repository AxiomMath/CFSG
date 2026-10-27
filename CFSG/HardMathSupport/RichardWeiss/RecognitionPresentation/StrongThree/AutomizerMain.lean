module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.AutoX
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Transfer
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Core
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.StrongThreeAutomizer

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC

theorem exists_elemAbelian_le_sylow {N : Type*} [Group N] [Finite N] {N₀ R : Subgroup N}
    (hRN₀ : R ≤ N₀) (hR3 : IsPGroup 3 R) (hRidx : ¬ 3 ∣ R.relIndex N₀) :
    ∃ E : Subgroup N, E ≤ R ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ CFSG.Open.pRank 3 N₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E₀, hE₀N, hE₀, hcard⟩ := exists_isElemAbelian_card_pRank Nat.prime_three N₀
  have hE₀3 : IsPGroup 3 E₀ := fun x => ⟨1, Subtype.ext (by simpa using hE₀.2 x x.2)⟩
  have hR₁p : IsPGroup 3 (R.subgroupOf N₀) :=
    hR3.of_surjective (Subgroup.subgroupOfEquivOfLe hRN₀).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hRN₀).symm.surjective
  let R₁ : Sylow 3 ↥N₀ := hR₁p.toSylow hRidx
  have hE₁p : IsPGroup 3 (E₀.subgroupOf N₀) :=
    hE₀3.of_surjective (Subgroup.subgroupOfEquivOfLe hE₀N).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hE₀N).symm.surjective
  obtain ⟨Q, hQ⟩ := hE₁p.exists_le_sylow
  obtain ⟨u, hu⟩ := sylow_conj_mem Q R₁
  refine ⟨E₀.map (MulAut.conj (u : N)).toMonoidHom, ?_, isElemAbelian_map _ hE₀, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    have hxE : (⟨x, hE₀N hx⟩ : ↥N₀) ∈ E₀.subgroupOf N₀ := hx
    have := (hu _).mp (hQ hxE)
    have h2 : (u : N) * x * (u : N)⁻¹ ∈ R := by
      have h3 : (u * ⟨x, hE₀N hx⟩ * u⁻¹ : ↥N₀) ∈ R.subgroupOf N₀ := this
      simpa using Subgroup.mem_subgroupOf.mp h3
    simpa [MulAut.conj_apply] using h2
  · rw [← hcard]
    exact (Nat.card_congr (Subgroup.equivMapOfInjective E₀ (MulAut.conj (u : N)).toMonoidHom
      (MulAut.conj (u : N)).injective).toEquiv).symm

theorem kFactStrongThreeAutomizer_of_gls3Plus (hG : Gls3StronglyThreeEmbeddedPlus) :
    CFSG.AGLEmbeddingD2.McLaughlin.KFactStrongThreeAutomizer := by
  classical
  intro N _ _ hN N₀ hstr h2 R hRN₀ hR3 hRidx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hC3 := not_dvd_card_normalCore hstr
  have hstr' := stronglyEmbedded_coreImage hstr
  have h2' : 2 ≤ CFSG.Open.pRank 3 N₀ := h2.ge
  have hR3d : 3 ∣ Nat.card R := by
    have h1 := Subgroup.relIndex_mul_card R N₀
    rw [inf_of_le_left hRN₀] at h1
    have : 3 ∣ R.relIndex N₀ * Nat.card R := h1 ▸ hstr.2.1
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp this with h | h
    · exact absurd h hRidx
    · exact h
  obtain ⟨E, hEM, hE, hEcard⟩ := exists_elemAbelian_coreImage hstr h2'
  have D : CoreFree (coreImage N₀) E :=
    ⟨hstr', normalCore_coreImage, hEM, hE, hEcard⟩
  have hX := isKGroup_quotient hN N₀.normalCore
  obtain ⟨K, hKn, hKs, hKnc, hKc⟩ := D.exists_simple_normal
  have hK0 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance
  have hK3 := D.three_dvd_of_normal hK0
  obtain ⟨P', hRP', hP'N₀⟩ := exists_sylow_le_of_le hstr hRN₀ hR3
  have hP'R : (P' : Subgroup N) ≤ R := by
    have h1 := Subgroup.relIndex_mul_relIndex R P' N₀ hRP' hP'N₀
    have h3 : ¬ 3 ∣ R.relIndex P' := fun h => hRidx (h1 ▸ Dvd.dvd.mul_right h _)
    obtain ⟨n, hn⟩ := P'.isPGroup'.index (R.subgroupOf P')
    have hn' : R.relIndex P' = 3 ^ n := hn
    have : n = 0 := by
      by_contra hne
      exact h3 (hn' ▸ dvd_pow_self 3 hne)
    rw [this, pow_zero] at hn'
    exact Subgroup.relIndex_eq_one.mp hn'
  have hReq : (P' : Subgroup N) = R := le_antisymm hP'R hRP'
  set f : N →* N ⧸ N₀.normalCore := coreMk N₀ with hf
  set P : Sylow 3 (N ⧸ N₀.normalCore) := Sylow.mapSurjective (coreMk_surjective (N₀ := N₀)) P'
    with hPdef
  have hPe : (P : Subgroup (N ⧸ N₀.normalCore)) = R.map f := by
    rw [hPdef, Sylow.coe_mapSurjective, hReq]
  have hPM : (P : Subgroup (N ⧸ N₀.normalCore)) ≤ coreImage N₀ := hPe ▸ Subgroup.map_mono hRN₀
  have hrk : ∀ E' : Subgroup (N ⧸ N₀.normalCore), E' ≤ (P : Subgroup _) →
      IsElemAbelian 3 E' → Nat.card E' ≤ 9 := by
    intro E' hE'P hE'
    rw [hPe] at hE'P
    set F : Subgroup N := R ⊓ E'.comap f with hFdef
    have hF3 : IsPGroup 3 F := hR3.to_inf_left
    have hFmap : F.map f = E' := by
      ext e
      constructor
      · rintro ⟨x, ⟨-, hxE⟩, rfl⟩
        exact hxE
      · intro he
        obtain ⟨r, hr, rfl⟩ := hE'P he
        exact ⟨r, ⟨hr, he⟩, rfl⟩
    have hFel : IsElemAbelian 3 F := isElemAbelian_of_map hC3 hF3 (hFmap ▸ hE')
    have hcard : Nat.card E' = Nat.card F := by
      rw [← hFmap]; exact card_map_core hC3 hF3
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hF3
    have hkle : k ≤ CFSG.Open.pRank 3 N₀ :=
      le_pRank Nat.prime_three (inf_le_left.trans hRN₀) hFel hk
    rw [hcard, hk]
    calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  have hrank : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup (N ⧸ N₀.normalCore)) := by
    obtain ⟨E₂, hE₂R, hE₂el, hE₂c⟩ := exists_elemAbelian_le_sylow hRN₀ hR3 hRidx
    rw [h2] at hE₂c
    have hE₂3 : IsPGroup 3 E₂ := hR3.to_le hE₂R
    refine le_pRank Nat.prime_three (E := E₂.map f) ?_ (isElemAbelian_map f hE₂el) (k := 2) ?_
    · rw [hPe]; exact Subgroup.map_mono hE₂R
    · rw [card_map_core hC3 hE₂3, hE₂c]
  have hΓX : gammaCore 3 1 ⊤ (P : Subgroup (N ⧸ N₀.normalCore)) < ⊤ :=
    lt_of_le_of_lt ((gammaCore_le_inf hstr' hPM _ _ le_rfl).trans inf_le_left)
      (lt_top_iff_ne_top.mpr hstr'.1)
  have hconc := hG _ hX K hKn hKs hKnc hKc P hrank hΓX
  obtain ⟨hA1, hA2⟩ := autoGoal_of_plus hKs hKnc hstr' P hPM hK3 hrk hconc
  rw [hPe] at hA1 hA2
  have hinj : ∀ {E : Subgroup N}, IsPGroup 3 E → ∀ x ∈ E, ∀ y ∈ E, f x = f y → x = y :=
    fun hE x hx y hy h => injOn_core_of_pgroup hC3 hE hx hy h
  have hlift := fun {g : N ⧸ N₀.normalCore}
      (hg : g ∈ Subgroup.normalizer ((R.map f : Subgroup _) : Set _)) =>
    exists_lift_normalizer hstr hRN₀ hR3 hR3d hg
  refine ⟨fun hab => ?_, fun hodd => ?_⟩
  · obtain ⟨hEl, h9, hirr⟩ := hA1 (comm_map hab)
    refine ⟨isElemAbelian_of_map hC3 hR3 hEl, ?_, ?_⟩
    · rw [← card_map_core hC3 hR3]; exact h9
    · intro W hWR hW
      have hW3 : IsPGroup 3 W := hR3.to_le hWR
      have hnorm : Subgroup.normalizer
          ((Subgroup.map f R : Subgroup (N ⧸ N₀.normalCore)) : Set (N ⧸ N₀.normalCore)) ≤
          Subgroup.normalizer
            ((Subgroup.map f W : Subgroup (N ⧸ N₀.normalCore)) : Set (N ⧸ N₀.normalCore)) := by
        intro g hg
        obtain ⟨n, ⟨hnN₀, hnR⟩, rfl⟩ := hlift hg
        have hnW := hW ⟨hnN₀, hnR⟩
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact ⟨n * w * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnW w).mp hw, by simp [map_mul, hf]⟩
        · intro hy
          have hyR : y ∈ R.map f :=
            (Subgroup.mem_normalizer_iff.mp hg y).mpr (Subgroup.map_mono hWR hy)
          obtain ⟨r, hr, rfl⟩ := hyR
          obtain ⟨w', hw', hw'e⟩ := hy
          have hnr : n * r * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hnR r).mp hr
          have : w' = n * r * n⁻¹ :=
            hinj hR3 w' (hWR hw') _ hnr (by rw [hw'e, map_mul, map_mul, map_inv])
          have hrW : r ∈ W := (Subgroup.mem_normalizer_iff.mp hnW r).mpr (this ▸ hw')
          exact ⟨r, hrW, rfl⟩
      rcases hirr (W.map f) (Subgroup.map_mono hWR) hnorm with h | h
      · left
        refine eq_bot_iff.mpr fun x hx => ?_
        have : f x ∈ W.map f := ⟨x, hx, rfl⟩
        rw [h, Subgroup.mem_bot] at this
        exact Subgroup.mem_bot.mpr (inj_core_of_pgroup hC3 hW3 hx this)
      · right
        refine le_antisymm hWR fun x hx => ?_
        have : f x ∈ W.map f := h ▸ ⟨x, hx, rfl⟩
        obtain ⟨w, hw, hwx⟩ := this
        have := hinj hR3 w (hWR hw) x hx hwx
        exact this ▸ hw
  · have hodd' : ¬ 2 ∣ (coreImage N₀).index := by
      have hker : (coreMk N₀).ker ≤ N₀ := by
        rw [coreMk, QuotientGroup.ker_mk']; exact N₀.normalCore_le
      unfold coreImage
      rwa [Subgroup.index_map_eq N₀ coreMk_surjective hker]
    obtain ⟨hEl, h9, htr⟩ := hA2 hodd'
    refine ⟨isElemAbelian_of_map hC3 hR3 hEl, ?_, ?_⟩
    · rw [← card_map_core hC3 hR3]; exact h9
    · intro x hx y hy hx1 hy1
      have hfx : f x ≠ 1 := fun h => hx1 (inj_core_of_pgroup hC3 hR3 hx h)
      have hfy : f y ≠ 1 := fun h => hy1 (inj_core_of_pgroup hC3 hR3 hy h)
      obtain ⟨g, hg, hgxy⟩ := htr (f x) ⟨x, hx, rfl⟩ (f y) ⟨y, hy, rfl⟩ hfx hfy
      obtain ⟨n, hn, rfl⟩ := hlift hg
      refine ⟨n, hn, ?_⟩
      have hnr : n * x * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hn.2 x).mp hx
      exact hinj hR3 _ hnr y hy (by rw [map_mul, map_mul, map_inv]; exact hgxy)

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
