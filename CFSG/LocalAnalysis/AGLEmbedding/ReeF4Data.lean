module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorCenter
public import CFSG.LocalAnalysis.AGLEmbedding.G28InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4DataAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section ReeF4DataProof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_conj_subgroupOf {p : ℕ} {H F : Subgroup G} (hFH : F ≤ H) (t : H) :
    ((F.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))).map
        (MulAut.conj (QuotientGroup.mk' (primeComplementCore (G := H) p) t)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨f, hf, hfy⟩ := Subgroup.mem_subgroupOf.mp hy
    have hfH : f ∈ H := hFH hf
    have hy' : y = t * ⟨f, hfH⟩ * t⁻¹ := Subtype.ext (by simpa using hfy.symm)
    refine ⟨QuotientGroup.mk' _ ⟨f, hfH⟩, ⟨⟨f, hfH⟩, Subgroup.mem_subgroupOf.mpr hf, rfl⟩, ?_⟩
    rw [hy']
    simp [MulAut.conj_apply]
  · rintro ⟨_, ⟨⟨f, hfH⟩, hf, rfl⟩, rfl⟩
    refine ⟨t * ⟨f, hfH⟩ * t⁻¹, Subgroup.mem_subgroupOf.mpr ⟨f, Subgroup.mem_subgroupOf.mp hf,
      by simp⟩, ?_⟩
    simp [MulAut.conj_apply]

theorem stmtReeF4Data_of (hK : KFactReeF4Local) : StmtReeF4Data := by
  intro G _ _ _ d hd T _ _ eT P M H R U h
  obtain ⟨K, hKn, ⟨eK⟩, hC, hUK⟩ := h.socle
  obtain ⟨eT⟩ := eT
  obtain ⟨Rbar, hRbar, hred⟩ := h.ext.reducedNongeneration
  obtain ⟨hS, hZK⟩ := hK _ K d hd hKn ⟨eK.trans eT⟩ hC Rbar _ hred.three_le_pRank
    hred.weakCore_le hred.ne_top
  rw [hRbar] at hS hZK
  have h5 : Nat.Prime 5 := Fact.out
  set π := QuotientGroup.mk' (primeComplementCore (G := H) 5) with hπ
  have hRH : R ≤ H := h.ext.le_H
  have hR5 : IsPGroup 5 R := h.ext.isPGroup
  have hXb : ((centerOf R).subgroupOf H).map π = centerOf ((R.subgroupOf H).map π) :=
    map_inf_centralizer_eq hRH hR5
  have hZH : centerOf R ≤ H := inf_le_left.trans hRH
  have hZp : IsPGroup 5 (centerOf R) := hR5.to_le inf_le_left
  have hcardX : Nat.card (centerOf R) = 5 ^ 2 := by
    have h1 := card_map_mk_of_isPGroup h5 _ (primeComplementCore_coprime 5)
      (hZp.comap_subtype (K := H))
    rw [← hS.center_card, ← hXb]
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZH).toEquiv]
    exact h1.symm
  have hcenter_ne : centerOf ((R.subgroupOf H).map π) ≠ ⊥ := by
    intro hbot
    have := hS.center_card
    rw [hbot, Subgroup.card_bot] at this
    norm_num at this
  have hCS : CenterInSitu 5 ((R.subgroupOf H).map π) (((H ⊓ M).subgroupOf H).map π) :=
    ⟨hS.primeCore, hS.normal_dichotomy, hS.centralizer_le, hcenter_ne⟩
  have hsurv := h.ext.survivorData_center h.glob hCS
  have hZU : centerOf R ≤ U := by
    refine le_of_map_le_of_isPGroup hRH hR5 inf_le_left h.le_R ?_
    rw [hUK, hXb]
    exact le_inf inf_le_left hZK
  have helem : IsElemAbelian 5 (centerOf R) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · show (a : G) * b = b * a
      exact Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1
    · have hxH : x ∈ H := hZH hx
      have hxT : π ⟨x, hxH⟩ ∈ centerOf ((R.subgroupOf H).map π) := by
        rw [← hXb]
        exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
      have h1 : π (⟨x, hxH⟩ ^ 5) = π 1 := by rw [map_pow, hS.center_elem.2 _ hxT, map_one]
      have h2 := eq_of_map_eq_of_isPGroup hR5 (by simpa using R.pow_mem hx.1 5) R.one_mem h1
      simpa using congrArg Subtype.val h2
  have hsolv : Group.IsSolvable (((H ⊓ M).subgroupOf H).map π) := hS.solvable
  have hnorm : H ⊓ M ⊓ Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (centerOf R : Set G) := by
    intro g hg
    have hgR := hg.2
    have hgC : g ∈ Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro c
      simp only [Subgroup.mem_centralizer_iff]
      constructor
      · intro hc r hr
        have hr' : g⁻¹ * r * g ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgR) r).mp hr
          simpa using this
        have := hc _ hr'
        calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
          _ = g * c * g⁻¹ * r := by group
      · intro hc r hr
        have hr' : g * r * g⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hgR r).mp hr
        have := hc _ hr'
        have e : r * c = g⁻¹ * ((g * r * g⁻¹) * (g * c * g⁻¹)) * g := by group
        rw [e, this]
        group
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hgR, hgC⟩
  have hcardmap : ∀ F : Subgroup G, F ≤ centerOf R →
      Nat.card ((F.subgroupOf H).map π) = Nat.card F := fun F hF => by
    have h1 := card_map_mk_of_isPGroup h5 _ (primeComplementCore_coprime 5)
      ((hZp.to_le hF).comap_subtype (K := H))
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hF.trans hZH)).toEquiv]
    exact h1
  have hmapZ : ∀ F : Subgroup G, F ≤ centerOf R →
      (F.subgroupOf H).map π ≤ centerOf ((R.subgroupOf H).map π) := fun F hF => by
    rw [← hXb]
    exact Subgroup.map_mono (Subgroup.comap_mono hF)
  have htrans : ∀ F F' : Subgroup G, F ≤ centerOf R → F' ≤ centerOf R → Nat.card F = 5 →
      Nat.card F' = 5 → ∃ g ∈ H ⊓ M ⊓ Subgroup.normalizer (R : Set G),
        F.map (MulAut.conj g).toMonoidHom = F' := by
    intro F F' hF hF' hFc hF'c
    obtain ⟨gb, hgb, hgbF⟩ := hS.transitive _ _ (hmapZ F hF) (hmapZ F' hF')
      (by rw [hcardmap F hF, hFc]) (by rw [hcardmap F' hF', hF'c])
    obtain ⟨t, htK, htg⟩ := exists_mem_normalizer_lift h.ext hgb (hS.le_normalizer hgb)
    refine ⟨t, htK, ?_⟩
    have hFt : F.map (MulAut.conj (t : G)).toMonoidHom ≤ centerOf R := by
      rintro _ ⟨f, hf, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hnorm htK) f).mp (hF hf)
    have hFtmap : ((F.map (MulAut.conj (t : G)).toMonoidHom).subgroupOf H).map π =
        (F'.subgroupOf H).map π := by
      rw [map_conj_subgroupOf (hF.trans hZH) t, htg, hgbF]
    exact le_antisymm
      (le_of_map_le_of_isPGroup hRH hR5 (hFt.trans inf_le_left) (hF'.trans inf_le_left)
        hFtmap.le)
      (le_of_map_le_of_isPGroup hRH hR5 (hF'.trans inf_le_left) (hFt.trans inf_le_left)
        hFtmap.ge)
  set B := H ⊓ M ⊓ Subgroup.normalizer (R : Set G) with hB
  have hBH : B ≤ H := inf_le_left.trans inf_le_left
  have hBmap : (B.subgroupOf H).map π = ((H ⊓ M).subgroupOf H).map π := by
    apply le_antisymm
    · exact Subgroup.map_mono (Subgroup.comap_mono inf_le_left)
    · intro gb hgb
      obtain ⟨t, htK, htg⟩ := exists_mem_normalizer_lift h.ext hgb (hS.le_normalizer hgb)
      exact ⟨t, Subgroup.mem_subgroupOf.mpr htK, htg⟩
  have hirr : ∀ Y₁ : Subgroup G, Y₁ ≤ B → Y₁.relIndex B ≤ 3 → ∀ F : Subgroup G,
      F ≤ centerOf R → Y₁ ≤ Subgroup.normalizer (F : Set G) → F = ⊥ ∨ F = centerOf R := by
    intro Y₁ hY₁ hidx F hF hY₁F
    have hY₁H : Y₁ ≤ H := hY₁.trans hBH
    have hidx' : ((Y₁.subgroupOf H).map π).relIndex (((H ⊓ M).subgroupOf H).map π) ≤ 3 := by
      rw [← hBmap]
      have hd := relIndex_map_dvd π (Subgroup.comap_mono hY₁ : Y₁.subgroupOf H ≤ B.subgroupOf H)
      have hrel : (Y₁.subgroupOf H).relIndex (B.subgroupOf H) = Y₁.relIndex B :=
        Subgroup.relIndex_subgroupOf hBH
      change ((Y₁.subgroupOf H).map π).relIndex ((B.subgroupOf H).map π) ∣
        (Y₁.subgroupOf H).relIndex (B.subgroupOf H) at hd
      rw [hrel] at hd
      have hpos : 0 < Y₁.relIndex B := by
        rw [Subgroup.relIndex]
        exact Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      exact (Nat.le_of_dvd hpos hd).trans hidx
    have hY₁Y₀ : (Y₁.subgroupOf H).map π ≤ ((H ⊓ M).subgroupOf H).map π :=
      Subgroup.map_mono (Subgroup.comap_mono (hY₁.trans inf_le_left))
    have hnormF : (Y₁.subgroupOf H).map π ≤
        Subgroup.normalizer (((F.subgroupOf H).map π : Subgroup _) : Set _) := by
      rintro _ ⟨y, hy, rfl⟩
      have hyF := hY₁F (Subgroup.mem_subgroupOf.mp hy)
      have heq : F.map (MulAut.conj (y : G)).toMonoidHom = F :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hyF
      have := map_conj_subgroupOf (p := 5) (hF.trans hZH) y
      rw [heq] at this
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr this.symm
    rcases hS.irred _ hY₁Y₀ hidx' _ (hmapZ F hF) hnormF with h1 | h1
    · left
      have hFp := hZp.to_le hF
      rw [eq_bot_iff]
      intro f hf
      have hfH := hF.trans hZH hf
      have hmem : π ⟨f, hfH⟩ ∈ (F.subgroupOf H).map π :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hf)
      rw [h1, Subgroup.mem_bot] at hmem
      have := eq_of_map_eq_of_isPGroup hR5 (a := ⟨f, hfH⟩) (b := 1) (hF hf).1 R.one_mem
        (by rw [hmem, map_one])
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · right
      refine le_antisymm hF (le_of_map_le_of_isPGroup hRH hR5 inf_le_left (hF.trans
        inf_le_left) ?_)
      rw [h1, hXb]
  exact ⟨⟨hsurv, helem, hcardX, fun L hL hLL => le_glbPrimeCore_of_perfect hsolv hL hLL, hnorm,
    htrans, hirr⟩, hZU⟩

end ReeF4DataProof

end CFSG.AGLEmbedding
