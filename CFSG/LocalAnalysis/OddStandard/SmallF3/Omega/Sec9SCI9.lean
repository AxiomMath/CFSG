module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SCI8
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SGU7
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem asc82Sec9CosIrred_of (hT6 : Asc82Tab6M) : Asc82Sec9CosIrred := by
  intro G _ _ L hL P hP B hBP hB s hs2 hsN hsB hα B' hB'B hinv
  obtain ⟨α, hα⟩ := hα
  obtain ⟨V, _, _, _, Q, hQ, e, hm, F, hF16, hlift4, hFB, hBF⟩ :=
    sec9g_model_E16 hT6 G L hL P hP B hBP hB
  have hBL : B ≤ L := hBP.trans hP.1
  have hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f := by
    intro f hf h1
    obtain ⟨t, htt, htf, -, -⟩ := hlift4 f hf h1
    exact ⟨t, htt, htf⟩
  obtain ⟨b, hb⟩ := sec9t_exists_evenFrame hQ hm.1 F hF16 hlift4
  have hn : 3 ≤ Module.finrank (ZMod 3) V := by rw [hm.1]; norm_num
  have hΩ : ∀ g ∈ F.comap (phiSim Q), SimInOmegaStar hQ (phiSim Q g) := by
    intro g hg
    obtain ⟨b', hb', hb'g⟩ := hBF (phiSim Q g) hg
    refine ⟨((e (QuotientGroup.mk (⟨b', hBL hb'⟩ : ↥L)) : omegaProj hQ) : ProjOrth Q),
      (e (QuotientGroup.mk (⟨b', hBL hb'⟩ : ↥L))).2, ?_⟩
    rw [← hb'g]
    exact (ffInducesHom_of_mem hm e ⟨b', hBL hb'⟩ (Subgroup.le_normalizer (hBL hb'))).symm
  have hc : ∀ i j : Fin (Module.finrank (ZMod 3) V), Q (b i) = Q (b j) :=
    fun i j => sec9ci_norm_const hQ hm hb hΩ i j
  have h1 : SimHasDim (ffInducesHom hm e ⟨s, hsN⟩) 1 := simHasDim_of_inducesTypeSome hm e hsN hα
  have hx : ∀ g ∈ F.comap (phiSim Q), ffInducesHom hm e ⟨s, hsN⟩ * phiSim Q g =
      phiSim Q g * ffInducesHom hm e ⟨s, hsN⟩ := by
    intro g hg
    obtain ⟨b', hb', hb'g⟩ := hBF (phiSim Q g) hg
    rw [← hb'g, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hsB b' hb')
  obtain ⟨j, r, hr, hrb⟩ := sec9ci_refl_of_i1 hQ hm.1 hb hx h1
  have hne : layerCent L s ≠ ⊥ := sec9ci_layer_ne_bot hT6 hL hm e hs2 hsN h1
  have hF'F : (B'.subgroupOf B).map (sec9ciPsiB hm e hBL) ≤ F := by
    intro f hf
    obtain ⟨c, -, rfl⟩ := Subgroup.mem_map.mp hf
    exact hFB (c : G) c.2
  have hinv' : ∀ u v w z : Fin (Module.finrank (ZMod 3) V), u ≠ v → u ≠ w → u ≠ z → v ≠ w →
      v ≠ z → w ≠ z → u ≠ j → v ≠ j → w ≠ j → z ≠ j →
      ∃ g : OGroup Q, (∀ i, (g : V ≃ₗ[ZMod 3] V) (b i) =
        b ((Equiv.swap u v * Equiv.swap w z) i)) ∧
        ∀ f ∈ (B'.subgroupOf B).map (sec9ciPsiB hm e hBL),
          phiSim Q g * f * (phiSim Q g)⁻¹ ∈ (B'.subgroupOf B).map (sec9ciPsiB hm e hBL) := by
    intro u v w z huv huw huz hvw hvz hwz huj hvj hwj hzj
    obtain ⟨g, x, hg, hxL, hxN, hxx, hxact⟩ := sec9ci_exists_inv hT6 hL hm e hBL hB hs2 hsN hne
      F hFB hBF hlift hb hn hc hr hrb huv huw huz hvw hvz hwz huj hvj hwj hzj
    refine ⟨g, hg, ?_⟩
    intro f hf
    obtain ⟨c, hc', rfl⟩ := Subgroup.mem_map.mp hf
    have hcB' : (c : G) ∈ B' := hc'
    have hxc : x * (c : G) * x⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hxN c).mp c.2
    have hxcB' : x * (c : G) * x⁻¹ ∈ B' :=
      hinv x ⟨hxL, hxN⟩ ⟨1, by simpa [pow_two] using hxx⟩ c hcB'
    exact Subgroup.mem_map.mpr ⟨⟨x * (c : G) * x⁻¹, hxc⟩, hxcB',
      hxact c ⟨x * (c : G) * x⁻¹, hxc⟩ rfl⟩
  have hinj := sec9ciPsiB_injective hL hm e hBL hB
  rcases sec9ci_irred_F hm.1 hb hlift j _ hF'F hinv' with h | h
  · left
    rw [Subgroup.eq_bot_iff_forall]
    intro c hc'
    have hcB : c ∈ B := hB'B hc'
    have hmem : sec9ciPsiB hm e hBL ⟨c, hcB⟩ ∈ (B'.subgroupOf B).map (sec9ciPsiB hm e hBL) :=
      Subgroup.mem_map.mpr ⟨⟨c, hcB⟩, hc', rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    have := hinj (hmem.trans (map_one (sec9ciPsiB hm e hBL)).symm)
    exact congrArg Subtype.val this
  · right
    refine le_antisymm hB'B (fun c hc' => ?_)
    have hmem : sec9ciPsiB hm e hBL ⟨c, hc'⟩ ∈ F := hFB c hc'
    rw [← h] at hmem
    obtain ⟨c', hc'', hc'eq⟩ := Subgroup.mem_map.mp hmem
    have := hinj hc'eq
    rw [this] at hc''
    exact hc''

theorem aschOmega6Minus_of_tab6_full (hsh : Asc82Shapes) (h36 : Asc82Lemma36)
    (h37 : Asc82Lemma37) (h66 : Asc82Lemma66) (h68 : Asc82Lemma68) (h82 : Asc82Lemma82)
    (hZ : Asc82ZExists) (hM : Asc82Tab6M) (hN : Asc82NormA6) (h84 : Asc82Thm84) :
    AschOmega6Minus :=
  aschOmega6Minus_of_tab6_t0 hsh h36 h37 h66 h68 h82 hZ hM hN (asc82Sec9CosIrred_of hM) h84

end CFSG.OddStandard.SmallF3.Omega
