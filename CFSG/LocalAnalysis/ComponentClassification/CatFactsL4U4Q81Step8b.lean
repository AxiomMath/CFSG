module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step8a
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Step7c
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBasic

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Setting46e

variable {S : Subgroup X} {w z : X} {V : Subgroup X} {i₀ j₀ : ℕ}

theorem barD_inf_KBar (hs : Setting46e t L 3 4 S w z V i₀ j₀) (i j : ℕ) :
    barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L) ⊓
        Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
        (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  have hKM := Standing.Setup42.K_le_centralizer_beta (L := L) (t := t) (w := w) (z := z) i j
  have hDM := hσ.D_le_centralizer_beta i j
  have hDp : IsPGroup 2 ↥(S ⊓ L) := (hs.standing.isSylowOf_inf hs.sylow).isPGroup
  have hSyl : IsSylowOf 2 (barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)))
      (Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) :=
    isSylowOf_map _ (Q81.isSylowOf_subgroupOf (hσ.isSylowOf_Dstar i j) hKM)
  have hbarDp : IsPGroup 2 ↥(barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (S ⊓ L)) := hDp.of_equiv (barEquiv hDM hDp)
  have hle : barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
      (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ≤
      barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L) ⊓
        Standing.Setup42.KBar L (w ^ (orderOf w / 2) * t ^ i * z ^ j) :=
    le_inf (map_mono fun x hx => (mem_inf.mp hx).1)
      (map_mono fun x hx => (mem_inf.mp hx).2)
  exact hSyl.eq_of_le hle inf_le_right (hbarDp.to_le inf_le_left)

theorem false_of_q81Data
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X) (hcat : ¬ Blueprint.Catalog X)
    (hCI : GSLit.ClassicalInvolutionInput) (h219 : Harris82Lemma219Input)
    (hP2 : Harris81Lemma33Simple) (hGO : TBLit.GriessMultipliersOdd)
    (hGC : TBLit.GriessMultipliersCentralCovers) (hT2 : Harris82Theorem2SLTwo)
    (hF : L4U4ThreeInvolutionFacts) (hFC : AutPSL2FieldCentralizerInput)
    (hKC : AutPSL2CentralizerInput) (hKG : AutPSL2SylowInput) (hKF : AutPSL2FusionInput)
    (hs : Setting46e t L 3 4 S w z V i₀ j₀)
    (hQ : ∀ i j : ℕ, IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
      (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
        Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1) →
      hs.setup.Q81Data i j)
    {i j : ℕ} (hD : hs.setup.Q81Data i j)
    (hβt : ∀ c : X, c * t * c⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hσ := hs.setup
  obtain ⟨W, R, -, hTW, -, hR, hWR, -, hRz, hZR, -⟩ :=
    hs.exists_R hnonab hQ hD hF hFC hKC hKG hβt
  obtain ⟨x, hxD, hxDs, hx2⟩ := hs.exists_x hFC hKC i j
  have hx1 : x ≠ 1 := fun h => hxDs (h ▸ one_mem _)
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [sq]; exact hx2) hx1
  obtain ⟨c, -, hc⟩ := hσ.exists_conj_eq_z hKF hxD (by rw [sq]; exact hx2) hx1
  have hDM := hσ.D_le_centralizer_beta i j
  have hxβ := hDM hxD
  have hDp : IsPGroup 2 ↥(S ⊓ L) := (hs.standing.isSylowOf_inf hs.sylow).isPGroup
  have hDsM : S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j) ≤
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j} := inf_le_left.trans hDM
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hLM : Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1 := by
    rcases hD.center_cases with ⟨h, -⟩ | ⟨h, -⟩
    · exact .inl h
    · exact .inr h
  have hZ2 : Nat.card ↥(center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) ∣ 2 := by
    rcases hD.center_cases with ⟨-, h | ⟨h, -⟩⟩ | ⟨-, h | ⟨h, -⟩⟩ <;> rw [h] <;> norm_num
  have hlay : Blueprint.LieModel ↥(GSThmB.layerIn
      (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓ centralizer {hσ.tBar i j}))
      .PSL 2 3 2 := by
    rw [hD.layerIn_eq]
    exact hD.lieModel
  have hDN : barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L) ≤
      normalizer ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : Subgroup _) : Set _) := by
    rw [normalizer_eq_top_iff.mpr hEn]
    exact le_top
  have hDC : barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L) ≤
      centralizer {hσ.tBar i j} := by
    intro a ha
    obtain ⟨d, hd, rfl⟩ := mem_barOf.mp ha
    rw [mem_centralizer_singleton_iff, Standing.Setup42.tBar, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp (hs.standing.config.le_centralizer hd.2))
  obtain ⟨e⟩ := hs.nonempty_D_equiv
  have hDe : Nonempty (↥(barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L)) ≃*
      DihedralGroup 8) := ⟨(barEquiv hDM hDp).symm.trans e⟩
  have hcard8 : Nat.card ↥(barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L) ⊓
      GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {hσ.tBar i j})) = 8 := by
    rw [hD.layerIn_eq, hs.barD_inf_KBar i j, card_barOf hDsM (hDp.to_le inf_le_left),
      hs.card_Dstar hFC hKC i j]
  have hxbD : (QuotientGroup.mk ⟨x, hxβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
      barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (S ⊓ L) :=
    mk_mem_barOf hxβ hxD
  have hxbK : (QuotientGroup.mk ⟨x, hxβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∉
      GSThmB.layerIn (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {hσ.tBar i j}) := by
    rw [hD.layerIn_eq]
    intro hxK
    have h1 : (QuotientGroup.mk ⟨x, hxβ⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈
        barOf (centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})
          (S ⊓ L ⊓ centralizerResidual L (w ^ (orderOf w / 2) * t ^ i * z ^ j)) := by
      rw [← hs.barD_inf_KBar i j]
      exact mem_inf.mpr ⟨hxbD, hxK⟩
    obtain ⟨y, hy, hyx⟩ := mem_barOf.mp h1
    have h2 : (y : X) = x := mk_injOn hDM hDp (mem_inf.mp hy).1 hxD hyx
    exact hxDs (h2 ▸ hy)
  obtain ⟨J, hJle, hJp, hJt⟩ := hF.pgl (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) _
    hD.quasisimple hLM hZ2 (hσ.tBar i j) _ (hσ.tBar_mem_normalizer_layer i j)
    (hσ.orderOf_tBar i j) hlay hDN hDC hDe hcard8 _ hxbD hxbK (Q81.orderOf_mk_of_two hxβ hxo)
  have hIC : ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
      centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ :
        MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}).subgroupOf
        (centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})).IsSubnormal := by
    have hn : ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ⊓
        centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ :
          MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}).subgroupOf
          (centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ :
            MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})).Normal :=
      ⟨fun n hn g => mem_inf.mpr ⟨hEn.conj_mem _ (mem_inf.mp hn).1 _,
        mul_mem (mul_mem g.2 (mem_inf.mp hn).2) (inv_mem g.2)⟩⟩
    exact hn.isSubnormal
  have hJp' : IsPComponent 2 (J.subgroupOf (centralizer {(QuotientGroup.mk ⟨x, hxβ⟩ :
      MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))})) :=
    (CatalogueBPrimeJoin.pComponent_subgroupOf_iff_of_subnormal hJle inf_le_right hIC).mpr hJp
  exact hs.false_of_conj_z hnonab hK hcat hCI h219 hP2 hGO hGC hT2 hR hRz hZR
    (hTW.trans hWR) (hσ.orderOf_beta i j) hxo hxβ hc (hJle.trans inf_le_right) hJp' hJt

end Setting46e

end CFSG.ComponentClassification.HarrisLit
