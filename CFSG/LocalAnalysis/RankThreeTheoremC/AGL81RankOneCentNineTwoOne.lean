module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineTwoOneEscape
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111OneSmallKappa
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineOneThreeProof
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineCompetitorSplit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.AGLEmbedding CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers

section Reduced

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {Rb : Sylow p Y} {Y₀ : Subgroup Y}

theorem layer_eq_bot_of_forall_component_le (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic)
    (h : ReducedNongeneration p Y Rb Y₀) (hX : CatalogSimpleSections Y)
    (hle : ∀ L : Subgroup Y, IsComponentOf L ⊤ → L ≤ Y₀) : CFSG.layer Y = ⊥ := by
  have hno : ∀ K : Subgroup Y, ¬ IsComponentOf K ⊤ := by
    intro K hK
    by_cases hcyc : ∀ L : Subgroup Y, IsComponentOf L ⊤ →
        IsCyclic ((Rb : Subgroup Y) ⊓ L : Subgroup Y)
    · obtain ⟨L, hL, hLX⟩ := h.exists_not_le_of_caseTwo_of_aut
        (h.cycAutRankLeTwo_of_kFactOutCyclic hX hOut) hcyc hK
      exact hLX (hle L hL)
    push Not at hcyc
    obtain ⟨L, hL, hLnc⟩ := hcyc
    have hLE : L ≤ CFSG.layer Y := by
      rw [CFSG.layer.eq_sSup]
      exact le_sSup ((CFSG.isComponent_iff_open L).mpr hL)
    have hnc : ¬ IsCyclic ((Rb : Subgroup Y) ⊓ CFSG.layer Y : Subgroup Y) := fun hc =>
      hLnc (Subgroup.isCyclic_of_le (inf_le_inf_left _ hLE))
    have hEX : CFSG.layer Y ≤ Y₀ := by
      rw [CFSG.layer.eq_sSup]
      exact sSup_le fun L' hL' => hle L' ((CFSG.isComponent_iff_open L').mp hL')
    have htop := h74 Y p h.prime h.ne_two hX h.core_eq_bot Rb h.three_le_pRank hnc
    exact h.ne_top (top_le_iff.mp (htop ▸ sup_le hEX h.weakCore_le))
  rw [CFSG.layer.eq_sSup, eq_bot_iff]
  exact sSup_le fun L hL => absurd ((CFSG.isComponent_iff_open L).mp hL) (hno L)

theorem isCyclic_center_of_layer_eq_bot (h : ReducedNongeneration p Y Rb Y₀)
    (hlayer : CFSG.layer Y = ⊥) : IsCyclic (Subgroup.center (Rb : Subgroup Y)) := by
  have hp := h.prime
  haveI : Fact p.Prime := ⟨hp⟩
  set Q := CFSG.pCore p Y with hQ
  have hQp : IsPGroup p Q := CFSG.pCore_isPGroup
  haveI : Q.Normal := CFSG.pCore_normal
  have hQR : Q ≤ (Rb : Subgroup Y) := hQp.le_sylow_of_normal Rb
  have hQc : Subgroup.centralizer (Q : Set Y) ≤ Q :=
    CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot Y p h.core_eq_bot hlayer
  haveI hZ : IsCyclic (Subgroup.center Q) :=
    h.isCyclic_of_characteristic_of_isMulCommutative (Subgroup.center Q)
      (IsMulCommutative.of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
  have hcomm : ∀ z : Subgroup.center (Rb : Subgroup Y), ∀ q ∈ Q,
      q * ((z : (Rb : Subgroup Y)) : Y) = ((z : (Rb : Subgroup Y)) : Y) * q := fun z q hq =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨q, hQR hq⟩)
  have hmemQ : ∀ z : Subgroup.center (Rb : Subgroup Y), ((z : (Rb : Subgroup Y)) : Y) ∈ Q :=
    fun z => hQc (Subgroup.mem_centralizer_iff.mpr (hcomm z))
  let f : Subgroup.center (Rb : Subgroup Y) →* Subgroup.center Q :=
    { toFun := fun z => ⟨⟨_, hmemQ z⟩, Subgroup.mem_center_iff.mpr fun q =>
        Subtype.ext (hcomm z q q.2)⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Injective f := fun x y hxy =>
    Subtype.ext (Subtype.ext (congrArg (fun w : Subgroup.center Q => ((w : Q) : Y)) hxy))
  exact isCyclic_of_surjective (MonoidHom.ofInjective hf).symm.toMonoidHom
    (MulEquiv.surjective _)

end Reduced

variable {G : Type} [Group G] [Finite G]

theorem isCyclic_center_of_d1KBar_eq_bot (h74 : AGL81SevenFourTwo) (hOut : KFactOutCyclic)
    (hKp : Open.IsKProper G) {p : ℕ} {P : Sylow p G} {M H₁ R₁ : Subgroup G}
    (he : D1Escape p P M H₁ R₁) {U N : Subgroup G} (hU : IsAGLQ p M U) (hUN : U ≤ N)
    (hNM : ¬ N ≤ M) (hNtop : N ≠ ⊤) (hK : d1KBar p M N = ⊥) {B : Subgroup G}
    (hB : CFSG.ABGLocalTools.IsSylowOf p B (N ⊓ M)) (hB3 : 3 ≤ Open.pRank p B) :
    IsCyclic ↥(Subgroup.center ↥B) := by
  have hp := he.prime
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨S, hS⟩ := hB
  have hBNM : B ≤ N ⊓ M := hS ▸ Subgroup.map_subtype_le _
  have hBM : B ≤ M := hBNM.trans inf_le_right
  have hBp : IsPGroup p B := hS ▸ S.isPGroup'.map _
  have hBQ : IsAGLQ p M B :=
    ⟨hBM, hBp, Or.inl (by rw [CFSG.SectionRank.pRank_coe_eq_openPRank]; exact hB3)⟩
  have hBin : CFSG.Quasithin.IsSylowIn p B (N ⊓ M) := by
    refine ⟨hBNM, hBp, ?_⟩
    have hBS : B.subgroupOf (N ⊓ M) = S := by
      rw [← hS, Subgroup.subgroupOf,
        Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
    rw [Subgroup.relIndex, hBS]
    exact S.not_dvd_index
  have hBN := isSylowIn_of_isSylowIn_inf hBin (normalizer_le_of_isAGLQ_escape he hBQ)
  set T : Sylow p N := hBN.toSylow with hT
  have hTB : (T : Subgroup N).map N.subtype = B := by
    rw [hT, CFSG.Quasithin.IsSylowIn.coe_toSylow]
    exact Subgroup.map_subgroupOf_eq_of_le hBN.le
  obtain ⟨m, hm, hBP⟩ := Hyp111.exists_conj_le he.sylow_le hBp hBM
  have hP' : ((m • P : Sylow p G) : Subgroup G) =
      (P : Subgroup G).map (MulAut.conj m).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl
  have hP'M : ((m • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [hP']
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (he.sylow_le hx)) (M.inv_mem hm)
  have hW' : GLBWeakCore p ((m • P : Sylow p G) : Subgroup G) ≤ M := by
    rw [hP']
    exact weakCore_conj_le hp he.weakCore_le hm
  have hcore : GLBPrimeCore p N ≤ M := by
    rw [← map_primeComplementCore_eq]
    exact core_le_of_base ⟨⟨H₁, R₁, he⟩⟩ hU hUN
  obtain ⟨Tb, hTb, hred⟩ := reducedNongeneration_of_not_le hp he.ne_two (m • P) hP'M hW' hNM T
    (by rw [hTB, hP']; exact hBP) (by rw [hTB]; exact hB3) hcore
  have hX : CatalogSimpleSections (N ⧸ primeComplementCore (G := N) p) :=
    (catalogSimpleSections_of_isKProper hKp N hNtop).quotient _
  have hle : ∀ L : Subgroup (N ⧸ primeComplementCore (G := N) p), IsComponentOf L ⊤ →
      L ≤ d1X0 p M N := fun L hL => by
    by_contra hLX
    have hLK : L ≤ d1KBar p M N := le_iSup₂_of_le L ⟨hL, hLX⟩ le_rfl
    rw [hK] at hLK
    exact hLX (hLK.trans bot_le)
  haveI hc := isCyclic_center_of_layer_eq_bot hred
    (layer_eq_bot_of_forall_component_le h74 hOut hred hX hle)
  set π := QuotientGroup.mk' (primeComplementCore (G := N) p) with hπ
  have hO : p.Coprime (Nat.card (primeComplementCore (G := N) p)) :=
    primeComplementCore_coprime p
  have hinj : Function.Injective (π.comp (T : Subgroup N).subtype) := by
    refine (injective_iff_map_eq_one _).mpr fun x hx => ?_
    have hxO : (x : N) ∈ primeComplementCore (G := N) p := by
      rw [← QuotientGroup.ker_mk' (primeComplementCore (G := N) p)]
      exact hx
    obtain ⟨k, hk⟩ := T.isPGroup' x
    have h1 : orderOf (x : N) ∣ p ^ k :=
      orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
    have h2 : orderOf (x : N) ∣ Nat.card (primeComplementCore (G := N) p) :=
      Subgroup.orderOf_coe (⟨(x : N), hxO⟩ : primeComplementCore (G := N) p) ▸
        orderOf_dvd_natCard _
    have h3 := Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left k hO)) h2
    exact Subtype.ext (orderOf_eq_one_iff.mp h3)
  have hrange : (π.comp (T : Subgroup N).subtype).range = (Tb : Subgroup _) := by
    rw [hTb, MonoidHom.range_comp, Subgroup.range_subtype]
  let e : ↥B ≃* ↥(Tb : Subgroup (N ⧸ primeComplementCore (G := N) p)) :=
    ((MulEquiv.subgroupCongr hTB).symm.trans
      (Subgroup.equivMapOfInjective (T : Subgroup N) N.subtype N.subtype_injective).symm).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange))
  exact isCyclic_of_surjective (Subgroup.centerCongr e.symm).toMonoidHom (MulEquiv.surjective _)

end CFSG.LocalAnalysis.RankThreeTheoremC
