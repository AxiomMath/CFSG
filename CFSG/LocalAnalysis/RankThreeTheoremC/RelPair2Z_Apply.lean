module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux1
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_ApplyAux2
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2Z_PComp
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Plumb
import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Transfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup Equiv
  CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

theorem zj_apply {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Type} [Group Y] [Finite Y]
    (hK1 : KFactZJFactorization) (hsec : CFSG.AGLEmbedding.CatalogSimpleSections Y)
    (hcharTwo : centralizer (CFSG.pCore 2 Y : Set Y) ≤ CFSG.pCore 2 Y)
    (hrkp : ∀ E : Subgroup Y, IsElemAbelian p E → Nat.card E ≤ p ^ 2)
    (hrk3 : ∀ E : Subgroup Y, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3)
    (hsylow : CFSG.ABGLocalTools.IsSylowOf 2 (CFSG.pCore 2 Y) (CFSG.pPrimeCore p Y))
    {J V : Subgroup Y} (hJn : J.Normal) (hJc : CFSG.IsPComponent p J)
    {L : Subgroup (Y ⧸ CFSG.pPrimeCore p Y)} (hLs : IsSimpleGroup L)
    (hLnab : ∃ a b : L, a * b ≠ b * a)
    (hLn : L.Normal) (hLc : centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) = ⊥)
    (hJL : J.map (QuotientGroup.mk' (CFSG.pPrimeCore p Y)) = L)
    (hJp : pElementSubgroup p J = J) (hV : IsPGroup 2 V) (hcore : CFSG.pCore 2 Y ≤ V)
    (hJ0 : ¬ 3 ∣ Nat.card (⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ : Subgroup Y))
    (hnc : ∀ Z : Subgroup Y, Z ≤ V → Z ≠ ⊥ → (Z.subgroupOf V).Characteristic →
      ¬ J ≤ normalizer (Z : Set Y) ⊔ CFSG.pPrimeCore p Y) :
    IsChevTwo L ∨ ∃ n : ℕ, Nonempty (L ≃* alternatingGroup (Fin n)) := by
  have _ := hJc
  have : Fact p.Prime := ⟨hp⟩
  have : J.Normal := hJn
  have : IsSimpleGroup L := hLs
  obtain ⟨W, hW⟩ : ∃ W : Subgroup Y, J ⊔ V = W := ⟨_, rfl⟩
  have hJW : J ≤ W := hW ▸ le_sup_left
  have hVW : V ≤ W := hW ▸ le_sup_right
  have hRW : CFSG.pCore 2 Y ≤ W := hcore.trans hVW
  have hpL : p ∣ Nat.card L := zja_dvd_card hp hLnab hJL hJp
  have hpc : CFSG.pCore 2 W = (CFSG.pCore 2 Y).subgroupOf W :=
    zja_pCore_eq hp hp2 hsylow hLs hLn hLc hpL hJL hJW
  have hPle : (CFSG.pPrimeCore p W).map W.subtype ≤ CFSG.pPrimeCore p Y :=
    zja_map_subtype_le hp hLs hLn hLc hpL hJL hJW (N := CFSG.pPrimeCore p W)
      CFSG.pPrimeCore_coprime_card
  have hcharW : centralizer (CFSG.pCore 2 W : Set W) ≤ CFSG.pCore 2 W := by
    rw [hpc]
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hcharTwo
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.mp hx) ⟨r, hRW hr⟩ hr)
  have h2cl : ∀ T₂ : Sylow 2 (CFSG.pPrimeCore p W),
      (T₂ : Subgroup (CFSG.pPrimeCore p W)).Normal :=
    fun T₂ => zja_sylow_normal hsylow hPle T₂
  have hKn : (J.subgroupOf W).Normal := inferInstance
  have hKp : pElementSubgroup p (J.subgroupOf W) = J.subgroupOf W :=
    zja_pElementSubgroup_subgroupOf hJW hJp
  obtain ⟨e₂⟩ := zja_exists_equiv_image hp hLs hLn hLc hpL hJL hJW
  have hcomp : CFSG.IsComponent
      ((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) := by
    refine ⟨?_, ?_⟩
    · have : IsSimpleGroup
          ↥((J.subgroupOf W).map (QuotientGroup.mk' (CFSG.pPrimeCore p W))) :=
        e₂.isSimpleGroup
      refine zja_isQuasisimple_of_simple ?_
      obtain ⟨a, b, hab⟩ := hLnab
      exact ⟨e₂.symm a, e₂.symm b, fun h => hab (by simpa using congrArg e₂ h)⟩
    · exact Subgroup.Normal.isSubnormal
        (Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _))
  have hPC : CFSG.IsPComponent p (J.subgroupOf W) :=
    isPComponent_of_normal hp hKn hKp hcomp rfl
  have hS2 : IsPGroup 2 (V.subgroupOf W) := hV.comap_subtype
  have hKS : J.subgroupOf W ⊔ V.subgroupOf W = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hJW,
      Subgroup.map_subgroupOf_eq_of_le hVW, hW, Subgroup.map_top, Subgroup.range_subtype]
  have hT : ∃ T : Sylow 2 W, J.subgroupOf W ⊔ (T : Subgroup W) = ⊤ := by
    obtain ⟨T, hT⟩ := hS2.exists_le_sylow
    exact ⟨T, eq_top_iff.mpr (hKS.ge.trans (sup_le_sup_left hT _))⟩
  have h3 : ¬ 3 ∣ Nat.card (⁅J.subgroupOf W,
      (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map (J.subgroupOf W).subtype⁆ : Subgroup W) := by
    let ι : ↥(J.subgroupOf W) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJW
    have hcore' : (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map ι.toMonoidHom =
        CFSG.pPrimeCore p ↥J := CFSG.pPrimeCore_map_iso p ι
    have hhom : W.subtype.comp (J.subgroupOf W).subtype = J.subtype.comp ι.toMonoidHom := by
      ext x
      rfl
    have himg : ((CFSG.pPrimeCore p ↥(J.subgroupOf W)).map (J.subgroupOf W).subtype).map
        W.subtype = (CFSG.pPrimeCore p ↥J).map J.subtype := by
      rw [Subgroup.map_map, hhom, ← Subgroup.map_map, hcore']
    have hcomm : (⁅J.subgroupOf W, (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map
        (J.subgroupOf W).subtype⁆ : Subgroup W).map W.subtype =
        ⁅J, (CFSG.pPrimeCore p ↥J).map J.subtype⁆ := by
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hJW, himg]
    have hcard := Subgroup.card_map_of_injective
      (K := (⁅J.subgroupOf W, (CFSG.pPrimeCore p ↥(J.subgroupOf W)).map
        (J.subgroupOf W).subtype⁆ : Subgroup W)) W.subtype_injective
    rw [hcomm] at hcard
    rw [← hcard]
    exact hJ0
  have hnc' : ∀ Z' : Subgroup W, Z' ≤ V.subgroupOf W → Z' ≠ ⊥ →
      (Z'.subgroupOf (V.subgroupOf W)).Characteristic →
      ¬ J.subgroupOf W ≤ normalizer (Z' : Set W) ⊔ CFSG.pPrimeCore p W := by
    intro Z' hZ'S hZ'1 hZ'c hcover
    have hZV : Z'.map W.subtype ≤ V := by
      rintro _ ⟨z, hz, rfl⟩
      exact hZ'S hz
    have hZ1 : Z'.map W.subtype ≠ ⊥ := fun h =>
      hZ'1 ((Subgroup.map_eq_bot_iff_of_injective Z' W.subtype_injective).mp h)
    have hZc : ((Z'.map W.subtype).subgroupOf V).Characteristic := by
      let e : ↥(V.subgroupOf W) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVW
      have hchar := zja_characteristic_map e hZ'c
      have heq : (Z'.subgroupOf (V.subgroupOf W)).map e.toMonoidHom =
          (Z'.map W.subtype).subgroupOf V := by
        ext x
        constructor
        · rintro ⟨s, hs, rfl⟩
          exact ⟨s, hs, rfl⟩
        · intro hx
          obtain ⟨z, hz, hzx⟩ := hx
          exact ⟨⟨z, hZ'S hz⟩, hz, Subtype.ext hzx⟩
      rw [← heq]
      exact hchar
    refine hnc _ hZV hZ1 hZc ?_
    have h1 : (J.subgroupOf W).map W.subtype ≤
        (normalizer (Z' : Set W) ⊔ CFSG.pPrimeCore p W).map W.subtype :=
      Subgroup.map_mono hcover
    rw [Subgroup.map_subgroupOf_eq_of_le hJW, Subgroup.map_sup] at h1
    refine h1.trans (sup_le_sup ?_ hPle)
    rintro _ ⟨g, hg, rfl⟩
    exact thg_mem_normalizer_map hg
  have hcoreS : CFSG.pCore 2 W ≤ V.subgroupOf W := by
    rw [hpc]
    exact Subgroup.comap_mono hcore
  have hrkpW : ∀ E : Subgroup W, IsElemAbelian p E → Nat.card E ≤ p ^ 2 := fun E hE => by
    have h := hrkp (E.map W.subtype) (thr_isElemAbelian_map hE)
    rwa [Subgroup.card_map_of_injective W.subtype_injective] at h
  have hrk3W : ∀ E : Subgroup W, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 3 := fun E hE => by
    have h := hrk3 (E.map W.subtype) (thr_isElemAbelian_map hE)
    rwa [Subgroup.card_map_of_injective W.subtype_injective] at h
  have key := hK1 p hp hp2 (↥W) (hsec.subgroup W) hcharW hrkpW hrk3W (J.subgroupOf W) hKn hPC hT
    h3 h2cl (V.subgroupOf W) hS2 hcoreS hnc'
  have hLcen : center L = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : (z : Y ⧸ CFSG.pPrimeCore p Y) ∈
        centralizer (L : Set (Y ⧸ CFSG.pPrimeCore p Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨h, hh⟩)
    rw [hLc, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.mpr (Subtype.ext hz')
  let ψ₀ : ↥(J.subgroupOf W) →* Y ⧸ CFSG.pPrimeCore p Y :=
    ((QuotientGroup.mk' (CFSG.pPrimeCore p Y)).comp W.subtype).comp (J.subgroupOf W).subtype
  have hψ₀L : ∀ x : ↥(J.subgroupOf W), ψ₀ x ∈ L := by
    intro x
    rw [← hJL]
    exact Subgroup.mem_map_of_mem _ x.2
  let ψ : ↥(J.subgroupOf W) →* ↥L := ψ₀.codRestrict L hψ₀L
  have hψ : Function.Surjective ψ := by
    rintro ⟨y, hy⟩
    rw [← hJL] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact ⟨⟨⟨j, hJW hj⟩, hj⟩, rfl⟩
  have hker : p.Coprime (Nat.card ψ.ker) := by
    have hle : ψ.ker.map (W.subtype.comp (J.subgroupOf W).subtype) ≤ CFSG.pPrimeCore p Y := by
      rintro _ ⟨x, hx, rfl⟩
      have hx1 : ψ₀ x = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      exact (QuotientGroup.eq_one_iff _).mp hx1
    have hinj : Function.Injective (W.subtype.comp (J.subgroupOf W).subtype) :=
      W.subtype_injective.comp (J.subgroupOf W).subtype_injective
    rw [← Subgroup.card_map_of_injective hinj]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hle)
      CFSG.pPrimeCore_coprime_card
  obtain ⟨e⟩ := zja_quotient_equiv hp (G := ↥(J.subgroupOf W)) (M := ↥L) hpL hLcen ψ hψ hker
  exact zja_chevTwo_or_alt_of_mulEquiv e key

end CFSG.LocalAnalysis.RankThreeTheoremC
