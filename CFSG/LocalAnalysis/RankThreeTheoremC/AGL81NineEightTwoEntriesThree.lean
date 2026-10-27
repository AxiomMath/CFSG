module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineEightTwoEntries
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3SylowKleinTools
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62Check
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Sp62Transport
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48Inner
import CFSG.Adapters.CatalogueFieldBridges.Symplectic
import CFSG.RankThree.PartTwo.Sec4.T444.Item434RemTitsLocal
import CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux.Cat
public import CFSG.RankThree.PartTwo.Toolkit.M12LocalGroups
public import CFSG.Sporadic.Schreier.TitsCert

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111

open CFSG.Open

theorem kFactNineThreeNoTwoAt_of_model {p : ℕ} (hp : p.Prime) {i : TauCeti.CFSGIndex}
    {M : Type} [Group M] [Finite M] (hM : Nonempty (M ≃* i.Group)) {B₀ : Subgroup M}
    (hB₀ : IsPGroup p B₀)
    (h : ∀ V : Subgroup (MulAut M), IsPGroup 2 V →
      B₀.map (MulAut.conj : M →* MulAut M) ≤ Subgroup.normalizer (V : Set (MulAut M)) → V = ⊥) :
    KFactNineThreeNoTwoAt p i := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro X _ _ K hK ⟨e⟩ _ T S hS hTS
  haveI := hK
  obtain ⟨eM⟩ := hM
  obtain ⟨T₀, hBT₀⟩ := hB₀.exists_le_sylow
  obtain ⟨Φ, hΦ⟩ := exists_mulEquiv_map_eq_sylow (e.trans eM.symm) T₀.isPGroup'
    T₀.not_dvd_index T
  set ψ : MulAut K ≃* MulAut M := MulAut.congr Φ.symm with hψ
  have hψc : ∀ r : M, ψ (MulAut.conj (Φ r)) = MulAut.conj r := by
    intro r
    ext a
    simp [hψ, MulAut.conj_apply]
  refine Hyp111.le_centralizer_of_aut (T := (T : Subgroup K).map K.subtype)
    (Subgroup.map_subtype_le _) (fun V hV hN => ?_) hS hTS
  refine (Subgroup.map_eq_bot_iff_of_injective (f := ψ.toMonoidHom) V ψ.injective).1
    (h _ (hV.map _) ?_)
  rintro _ ⟨r, hr, rfl⟩
  have hrT : Φ r ∈ (T : Subgroup K) := by
    rw [hΦ]
    exact ⟨r, hBT₀ hr, rfl⟩
  rw [← Subgroup.map_equiv_normalizer_eq, ← hψc r]
  exact ⟨_, hN (Φ r) ⟨Φ r, hrT, rfl⟩, rfl⟩

theorem kFactNineThreeNoTwoAt_of_model_coprime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {i : TauCeti.CFSGIndex} {M : Type} [Group M] [Finite M] (hM : Nonempty (M ≃* i.Group))
    {B₀ : Subgroup M} (hB₀ : IsPGroup p B₀)
    (h : ∀ V : Subgroup (MulAut M), ¬ p ∣ Nat.card V →
      B₀.map (MulAut.conj : M →* MulAut M) ≤ Subgroup.normalizer (V : Set (MulAut M)) → V = ⊥) :
    KFactNineThreeNoTwoAt p i := by
  refine kFactNineThreeNoTwoAt_of_model hp hM hB₀ fun V hV hN => h V ?_ hN
  obtain ⟨k, hk⟩ := hV.exists_card_eq
  rw [hk]
  exact fun hdvd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd))

theorem kFactNineThreeNoTwoAt_linThreeFour {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 2 ∧ d.1 = .A 2 q) :
    KFactNineThreeNoTwoAt 3 (.lie d) :=
  fun _ _ _ _ _ hiso hL34 => (hL34 ⟨rfl, d, hd, hiso⟩).elim

open CFSG.RankThree.PartTwo.Toolkit.M12 in
theorem kFactNineThreeNoTwoAt_m12 :
    KFactNineThreeNoTwoAt 3 (.sporadic .M12) := by
  have hE : IsElemAbelian 3 basisE.sub :=
    isElemAbelian_iff_isElementaryAbelian.mpr basisE.isElementaryAbelian
  exact kFactNineThreeNoTwoAt_of_model_coprime Nat.prime_three (by norm_num)
    CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv hE.isPGroup
    (CFSG.RankThree.PartTwo.Sec4.Item434SporGen.noSignalizer_E hE)

open CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two CFSG.RankThree.PartTwo.Sec4
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII CFSG.RankThree.PartTwo.Sec4.Item434Kit in
theorem kFactNineThreeNoTwoAt_sp62 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 1 ∧ d.1 = .B 3 q) :
    KFactNineThreeNoTwoAt 3 (.lie d) := by
  obtain ⟨e⟩ := KFactProofs.nonempty_catGroup_equiv_H6 d hd
  have hZ : Subgroup.center H6 = ⊥ := by
    haveI : IsSimpleGroup (StatedProj (StatedSp 3 (ZMod 2))) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp (ZMod 2) 3 (by norm_num)
        (Or.inr (Or.inr ⟨Nat.card_zmod 2, le_rfl⟩))
    haveI : IsSimpleGroup H6 := CFSG.AGLEmbedding.KFactProofs.Sp62Local.eProj.symm.isSimpleGroup
    exact Item434Spor.center_eq_bot_of_simple (by rw [card_H6]; norm_num)
  have hinj := conj_injective_of_center_eq_bot hZ
  have hf := wreathFacts_zH
  refine kFactNineThreeNoTwoAt_of_model_coprime Nat.prime_three (by norm_num) ⟨e.symm⟩
    (isElemAbelian_baseA hf).isPGroup fun Y hY3 hYN => ?_
  set Y' := Y.comap (MulAut.conj : H6 →* MulAut H6) with hY'
  have hYmap : Y'.map MulAut.conj = Y := Subgroup.map_comap_eq_self fun φ _ => by
    obtain ⟨g, hg⟩ := CFSG.AGLEmbedding.KFactProofs.Sp62Local.all_inner_H6 φ
    exact MonoidHom.mem_range.2 ⟨g, hg.symm⟩
  have hY'card : Nat.card Y' = Nat.card Y := by
    conv_rhs => rw [← hYmap]
    rw [Subgroup.card_map_of_injective hinj]
  have hAN : baseA zH ≤ Subgroup.normalizer (Y' : Set H6) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hc := Subgroup.mem_normalizer_iff.mp (hYN ⟨a, ha, rfl⟩) (MulAut.conj y)
    rw [hY', Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hc
  have hbot := eq_bot_of_baseA_le_normalizer (by rwa [hY'card]) hAN
  rw [← hYmap, hbot, Subgroup.map_bot]

open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag in
theorem kFactNineThreeNoTwoAt_sp48 {d : TauCeti.ValidLieTypeIndex}
    (hd : ∃ q : TauCeti.PrimePower, q.p = 2 ∧ q.exponent = 3 ∧ d.1 = .B 2 q) :
    KFactNineThreeNoTwoAt 3 (.lie d) := by
  obtain ⟨d1, hv⟩ := d
  obtain ⟨q, hqp, hqe, hd1⟩ := hd
  change d1 = _ at hd1
  subst hd1
  have hk : Nat.card (GaloisField 2 3) = q.card := by
    rw [TauCeti.PrimePower.card_def, hqp, hqe, GaloisField.card 2 3 (by norm_num)]
  obtain ⟨e⟩ := CFSG.Adapters.CatalogueFieldBridges.nonempty_mulEquiv_lie_B2_of_statedProj hv hk
  have hfinj : Function.Injective (proj 2 (GaloisField 2 3)) :=
    CFSG.RankThree.PartTwo.KFacts.proj_injective_of_charTwo
  obtain ⟨hE, hE9⟩ := isElemAbelian_sp4E9 (F := GaloisField 2 3)
  have hEe := hE.map (proj 2 (GaloisField 2 3))
  have hE9' : Nat.card ((sp4E9 (GaloisField 2 3)).map (proj 2 (GaloisField 2 3))) = 9 := by
    rw [Subgroup.card_map_of_injective hfinj, hE9]
  exact kFactNineThreeNoTwoAt_of_model_coprime Nat.prime_three (by norm_num) ⟨e⟩ hEe.isPGroup
    fun Y hY hYN => eq_bot_of_inn_le_normalizer hEe hE9' hY hYN

open CFSG.Sporadic.Schreier.Tits CFSG.RankThree.PartTwo.Sec4.Item434RemTits
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux in
theorem kFactNineThreeNoTwoAt_titsThree
    {d : TauCeti.ValidLieTypeIndex} (hd : d.1 = .tits) :
    KFactNineThreeNoTwoAt 3 (.lie d) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d1, hv⟩ := d
  change d1 = _ at hd
  subst hd
  obtain ⟨e⟩ := nonempty_mulEquiv_titsD_cat hv
  have h27 : (Nat.card titsD).factorization 3 = 3 :=
    CFSG.RankThree.PartTwo.Sec4.Item434RemTits.factorization_card_titsD
  obtain ⟨K₉, hK₉⟩ := Sylow.exists_subgroup_card_pow_prime (G := sylD) 3 (n := 2)
    (by rw [card_sylD, h27]; norm_num)
  set E := K₉.map sylD.subtype with hEdef
  have hE9 : Nat.card E = 9 := by
    rw [hEdef, Subgroup.card_map_of_injective sylD.subtype_injective, hK₉]
    norm_num
  have hEe : IsElemAbelian 3 E := by
    refine ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hE9]; norm_num), ?_⟩
    rintro _ ⟨r, -, rfl⟩
    have h3 : ((r : titsD) : Equiv.Perm (Fin 1755)) * r * r = 1 :=
      cube_of_mem_sylPerms (mem_sylGrp.1 (Subgroup.mem_subgroupOf.1 r.2))
    have hr3 : (r : titsD) ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, pow_three']
      exact h3
    exact hr3
  exact kFactNineThreeNoTwoAt_of_model_coprime Nat.prime_three (by norm_num) ⟨e.symm⟩
    hEe.isPGroup (noSignalizer hEe hE9)

end CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
