module

public import CFSG.ClassicalInvolution.Asc77.AscP1Lem75Conj
import CFSG.ClassicalInvolution.Asc77.AscT8T5Eng
public import CFSG.ClassicalInvolution.Q3.TL4ConnDefs

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight

section Mu

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conjSub_mem_DSet_conj_gen (hΩ : HypOmegaGen Ω) {W R : Subgroup G} (hR : R ∈ DSet Ω W)
    (g : G) : conjSub g R ∈ DSet Ω (conjSub g W) := by
  refine ⟨Q3CL.Thompson.conjSub_mem_RSet hΩ hR.1 g, fun x hx => ?_⟩
  rw [mem_conjSub_iff] at hx
  have h1 := hR.2 hx
  rw [Thompson.conjSub_normalizer, mem_conjSub_iff]
  exact h1

theorem conjSub_MGrp_gen (hΩ : HypOmegaGen Ω) (g : G) (W : Subgroup G) :
    conjSub g (MGrp Ω W) = MGrp Ω (conjSub g W) := by
  apply le_antisymm
  · unfold MGrp
    rw [conjSub, Subgroup.map_iSup]
    refine iSup_le fun R => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hR => ?_
    exact le_iSup₂ (f := fun R (_ : R ∈ DSet Ω (conjSub g W)) => R) (conjSub g R)
      (conjSub_mem_DSet_conj_gen hΩ hR g)
  · refine iSup₂_le fun R hR => ?_
    have hR' : conjSub g⁻¹ R ∈ DSet Ω W := by
      have := conjSub_mem_DSet_conj_gen hΩ hR g⁻¹
      rwa [conjSub_inv_conjSub] at this
    have h1 : conjSub g⁻¹ R ≤ MGrp Ω W := le_MGrp_of_mem_D hR'
    have h2 := conjSub_mono (n := g) h1
    rwa [conjSub_conjSub_inv] at h2

noncomputable def muGroupConjEquivGen (hΩ : HypOmegaGen Ω) (g : G) (W : Subgroup G) :
    ↥(muGroup Ω W) ≃* ↥(muGroup Ω (conjSub g W)) :=
  (MulEquiv.subgroupMap (nquotConj g (conjSub_sup_OCW g W)) (muGroup Ω W)).trans
    (MulEquiv.subgroupCongr (by
      ext q
      constructor
      · rintro ⟨q₀, hq₀, rfl⟩
        obtain ⟨m, hm, rfl⟩ := mem_muGroup_iff.mp hq₀
        have hmN : m ∈ Subgroup.normalizer (W : Set G) := MGrp_sup_le_normalizer Ω W hm
        show nquotConj g (conjSub_sup_OCW g W) (piG W m) ∈ _
        rw [nquotConj_piG g W hmN]
        refine piG_mem_muGroup ?_
        rw [← conjSub_MGrp_gen hΩ, ← conjSub_OCW, ← Thompson.conjSub_sup]
        exact conj_mem_conjSub hm
      · intro hq
        obtain ⟨m', hm', rfl⟩ := mem_muGroup_iff.mp hq
        rw [← conjSub_MGrp_gen hΩ, ← conjSub_OCW, ← Thompson.conjSub_sup, mem_conjSub_iff] at hm'
        refine ⟨piG W (g⁻¹ * m' * g), piG_mem_muGroup hm', ?_⟩
        have hmN : g⁻¹ * m' * g ∈ Subgroup.normalizer (W : Set G) :=
          MGrp_sup_le_normalizer Ω W hm'
        show nquotConj g (conjSub_sup_OCW g W) (piG W (g⁻¹ * m' * g)) = _
        rw [nquotConj_piG g W hmN]
        congr 1
        group))

omit [Finite G] in
theorem muAbelian_notE4_transfer_gen {W W' : Subgroup G}
    (e : ↥(muGroup Ω W) ≃* ↥(muGroup Ω W'))
    (hab : ∀ x ∈ muGroup Ω W, ∀ y ∈ muGroup Ω W, x * y = y * x) (hE4 : ¬ MuIsoE4 Ω W) :
    (∀ x ∈ muGroup Ω W', ∀ y ∈ muGroup Ω W', x * y = y * x) ∧ ¬ MuIsoE4 Ω W' :=
  CFSG.ClassicalInvolution.Asc77.T8T.muAbelian_notE4_transfer_gen e hab hE4

theorem exists_conjSub_wset_le (hΩ : ConjInvariant Ω) {W₀ : Subgroup G} (hW₀ : W₀ ∈ WSet Ω)
    (S : Sylow 2 G) :
    ∃ g : G, conjSub g W₀ ∈ WSet Ω ∧ conjSub g W₀ ≤ (S : Subgroup G) ∧
      ∀ s ∈ (S : Subgroup G), conjSub s (conjSub g W₀) = conjSub g W₀ := by
  obtain ⟨η₀, ⟨S₀, hη₀, hinv⟩, rfl⟩ := hW₀
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow S₀ S
  have hle : (⨆ U ∈ η₀, U : Subgroup G) ≤ (S₀ : Subgroup G) :=
    iSup₂_le fun U hU => (hη₀.1 hU).2
  have hN : (S₀ : Subgroup G) ≤ Subgroup.normalizer ((⨆ U ∈ η₀, U : Subgroup G) : Set G) :=
    le_normalizer_biSup_of_acts hinv
  refine ⟨g, WSet.conj hΩ ⟨η₀, ⟨S₀, hη₀, hinv⟩, rfl⟩ g, ?_, fun s hs => ?_⟩
  · rw [← hg]
    exact conjSub_mono hle
  · rw [← hg, mem_conjSub_iff] at hs
    have h1 : conjSub (g⁻¹ * s * g) (⨆ U ∈ η₀, U : Subgroup G) = ⨆ U ∈ η₀, U :=
      mem_normalizer_iff_conjSub_eq.mp (hN hs)
    calc conjSub s (conjSub g (⨆ U ∈ η₀, U : Subgroup G))
        = conjSub g (conjSub (g⁻¹ * s * g) (⨆ U ∈ η₀, U : Subgroup G)) := by
          rw [← conjSub_mul, ← conjSub_mul]
          congr 1
          group
      _ = conjSub g (⨆ U ∈ η₀, U : Subgroup G) := by rw [h1]

end Mu

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {Rd : Subgroup Y} {Sd : Sylow 2 Rd} {z : Y}

theorem TightLargeHypR.exists_std8_of_wset (hL : TightLargeHypR r n Y Rd Sd z)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {t : Y} (ht : IsUniqueInvolution J t) {W₀ : Subgroup Y}
    (hW₀ : W₀ ∈ WSet (CoreAssembly.conjClass (tightCore Rd))) :
    ∃ (g : Y) (S : Sylow 2 Y) (R T : Subgroup Y),
      TightStd8R r n Rd Sd z J S R T (conjSub g W₀) t := by
  have hΩ := hL.datum.hypOmegaGen
  have hK : tightCore Rd ∈ CoreAssembly.conjClass (tightCore Rd) :=
    CoreAssembly.mem_conjClass_self _
  obtain ⟨hJΩ, -, T, hT, hTJ, hTN⟩ := id hJ
  have hTJ' : IsSylow2In T J := Q3CL.T3.isSylow2In_of_mem_RSet_of_le hΩ hJΩ hT hTJ
  obtain ⟨R, hRK, hRfix⟩ := exists_sylow_normalized hTJ'.2.1 hTN
  have hRn : T ≤ Subgroup.normalizer (R : Set Y) := fun w hw =>
    mem_normalizer_iff_conjSub_eq.mpr (hRfix w hw)
  obtain ⟨S, hS⟩ := (hTJ'.2.1.to_sup_of_normal_right' hRK.2.1 hRn).exists_le_sylow
  obtain ⟨g, hgW, hgS, hgN⟩ := exists_conjSub_wset_le hΩ.conjInvariant hW₀ S
  exact ⟨g, S, R, T,
    { large := hL
      hJ := hJ
      ht := ht
      hR := ⟨mem_RSet_of_isSylow2In hK hRK, hRK.1, le_sup_right.trans hS⟩
      hT := ⟨hT, hTJ, le_sup_left.trans hS⟩
      hW := ⟨hgW, hgS, hgN⟩ }⟩

theorem TightLargeHypR.exists_std8_mu (hL : TightLargeHypR r n Y Rd Sd z)
    {J : Subgroup Y} (hJ : J ∈ omegaNbr (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd))
    {t : Y} (ht : IsUniqueInvolution J t)
    (hμ : ∃ W₀ ∈ WSet (CoreAssembly.conjClass (tightCore Rd)),
      (∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W₀,
        ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W₀, x * y = y * x) ∧
      ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W₀) :
    ∃ (S : Sylow 2 Y) (R T W : Subgroup Y), TightStd8R r n Rd Sd z J S R T W t ∧
      (∀ x ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W,
        ∀ y ∈ muGroup (CoreAssembly.conjClass (tightCore Rd)) W, x * y = y * x) ∧
      ¬ MuIsoE4 (CoreAssembly.conjClass (tightCore Rd)) W := by
  obtain ⟨W₀, hW₀, hab, hE4⟩ := hμ
  obtain ⟨g, S, R, T, hs⟩ := TightLargeHypR.exists_std8_of_wset hL hJ ht hW₀
  exact ⟨S, R, T, conjSub g W₀, hs,
    muAbelian_notE4_transfer_gen (muGroupConjEquivGen hL.datum.hypOmegaGen g W₀) hab hE4⟩

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
