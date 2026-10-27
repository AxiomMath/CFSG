module

public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.CaseDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple
public import CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius.LemmaQ

public section

open Subgroup

namespace CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius

theorem isPerfect_psl_gen {p n : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) :
    Group.IsPerfect (CFSG.AGLEmbedding.PSL2GF p n) := by
  have hcast : ∀ m : ℕ, 0 < m → m < p → ((m : ℕ) : GaloisField p n) ≠ 0 := by
    intro m hm0 hmp h
    rw [CharP.cast_eq_zero_iff (GaloisField p n) p] at h
    exact absurd (Nat.le_of_dvd hm0 h) (by omega)
  refine ⟨SL2Simple.PSL_commutator_eq_top ⟨2, ?_, fun h => ?_⟩⟩
  · exact_mod_cast hcast 2 (by norm_num) (by omega)
  · have h3 : ((3 : ℕ) : GaloisField p n) = 0 := by
      push_cast
      linear_combination h
    exact hcast 3 (by norm_num) (by omega) h3

theorem frobCaseI_holds : FrobCaseI := by
  intro hSE Sch p n _ hp5 hn3 Y _ _ hcore hcat L U Γ e hUL hUY hΓ hN hLΓ W hW hUW
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have hn2 : 2 ≤ n := by omega
  obtain ⟨Q₀, hQ₀⟩ := hUY
  let S : Sylow p Y := Sylow.mapSurjective (f := (⊤ : Subgroup Y).subtype)
    (fun y => ⟨⟨y, mem_top y⟩, rfl⟩) Q₀
  have hSU : (S : Subgroup Y) = U := (Sylow.coe_mapSurjective _ _).trans hQ₀
  have hNS : ∀ D : Subgroup Y, D ≤ S → D ≠ ⊥ → normalizer (D : Set Y) ≤ Γ := hSU ▸ hN
  have hpc :=
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.pCore_eq_bot S hΓ hNS
  have hY : (⊤ : Subgroup Y) ≠ ⊥ := fun h => hLΓ (le_top.trans (h ▸ bot_le))
  obtain ⟨K, hK⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.exists_isComponentOf
      hcore hpc hY
  have huniq : ∀ K' : Subgroup Y, CFSG.Open.IsComponentOf K' ⊤ → K' = K := fun K' hK' =>
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.eq_of_isComponentOf
      hp2 hcore S hΓ hNS hK' hK
  have hKn : K.Normal :=
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.normal_of_unique hK huniq
  have hZ := CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.center_eq_bot
    hp hcore hK (fun N _ hNp =>
      CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.normal_eq_bot S hΓ hNS hNp)
  obtain ⟨hsimple, hnonab⟩ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.simple_of_center_eq_bot hK hZ
  have hcatK : CFSG.Open.IsCatalogGroup K := hcat.simple_subgroup K hsimple hnonab
  have hC := CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.centralizer_eq_bot
    hcore hpc hK huniq hZ
  have := Sch K hsimple hnonab hcatK
  have hPSL : Group.IsPerfect (CFSG.AGLEmbedding.PSL2GF p n) := isPerfect_psl_gen hp5
  have : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hLK : L ≤ K :=
    CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic5AlmostSimple.le_of_isPerfect hC L
  obtain ⟨T, hT⟩ :=
    CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal S ‹K.Normal›.isSubnormal
  rw [hSU, inf_eq_left.mpr (hUL.le.trans hLK)] at hT
  have hGLB : CFSG.Open.GLBCore p 1 (T : Subgroup K) ≠ ⊤ := by
    have hle : CFSG.Open.GLBCore p 1 (T : Subgroup K) ≤ Γ.comap K.subtype := by
      refine sSup_le ?_
      rintro _ ⟨Q, hQT, hQ1, rfl⟩ x hx
      change (x : Y) ∈ Γ
      have hQne : Q.map K.subtype ≠ ⊥ := by
        rw [Ne, map_eq_bot_iff_of_injective _ K.subtype_injective]
        rintro rfl
        obtain ⟨E, hE, -, hEc⟩ :=
          CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hp (⊥ : Subgroup K)
        rw [le_bot_iff.mp hE, card_bot, ← pow_zero p] at hEc
        have := Nat.pow_right_injective hp.two_le hEc
        omega
      exact hN (Q.map K.subtype) ((map_mono (f := K.subtype) hQT).trans hT.le) hQne
        (le_normalizer_map K.subtype ⟨x, hx, rfl⟩)
    intro htop
    rw [htop, top_le_iff] at hle
    refine hLΓ fun l hl => ?_
    have : (⟨l, hLK hl⟩ : K) ∈ Γ.comap K.subtype := hle ▸ mem_top _
    exact this
  have hTL : (T : Subgroup K) ≤ L.subgroupOf K := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hUL.le (hT.le (mem_map_of_mem K.subtype hx))
  have hLe : Nonempty (L.subgroupOf K ≃* CFSG.AGLEmbedding.PSL2GF p n) :=
    ⟨(subgroupOfEquivOfLe hLK).trans e⟩
  have hLtop : L.subgroupOf K = ⊤ :=
    hSE K hsimple hnonab hcatK p n hp5 hn3 T (L.subgroupOf K) hTL hLe hGLB
  have hKL : K ≤ L := by
    intro y hy
    have hmem : (⟨y, hy⟩ : K) ∈ L.subgroupOf K := by
      rw [hLtop]
      exact mem_top _
    exact Subgroup.mem_subgroupOf.mp hmem
  have hLeq : L = K := le_antisymm hLK hKL
  have hWN : W ≤ normalizer (L : Set Y) := by
    rw [hLeq, normalizer_eq_top]
    exact le_top
  have hUp : IsPGroup p U := hUL.isPGroup
  have hUc : Nat.card U = p ^ n := by
    obtain ⟨Q, hQ⟩ := hUL
    have h1 := (CFSG.AGLEmbedding.psl2GF_sylow p n (by omega)
      (Sylow.mapSurjective (f := e.toMonoidHom) e.surjective Q)).2
    rw [Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective Q] at h1
    rw [← hQ, Subgroup.card_map_of_injective L.subtype_injective,
      ← Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
    exact h1
  have hWC : W ≤ centralizer (L : Set Y) :=
    le_centralizer_of_coprime_of_psl2GF hp2 hn2 e hUL.le hUp hUc hWN hUW hW
  have hCL : centralizer (L : Set Y) = ⊥ := by
    rw [hLeq]
    exact hC
  rw [hCL] at hWC
  exact le_bot_iff.mp hWC

end CFSG.LocalAnalysis.RankFourTheoremC.PPointFrobenius
