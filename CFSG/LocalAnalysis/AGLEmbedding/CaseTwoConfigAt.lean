module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallCentralizer
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPOdd
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoNoSPDefs
import CFSG.Assembly.ComponentTypeDefs
import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1ComponentConfigU.b0_of_shape (hcfg : D1ComponentConfigU p P M H R Rbar) {z : G}
    (hzp : orderOf z = p) (hzR : z ∈ R) (hRz : R ≤ Subgroup.centralizer ({z} : Set G))
    (hCM : ¬ Subgroup.centralizer ({z} : Set G) ≤ M)
    (hshape : D1CzShape p P M R z)
    (hnTQ : ∀ m ∈ M, ∀ T : Sylow p (Subgroup.centralizer ({z} : Set G)),
      R ≤ (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype →
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≤
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom →
      (T : Subgroup _).map (Subgroup.centralizer ({z} : Set G)).subtype ≠
        (P : Subgroup G).map (MulAut.conj m).toMonoidHom) :
    D1CzB0 p R z ∧ pCoreOf 2 M ⊓ Subgroup.centralizer ({z} : Set G) ≠ ⊥ ∧ D1CzEven p z := by
  have hp := hcfg.red.prime
  have hp2 := hcfg.red.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({z} : Set G) with hCdef
  obtain ⟨m, hm, T, hRT, hTP⟩ := hcfg.exists_sylow_centralizer hRz
  set Q' : Subgroup G := (P : Subgroup G).map (MulAut.conj m).toMonoidHom with hQ'def
  set Tg : Subgroup G := (T : Subgroup C).map C.subtype with hTgdef
  have hQ'p : IsPGroup p Q' := P.isPGroup'.map _
  have hQ'M : Q' ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact M.mul_mem (M.mul_mem hm (hcfg.ext.sylow_le hx)) (M.inv_mem hm)
  have hTgC : Tg ≤ C := Subgroup.map_subtype_le _
  have hne : Tg ≠ Q' := hnTQ m hm T hRT hTP
  have hQC : Q' ⊓ C ≤ Tg := by
    rintro x ⟨hxQ, hxC⟩
    have hTeq : (T : Subgroup C) = Q'.subgroupOf C :=
      (T.is_maximal' hQ'p.comap_subtype fun t ht => hTP ⟨t, ht, rfl⟩).symm
    have hx : (⟨x, hxC⟩ : C) ∈ (T : Subgroup C) := by
      rw [hTeq]
      exact hxQ
    exact ⟨_, hx, rfl⟩
  obtain ⟨t, htT, htc, htp, htz, hΩ⟩ := hshape.1 m hm T hRT hTP
  have hzT : z ∈ Tg := hRT hzR
  have hzc : ∀ g ∈ Tg, Commute z g := fun g hg =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hTgC hg)).symm
  have hne2 := twoCore_inf_centralizer_ne_bot hcfg.glob.charTwo hcfg.loc.maxLocal.1 hp2 hQ'p
    hQ'M hTP hne hzT htT hzc htc hzp htp htz hΩ hQC
  have hle := hshape.2
  have heven : 2 ∣ Nat.card (GLBPrimeCore p C) := by
    obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne2
    obtain ⟨k, hk⟩ := (RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M).to_inf_left
      (K := C) u
    have hku : (u : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hu1' : (u : G) ≠ 1 := fun h => hu1 (Subtype.ext h)
    have hord : orderOf (u : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hku
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hu1' (orderOf_eq_one_iff.mp (by rw [hj, pow_zero]))
    have h2 : 2 ∣ orderOf (u : G) := by
      rw [hj]
      exact dvd_pow_self 2 hj0
    exact h2.trans (Subgroup.orderOf_dvd_natCard _ (hle u.2))
  refine ⟨?_, hne2, heven⟩
  by_contra hnB0
  have hRne : R ≠ Tg := fun h => hnB0 ⟨T, h.symm⟩
  have hcard := Subgroup.card_lt_of_lt (lt_of_le_of_ne hRT hRne)
  have hcore : GLBPrimeCore p C ≤ M :=
    intersecting_local_primeCore_le p hp P hcfg.ext.sylow_le hcfg.ext.weakCore_le
      (hcfg.ext.three_le_pRank.trans (pRank_mono p hp (le_inf hRz hcfg.ext.le_M)))
  have hodd := D1Extremal.odd_card_glbPrimeCore_of_lt hcfg.ext hCM hcore (T.isPGroup'.map _) hTgC
    (hTP.trans hQ'M) (hcfg.ext.three_le_pRank.trans (pRank_mono p hp hRT)) hcard
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr heven)

end CFSG.AGLEmbedding
