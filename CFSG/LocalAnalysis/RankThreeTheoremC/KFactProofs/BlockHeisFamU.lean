module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamUSylow
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamUArith
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisFamDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisOut
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisRank
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open CFSG.Open CFSG.Blueprint CFSG.AGLEmbedding

theorem famU_noHeisAut
    {L : Type} [Group L] [Finite L] (hperf : Group.IsPerfect L) (hrk : OddRankLeThree L)
    (hsimp : IsSimpleGroup (L ⧸ Subgroup.center L)) {n f : ℕ}
    (hm : StatedClassicalModel (L ⧸ Subgroup.center L) .PSU n 2 f) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (hgcd : ¬ p ∣ Nat.gcd n (2 ^ f + 1))
    (hlt : n / orderOf (-((2 ^ f : ℕ) : ZMod p)) < p)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) : NoHeisAut p (L ⧸ Subgroup.center L) := by
  haveI := hperf
  haveI := hsimp
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hmodel : LieModel (L ⧸ Subgroup.center L) .PSU n 2 f :=
    Or.inl ⟨by simp [classicalTags], hm⟩
  obtain ⟨hCyc, hout⟩ := heis_out_data hp hp5 hmodel (by decide)
    (fun h => absurd h (by decide)) (fun _ => hgcd)
  obtain ⟨⟨-, hf, hn3, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hm
  have hpq : ¬ p ∣ 2 ^ f := fun h => by
    have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow h)
    omega
  obtain ⟨M, _, hMc, hMp, hS⟩ :=
    famU_sylow_PSU (L := K) (n := n) hp hp2 Nat.prime_two hK hpq (by omega) hgcd hlt
  have hXS := famU_sylowShape_of_mulEquiv eK.symm hS
  refine noHeisAut_of_abelian_sylow hp hp5 (heis_conj_injective L) hCyc
    (fun A hA hAp => heis_rank_quotient hrk hp hp2 hZ A hA hAp) fun S => ?_
  obtain ⟨φ⟩ := hXS S
  refine ⟨fun x hx y hy => ?_, fun hα => Or.inr ?_⟩
  · have h := hMc (φ ⟨x, hx⟩) (φ ⟨y, hy⟩)
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (φ.injective h)
  · obtain ⟨f₀, hf₀⟩ := hout hα
    have ha : 2 ≤ padicValInt p ((-((2 ^ f : ℕ) : ℤ)) ^ orderOf (-((2 ^ f : ℕ) : ZMod p)) - 1) := by
      subst hf₀
      have h1 : 1 ≤ f₀ := by
        rcases Nat.eq_zero_or_pos f₀ with h0 | h0
        · rw [h0, mul_zero] at hf
          omega
        · exact h0
      have h2 : ¬ p ∣ 2 := fun h => by
        have := Nat.le_of_dvd (by norm_num) h
        omega
      exact famU_two_le_padicValInt hp hp2 h2 le_rfl h1
    intro x hx hxp
    obtain ⟨y, hy⟩ := hMp ha (φ ⟨x, hx⟩) (by
      rw [← map_pow]
      have : (⟨x, hx⟩ : (S : Subgroup (L ⧸ Subgroup.center L))) ^ p = 1 := Subtype.ext hxp
      rw [this, map_one])
    refine ⟨(φ.symm y : (S : Subgroup (L ⧸ Subgroup.center L))), (φ.symm y).2, ?_⟩
    have : (φ.symm y) ^ p = ⟨x, hx⟩ := by
      apply φ.injective
      rw [map_pow, MulEquiv.apply_symm_apply, hy]
    exact congrArg Subtype.val this

theorem heisCoreOn_idxTwistedA_of_rank_facts
    (hF : HeisURankFacts) : HeisCoreOn IdxTwistedA := by
  intro L _ _ hperf hodd hrk hsimp d hd e p hp hp5
  obtain ⟨d, hv⟩ := d
  cases d with
  | twistedA r q =>
    change q.p = 2 at hd
    have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
    rw [hd] at hc
    have hc' := hc
    obtain ⟨⟨-, hf, hn3, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hc'
    rcases hF L hperf hodd hrk hsimp (r + 1) q.exponent K hK hn3 hf eK p hp hp5 with
      ⟨hgcd, hlt, hZ⟩ | ⟨h5, hn5, hf2, hbot⟩
    · exact Or.inl (famU_noHeisAut hperf hrk hsimp hc hp hp5 hgcd hlt hZ)
    · refine Or.inr ⟨h5, hbot, q, ?_, ?_⟩
      · have hr : r = 4 := by omega
        subst hr
        rfl
      · rw [TauCeti.PrimePower.card_def, hd, hf2]
        norm_num
  | _ => exact hd.elim

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
