module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541Even
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K541EvenExcl
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.Quasithin.Vol2.Ch11SecAKE14

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData CFSG.AGLEmbedding KFactsPair
open CFSG.QuasithinUnique.Setup.X7Sec CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

namespace K541EvenProof

theorem statedModel_of_isLThreeOfExp {n : ℕ} (hn : 2 ≤ n) {S : Type} [Group S]
    (h : IsLThreeOfExp n S) : CFSG.Open.StatedClassicalModel S .PSL 3 2 n := by
  rcases h with ⟨h1, -⟩ | ⟨-, d, Q, hQ2, hQe, hd, ⟨e⟩⟩
  · omega
  · obtain ⟨d1, hv⟩ := d
    simp only at hd
    subst hd
    rcases Q with ⟨p, ex, hp, hex⟩
    simp only at hQ2 hQe
    subst hQ2
    subst hQe
    exact CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e

end K541EvenProof

open K541EvenProof in
theorem K541Even_holds :
    K541Even := by
  intro X _ _ T hX Ls hLs hcomm n hn hL3
  have hn2 : 2 ≤ n := by
    rcases hL3 with ⟨h1, -⟩ | ⟨h2, -⟩
    · subst h1; exact absurd hn (by decide)
    · exact h2
  have hodd := K541Proof.odd_card_center_of_component hX hLs
  have hqs : CFSG.Open.IsQuasisimple ↥Ls := hLs.2.2
  have hperf : Group.IsPerfect ↥Ls := Group.isPerfect_def.2 hqs.1
  have hmodel := statedModel_of_isLThreeOfExp hn2 hL3
  by_cases hZ : Subgroup.center ↥Ls = ⊥
  ·
    exfalso
    obtain ⟨W, _, _, _, ρ, hρ, A, hAel, hAbest, -, hLA⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.exists_rep_offender X T hX Ls hLs hcomm
    have hLbot : Ls ≠ ⊥ := by
      intro h
      have hs : IsSimpleGroup (↥Ls ⧸ Subgroup.center ↥Ls) := hLs.2.2.2
      subst h
      have : Nontrivial (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸
          Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T))) := hs.toNontrivial
      obtain ⟨x, y, hxy⟩ := exists_pair_ne
        (↥(⊥ : Subgroup (X ⧸ gnC T)) ⧸ Subgroup.center ↥(⊥ : Subgroup (X ⧸ gnC T)))
      induction x using QuotientGroup.induction_on with
      | _ a =>
        induction y using QuotientGroup.induction_on with
        | _ b => exact hxy (congrArg QuotientGroup.mk (Subsingleton.elim a b))
    obtain ⟨V, _, _, f, E, hV2, hfr, hirr, hEN, hE1, hEel, hEq, hoff⟩ :=
      CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.componentSectionProp (X ⧸ gnC T) W ρ hρ
        (CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531.pCore_two_gnQuot hX) A hAel hAbest Ls
        hLs (by rw [hLA]; exact hLbot)
    let e0 : (↥Ls ⧸ Subgroup.center ↥Ls) ≃* ↥Ls :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    haveI : IsSimpleGroup ↥Ls := by
      haveI := hLs.2.2.2
      exact e0.symm.isSimpleGroup
    have hfinj : Function.Injective f := by
      rw [← MonoidHom.ker_eq_bot_iff]
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal f.ker with h | h
      · exact h
      · exfalso
        apply hfr
        refine eq_bot_iff.2 ?_
        rintro _ ⟨x, rfl⟩
        have hx : x ∈ f.ker := h ▸ Subgroup.mem_top x
        exact Subgroup.mem_bot.2 (MonoidHom.mem_ker.1 hx)
    let e : ↥Ls ≃* ↥f.range := MonoidHom.ofInjective hfinj
    have hperfL : Group.IsPerfect ↥f.range :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    have hmapc : (Subgroup.center ↥Ls).map e.toMonoidHom = Subgroup.center ↥f.range :=
      Subgroup.map_center_eq e
    have hcL : Subgroup.center ↥f.range = ⊥ := by rw [← hmapc, hZ, Subgroup.map_bot]
    have hmodelL : CFSG.Open.StatedClassicalModel (↥f.range ⧸ Subgroup.center ↥f.range)
        .PSL 3 2 n :=
      CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv
        (QuotientGroup.congr _ _ e hmapc) hmodel
    have := evenExclusion hn hn2 V hV2 f.range E hirr hperfL hcL hmodelL hEN hE1 hEel hEq
    omega
  ·
    obtain ⟨F, iF, iFin, φ, hFcard, hcov⟩ :=
      exists_cover_of_model hperf hodd (by omega : 1 ≤ n) hmodel
    have hS3 : Nat.card (scalars 3 F) ∣ 3 := by
      rw [scalars_eq_center]
      exact CFSG.Quasithin.Vol2.Ch11.SecA.C10KH.card_center_sl3_dvd F
    have hkerS : φ.ker ≤ scalars 3 F := fun x hx => hcov.ker_le x hx
    have hnb : ¬ scalars 3 F ≤ φ.ker := by
      intro hle
      apply hZ
      rw [← hcov.map_scalars, eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      exact Subgroup.mem_bot.2 (hle hs)
    have hk3 : Nat.card φ.ker ∣ 3 := (Subgroup.card_dvd_of_le hkerS).trans hS3
    have hkbot : φ.ker = ⊥ := by
      rcases (Nat.dvd_prime Nat.prime_three).1 hk3 with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hnb
        have hS3' : Nat.card (scalars 3 F) ≤ 3 := Nat.le_of_dvd (by norm_num) hS3
        rw [← Subgroup.eq_of_le_of_card_ge hkerS
          (by omega : Nat.card (scalars 3 F) ≤ Nat.card φ.ker)]
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hkbot
    have : Fintype F := Fintype.ofFinite F
    have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
    have hFcard' : Fintype.card F = 2 ^ n := by rw [Fintype.card_eq_nat_card]; exact hFcard
    have hGF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
      rw [Fintype.card_eq_nat_card]; exact GaloisField.card 2 n (by omega)
    let εF : F ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by rw [hFcard', hGF])
    exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hcov.surjective⟩).symm.trans
      (CFSG.LargeExtraspecial.A2Mod.slEquiv εF)⟩

end CFSG.LocalAnalysis.RankThreeUC.S15
