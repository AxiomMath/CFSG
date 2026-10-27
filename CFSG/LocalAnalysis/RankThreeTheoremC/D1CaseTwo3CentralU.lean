module

public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3DataU
import CFSG.LocalAnalysis.AGLEmbedding.A15ComponentsAux
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarCore
import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoStarProj
import CFSG.LocalAnalysis.AGLEmbedding.OneLieLambdaAux
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDataBase
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.AGLEmbedding

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}

theorem D1CaseTwoDataU.toPhaseThree (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoDataU p P M H R Rbar) : D1PhaseThree p P M H R :=
  hd.cfg.toU.toPhaseThree_of_rank (kFactCycAut_of_kFactOutCyclic hOut) hS hKL hd.cyclic hd.rank

theorem D1CaseTwoDataU.toBase (hd : D1CaseTwoDataU p P M H R Rbar) :
    D1CaseTwoDataBase p P M H R Rbar :=
  ⟨hd.cfg.toU, hd.cyclic, hd.rank⟩

theorem D1CaseTwoDataU.inf_X0_facts (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hd : D1CaseTwoDataU p P M H R Rbar)
    {L : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hL : IsComponentOf L ⊤)
    (hLX : ¬ L ≤ d1X0 p M H) :
    Group.IsSolvable ((d1X0 p M H).comap L.subtype) ∧
      ∀ k : L, (∀ y ∈ (d1X0 p M H).comap L.subtype, k * y * k⁻¹ ∈ (d1X0 p M H).comap L.subtype) →
        k ∈ (d1X0 p M H).comap L.subtype :=
  hd.toBase.inf_X0_facts (kFactCycAut_of_kFactOutCyclic hOut) hS hKL hL hLX

theorem D1CaseTwoDataU.pRank_plusCore_le_one (hd : D1CaseTwoDataU p P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 p M H) : Open.pRank p (d1PlusCore p H Kb) ≤ 1 := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  set O := primeComplementCore (G := H) p
  set C := Subgroup.centralizer (Kb : Set (H ⧸ O))
  have h1 : Open.pRank p (d1PlusCore p H Kb) = Open.pRank p C := by
    unfold d1PlusCore
    rw [← pRank_map_mk_eq_pRank_map_subtype hp O (primeComplementCore_coprime p),
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective O)]
  rw [h1]
  obtain ⟨E, hEC, hEel, hEcard⟩ := pRank_attained p hp C
  obtain ⟨n, hn⟩ := exists_conjugate_le_sylow_of_le p Rbar
    (hd.cfg.red.sylow_le_normalizer_component hKb)
    (hEC.trans (Subgroup.centralizer_le_normalizer _)) (IsPGroup.of_card hEcard)
  have hnN : (n : H ⧸ O) ∈ Subgroup.normalizer (Kb : Set (H ⧸ O)) := n.2
  have hEn : E.map (MulAut.conj (n : H ⧸ O)).toMonoidHom ≤ (Rbar : Subgroup _) ⊓ C := by
    refine le_inf hn ?_
    rintro _ ⟨e, he, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr fun k hk => ?_
    have hk' : (n : H ⧸ O)⁻¹ * k * n ∈ Kb :=
      (Subgroup.mem_normalizer_iff.mp hnN ((n : H ⧸ O)⁻¹ * k * n)).mpr
        (by simpa [mul_assoc] using hk)
    have hc := Subgroup.mem_centralizer_iff.mp (hEC he) _ hk'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * ((n : H ⧸ O) * e * (n : H ⧸ O)⁻¹)
        = (n : H ⧸ O) * (((n : H ⧸ O)⁻¹ * k * n) * e) * (n : H ⧸ O)⁻¹ := by group
      _ = (n : H ⧸ O) * (e * ((n : H ⧸ O)⁻¹ * k * n)) * (n : H ⧸ O)⁻¹ := by rw [hc]
      _ = ((n : H ⧸ O) * e * (n : H ⧸ O)⁻¹) * k := by group
  have h2 := (pRank_mono p hp hEn).trans
    (hd.cfg.red.pRank_inf_centralizer_le_one_of_not_le hKb hKX)
  rw [pRank_map_of_injective p hp _ (MulAut.conj (n : H ⧸ O)).injective] at h2
  exact (le_csSup (pRank_bddAbove p hp E) ⟨E, le_rfl, hEel, hEcard⟩).trans h2

theorem D1CaseTwoDataU.perfect_le_plusCore (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoDataU p P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 p M H) {U : Subgroup G} (hU : U ≤ H ⊓ M) (hUp : ⁅U, U⁆ = U) :
    U ≤ d1PlusCore p H Kb := by
  have hp := hd.cfg.red.prime
  have : Fact p.Prime := ⟨hp⟩
  have hred := hd.cfg.red
  set π := QuotientGroup.mk' (primeComplementCore (G := H) p)
  set Ub := (U.subgroupOf H).map π with hUbdef
  have hUH : U ≤ H := hU.trans inf_le_left
  have hUb : ⁅Ub, Ub⁆ = Ub := by
    have h1 : ⁅U.subgroupOf H, U.subgroupOf H⁆ = U.subgroupOf H := by
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hUH, hUp]
    rw [hUbdef, ← Subgroup.map_commutator, h1]
  have hUbX : Ub ≤ d1X0 p M H := Subgroup.map_mono fun u hu => Subgroup.mem_subgroupOf.mpr
    (hU (Subgroup.mem_subgroupOf.mp hu))
  obtain ⟨hsolv, hself⟩ := D1CaseTwoDataU.inf_X0_facts hOut hS hKL hd hKb hKX
  obtain ⟨hsimple, hnonab, hcat, -⟩ := hred.isSimpleGroup_of_isCyclic hd.cfg.catalog hKb
    (hd.cyclic Kb hKb)
  have hZ := hred.center_eq_bot_of_isCyclic hKb (hd.cyclic Kb hKb)
  have hUbN : Ub ≤ Subgroup.normalizer (Kb : Set _) :=
    le_normalizer_of_perfect (fun L₁ L₂ L₃ h₁ h₂ h₃ h₁₂ h₁₃ h₂₃ =>
      hred.false_of_three_components h₁ h₂ h₃ h₁₂ h₁₃ h₂₃) hUb hKb
  have hUbK : Ub ≤ Kb ⊔ Subgroup.centralizer (Kb : Set _) :=
    perfect_le_sup_centralizer_of_outer (hSch Kb hsimple hnonab hcat) hUb hUbN
  obtain ⟨ρ, hρ⟩ := exists_proj hZ hUbK
  have hρX : ∀ u : Ub, ρ u ∈ (d1X0 p M H).comap Kb.subtype := by
    intro u
    apply hself
    intro y hy
    set a : H ⧸ primeComplementCore (G := H) p :=
      ((ρ u : Kb) : H ⧸ primeComplementCore (G := H) p) with ha
    set b : H ⧸ primeComplementCore (G := H) p := (u : H ⧸ primeComplementCore (G := H) p)
    have hc : a⁻¹ * b ∈ Subgroup.centralizer (Kb : Set _) := hρ u
    have hconj : a * (y : H ⧸ primeComplementCore (G := H) p) * a⁻¹ = b * y * b⁻¹ := by
      have h1 : (y : H ⧸ primeComplementCore (G := H) p) * (a⁻¹ * b) = (a⁻¹ * b) * y :=
        Subgroup.mem_centralizer_iff.mp hc (y : _) y.2
      calc a * (y : H ⧸ primeComplementCore (G := H) p) * a⁻¹
          = a * ((y : H ⧸ primeComplementCore (G := H) p) * (a⁻¹ * b)) * b⁻¹ := by group
        _ = b * y * b⁻¹ := by rw [h1]; group
    show ((ρ u * y * (ρ u)⁻¹ : Kb) : H ⧸ primeComplementCore (G := H) p) ∈ d1X0 p M H
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← ha, hconj]
    exact (d1X0 p M H).mul_mem ((d1X0 p M H).mul_mem (hUbX u.2) hy) ((d1X0 p M H).inv_mem
      (hUbX u.2))
  have hρ1 : ∀ u : Ub, ρ u = 1 := by
    have : Group.IsPerfect Ub := Subgroup.isPerfect_iff.mpr hUb
    have : Group.IsPerfect ρ.range := Group.IsPerfect.range ρ
    have hle : ρ.range ≤ (d1X0 p M H).comap Kb.subtype := by
      rintro _ ⟨u, rfl⟩
      exact hρX u
    have hsol : Group.IsSolvable ρ.range := Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective hle)
    intro u
    by_contra hu
    have : Nontrivial ρ.range := ⟨⟨⟨ρ u, u, rfl⟩, 1, fun h => hu (congrArg Subtype.val h)⟩⟩
    exact Group.IsPerfect.not_isSolvable (G := ρ.range) hsol
  have hUbC : Ub ≤ Subgroup.centralizer (Kb : Set _) := by
    intro u hu
    have := hρ ⟨u, hu⟩
    rwa [hρ1 ⟨u, hu⟩, Subgroup.coe_one, inv_one, one_mul] at this
  intro u hu
  exact Subgroup.mem_map.mpr ⟨⟨u, hUH hu⟩,
    hUbC ⟨⟨u, hUH hu⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩, rfl⟩

theorem D1CaseTwoDataU.pRank_le_one_of_perfect_barM (hOut : KFactOutCyclic) (hS : KFactSeitzCyc)
    (hKL : KFactCaseTwoLocal) (hSch : KFactCatalogSchreier)
    (hd : D1CaseTwoDataU p P M H R Rbar)
    {Kb : Subgroup (H ⧸ primeComplementCore (G := H) p)} (hKb : IsComponentOf Kb ⊤)
    (hKX : ¬ Kb ≤ d1X0 p M H) {V : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hV : V ≤ barM M (H ⊓ M)) (hVp : ⁅V, V⁆ = V) : Open.pRank p V ≤ 1 := by
  have hp := hd.cfg.red.prime
  obtain ⟨V', hV'le, hV'p, hV'bar⟩ :=
    exists_perfect_le_of_le_barM (inf_le_right : H ⊓ M ≤ M) hV hVp
  have h1 := pRank_mono p hp (hd.perfect_le_plusCore hOut hS hKL hSch hKb hKX hV'le hV'p)
  have h2 := stmtBarPRankLift hp hd.cfg.red.ne_two M V' (hV'le.trans inf_le_right)
  rw [hV'bar] at h2
  exact h2.trans (h1.trans (hd.pRank_plusCore_le_one hKb hKX))

end CFSG.LocalAnalysis.RankThreeTheoremC
