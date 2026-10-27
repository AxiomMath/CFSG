module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2UnitaryCTModel
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2RowUnitaryCover
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindCTUnitaryMain

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup Matrix CFSG.Blueprint CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
open CFSG.LieType.BorelTits (unitaryInvolution unitaryInvolution_involutive)
open CFSG.LieType.CurtisTits (rankOne levi)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)

section Param

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] {N : ℕ}
  {F : Type} [Field F]

structure NsUniParam (ε : ℕ) (hε : ε ≤ 1) (σ : F ≃+* F) (ι : K →+* F)
    (hι : ∀ c, σ (ι c) = ι c) (e : L ≃* StatedSp N K) (k : Fin N) where
  Φ : ctuBlock σ ε ({k} : Finset (Fin N)) →* G
  ker_le : Φ.ker ≤ center (ctuBlock σ ε ({k} : Finset (Fin N)))
  range_eq : Φ.range = centralizerPerfectCore (modelToG e (nsTorusSp K k))
  N1 : ∀ (y : StatedSp N K) (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ),
    Φ ⟨ctuEmbed ε hε σ ι hι y, ctuEmbed_mem_ctuBlock_iff.2 hy⟩ = ((e.symm y : L) : G)

variable {ε : ℕ} {hε : ε ≤ 1} {σ : F ≃+* F} {ι : K →+* F} {hι : ∀ c, σ (ι c) = ι c}
  {e : L ≃* StatedSp N K}

@[expose] def NsUniParamAgree (P : ∀ k : Fin N, NsUniParam ε hε σ ι hι e k) : Prop :=
  ∀ (k l : Fin N) (x : SU σ (2 * N + ε)) (hx : x ∈ ctuBlock σ ε ({k} : Finset (Fin N)))
    (hx' : x ∈ ctuBlock σ ε ({l} : Finset (Fin N))), (P k).Φ ⟨x, hx⟩ = (P l).Φ ⟨x, hx'⟩

theorem NsUniParam.N1' {k : Fin N} (P : NsUniParam ε hε σ ι hι e k) {y : StatedSp N K}
    (hy : y ∈ spBlock K ({k} : Finset (Fin N))ᶜ) (x : ctuBlock σ ε ({k} : Finset (Fin N)))
    (hx : (x : SU σ (2 * N + ε)) = ctuEmbed ε hε σ ι hι y) : P.Φ x = ((e.symm y : L) : G) := by
  rw [← P.N1 y hy]
  congr 1
  exact Subtype.ext hx

end Param

section Recognition

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] {N ε : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {hε : ε ≤ 1}
  {ι : K →+* F} {hι : ∀ c, unitaryInvolution F 2 1 (ι c) = ι c} {e : L ≃* StatedSp N K}

theorem exists_ct_nsUniRow_of_agree (hN : 5 ≤ N) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin N, NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P) :
    ∃ ψ : SU (unitaryInvolution F 2 1) (2 * N + ε) →* G, ψ.range = nsGlobal e ∧
      ψ.ker ≤ center (SU (unitaryInvolution F 2 1) (2 * N + ε)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn3 : 3 ≤ 2 * N + ε := by omega
  have hnq : (2 * N + ε, 2 ^ 1) ≠ (3, 2) := fun h => by
    have := (Prod.mk.inj h).1
    omega
  set σ := unitaryInvolution F 2 1 with hσdef
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  set D := rootDatum hF (2 * N + ε) with hD
  have hdiv : (2 * N + ε) / 2 = N := by omega
  have hrankN : D.rank = N := hdiv
  choose kJ hkJ using fun J : {J : Finset (Fin D.rank) // J.card ≤ 2} =>
    exists_plane_off_ctu (N := N) hN J.1 J.2
  have hKle : ∀ J : {J : Finset (Fin D.rank) // J.card ≤ 2},
      D.leviAmalgam J ≤ ctuBlock σ ε ({kJ J} : Finset (Fin N)) :=
    fun J => levi_le_ctuBlock hε (hkJ J)
  set φ : ∀ J, D.leviAmalgam J →* G := fun J => (P (kJ J)).Φ.comp (Subgroup.inclusion (hKle J))
    with hφ
  have hφapp : ∀ J (x : D.leviAmalgam J), φ J x = (P (kJ J)).Φ ⟨x, hKle J x.2⟩ :=
    fun _ _ => rfl
  have hcomp : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ := by
    intro I J _ x y hxy
    rw [hφapp, hφapp]
    have hy' : (x : SU σ (2 * N + ε)) ∈ ctuBlock σ ε ({kJ J} : Finset (Fin N)) := by
      rw [hxy]
      exact hKle J y.2
    rw [hagree (kJ I) (kJ J) _ (hKle I x.2) hy']
    congr 2
  have hpiece : ∀ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (y : StatedSp N K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ D.leviAmalgam J),
      φ J ⟨_, hy⟩ = ((e.symm y : L) : G) := by
    intro J y hy
    rw [hφapp]
    exact (P (kJ J)).N1' (ctuEmbed_mem_ctuBlock_iff.1 (hKle J hy)) _ rfl
  set G₀ : Subgroup G := ⨆ J, (φ J).range with hG₀
  have hle : ∀ J x, φ J x ∈ G₀ := fun J x => le_iSup (fun J => (φ J).range) J ⟨x, rfl⟩
  set φ' : ∀ J, D.leviAmalgam J →* G₀ := fun J => (φ J).codRestrict G₀ (hle J) with hφ'
  have hcomp' : CFSG.LieType.CurtisTits.IsCompatible D.leviAmalgam φ' :=
    fun I J hIJ x y hxy => Subtype.ext (hcomp I J hIJ x y hxy)
  have hgen' : ⨆ J, (φ' J).range = ⊤ := by
    apply Subgroup.map_injective G₀.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    refine (iSup_congr fun J => ?_).trans hG₀.symm
    rw [← MonoidHom.range_comp]
    rfl
  have hrank : ∀ (j : Fin D.rank) (y : StatedSp N K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j),
      ∃ (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (hJ : ctuEmbed ε hε σ ι hι y ∈
        D.leviAmalgam J), φ J ⟨_, hJ⟩ = ((e.symm y : L) : G) := by
    intro j y hy
    set J : {J : Finset (Fin D.rank) // J.card ≤ 2} := ⟨{j}, by simp⟩ with hJ
    have hxJ : ctuEmbed ε hε σ ι hι y ∈ D.leviAmalgam J :=
      CFSG.LieType.CurtisTits.rankOne_le_levi _ (Finset.mem_singleton_self j) hy
    exact ⟨J, hxJ, hpiece J y hxJ⟩
  have hjl : (N - 1 : ℕ) < D.rank := by change N - 1 < (2 * N + ε) / 2; omega
  have hnt : ∃ J, ∃ x, φ' J x ≠ 1 := by
    have hlast : ¬((⟨N - 1, hjl⟩ : Fin D.rank).val + 1 < (2 * N + ε) / 2) := by
      change ¬(N - 1 + 1 < (2 * N + ε) / 2)
      omega
    obtain ⟨J, hJ, hφJ⟩ := hrank ⟨N - 1, hjl⟩ _
      (ctuEmbed_nsElt_mem_rankOne (hε := hε) (ι := ι) (hι := hι) hσ hlast)
    refine ⟨J, ⟨_, hJ⟩, fun h => ?_⟩
    have h1 : φ J ⟨_, hJ⟩ = 1 := congrArg Subtype.val h
    rw [hφJ] at h1
    have h2 : e.symm (nsElt (K := K) ⟨(⟨N - 1, hjl⟩ : Fin D.rank).val, by omega⟩) = 1 :=
      Subtype.ext h1
    rw [MulEquiv.map_eq_one_iff] at h2
    exact nsElt_ne_one _ h2
  have hadm : StatedLieAdmissible .PSU (2 * N + ε) 2 1 := ⟨Nat.prime_two, le_rfl, hn3, hnq⟩
  obtain ⟨-, -, hrec, -⟩ :=
    CFSG.LieType.CurtisTits.curtisTitsConclusion_unitary.{0} (F := F) (p := 2) (f := 1)
      (n := 2 * N + ε) hadm hF
  obtain ⟨ψ₀, hψ₀, hsurj, hker, -, -, -, -⟩ := hrec G₀ φ' hcomp' hgen' hnt
  set ψ : SU σ (2 * N + ε) →* G := G₀.subtype.comp ψ₀ with hψdef
  have hψrange : ψ.range = G₀ := by
    rw [hψdef, MonoidHom.range_comp, MonoidHom.range_eq_top.2 hsurj, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hψφ : ∀ J (x : D.leviAmalgam J), ψ x = φ J x := fun J x =>
    congrArg Subtype.val (hψ₀ J x)
  have hψker : ψ.ker ≤ center (SU σ (2 * N + ε)) := by
    intro z hz
    apply hker
    rw [MonoidHom.mem_ker] at hz ⊢
    exact G₀.subtype_injective (by rw [map_one]; exact hz)
  have hG₀le : G₀ ≤ nsGlobal e := by
    refine iSup_le fun J => ?_
    rintro _ ⟨x, rfl⟩
    have h1 : φ J x ∈ (P (kJ J)).Φ.range := ⟨_, (hφapp J x).symm⟩
    rw [(P (kJ J)).range_eq] at h1
    rw [nsGlobal_def]
    exact le_iSup (fun i : Fin N => centralizerPerfectCore (modelToG e (nsTorusSp K i))) _ h1
  have hrankψ : ∀ (j : Fin D.rank) (y : StatedSp N K)
      (hy : ctuEmbed ε hε σ ι hι y ∈ rankOne D.rootGroup j),
      ψ (ctuEmbed ε hε σ ι hι y) = ((e.symm y : L) : G) := by
    intro j y hy
    obtain ⟨J, hJ, hφJ⟩ := hrank j y hy
    rw [← hφJ]
    exact hψφ J ⟨_, hJ⟩
  have hns : ∀ k : Fin N, ψ (ctuEmbed ε hε σ ι hι (nsElt k)) = ((e.symm (nsElt k) : L) : G) := by
    refine eq_nsElt_of_eq_last_of_eq_swap (ψ.comp (ctuEmbed ε hε σ ι hι))
      (L.subtype.comp e.symm.toMonoidHom) (fun k hk => ?_) (fun j hj => ?_)
    · have hkr : k.val < D.rank := by omega
      have hlast : ¬((⟨k.val, hkr⟩ : Fin D.rank).val + 1 < (2 * N + ε) / 2) := by
        change ¬(k.val + 1 < (2 * N + ε) / 2)
        omega
      have hmem : ctuEmbed ε hε σ ι hι (nsElt k) ∈ rankOne D.rootGroup ⟨k.val, hkr⟩ :=
        ctuEmbed_nsElt_mem_rankOne (hε := hε) (ι := ι) (hι := hι) hσ hlast
      exact hrankψ _ _ hmem
    · have hjr : j.val < D.rank := by omega
      have hjs : (⟨j.val, hjr⟩ : Fin D.rank).val + 1 < (2 * N + ε) / 2 := by
        change j.val + 1 < (2 * N + ε) / 2
        omega
      have hmem : ctuEmbed ε hε σ ι hι (permSp K (Equiv.swap j ⟨j.val + 1, hj⟩)) ∈
          rankOne D.rootGroup ⟨j.val, hjr⟩ :=
        ctuEmbed_permSp_swap_mem_rankOne (hε := hε) (ι := ι) (hι := hι) hσ hjs
      exact hrankψ _ _ hmem
  have hEk : ∀ k : Fin N, centralizerPerfectCore (modelToG e (nsTorusSp K k)) ≤ G₀ := by
    intro k
    set B := ctuBlock σ ε ({k} : Finset (Fin N)) with hB
    set A := perfectCore B with hAdef
    have hAB : A ≤ B := CFSG.Quasithin.perfectCore_le B
    have hk' : k ∈ ({k} : Finset (Fin N)) := Finset.mem_singleton_self k
    have hnsk : nsElt (K := K) k ∈ spBlock K ({k} : Finset (Fin N)) := by
      rw [spBlock_singleton]
      exact nsTorusSp_le_longRootSp2 k (mem_zpowers _)
    have hA1 : A.map ψ ≤ centralizerPerfectCore (modelToG e (nsTorusSp K k)) := by
      refine CFSG.Quasithin.le_perfectCore_of_perfect ?_ ?_
      · rw [nsTorusSp, centralizer_modelToG_zpowers]
        rintro _ ⟨a, ha, rfl⟩
        rw [mem_centralizer_singleton_iff, ← hns k, ← map_mul, ← map_mul]
        congr 1
        exact commute_ctuBlock_ctuEmbed (hAB ha) hnsk
      · rw [← map_commutator, CFSG.Quasithin.perfectCore_perfect]
    have hcardE : Nat.card (centralizerPerfectCore (modelToG e (nsTorusSp K k))) ≤
        Nat.card (A.map ψ) := by
      have hinj : Function.Injective (ψ.comp A.subtype) := by
        intro x y hxy
        exact Subtype.ext (injOn_ctuBlock_of_ker_le_center hF hn3 hnq hψker hk' (hAB x.2)
          (hAB y.2) hxy)
      have h1 : Nat.card (A.map ψ) = Nat.card A := by
        have h2 : A.map ψ = (ψ.comp A.subtype).range := by
          rw [MonoidHom.range_comp, range_subtype]
        rw [h2]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have hEperf : perfectCore (centralizerPerfectCore (modelToG e (nsTorusSp K k))) =
          centralizerPerfectCore (modelToG e (nsTorusSp K k)) :=
        CFSG.Quasithin.perfectCore_eq_self_of_perfect
          (F4Pilot.commutator_centralizerPerfectCore _)
      have h3 : centralizerPerfectCore (modelToG e (nsTorusSp K k)) =
          (perfectCore (⊤ : Subgroup B)).map (P k).Φ := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, (P k).range_eq, hEperf]
      have h4 : (perfectCore (⊤ : Subgroup B)).map B.subtype = A := by
        rw [CFSG.Quasithin.map_perfectCore, ← MonoidHom.range_eq_map, range_subtype]
      rw [h1, h3, ← h4, Subgroup.card_map_of_injective B.subtype_injective]
      exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)
    have heq := Subgroup.eq_of_le_of_card_ge hA1 hcardE
    rw [← heq, ← hψrange]
    rintro _ ⟨a, -, rfl⟩
    exact ⟨a, rfl⟩
  have hG₀eq : G₀ = nsGlobal e := le_antisymm hG₀le (by
    rw [nsGlobal_def]
    exact iSup_le hEk)
  exact ⟨ψ, hψrange.trans hG₀eq, hψker⟩

theorem nsUnitaryCover_of_nsUniParamAgree (hN : 5 ≤ N) (hF : Nat.card F = (2 ^ 1) ^ 2)
    (P : ∀ k : Fin N, NsUniParam ε hε (unitaryInvolution F 2 1) ι hι e k)
    (hagree : NsUniParamAgree P) : NsUnitaryCover e (2 * N + ε) := by
  obtain ⟨ψ, hψr, hψk⟩ := exists_ct_nsUniRow_of_agree hN hF P hagree
  exact nsUnitaryCover_of_SU hF ψ hψr hψk

end Recognition

end CFSG.SeitzReduction.SymplecticPilot
