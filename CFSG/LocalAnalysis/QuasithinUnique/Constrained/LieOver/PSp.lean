module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.LieOver.Tags
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieRes
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B113LieSpCent
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aOvergroupSp
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherMaximal

public section

namespace CFSG.Quasithin.LieOver

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.QuasithinUnique.B113Lie CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.BorelTits

theorem ld_single_ne_zero {r : ℕ} {K : Type} [Field K] (j : Fin r) :
    (Pi.single (Sum.inl j) 1 : Fin r ⊕ Fin r → K) ≠ 0 := fun h => by
  have := congrFun h (Sum.inl j)
  simp at this

theorem ld_flag_eq {r : ℕ} {K : Type} [Field K] {d : ℕ} (hdr : d ≤ r) :
    SymplecticFlag.flag r K d = SymplecticFlag.isoFlag r K d := by
  rw [SymplecticFlag.flag, if_pos hdr]

theorem ld_single_mem {r : ℕ} {K : Type} [Field K] (hr : 1 ≤ r) {d : ℕ} (hd : 1 ≤ d)
    (hdr : d ≤ r) : (Pi.single (Sum.inl ⟨0, hr⟩) 1 : Fin r ⊕ Fin r → K) ∈
      SymplecticFlag.flag r K d := by
  rw [ld_flag_eq hdr]
  exact Submodule.subset_span ⟨⟨0, hr⟩, show (0 : ℕ) < d by omega, rfl⟩

theorem ld_flag_ne_bot {r : ℕ} {K : Type} [Field K] (hr : 1 ≤ r) {d : ℕ} (hd : 1 ≤ d)
    (hdr : d ≤ r) : SymplecticFlag.flag r K d ≠ ⊥ := fun h => by
  have hmem := ld_single_mem (K := K) hr hd hdr
  rw [h, Submodule.mem_bot] at hmem
  exact ld_single_ne_zero (K := K) ⟨0, hr⟩ hmem

theorem ld_spForm_β {r : ℕ} {K : Type} [Field K] (u v : Fin r ⊕ Fin r → K) :
    (spForm r K).β u v = pairedSympForm K r u v :=
  (Matrix.toBilin'_apply' _ u v).symm

theorem ld_isTI {r : ℕ} {K : Type} [Field K] {d : ℕ} (hdr : d ≤ r) :
    SymplecticFlag.IsTotallyIsotropic (pairedSympForm K r) (SymplecticFlag.flag r K d) := by
  rw [ld_flag_eq hdr]
  exact SymplecticHigher.isTotallyIsotropic_isoFlag d

theorem ld_reflTI {r : ℕ} {K : Type} [Field K] {d : ℕ} (hdr : d ≤ r) :
    (spForm r K).IsTotallyIsotropic (SymplecticFlag.flag r K d) :=
  fun x hx => (ReflForm.mem_perp (F := spForm r K)).2 fun w hw => by
    rw [ld_spForm_β]
    exact ld_isTI hdr w hw x hx

theorem ld_mem_rad_of_commute {K V H : Type} [Field K] [AddCommGroup V] [Module K V] [Group H]
    {F : ReflForm K V} {ρ : H →* Module.End K V} [CharP K 2]
    (hσ : F.σ = RingEquiv.refl K) (hρ : IsIsometric F ρ)
    (htrans : ∀ x : V, ∃ h : H, ∀ v, ρ h v = v + F.β x v • x)
    (hsiegel : ∀ x y : V, F.β x y = 0 → ∃ h : H, ∀ v, ρ h v = v + F.β x v • y + F.β y v • x)
    {W : Submodule K V} (hW : F.IsTotallyIsotropic W) {w : V} (hw : w ∈ W) (hw0 : w ≠ 0)
    {g : H} (hg : ∀ q ∈ CFSG.QuasithinUnique.B113Lie.Sp.rad F ρ W hW, g * q = q * g) :
    g ∈ CFSG.QuasithinUnique.B113Lie.Sp.rad F ρ W hW := by
  have hfix : ∀ u ∈ W, ρ g u = u := by
    intro u hu
    by_cases hu0 : u = 0
    · rw [hu0, map_zero]
    · obtain ⟨t, ht⟩ := htrans u
      exact CFSG.QuasithinUnique.B113Lie.Sp.fix_of_commute_transvection hσ hρ hu0 ht
        (hg t (CFSG.QuasithinUnique.B113Lie.Sp.transvection_mem_rad hu ht))
  refine ⟨hfix, fun v hv => ?_⟩
  obtain ⟨s, hs⟩ := hsiegel w v (hv w hw)
  have hgs : g * s = s * g :=
    hg s (CFSG.QuasithinUnique.B113Lie.Sp.siegel_mem_rad hw hv hs)
  have hmem := CFSG.QuasithinUnique.B113Lie.Sp.sub_mem_span_of_commute_siegel hρ hw0
    (hfix w hw) hs hgs
  exact (Submodule.span_singleton_le_iff_mem w W).2 hw hmem

theorem ld_charTwo_projStabilizer_flag {r : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hr : 1 ≤ r) {d : ℕ} (hd : 1 ≤ d) (hdr : d ≤ r) :
    CharTwo (SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d)) := by
  refine CFSG.QuasithinUnique.B113Lie.Sp.charTwo_projStabilizer_of_cent
    (ld_flag_ne_bot hr hd hdr) (ld_reflTI hdr) fun g hg => ?_
  exact ld_mem_rad_of_commute (F := spForm r K) (ρ := natRep (StatedSp r K)) rfl
    (isIsometric_natRep_statedSp r K) CFSG.QuasithinUnique.B113Lie.Sp.exists_transvection
    CFSG.QuasithinUnique.B113Lie.Sp.exists_siegel (ld_reflTI hdr) (ld_single_mem hr hd hdr)
    (ld_single_ne_zero ⟨0, hr⟩) hg

theorem ld_projStabilizer_one_ne_two {r : ℕ} {K : Type} [Field K] (hr : 2 ≤ r) :
    SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 1) ≠
      SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 2) := by
  intro heq
  have h1 := congrArg (Subgroup.comap (SymplecticFlag.proj r K)) heq
  rw [SymplecticHigher.comap_projStabilizer, SymplecticHigher.comap_projStabilizer] at h1
  have hne1 : SymplecticFlag.flag r K 1 ≠ ⊥ := ld_flag_ne_bot (by omega) le_rfl (by omega)
  have hne2 : SymplecticFlag.flag r K 2 ≠ ⊥ := ld_flag_ne_bot (by omega) (by omega) (by omega)
  have hti1 : SymplecticFlag.IsTotallyIsotropic (pairedSympForm K r)
      (SymplecticFlag.flag r K 1) := ld_isTI (by omega)
  have hti2 : SymplecticFlag.IsTotallyIsotropic (pairedSympForm K r)
      (SymplecticFlag.flag r K 2) := ld_isTI (by omega)
  have h2 : SymplecticFlag.flag r K 2 = SymplecticFlag.flag r K 1 :=
    SymplecticHigher.eq_of_stabilizer_le hne1 hti1 hne2 hti2 h1.le
  have h3 : Module.finrank K (SymplecticFlag.flag r K 2) =
      Module.finrank K (SymplecticFlag.flag r K 1) := by rw [h2]
  rw [SymplecticHigher.finrank_flag (i := 2) (by omega),
    SymplecticHigher.finrank_flag (i := 1) (by omega)] at h3
  omega

theorem ld_sylowFacts_sp {K : Type} [Field K] [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r)
    [IsSimpleGroup (StatedProj (StatedSp r K))] :
    SylowFacts (StatedProj (StatedSp r K)) (SymplecticFlag.projUnipotent r K) := by
  have : Finite (StatedProj (StatedSp r K)) := inferInstance
  have hr1 : 1 ≤ r := by omega
  obtain ⟨P0, hP0⟩ := SymplecticFlag.exists_sylow_projUnipotent (K := K) 2 hr1
  have hU0 : IsSylowTwoOf (SymplecticFlag.projUnipotent r K) ⊤ :=
    hP0 ▸ CFSG.QuasithinUnique.B113Lie.isSylowTwoOf_top_of_sylow P0
  have hUP : ∀ d : ℕ, 1 ≤ d → d ≤ r →
      SymplecticFlag.projUnipotent r K ≤
        SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d) := fun d _ hdr =>
    Subgroup.map_mono ((SymplecticFlag.unipotent_le_borelSubgroup (r := r) (K := K)).trans
      (SymplecticHigher.borelSubgroup_le_stabilizer_flag hdr))
  have hcov : ∀ d : ℕ, 1 ≤ d → d ≤ r →
      SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d) ⋖ ⊤ := fun d hd hdr =>
    (SymplecticHigher.isCoatom_projStabilizer_flag hd hdr).covBy_top
  have h2 : 2 ∣ Nat.card (StatedProj (StatedSp r K)) :=
    CFSG.QuasithinUnique.B113Lie.Sp.two_dvd_card_statedProj (K := K) (r := r)
      (ld_single_ne_zero (K := K) ⟨0, hr1⟩)
  have hU1 : SymplecticFlag.projUnipotent r K ≠ ⊥ := ne_bot_of_two_dvd hU0 h2
  have hX : pCoreOf 2 (⊤ : Subgroup (StatedProj (StatedSp r K))) = ⊥ :=
    pCoreOf_top_eq_bot_of_simple hU0 (hUP 1 le_rfl (by omega))
      (hcov 1 le_rfl (by omega)).lt.ne
  refine (ParabolicData.of_coatoms
    (Ps := (fun d : ℕ => SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K d)) ''
      {d | 1 ≤ d ∧ d ≤ r}) hU0 hU1 hX ?_ ?_ ?_ ?_).sylowFacts
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact ⟨hcov d hd hdn, hUP d hd hdn⟩
  · exact ⟨SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 1),
      ⟨1, ⟨le_rfl, by omega⟩, rfl⟩,
      SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K 2),
      ⟨2, ⟨by norm_num, by omega⟩, rfl⟩, ld_projStabilizer_one_ne_two (by omega)⟩
  · intro A hUA hA
    obtain ⟨i, hi1, hin, hAi⟩ :=
      (CFSG.QuasithinUnique.Setup.X7a.symplectic_unitriangular_overgroup_subflag_containment
        (r := r) (K := K)).2 A hA hUA
    exact ⟨SymplecticHigher.projStabilizer r K (SymplecticFlag.flag r K i),
      ⟨i, ⟨hi1, hin⟩, rfl⟩, hAi⟩
  · rintro P ⟨d, ⟨hd, hdn⟩, rfl⟩
    exact ld_charTwo_projStabilizer_flag (by omega) hd hdn

theorem asLieTwoPSpGe3_holds : AsLieTwoPSpGe3 := by
  intro n f X _ _ hn hS hadm hmod
  have hmc : StatedClassicalModel X .PSp n 2 f := hmod.statedClassicalModel (by decide)
  obtain ⟨-, K, hF, hFin, hcard, ⟨e⟩⟩ := hmc
  have hCh : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hadm.2.1 hcard
  have hsimp : IsSimpleGroup (StatedProj (StatedSp n K)) := e.symm.isSimpleGroup
  have hall : ∀ T : Subgroup X, IsSylowTwoOf T ⊤ → SylowFacts X T := fun T hT =>
    SylowFacts.of_mulEquiv_isSylow e (ld_sylowFacts_sp (K := K) hn) hT
  exact ⟨overgroups_of_forall_sylowFacts hall, oddAut_of_forall_sylowFacts hall⟩

end CFSG.Quasithin.LieOver
