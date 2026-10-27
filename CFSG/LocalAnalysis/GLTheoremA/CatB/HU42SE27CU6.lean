module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Defs
import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.OrthBlocks
import CFSG.LocalAnalysis.GLTheoremA.CatA.Shared

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.ClassicalGroups.UnitaryFlag (commute_scalar gramSU)

abbrev pi6 : M6 →* S6 := QuotientGroup.mk' Z6

theorem ker_pi6_le_center : pi6.ker ≤ Subgroup.center M6 := by
  intro z hz
  rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at hz
  obtain ⟨c, hc⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  change (g : GL (Fin 6) F4) * (z : GL (Fin 6) F4) =
    (z : GL (Fin 6) F4) * g
  rw [← hc]
  exact (commute_scalar c (g : GL (Fin 6) F4)).eq

theorem mem_center_of_mem_Z6 {z : M6} (hz : z ∈ Z6) :
    z ∈ Subgroup.center M6 := by
  apply ker_pi6_le_center
  rw [MonoidHom.mem_ker]
  exact (QuotientGroup.eq_one_iff z).mpr hz

theorem CenD_val (s : M6) :
    CenD (s : GL (Fin 6) F4) = Subgroup.centralizer ({s} : Set M6) := by
  ext x
  rw [mem_CenD, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    apply Subtype.ext
    exact h
  · intro h
    exact congrArg Subtype.val h

theorem exists_perfect_map_of_perfect (s : M6) (sbar : S6) (hπs : pi6 s = sbar)
    {K : Subgroup S6} (hKle : K ≤ Subgroup.centralizer ({sbar} : Set S6))
    (hKperf : Group.IsPerfect ↥K) :
    ∃ J : Subgroup M6, J ≤ CenD (s : GL (Fin 6) F4) ∧ Group.IsPerfect ↥J ∧
      J.map pi6 = K := by
  classical
  have hfixα : fixSubgroup (MulAut.conj s) = CenD (s : GL (Fin 6) F4) := by
    rw [CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.fixSubgroup_conj_eq_centralizer',
      CenD_val]
  have hfixβ : fixSubgroup (MulAut.conj sbar) = Subgroup.centralizer ({sbar} : Set S6) :=
    CFSG.HardMathSupport.Dickson.Sec6.OrthBlocks.fixSubgroup_conj_eq_centralizer' sbar
  have hαβ : ∀ k : M6, pi6 ((MulAut.conj s) k) = (MulAut.conj sbar) (pi6 k) := by
    intro k
    rw [MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hπs]
  by_cases hKbot : K = ⊥
  · subst hKbot
    exact ⟨⊥, bot_le, Subgroup.isPerfect_iff.mpr (by simp), by simp⟩
  · have hKnt : Nontrivial ↥K := (Subgroup.nontrivial_iff_ne_bot K).2 hKbot
    have hKimg : K ≤ (CenD (s : GL (Fin 6) F4)).map pi6 := by
      have h := CFSG.HardMathSupport.Solomon.Coordinator.le_map_fixSubgroup_of_perfect
        pi6 ker_pi6_le_center (MulAut.conj s) (MulAut.conj sbar) hαβ
        (QuotientGroup.mk'_surjective Z6) (by rw [hfixβ]; exact hKle)
        (Subgroup.isPerfect_iff.mp hKperf)
      rwa [hfixα] at h
    let P : Subgroup M6 := CenD (s : GL (Fin 6) F4) ⊓ K.comap pi6
    have hPmap : P.map pi6 = K := by
      apply le_antisymm
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        exact hy.2
      · intro x hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hKimg hx)
        exact Subgroup.mem_map.mpr
          ⟨y, ⟨hy, by show pi6 y ∈ K; rw [hyx]; exact hx⟩, hyx⟩
    let φ : ↥P →* ↥K := (pi6.comp P.subtype).codRestrict K (fun p => p.2.2)
    have hφ : Function.Surjective φ := by
      intro k
      obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp (hKimg k.2)
      refine ⟨⟨x, ⟨hx, ?_⟩⟩, ?_⟩
      · show pi6 x ∈ K
        rw [hxπ]
        exact k.2
      · apply Subtype.ext
        exact hxπ
    obtain ⟨K', hK'map, hK'perf, -⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.i7_exists_perfect_cover φ hφ
    let J : Subgroup M6 := K'.map P.subtype
    refine ⟨J, ?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact y.2.1
    · haveI : Group.IsPerfect ↥K' := hK'perf
      exact Group.IsPerfect.map (H := K') P.subtype
    · apply le_antisymm
      · intro x hx
        obtain ⟨y, hyJ, hyx⟩ := Subgroup.mem_map.mp hx
        obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hyJ
        rw [← hyx]
        exact z.2.2
      · intro x hx
        have hmem : (⟨x, hx⟩ : ↥K) ∈ K'.map φ := by
          rw [hK'map]
          exact Subgroup.mem_top _
        obtain ⟨z, hzK', hz⟩ := Subgroup.mem_map.mp hmem
        exact Subgroup.mem_map.mpr
          ⟨P.subtype z, Subgroup.mem_map.mpr ⟨z, hzK', rfl⟩, congrArg Subtype.val hz⟩

theorem centSplitOn_S6_of (hN : U6NineFact) (hC : U6CubeFact) :
    CentSplitOn CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.S6 := by
  intro sbar hsbar
  obtain ⟨s, hs⟩ := QuotientGroup.mk'_surjective Z6 sbar
  have hsbar1 : sbar ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hsbar
    omega
  have hs3bar : sbar ^ 3 = 1 := by
    rw [← hsbar]
    exact pow_orderOf_eq_one sbar
  have hs3ker : s ^ 3 ∈ Z6 := by
    refine (QuotientGroup.eq_one_iff (s ^ 3)).mp ?_
    show pi6 (s ^ 3) = 1
    rw [map_pow, hs, hs3bar]
  obtain ⟨c, hc⟩ :=
    (hs3ker : ((s ^ 3 : M6) : GL (Fin 6) F4) ∈ StatedScalars (Fin 6) F4)
  have hcube : (s : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← Subgroup.coe_pow]
    exact hc.symm
  have hs3val : ((s ^ 3 : M6) : GL (Fin 6) F4) =
      Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [Subgroup.coe_pow]
    exact hcube
  have hBmem : (s : GL (Fin 6) F4) ∈ primeFormUnitary hF4 (idGram F4 6) := by
    have hsgram : (s : GL (Fin 6) F4) ∈ gramSU hF4 (idGram F4 6) := by
      rw [gramSU_idGram_six]
      exact s.2
    exact ((mem_gramSU_iff_unitary hF4).mp hsgram).1
  let B : primeFormUnitary hF4 (idGram F4 6) := ⟨(s : GL (Fin 6) F4), hBmem⟩
  by_cases hc1 : c = 1
  · have hs3 : s ^ 3 = 1 := by
      apply Subtype.ext
      show ((s ^ 3 : M6) : GL (Fin 6) F4) = ((1 : M6) : GL (Fin 6) F4)
      rw [hs3val, hc1, map_one]
      rfl
    have hsnotZ : s ∉ Z6 := by
      intro hsZ
      have h1 : pi6 s = 1 := (QuotientGroup.eq_one_iff s).mpr hsZ
      rw [hs] at h1
      exact hsbar1 h1
    rcases hC s hs3 hsnotZ with hall | ⟨R, hRle, hRsimple, hRnc, hRcard, hRinf,
      hRcen, hRdec, hRne⟩
    · left
      intro K hKle hKperf
      obtain ⟨J, hJle, hJperf, hJmap⟩ :=
        exists_perfect_map_of_perfect s sbar hs hKle hKperf
      have hJbot : J = ⊥ := hall J hJle (Subgroup.isPerfect_iff.mp hJperf)
      have hKbot : K = ⊥ := by rw [← hJmap, hJbot, Subgroup.map_bot]
      rw [hKbot]
      simp
    · right
      refine ⟨R.map pi6, ?_, ?_, ?_, ?_, ?_⟩
      · intro x hx
        obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hrs : r * s = s * r := by
          apply Subtype.ext
          show (r : GL (Fin 6) F4) * (s : GL (Fin 6) F4) =
            (s : GL (Fin 6) F4) * (r : GL (Fin 6) F4)
          exact mem_CenD.mp (hRle hr)
        calc pi6 r * sbar = pi6 r * pi6 s := by rw [hs]
          _ = pi6 (r * s) := (map_mul _ _ _).symm
          _ = pi6 (s * r) := by rw [hrs]
          _ = pi6 s * pi6 r := map_mul _ _ _
          _ = sbar * pi6 r := by rw [hs]
      · intro g hg
        have hgcomm : g * sbar = sbar * g :=
          Subgroup.mem_centralizer_singleton_iff.mp hg
        obtain ⟨g0, hg0⟩ := QuotientGroup.mk'_surjective Z6 g
        let z : M6 := s⁻¹ * g0 * s * g0⁻¹
        have hz1 : pi6 z = 1 := by
          have hzdef : z = s⁻¹ * g0 * s * g0⁻¹ := rfl
          calc pi6 z = (pi6 s)⁻¹ * pi6 g0 * pi6 s * (pi6 g0)⁻¹ := by
                rw [hzdef, map_mul, map_mul, map_mul, map_inv, map_inv]
            _ = sbar⁻¹ * g * sbar * g⁻¹ := by rw [hs, hg0]
            _ = sbar⁻¹ * (g * sbar) * g⁻¹ := by group
            _ = sbar⁻¹ * (sbar * g) * g⁻¹ := by rw [hgcomm]
            _ = 1 := by group
        have hzZ : z ∈ Z6 := (QuotientGroup.eq_one_iff z).mp hz1
        have hg0s : g0 * s * g0⁻¹ = s * z := by
          dsimp [z]
          group
        have hg0Cen : g0 ∈ CenD (s : GL (Fin 6) F4) := hRcen g0 z hzZ hg0s
        obtain ⟨n, z', hz'Z, r, hrR, hg0dec⟩ := hRdec g0 hg0Cen
        refine ⟨n, pi6 r, Subgroup.mem_map.mpr ⟨r, hrR, rfl⟩, ?_⟩
        have hz'1 : pi6 z' = 1 := (QuotientGroup.eq_one_iff z').mpr hz'Z
        have hdec := congrArg pi6 hg0dec
        simpa [map_mul, map_pow, hg0, hz'1, hs] using hdec
      · intro hmem
        obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp hmem
        have hz1 : pi6 (s⁻¹ * r) = 1 := by
          rw [map_mul, map_inv, hs, hr, inv_mul_cancel]
        have hzZ : s⁻¹ * r ∈ Z6 := (QuotientGroup.eq_one_iff (s⁻¹ * r)).mp hz1
        have hcomm : s * (s⁻¹ * r) = (s⁻¹ * r) * s :=
          Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hzZ) s
        have hsz : s = (s⁻¹ * r)⁻¹ * r := by
          have h1 : r = s * (s⁻¹ * r) := by group
          calc s = (s⁻¹ * r)⁻¹ * ((s⁻¹ * r) * s) := by group
            _ = (s⁻¹ * r)⁻¹ * (s * (s⁻¹ * r)) := by rw [← hcomm]
            _ = (s⁻¹ * r)⁻¹ * r := by rw [← h1]
        exact hRne (s⁻¹ * r)⁻¹ (Z6.inv_mem hzZ) r hrR hsz
      · have hZR : Subgroup.center ↥R = ⊥ :=
          TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hRnc
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_bot]
        obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp y.2
        have hcent : ∀ r' ∈ R, r * r' = r' * r := by
          intro r' hr'
          have hmem' : pi6 r' ∈ R.map pi6 := Subgroup.mem_map.mpr ⟨r', hr', rfl⟩
          have hcπ : pi6 r * pi6 r' = pi6 r' * pi6 r := by
            have h := congrArg Subtype.val
              (Subgroup.mem_center_iff.mp hy ⟨pi6 r', hmem'⟩)
            simpa [hr] using h.symm
          have hz1 : pi6 (r * r' * r⁻¹ * r'⁻¹) = 1 := by
            rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcπ]
            group
          have hzZ : r * r' * r⁻¹ * r'⁻¹ ∈ Z6 :=
            (QuotientGroup.eq_one_iff _).mp hz1
          have hzR : r * r' * r⁻¹ * r'⁻¹ ∈ R :=
            R.mul_mem (R.mul_mem (R.mul_mem hrR hr') (R.inv_mem hrR)) (R.inv_mem hr')
          have hz : r * r' * r⁻¹ * r'⁻¹ ∈ R ⊓ Z6 :=
            Subgroup.mem_inf.mpr ⟨hzR, hzZ⟩
          rw [hRinf, Subgroup.mem_bot] at hz
          calc r * r' = (r * r' * r⁻¹ * r'⁻¹) * (r' * r) := by group
            _ = 1 * (r' * r) := by rw [hz]
            _ = r' * r := one_mul _
        have hrcenter : (⟨r, hrR⟩ : ↥R) ∈ Subgroup.center ↥R := by
          rw [Subgroup.mem_center_iff]
          intro r'
          apply Subtype.ext
          show r' * r = r * r'
          exact (hcent r'.1 r'.2).symm
        have hr1 : r = 1 := by
          have hbot : (⟨r, hrR⟩ : ↥R) ∈ (⊥ : Subgroup ↥R) := by
            rw [← hZR]
            exact hrcenter
          exact congrArg Subtype.val (Subgroup.mem_bot.mp hbot)
        apply Subtype.ext
        rw [← hr, hr1, map_one]
        rfl
      · let f : ↥R → ↥(R.map pi6) := fun x =>
          ⟨pi6 x.1, Subgroup.mem_map.mpr ⟨x.1, x.2, rfl⟩⟩
        have hf : Function.Bijective f := by
          constructor
          · intro x y hxy
            have hxy' : pi6 x.1 = pi6 y.1 := congrArg Subtype.val hxy
            have hz1 : pi6 (x.1 * y.1⁻¹) = 1 := by
              rw [map_mul, map_inv, hxy', mul_inv_cancel]
            have hzZ : x.1 * y.1⁻¹ ∈ Z6 :=
              (QuotientGroup.eq_one_iff _).mp hz1
            have hzR : x.1 * y.1⁻¹ ∈ R := R.mul_mem x.2 (R.inv_mem y.2)
            have hz : x.1 * y.1⁻¹ ∈ R ⊓ Z6 := Subgroup.mem_inf.mpr ⟨hzR, hzZ⟩
            rw [hRinf, Subgroup.mem_bot] at hz
            apply Subtype.ext
            calc x.1 = (x.1 * y.1⁻¹) * y.1 := by group
              _ = 1 * y.1 := by rw [hz]
              _ = y.1 := one_mul _
          · intro y
            obtain ⟨r, hrR, hr⟩ := Subgroup.mem_map.mp y.2
            exact ⟨⟨r, hrR⟩, Subtype.ext hr⟩
        have hcard : Nat.card ↥(R.map pi6) = Nat.card ↥R :=
          (Nat.card_congr (Equiv.ofBijective f hf)).symm
        rw [hcard, hRcard]
  · left
    intro K hKle hKperf
    obtain ⟨J, hJle, hJperf, hJmap⟩ :=
      exists_perfect_map_of_perfect s sbar hs hKle hKperf
    have hJdvd : Nat.card ↥J ∣ 504 :=
      hN B c hc1 hcube J hJle (Subgroup.isPerfect_iff.mp hJperf)
    have hKdvd : Nat.card ↥K ∣ Nat.card ↥J := by
      rw [← hJmap]
      exact Subgroup.card_map_dvd J pi6
    exact fun h5 => by
      have h504 : 5 ∣ (504 : ℕ) := (dvd_trans h5 hKdvd).trans hJdvd
      norm_num at h504

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
