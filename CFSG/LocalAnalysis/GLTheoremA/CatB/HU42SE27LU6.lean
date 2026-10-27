module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27LDefs
public import CFSG.LocalAnalysis.GLTheoremA.PartI.LevelLieU6Aut
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Nine
import CFSG.LocalAnalysis.GLTheoremA.CatB.HU42SE27CU6Cube
import CFSG.LocalAnalysis.GLTheoremA.CatA.KU6CentPGU
import CFSG.GroupTheory.CentralExtensionPGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

open CFSG.Open CFSG.Fischer CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.LocalAnalysis.GLTheoremA.LevelLieU6
open CFSG.ClassicalGroups.UnitaryFlag (commute_scalar gramSU)

private theorem Z6_cube {z : M6} (hz : z ∈ Z6) : z ^ 3 = 1 := by
  obtain ⟨c, hc⟩ := CFSG.LocalAnalysis.GLTheoremA.KU6Cent.mem_Z6.mp hz
  apply Subtype.ext
  show ((z ^ 3 : M6) : GL (Fin 6) F4) = ((1 : M6) : GL (Fin 6) F4)
  rw [Subgroup.coe_pow, ← hc, ← map_pow,
    CFSG.LocalAnalysis.GLTheoremA.KU6Cent.units_cube c, map_one]
  rfl

theorem invCentOn_S6_of (hSU : SUInvCent 6) :
    InvCentOn CFSG.LocalAnalysis.GLTheoremA.LevelLieU6.S6 := by
  intro E U₀ s hEel hEcard hU hUne hEnorm hsE hs1 hNo
  classical
  obtain ⟨ŝ, hŝ⟩ := QuotientGroup.mk'_surjective Z6 s
  have hs3 : s ^ 3 = 1 := hEel.2 s hsE
  have hs3ker : ŝ ^ 3 ∈ Z6 := by
    refine (QuotientGroup.eq_one_iff (ŝ ^ 3)).mp ?_
    show pi6 (ŝ ^ 3) = 1
    rw [map_pow, hŝ, hs3]
  have hsnotZ : ŝ ∉ Z6 := by
    intro hZ
    have h1 : pi6 ŝ = 1 := (QuotientGroup.eq_one_iff ŝ).mpr hZ
    rw [hŝ] at h1
    exact hs1 h1
  have hBmem : (ŝ : GL (Fin 6) F4) ∈ primeFormUnitary hF4 (idGram F4 6) := by
    have hsgram : (ŝ : GL (Fin 6) F4) ∈ gramSU hF4 (idGram F4 6) := by
      rw [gramSU_idGram_six]
      exact ŝ.2
    exact ((mem_gramSU_iff_unitary hF4).mp hsgram).1
  let B : primeFormUnitary hF4 (idGram F4 6) := ⟨(ŝ : GL (Fin 6) F4), hBmem⟩
  obtain ⟨c, hc⟩ :=
    (hs3ker : ((ŝ ^ 3 : M6) : GL (Fin 6) F4) ∈ StatedScalars (Fin 6) F4)
  have hcube : (ŝ : GL (Fin 6) F4) ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 6) c := by
    rw [← Subgroup.coe_pow]
    exact hc.symm
  obtain ⟨K, hKle, hKperf, h5K⟩ :
      ∃ K : Subgroup S6, K ≤ Subgroup.centralizer ({s} : Set S6) ∧ Group.IsPerfect ↥K ∧
        5 ∣ Nat.card ↥K := by
    by_contra h
    exact hNo (fun K hKle hKp h5 => h ⟨K, hKle, hKp, h5⟩)
  have hc1 : c = 1 := by
    by_contra hc1
    obtain ⟨J, hJle, hJperf, hJmap⟩ := exists_perfect_map_of_perfect ŝ s hŝ hKle hKperf
    have hJdvd : Nat.card ↥J ∣ 504 :=
      u6NineFact_holds B c hc1 hcube J hJle (Subgroup.isPerfect_iff.mp hJperf)
    have hKdvd : Nat.card ↥K ∣ Nat.card ↥J := by
      rw [← hJmap]
      exact Subgroup.card_map_dvd J pi6
    have h504 : 5 ∣ (504 : ℕ) := (dvd_trans h5K hKdvd).trans hJdvd
    norm_num at h504
  have hs3M : ŝ ^ 3 = 1 := by
    apply Subtype.ext
    show ((ŝ ^ 3 : M6) : GL (Fin 6) F4) = ((1 : M6) : GL (Fin 6) F4)
    rw [Subgroup.coe_pow, hcube, hc1, map_one]
    rfl
  rcases u6CubeFact_holds ŝ hs3M hsnotZ with hall | ⟨R, hRle, hRsimple, hRnc, hRcard, hRinf,
    hRcen, hRdec, hRne⟩
  · exfalso
    obtain ⟨J, hJle, hJperf, hJmap⟩ := exists_perfect_map_of_perfect ŝ s hŝ hKle hKperf
    have hJbot : J = ⊥ := hall J hJle (Subgroup.isPerfect_iff.mp hJperf)
    have hKbot : K = ⊥ := by rw [← hJmap, hJbot, Subgroup.map_bot]
    rw [hKbot] at h5K
    simp at h5K
  let Ê : Subgroup M6 := E.comap pi6
  have hcommR : ∀ r ∈ R, Commute r ŝ := by
    intro r hr
    have h := hRle hr
    rw [CenD_val] at h
    exact Subgroup.mem_centralizer_singleton_iff.mp h
  have hdec : ∀ ê ∈ Ê, ∃ n : ℕ, ∃ z ∈ Z6, ∃ r ∈ R, ê = ŝ ^ n * z * r := by
    intro ê hê
    have heE : pi6 ê ∈ E := hê
    have hcommE : pi6 ê * s = s * pi6 ê :=
      congrArg Subtype.val (hEel.1.is_comm.comm ⟨pi6 ê, heE⟩ ⟨s, hsE⟩)
    have hzZ : ŝ⁻¹ * (ê * ŝ * ê⁻¹) ∈ Z6 := by
      rw [← QuotientGroup.eq_one_iff]
      show pi6 (ŝ⁻¹ * (ê * ŝ * ê⁻¹)) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hŝ, hcommE]
      group
    have hcen : ê ∈ CenD (ŝ : GL (Fin 6) F4) :=
      hRcen ê _ hzZ (by group)
    obtain ⟨n, z, hz, r, hr, hd⟩ := hRdec ê hcen
    exact ⟨n, z, hz, r, hr, hd⟩
  have hpi_r : ∀ (n : ℕ) (z r ê : M6), z ∈ Z6 → ê = ŝ ^ n * z * r →
      pi6 r = (s ^ n)⁻¹ * pi6 ê := by
    intro n z r ê hz hd
    have hzpi : pi6 z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    have hrw : r = (ŝ ^ n * z)⁻¹ * ê := by rw [hd]; group
    rw [hrw, map_mul, map_inv, map_mul, map_pow, hŝ, hzpi, mul_one]
  have hÊab : ∀ a ∈ Ê, ∀ b ∈ Ê, a * b = b * a := by
    intro a ha b hb
    obtain ⟨n, z, hz, r, hr, hd⟩ := hdec a ha
    obtain ⟨m, w, hw, t, ht, hd2⟩ := hdec b hb
    have hsub_a : pi6 a ∈ E := ha
    have hsub_b : pi6 b ∈ E := hb
    have hŝz : Commute ŝ z := Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hz) ŝ
    have hŝw : Commute ŝ w := Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hw) ŝ
    have hzw : Commute z w := (Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hz) w).symm
    have hss : Commute (ŝ ^ n) (ŝ ^ m) := (Commute.refl ŝ).pow_pow n m
    have h1 : Commute (ŝ ^ n) (ŝ ^ m * w) := hss.mul_right (hŝw.pow_left n)
    have h2 : Commute z (ŝ ^ m * w) := (hŝz.symm.pow_right m).mul_right hzw
    have haa : Commute (ŝ ^ n * z) (ŝ ^ m * w) := h1.mul_left h2
    have hŝm_r : Commute (ŝ ^ m) r := (hcommR r hr).symm.pow_left m
    have hw_r : Commute w r := (Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hw) r).symm
    have hŝn_t : Commute (ŝ ^ n) t := (hcommR t ht).symm.pow_left n
    have hz_t : Commute z t := (Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hz) t).symm
    have har1 : Commute (ŝ ^ m * w) r := hŝm_r.mul_left hw_r
    have har2 : Commute (ŝ ^ n * z) t := hŝn_t.mul_left hz_t
    have hrt : r * t = t * r := by
      have hmemR : r * t * r⁻¹ * t⁻¹ ∈ R :=
        R.mul_mem (R.mul_mem (R.mul_mem hr ht) (R.inv_mem hr)) (R.inv_mem ht)
      have hpi1 : pi6 r = (s ^ n)⁻¹ * pi6 a := hpi_r n z r a hz hd
      have hpi2 : pi6 t = (s ^ m)⁻¹ * pi6 b := hpi_r m w t b hw hd2
      have hmema : pi6 r ∈ E := by
        rw [hpi1]
        exact E.mul_mem (E.inv_mem (E.pow_mem hsE n)) hsub_a
      have hmemb : pi6 t ∈ E := by
        rw [hpi2]
        exact E.mul_mem (E.inv_mem (E.pow_mem hsE m)) hsub_b
      have hcommpi : pi6 r * pi6 t = pi6 t * pi6 r :=
        congrArg Subtype.val (hEel.1.is_comm.comm ⟨pi6 r, hmema⟩ ⟨pi6 t, hmemb⟩)
      have hpiz : pi6 (r * t * r⁻¹ * t⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcommpi]
        group
      have hmemZ : r * t * r⁻¹ * t⁻¹ ∈ Z6 := (QuotientGroup.eq_one_iff _).mp hpiz
      have hbot : r * t * r⁻¹ * t⁻¹ ∈ R ⊓ Z6 := Subgroup.mem_inf.mpr ⟨hmemR, hmemZ⟩
      rw [hRinf, Subgroup.mem_bot] at hbot
      calc r * t = (r * t * r⁻¹ * t⁻¹) * (t * r) := by group
        _ = 1 * (t * r) := by rw [hbot]
        _ = t * r := one_mul _
    calc a * b = (ŝ ^ n * z * r) * (ŝ ^ m * w * t) := by rw [hd, hd2]
      _ = (ŝ ^ n * z) * (r * (ŝ ^ m * w)) * t := by group
      _ = (ŝ ^ n * z) * ((ŝ ^ m * w) * r) * t := by rw [har1.eq]
      _ = ((ŝ ^ n * z) * (ŝ ^ m * w)) * (r * t) := by group
      _ = ((ŝ ^ m * w) * (ŝ ^ n * z)) * (t * r) := by rw [haa.eq, hrt]
      _ = (ŝ ^ m * w) * ((ŝ ^ n * z) * t) * r := by group
      _ = (ŝ ^ m * w) * (t * (ŝ ^ n * z)) * r := by rw [har2.eq]
      _ = (ŝ ^ m * w * t) * (ŝ ^ n * z * r) := by group
      _ = b * a := by rw [hd2, hd]
  have hÊ3 : ∀ e ∈ Ê, e ^ 3 = 1 := by
    intro e he
    obtain ⟨n, z, hz, r, hr, hd⟩ := hdec e he
    have heE : pi6 e ∈ E := he
    have hpi1 : pi6 r = (s ^ n)⁻¹ * pi6 e := hpi_r n z r e hz hd
    have hr3 : r ^ 3 = 1 := by
      have hmemR : r ^ 3 ∈ R := R.pow_mem hr 3
      have hmemZ : r ^ 3 ∈ Z6 := by
        rw [← QuotientGroup.eq_one_iff (N := Z6)]
        show pi6 (r ^ 3) = 1
        rw [map_pow, hpi1]
        exact hEel.2 _ (E.mul_mem (E.inv_mem (E.pow_mem hsE n)) heE)
      have hbot : r ^ 3 ∈ R ⊓ Z6 := Subgroup.mem_inf.mpr ⟨hmemR, hmemZ⟩
      rw [hRinf, Subgroup.mem_bot] at hbot
      exact hbot
    have hŝz0 : Commute ŝ z := Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hz) ŝ
    have hŝz : Commute (ŝ ^ n) z := hŝz0.pow_left n
    have hŝr : Commute (ŝ ^ n) r := (hcommR r hr).symm.pow_left n
    have hzr : Commute z r := (Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hz) r).symm
    have hŝn3 : (ŝ ^ n) ^ 3 = 1 := by
      rw [← pow_mul, show n * 3 = 3 * n from Nat.mul_comm n 3, pow_mul, hs3M, one_pow]
    have hz3 : z ^ 3 = 1 := Z6_cube hz
    calc e ^ 3 = (ŝ ^ n * z * r) ^ 3 := by rw [hd]
      _ = ((ŝ ^ n * z) ^ 3) * r ^ 3 := (hŝr.mul_left hzr).mul_pow 3
      _ = ((ŝ ^ n) ^ 3 * z ^ 3) * r ^ 3 := by rw [hŝz.mul_pow 3]
      _ = 1 := by rw [hŝn3, hz3, hr3]; group
  let Û : Subgroup M6 := U₀.comap pi6
  let φ : ↥Û →* ↥U₀ := (pi6.comp Û.subtype).codRestrict U₀ (fun x => x.2)
  have hφapply : ∀ x : ↥Û, ((φ x : ↥U₀) : S6) = pi6 (x : M6) := fun x => rfl
  have hφsurj : Function.Surjective φ := by
    intro u
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z6 (u : S6)
    refine ⟨⟨x, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hx]; exact u.2
    · apply Subtype.ext
      exact hx
  have hφker_center : φ.ker ≤ Subgroup.center ↥Û := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    change (y : M6) * (x : M6) = (x : M6) * (y : M6)
    have hxZ : (x : M6) ∈ Z6 := by
      have h1 : pi6 (x : M6) = 1 := by
        have h := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
        simpa [hφapply] using h
      exact (QuotientGroup.eq_one_iff (x : M6)).mp h1
    exact Subgroup.mem_center_iff.mp (mem_center_of_mem_Z6 hxZ) (y : M6)
  haveI : Group.IsNilpotent ↥U₀ := hU.isNilpotent
  haveI : Group.IsNilpotent ↥Û := Subgroup.isNilpotent_of_ker_le_center φ hφker_center
  obtain ⟨Q : Sylow 2 ↥Û⟩ := (inferInstance : Nonempty (Sylow 2 ↥Û))
  have hQne : (Q : Subgroup ↥Û) ≠ ⊥ := by
    have h2U0 : 2 ∣ Nat.card ↥U₀ := by
      obtain ⟨k, hkpos, hk⟩ :=
        hU.nontrivial_iff_card.mp ((Subgroup.nontrivial_iff_ne_bot U₀).mpr hUne)
      rw [hk]
      simpa using Nat.pow_dvd_pow 2 hkpos
    have h2U : 2 ∣ Nat.card ↥Û :=
      dvd_trans h2U0 (Subgroup.card_dvd_of_surjective (f := φ) hφsurj)
    exact Sylow.ne_bot_of_dvd_card Q h2U
  let P₂ : Subgroup M6 := (Q : Subgroup ↥Û).map Û.subtype
  have hP2p : IsPGroup 2 P₂ := Q.isPGroup'.map Û.subtype
  have hP2ne : P₂ ≠ ⊥ := by
    intro hbot
    exact hQne ((Subgroup.map_eq_bot_iff_of_injective (f := Û.subtype)
      (H := (Q : Subgroup ↥Û)) Subtype.coe_injective).mp hbot)
  have hEnormÛ : Ê ≤ Subgroup.normalizer (Û : Set M6) := by
    rw [Subgroup.le_normalizer_iff]
    intro ê hê x hx
    rw [Subgroup.mem_comap] at hx ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.le_normalizer_iff.mp hEnorm) (pi6 ê) hê (pi6 x) hx
  have hEnormP : Ê ≤ Subgroup.normalizer (P₂ : Set M6) := by
    rw [Subgroup.le_normalizer_iff]
    intro ê hê p hp
    obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
    have hmemÛ : ê * (q : M6) * ê⁻¹ ∈ Û :=
      (Subgroup.le_normalizer_iff.mp hEnormÛ) ê hê (q : M6) q.2
    have hQnormal : (Q : Subgroup ↥Û).Normal := inferInstance
    obtain ⟨k, hk⟩ := Q.isPGroup' (⟨q, hq⟩ : ↥(Q : Subgroup ↥Û))
    have hqpow : (q : M6) ^ 2 ^ k = 1 := by
      have h := congrArg (fun x : ↥(Q : Subgroup ↥Û) => (x : M6)) hk
      simpa using h
    have hy2 : (⟨ê * (q : M6) * ê⁻¹, hmemÛ⟩ : ↥Û) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      show (ê * (q : M6) * ê⁻¹) ^ 2 ^ k = 1
      rw [conj_pow, hqpow]
      simp
    have hyQ : (⟨ê * (q : M6) * ê⁻¹, hmemÛ⟩ : ↥Û) ∈ Q :=
      CFSG.GroupTheory.mem_sylow_of_pow_eq_one hQnormal hy2
    exact Subgroup.mem_map.mpr ⟨_, hyQ, rfl⟩
  obtain ⟨zh, hzh2, hzhne, hzhcomm⟩ := hSU Ê P₂ hP2p hP2ne hEnormP hÊab hÊ3
  refine ⟨pi6 zh, ?_, ?_, ?_⟩
  · rw [← map_pow, hzh2, map_one]
  · intro h1
    have hZ : zh ∈ Z6 := (QuotientGroup.eq_one_iff zh).mp h1
    have h3 : zh ^ 3 = 1 := Z6_cube hZ
    have hz1 : zh = 1 := by
      have hpow : zh ^ 3 = zh ^ 2 * zh := by simpa using pow_succ zh 2
      have h := h3
      rw [hpow, hzh2, one_mul] at h
      exact h
    exact hzhne hz1
  · intro e he
    obtain ⟨ê, rfl⟩ := QuotientGroup.mk'_surjective Z6 e
    have hêÊ : ê ∈ Ê := by
      rw [Subgroup.mem_comap]
      exact he
    rw [← map_mul, ← map_mul, hzhcomm ê hêÊ]

end CFSG.LocalAnalysis.GLTheoremA.CatB.U42Cat

end
