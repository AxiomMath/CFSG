module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SignalizerNoncentral2_7Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GeneratorRank
import CFSG.LocalAnalysis.RankThreeTheoremC.PlaneTransvection
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_10
import CFSG.LocalAnalysis.RankThreeTheoremC.ObstructionElements

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.RankThree.PartOne.Planes Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace NoncentralConfig

variable {p : ℕ} {P : Sylow p G} {M D U : Subgroup G} {u : G}
  (hc : NoncentralConfig G p P M D U u)

include hc

theorem D_inf_centralizer_u : D ⊓ centralizer ({u} : Set G) = U := by
  classical
  have hprime := hc.prime
  have hle : U ≤ D ⊓ centralizer ({u} : Set G) := by
    refine le_inf hc.U_le_D fun x hx => mem_centralizer_singleton_iff.mpr (hc.U_comm hx hc.uU)
  have hdvd1 : Nat.card U ∣ Nat.card ↥(D ⊓ centralizer ({u} : Set G)) := Subgroup.card_dvd_of_le hle
  have hdvd2 : Nat.card ↥(D ⊓ centralizer ({u} : Set G)) ∣ Nat.card D :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hc.Uc] at hdvd1
  rw [hc.card_D] at hdvd2
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hprime).mp hdvd2
  have hk2 : 2 ≤ k := by
    have := (Nat.pow_dvd_pow_iff_le_right hprime.one_lt).mp (hkc ▸ hdvd1)
    exact this
  by_cases hk3 : k = 3
  · exfalso
    have heq : D ⊓ centralizer ({u} : Set G) = D :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hkc, hk3, hc.card_D])
    apply hc.uZ
    refine ⟨⟨u, hc.U_le_D hc.uU⟩, mem_center_iff.mpr fun g => Subtype.ext ?_, rfl⟩
    have : (g : G) ∈ D ⊓ centralizer ({u} : Set G) := by
      rw [heq]
      exact g.2
    exact mem_centralizer_singleton_iff.mp this.2
  · have hk2' : k = 2 := by omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hkc, hk2', hc.Uc])).symm

theorem eq_or_eq_of_between {K : Subgroup G} (hUK : U ≤ K) (hKD : K ≤ D) : K = U ∨ K = D := by
  classical
  have hprime := hc.prime
  have hdvd1 : Nat.card U ∣ Nat.card K := Subgroup.card_dvd_of_le hUK
  have hdvd2 : Nat.card K ∣ Nat.card D := Subgroup.card_dvd_of_le hKD
  rw [hc.Uc] at hdvd1
  rw [hc.card_D] at hdvd2
  obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hprime).mp hdvd2
  have hk2 : 2 ≤ k := (Nat.pow_dvd_pow_iff_le_right hprime.one_lt).mp (hkc ▸ hdvd1)
  by_cases hk3 : k = 3
  · right
    exact Subgroup.eq_of_le_of_card_ge hKD (by rw [hkc, hk3, hc.card_D])
  · left
    have hk2' : k = 2 := by omega
    exact Subgroup.eq_of_le_of_card_ge hUK (by rw [hkc, hk2', hc.Uc]) |>.symm

theorem exists_d0 : ∃ d ∈ D, d ∉ U := by
  by_contra h
  push Not at h
  exact hc.UD.ne (le_antisymm hc.UD.le fun d hd => h d hd)

theorem D_eq_sup {d : G} (hdD : d ∈ D) (hdU : d ∉ U) : D = U ⊔ zpowers d := by
  have hle : U ⊔ zpowers d ≤ D := sup_le hc.U_le_D (zpowers_le.mpr hdD)
  rcases hc.eq_or_eq_of_between le_sup_left hle with h | h
  · exfalso
    apply hdU
    rw [← h]
    exact mem_sup_right (mem_zpowers d)
  · exact h.symm

theorem commutator_mem_U {y d : G} (hyP : y ∈ (P : Subgroup G)) (hyU : y ∈ centralizer (U : Set G))
    (hdD : d ∈ D) : y * d * y⁻¹ * d⁻¹ ∈ U := by
  have hyu : ∀ x ∈ U, y * x * y⁻¹ = x := fun x hx => by
    have := mem_centralizer_iff.mp hyU x hx
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]
  have hdP : d ∈ (P : Subgroup G) := hc.D_le_P hdD
  have hdu : d * u * d⁻¹ ∈ U := (mem_normalizer_iff.mp (hc.PU hdP) u).mp hc.uU
  have hdD' : y * d * y⁻¹ ∈ D := by
    have := (mem_normalizer_iff.mp (hc.PD hyP) d).mp hdD
    exact this
  have hcent : d⁻¹ * (y * d * y⁻¹) ∈ D ⊓ centralizer ({u} : Set G) := by
    refine ⟨D.mul_mem (D.inv_mem hdD) hdD', mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : y * d * y⁻¹ * u * (y * d * y⁻¹)⁻¹ = d * u * d⁻¹ := by
      have e1 : y * d * y⁻¹ * u * (y * d * y⁻¹)⁻¹ = y * (d * (y⁻¹ * u * y) * d⁻¹) * y⁻¹ := by
        group
      have e2 : y⁻¹ * u * y = u := by
        have h := hyu u hc.uU
        calc y⁻¹ * u * y = y⁻¹ * (y * u * y⁻¹) * y := by rw [h]
          _ = u := by group
      rw [e1, e2]
      exact hyu _ hdu
    calc d⁻¹ * (y * d * y⁻¹) * u = d⁻¹ * ((y * d * y⁻¹) * u * (y * d * y⁻¹)⁻¹) * (y * d * y⁻¹) := by
          group
      _ = d⁻¹ * (d * u * d⁻¹) * (y * d * y⁻¹) := by rw [h1]
      _ = u * (d⁻¹ * (y * d * y⁻¹)) := by group
  rw [hc.D_inf_centralizer_u] at hcent
  have h2 : d * (d⁻¹ * (y * d * y⁻¹)) * d⁻¹ ∈ U :=
    (mem_normalizer_iff.mp (hc.PU hdP) _).mp hcent
  have e3 : d * (d⁻¹ * (y * d * y⁻¹)) * d⁻¹ = y * d * y⁻¹ * d⁻¹ := by group
  rwa [e3] at h2

omit hc in
abbrev R (P : Sylow p G) (U : Subgroup G) : Subgroup G :=
  (P : Subgroup G) ⊓ centralizer (U : Set G)

theorem u_mem_R : u ∈ R P U :=
  ⟨hc.U_le_P hc.uU, mem_centralizer_iff.mpr fun _ hx => hc.U_comm hx hc.uU⟩

omit [Finite G] hc in
theorem R_comm_U {y x : G} (hy : y ∈ R P U) (hx : x ∈ U) : y * x = x * y :=
  (mem_centralizer_iff.mp hy.2 x hx).symm

@[expose] noncomputable def psi {d : G} (hdD : d ∈ D) : ↥(R P U) →* ↥U :=
  { toFun := fun y => ⟨(y : G) * d * (y : G)⁻¹ * d⁻¹, hc.commutator_mem_U y.2.1 y.2.2 hdD⟩
    map_one' := Subtype.ext (by simp)
    map_mul' := fun y y' => Subtype.ext (by
      have hb := hc.commutator_mem_U y'.2.1 y'.2.2 hdD
      have hg' := hc.commutator_mem_U y.2.1 y.2.2 hdD
      change (y : G) * y' * d * ((y : G) * y')⁻¹ * d⁻¹ =
        ((y : G) * d * (y : G)⁻¹ * d⁻¹) * ((y' : G) * d * (y' : G)⁻¹ * d⁻¹)
      exact commutator_mul_aux_7 (R_comm_U (U := U) y.2 hb)
        (hc.U_comm hg' hb)) }

theorem psi_apply {d : G} (hdD : d ∈ D) (y : ↥(R P U)) :
    ((hc.psi hdD y : U) : G) = (y : G) * d * (y : G)⁻¹ * d⁻¹ := rfl

theorem psi_eq_one_iff {d : G} (hdD : d ∈ D) (hdU : d ∉ U) (y : ↥(R P U)) :
    hc.psi hdD y = 1 ↔ (y : G) ∈ centralizer (D : Set G) := by
  constructor
  · intro h
    have h1 : (y : G) * d * (y : G)⁻¹ * d⁻¹ = 1 := congrArg Subtype.val h
    have hyd : (y : G) * d = d * (y : G) := by
      have := mul_inv_eq_one.mp h1
      exact mul_inv_eq_iff_eq_mul.mp this
    have hD : D ≤ centralizer ({(y : G)} : Set G) := by
      rw [hc.D_eq_sup hdD hdU]
      refine sup_le (fun x hx => mem_centralizer_singleton_iff.mpr (R_comm_U (U := U) y.2 hx).symm)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyd.symm))
    exact mem_centralizer_iff.mpr fun x hx => mem_centralizer_singleton_iff.mp (hD hx)
  · intro h
    apply Subtype.ext
    have hyd : d * (y : G) = (y : G) * d := mem_centralizer_iff.mp h d hdD
    change (y : G) * d * (y : G)⁻¹ * d⁻¹ = 1
    rw [← hyd]
    group

theorem psi_u {d : G} (hdD : d ∈ D) (hdU : d ∉ U) :
    ((hc.psi hdD ⟨u, hc.u_mem_R⟩ : U) : G) ∈ (center D).map D.subtype ∧
      hc.psi hdD ⟨u, hc.u_mem_R⟩ ≠ 1 := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hDc := (hc.ext.pow_eq_one_and_commutator_mem hprime hc.odd).2
  have huD : u ∈ D := hc.U_le_D hc.uU
  constructor
  · have hcent := hDc u huD d hdD
    have hmemD : u * d * u⁻¹ * d⁻¹ ∈ D := D.mul_mem (D.mul_mem (D.mul_mem huD hdD) (D.inv_mem huD))
      (D.inv_mem hdD)
    exact ⟨⟨_, hmemD⟩, mem_center_iff.mpr fun g => Subtype.ext
      (mem_centralizer_iff.mp hcent g g.2), rfl⟩
  · intro h
    rw [hc.psi_eq_one_iff hdD hdU] at h
    exact hc.uZ (hc.ext.mem_center_of_mem_centralizer hprime hc.odd hc.nonab
      (hc.U_le_P hc.uU) h (hc.pow_U hc.uU))

omit hc in
abbrev D2 (P : Sylow p G) (D : Subgroup G) : Subgroup G :=
  (P : Subgroup G) ⊓ centralizer (D : Set G)

theorem D2_le_R : D2 P D ≤ R P U := fun _ ha =>
  ⟨ha.1, mem_centralizer_iff.mpr fun x hx => mem_centralizer_iff.mp ha.2 x (hc.U_le_D hx)⟩

theorem PD2 : (P : Subgroup G) ≤ normalizer (D2 P D : Set G) :=
  (le_inf le_normalizer (hc.PD.trans (normalizer_le_normalizer_centralizer D))).trans
    inf_normalizer_le_normalizer_inf

theorem mem_Z_of_mem_D2 {a : G} (ha : a ∈ D2 P D) (hap : a ^ p = 1) :
    a ∈ (center D).map D.subtype :=
  hc.ext.mem_center_of_mem_centralizer hc.prime hc.odd hc.nonab ha.1 ha.2 hap

theorem isCyclic_D2 : IsCyclic (D2 P D) := by
  classical
  by_contra hnc
  have hp := hc.prime
  have hQp : IsPGroup p (D2 P D) := P.isPGroup'.to_le inf_le_left
  have h2 := two_le_pRank_of_not_isCyclic hp hc.odd hQp hnc
  obtain ⟨E, hE, hEe, hEc⟩ := pRank_attained p (D2 P D) (by omega)
  have hEZ : E ≤ (center D).map D.subtype := fun a ha => hc.mem_Z_of_mem_D2 (hE ha) (hEe.2 a ha)
  have h3 := Subgroup.card_le_of_le hEZ
  rw [hEc, hc.card_Z] at h3
  have h4 : p ^ 2 ≤ p ^ CFSG.Open.pRank p (D2 P D) := Nat.pow_le_pow_right hp.pos h2
  have h5 : p < p ^ 2 := by
    have := hp.one_lt
    nlinarith
  omega

theorem isMetacyclic_sup {y : G} (hy : y ∈ (P : Subgroup G)) :
    CFSG.IsMetacyclic ↥(D2 P D ⊔ zpowers y) := by
  classical
  set H : Subgroup G := D2 P D ⊔ zpowers y with hH
  have hD2H : D2 P D ≤ H := le_sup_left
  have hyH : y ∈ H := mem_sup_right (mem_zpowers y)
  have hHP : H ≤ (P : Subgroup G) := sup_le inf_le_left (zpowers_le.mpr hy)
  have hzP : zpowers y ≤ normalizer (D2 P D : Set G) := zpowers_le.mpr (hc.PD2 hy)
  have := hc.isCyclic_D2
  have hN : ((D2 P D).subgroupOf H).Normal :=
    (normal_subgroupOf_iff_le_normalizer hD2H).2 (hHP.trans hc.PD2)
  refine ⟨(D2 P D).subgroupOf H, hN,
    isCyclic_of_surjective (subgroupOfEquivOfLe hD2H).symm.toMonoidHom
      (subgroupOfEquivOfLe hD2H).symm.surjective, ?_⟩
  refine ⟨QuotientGroup.mk ⟨y, hyH⟩, fun x => ?_⟩
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
  have hmem : (h : G) ∈ (↑(D2 P D ⊔ zpowers y) : Set G) := h.2
  rw [coe_mul_of_right_le_normalizer_left _ _ hzP] at hmem
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.1 hmem
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
  refine mem_zpowers_iff.2 ⟨k, ?_⟩
  rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, mem_subgroupOf]
  have hyk : y ^ k ∈ normalizer (D2 P D : Set G) := hzP (zpow_mem_zpowers y k)
  have hyk' : (y ^ k)⁻¹ ∈ normalizer (D2 P D : Set G) := (normalizer (D2 P D : Set G)).inv_mem hyk
  have h1 : ((((⟨y, hyH⟩ : H) ^ k)⁻¹ * h : H) : G) = (y ^ k)⁻¹ * (h : G) := by simp
  rw [h1, ← hab]
  have e : (y ^ k)⁻¹ * (a * y ^ k) = (y ^ k)⁻¹ * a * ((y ^ k)⁻¹)⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.mp hyk' a).mp ha

theorem commute_of_mem_sup {y z : G} (hy : y ∈ (P : Subgroup G)) (hyp : y ^ p = 1)
    (hz : z ∈ D2 P D ⊔ zpowers y) (hzp : z ^ p = 1) : y * z = z * y := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  set H : Subgroup G := D2 P D ⊔ zpowers y with hH
  have hHP : H ≤ (P : Subgroup G) := sup_le inf_le_left (zpowers_le.mpr hy)
  have hHp : IsPGroup p H := P.isPGroup'.to_le hHP
  have hyH : y ∈ H := mem_sup_right (mem_zpowers y)
  by_cases hcyc : IsCyclic H
  · exact congrArg Subtype.val
      ((IsCyclic.isMulCommutative (α := H)).is_comm.comm ⟨y, hyH⟩ ⟨z, hz⟩)
  · have : Fact (IsPGroup p H) := ⟨hHp⟩
    obtain ⟨-, hel⟩ := CFSG.lemma_4_10 (p := p) hc.odd (hc.isMetacyclic_sup hy) hcyc
    have hyΩ : (⟨y, hyH⟩ : H) ∈ CFSG.omega₁ (G := H) (p := p) := by
      refine Subgroup.subset_closure ?_
      show (⟨y, hyH⟩ : H) ^ (p ^ 1) = 1
      apply Subtype.ext
      simpa using hyp
    have hzΩ : (⟨z, hz⟩ : H) ∈ CFSG.omega₁ (G := H) (p := p) := by
      refine Subgroup.subset_closure ?_
      show (⟨z, hz⟩ : H) ^ (p ^ 1) = 1
      apply Subtype.ext
      simpa using hzp
    have hcomm := (hel.toIsMulCommutative).is_comm.comm ⟨_, hyΩ⟩ ⟨_, hzΩ⟩
    have := congrArg (fun x => ((x : CFSG.omega₁ (G := H) (p := p)) : H).1) hcomm
    simpa using this

theorem commute_of_pow_eq_one {y y' : G} (hy : y ∈ R P U) (hy' : y' ∈ R P U) (hyp : y ^ p = 1)
    (hy'p : y' ^ p = 1) : y * y' = y' * y := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  by_cases hyU : y ∈ U
  · exact (R_comm_U (U := U) hy' hyU).symm
  by_cases hy'U : y' ∈ U
  · exact R_comm_U (U := U) hy hy'U
  obtain ⟨d, hdD, hdU⟩ := hc.exists_d0
  obtain ⟨z, hzZ, hz1, hordz, hzeq⟩ := hc.exists_Z_gen
  have hzU : z ∈ U := hc.Z_le_U hzZ
  have hup := hc.pow_U hc.uU
  let ψ := hc.psi hdD
  let Y : ↥(R P U) := ⟨y, hy⟩
  let Y' : ↥(R P U) := ⟨y', hy'⟩
  let 𝔲 : ↥(R P U) := ⟨u, hc.u_mem_R⟩
  obtain ⟨hψuZ, hψu1⟩ := hc.psi_u hdD hdU
  have hZgen : zpowers ((ψ 𝔲 : U) : G) = (center D).map D.subtype := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hψuZ) ?_
    have hne : ((ψ 𝔲 : U) : G) ≠ 1 := fun h => hψu1 (Subtype.ext h)
    have hpow := hc.pow_U (ψ 𝔲).2
    rw [hc.card_Z, Nat.card_zpowers, orderOf_eq_prime hpow hne]
  have hψYZ : ((ψ Y : U) : G) ∉ (center D).map D.subtype := by
    intro hmem
    rw [← hZgen] at hmem
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
    have hYk : ψ Y = (ψ 𝔲) ^ k := Subtype.ext (by simpa using hk.symm)
    have h1 : ψ (Y * 𝔲 ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, hYk, zpow_neg, mul_inv_cancel]
    have hw := (hc.psi_eq_one_iff hdD hdU _).1 h1
    have hwG : y * u ^ (-k) ∈ centralizer (D : Set G) := by simpa using hw
    have hcomm : Commute y (u ^ (-k)) :=
      Commute.zpow_right (R_comm_U (U := U) hy hc.uU) (-k)
    have hwp : (y * u ^ (-k)) ^ p = 1 := by
      rw [hcomm.mul_pow, hyp, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
        zpow_natCast, hup, one_zpow]
    have hwP : y * u ^ (-k) ∈ (P : Subgroup G) :=
      (P : Subgroup G).mul_mem hy.1 (zpow_mem (hc.U_le_P hc.uU) _)
    have hwZ := hc.mem_Z_of_mem_D2 ⟨hwP, hwG⟩ hwp
    apply hyU
    have : y = (y * u ^ (-k)) * u ^ k := by group
    rw [this]
    exact U.mul_mem (hc.Z_le_U hwZ) (zpow_mem hc.uU k)
  have hw1z : ((ψ Y : U) : G) ∉ zpowers z := by
    rw [hzeq]
    exact hψYZ
  obtain ⟨s, t, hst⟩ := exists_pow_mul_pow_of_mem_plane hc.Ue hc.Uc hzU hz1 (ψ Y).2 hw1z (ψ Y').2
  have hztZ : z ^ t ∈ zpowers ((ψ 𝔲 : U) : G) := by
    rw [hZgen]
    exact pow_mem hzZ t
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hztZ
  have hdec : ψ Y' = (ψ Y) ^ s * (ψ 𝔲) ^ k := Subtype.ext (by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_zpow]
    rw [hk]
    exact hst)
  have h2 : ψ (Y' * (Y ^ s * 𝔲 ^ k)⁻¹) = 1 := by
    rw [map_mul, map_inv, map_mul, map_pow, map_zpow, ← hdec, mul_inv_cancel]
  have hc2 := (hc.psi_eq_one_iff hdD hdU _).1 h2
  have hcG : y' * (y ^ s * u ^ k)⁻¹ ∈ centralizer (D : Set G) := by simpa using hc2
  have hcP : y' * (y ^ s * u ^ k)⁻¹ ∈ (P : Subgroup G) :=
    (P : Subgroup G).mul_mem hy'.1 ((P : Subgroup G).inv_mem ((P : Subgroup G).mul_mem
      (pow_mem hy.1 s) (zpow_mem (hc.U_le_P hc.uU) k)))
  set c : G := y' * (y ^ s * u ^ k)⁻¹ with hcdef
  have hy'eq : y' = c * y ^ s * u ^ k := by
    rw [hcdef]
    group
  have hukcomm : Commute y' (u ^ k) := Commute.zpow_right (R_comm_U (U := U) hy' hc.uU) k
  have hy''p : (c * y ^ s) ^ p = 1 := by
    have h3 : c * y ^ s = y' * (u ^ k)⁻¹ := by
      rw [hy'eq]
      group
    rw [h3, (hukcomm.inv_right).mul_pow, hy'p, one_mul, inv_pow, ← zpow_natCast, ← zpow_mul,
      mul_comm, zpow_mul, zpow_natCast, hup, one_zpow, inv_one]
  have hy''mem : c * y ^ s ∈ D2 P D ⊔ zpowers y :=
    (D2 P D ⊔ zpowers y).mul_mem (mem_sup_left ⟨hcP, hcG⟩)
      (mem_sup_right (pow_mem (mem_zpowers y) s))
  have hcomm := hc.commute_of_mem_sup hy.1 hyp hy''mem hy''p
  have hycomm : y * u ^ k = u ^ k * y := (Commute.zpow_right (R_comm_U (U := U) hy hc.uU) k).eq
  rw [hy'eq, ← mul_assoc, mul_assoc y (c * y ^ s) (u ^ k)]
  calc y * (c * y ^ s * u ^ k) = (y * (c * y ^ s)) * u ^ k := by group
    _ = ((c * y ^ s) * y) * u ^ k := by rw [hcomm]
    _ = (c * y ^ s) * (y * u ^ k) := by group
    _ = (c * y ^ s) * (u ^ k * y) := by rw [hycomm]
    _ = c * y ^ s * u ^ k * y := by group

theorem pRank_P : CFSG.Open.pRank p (P : Subgroup G) = 3 :=
  (sylow_le_of_isCoreMaxLocal hc.setting hc.sigma hc.ext.obstruction.1).2

theorem isElemAbelian_B : IsElemAbelian p (omegaOneOf p (R P U)) := by
  classical
  set S : Set G := {x | x ∈ R P U ∧ x ^ p = 1} with hS
  have hgen : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := fun x hx y hy =>
    hc.commute_of_pow_eq_one hx.1 hy.1 hx.2 hy.2
  have h1 : ∀ y ∈ closure S, ∀ x ∈ S, x * y = y * x := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy => exact fun x hx => hgen x hx y hy
    | one => exact fun x _ => by simp
    | mul a b _ _ iha ihb =>
      intro x hx
      calc x * (a * b) = (x * a) * b := by group
        _ = (a * x) * b := by rw [iha x hx]
        _ = a * (x * b) := by group
        _ = a * (b * x) := by rw [ihb x hx]
        _ = (a * b) * x := by group
    | inv a _ iha =>
      intro x hx
      have := iha x hx
      calc x * a⁻¹ = a⁻¹ * (a * x) * a⁻¹ := by group
        _ = a⁻¹ * (x * a) * a⁻¹ := by rw [this]
        _ = a⁻¹ * x := by group
  have hcl : ∀ x ∈ closure S, ∀ y ∈ closure S, x * y = y * x := by
    intro x hx y hy
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact h1 y hy x hx
    | one => simp
    | mul a b _ _ iha ihb =>
      calc a * b * y = a * (b * y) := by group
        _ = a * (y * b) := by rw [ihb]
        _ = (a * y) * b := by group
        _ = (y * a) * b := by rw [iha]
        _ = y * (a * b) := by group
    | inv a _ iha =>
      calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * y) * a⁻¹ := by rw [iha]
        _ = y * a⁻¹ := by group
  refine ⟨⟨⟨fun a b => Subtype.ext (hcl a a.2 b b.2)⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (hcl x hx y hy) p), ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

omit [Finite G] hc in
theorem mem_B {y : G} (hy : y ∈ R P U) (hyp : y ^ p = 1) : y ∈ omegaOneOf p (R P U) :=
  subset_closure ⟨hy, hyp⟩

omit [Finite G] hc in
theorem B_le_R : omegaOneOf p (R P U) ≤ R P U := omegaOneOf_le p _

theorem U_le_B : U ≤ omegaOneOf p (R P U) :=
  le_omegaOneOf_of_isElemAbelian (fun _ hx => ⟨hc.U_le_P hx,
    mem_centralizer_iff.mpr fun _ hy => hc.U_comm hy hx⟩) hc.Ue

theorem card_B : Nat.card (omegaOneOf p (R P U)) = p ^ 3 := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hB := hc.isElemAbelian_B
  have h3 : 3 ≤ CFSG.Open.pRank p (R P U) := hc.rank3
  obtain ⟨E, hER, hE, hEc⟩ := pRank_attained p (R P U) (by omega)
  have hEB : E ≤ omegaOneOf p (R P U) := le_omegaOneOf_of_isElemAbelian hER hE
  obtain ⟨k, hk⟩ := (elementary_isPGroup p _ hB).exists_card_eq
  have hBP : omegaOneOf p (R P U) ≤ (P : Subgroup G) := B_le_R.trans inf_le_left
  have hkle : k ≤ CFSG.Open.pRank p (P : Subgroup G) := by
    unfold CFSG.Open.pRank
    exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨_, hBP, hB, hk⟩
  rw [hc.pRank_P] at hkle
  have h4 : p ^ CFSG.Open.pRank p (R P U) ≤ p ^ k := by
    rw [← hEc, ← hk]
    exact Subgroup.card_le_of_le hEB
  have h5 := (Nat.pow_le_pow_iff_right hprime.one_lt).1 h4
  rw [hk]
  congr 1
  omega

omit [Finite G] hc in
theorem B_le_P : omegaOneOf p (R P U) ≤ (P : Subgroup G) := B_le_R.trans inf_le_left

theorem normalizer_le_of_le_R {X : Subgroup G} (hXR : X ≤ R P U)
    (hX2 : 2 ≤ CFSG.Open.pRank p X) : normalizer (X : Set G) ≤ M := by
  classical
  have hprime := hc.prime
  have : Fact p.Prime := ⟨hprime⟩
  have hB := hc.isElemAbelian_B
  set X₁ : Subgroup G := omegaOneOf p X with hX₁
  have hX₁B : X₁ ≤ omegaOneOf p (R P U) := by
    refine (closure_le _).2 fun x hx => mem_B (hXR hx.1) hx.2
  have hX₁P : X₁ ≤ (P : Subgroup G) := hX₁B.trans B_le_P
  obtain ⟨E, hEX, hE, hEc⟩ := pRank_attained p X (by omega)
  have hX₁2 : 2 ≤ CFSG.Open.pRank p X₁ := by
    have hEX₁ : E ≤ X₁ := le_omegaOneOf_of_isElemAbelian hEX hE
    have : CFSG.Open.pRank p X ≤ CFSG.Open.pRank p X₁ := by
      unfold CFSG.Open.pRank
      exact le_csSup (pRank_set_bddAbove p hprime.one_lt _) ⟨E, hEX₁, hE, hEc⟩
    omega
  have hBC : omegaOneOf p (R P U) ≤ (P : Subgroup G) ⊓ centralizer (X₁ : Set G) := by
    refine le_inf B_le_P fun b hb => mem_centralizer_iff.mpr fun x hx => ?_
    exact congrArg Subtype.val (hB.1.is_comm.comm ⟨x, hX₁B hx⟩ ⟨b, hb⟩)
  have hB3 : 3 ≤ CFSG.Open.pRank p (omegaOneOf p (R P U)) := by
    unfold CFSG.Open.pRank
    refine (Nat.le_refl 3).trans (le_csSup (pRank_set_bddAbove p hprime.one_lt _)
      ⟨_, le_rfl, hB, ?_⟩)
    exact hc.card_B
  have hX₁3 : 3 ≤ CFSG.Open.pRank p (X₁ ⊔ ((P : Subgroup G) ⊓ centralizer (X₁ : Set G))) :=
    hB3.trans (pRank_mono p hprime.one_lt (hBC.trans le_sup_right))
  exact (normalizer_le_normalizer_omegaOneOf p X).trans
    ((aschCore_normalizer_le 2 p (P : Subgroup G) X₁ hX₁P hX₁2 hX₁3).trans
      hc.ext.obstruction.1.2)

theorem commutator_mem_centralizer_D {y y' : G} (hy : y ∈ R P U) (hy' : y' ∈ R P U) :
    y * y' * y⁻¹ * y'⁻¹ ∈ centralizer (D : Set G) := by
  classical
  obtain ⟨d, hdD, hdU⟩ := hc.exists_d0
  let ψ := hc.psi hdD
  let Y : ↥(R P U) := ⟨y, hy⟩
  let Y' : ↥(R P U) := ⟨y', hy'⟩
  have hcomm : ψ Y * ψ Y' = ψ Y' * ψ Y := hc.Ue.1.is_comm.comm _ _
  have h1 : ψ (Y * Y' * Y⁻¹ * Y'⁻¹) = 1 := by
    simp only [map_mul, map_inv]
    rw [hcomm]
    group
  have h2 := (hc.psi_eq_one_iff hdD hdU _).1 h1
  simpa using h2

end NoncentralConfig

end CFSG.LocalAnalysis.RankThreeTheoremC
