module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.OutBOm6
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CBSwapProof
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CNCtx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec6Outside
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FF6PSCent
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Ctx
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5B517Pair
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Statements2
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEIso2

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r : G}
  {B A K₁ K₂ : Subgroup G} {h : G}

theorem sec5cn_mem_normalizer_of_le {K : Subgroup G} {m : G} (hle : K ≤ CFSG.conjugate K m) :
    m ∈ normalizer (K : Set G) := by
  have hcard : Nat.card (CFSG.conjugate K m) ≤ Nat.card K := by
    simpa only [CFSG.conjugate] using
      (Subgroup.card_map_of_injective (K := K) (f := (MulAut.conj m⁻¹).toMonoidHom)
        (MulAut.conj m⁻¹).injective).le
  exact (sec5b513_conjugate_eq_iff).mp (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem sec5cn_le_conjugate (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {m : G}
    (hmz : m ∈ centralizer ({z} : Set G)) (hKL : K₁ ⊔ K₂ ≤ CFSG.conjugate L m) :
    K₁ ⊔ K₂ ≤ CFSG.conjugate (K₁ ⊔ K₂) m := by
  have hKm : twoRes (CFSG.conjugate L m ⊓ centralizer ({z} : Set G)) =
      CFSG.conjugate (K₁ ⊔ K₂) m := by
    rw [← sec5b513_conjugate_inf_centralizer L hmz, sec5b513_twoRes_conjugate, ← c.prod]
  rw [← hKm]
  conv_lhs => rw [c.prod]
  unfold twoRes
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hg, hodd⟩
  have hgK : g ∈ K₁ ⊔ K₂ := c.K_odd_mem hg hodd
  exact Subgroup.subset_closure
    ⟨Subgroup.mem_inf.mpr ⟨hKL hgK, (Subgroup.mem_inf.mp hg).2⟩, hodd⟩

theorem sec5cn_core (h36 : Asc82Lemma36) (h52a : Asc82Lemma52a) (hO : Asc82Outside)
    (hAut : Asc82FactAutOm6) (c : Sec5HCtx G t L S z r B A K₁ K₂ h) {m : G}
    (hmz : m ∈ centralizer ({z} : Set G)) (hs2 : orderOf (m⁻¹ * t * m) = 2)
    (hsz : m⁻¹ * t * m ≠ z) (hst : (m⁻¹ * t * m) * t = t * (m⁻¹ * t * m))
    (hs1 : m⁻¹ * t * m ≠ t) (hs3 : m⁻¹ * t * m ≠ t * z)
    (hK : ∀ k ∈ K₁ ⊔ K₂, (m⁻¹ * t * m) * k = k * (m⁻¹ * t * m)) :
    m ∈ normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOm : IsOm6Z2 L := c.toSec5Ctx.toSec5Setting.isOm6Z2
  have ht2 : orderOf t = 2 := c.involution
  have hss : (m⁻¹ * t * m) * (m⁻¹ * t * m) = 1 := by
    rw [← pow_two, ← hs2]
    exact pow_orderOf_eq_one _
  have hsC : m⁻¹ * t * m ∈ centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hst
  have hsN : m⁻¹ * t * m ∈ normalizer (L : Set G) :=
    sec4_mem_normalizer h36 c.toSec3SettingLB _ hsC
  have hKc : twoRes (L ⊓ centralizer ({z} : Set G)) ≤ centralizer ({m⁻¹ * t * m} : Set G) := by
    rw [← c.prod]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hK k hk).symm
  have htC : t ∈ centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (c.L_le_centralizer hy)
  have hmz' : m * z = z * m := Subgroup.mem_centralizer_singleton_iff.mp hmz
  have hmz'' : m⁻¹ * z = z * m⁻¹ := by
    calc m⁻¹ * z = m⁻¹ * (z * m) * m⁻¹ := by group
      _ = m⁻¹ * (m * z) * m⁻¹ := by rw [hmz']
      _ = z * m⁻¹ := by group
  have hsz' : (m⁻¹ * t * m) * z = z * (m⁻¹ * t * m) := by
    calc (m⁻¹ * t * m) * z = m⁻¹ * t * (m * z) := by group
      _ = m⁻¹ * t * (z * m) := by rw [hmz']
      _ = m⁻¹ * (t * z) * m := by group
      _ = m⁻¹ * (z * t) * m := by rw [c.t_comm_z]
      _ = (m⁻¹ * z) * t * m := by group
      _ = (z * m⁻¹) * t * m := by rw [hmz'']
      _ = z * (m⁻¹ * t * m) := by group
  rcases hAut G L hOm t ht2 c.centre z c.pocket _ hs2 hsN hKc with hL1 | hL2 | ⟨hq, hle⟩
  · exfalso
    have hsL : m⁻¹ * t * m ∈ centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hL1 hy)
    exact sec5cb_not_mem_centralizer h52a c.toSec5Ctx.toSec5Setting ht2 hs2 hst.symm hs1.symm
      htC hsL
  · exfalso
    have hszL : (m⁻¹ * t * m) * z ∈ centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy =>
        Subgroup.mem_centralizer_singleton_iff.mp (hL2 hy)
    have hsz2 : orderOf ((m⁻¹ * t * m) * z) = 2 := by
      refine orderOf_eq_prime ?_ ?_
      · calc ((m⁻¹ * t * m) * z) ^ 2 = ((m⁻¹ * t * m) * z) * ((m⁻¹ * t * m) * z) := pow_two _
          _ = (m⁻¹ * t * m) * (z * (m⁻¹ * t * m)) * z := by group
          _ = (m⁻¹ * t * m) * ((m⁻¹ * t * m) * z) * z := by rw [hsz']
          _ = ((m⁻¹ * t * m) * (m⁻¹ * t * m)) * (z * z) := by group
          _ = 1 := by rw [hss, c.z_mul_self, mul_one]
      · intro h1
        apply hsz
        calc m⁻¹ * t * m = (m⁻¹ * t * m) * (z * z) := by rw [c.z_mul_self, mul_one]
          _ = ((m⁻¹ * t * m) * z) * z := by group
          _ = z := by rw [h1, one_mul]
    have hrt : t * ((m⁻¹ * t * m) * z) = ((m⁻¹ * t * m) * z) * t := by
      calc t * ((m⁻¹ * t * m) * z) = (t * (m⁻¹ * t * m)) * z := by group
        _ = ((m⁻¹ * t * m) * t) * z := by rw [hst]
        _ = (m⁻¹ * t * m) * (t * z) := by group
        _ = (m⁻¹ * t * m) * (z * t) := by rw [c.t_comm_z]
        _ = ((m⁻¹ * t * m) * z) * t := by group
    have hne : t ≠ (m⁻¹ * t * m) * z := by
      intro h1
      apply hs3
      calc m⁻¹ * t * m = (m⁻¹ * t * m) * (z * z) := by rw [c.z_mul_self, mul_one]
        _ = ((m⁻¹ * t * m) * z) * z := by group
        _ = t * z := by rw [← h1]
    exact sec5cb_not_mem_centralizer h52a c.toSec5Ctx.toSec5Setting ht2 hsz2 hrt hne htC hszL
  · have hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (L : Set G)) → IsCyclic ↥P :=
      fun P hP => sec5_isCyclic_of_isSylow2Of (h52a G t L c.toSec5Ctx.toSec5Setting) hP
    have hX : layerCent L (m⁻¹ * t * m) ≤ CFSG.conjugate L m :=
      (le_twoPrimeRes_of_isQuasisimple hq).trans (hO.thm2L G t L c.toSec3SettingLB hcyc
        (asc82OddInnerOm6_holds G L (Or.inl hOm)) (-1) m hsC hs1 _ (Or.inl rfl))
    have hKL : K₁ ⊔ K₂ ≤ CFSG.conjugate L m := by
      rw [c.prod]
      exact hle.trans hX
    exact sec5cn_mem_normalizer_of_le (sec5cn_le_conjugate c hmz hKL)

end CFSG.OddStandard.SmallF3.Omega
