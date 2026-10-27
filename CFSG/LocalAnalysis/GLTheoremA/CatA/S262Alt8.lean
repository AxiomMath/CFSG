module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S262Defs
public import CFSG.LocalAnalysis.GL83PartI.I_27_9_3.Alt
import CFSG.GroupTheory.PLayer.Conj
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import Certificates.Data.A5

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S262

open CFSG.Open
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped Pointwise

abbrev Alt8Sub : Subgroup (Equiv.Perm (Fin 8)) := alternatingGroup (Fin 8)

abbrev Alt8 : Type := Alt8Sub

abbrev s8 : Finset (Fin 8) := {3, 4, 5, 6, 7}

@[expose] def c8 : Alt8 :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by
    rw [Equiv.Perm.mem_alternatingGroup]
    decide⟩

theorem card_mulAut_alt8 :
    Nat.card (MulAut (alternatingGroup (Fin 8))) = 40320 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 8
    (by norm_num) (by norm_num)
  rw [← Nat.card_congr
      (Equiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 8))) hbij),
    Nat.card_perm, Nat.card_fin]
  norm_num

abbrev K8 : Subgroup Alt8 := (GL83.altOn (s8 : Set (Fin 8))).subgroupOf Alt8Sub

theorem c8_apply_eq_iff (x : Fin 8) : (c8 : Equiv.Perm (Fin 8)) x = x ↔ x ∈ s8 := by
  revert x
  decide

theorem c8_pow_three : c8 ^ 3 = 1 := by
  apply Subtype.ext
  decide

theorem K8_equiv_alt5 : Nonempty (K8 ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := GL83.PiGen.exists_altOn_equiv_fin s8 (m := 5) (by decide)
  exact ⟨(Subgroup.subgroupOfEquivOfLe
    (GL83.PiGen.altOn_le_alternatingGroup (s8 : Set (Fin 8)))).trans e⟩

theorem K8_isSimpleGroup : IsSimpleGroup K8 := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup_five
  obtain ⟨e⟩ := K8_equiv_alt5
  exact e.isSimpleGroup

theorem K8_three_dvd_card : 3 ∣ Nat.card K8 := by
  obtain ⟨e⟩ := K8_equiv_alt5
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  norm_num

theorem K8_not_commutative : ∃ a b : K8, a * b ≠ b * a := by
  have hnc : ¬ IsMulCommutative (alternatingGroup (Fin 5)) := by
    rw [alternatingGroup.isMulCommutative_iff_card_le_three]
    norm_num
  have hnc' : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnc (isMulCommutative_iff.mpr h)
  obtain ⟨e⟩ := K8_equiv_alt5
  obtain ⟨a, b, hab⟩ := hnc'
  exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩

theorem K8_le_centralizer : K8 ≤ Subgroup.centralizer ({c8} : Set Alt8) := by
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  have hk' : (k : Equiv.Perm (Fin 8)) ∈ GL83.altOn (s8 : Set (Fin 8)) :=
    Subgroup.mem_subgroupOf.mp hk
  exact (GL83.PiGen.commute_of_mem_altOn
    (S := (s8 : Set (Fin 8))) (fun x hx => (c8_apply_eq_iff x).2 hx) hk').symm

theorem mem_s8_iff_of_mem_centralizer {k : Alt8}
    (hk : k ∈ Subgroup.centralizer ({c8} : Set Alt8)) (x : Fin 8) :
    (k : Equiv.Perm (Fin 8)) x ∈ s8 ↔ x ∈ s8 := by
  have hcomm : (k : Equiv.Perm (Fin 8)) * (c8 : Equiv.Perm (Fin 8)) =
      (c8 : Equiv.Perm (Fin 8)) * (k : Equiv.Perm (Fin 8)) :=
    congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hk)
  constructor
  · intro hx
    have h1 : (c8 : Equiv.Perm (Fin 8)) ((k : Equiv.Perm (Fin 8)) x) =
        (k : Equiv.Perm (Fin 8)) x := (c8_apply_eq_iff _).2 hx
    have h2 : (k : Equiv.Perm (Fin 8)) ((c8 : Equiv.Perm (Fin 8)) x) =
        (c8 : Equiv.Perm (Fin 8)) ((k : Equiv.Perm (Fin 8)) x) :=
      congrArg (fun p : Equiv.Perm (Fin 8) => p x) hcomm
    rw [h1] at h2
    exact (c8_apply_eq_iff x).1 ((k : Equiv.Perm (Fin 8)).injective h2)
  · intro hx
    have h1 : (c8 : Equiv.Perm (Fin 8)) x = x := (c8_apply_eq_iff x).2 hx
    have h2 : (k : Equiv.Perm (Fin 8)) ((c8 : Equiv.Perm (Fin 8)) x) =
        (c8 : Equiv.Perm (Fin 8)) ((k : Equiv.Perm (Fin 8)) x) :=
      congrArg (fun p : Equiv.Perm (Fin 8) => p x) hcomm
    rw [h1] at h2
    exact (c8_apply_eq_iff _).1 h2.symm

theorem K8_normal : (K8.subgroupOf (Subgroup.centralizer ({c8} : Set Alt8))).Normal := by
  refine (Subgroup.normal_subgroupOf_iff K8_le_centralizer).mpr ?_
  intro h k hh hk
  have hh' : (h : Equiv.Perm (Fin 8)) ∈ GL83.altOn (s8 : Set (Fin 8)) :=
    Subgroup.mem_subgroupOf.mp hh
  have hpres : ∀ x, (k : Equiv.Perm (Fin 8)) x ∈ s8 ↔ x ∈ s8 :=
    mem_s8_iff_of_mem_centralizer hk
  have hconj := GL83.PiGen.conj_mem_altOn (S := (s8 : Set (Fin 8))) hpres hh'
  exact Subgroup.mem_subgroupOf.mpr (by simpa [K8] using hconj)

theorem glaPLayer_centralizer_threeCycle_ne_bot :
    GLAPLayer 3 (Subgroup.centralizer ({c8} : Set Alt8)) ≠ ⊥ := by
  haveI : IsSimpleGroup K8 := K8_isSimpleGroup
  have hle := CFSG.HardMathSupport.Solomon.Coordinator.le_glaPLayer_of_normal_simple
    (p := 3) (by norm_num)
    K8_le_centralizer K8_normal K8_not_commutative K8_three_dvd_card
  intro hbot
  have hKbot : K8 = ⊥ := le_bot_iff.mp (hbot ▸ hle)
  obtain ⟨x, hx⟩ := exists_ne (1 : K8)
  have hx1 : x = 1 := by
    apply Subtype.ext
    have hmem : (x : Alt8) ∈ (⊥ : Subgroup Alt8) := by
      rw [← hKbot]
      exact x.2
    exact Subgroup.mem_bot.mp hmem
  exact hx hx1

theorem i262Alt8_aux :
    ∀ A : Subgroup (MulAut Alt8), IsElemAbelian 3 A → 9 ≤ Nat.card A →
      ∃ a ∈ A, a ≠ 1 ∧ GLAPLayer 3 (fixSubgroup a) ≠ ⊥ := by
  intro A hA h9
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcardAut : Nat.card (MulAut Alt8) = 40320 := card_mulAut_alt8
  haveI : Finite (MulAut Alt8) :=
    Nat.finite_of_card_ne_zero (by rw [hcardAut]; norm_num)
  have hAdvd : Nat.card A ∣ 40320 := by
    calc Nat.card A ∣ Nat.card (MulAut Alt8) := Subgroup.card_subgroup_dvd_card A
      _ = 40320 := hcardAut
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA.isPGroup
  have hkge : 2 ≤ k := by
    rw [hk] at h9
    by_contra h
    have hk1 : k ≤ 1 := by omega
    have hpow : 3 ^ k ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
    norm_num at hpow
    omega
  have hkle : k ≤ 2 := by
    by_contra h
    have h3k : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega : 3 ≤ k)
    have hdvd : 3 ^ k ∣ 40320 := by rw [← hk]; exact hAdvd
    have h27 : (27 : ℕ) ∣ 40320 := by simpa using h3k.trans hdvd
    norm_num at h27
  have hk2 : k = 2 := by omega
  have hAcard : Nat.card A = 9 := by rw [hk, hk2]; norm_num
  have hAindex : ¬ 3 ∣ A.index := by
    have h := Subgroup.card_mul_index A
    rw [hAcard, hcardAut] at h
    have hidx : A.index = 4480 := by omega
    rw [hidx]
    norm_num
  let A' : Sylow 3 (MulAut Alt8) := hA.isPGroup.toSylow hAindex
  have hA'coe : (A' : Subgroup (MulAut Alt8)) = A :=
    IsPGroup.toSylow_coe hA.isPGroup hAindex
  let γ : MulAut Alt8 := MulAut.conj c8
  have hγ3 : γ ^ 3 = 1 := by
    have hmap : γ ^ 3 = MulAut.conj (c8 ^ 3) := by
      dsimp only [γ]
      exact (map_pow (MulAut.conj : Alt8 →* MulAut Alt8) c8 3).symm
    rw [hmap, c8_pow_three, map_one]
  have hγne : γ ≠ 1 := by
    let x8 : Alt8 :=
      ⟨Equiv.swap 0 1 * Equiv.swap 1 3, by
        rw [Equiv.Perm.mem_alternatingGroup]
        decide⟩
    have hxP : (c8 : Equiv.Perm (Fin 8)) * (x8 : Equiv.Perm (Fin 8)) *
        (c8 : Equiv.Perm (Fin 8))⁻¹ ≠ (x8 : Equiv.Perm (Fin 8)) := by decide
    intro h
    have hfix : γ x8 = x8 := by rw [h]; rfl
    have hfixP : (c8 : Equiv.Perm (Fin 8)) * (x8 : Equiv.Perm (Fin 8)) *
        (c8 : Equiv.Perm (Fin 8))⁻¹ = (x8 : Equiv.Perm (Fin 8)) :=
      congrArg Subtype.val hfix
    exact hxP (by simpa [γ, MulAut.conj_apply] using hfixP)
  have hzp : IsPGroup 3 (Subgroup.zpowers γ) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers]
    exact orderOf_dvd_iff_pow_eq_one.mpr hγ3
  obtain ⟨P, hP⟩ := hzp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (MulAut Alt8) P A'
  have hγP : γ ∈ (P : Subgroup (MulAut Alt8)) := hP (Subgroup.mem_zpowers γ)
  let a : MulAut Alt8 := MulAut.conj g γ
  have haA : a ∈ A := by
    have hsub : (MulAut.conj g) • (P : Subgroup (MulAut Alt8)) = A := by
      calc (MulAut.conj g) • (P : Subgroup (MulAut Alt8))
          = ↑(g • P) := (Sylow.coe_subgroup_smul).symm
        _ = (A' : Subgroup (MulAut Alt8)) := by rw [hg]
        _ = A := hA'coe
    have hmem : (MulAut.conj g) γ ∈
        (MulAut.conj g) • (P : Subgroup (MulAut Alt8)) :=
      Subgroup.smul_mem_pointwise_smul γ (MulAut.conj g) _ hγP
    rwa [hsub] at hmem
  have hane : a ≠ 1 := by
    intro ha1
    have hγ1 : γ = 1 := by
      have h := congrArg (fun e : MulAut Alt8 => (MulAut.conj g)⁻¹ e) ha1
      have h' : (MulAut.conj g)⁻¹ a = γ := by
        dsimp only [a]
        exact (MulAut.conj g).symm_apply_apply γ
      rw [h'] at h
      simpa using h
    exact hγne hγ1
  refine ⟨a, haA, hane, ?_⟩
  have hγlayer : GLAPLayer 3 (fixSubgroup γ) ≠ ⊥ := by
    change GLAPLayer 3 (fixSubgroup (MulAut.conj c8)) ≠ ⊥
    rw [CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_fixSubgroup_conj c8]
    exact glaPLayer_centralizer_threeCycle_ne_bot
  exact glaPLayer_fixSubgroup_ne_bot_of_conj (p := 3) (by norm_num)
    (α := a) (δ := γ) (ψ := g⁻¹) (by
      dsimp only [a]
      rw [MulAut.conj_apply, inv_inv]
      group) hγlayer

theorem i262Alt8_holds : I262Alt8 := by
  simpa [I262Alt8, Alt8] using i262Alt8_aux

end CFSG.LocalAnalysis.GLTheoremA.S262

end
