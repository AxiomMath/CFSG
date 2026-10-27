module

public import CFSG.Permutation.TranspositionCentralizer
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.ParabolicComap
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SmallGroups

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section14

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup

variable {X : Type} [Group X] [Finite X] {n : ℕ}

theorem map_eq_alternatingGroup_of_closure_odd (hn : 5 ≤ n) {L : Subgroup X} (hLn : L.Normal)
    (hLodd : L = Subgroup.closure {x : X | x ∈ L ∧ Odd (orderOf x)})
    (φ : X →* Equiv.Perm (Fin n)) (hφ : Function.Surjective φ) (hLker : ¬ L ≤ φ.ker) :
    L.map φ = alternatingGroup (Fin n) := by
  classical
  haveI : L.Normal := hLn
  have hmap_closure : L.map φ = Subgroup.closure (φ '' {x : X | x ∈ L ∧ Odd (orderOf x)}) := by
    conv_lhs => rw [hLodd]
    rw [MonoidHom.map_closure]
  have hle : L.map φ ≤ alternatingGroup (Fin n) := by
    rw [hmap_closure, Subgroup.closure_le]
    rintro _ ⟨x, ⟨hxL, hxodd⟩, rfl⟩
    exact CFSG.Quasithin.F53.mem_alt_of_odd_order (Odd.of_dvd_nat hxodd (orderOf_map_dvd φ x))
  have hnt : Nontrivial (L.map φ) := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    intro hbot
    apply hLker
    intro x hxL
    rw [MonoidHom.mem_ker]
    by_contra hx1
    have hxmem : φ x ∈ L.map φ := Subgroup.mem_map_of_mem φ hxL
    rw [hbot] at hxmem
    exact hx1 (by simpa using hxmem)
  have hmap_normal : (L.map φ).Normal := hLn.map φ hφ
  haveI : (L.map φ).Normal := hmap_normal
  have hAlt : alternatingGroup (Fin n) ≤ L.map φ :=
    Equiv.Perm.alternatingGroup_le_of_normal (α := Fin n) (by simpa using hn) hnt
  exact le_antisymm hle hAlt

theorem map_eq_zpowers_swap (hn : 7 ≤ n) {R : Subgroup X} (φ : X →* Equiv.Perm (Fin n))
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hR2 : IsPGroup 2 R) {i j : Fin n}
    (hij : i ≠ j)
    (hNR : (Subgroup.normalizer (R : Set X)).map φ =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin n)))) :
    R.map φ = Subgroup.zpowers (Equiv.swap i j) := by
  classical
  let Q : Subgroup X := CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
  let N : Subgroup X := Subgroup.normalizer (R : Set X)
  let C : Subgroup (Equiv.Perm (Fin n)) :=
    Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin n)))
  let S : Subgroup (Equiv.Perm (Fin n)) := R.map φ
  have hNR' : N.map φ = C := hNR
  have hR2S : IsPGroup 2 S := hR2.map φ
  have hS_le_C : S ≤ C := by
    rintro _ ⟨r, hr, rfl⟩
    rw [← hNR']
    exact Subgroup.mem_map_of_mem φ (Subgroup.le_normalizer hr)
  have hC_le_normalizer_S : C ≤ Subgroup.normalizer (S : Set (Equiv.Perm (Fin n))) := by
    rw [Subgroup.le_normalizer_iff]
    intro c hc s hs
    rw [← hNR'] at hc
    obtain ⟨nn, hnN, rfl⟩ := Subgroup.mem_map.mp hc
    obtain ⟨r, hrR, rfl⟩ := Subgroup.mem_map.mp hs
    rw [← map_mul, ← map_inv, ← map_mul]
    exact Subgroup.mem_map_of_mem φ ((Subgroup.mem_normalizer_iff.mp hnN r).mp hrR)
  have hS_le_zpowers : S ≤ Subgroup.zpowers (Equiv.swap i j) :=
    CFSG.Permutation.TranspositionCentralizer.le_zpowers_swap_of_isPGroup (α := Fin n) hij
      (by simpa using hn) hR2S hS_le_C hC_le_normalizer_S
  have hS_ne_bot : S ≠ ⊥ := by
    intro hSbot
    have hR_le_ker : R ≤ φ.ker := (Subgroup.map_eq_bot_iff R).mp hSbot
    have hR_eq_Q : R = Q := le_antisymm (by simpa [Q, hker] using hR_le_ker) hQR
    haveI : Q.Normal := by
      change (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).Normal
      rw [← hker]
      exact MonoidHom.normal_ker φ
    have hN_top : N = ⊤ := by
      change Subgroup.normalizer (R : Set X) = ⊤
      rw [hR_eq_Q]
      exact Subgroup.normalizer_eq_top Q
    have hC_top : C = ⊤ := by
      rw [← hNR', hN_top, Subgroup.map_top_of_surjective φ hφ]
    have h3n : 3 ≤ n := by omega
    exact CFSG.Permutation.TranspositionCentralizer.centralizer_swap_ne_top (α := Fin n) hij
      (by simpa using h3n) hC_top
  have hZ_card : Nat.card (Subgroup.zpowers (Equiv.swap i j)) = 2 := by
    rw [Nat.card_zpowers,
      Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr hij)]
  have hS_eq_zpowers : S = Subgroup.zpowers (Equiv.swap i j) := by
    let Z : Subgroup (Equiv.Perm (Fin n)) := Subgroup.zpowers (Equiv.swap i j)
    haveI : Fact (Nat.card Z).Prime :=
      ⟨by rw [show Nat.card Z = 2 from hZ_card]; norm_num⟩
    have hsub : S.subgroupOf Z = ⊥ ∨ S.subgroupOf Z = ⊤ :=
      (S.subgroupOf Z).eq_bot_or_eq_top_of_prime_card
    rcases hsub with hbot | htop
    · exfalso
      apply hS_ne_bot
      rw [eq_bot_iff]
      intro s hs
      have hmem : (⟨s, hS_le_zpowers hs⟩ : Z) ∈ S.subgroupOf Z := hs
      rw [hbot] at hmem
      simpa using hmem
    · exact le_antisymm hS_le_zpowers (Subgroup.subgroupOf_eq_top.mp htop)
  exact hS_eq_zpowers

theorem sup_eq_top_of_map_eq {L R : Subgroup X} (φ : X →* Equiv.Perm (Fin n))
    (hkerR : φ.ker ≤ R) (hL : L.map φ = alternatingGroup (Fin n))
    {i j : Fin n} (hij : i ≠ j) (hR : R.map φ = Subgroup.zpowers (Equiv.swap i j)) :
    L ⊔ R = ⊤ := by
  have hmap : (L ⊔ R).map φ = ⊤ := by
    rw [Subgroup.map_sup, hL, hR]
    exact CFSG.Permutation.TranspositionCentralizer.alternatingGroup_sup_zpowers_swap hij
  have hker : φ.ker ≤ L ⊔ R := hkerR.trans le_sup_right
  have hcomap := Subgroup.comap_map_eq φ (L ⊔ R)
  rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker] at hcomap
  exact hcomap.symm

section Parabolic

theorem le_comap_fixingSubgroup {R : Subgroup X} (φ : X →* Equiv.Perm (Fin n))
    {i j k : Fin n} (hR : R.map φ = Subgroup.zpowers (Equiv.swap i j)) :
    R ≤ (fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ := by
  rw [← Subgroup.map_le_iff_le_comap, hR]
  exact Subgroup.zpowers_le.mpr
    (CFSG.Permutation.TranspositionCentralizer.swap_mem_fixingSubgroup i j k)

theorem minParabolic_comap_fixingSubgroup {R : Subgroup X} (φ : X →* Equiv.Perm (Fin n))
    (hφ : Function.Surjective φ) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R) (hR2 : IsPGroup 2 R)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hR : R.map φ = Subgroup.zpowers (Equiv.swap i j)) :
    CFSG.Quasithin.MinParabolic
      ((fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ) R R := by
  classical
  have hkerR : φ.ker ≤ R := by
    rw [hker]
    exact hQR
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 ⊤
  have hRcomap : (Subgroup.zpowers (Equiv.swap i j)).comap φ = R := by
    rw [← hR, Subgroup.comap_map_eq, sup_eq_left.mpr hkerR]
  have hE2 : IsPGroup 2 (Subgroup.zpowers (Equiv.swap i j)) := by
    have hZcard : Nat.card (Subgroup.zpowers (Equiv.swap i j)) = 2 := by
      rw [Nat.card_zpowers,
        Equiv.Perm.IsSwap.orderOf (Equiv.Perm.swap_isSwap_iff.mpr hij)]
    exact IsPGroup.of_card (p := 2) (G := Subgroup.zpowers (Equiv.swap i j)) (n := 1)
      (by rw [hZcard]; norm_num)
  have hgen := minParabolic_comap_of_relIndex_eq_three (X := X) φ hφ hker2
    (E := Subgroup.zpowers (Equiv.swap i j))
    (P := fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n)))
    hE2
    (Subgroup.zpowers_le.mpr
      (CFSG.Permutation.TranspositionCentralizer.swap_mem_fixingSubgroup i j k))
    (CFSG.Permutation.TranspositionCentralizer.relIndex_zpowers_swap_fixingSubgroup
      hij hik hjk)
    (CFSG.Permutation.TranspositionCentralizer.fixingSubgroup_not_le_normalizer_zpowers_swap
      hij hik hjk)
  simpa [hRcomap] using hgen

end Parabolic

theorem charTwo_comap_fixingSubgroup {R : Subgroup X} (φ : X →* Equiv.Perm (Fin n))
    (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X))
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {i j k : Fin n} (hR : R.map φ = Subgroup.zpowers (Equiv.swap i j)) :
    CFSG.QuasithinUnique.CharTwo
      ((fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ) := by
  have hRP : R ≤ (fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ :=
    le_comap_fixingSubgroup φ hR
  have hQP : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤
      (fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ :=
    hQR.trans hRP
  exact CFSG.QuasithinUnique.CharTwo.of_pCoreOf_le hC le_top hQP

theorem perfectCore_comap_fixingSubgroup_eq_bot {R : Subgroup X}
    (φ : X →* Equiv.Perm (Fin n)) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {i j k : Fin n} (hR : R.map φ = Subgroup.zpowers (Equiv.swap i j)) :
    CFSG.Quasithin.perfectCore
      ((fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ) = ⊥ := by
  classical
  have hker_solv : IsSolvable φ.ker := by
    rw [hker]
    haveI : Group.IsNilpotent (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)).isNilpotent
    exact IsNilpotent.to_isSolvable
  have hSf_solv :
      IsSolvable (fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))) :=
    CFSG.Permutation.TranspositionCentralizer.isSolvable_fixingSubgroup_compl_triple i j k
  exact perfectCore_comap_eq_bot (X := X) φ hker_solv hSf_solv

theorem normalizer_sup_comap_fixingSubgroup_eq_top {R : Subgroup X}
    (φ : X →* Equiv.Perm (Fin n)) (hφ : Function.Surjective φ)
    (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hQR : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ R)
    {i j k : Fin n} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hR : R.map φ = Subgroup.zpowers (Equiv.swap i j))
    (hNR : (Subgroup.normalizer (R : Set X)).map φ =
      Subgroup.centralizer ({Equiv.swap i j} : Set (Equiv.Perm (Fin n)))) :
    Subgroup.normalizer (R : Set X) ⊔
      (fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))).comap φ = ⊤ := by
  classical
  let Sf : Subgroup (Equiv.Perm (Fin n)) :=
    fixingSubgroup (Equiv.Perm (Fin n)) ({i, j, k}ᶜ : Set (Fin n))
  let P : Subgroup X := Sf.comap φ
  let N : Subgroup X := Subgroup.normalizer (R : Set X)
  have hPmap : P.map φ = Sf := by
    rw [show P = Sf.comap φ from rfl, Subgroup.map_comap_eq,
      MonoidHom.range_eq_top.mpr hφ, top_inf_eq]
  have hmap : (N ⊔ P).map φ = ⊤ := by
    rw [Subgroup.map_sup, hNR, hPmap]
    exact CFSG.Permutation.TranspositionCentralizer.centralizer_swap_sup_fixingSubgroup_eq_top
      hij hik hjk
  have hker_le : φ.ker ≤ N ⊔ P := by
    rw [hker]
    exact (hQR.trans (Subgroup.le_normalizer)).trans le_sup_left
  have hcomap := Subgroup.comap_map_eq φ (N ⊔ P)
  rw [hmap, Subgroup.comap_top, sup_eq_left.mpr hker_le] at hcomap
  exact hcomap.symm
