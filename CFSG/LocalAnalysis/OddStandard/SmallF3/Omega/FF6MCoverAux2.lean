module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2GenCover
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFKindDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {A B : Type} [Group A] [Group B] {ρ : A →* B}

private theorem ff6m_twoRes_aux2 (hρ : OddCentralCover ρ) :
    (twoRes (⊤ : Subgroup A)).map ρ = twoRes (⊤ : Subgroup B) := by
  unfold twoRes
  rw [MonoidHom.map_closure]
  congr 1
  ext b
  constructor
  · rintro ⟨a, ⟨-, haodd⟩, rfl⟩
    exact ⟨Subgroup.mem_top _, haodd.of_dvd_nat (orderOf_map_dvd ρ a)⟩
  · rintro ⟨-, hbodd⟩
    obtain ⟨a, ha⟩ := hρ.surjective b
    refine ⟨a, ⟨Subgroup.mem_top _, ?_⟩, ha⟩
    have hker : a ^ orderOf b ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_pow, ha, pow_orderOf_eq_one]
    have hpow : (a ^ orderOf b) ^ Nat.card ρ.ker = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard ρ.ker hker)
    have hdvd : orderOf a ∣ orderOf b * Nat.card ρ.ker := by
      apply orderOf_dvd_of_pow_eq_one
      rw [pow_mul]
      exact hpow
    exact (hbodd.mul hρ.odd_card_ker).of_dvd_nat hdvd

theorem ff6m_cover_xTwoCore [Finite A] (hρ : OddCentralCover ρ) (h : XTwoCore B) :
    XTwoCore A := by
  haveI : Finite B := Finite.of_surjective ρ hρ.surjective
  let T : Subgroup A := twoRes (⊤ : Subgroup A)
  let TB : Subgroup B := twoRes (⊤ : Subgroup B)
  have hmapT : T.map ρ = TB := ff6m_twoRes_aux2 hρ
  let ψ : ↥T →* ↥TB :=
    { toFun := fun x => ⟨ρ (x : A), by rw [← hmapT]; exact Subgroup.mem_map_of_mem ρ x.2⟩
      map_one' := Subtype.ext (map_one ρ)
      map_mul' := fun x y => Subtype.ext (map_mul ρ (x : A) (y : A)) }
  let P : Subgroup ↥T := (CFSG.pCore 2 ↥TB).comap ψ
  have hPnormal : P.Normal := (CFSG.pCore_normal (p := 2) (G := ↥TB)).comap ψ
  haveI := hPnormal
  have hPnil : Group.IsNilpotent ↥P := by
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥TB) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥TB)).isNilpotent
    let ψ' : ↥P →* ↥(CFSG.pCore 2 ↥TB) :=
      (ψ.comp P.subtype).codRestrict _ (fun x => x.2)
    refine Subgroup.isNilpotent_of_ker_le_center ψ' ?_
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    apply Subtype.ext
    have hxk : ψ (x : ↥T) = 1 := by
      have h := MonoidHom.mem_ker.mp hx
      exact congrArg Subtype.val h
    have hxkerA : ((x : ↥T) : A) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker]
      exact congrArg Subtype.val hxk
    have hxc : ((x : ↥T) : A) ∈ center A := hρ.ker_le_center hxkerA
    simp only [Subgroup.coe_mul]
    exact Subgroup.mem_center_iff.mp hxc ((y : ↥T) : A)
  have hpc : twoPrimeRes TB = (CFSG.pCore 2 ↥TB).map TB.subtype := by
    simpa only [TB, XTwoCore, ffX, CFSG.inSubgroup] using h
  have hle : twoPrimeRes T ≤ CFSG.inSubgroup (CFSG.pCore 2) T := by
    rw [twoPrimeRes]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    obtain ⟨hgT, j, hgj⟩ := hg
    let g' : ↥T := ⟨g, hgT⟩
    have hgP : g' ∈ P := by
      show ψ g' ∈ CFSG.pCore 2 ↥TB
      have hdvd : orderOf (ψ g') ∣ 2 ^ j := by
        have h := orderOf_map_dvd ψ g'
        rwa [← Subgroup.orderOf_coe g', hgj] at h
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hmemTB : (ψ g' : B) ∈ twoPrimeRes TB := by
        rw [twoPrimeRes]
        refine Subgroup.subset_closure ⟨(ψ g').2, ⟨i, ?_⟩⟩
        simpa [Subgroup.orderOf_coe] using hi
      have hmemB : (ψ g' : B) ∈ (CFSG.pCore 2 ↥TB).map TB.subtype := by
        rw [← hpc]
        exact hmemTB
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmemB
      have hy' : y = ψ g' := TB.subtype_injective (by simpa using hyeq)
      exact hy' ▸ hy
    have hg2 : g' ^ (2 ^ j) = 1 := by
      apply Subtype.ext
      show (g : A) ^ (2 ^ j) = 1
      rw [← hgj]
      exact pow_orderOf_eq_one g
    have hpcore : g' ∈ CFSG.pCore 2 ↥T :=
      mem_pCore_two_of_nilpotent_normal P hPnil hgP hg2
    show g ∈ (CFSG.pCore 2 ↥T).map T.subtype
    exact Subgroup.mem_map_of_mem T.subtype hpcore
  have hge : CFSG.inSubgroup (CFSG.pCore 2) T ≤ twoPrimeRes T := by
    intro g hg
    rw [CFSG.inSubgroup] at hg
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hg
    rw [← hyeq, twoPrimeRes]
    refine Subgroup.subset_closure ⟨y.2, ?_⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.pCore_isPGroup (p := 2) (G := ↥T))) ⟨y, hy⟩
    exact ⟨k, by simpa [Subgroup.orderOf_coe] using hk⟩
  change twoPrimeRes T = CFSG.inSubgroup (CFSG.pCore 2) T
  exact le_antisymm hle hge

end CFSG.OddStandard.SmallF3.Omega