module

public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddQuad
public import CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1POddBound

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Open.StatedAPI
open Matrix

theorem gomiOdd_two_ne_zero {K : Type} [Field K] [Finite K] (h : Odd (Nat.card K)) :
    (2 : K) ≠ 0 := by
  intro h2
  have hne : (1 : K) ≠ 0 := one_ne_zero
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : addOrderOf (1 : K) = 2 :=
    addOrderOf_eq_prime (by simpa using h2) hne
  have hdvd : addOrderOf (1 : K) ∣ Nat.card K := addOrderOf_dvd_natCard _
  rw [hord] at hdvd
  exact (Nat.not_even_iff_odd.mpr h) (even_iff_two_dvd.mpr hdvd)

theorem gomiOdd_false_of_statedProj_sp_two {T : Type} [Group T] {K : Type} [Field K] [Finite K]
    (hK2 : (2 : K) ≠ 0) (e : T ≃* StatedProj (StatedSp 2 K)) (E : Subgroup T)
    (hEcard : Nat.card E = 2 ^ 6) (hEsq : ∀ x ∈ E, x * x = 1) : False := by
  set H := StatedSp 2 K with hH
  set Z : Subgroup H := (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf H with hZ
  let π : H →* StatedProj H := QuotientGroup.mk' Z
  set E' : Subgroup (StatedProj H) := E.map e.toMonoidHom with hE'
  have hE'card : Nat.card E' = 2 ^ 6 := by
    rw [hE', Subgroup.card_map_of_injective e.injective]
    exact hEcard
  have hE'sq : ∀ y ∈ E', y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hEsq x hx, map_one]
  set P : Subgroup H := E'.comap π with hP
  have hsq1 : ((-1 : Kˣ)) ^ 2 = 1 := by simp
  let zH : H := ⟨GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : Kˣ),
    (scalar_mem_statedSp_iff (by norm_num) (-1 : Kˣ)).mpr hsq1⟩
  have hzZ : zH ∈ Z := by
    rw [hZ, Subgroup.mem_subgroupOf]
    exact ⟨-1, rfl⟩
  have hzP : zH ∈ P := by
    rw [hP, Subgroup.mem_comap]
    have : π zH = 1 := (QuotientGroup.eq_one_iff zH).mpr hzZ
    rw [this]
    exact E'.one_mem
  set z : P := ⟨zH, hzP⟩ with hz
  have hscal_central : ∀ g : H, g * zH = zH * g := by
    intro g
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul, zH, GeneralLinearGroup.coe_scalar]
    exact ((Matrix.scalar_commute (-(1 : K)) (fun r => Commute.all _ _) _).symm)
  have hsqP : ∀ x : P, x * x = 1 ∨ x * x = z := by
    intro x
    have hx2 : ((x : H) * (x : H)) ∈ Z := by
      rw [← QuotientGroup.eq_one_iff]
      show π ((x : H) * (x : H)) = 1
      rw [map_mul]
      exact hE'sq _ x.2
    rw [hZ, Subgroup.mem_subgroupOf] at hx2
    obtain ⟨c, hc⟩ := hx2
    have hcsp : GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c ∈ StatedSp 2 K := by
      rw [hc]
      exact ((x : H) * (x : H)).2
    have hc2 : c ^ 2 = 1 := (scalar_mem_statedSp_iff (by norm_num) c).mp hcsp
    have hc2' : (c : K) * (c : K) = 1 := by
      have := congrArg Units.val hc2
      simpa [sq] using this
    rcases mul_self_eq_one_iff.mp hc2' with h1 | h1
    · left
      have hc1 : c = 1 := Units.ext h1
      have : ((x : H) * (x : H) : H) = 1 := by
        apply Subtype.ext
        rw [← hc, hc1, map_one]
        rfl
      exact Subtype.ext this
    · right
      have hc1 : c = -1 := Units.ext (by simpa using h1)
      have : ((x : H) * (x : H) : H) = zH := by
        apply Subtype.ext
        rw [← hc, hc1]
      exact Subtype.ext this
  have hzz : zH * zH = 1 := by
    apply Subtype.ext
    show (GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : Kˣ)) *
      (GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) (-1 : Kˣ)) = 1
    rw [← map_mul]
    simp
  have hquad : GomiQuad P z := ⟨fun x => Subtype.ext (hscal_central x), Subtype.ext hzz, hsqP⟩
  have hbound : ∀ W : Subgroup P, GomiElemAb W → Nat.card W ≤ 4 := by
    intro W hW
    have hinj : Function.Injective (fun x : P => (x : H)) := Subtype.val_injective
    set W' : Subgroup H := W.map P.subtype with hW'
    have hW'card : Nat.card W' = Nat.card W := by
      rw [hW']
      exact Subgroup.card_map_of_injective hinj
    have hsqW : ∀ h ∈ W', h * h = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      have := hW.2 x hx
      exact congrArg Subtype.val this
    rw [← hW'card]
    exact gomiOdd_card_le_four_statedSp hK2 W' hsqW
  have hle := hquad.card_le_thirty_two hbound
  have hsurj : Function.Surjective (fun x : P => (⟨π x, x.2⟩ : E')) := by
    rintro ⟨y, hy⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective Z y
    exact ⟨⟨g, hy⟩, rfl⟩
  have hge : Nat.card E' ≤ Nat.card P := Nat.card_le_card_of_surjective _ hsurj
  rw [hE'card] at hge
  omega

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
