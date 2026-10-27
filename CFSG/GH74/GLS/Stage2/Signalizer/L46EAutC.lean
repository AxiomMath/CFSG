module

public import CFSG.GH74.GLS.Stage2.Signalizer.L46EDefs
public import CFSG.GH74.GLS.Stage2.Signalizer.L46EAutCQuo
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87FL3Char
public import CFSG.RankThree.PartOne.AUTSL.Interface

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L46E

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87 CFSG.GH74.GLS.Stage2.Signalizer.L46E.AutC
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups

namespace AutC

section Generation

variable {Y : Type} [Group Y] {p : ℕ}

theorem ncl_closure_p_elements (X : Subgroup Y) (hX : IsPGroup p ↥X) (k : ↥(ncl X)) :
    k ∈ Subgroup.closure {x : ↥(ncl X) | ∃ a : ℕ, x ^ p ^ a = 1} := by
  obtain ⟨k, hk⟩ := k
  have hk' : k ∈ Subgroup.closure (Group.conjugatesOfSet (X : Set Y)) := hk
  refine Subgroup.closure_induction
    (p := fun x hx => (⟨x, hx⟩ : ↥(ncl X)) ∈
      Subgroup.closure {x : ↥(ncl X) | ∃ a : ℕ, x ^ p ^ a = 1}) ?_ ?_ ?_ ?_ hk'
  · intro x hx
    obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, rfl⟩ := isConj_iff.mp hconj
    obtain ⟨m, hm⟩ := hX ⟨a, ha⟩
    refine Subgroup.subset_closure ⟨m, ?_⟩
    apply Subtype.ext
    have h1 : a ^ p ^ m = 1 := by simpa using congrArg Subtype.val hm
    show (c * a * c⁻¹) ^ p ^ m = 1
    rw [conj_pow, h1]
    group
  · exact one_mem _
  · intro x y hx hy ihx ihy
    exact mul_mem ihx ihy
  · intro x hx ihx
    exact inv_mem ihx

end Generation

section CenterLemmas

variable {G : Type*} [Group G]

theorem mulAut_mem_center (e : MulAut G) {z : G} (hz : z ∈ Subgroup.center G) :
    e z ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff] at hz ⊢
  intro g
  obtain ⟨g', rfl⟩ := e.surjective g
  rw [← map_mul, ← map_mul, hz g']

theorem map_center_eq_of_mulAut (e : MulAut G) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center G := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mulAut_mem_center e hz
  · intro hx
    refine ⟨e.symm x, mulAut_mem_center e.symm hx, by simp⟩

end CenterLemmas

end AutC

open AutC

theorem autFactCOdd_thm : AutFactCOdd := by
  intro Y _ _ p z X hp hp2 hC y hy hcop
  obtain ⟨n, hn, hLie, hXz, hmax, hOp, hel, hcard⟩ := hC
  have hpp : Fact p.Prime := ⟨hp⟩
  have hXK : X ≤ ncl X := (le_sup_left : X ≤ X ⊔ zpowers z).trans hXz
  have hKn : (ncl X).Normal := Subgroup.normalClosure_normal
  obtain ⟨F, iF, fF, hFcard, ⟨ι⟩⟩ :=
    CFSG.RankThree.PartOne.AUTSL.exists_projectiveSL_equiv_of_lieModel hLie
  have hpF : p ∣ Nat.card F := by
    rw [hFcard]
    exact dvd_pow_self p (by omega)
  have hchar : CharP F p := charP_of_dvd_card p hpF
  have h2 : (2 : F) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : F) = 0 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp ((CharP.cast_eq_zero_iff F p 2).mp h'))
  set K : Subgroup Y := ncl X with hK
  let φ : ↥K →* projectiveSL 3 F :=
    ι.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hs : Function.Surjective φ := ι.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerφ : φ.ker = Subgroup.center ↥K := by
    ext k
    rw [MonoidHom.mem_ker]
    show ι (QuotientGroup.mk k) = 1 ↔ _
    rw [map_eq_one_iff ι ι.injective, QuotientGroup.eq_one_iff]
  let θ : MulAut ↥K := MulAut.conjNormal y
  have hθapply : ∀ k : ↥K, ((θ k : ↥K) : Y) = y * (k : Y) * y⁻¹ := fun k =>
    MulAut.conjNormal_apply y k
  have hordθ : Nat.Coprime (orderOf θ) p :=
    Nat.Coprime.coprime_dvd_left
      (orderOf_map_dvd (MulAut.conjNormal : Y →* MulAut ↥K) y) hcop
  have hfixy : ∀ x ∈ X, y * x * y⁻¹ = x := fun x hx =>
    mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hy x hx).symm
  set P : Subgroup Y := X ⊔ K ⊓ centralizer ({z} : Set Y) with hP
  have hPK : P ≤ K := hmax.1.1
  have hPar : ParData ↥K p (P.subgroupOf K) := parData_of_isMaxParabolicP hmax
  have hel' : IsElementaryAbelian p ↥X := hel
  have hXpg : IsPGroup p ↥X := IsElementaryAbelian.isPGroup p ↥X
  set X₀ : Subgroup ↥K := X.subgroupOf K with hX₀
  have hXp : IsPGroup p ↥X₀ :=
    hXpg.of_injective (Subgroup.subgroupOfEquivOfLe hXK).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hXK).injective
  have hPnorm : P ≤ normalizer (X : Set Y) := by
    rw [hOp]
    exact le_normalizer_Op p P
  have hXP : P.subgroupOf K ≤ normalizer (X₀ : Set ↥K) := by
    intro k hk
    have hkP : (k : Y) ∈ P := hk
    have hkX := hPnorm hkP
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp hkX (x : Y)
  have hθX : ∀ x ∈ X₀, θ x = x := by
    intro x hx
    apply Subtype.ext
    rw [hθapply]
    exact hfixy x hx
  have hθker : φ.ker.map θ.toMonoidHom = φ.ker := by
    rw [hkerφ]
    exact map_center_eq_of_mulAut θ
  have hXne : X₀.map φ ≠ ⊥ := by
    intro hbot
    have hXc : X₀ ≤ Subgroup.center ↥K := by
      intro x hx
      have : φ x ∈ X₀.map φ := Subgroup.mem_map_of_mem φ hx
      rw [hbot, Subgroup.mem_bot] at this
      rw [← hkerφ]
      exact this
    set Zc : Subgroup Y := (Subgroup.center ↥K).map K.subtype with hZc
    have hZn : Zc.Normal := ⟨fun n hn g => by
      obtain ⟨z₀, hz₀, rfl⟩ := hn
      refine ⟨MulAut.conjNormal g z₀, mulAut_mem_center (MulAut.conjNormal g) hz₀, ?_⟩
      exact MulAut.conjNormal_apply g z₀⟩
    have hXZ : (X : Set Y) ⊆ Zc := by
      intro x hx
      exact ⟨⟨x, hXK hx⟩, hXc (show (⟨x, hXK hx⟩ : ↥K) ∈ X₀ from hx), rfl⟩
    have hKZ : K ≤ Zc := Subgroup.normalClosure_le_normal hXZ
    have hcentral : ∀ k : ↥K, k ∈ Subgroup.center ↥K := by
      intro k
      obtain ⟨z₀, hz₀, hz₀k⟩ := hKZ k.2
      have : z₀ = k := Subtype.ext hz₀k
      exact this ▸ hz₀
    have hone : proj 3 F (elP 1 0) = 1 := by
      obtain ⟨k, hk⟩ := hs (proj 3 F (elP 1 0))
      rw [← hk]
      have : k ∈ φ.ker := by rw [hkerφ]; exact hcentral k
      exact this
    have := eq_zero_of_elP_mem_scalars (proj_eq_one_iff.mp hone)
    exact one_ne_zero this.1
  have hcentθ : ∀ k : ↥K, θ k * k⁻¹ ∈ Subgroup.center ↥K := by
    intro k
    have := trivial_on_quotient p h2 φ hs hkerφ.le hPar hXP hXp hXne θ hθX hθker hordθ k
    rw [← hkerφ, MonoidHom.mem_ker, map_mul, map_inv, this, mul_inv_cancel]
  have hZ : ∀ z' ∈ Subgroup.center ↥K, (∃ a : ℕ, z' ^ p ^ a = 1) → θ z' = z' := by
    rintro z' hz' ⟨a, ha⟩
    have hz'P : (z' : Y) ∈ P := by
      obtain ⟨U₀, hU₀⟩ := hPar.syl
      exact hU₀ (Subgroup.center_le_normalizer _ hz')
    have hz'pow : (z' : Y) ^ p ^ a = 1 := by simpa using congrArg Subtype.val ha
    have hcomm : ∀ g ∈ P, g * (z' : Y) = (z' : Y) * g := by
      intro g hg
      have := Subgroup.mem_center_iff.mp hz' ⟨g, hPK hg⟩
      exact congrArg Subtype.val this
    have hzpP : zpowers (z' : Y) ≤ P := (Subgroup.zpowers_le).mpr hz'P
    have hcommzpow : ∀ g ∈ P, ∀ m : ℤ, g * (z' : Y) ^ m = (z' : Y) ^ m * g :=
      fun g hg m => (Commute.zpow_right (hcomm g hg : Commute g (z' : Y)) m).eq
    have hnorm : P ≤ normalizer ((zpowers (z' : Y) : Subgroup Y) : Set Y) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨m, rfl⟩
        have h1 : g * (z' : Y) ^ m * g⁻¹ = (z' : Y) ^ m := by
          rw [hcommzpow g hg m]
          group
        rw [h1]
        exact ⟨m, rfl⟩
      · rintro ⟨m, hm⟩
        refine ⟨m, ?_⟩
        have hm' : (z' : Y) ^ m = g * x * g⁻¹ := hm
        have h2 : x = g⁻¹ * (z' : Y) ^ m * g := by
          rw [hm']
          group
        rw [h2, hcommzpow g⁻¹ (P.inv_mem hg) m]
        group
    have hpg : IsPGroup p ↥(zpowers (z' : Y)) := by
      intro g
      obtain ⟨g, m, rfl⟩ := g
      refine ⟨a, ?_⟩
      apply Subtype.ext
      show ((z' : Y) ^ m) ^ p ^ a = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz'pow, one_zpow]
    have hle := le_Op_of_normal' hzpP hnorm hpg
    rw [← hOp] at hle
    have hzX : (z' : Y) ∈ X := hle (Subgroup.mem_zpowers _)
    apply Subtype.ext
    rw [hθapply]
    exact hfixy _ hzX
  have hθ1 : θ = 1 := eq_one_of_central p θ hcentθ (ncl_closure_p_elements X hXpg) hZ hordθ
  refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
  have h1 := congrArg Subtype.val (DFunLike.congr_fun hθ1 ⟨k, hk⟩)
  have h2' : y * k * y⁻¹ = k := by simpa [hθapply] using h1
  calc k * y = (y * k * y⁻¹) * y := by rw [h2']
    _ = y * k := by group

end CFSG.GH74.GLS.Stage2.Signalizer.L46E
