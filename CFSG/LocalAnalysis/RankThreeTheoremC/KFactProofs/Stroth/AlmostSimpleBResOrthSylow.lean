module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimpleBResSpOuter

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.Open (IsElemAbelian)

@[expose] def SylowIso (p : ℕ) (G G' : Type*) [Group G] [Group G'] : Prop :=
  ∀ (P : Sylow p G) (P' : Sylow p G'), Nonempty (↥P ≃* ↥P')

section Cover

variable {O H G' : Type*} [Group O] [Group H] [Group G'] {p : ℕ} [Fact p.Prime]

theorem le_of_isPGroup_of_sq_mem (hp2 : p ≠ 2) {N : Subgroup O} (hsq : ∀ g : O, g ^ 2 ∈ N)
    {S : Subgroup O} (hS : IsPGroup p S) : S ≤ N := by
  intro x hx
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  have hk' : x ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : Odd (p ^ k) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have hx' : x = (x ^ 2) ^ (m + 1) := by
    have h1 : (x ^ 2) ^ (m + 1) = x ^ (p ^ k) * x := by
      rw [← pow_mul, hm, ← pow_succ]
      congr 1
    rw [h1, hk', one_mul]
  rw [hx']
  exact Subgroup.pow_mem _ (hsq x) _

theorem eq_one_of_isPGroup_of_sq_eq_one (hp2 : p ≠ 2) {S : Subgroup O} (hS : IsPGroup p S) {x : O}
    (hx : x ∈ S) (hx2 : x ^ 2 = 1) : x = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨x, hx⟩
  have hk' : x ^ (p ^ k) = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hodd : Odd (p ^ k) := ((Fact.out : p.Prime).odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have h1 : x ^ (p ^ k) = x := by
    rw [hm, pow_succ, pow_mul, hx2, one_pow, one_mul]
  rw [← h1, hk']

theorem sylowIso_of_cover [Finite O] [Finite H] (hp2 : p ≠ 2) {N : Subgroup O}
    (hsq : ∀ g : O, g ^ 2 ∈ N) (π : N →* H) (hπ : Function.Surjective π)
    (hker : ∀ x, π x = 1 → x ^ 2 = 1) (hO : SylowIso p O G') : SylowIso p H G' := by
  intro P P'
  obtain ⟨S⟩ : Nonempty (Sylow p O) := inferInstance
  have hSN : (S : Subgroup O) ≤ N := le_of_isPGroup_of_sq_mem hp2 hsq S.isPGroup'
  let SN : Sylow p N := S.subtype hSN
  let SH : Sylow p H := Sylow.mapSurjective hπ SN
  let e1 : ↥SN ≃* ↥S := Subgroup.subgroupOfEquivOfLe hSN
  let φ : ↥SN →* H := π.comp (SN : Subgroup N).subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h2 : (((x : N) : O)) ^ 2 = 1 := by
      have := hker (x : N) hx
      have h3 := congrArg Subtype.val this
      simpa using h3
    have hxS : ((x : N) : O) ∈ (S : Subgroup O) := x.2
    have h4 := eq_one_of_isPGroup_of_sq_eq_one hp2 S.isPGroup' hxS h2
    apply Subtype.ext
    apply Subtype.ext
    simpa using h4
  let e2 : ↥SN ≃* ↥SH := MulEquiv.ofBijective
    (φ.codRestrict (SH : Subgroup H) (fun x => Subgroup.mem_map_of_mem π x.2))
    ⟨fun a b h => hφ (congrArg Subtype.val h), fun y => by
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 y.2
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩⟩
  obtain ⟨e3⟩ := hO S P'
  exact ⟨(Sylow.equiv P SH).trans (e2.symm.trans (e1.trans e3))⟩

end Cover

section SpSide

variable {p : ℕ}

theorem le_of_elemAbelian_sylowSp {G : Type} [Group G] (hp : p.Prime) (hp2 : p ≠ 2) {F : Type}
    [Field F] [Finite F] {n' : ℕ} (hpc : ¬ p ∣ Nat.card F) (hS : SylowIso p G (StatedSp n' F))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) :
    2 * orderOf (Nat.card F : ZMod p) ≤
      (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n' else n') := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hEP⟩ := (IsPGroup.of_card hEc).exists_le_sylow
  obtain ⟨P'⟩ : Nonempty (Sylow p (StatedSp n' F)) := inferInstance
  obtain ⟨φ⟩ := hS P P'
  let ψ : ↥E →* StatedSp n' F :=
    (P' : Subgroup (StatedSp n' F)).subtype.comp
      (φ.toMonoidHom.comp (Subgroup.inclusion hEP))
  have hψ : Function.Injective ψ := by
    exact Subtype.val_injective.comp (φ.injective.comp (Subgroup.inclusion_injective hEP))
  have hWc : Nat.card ψ.range = p ^ 2 := by
    rw [← hEc]
    exact (Nat.card_congr (MonoidHom.ofInjective hψ).toEquiv).symm
  have hcomm : IsMulCommutative ψ.range := by
    haveI := hE.1
    refine ⟨⟨fun a b => ?_⟩⟩
    obtain ⟨x, hx⟩ := a.2
    obtain ⟨y, hy⟩ := b.2
    apply Subtype.ext
    show (a : StatedSp n' F) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    congr 1
    exact mul_comm' x y
  have hW : IsElemAbelian p ψ.range := by
    refine ⟨hcomm, ?_⟩
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (hE.2 x x.2)
    rw [this, map_one]
  exact le_of_elemAbelian_sp hp hp2 hpc hW hWc

theorem exists_pair_sp (hp : p.Prime) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F] [CharP F 2]
    {n' : ℕ} (hpc : ¬ p ∣ Nat.card F)
    (h2e : 2 * orderOf (Nat.card F : ZMod p) ≤
      (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n' else n')) :
    ∃ y₁ y₂ : StatedSp n' F, Commute y₁ y₂ ∧ y₁ ^ p = 1 ∧ y₂ ^ p = 1 ∧
      ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  obtain ⟨e', he', hn', hpe⟩ := exists_block_size_sp (K := F) hp hpc h2e
  have hdvd := dvd_card_statedSp_of_dvd (K := F) he' hpe
  obtain ⟨x₁, x₂, hc, h1, h2, hi, -, -⟩ := exists_two_indep_fixed_sp (K := F) hp hp2 he' hn' hdvd
    (τ := RingEquiv.refl F) (by show (1 : F ≃+* F) ^ p = 1; exact one_pow p)
  let e₀ : StatedSp n' F ≃* StatedProj (StatedSp n' F) :=
    MulEquiv.ofBijective (proj n' F) ⟨proj_injective_sp (by omega), QuotientGroup.mk'_surjective _⟩
  refine ⟨e₀.symm x₁, e₀.symm x₂, hc.map e₀.symm, ?_, ?_, fun i j hij => ?_⟩
  · rw [← map_pow, h1, map_one]
  · rw [← map_pow, h2, map_one]
  · rw [← map_zpow, ← map_zpow, ← map_mul] at hij
    exact hi i j (e₀.symm.injective (hij.trans (map_one e₀.symm).symm))

theorem exists_pair_of_sylowIso (hp : p.Prime) (hp2 : p ≠ 2) {F : Type} [Field F] [Finite F]
    [CharP F 2] {n' : ℕ} (hpc : ¬ p ∣ Nat.card F)
    (h2e : 2 * orderOf (Nat.card F : ZMod p) ≤
      (if Even (orderOf (Nat.card F : ZMod p)) then 2 * n' else n'))
    {G : Type} [Group G] (hS : SylowIso p G (StatedSp n' F)) :
    ∃ y₁ y₂ : G, Commute y₁ y₂ ∧ y₁ ^ p = 1 ∧ y₂ ^ p = 1 ∧
      ∀ i j : ℤ, y₁ ^ i * y₂ ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y₁, y₂, hc, h1, h2, hi⟩ := exists_pair_sp hp hp2 hpc h2e (n' := n')
  have hnorm : Subgroup.zpowers y₂ ≤ Subgroup.normalizer (Subgroup.zpowers y₁) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hc.zpow_left k).eq
  have hW : IsPGroup p (Subgroup.zpowers y₁ ⊔ Subgroup.zpowers y₂ : Subgroup (StatedSp n' F)) :=
    IsPGroup.to_sup_of_normal_left' (CFSG.Open.isElemAbelian_zpowers h1).isPGroup
      (CFSG.Open.isElemAbelian_zpowers h2).isPGroup hnorm
  obtain ⟨P', hP'⟩ := hW.exists_le_sylow
  have hy1 : y₁ ∈ (P' : Subgroup (StatedSp n' F)) :=
    hP' (Subgroup.mem_sup_left (Subgroup.mem_zpowers y₁))
  have hy2 : y₂ ∈ (P' : Subgroup (StatedSp n' F)) :=
    hP' (Subgroup.mem_sup_right (Subgroup.mem_zpowers y₂))
  obtain ⟨P⟩ : Nonempty (Sylow p G) := inferInstance
  obtain ⟨φ⟩ := hS P P'
  let a : ↥P' := ⟨y₁, hy1⟩
  let b : ↥P' := ⟨y₂, hy2⟩
  have hab : Commute a b := Subtype.ext hc.eq
  have ha : a ^ p = 1 := Subtype.ext (by simpa using h1)
  have hb : b ^ p = 1 := Subtype.ext (by simpa using h2)
  refine ⟨((φ.symm a : ↥P) : G), ((φ.symm b : ↥P) : G),
    (hab.map φ.symm).map (P : Subgroup G).subtype, ?_, ?_, fun i j hij => ?_⟩
  · have : (φ.symm a) ^ p = 1 := by rw [← map_pow, ha, map_one]
    simpa using congrArg Subtype.val this
  · have : (φ.symm b) ^ p = 1 := by rw [← map_pow, hb, map_one]
    simpa using congrArg Subtype.val this
  · have h3 : (φ.symm a) ^ i * (φ.symm b) ^ j = 1 := by
      apply Subtype.ext
      simpa using hij
    have h4 : a ^ i * b ^ j = 1 := by
      apply φ.symm.injective
      rw [map_mul, map_zpow, map_zpow, h3, map_one]
    exact hi i j (by simpa using congrArg Subtype.val h4)

end SpSide

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.AlmostSimple
