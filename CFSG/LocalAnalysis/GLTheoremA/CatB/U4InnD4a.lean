module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp8c
public import CFSG.LocalAnalysis.GLTheoremA.CatB.U4InnSp6

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

open CFSG.Open Module CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

theorem unique_decomp {G : Type*} [Group G] {P Q : Subgroup G} (hPQ : P ⊓ Q = ⊥)
    {a a' b b' : G} (ha : a ∈ P) (ha' : a' ∈ P) (hb : b ∈ Q) (hb' : b' ∈ Q)
    (h : a * b = a' * b') : a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ P ⊓ Q := ⟨P.mul_mem (P.inv_mem ha') ha, h1 ▸ Q.mul_mem hb' (Q.inv_mem hb)⟩
  rw [hPQ, Subgroup.mem_bot] at h2
  have e1 : a = a' := by
    have := congrArg (a' * ·) h2
    simpa using this
  refine ⟨e1, ?_⟩
  subst e1
  exact mul_left_cancel h


theorem pPrimeCore_of_le_centralizer {s : StatedSp 4 (ZMod 2)} (hs3 : s ^ 3 = 1)
    (hs1 : s ≠ 1) {X : Type} [Group X] [Finite X] (ι : X →* StatedSp 4 (ZMod 2))
    (hι : Function.Injective ι)
    (hX : ∀ x, ι x ∈ Subgroup.centralizer ({s} : Set (StatedSp 4 (ZMod 2))))
    (L : Subgroup X) (hLp : Group.IsPerfect ↥L) (hL : 25920 ∣ Nat.card ↥L) :
    CFSG.pPrimeCore 3 X = ⊥ := by
  obtain ⟨s₀, m, A₀, A₁, hc⟩ := exists_class hs3 hs1
  obtain ⟨E, _, hE, W, _, _, _, Hf, hsymm, hsep, hdim, ⟨e₁⟩⟩ := hc.unitary
  have hsum := hc.sum_eq
  have hCX : ∀ x, ι x ∈ A₀ ⊔ A₁ := fun x => by rw [← hc.centralizer_eq]; exact hX x
  have hpos : 25920 ≤ Nat.card X :=
    Nat.le_of_dvd Nat.card_pos (hL.trans (Subgroup.card_subgroup_dvd_card L))
  have hbound : Nat.card X ≤ Nat.card ↥A₀ * Nat.card ↥A₁ := by
    refine le_trans ?_ (card_sup_le hc.commute)
    exact Nat.card_le_card_of_injective (fun x => (⟨ι x, hCX x⟩ : ↥(A₀ ⊔ A₁)))
      (fun x y hxy => hι (congrArg Subtype.val hxy))
  have hA₁ : Nat.card ↥A₁ = Nat.card (sesqUnitaryGroup Hf) := Nat.card_congr e₁.toEquiv
  have hm : m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 := by have := hc.one_le; omega
  rcases hm with rfl | rfl | rfl | rfl
  ·
    have hs₀ : s₀ = 3 := by omega
    subst hs₀
    obtain ⟨-, e₀⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨e₀⟩ := e₀
    have hcard₁ : Nat.card ↥A₁ = 3 := by rw [hA₁]; exact card_unitary_one hE hsymm hsep hdim
    have hdec : ∀ x : X, ∃ a ∈ A₀, ∃ b ∈ A₁, ι x = a * b := fun x =>
      exists_mul_of_mem_sup hc.commute (hCX x)
    choose a ha b hb hab using hdec
    have hcomm' : ∀ x y : X, a x * b x * (a y * b y) = (a x * a y) * (b x * b y) := by
      intro x y
      have := hc.commute (a y) (ha y) (b x) (hb x)
      calc a x * b x * (a y * b y) = a x * (b x * a y) * b y := by group
        _ = a x * (a y * b x) * b y := by rw [← this]
        _ = (a x * a y) * (b x * b y) := by group
    let π : X →* ↥A₀ :=
      { toFun := fun x => ⟨a x, ha x⟩
        map_one' := by
          apply Subtype.ext
          have h1 : ι 1 = 1 := map_one ι
          have := unique_decomp hc.disjoint (ha 1) A₀.one_mem (hb 1) A₁.one_mem
            (by rw [← hab, h1, mul_one])
          exact this.1
        map_mul' := by
          intro x y
          apply Subtype.ext
          have h1 : ι (x * y) = ι x * ι y := map_mul ι x y
          have := unique_decomp hc.disjoint (ha (x * y)) (A₀.mul_mem (ha x) (ha y))
            (hb (x * y)) (A₁.mul_mem (hb x) (hb y))
            (by rw [← hab, h1, hab x, hab y, hcomm'])
          exact this.1 }
    let π' : X →* StatedSp 3 (ZMod 2) := e₀.toMonoidHom.comp π
    have hker : ∀ x ∈ π'.ker, ι x ∈ A₁ := by
      intro x hx
      have h1 : π x = 1 := by
        have : e₀ (π x) = 1 := hx
        exact e₀.injective (by rw [this, map_one])
      have h2 : a x = 1 := congrArg Subtype.val h1
      rw [hab x, h2, one_mul]
      exact hb x
    have hk : CFSG.pPrimeCore 3 ↥π'.ker = ⊥ := by
      refine pPrimeCore_eq_bot_of_exponent fun g => ⟨1, ?_⟩
      have h1 := pow_card_eq_one' (G := ↥A₁) (x := ⟨ι g.1, hker g.1 g.2⟩)
      rw [hcard₁] at h1
      have h2 := congrArg Subtype.val h1
      apply Subtype.ext
      apply hι
      simpa using h2
    let ρ : X →* ↥A₁ :=
      { toFun := fun x => ⟨b x, hb x⟩
        map_one' := by
          apply Subtype.ext
          have h1 : ι 1 = 1 := map_one ι
          have := unique_decomp hc.disjoint (ha 1) A₀.one_mem (hb 1) A₁.one_mem
            (by rw [← hab, h1, mul_one])
          exact this.2
        map_mul' := by
          intro x y
          apply Subtype.ext
          have h1 : ι (x * y) = ι x * ι y := map_mul ι x y
          have := unique_decomp hc.disjoint (ha (x * y)) (A₀.mul_mem (ha x) (ha y))
            (hb (x * y)) (A₁.mul_mem (hb x) (hb y))
            (by rw [← hab, h1, hab x, hab y, hcomm'])
          exact this.2 }
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    haveI : IsCyclic ↥A₁ := isCyclic_of_prime_card hcard₁
    have hLρ : ∀ x ∈ L, ρ x = 1 := by
      intro x hx
      have h1 : x ∈ ⁅L, L⁆ := by rw [Subgroup.isPerfect_iff.1 hLp]; exact hx
      have h2 : x ∈ commutator X := by
        rw [commutator_def]
        exact Subgroup.commutator_mono le_top le_top h1
      exact Abelianization.commutator_subset_ker ρ h2
    have hLa : ∀ x ∈ L, a x = ι x := by
      intro x hx
      have h1 : b x = 1 := congrArg Subtype.val (hLρ x hx)
      rw [hab x, h1, mul_one]
    let f : ↥L →* StatedSp 3 (ZMod 2) := π'.comp L.subtype
    have hf : Function.Injective f := by
      intro x y hxy
      have h1 : π (x : X) = π (y : X) := e₀.injective hxy
      have h2 : a (x : X) = a (y : X) := congrArg Subtype.val h1
      rw [hLa _ x.2, hLa _ y.2] at h2
      exact Subtype.ext (hι h2)
    have hfr : Nat.card f.range = Nat.card ↥L := (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
    have hfle : f.range ≤ π'.range := by
      rintro _ ⟨x, rfl⟩
      exact ⟨x.1, rfl⟩
    have h81 : 81 ∣ Nat.card ↥π'.range := by
      have h1 : Nat.card f.range ∣ Nat.card ↥π'.range := Subgroup.card_dvd_of_le hfle
      rw [hfr] at h1
      exact (show 81 ∣ 25920 by norm_num).trans (hL.trans h1)
    have hr : CFSG.pPrimeCore 3 ↥π'.range = ⊥ := U4Sp6.pPrimeCore_eq_bot_of_dvd _ h81
    exact pPrimeCore_eq_bot_of_ker_range π' hk hr
  ·
    exfalso
    have hs₀ : s₀ = 2 := by omega
    subst hs₀
    obtain ⟨-, e₀⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨e₀⟩ := e₀
    have hcard₀ : Nat.card ↥A₀ = 720 := by
      rw [Nat.card_congr e₀.toEquiv]; exact card_sp_two
    rw [hA₁, card_unitary_two hE hsymm hsep hdim, hcard₀] at hbound
    omega
  ·
    exfalso
    have hs₀ : s₀ = 1 := by omega
    subst hs₀
    obtain ⟨-, e₀⟩ := hc.fixed.resolve_left (by omega)
    obtain ⟨e₀⟩ := e₀
    have hcard₀ : Nat.card ↥A₀ = 6 := by
      rw [Nat.card_congr e₀.toEquiv]; exact card_sp_one
    rw [hA₁, card_unitary_three hE hsymm hsep hdim, hcard₀] at hbound
    omega
  ·
    have hs₀ : s₀ = 0 := by omega
    subst hs₀
    have hA₀ : A₀ = ⊥ := (hc.fixed.resolve_right (by omega)).2
    have hXA : ∀ x, ι x ∈ A₁ := fun x => by
      have := hCX x
      rwa [hA₀, bot_sup_eq] at this
    let ι₁ : X →* sesqUnitaryGroup Hf :=
      e₁.toMonoidHom.comp (ι.codRestrict A₁ hXA)
    have hι₁ : Function.Injective ι₁ := by
      refine e₁.injective.comp ?_
      intro x y hxy
      exact hι (congrArg Subtype.val hxy)
    exact pPrimeCore_of_unitary_four hE hsymm hsep hdim ι₁ hι₁ L hLp hL

end CFSG.LocalAnalysis.GLTheoremA.CatB.U4Sp8

end
