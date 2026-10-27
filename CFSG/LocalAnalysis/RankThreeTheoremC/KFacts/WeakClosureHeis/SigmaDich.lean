module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.WeakClosureHeis.FamilyTools
public import CFSG.GroupTheory.WeirSylow.Defs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis

open CFSG.GroupTheory.WeirSylow

namespace SigmaDich

def baseHom (D Q : Type*) [Group D] [Group Q] : (Q → D) →* D ≀ᵣ Q where
  toFun f := ⟨f, 1⟩
  map_one' := rfl
  map_mul' f g := by ext <;> simp [RegularWreathProduct.mul_def]

theorem baseHom_injective (D Q : Type*) [Group D] [Group Q] :
    Function.Injective (baseHom D Q) := fun _ _ h => congrArg RegularWreathProduct.left h

theorem exists_elemAbelian_of_injective {p k : ℕ} {G A : Type*} [Group G] [Group A]
    [IsMulCommutative A] (hA : ∀ x : A, x ^ p = 1) (hcard : Nat.card A = p ^ k)
    (Ψ : A →* G) (hΨ : Function.Injective Ψ) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ k := by
  refine ⟨Ψ.range, ⟨inferInstance, ?_⟩, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [← map_pow, hA x, map_one]
  · rw [← hcard]
    exact Nat.card_congr (Equiv.ofInjective Ψ hΨ).symm

theorem exists_elemAbelian_wreath {p : ℕ} (hp : p.Prime) {D : Type*} [Group D] [Finite D]
    (hdvd : p ∣ Nat.card D) :
    ∃ E : Subgroup (D ≀ᵣ Multiplicative (ZMod p)),
      CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ p := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hgp : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
  have hZcard : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hg]
  let Ψ : (Multiplicative (ZMod p) → Subgroup.zpowers g) →* D ≀ᵣ Multiplicative (ZMod p) :=
    (baseHom D _).comp (MonoidHom.compLeft (Subgroup.zpowers g).subtype _)
  have hΨ : Function.Injective Ψ := by
    refine (baseHom_injective D _).comp ?_
    intro f f' h
    funext x
    exact Subtype.ext (congrFun h x)
  have key : ∀ z : Subgroup.zpowers g, z ^ p = 1 := by
    rintro ⟨z, hz⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgp,
      one_zpow]
    rfl
  refine exists_elemAbelian_of_injective ?_ ?_ Ψ hΨ
  · intro f
    funext x
    exact key (f x)
  · rw [Nat.card_fun, hZcard, Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]

theorem towerExp_pos {p a : ℕ} (ha : 1 ≤ a) : ∀ n, 1 ≤ towerExp p a n
  | 0 => ha
  | n + 1 => by rw [towerExp_succ]; omega

theorem exists_elemAbelian_wreathTower {p : ℕ} (hp : p.Prime) {a : ℕ} (ha : 1 ≤ a) :
    ∀ n : ℕ, 1 ≤ n →
      ∃ E : Subgroup (wreathTower p (Multiplicative (ZMod (p ^ a))) n),
        CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ p := by
  intro n hn
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero a hp.ne_zero⟩
  have hC : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hD := card_wreathTower p (Multiplicative (ZMod (p ^ a))) hC n'
  have hdvd : p ∣ Nat.card (wreathTower p (Multiplicative (ZMod (p ^ a))) n') := by
    rw [hD]
    exact dvd_pow_self p (by have := towerExp_pos (p := p) ha n'; omega)
  exact exists_elemAbelian_wreath (D := wreathTower p (Multiplicative (ZMod (p ^ a))) n') hp hdvd

def sigmaEmbed (p e a N : ℕ) (i : Fin (Nat.digits p (N / e)).length)
    (j : Fin (Nat.digits p (N / e))[i]) :
    wreathTower p (Multiplicative (ZMod (p ^ a))) i →* sigmaModel p e a N :=
  (MonoidHom.mulSingle (fun i : Fin (Nat.digits p (N / e)).length =>
      Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i) i).comp
    (MonoidHom.mulSingle
      (fun _ : Fin (Nat.digits p (N / e))[i] => wreathTower p (Multiplicative (ZMod (p ^ a))) i) j)

theorem sigmaEmbed_injective (p e a N : ℕ) (i : Fin (Nat.digits p (N / e)).length)
    (j : Fin (Nat.digits p (N / e))[i]) : Function.Injective (sigmaEmbed p e a N i j) :=
  (Pi.mulSingle_injective (M := fun i : Fin (Nat.digits p (N / e)).length =>
      Fin (Nat.digits p (N / e))[i] → wreathTower p (Multiplicative (ZMod (p ^ a))) i) i).comp
    (Pi.mulSingle_injective
      (M := fun _ : Fin (Nat.digits p (N / e))[i] =>
        wreathTower p (Multiplicative (ZMod (p ^ a))) i) j)

theorem sigmaModel_comm {p a : ℕ} (e N : ℕ) (hL : (Nat.digits p (N / e)).length ≤ 1)
    (x y : sigmaModel p e a N) : x * y = y * x := by
  have comm0 : ∀ n : ℕ, n = 0 → ∀ u v : wreathTower p (Multiplicative (ZMod (p ^ a))) n,
      u * v = v * u := by
    rintro n rfl u v
    exact mul_comm (G := Multiplicative (ZMod (p ^ a))) u v
  funext i j
  have hi : (i : ℕ) = 0 := by have := i.2; omega
  exact comm0 (i : ℕ) hi (x i j) (y i j)

end SigmaDich

theorem sylow_isMulCommutative_of_sigmaModel_of_lt {p : ℕ} (hp : p.Prime) {G : Type} [Group G]
    [Finite G] {e a N : ℕ} (hlt : N / e < p)
    (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N)) :
    ∀ P : Sylow p G, IsMulCommutative (P : Subgroup G) := by
  intro S
  obtain ⟨φ⟩ := h S
  have hL : (Nat.digits p (N / e)).length ≤ 1 := by
    rw [Nat.digits_length_le_iff hp.one_lt]
    simpa using hlt
  exact ⟨⟨fun x y => φ.injective (by
    rw [map_mul, map_mul]
    exact SigmaDich.sigmaModel_comm e N hL _ _)⟩⟩

theorem SylowDichotomyAt.of_sylow_sigmaModel {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) {G : Type}
    [Group G] [Finite G] {e a N : ℕ} (ha : 1 ≤ a)
    (h : ∀ P : Sylow p G, Nonempty (P ≃* sigmaModel p e a N)) : SylowDichotomyAt G p := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_cases hm : N / e < p
  ·
    exact SylowDichotomyAt.of_sylow_comm (sylow_isMulCommutative_of_sigmaModel_of_lt hp hm h)
  ·
    push Not at hm
    have hL : 1 < (Nat.digits p (N / e)).length := by
      rw [Nat.lt_digits_length_iff hp.one_lt]
      simpa using hm
    have hne : N / e ≠ 0 := by omega
    let i₁ : Fin (Nat.digits p (N / e)).length := ⟨(Nat.digits p (N / e)).length - 1, by omega⟩
    have hi₁ : 1 ≤ (i₁ : ℕ) := by
      show 1 ≤ (Nat.digits p (N / e)).length - 1
      omega
    have hpos : 0 < (Nat.digits p (N / e))[i₁] := by
      have hlast := Nat.getLast_digit_ne_zero p hne
      have heq : (Nat.digits p (N / e))[i₁] =
          (Nat.digits p (N / e)).getLast (Nat.digits_ne_nil_iff_ne_zero.mpr hne) := by
        rw [List.getLast_eq_getElem]
        rfl
      rw [heq]
      exact Nat.pos_of_ne_zero hlast
    let j₁ : Fin (Nat.digits p (N / e))[i₁] := ⟨0, hpos⟩
    obtain ⟨E, hE, hEcard⟩ := SigmaDich.exists_elemAbelian_wreathTower hp ha i₁ hi₁
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p G))
    obtain ⟨φ⟩ := h S
    let Ψ : wreathTower p (Multiplicative (ZMod (p ^ a))) i₁ →* G :=
      (S : Subgroup G).subtype.comp (φ.symm.toMonoidHom.comp (SigmaDich.sigmaEmbed p e a N i₁ j₁))
    have hΨ : Function.Injective Ψ :=
      Subtype.coe_injective.comp
        (φ.symm.injective.comp (SigmaDich.sigmaEmbed_injective p e a N i₁ j₁))
    exact SylowDichotomyAt.of_elemAbelian hp ((isElemAbelian_map_iff_of_injective Ψ hΨ E).2 hE)
      (k := p) (by rw [Subgroup.card_map_of_injective hΨ]; exact hEcard) (by omega)

end CFSG.LocalAnalysis.RankThreeTheoremC.WeakClosureHeis
