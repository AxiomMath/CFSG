module

public import CFSG.GH74.Generic.BProg.B3.LocBalSL4Three
public import CFSG.GH74.Generic.BProg.B1.PilotS1ThreeFacts

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.Blueprint CFSG.Assembly.Dichotomy CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.Generic.BProg.B1.PilotS1
open scoped commutatorElement

namespace LocBalSL4ThreeMain

open LocBalSL4Abs LocBalSL4Three

variable {P : Type} [Group P]

theorem hP_three [Finite P] {F : Type} [Field F] [Finite F] {z : P} (hF3 : Nat.card F = 3)
    (hG : GrpS1 F P z)
    (hZ : ∀ x : P ⧸ Subgroup.center P, (∀ g : P ⧸ Subgroup.center P, g * x = x * g) → x = 1)
    {u : P} (hu2 : u * u = 1) (hπu : QuotientGroup.mk' (Subgroup.center P) u ≠ 1)
    {H : Subgroup (MulAut (P ⧸ Subgroup.center P))}
    (hH : (MulAut.conj : (P ⧸ Subgroup.center P) →* MulAut (P ⧸ Subgroup.center P)).range ≤ H)
    {c : ↥H}
    (hc : c ∈ involutionOddCore (phi hH (QuotientGroup.mk' (Subgroup.center P) u)))
    {w : P ⧸ Subgroup.center P}
    (hw : w ∈ (Subgroup.centralizer ({u} : Set P)).map (QuotientGroup.mk' (Subgroup.center P))) :
    ((c : ↥H) : MulAut (P ⧸ Subgroup.center P)) w = w := by
  let π : P →* P ⧸ Subgroup.center P := QuotientGroup.mk' (Subgroup.center P)
  have hker : ∀ g : P, π g = 1 ↔ g = 1 ∨ g = z := fun g => by
    show QuotientGroup.mk' (Subgroup.center P) g = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hG.center g
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hG.like.z_ord, sq] at h
    exact h
  have hz1 : z ≠ 1 := by
    intro h
    have := hG.like.z_ord
    rw [h, orderOf_one] at this
    omega
  have hzc : ∀ g : P, g * z = z * g := fun g => hG.like.z_central g (Subgroup.mem_top g)
  have hu1 : u ≠ 1 := fun h => hπu (by rw [h, map_one])
  have huz : u ≠ z := fun h => hπu ((hker u).2 (Or.inr h))
  have hord : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  obtain ⟨J₁, J₂, hS⟩ := hG.like.split u (Subgroup.mem_top u) hord huz
  have hO0 := hS.pPrimeCore_eq_bot_three hF3
  have hO : ∀ R : Subgroup P, R ≤ centralizer ({u} : Set P) →
      (∀ g ∈ centralizer ({u} : Set P), ∀ r ∈ R, g * r * g⁻¹ ∈ R) → Odd (Nat.card ↥R) → R = ⊥ := by
    intro R hRC hRn hRo
    have hC : centralizer ({u} : Set P) ⊓ ⊤ = centralizer ({u} : Set P) := inf_top_eq _
    have hRC' : R ≤ centralizer ({u} : Set P) ⊓ ⊤ := fun r hr => ⟨hRC hr, trivial⟩
    let R' : Subgroup ↥(centralizer ({u} : Set P) ⊓ ⊤) := R.subgroupOf _
    have hR'n : R'.Normal := ⟨fun n hn g => by
      show ((g * n * g⁻¹ : ↥(centralizer ({u} : Set P) ⊓ ⊤)) : P) ∈ R
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hRn _ g.2.1 _ hn⟩
    have hcard : Nat.card ↥R' = Nat.card ↥R :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRC').toEquiv
    have hle : R' ≤ pPrimeCore 2 ↥(centralizer ({u} : Set P) ⊓ ⊤) :=
      le_sSup ⟨hR'n, Nat.coprime_two_left.2 (hcard ▸ hRo)⟩
    rw [hO0, le_bot_iff] at hle
    rw [eq_bot_iff]
    intro r hr
    have : (⟨r, hRC' hr⟩ : ↥(centralizer ({u} : Set P) ⊓ ⊤)) ∈ R' := hr
    rw [hle, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  obtain ⟨Q, hQC, hQn, hQo, hzmem⟩ := twist_mem hZ hH hc
  have hQ : Q = ⊥ :=
    Q_eq_bot (π := π) (QuotientGroup.mk'_surjective _) hzc hz2 hz1 hker hO hQC hQn hQo
  obtain ⟨g, hg, rfl⟩ := hw
  have hπg : π g ∈ centralizer ({π u} : Set (P ⧸ Subgroup.center P)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp hg]
  have h1 := hzmem (π g) hπg
  rw [hQ, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem locBal32_of_grpS1_three [Finite P] {F : Type} [Field F] [Finite F] {z : P}
    (hF3 : Nat.card F = 3) (hG : GrpS1 F P z) (hq : CFSG.IsQuasisimple P)
    (hgen : ∀ Ab : Subgroup P, CFSG.IsElementaryAbelian 2 ↥Ab → Nat.card ↥Ab = 8 →
      (⨆ (b : P) (_ : b ∈ Ab ∧ b ∉ Subgroup.center P), centralizer ({b} : Set P)) = ⊤)
    {Ab : Subgroup P} (hAe : CFSG.IsElementaryAbelian 2 ↥Ab) (hA8 : Nat.card ↥Ab = 8)
    (B : Subgroup (MulAut (P ⧸ Subgroup.center P)))
    (hB : B ≤ (Ab.map (QuotientGroup.mk' (Subgroup.center P))).map
      (MulAut.conj : (P ⧸ Subgroup.center P) →* MulAut (P ⧸ Subgroup.center P))) :
    IsLocBal32 (P ⧸ Subgroup.center P) B := by
  have hZ := centerless_quotient_of_quasisimple hq
  have hmk : ∀ b : P, QuotientGroup.mk' (Subgroup.center P) b ≠ 1 ↔ b ∉ Subgroup.center P :=
    fun b => by
      rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hG.like.z_ord, sq] at h
    exact h
  have hz1 : z ≠ 1 := by
    intro h
    have := hG.like.z_ord
    rw [h, orderOf_one] at this
    omega
  have hzA : z ∈ Ab := hG.e8 Ab hAe hA8
  have hπz : QuotientGroup.mk' (Subgroup.center P) z = 1 := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hG.center]
    exact Or.inr rfl
  refine locBal32_of_fix (QuotientGroup.mk' (Subgroup.center P)) (QuotientGroup.mk'_surjective _) hZ
    hAe hA8 hzA hz1 hπz ?_ ?_ B hB
  · have h := hgen Ab hAe hA8
    simp only [hmk]
    exact h
  · intro u huA hπu H hH c hc w hw
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hu2 : u * u = 1 := by
      rw [← pow_two]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Ab) u huA
    exact hP_three hF3 hG hZ hu2 hπu hH hc hw

end LocBalSL4ThreeMain

end CFSG.GH74.Generic.BProg.B3
