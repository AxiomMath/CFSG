module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29First
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29S1D
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L29Sylow

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.ABGLocalTools CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage12

section Lift

variable {G : Type} [Group G] [Finite G] {z : G}

theorem sylow_O2_centralizer_of_bar {U : Subgroup G} {u : G} (hzU : z ∈ U) (huU : u ∈ U)
    (hu : u ∈ Cen z)
    (hE : ∀ S : Sylow 2 ↥(O2Of (centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)))),
      IsCyclic ↥S ∨ IsDihedral ↥S) :
    ∀ P : Sylow 2 ↥(O2Of (centralizer (U : Set G))), IsCyclic ↥P ∨ IsDihedral ↥P := by
  have hle : centralizer (U : Set G) ≤ Cen z := by
    intro g hg
    show g ∈ centralizer ({z} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp hg z hzU).symm
  let f0 : ↥(centralizer (U : Set G)) →* CentralizerBar z :=
    (toBar z).comp (Subgroup.inclusion hle)
  have hrange : ∀ g : ↥(centralizer (U : Set G)),
      f0 g ∈ centralizer ({toBar z ⟨u, hu⟩} : Set (CentralizerBar z)) := by
    intro g
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgu : (g : G) * u = u * g := (Subgroup.mem_centralizer_iff.mp g.2 u huU).symm
    show toBar z (Subgroup.inclusion hle g) * toBar z ⟨u, hu⟩ =
      toBar z ⟨u, hu⟩ * toBar z (Subgroup.inclusion hle g)
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hgu
  have hodd : Odd (Nat.card f0.ker) := by
    let φ : ↥f0.ker →* ↥(toBar z).ker :=
      ((Subgroup.inclusion hle).comp f0.ker.subtype).codRestrict (toBar z).ker fun g => g.2
    have hinj : Function.Injective φ := by
      intro a b hab
      apply Subtype.ext
      apply Subgroup.inclusion_injective hle
      exact congrArg (fun t : ↥(toBar z).ker => (t : ↥(Cen z))) hab
    have hdvd : Nat.card f0.ker ∣ Nat.card (toBar z).ker :=
      Subgroup.card_dvd_of_injective φ hinj
    have hodd0 : Odd (Nat.card (toBar z).ker) := by
      rw [show (toBar z).ker = pPrimeCore 2 ↥(Cen z) from QuotientGroup.ker_mk' _]
      exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
    exact Odd.of_dvd_nat hodd0 hdvd
  intro P
  exact cyclic_or_dihedral_of_odd_ker (centralizer (U : Set G)) _ f0 hodd hrange hE P

theorem lemma29Alt_of_swap_pair {k : Kind} (hk : IsClassicalKind k) (hz1 : z ≠ 1) {q : ℕ}
    {L₁ L₂ : Subgroup (CentralizerBar z)} (hp : PairShape z q q L₁ L₂) {u : G} (hu : u ∈ Cen z)
    (hu2 : u * u = 1) (hu1 : u ∉ zpowers z) (hsw : Swaps z u L₁ L₂) {U : Subgroup G}
    (hU : IVK.IsFourSubgroup U) (hzU : z ∈ U) (huU : u ∈ U) : Lemma29Alt z k U := by
  have hbar2 : toBar z ⟨u, hu⟩ * toBar z ⟨u, hu⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, hu⟩ * ⟨u, hu⟩ : ↥(Cen z)) = 1 := Subtype.ext hu2
    rw [this, map_one]
  have hinv : (toBar z ⟨u, hu⟩)⁻¹ = toBar z ⟨u, hu⟩ := inv_eq_of_mul_eq_one_right hbar2
  obtain ⟨ht, h1, h2⟩ := id hsw
  have h₁₂ : L₁.map (MulAut.conj (toBar z ⟨u, hu⟩)).toMonoidHom = L₂ := by
    have h1' : L₁.map (MulAut.conj (toBar z ⟨u, ht⟩)⁻¹).toMonoidHom = L₂ := h1
    rwa [hinv] at h1'
  have h₂₁ : L₂.map (MulAut.conj (toBar z ⟨u, hu⟩)).toMonoidHom = L₁ := by
    have h2' : L₂.map (MulAut.conj (toBar z ⟨u, ht⟩)⁻¹).toMonoidHom = L₁ := h2
    rwa [hinv] at h2'
  have hE := sylow_O2_swap_cyclic_or_dihedral (H := CentralizerBar z) hp.ne hp.comps
    hp.prod.2.1 hp.prod.2.2 (centralizer_pair_le_inf hp) hp.odd₁ hp.gt₁ hp.sl₁ hp.sl₂ hbar2 h₁₂
    h₂₁
  have hdc := sylow_O2_centralizer_of_bar hzU huU hu hE
  have hUeq : zpowers z ⊔ zpowers u = U := eq_zpowers_sup_of_mem hU hzU huU hz1 hu1
  refine lemma29Alt_of_cyclic_or_dihedral hk hdc (Or.inr ⟨u, 1, ⟨L₁, L₂, hp.ne, hp.comps, hsw⟩, ?_⟩)
  show (zpowers z ⊔ zpowers u).map (MulAut.conj (1 : G)⁻¹).toMonoidHom = U
  rw [← hUeq]
  ext y
  simp

end Lift

theorem l29OneClassSwap_proved : L29OneClassSwap := by
  intro G _ _ z S ε ctx q L₁ L₂ hq _ u _ hu hu2 hu1 hsw U hU hzU huU
  have hz1 : z ≠ 1 := by
    intro h
    have := ctx.central.1
    rw [h, orderOf_one] at this
    omega
  exact lemma29Alt_of_swap_pair (Or.inr ⟨ε, rfl⟩) hz1 (PairShape.of_pair hq.pair) hu hu2 hu1 hsw hU
    hzU huU

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
