module

public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseSetup
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.CloseProd
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.InvolutoryAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.RuStd.S2.U43FixNine

public section

namespace CFSG.EvenSporadicStandard.RuStd.S2.Close

open Subgroup
open scoped commutatorElement

section Fix

variable {X : Type} [Group X] [Finite X]

private theorem oddCore_map_eq (α : MulAut X) :
    (CFSG.oddCore X).map α.toMonoidHom = CFSG.oddCore X := by
  have hle : (CFSG.oddCore X).map α.toMonoidHom ≤ CFSG.oddCore X := by
    refine le_sSup ⟨Subgroup.Normal.map inferInstance _ α.surjective, ?_⟩
    rw [Subgroup.card_map_of_injective α.injective]
    exact odd_card_oddCore X
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Subgroup.card_map_of_injective α.injective])

theorem nine_dvd_card_fix
    {N : Subgroup (X ⧸ CFSG.oddCore X)} (hN : N.Normal)
    (e : ↥N ≃* U43) (hC : ∀ x : X ⧸ CFSG.oddCore X, (∀ n ∈ N, x * n = n * x) → x = 1)
    (α : MulAut X) (hα : α * α = 1) :
    9 ∣ Nat.card {q : X // q ∈ ⁅N.comap (proj X), N.comap (proj X)⁆ ∧ α q = q} := by
  haveI := hN
  have hNS := u43_nonabSimple e
  have hπs := proj_surjective X
  set O := CFSG.oddCore X with hO
  set N₁ : Subgroup X := N.comap (proj X) with hN₁
  set Q : Subgroup X := ⁅N₁, N₁⁆ with hQ
  have hαα : ∀ x, α (α x) = x := fun x => by
    simpa using congrArg (fun σ : MulAut X => σ x) hα
  have hQN : Q.map (proj X) = N := by
    rw [hQ, Subgroup.map_commutator, hN₁, Subgroup.map_comap_eq_self_of_surjective hπs]
    exact hNS.perfect
  obtain ⟨ᾱ, hᾱ⟩ : ∃ ᾱ : MulAut (X ⧸ O), ∀ x : X, ᾱ (proj X x) = proj X (α x) :=
    ⟨QuotientGroup.congr O O α (oddCore_map_eq α), fun x => rfl⟩
  have hᾱᾱ : ∀ y : X ⧸ O, ᾱ (ᾱ y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := hπs y
    rw [hᾱ, hᾱ, hαα]
  have hNα : ∀ n ∈ N, ᾱ n ∈ N := fun n hn => by
    have h := map_eq_of_simple N hNS.1 hC ᾱ
    exact h ▸ Subgroup.mem_map_of_mem _ hn
  have hN₁α : ∀ x ∈ N₁, α x ∈ N₁ := fun x hx => by
    rw [hN₁, Subgroup.mem_comap] at hx ⊢
    rw [← hᾱ]
    exact hNα _ hx
  have hQα : ∀ q ∈ Q, α q ∈ Q := by
    have h : Q.map α.toMonoidHom ≤ Q := by
      rw [hQ, Subgroup.map_commutator]
      have hle : N₁.map α.toMonoidHom ≤ N₁ := by
        rintro _ ⟨x, hx, rfl⟩
        exact hN₁α x hx
      exact Subgroup.commutator_mono hle hle
    exact fun q hq => h ⟨q, hq, rfl⟩
  have hZodd : ∀ z ∈ Q ⊓ O, Odd (orderOf z) := fun z hz =>
    Odd.of_dvd_nat (odd_card_oddCore X) (Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.1 hz).2)
  set P : Subgroup X := Q ⊓ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X) with hP
  have hPmem : ∀ y : X ⧸ O, y ∈ P.map (proj X) ↔ y ∈ N ∧ ᾱ y = y := by
    intro y
    constructor
    · rintro ⟨q, ⟨hqQ, hqα⟩, rfl⟩
      refine ⟨hQN ▸ Subgroup.mem_map_of_mem _ hqQ, ?_⟩
      rw [hᾱ]
      exact congrArg (proj X) hqα
    · rintro ⟨hyN, hyα⟩
      obtain ⟨q₀, hq₀, rfl⟩ : y ∈ Q.map (proj X) := hQN ▸ hyN
      have h1 : (QuotientGroup.mk q₀ : X ⧸ O) = QuotientGroup.mk (α q₀) := by
        have := hyα
        rw [hᾱ] at this
        exact this.symm
      have h2 : q₀⁻¹ * α q₀ ∈ O := QuotientGroup.eq.1 h1
      have h3 : q₀⁻¹ * α q₀ ∈ Q ⊓ O :=
        Subgroup.mem_inf.2 ⟨Q.mul_mem (Q.inv_mem hq₀) (hQα q₀ hq₀), h2⟩
      obtain ⟨z, hz, hfix⟩ := exists_fix_of_fix_mod (Q ⊓ O) hZodd α hαα q₀ h3
      refine ⟨q₀ * z, Subgroup.mem_inf.2 ⟨Q.mul_mem hq₀ (Subgroup.mem_inf.1 hz).1, hfix⟩, ?_⟩
      rw [map_mul, show proj X z = 1 from (QuotientGroup.eq_one_iff z).2 (Subgroup.mem_inf.1 hz).2,
        mul_one]
  obtain ⟨γ, hγγ, hγ⟩ := exists_restrict_involution N ᾱ hᾱᾱ hNα
  have hU := nine_dvd_card_fix_of_mulEquiv e γ hγγ
  have hcardF : Nat.card {n : N // γ n = n} = Nat.card ↥(P.map (proj X)) :=
    Nat.card_congr
      { toFun := fun n => ⟨(n.1 : X ⧸ O), (hPmem _).2 ⟨n.1.2, by
          rw [← hγ]; exact congrArg Subtype.val n.2⟩⟩
        invFun := fun y => ⟨⟨y.1, ((hPmem y.1).1 y.2).1⟩, Subtype.ext (by
          rw [hγ]; exact ((hPmem y.1).1 y.2).2)⟩
        left_inv := fun n => rfl
        right_inv := fun y => rfl }
  have hcardP : Nat.card P = Nat.card {q : X // q ∈ Q ∧ α q = q} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun q => Iff.rfl)
  rw [hcardF] at hU
  rw [← hcardP]
  exact hU.trans (Subgroup.card_map_dvd (H := P) (proj X))

end Fix

end CFSG.EvenSporadicStandard.RuStd.S2.Close
