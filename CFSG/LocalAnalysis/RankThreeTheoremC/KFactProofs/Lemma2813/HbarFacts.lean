module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Bridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813.Offender

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813

open CFSG.Open Subgroup CFSG.QuasithinUnique.Setup.Family
open scoped Pointwise

section B

variable {A : Type} [Group A] [Finite A] {X K R P : Subgroup A}

theorem Hbar_mono (X : Subgroup A) (ψ : ↥X →* GL32) {H₁ H₂ : Subgroup A} (h : H₁ ≤ H₂) :
    Hbar X ψ H₁ ≤ Hbar X ψ H₂ :=
  Subgroup.map_mono (Subgroup.comap_mono h)

theorem Hbar_isPGroup (X : Subgroup A) (ψ : ↥X →* GL32) {S : Subgroup A} (hS : IsPGroup 2 S) :
    IsPGroup 2 (Hbar X ψ S) :=
  hS.comap_subtype.map ψ

theorem Hbar_ne_bot (X : Subgroup A) {ψ : ↥X →* GL32}
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) {A₀ : Subgroup A} (hA₀X : A₀ ≤ X)
    (hA₀Q : ¬ A₀ ≤ pCoreOf 2 X) : Hbar X ψ A₀ ≠ ⊥ := by
  obtain ⟨a, ha, haQ⟩ := SetLike.not_le_iff_exists.1 hA₀Q
  intro hbot
  have hmem : ψ ⟨a, hA₀X ha⟩ ∈ Hbar X ψ A₀ :=
    Subgroup.mem_map_of_mem ψ (Subgroup.mem_subgroupOf.2 ha)
  rw [hbot, Subgroup.mem_bot] at hmem
  have hker : (⟨a, hA₀X ha⟩ : ↥X) ∈ ψ.ker := hmem
  rw [hψk, Subgroup.mem_subgroupOf] at hker
  exact haQ hker

theorem dbar_order (X : Subgroup A) {ψ : ↥X →* GL32} (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X)
    {d₀ : A} (hd₀X : d₀ ∈ X) (hd₀3 : orderOf d₀ = 3) : orderOf (ψ ⟨d₀, hd₀X⟩) = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : (⟨d₀, hd₀X⟩ : ↥X) ^ 3 = 1 :=
    Subtype.ext (by simpa [← hd₀3] using pow_orderOf_eq_one d₀)
  have h3 : ψ ⟨d₀, hd₀X⟩ ^ 3 = 1 := by
    rw [← map_pow, hcube, map_one]
  have h1 : ψ ⟨d₀, hd₀X⟩ ≠ 1 := by
    intro h1
    have hker : (⟨d₀, hd₀X⟩ : ↥X) ∈ ψ.ker := h1
    rw [hψk, Subgroup.mem_subgroupOf] at hker
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 (isPGroup_pCoreOf X)) ⟨d₀, hker⟩
    rw [Subgroup.orderOf_mk, hd₀3] at hk
    have h3k : 3 ∣ 2 ^ k := by
      rw [← hk]
    have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3k
    omega
  exact orderOf_eq_prime h3 h1

theorem dbar_mem_normalizer (X : Subgroup A) (ψ : ↥X →* GL32) {P : Subgroup A} (hPX : P ≤ X)
    {d₀ : A} (hd₀P : d₀ ∈ P) :
    ψ ⟨d₀, hPX hd₀P⟩ ∈ normalizer (Hbar X ψ (pCoreOf 2 P) : Set GL32) := by
  have key : ∀ g : A, ∀ hg : g ∈ P, ∀ y ∈ Hbar X ψ (pCoreOf 2 P),
      ψ ⟨g, hPX hg⟩ * y * (ψ ⟨g, hPX hg⟩)⁻¹ ∈ Hbar X ψ (pCoreOf 2 P) := by
    intro g hg y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    refine Subgroup.mem_map.2 ⟨⟨g, hPX hg⟩ * s * ⟨g, hPX hg⟩⁻¹, ?_, by simp [map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    have := (Subgroup.mem_normalizer_iff.1 (normalizer_pCoreOf P hg) (s : A)).1 hs
    simpa using this
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key d₀ hd₀P y
  · intro hy
    have := key (d₀⁻¹) (P.inv_mem hd₀P) _ hy
    have e : ψ ⟨d₀⁻¹, hPX (P.inv_mem hd₀P)⟩ = (ψ ⟨d₀, hPX hd₀P⟩)⁻¹ := by
      rw [← map_inv]
      rfl
    rw [e] at this
    simpa [mul_assoc] using this

theorem hb_card_Hbar (X : Subgroup A) {ψ : ↥X →* GL32}
    (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X) {A₀ : Subgroup A} (hA₀X : A₀ ≤ X) :
    Nat.card (Hbar X ψ A₀) * Nat.card ↥(A₀ ⊓ pCoreOf 2 X) = Nat.card A₀ := by
  have h1 := Subgroup.card_ker_mul_card_range (ψ.domRestrict (A₀.subgroupOf X))
  rw [MonoidHom.domRestrict_range, MonoidHom.ker_domRestrict] at h1
  have h2 : Nat.card ↥(ψ.ker.subgroupOf (A₀.subgroupOf X)) = Nat.card ↥(A₀ ⊓ pCoreOf 2 X) := by
    rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective (A₀.subgroupOf X)),
      Subgroup.subgroupOf_map_subtype, hψk]
    have h3 : (pCoreOf 2 X).subgroupOf X ⊓ A₀.subgroupOf X = (A₀ ⊓ pCoreOf 2 X).subgroupOf X := by
      ext x
      simp [Subgroup.mem_subgroupOf, and_comm]
    rw [h3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hA₀X)).toEquiv
  have h4 : Nat.card ↥(A₀.subgroupOf X) = Nat.card A₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA₀X).toEquiv
  rw [h2, h4] at h1
  rw [← h1, mul_comm]
  rfl

section TR

variable {ψ : ↥X →* GL32} {N : Type} [AddCommGroup N] [DistribMulAction GL32 N]
  {ι : ↥(TT X) → N}

theorem hb_card_inf_le [Finite N] (hι : IsTBridge X ψ ι) {A₀ : Subgroup A} (hA₀X : A₀ ≤ X)
    (hAc : IsMulCommutative A₀) :
    Nat.card ↥(A₀ ⊓ TT X) ≤ Nat.card (fixSub N (Hbar X ψ A₀)) := by
  have hmem : ∀ a : ↥(A₀ ⊓ TT X),
      ι ⟨(a : A), (Subgroup.mem_inf.1 a.2).2⟩ ∈ fixSub N (Hbar X ψ A₀) := by
    intro a
    rw [hι.mem_fixSub_iff hA₀X]
    intro x hx
    have := hAc.is_comm.comm ⟨x, hx⟩ ⟨(a : A), (Subgroup.mem_inf.1 a.2).1⟩
    exact congrArg Subtype.val this
  refine Nat.card_le_card_of_injective
    (fun a => ⟨ι ⟨(a : A), (Subgroup.mem_inf.1 a.2).2⟩, hmem a⟩) ?_
  intro a b hab
  have h1 := hι.bij.1 (Subtype.mk.inj hab)
  exact Subtype.ext (Subtype.mk.inj h1)

end TR

theorem Hyp2813.offender_N (h : Hyp2813 X K R P) (hS : pCoreOf 2 P ≠ ⊥) {ψ : ↥X →* GL32}
    (hψs : Function.Surjective ψ) (hψk : ψ.ker = (pCoreOf 2 X).subgroupOf X)
    {N : Type} [AddCommGroup N] [Finite N] [DistribMulAction GL32 N] {ι : ↥(TT X) → N}
    (hι : IsTBridge X ψ ι) {A₀ : Subgroup A}
    (hA : A₀ ∈ CFSG.thompsonAbelianSubgroups (pCoreOf 2 P)) :
    Nat.card N ≤ Nat.card (Hbar X ψ A₀) * Nat.card (fixSub N (Hbar X ψ A₀)) := by
  have _ := hψs
  have hAS : A₀ ≤ pCoreOf 2 P := hA.1
  have hAc : IsMulCommutative A₀ := hA.2.1
  have hA₀X : A₀ ≤ X := hAS.trans ((pCoreOf_le_self P).trans h.P_le)
  have hineq := h.offender_ineq hS hA
  have h1 := hb_card_Hbar X hψk hA₀X
  have h2 := hb_card_inf_le hι hA₀X hAc
  have h3 : Nat.card N = Nat.card (TT X) := (Nat.card_congr (Equiv.ofBijective ι hι.bij)).symm
  have hq : 0 < Nat.card ↥(A₀ ⊓ pCoreOf 2 X) := Nat.card_pos
  rw [h3]
  rw [← h1] at hineq
  have h5 : Nat.card (TT X) ≤ Nat.card ↥(A₀ ⊓ TT X) * Nat.card (Hbar X ψ A₀) := by
    refine Nat.le_of_mul_le_mul_right ?_ hq
    calc Nat.card (TT X) * Nat.card ↥(A₀ ⊓ pCoreOf 2 X)
        ≤ Nat.card ↥(A₀ ⊓ TT X) * (Nat.card (Hbar X ψ A₀) * Nat.card ↥(A₀ ⊓ pCoreOf 2 X)) :=
          hineq
      _ = Nat.card ↥(A₀ ⊓ TT X) * Nat.card (Hbar X ψ A₀) * Nat.card ↥(A₀ ⊓ pCoreOf 2 X) := by
          ring
  calc Nat.card (TT X) ≤ Nat.card ↥(A₀ ⊓ TT X) * Nat.card (Hbar X ψ A₀) := h5
    _ ≤ Nat.card (fixSub N (Hbar X ψ A₀)) * Nat.card (Hbar X ψ A₀) := Nat.mul_le_mul_right _ h2
    _ = Nat.card (Hbar X ψ A₀) * Nat.card (fixSub N (Hbar X ψ A₀)) := mul_comm _ _

end B

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Lemma2813
