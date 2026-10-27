module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263DXSeed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

@[expose] def autComm {P : Type} [Group P] (𝔹 : Subgroup (MulAut P)) (Y : Subgroup P) : Subgroup P :=
  Subgroup.closure {z | ∃ b ∈ 𝔹, ∃ y ∈ Y, z = b y * y⁻¹}

@[expose] def FamSel (p : ℕ) (P : Type) [Group P] [Finite P] (inn : MulAut P → Prop) : Prop :=
  ∀ u : MulAut P, inn u → u ^ p = 1 → u ≠ 1 →
  ∀ 𝔹 : Subgroup (MulAut P), (∀ b ∈ 𝔹, inn b ∧ b ^ p = 1 ∧ b * u = u * b) →
  ∀ Y : Subgroup P, Y ≤ fixSubgroup u → IsPGroup 2 ↥Y → (∀ b ∈ 𝔹, Y.map b.toMonoidHom = Y) →
  autComm 𝔹 Y ≠ ⊥ →
  ∃ J : Subgroup P, IsComponentOf J (fixSubgroup u) ∧ p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) ∧
    ⁅autComm 𝔹 Y, J⁆ ≠ ⊥ ∧ autComm 𝔹 Y ≤ J ⊔ (fixSubgroup u ⊓ Subgroup.centralizer (J : Set P))

structure SDCore (p : ℕ) {Ω : Type} [Group Ω] [Finite Ω] (S B₀ T' : Subgroup Ω) (x : Ω)
    (J : Subgroup Ω) : Prop where
  comp : IsComponentOf J (S ⊓ Subgroup.centralizer ({x} : Set Ω))
  pdvd : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J)
  act : ⁅(⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω), J⁆ ≠ ⊥
  inn : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≤
    J ⊔ (S ⊓ Subgroup.centralizer ({x} : Set Ω) ⊓ Subgroup.centralizer (J : Set Ω))
  chev : IsChevSimple 2 (↥J ⧸ Subgroup.center ↥J)

theorem SDCore.toSelComp {p : ℕ} {Ω : Type} [Group Ω] [Finite Ω] {S B₀ T' : Subgroup Ω} {x : Ω}
    {J : Subgroup Ω} (h : SDCore p S B₀ T' x J)
    (hgf : p = 3 → ¬ GLAMarking (↥J) (fun lab _ _ _ _ _ => lab.n = 1)) :
    SelComp p S B₀ T' x J :=
  ⟨h.comp, h.pdvd, h.act, h.inn, h.chev, hgf⟩

theorem sd_center_two_trivial {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {G : Type} [Group G] [Finite G]
    (hG : GLAPPrimeCore p G = ⊥) {z : G} (hz : z ∈ Subgroup.center G) {k : ℕ}
    (hzk : z ^ (2 ^ k) = 1) : z = 1 := by
  have hpg : IsPGroup p (Subgroup.center G) :=
    CFSG.HardMathSupport.Solomon.Coordinator.isPGroup_center_of_pPrimeCore_eq_bot hp hG
  obtain ⟨m, hm⟩ := hpg ⟨z, hz⟩
  have hm' : z ^ (p ^ m) = 1 := congrArg Subtype.val hm
  have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
  have h2 : orderOf z ∣ p ^ m := orderOf_dvd_of_pow_eq_one hm'
  have hcop : Nat.Coprime (2 ^ k) (p ^ m) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
  have h3 : orderOf z ∣ Nat.gcd (2 ^ k) (p ^ m) := Nat.dvd_gcd h1 h2
  rw [hcop, Nat.dvd_one] at h3
  exact orderOf_eq_one_iff.1 h3

theorem sd_centFix_zpowers_eq {X : Type*} [Group X] (β : MulAut X) :
    CFSG.LocalAnalysis.GLTheoremA.I142.centFix (Subgroup.zpowers β) = fixSubgroup β := by
  ext x
  rw [CFSG.LocalAnalysis.GLTheoremA.I142.mem_centFix, mem_fixSubgroup]
  constructor
  · intro h
    exact h β (Subgroup.mem_zpowers β)
  · intro hx e he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have hβs : β ∈ MulAction.stabilizer (MulAut X) x := MulAction.mem_stabilizer_iff.2 hx
    exact MulAction.mem_stabilizer_iff.1 ((MulAction.stabilizer (MulAut X) x).zpow_mem hβs k)

theorem sd_center_eq_bot_of_simple {X : Type*} [Group X] (hs : IsSimpleGroup X)
    (hnc : ∃ a b : X, a * b ≠ b * a) : Subgroup.center X = ⊥ := by
  rcases (Subgroup.center X).normal_of_le_center le_rfl |>.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have : a ∈ Subgroup.center X := by rw [h]; trivial
    exact hab (Subgroup.mem_center_iff.1 this b).symm

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
