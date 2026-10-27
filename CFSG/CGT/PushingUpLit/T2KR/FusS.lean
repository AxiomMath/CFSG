module

public import CFSG.CGT.PushingUpLit.T2KR.GenFourMod
public import CFSG.CGT.Timmesfeld75.Defs

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.T2K CFSG.QuasithinUnique.Setup.Campbell
  CFSG.QuasithinUnique.Setup.Offender CFSG.Quasithin.JonesParshall CFSG.CGT.Timmesfeld75
open scoped commutatorElement LinearAlgebra.Projectivization
open MData (QM)

theorem mul_self_eq_one_of_mem_rootGrp {n : ℕ} {p : ℙ (Fq n) (Fin 2 → Fq n)}
    {g : Matrix.SpecialLinearGroup (Fin 2) (Fq n)} (hg : g ∈ rootGrp p) : g * g = 1 := by
  obtain ⟨x₀, hx₀⟩ := exists_smul_pt0 p
  rw [← hx₀, mem_rootGrp_smul_iff, rootGrp_pt0] at hg
  obtain ⟨t, ht⟩ := hg
  have ht' : CFSG.SL2MinimalFaithful.unipotent t.toAdd = x₀⁻¹ * g * x₀ := ht
  have hchar : CharP (Fq n) 2 := inferInstance
  have h2 : CFSG.SL2MinimalFaithful.unipotent t.toAdd * CFSG.SL2MinimalFaithful.unipotent t.toAdd =
      1 := by
    rw [← CFSG.SL2MinimalFaithful.unipotent_add, CharTwo.add_self_eq_zero]
    apply Subtype.ext
    simp [CFSG.SL2MinimalFaithful.coe_unipotent, Matrix.one_fin_two]
  rw [ht'] at h2
  have : g * g = x₀ * ((x₀⁻¹ * g * x₀) * (x₀⁻¹ * g * x₀)) * x₀⁻¹ := by group
  rw [this, h2]
  group

theorem three_le_card_of_ne {K : Type*} [Group K] [Finite K] (R : Subgroup K) {a b : K}
    (ha : a ∈ R) (hb : b ∈ R) (h1a : a ≠ 1) (h1b : b ≠ 1) (hab : a ≠ b) : 3 ≤ Nat.card R := by
  classical
  let g : Fin 3 → R := ![1, ⟨a, ha⟩, ⟨b, hb⟩]
  have hg : Function.Injective g := by
    have h1a' : (1 : K) ≠ a := fun h => h1a h.symm
    have h1b' : (1 : K) ≠ b := fun h => h1b h.symm
    have hba : b ≠ a := fun h => hab h.symm
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g, Subtype.ext_iff]
  simpa using Nat.card_le_card_of_injective g hg

variable {G : Type} [Group G] [Finite G]

namespace MData

variable {L M : Subgroup G} {n : ℕ} (H : MData G L M n)

include H in
theorem rho_mem_of_commute (hn : n = 2) {N : Subgroup G} (hN : N ≤ L ⊔ QM L M)
    (hN2 : IsPGroup 2 N) {b ε : G} (hbM : b ∈ M) (hbχ : H.chi ⟨b, hbM⟩ ≠ 1) (hεN : ε ∈ N)
    (hεQ : ε ∉ QM L M) (hεb : ε * b = b * ε) {l : G} (hl : l ∈ N) (hlM : l ∈ M)
    (hlb : H.actHom ⟨b, hbM⟩ * H.actHom ⟨l, hlM⟩ = H.actHom ⟨l, hlM⟩ * H.actHom ⟨b, hbM⟩) :
    l ∈ QM L M ∨ ε⁻¹ * l ∈ QM L M := by
  classical
  set a : Equiv.Perm (Fin 2 → Fq n) := H.actHom ⟨b, hbM⟩ with ha
  let C : Subgroup ↥M := (Subgroup.centralizer ({a} : Set (Equiv.Perm (Fin 2 → Fq n)))).comap
    H.actHom
  let N₁ : Subgroup G := (C ⊓ N.subgroupOf M).map M.subtype
  have hmem : ∀ x : G, x ∈ N₁ ↔ ∃ hxM : x ∈ M, x ∈ N ∧
      a * H.actHom ⟨x, hxM⟩ = H.actHom ⟨x, hxM⟩ * a := by
    intro x
    constructor
    · rintro ⟨y, ⟨hyC, hyN⟩, rfl⟩
      refine ⟨y.2, hyN, ?_⟩
      have := Subgroup.mem_centralizer_singleton_iff.1 hyC
      exact this.symm
    · rintro ⟨hxM, hxN, hxc⟩
      exact ⟨⟨x, hxM⟩, ⟨Subgroup.mem_centralizer_singleton_iff.2 hxc.symm, hxN⟩, rfl⟩
  have hN₁N : N₁ ≤ N := by
    intro x hx
    obtain ⟨-, hxN, -⟩ := (hmem x).1 hx
    exact hxN
  have hN₁ : N₁ ≤ L ⊔ QM L M := hN₁N.trans hN
  have hN₁2 : IsPGroup 2 N₁ := hN2.to_le hN₁N
  have hεM : ε ∈ M := H.LQ_le (hN hεN)
  have hε₁ : ε ∈ N₁ := by
    refine (hmem ε).2 ⟨hεM, hεN, ?_⟩
    have e : (⟨b, hbM⟩ * ⟨ε, hεM⟩ : ↥M) = ⟨ε, hεM⟩ * ⟨b, hbM⟩ := Subtype.ext hεb.symm
    rw [ha, ← map_mul, e, map_mul]
  have hl₁ : l ∈ N₁ := (hmem l).2 ⟨hlM, hl, hlb⟩
  obtain ⟨p, hp⟩ := H.exists_root_point_of_isPGroup N₁ hN₁ hN₁2
  have hF : Nat.card (Fq n) = 4 := by
    rw [GaloisField.card 2 n H.n_ne_zero, hn]
    norm_num
  have hroot : Nat.card (rootGrp p) = 4 := by rw [card_rootGrp, hF]
  by_cases hfull : (H.rhoOn N₁ hN₁).range = rootGrp p
  · exfalso
    obtain ⟨x, hxN₁, hx⟩ := H.exists_actHom_conj_ne N₁ hN₁ hbM hbχ p (fun g hg => by
      have : g ∈ (H.rhoOn N₁ hN₁).range := hfull ▸ hg
      obtain ⟨y, hy⟩ := this
      exact ⟨y, hy⟩)
    obtain ⟨hxM, -, hxc⟩ := (hmem x).1 hxN₁
    apply hx
    have e : (⟨b, hbM⟩ * ⟨x, H.LQ_le (hN₁ hxN₁)⟩ * ⟨b, hbM⟩⁻¹ : ↥M) =
        ⟨b, hbM⟩ * ⟨x, hxM⟩ * ⟨b, hbM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, ← ha, hxc]
    group
  · have hlt : (H.rhoOn N₁ hN₁).range < rootGrp p := lt_of_le_of_ne hp hfull
    have hdvd : Nat.card (H.rhoOn N₁ hN₁).range ∣ 4 := by
      rw [← hroot]; exact Subgroup.card_dvd_of_le hp
    have hne4 : Nat.card (H.rhoOn N₁ hN₁).range ≠ 4 := by
      intro h4
      apply hlt.ne
      exact Subgroup.eq_of_le_of_card_ge hp (by rw [hroot, h4])
    have hle2 : Nat.card (H.rhoOn N₁ hN₁).range ≤ 2 := by
      have hpos : 0 < Nat.card (H.rhoOn N₁ hN₁).range := Nat.card_pos
      have h4 : Nat.card (H.rhoOn N₁ hN₁).range ∈ Nat.divisors 4 :=
        Nat.mem_divisors.2 ⟨hdvd, by norm_num⟩
      have e : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [e] at h4
      simp only [Finset.mem_insert, Finset.mem_singleton] at h4
      omega
    have hLQ : ∀ x : G, x ∈ N₁ → x ∈ L ⊔ QM L M := fun x hx => hN₁ hx
    have hρε1 : H.rho ⟨ε, hN₁ hε₁⟩ ≠ 1 := fun h => hεQ ((H.rho_eq_one_iff _).1 h)
    have hρεmem : H.rho ⟨ε, hN₁ hε₁⟩ ∈ (H.rhoOn N₁ hN₁).range := ⟨⟨ε, hε₁⟩, rfl⟩
    have hρlmem : H.rho ⟨l, hN₁ hl₁⟩ ∈ (H.rhoOn N₁ hN₁).range := ⟨⟨l, hl₁⟩, rfl⟩
    by_cases h1 : H.rho ⟨l, hN₁ hl₁⟩ = 1
    · exact Or.inl ((H.rho_eq_one_iff _).1 h1)
    · right
      by_cases h2 : H.rho ⟨l, hN₁ hl₁⟩ = H.rho ⟨ε, hN₁ hε₁⟩
      · apply (H.rho_eq_one_iff ⟨ε⁻¹ * l, (L ⊔ QM L M).mul_mem
          ((L ⊔ QM L M).inv_mem (hN₁ hε₁)) (hN₁ hl₁)⟩).1
        have e : (⟨ε⁻¹ * l, (L ⊔ QM L M).mul_mem ((L ⊔ QM L M).inv_mem (hN₁ hε₁)) (hN₁ hl₁)⟩ :
            ↥(L ⊔ QM L M)) = ⟨ε, hN₁ hε₁⟩⁻¹ * ⟨l, hN₁ hl₁⟩ := Subtype.ext rfl
        rw [e, map_mul, map_inv, h2, inv_mul_cancel]
      · exfalso
        have h3 : 3 ≤ Nat.card (H.rhoOn N₁ hN₁).range :=
          three_le_card_of_ne _ hρεmem hρlmem hρε1 h1 (fun h => h2 h.symm)
        omega

end MData

end CFSG.CGT.PushingUpLit.T2KR
