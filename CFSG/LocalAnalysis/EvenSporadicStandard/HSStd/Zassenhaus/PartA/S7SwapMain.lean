module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S7Swap

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.EvenSporadicStandard.HSStd
open scoped commutatorElement

local notation "A6" => alternatingGroup (Fin 6)

theorem swap_normal_eq {X : Type} [Group X] [Finite X] {tt : X} (htt : orderOf tt = 2)
    (e : ↥(centralizer ({tt} : Set X)) ≃* Multiplicative (ZMod 2) × MulAut A6)
    (N : Subgroup X) [N.Normal] (hNdef : N = normalClosureOf (centralizerDerived tt))
    (hB0 : centralizer (N : Set X) = ⊥) (φ : ↥N ≃* A6 × A6)
    (M : Subgroup X) [M.Normal] (hMN : M ≤ N) (hM : ∀ g ∈ N, ⁅tt, g⁆ ∈ M) : M = N := by
  haveI := isSimple_alt6
  haveI hK' : ((M.subgroupOf N).map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance φ.toMonoidHom φ.surjective
  have hmemK : ∀ (m : X) (hm : m ∈ M), φ ⟨m, hMN hm⟩ ∈ (M.subgroupOf N).map φ.toMonoidHom :=
    fun m hm => ⟨⟨m, hMN hm⟩, hm, rfl⟩
  rcases normal_prod_cases alt6_nonabelian ((M.subgroupOf N).map φ.toMonoidHom) with
    h | h | h | h
  ·
    exfalso
    have hM1 : ∀ m ∈ M, m = 1 := by
      intro m hm
      have h1 := hmemK m hm
      rw [h, Subgroup.mem_bot] at h1
      have := φ.injective (h1.trans (map_one φ).symm)
      exact congrArg Subtype.val this
    have htc : tt ∈ centralizer (N : Set X) := by
      rw [mem_centralizer_iff]
      intro g hg
      have h3 : tt * g * tt⁻¹ * g⁻¹ = 1 := hM1 _ (hM g hg)
      have h4 : tt * g * tt⁻¹ = g := mul_inv_eq_one.1 h3
      exact (mul_inv_eq_iff_eq_mul.1 h4).symm
    rw [hB0] at htc
    have : tt = 1 := Subgroup.mem_bot.1 htc
    rw [this, orderOf_one] at htt
    omega
  ·
    apply le_antisymm hMN
    intro n hn
    have h1 : φ ⟨n, hn⟩ ∈ (M.subgroupOf N).map φ.toMonoidHom := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkn⟩ := h1
    have hkeq : k = ⟨n, hn⟩ := φ.injective hkn
    subst hkeq
    exact hk
  · exfalso
    exact swap_key e N hNdef φ M hMN hM h
  · exfalso
    let φ' : ↥N ≃* A6 × A6 := φ.trans MulEquiv.prodComm
    have hK2 : (M.subgroupOf N).map φ'.toMonoidHom = (⊤ : Subgroup A6).prod ⊥ := by
      ext ⟨a, b⟩
      rw [Subgroup.mem_prod]
      constructor
      · rintro ⟨k, hk, hkab⟩
        have h1 : φ k ∈ (M.subgroupOf N).map φ.toMonoidHom := ⟨k, hk, rfl⟩
        rw [h, Subgroup.mem_prod] at h1
        have h2 : φ k = (b, a) := by
          have : φ' k = (a, b) := hkab
          have h3 : (φ k).swap = (a, b) := this
          exact Prod.ext (congrArg Prod.snd h3) (congrArg Prod.fst h3)
        rw [h2] at h1
        exact ⟨Subgroup.mem_top _, Subgroup.mem_bot.2 (Subgroup.mem_bot.1 h1.1)⟩
      · rintro ⟨-, hb⟩
        have hb' : b = 1 := Subgroup.mem_bot.1 hb
        subst hb'
        have h1 : ((1 : A6), a) ∈ (M.subgroupOf N).map φ.toMonoidHom := by
          rw [h, Subgroup.mem_prod]
          exact ⟨one_mem _, Subgroup.mem_top _⟩
        obtain ⟨k, hk, hk'⟩ := h1
        exact ⟨k, hk, by
          show (φ k).swap = (a, 1)
          have : φ k = (1, a) := hk'
          rw [this]; rfl⟩
    exact swap_key e N hNdef φ' M hMN hM hK2

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
