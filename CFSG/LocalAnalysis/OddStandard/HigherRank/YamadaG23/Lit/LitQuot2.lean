module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitQuot1
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit.LitOddQuot

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup
open scoped commutatorElement

variable {X : Type*} [Group X] [Finite X] {Z A : Subgroup X} [Z.Normal]
variable {G : Type*} [Group G] [Finite G] {π : X →* G}

theorem lit_bar (h : LitCtx Z A) (hπ : Function.Surjective π) (hk : π.ker = litP Z)
    (φ : ↥(normalizer (A : Set X)) →* Equiv.Perm (Fin 6)) (hφs : Function.Surjective φ)
    (hφk : ∀ g : ↥(normalizer (A : Set X)), φ g = 1 ↔ ∀ a ∈ A, ⁅a, (g : X)⁆ ∈ Z) :
    ∃ φ' : ↥(normalizer ((A.map π : Subgroup G) : Set G)) →* Equiv.Perm (Fin 6),
      LitBar (A.map π) φ' ∧
      ∀ n : ↥(normalizer (A : Set X)), φ' ⟨π n, lit_mem_normalizer_map n.2⟩ = φ n := by
  let ψ : ↥(normalizer (A : Set X)) →* ↥(normalizer ((A.map π : Subgroup G) : Set G)) :=
    { toFun := fun n => ⟨π n, lit_mem_normalizer_map n.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change π (x * y) = π x * π y
        rw [map_mul] }
  have hψs : Function.Surjective ψ := by
    intro y
    have hy : (y : G) ∈ (normalizer (A : Set X)).map π := by
      rw [← lit_map_normalizer h hπ hk]
      exact y.2
    obtain ⟨n, hn, hπn⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨n, hn⟩, Subtype.ext hπn⟩
  have hker : ψ.ker ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker] at hn ⊢
    have hπn : π (n : X) = 1 := Subtype.ext_iff.mp hn
    have hnP : (n : X) ∈ litP Z := hk ▸ (MonoidHom.mem_ker (f := π)).mpr hπn
    have hnC : (n : X) ∈ litC Z A := lit_normalizer_inf_litP_le h ⟨n.2, hnP⟩
    rw [hφk n]
    exact (mem_litC.mp hnC).2
  let ψinv := Function.surjInv hψs
  have hψinv : Function.RightInverse ψinv ψ := Function.rightInverse_surjInv hψs
  let φ' : ↥(normalizer ((A.map π : Subgroup G) : Set G)) →* Equiv.Perm (Fin 6) :=
    ψ.liftOfRightInverse ψinv hψinv ⟨φ, hker⟩
  have hφ' : ∀ n : ↥(normalizer (A : Set X)),
      φ' ⟨π n, lit_mem_normalizer_map n.2⟩ = φ n := by
    intro n
    exact ψ.liftOfRightInverse_comp_apply ψinv hψinv ⟨φ, hker⟩ n
  refine ⟨φ', ⟨lit_map_card h hk, lit_map_comm h hk, ?_, ?_,
    lit_map_two_mem h hπ hk, lit_map_even h hπ hk, lit_oddCore_quot h hπ hk⟩, hφ'⟩
  ·
    intro y
    obtain ⟨n, rfl⟩ := hφs y
    exact ⟨ψ n, hφ' n⟩
  ·
    intro g
    obtain ⟨n, rfl⟩ := hψs g
    have hψn : ψ n = ⟨π (n : X), lit_mem_normalizer_map n.2⟩ := rfl
    rw [hψn, hφ' n, hφk n]
    constructor
    · intro hcomm a ha
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      change π n * π a₀ = π a₀ * π n
      have hmem : ⁅a₀, (n : X)⁆ ∈ Z := hcomm a₀ ha₀
      have hkerZ : π ⁅a₀, (n : X)⁆ = 1 :=
        (MonoidHom.mem_ker (f := π)).mp
          (hk.symm ▸ (show Z ≤ litP Z from le_sup_left) hmem)
      rw [map_commutatorElement] at hkerZ
      exact (commutatorElement_eq_one_iff_mul_comm.mp hkerZ).symm
    · intro hcomm a ha
      change ⁅a, (n : X)⁆ ∈ Z
      have hmem : π a ∈ A.map π := Subgroup.mem_map_of_mem π ha
      have h1 : π n * π a = π a * π n := hcomm (π a) hmem
      have h2 : ⁅π a, π n⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr h1.symm
      have hπc : π ⁅a, (n : X)⁆ = 1 := by rw [map_commutatorElement]; exact h2
      have hmemP : ⁅a, (n : X)⁆ ∈ litP Z :=
        hk ▸ (MonoidHom.mem_ker (f := π)).mpr hπc
      have hna : (n : X) * a * (n : X)⁻¹ ∈ A :=
        (Subgroup.mem_set_normalizer_iff.mp n.2 a).mp ha
      have hmemA : ⁅a, (n : X)⁆ ∈ A := by
        have he : ⁅a, (n : X)⁆ = a * ((n : X) * a * (n : X)⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [he]
        exact A.mul_mem ha (A.inv_mem hna)
      have hmemAZ : ⁅a, (n : X)⁆ ∈ A ⊓ litP Z := ⟨hmemA, hmemP⟩
      rwa [lit_A_inf_litP h] at hmemAZ

end CFSG.OddStandard.HigherRank.YamadaG23
