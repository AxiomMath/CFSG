module

public import CFSG.LocalAnalysis.EvenBN.Tits.N.P4Fpf
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.LocalAnalysis.EvenBN.Tits.N.P4

open Subgroup

variable {Λ : Type*} [Group Λ]

@[expose] def resAut (M : Subgroup Λ) (φ : MulAut Λ) (hφ : ∀ n, n ∈ M ↔ φ n ∈ M) : MulAut ↥M where
  toFun m := ⟨φ m, (hφ m).1 m.2⟩
  invFun m := ⟨φ⁻¹ m, (hφ (φ⁻¹ m)).2 (by simpa using m.2)⟩
  left_inv m := Subtype.ext (by simp)
  right_inv m := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp)

@[expose] def resHom (M : Subgroup Λ) : stabSub M →* MulAut ↥M where
  toFun φ := resAut M φ.1 (mem_stabSub.1 φ.2)
  map_one' := by
    ext m
    rfl
  map_mul' φ ψ := by
    ext m
    rfl

theorem layer_trivial_sub [Finite Λ] (hcomm : ∀ a b : Λ, a * b = b * a) {N M : Subgroup Λ}
    (hidx : N.relIndex M = 16) {P : Subgroup (MulAut Λ)} (hP : IsPGroup 2 P) {x : MulAut Λ}
    (hx5 : x ^ 5 = 1) (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hPM : ∀ p ∈ P, ∀ m, m ∈ M ↔ p m ∈ M)
    (hPN : ∀ p ∈ P, ∀ n, n ∈ N ↔ p n ∈ N) (hxM : ∀ m, m ∈ M ↔ x m ∈ M)
    (hxN : ∀ n, n ∈ N ↔ x n ∈ N) (hfpf : ∀ l ∈ M, x l * l⁻¹ ∈ N → l ∈ N) :
    ∀ p ∈ P, ∀ l ∈ M, p l * l⁻¹ ∈ N := by
  classical
  let S := stabSub M
  have hPS : P ≤ S := fun p hp => hPM p hp
  have hxS : x ∈ S := hxM
  let ρ := resHom M
  have hρ : ∀ (φ : S) (m : ↥M), ((ρ φ m : ↥M) : Λ) = (φ : MulAut Λ) m := fun φ m => rfl
  have hcomm' : ∀ a b : ↥M, a * b = b * a := fun a b => Subtype.ext (hcomm a b)
  have hPsub : IsPGroup 2 (P.subgroupOf S) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPS).symm
  have hP' : IsPGroup 2 ↥((P.subgroupOf S).map ρ) := hPsub.map ρ
  let x' : MulAut ↥M := ρ ⟨x, hxS⟩
  have hx5' : x' ^ 5 = 1 := by
    have : (⟨x, hxS⟩ : S) ^ 5 = 1 := Subtype.ext hx5
    rw [← map_pow, this, map_one]
  have hxP' : ∀ q ∈ (P.subgroupOf S).map ρ, x' * q * x'⁻¹ ∈ (P.subgroupOf S).map ρ := by
    intro q hq
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hq
    refine Subgroup.mem_map.2 ⟨⟨x, hxS⟩ * p * ⟨x, hxS⟩⁻¹, ?_, by simp [x']⟩
    rw [Subgroup.mem_subgroupOf]
    have := hxP (p : MulAut Λ) (Subgroup.mem_subgroupOf.1 hp)
    simpa using this
  have hPN' : ∀ q ∈ (P.subgroupOf S).map ρ, ∀ n : ↥M, n ∈ N.subgroupOf M ↔ q n ∈ N.subgroupOf M := by
    intro q hq n
    obtain ⟨p, hp, rfl⟩ := Subgroup.mem_map.1 hq
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hρ]
    exact hPN (p : MulAut Λ) (Subgroup.mem_subgroupOf.1 hp) n
  have hxN' : ∀ n : ↥M, n ∈ N.subgroupOf M ↔ x' n ∈ N.subgroupOf M := by
    intro n
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hxN n
  have hfpf' : ∀ l : ↥M, x' l * l⁻¹ ∈ N.subgroupOf M → l ∈ N.subgroupOf M := by
    intro l hl
    rw [Subgroup.mem_subgroupOf] at hl ⊢
    exact hfpf l l.2 hl
  have key := layer_trivial hcomm' (N := N.subgroupOf M) hidx hP' hx5' hxP' hPN' hxN' hfpf'
  intro p hp l hl
  have hmem : ρ ⟨p, hPS hp⟩ ∈ (P.subgroupOf S).map ρ :=
    Subgroup.mem_map.2 ⟨⟨p, hPS hp⟩, Subgroup.mem_subgroupOf.2 hp, rfl⟩
  have := key _ hmem ⟨l, hl⟩
  rw [Subgroup.mem_subgroupOf] at this
  exact this

theorem layers_trivial [Finite Λ] (hcomm : ∀ a b : Λ, a * b = b * a) {Z E : Subgroup Λ} (hZE : Z ≤ E)
    (hZcard : Nat.card Z = 4) (hEcard : Nat.card E = 64) (hΛcard : Nat.card Λ = 1024)
    {x : MulAut Λ} (hx5 : x ^ 5 = 1) (hxZ : ∀ l, l ∈ Z ↔ x l ∈ Z) (hxE : ∀ l, l ∈ E ↔ x l ∈ E)
    (hfix : ∀ l, x l = l → l ∈ Z) {P : Subgroup (MulAut Λ)} (hP : IsPGroup 2 P)
    (hxP : ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hPZ : ∀ p ∈ P, ∀ l, l ∈ Z ↔ p l ∈ Z)
    (hPE : ∀ p ∈ P, ∀ l, l ∈ E ↔ p l ∈ E) :
    ∀ p ∈ P, p ∈ trivOn Z E hZE ∧ p ∈ trivOn E ⊤ le_top := by
  have hN5E : ¬ 5 ∣ Nat.card E := by rw [hEcard]; norm_num
  have hN5Z : ¬ 5 ∣ Nat.card Z := by rw [hZcard]; norm_num
  have hidxE : E.index = 16 := by
    have h := Subgroup.card_mul_index E
    rw [hEcard, hΛcard] at h
    omega
  have hfpfE : ∀ l : Λ, x l * l⁻¹ ∈ E → l ∈ E := by
    have := fpf_quot hcomm hx5 (N := E) (M := ⊤) le_top (fun l hl => (hxE l).1 hl)
      (fun l _ => Subgroup.mem_top _) hN5E (by rw [Subgroup.card_top, hΛcard, hEcard])
      (fun l _ h => hZE (hfix l h)) (C := Z) (fun l _ h => hfix l h) (by rw [hZcard]; norm_num)
    exact fun l hl => this l (Subgroup.mem_top l) hl
  have htop := layer_trivial hcomm hidxE hP hx5 hxP hPE hxE hfpfE
  have hrelZ : Z.relIndex E = 16 := by
    have h := Subgroup.relIndex_mul_card (H := Z) (K := E)
    rw [inf_eq_left.2 hZE, hZcard, hEcard] at h
    omega
  have hfpfZ : ∀ l ∈ E, x l * l⁻¹ ∈ Z → l ∈ Z :=
    fpf_quot hcomm hx5 (N := Z) (M := E) hZE (fun l hl => (hxZ l).1 hl) (fun l hl => (hxE l).1 hl)
      hN5Z (by rw [hEcard, hZcard]) (fun l _ h => hfix l h) (C := Z) (fun l _ h => hfix l h)
      (by rw [hZcard]; norm_num)
  have hlow := layer_trivial_sub hcomm hrelZ hP hx5 hxP hPE hPZ hxE hxZ hfpfZ
  intro p hp
  exact ⟨fun c hc => hlow p hp c hc, fun c _ => htop p hp c⟩

end CFSG.LocalAnalysis.EvenBN.Tits.N.P4
