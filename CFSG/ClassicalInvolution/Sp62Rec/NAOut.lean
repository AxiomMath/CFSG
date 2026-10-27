module

public import CFSG.ClassicalInvolution.Solomon73
public import CFSG.ClassicalInvolution.Solomon73.YamakiModel

public section

namespace CFSG.ClassicalInvolution.Sp62Rec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki CFSG.Open

variable {G : Type} [Group G] [Finite G] {A X' : Subgroup G}
  {A0 : Subgroup (StatedSp 3 (ZMod 2))}

theorem autL32_of_nu (hNX : Subgroup.normalizer (A : Set G) = X')
    (ν : ↥X' ≃* ↥N0) (hνA : (A.subgroupOf X').map ν.toMonoidHom = A0.subgroupOf N0)
    (hCA : Subgroup.centralizer (A : Set G) = A)
    (hρ : ∃ ρ : ↥N0 →* GL (Fin 3) (ZMod 2), Function.Surjective ρ ∧ ρ.ker = A0.subgroupOf N0) :
    AutL32 A := by
  obtain ⟨ρ, hρs, hρk⟩ := hρ
  have hmem : ∀ y : ↥X', y ∈ A.subgroupOf X' ↔ ν y ∈ A0.subgroupOf N0 := by
    intro y
    rw [← hνA, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  unfold AutL32
  refine ⟨ρ.comp (ν.toMonoidHom.comp (MulEquiv.subgroupCongr hNX).toMonoidHom), ?_, ?_⟩
  · intro g
    obtain ⟨n, hn⟩ := hρs g
    refine ⟨(MulEquiv.subgroupCongr hNX).symm (ν.symm n), ?_⟩
    simp only [MonoidHom.comp_apply, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, hn]
  · ext n
    have key : ν (MulEquiv.subgroupCongr hNX n) ∈ A0.subgroupOf N0 ↔ (n : G) ∈ A :=
      (hmem (MulEquiv.subgroupCongr hNX n)).symm.trans Subgroup.mem_subgroupOf
    have h1 : ρ (ν (MulEquiv.subgroupCongr hNX n)) = 1 ↔
        ν (MulEquiv.subgroupCongr hNX n) ∈ A0.subgroupOf N0 := by
      rw [← hρk, MonoidHom.mem_ker]
    rw [MonoidHom.mem_ker]
    show ρ (ν (MulEquiv.subgroupCongr hNX n)) = 1 ↔
      n ∈ (Subgroup.centralizer (A : Set G)).subgroupOf (Subgroup.normalizer (A : Set G))
    rw [h1, key, Subgroup.mem_subgroupOf, hCA]

theorem exists_fpf_of_nu (hNX : Subgroup.normalizer (A : Set G) = X')
    (ν : ↥X' ≃* ↥N0) (hνA : (A.subgroupOf X').map ν.toMonoidHom = A0.subgroupOf N0)
    (hAX : A ≤ X')
    (hfpf : ∃ x ∈ N0, x ^ 7 = 1 ∧ x ≠ 1 ∧ ∀ a ∈ A0, a * x = x * a → a = 1) :
    ∃ x ∈ Subgroup.normalizer (A : Set G), Odd (orderOf x) ∧ ∀ a ∈ A, a * x = x * a → a = 1 := by
  obtain ⟨x₀, hx₀N, hx₀7, -, hx₀fpf⟩ := hfpf
  obtain ⟨z, hzx⟩ : ∃ z : ↥X', ν z = ⟨x₀, hx₀N⟩ :=
    ⟨ν.symm ⟨x₀, hx₀N⟩, ν.apply_symm_apply _⟩
  have hz7 : z ^ 7 = 1 := by
    apply ν.injective
    rw [map_pow, hzx, map_one]
    exact Subtype.ext (by simpa using hx₀7)
  have hz7G : (z : G) ^ 7 = 1 := by
    simpa using congrArg Subtype.val hz7
  refine ⟨(z : G), ?_, ?_, ?_⟩
  · rw [hNX]
    exact z.2
  · exact Odd.of_dvd_nat (by decide) (orderOf_dvd_of_pow_eq_one hz7G)
  · intro a ha hcomm
    have haX : a ∈ X' := hAX ha
    have hmemA : (⟨a, haX⟩ : ↥X') ∈ A.subgroupOf X' := Subgroup.mem_subgroupOf.2 ha
    have hwA : ν ⟨a, haX⟩ ∈ A0.subgroupOf N0 := by
      rw [← hνA]
      exact Subgroup.mem_map_of_mem _ hmemA
    have hcomm' : ν (⟨a, haX⟩ * z) = ν (z * ⟨a, haX⟩) := by
      congr 1
      exact Subtype.ext hcomm
    rw [map_mul, map_mul, hzx] at hcomm'
    have hw := hx₀fpf _ (Subgroup.mem_subgroupOf.1 hwA) (congrArg Subtype.val hcomm')
    have h1 : (⟨a, haX⟩ : ↥X') = 1 := ν.injective (by rw [map_one]; exact Subtype.ext hw)
    exact congrArg Subtype.val h1

theorem mem_centralizer_iff_nu {e : G} (ν : ↥X' ≃* ↥N0) (heX : e ∈ X')
    (hνe : ((ν ⟨e, heX⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = alpha)
    (hαX0 : ∀ n ∈ N0, n * alpha = alpha * n → n ∈ X0)
    (hHα : Hhat ≤ Subgroup.centralizer ({alpha} : Set (StatedSp 3 (ZMod 2))))
    (x : G) (hx : x ∈ X') :
    x ∈ Subgroup.centralizer ({e} : Set G) ↔ ((ν ⟨x, hx⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ∈ X0 := by
  have key : x * e = e * x ↔ ν ⟨x, hx⟩ * ν ⟨e, heX⟩ = ν ⟨e, heX⟩ * ν ⟨x, hx⟩ := by
    rw [← map_mul, ← map_mul, ν.injective.eq_iff]
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  have key2 : ν ⟨x, hx⟩ * ν ⟨e, heX⟩ = ν ⟨e, heX⟩ * ν ⟨x, hx⟩ ↔
      ((ν ⟨x, hx⟩ : ↥N0) : StatedSp 3 (ZMod 2)) * alpha =
        alpha * ((ν ⟨x, hx⟩ : ↥N0) : StatedSp 3 (ZMod 2)) := by
    rw [← hνe]
    simp only [Subtype.ext_iff, Subgroup.coe_mul]
  rw [Subgroup.mem_centralizer_singleton_iff, key, key2]
  constructor
  · intro h
    exact hαX0 _ (ν ⟨x, hx⟩).2 h
  · intro h
    exact Subgroup.mem_centralizer_singleton_iff.1 (hHα (X0_le_Hhat h))

theorem exists_mem_normalizer_not_mem_centralizer {e : G}
    (hcard : Nat.card ↥(Subgroup.normalizer (A : Set G) ⊓ Subgroup.centralizer ({e} : Set G)) <
      Nat.card ↥(Subgroup.normalizer (A : Set G))) :
    ∃ n ∈ Subgroup.normalizer (A : Set G), n ∉ Subgroup.centralizer ({e} : Set G) := by
  by_contra h
  push_neg at h
  have hle : Subgroup.normalizer (A : Set G) ≤ Subgroup.centralizer ({e} : Set G) :=
    fun n hn => h n hn
  rw [inf_eq_left.2 hle] at hcard
  exact lt_irrefl _ hcard

end CFSG.ClassicalInvolution.Sp62Rec
