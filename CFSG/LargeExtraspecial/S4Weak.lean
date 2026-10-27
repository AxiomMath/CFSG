module

public import CFSG.LargeExtraspecial.S4Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S4

open Subgroup

theorem exists_mem_normalizer_not_mem_of_lt {X : Type*} [Group X] [Finite X] {p : ℕ}
    [Fact p.Prime] {P S₀ : Subgroup X} (hP : IsPGroup p P) (hlt : S₀ < P) :
    ∃ x ∈ P, x ∉ S₀ ∧ x ∈ normalizer (S₀ : Set X) := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hlt' : S₀.subgroupOf P < ⊤ := by
    refine lt_of_le_of_ne le_top fun htop => hlt.not_ge fun x hx => ?_
    have hx' : (⟨x, hx⟩ : P) ∈ S₀.subgroupOf P := by
      rw [htop]
      trivial
    exact mem_subgroupOf.mp hx'
  obtain ⟨y, hyN, hyP⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent (G := P) _ hlt')
  refine ⟨y, y.2, fun h => hyP (mem_subgroupOf.mpr h), ?_⟩
  have hy : y ∈ (normalizer (S₀ : Set X)).subgroupOf P := by
    rw [subgroupOf_normalizer_eq hlt.le]
    exact hyN
  exact mem_subgroupOf.mp hy

theorem map_conj_eq_of_mem_normalizer {X : Type*} [Group X] {H : Subgroup X} {x : X}
    (hx : x ∈ normalizer (H : Set X)) : H.map (MulAut.conj x).toMonoidHom = H := by
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_normalizer_iff.mp hx w).mp hw
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, by simp [mul_assoc]⟩
    change x⁻¹ * y * x ∈ H
    rw [mem_normalizer_iff.mp hx]
    convert hy using 1
    group

theorem mem_normalizer_of_map_conj_eq {X : Type*} [Group X] {H : Subgroup X} {x : X}
    (hx : H.map (MulAut.conj x).toMonoidHom = H) : x ∈ normalizer (H : Set X) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← hx]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← hx] at hy
    obtain ⟨w, hw, hwy⟩ := hy
    have : w = y := by
      have := congrArg (fun v => x⁻¹ * v * x) hwy
      simpa [mul_assoc] using this
    rwa [← this]

variable {G : Type*} [Group G] [Finite G] {S : Setting G}

instance instFiniteO : Finite S.O :=
  Finite.of_injective (fun s : S.O => ((s : S.Qt ≃ₗ[ZMod 2] S.Qt) : S.Qt → S.Qt))
    (fun _ _ h => Subtype.ext (LinearEquiv.ext (congrFun h)))

@[expose] def WeaklyClosed (S : Setting G) (g : G) : Prop :=
  ∀ h : G, h ∈ S.M → S.Lbar (h * g) ≤ normalizer (S.Lbar g : Set S.O) → S.Lbar (h * g) = S.Lbar g

theorem weaklyClosed_mul {g : G} (hw : WeaklyClosed S g) (h : S.M) :
    WeaklyClosed S ((h : G) * g) := by
  intro k hk hle
  have e0 : ∀ g'' : G, S.Lbar g'' = (S.Lbar ((h : G) * g'')).map
      (MulAut.conj (S.ρ h)⁻¹).toMonoidHom := by
    intro g''
    rw [← map_inv, ← Lbar_mul S h⁻¹]
    simp
  have hle' : S.Lbar (((h : G)⁻¹ * k * h) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    have h1 := Subgroup.map_mono (f := (MulAut.conj (S.ρ h)⁻¹).toMonoidHom) hle
    rw [map_equiv_normalizer_eq _ (MulAut.conj (S.ρ h)⁻¹), ← e0 g] at h1
    rwa [show ((h : G)⁻¹ * k * h) * g = (h : G)⁻¹ * (k * ((h : G) * g)) by group,
      e0 ((h : G)⁻¹ * (k * ((h : G) * g))), mul_inv_cancel_left]
  have hmem : (h : G)⁻¹ * k * h ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.inv_mem h.2) hk) h.2
  have heq := hw _ hmem hle'
  rw [show k * ((h : G) * g) = (h : G) * (((h : G)⁻¹ * k * h) * g) by group, Lbar_mul S h,
    heq, ← Lbar_mul S h]

theorem le_normalizer_of_weaklyClosed {g : G} (hw : WeaklyClosed S g) {T : Subgroup S.O}
    (hT : IsPGroup 2 T) (hTM : T ≤ S.Mbar) (hLT : S.Lbar g ≤ T) :
    T ≤ normalizer (S.Lbar g : Set S.O) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := T ⊓ normalizer (S.Lbar g : Set S.O) with hN
  by_contra hTN
  have hlt : N < T := lt_of_le_of_ne inf_le_left fun h => hTN (h ▸ inf_le_right)
  obtain ⟨y, hyT, hyN, hyNN⟩ := exists_mem_normalizer_not_mem_of_lt hT hlt
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.mp (hTM hyT)
  have hLN : S.Lbar g ≤ N := le_inf hLT le_normalizer
  have hle : S.Lbar ((k : G) * g) ≤ normalizer (S.Lbar g : Set S.O) := by
    rw [Lbar_mul S k]
    calc (S.Lbar g).map (MulAut.conj (S.ρ k)).toMonoidHom ≤
          N.map (MulAut.conj (S.ρ k)).toMonoidHom := map_mono hLN
      _ = N := map_conj_eq_of_mem_normalizer hyNN
      _ ≤ normalizer (S.Lbar g : Set S.O) := inf_le_right
  have heq := hw k k.2 hle
  rw [Lbar_mul S k] at heq
  exact hyN ⟨hyT, mem_normalizer_of_map_conj_eq heq⟩

theorem le_normalizer_Lbar_mul {g : G} (hw : WeaklyClosed S g) (h : S.M) {T : Subgroup S.O}
    (hT : IsPGroup 2 T) (hTM : T ≤ S.Mbar) (hLT : S.Lbar ((h : G) * g) ≤ T) :
    T ≤ normalizer (S.Lbar ((h : G) * g) : Set S.O) :=
  le_normalizer_of_weaklyClosed (weaklyClosed_mul hw h) hT hTM hLT

end CFSG.LargeExtraspecial.S4
