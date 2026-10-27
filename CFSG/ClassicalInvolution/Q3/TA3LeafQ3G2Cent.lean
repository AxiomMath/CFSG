module

public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Shape

public section

namespace CFSG.ClassicalInvolution.Q3.TA3

open CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab
open scoped MatrixGroups

structure CentShape (Y : Type) [Group Y] (C : Subgroup Y) (t : Y) (F₁ F₂ : Type) [Field F₁]
    [Field F₂] (h3 : (3 : F₂) = 0) where
  A : Subgroup Y
  B : Subgroup Y
  eA : ↥A ≃* SL(2, F₁)
  eB : ↥B ≃* SL(2, F₂)
  le_A : A ≤ C
  le_B : B ≤ C
  comm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a
  t_mem_A : t ∈ A
  t_mem_B : t ∈ B
  inter : ∀ x ∈ A, x ∈ B → x = 1 ∨ x = t
  eA_t : eA ⟨t, t_mem_A⟩ = -1
  eB_t : eB ⟨t, t_mem_B⟩ = -1
  normal_A : ∀ c ∈ C, ∀ a ∈ A, c * a * c⁻¹ ∈ A
  normal_B : ∀ c ∈ C, ∀ b ∈ B, c * b * c⁻¹ ∈ B
  cent_A : ∀ c ∈ C, (∀ a ∈ A, c * a = a * c) → c ∈ B
  cent_ij : ∀ c ∈ C, c * (eB.symm (SL3.i₀ F₂) : Y) = (eB.symm (SL3.i₀ F₂) : Y) * c →
    c * (eB.symm (SL3.j₀ h3) : Y) = (eB.symm (SL3.j₀ h3) : Y) * c → c ∈ A

namespace Q3Sh

variable {Y : Type} [Group Y] {N : Subgroup Y} {t : Y} (htN : t ∈ N)

@[expose] def ι : ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N)) →* Y :=
  N.subtype.comp (Subgroup.centralizer _).subtype

theorem ι_apply (x : ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N))) :
    ι htN x = ((x : ↥N) : Y) := rfl

theorem ι_injective : Function.Injective (ι htN) :=
  Subtype.val_injective.comp Subtype.val_injective

theorem ι_mem (x : ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N))) :
    ι htN x ∈ N ⊓ Subgroup.centralizer ({t} : Set Y) := by
  refine Subgroup.mem_inf.mpr ⟨(x : ↥N).2, ?_⟩
  rw [Subgroup.mem_centralizer_singleton_iff, ι_apply]
  simpa using congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp x.2)

theorem exists_ι {c : Y} (hc : c ∈ N ⊓ Subgroup.centralizer ({t} : Set Y)) :
    ∃ x, ι htN x = c := by
  refine ⟨⟨⟨c, hc.1⟩, ?_⟩, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hc.2)

theorem ι_mul_eq_iff {x y : ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N))} :
    ι htN x * ι htN y = ι htN y * ι htN x ↔ x * y = y * x := by
  rw [← map_mul, ← map_mul]
  exact (ι_injective htN).eq_iff

variable {F₁ F₂ : Type} [Field F₁] [Field F₂]
  (Sh : Shape ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N)) F₁ F₂)

theorem mem_map_iff {H : Subgroup ↥(Subgroup.centralizer ({⟨t, htN⟩} : Set ↥N))} {x} :
    ι htN x ∈ H.map (ι htN) ↔ x ∈ H :=
  ⟨fun ⟨_, hy, hyx⟩ => (ι_injective htN hyx) ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩

@[expose] noncomputable def toCentShape (hz : ((Sh.z : ↥N) : Y) = t) (h3 : (3 : F₂) = 0)
    (h2 : (2 : F₂) ≠ 0) : CentShape Y (N ⊓ Subgroup.centralizer ({t} : Set Y)) t F₁ F₂ h3 where
  A := Sh.I₁.map (ι htN)
  B := Sh.I₂.map (ι htN)
  eA := (Subgroup.equivMapOfInjective _ _ (ι_injective htN)).symm.trans Sh.e₁
  eB := (Subgroup.equivMapOfInjective _ _ (ι_injective htN)).symm.trans Sh.e₂
  le_A := by rintro _ ⟨x, -, rfl⟩; exact ι_mem htN x
  le_B := by rintro _ ⟨x, -, rfl⟩; exact ι_mem htN x
  comm := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    exact (ι_mul_eq_iff htN).mpr (Sh.comm a ha b hb)
  t_mem_A := ⟨Sh.z, Sh.z_mem₁, hz⟩
  t_mem_B := ⟨Sh.z, Sh.z_mem₂, hz⟩
  inter := by
    rintro _ ⟨a, ha, rfl⟩ hb
    have hb' : a ∈ Sh.I₂ := (mem_map_iff htN).mp hb
    have : a ∈ Sh.I₁ ⊓ Sh.I₂ := ⟨ha, hb'⟩
    rw [Sh.inter] at this
    rcases mem_zpowers_of_sq Sh.z_sq this with rfl | rfl
    · exact Or.inl (map_one _)
    · exact Or.inr hz
  eA_t := by
    have h1 : (Subgroup.equivMapOfInjective Sh.I₁ (ι htN) (ι_injective htN)).symm
        ⟨t, ⟨Sh.z, Sh.z_mem₁, hz⟩⟩ = ⟨Sh.z, Sh.z_mem₁⟩ :=
      (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hz.symm)
    simp only [MulEquiv.trans_apply]
    rw [h1]
    exact Sh.e₁_z
  eB_t := by
    have h1 : (Subgroup.equivMapOfInjective Sh.I₂ (ι htN) (ι_injective htN)).symm
        ⟨t, ⟨Sh.z, Sh.z_mem₂, hz⟩⟩ = ⟨Sh.z, Sh.z_mem₂⟩ :=
      (MulEquiv.symm_apply_eq _).mpr (Subtype.ext hz.symm)
    simp only [MulEquiv.trans_apply]
    rw [h1]
    exact Sh.e₂_z
  normal_A := by
    rintro c hc _ ⟨a, ha, rfl⟩
    obtain ⟨x, rfl⟩ := exists_ι htN hc
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, Sh.normal₁.conj_mem a ha x, rfl⟩
  normal_B := by
    rintro c hc _ ⟨b, hb, rfl⟩
    obtain ⟨x, rfl⟩ := exists_ι htN hc
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, Sh.normal₂.conj_mem b hb x, rfl⟩
  cent_A := by
    intro c hc h
    obtain ⟨x, rfl⟩ := exists_ι htN hc
    exact (mem_map_iff htN).mpr (mem_I₂_of_commute Sh fun a ha =>
      (ι_mul_eq_iff htN).mp (h _ ⟨a, ha, rfl⟩))
  cent_ij := by
    intro c hc hi hj
    obtain ⟨x, rfl⟩ := exists_ι htN hc
    refine (mem_map_iff htN).mpr (mem_I₁_of_commute_ij Sh h3 h2 ?_ ?_)
    · exact (ι_mul_eq_iff htN).mp hi
    · exact (ι_mul_eq_iff htN).mp hj

end Q3Sh

end CFSG.ClassicalInvolution.Q3.TA3
