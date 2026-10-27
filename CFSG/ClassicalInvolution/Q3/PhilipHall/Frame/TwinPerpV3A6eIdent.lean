module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6ePkg
public import CFSG.ClassicalInvolution.Q3.TL4AECoverF

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.Open

variable {Y : Type} [Group Y]

theorem aeIdent_inj {P : Set (Subgroup Y)} (A : AEIdent P 8) {I : Subgroup Y} (hpI : pSpan P = I)
    (hker : A.φ.ker = ⊥) : Function.Injective (A.φ.comp (Subgroup.inclusion hpI.symm.le)) := by
  have h1 : Function.Injective A.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  exact h1.comp (Subgroup.inclusion_injective _)

theorem aeIdent_range {P : Set (Subgroup Y)} (A : AEIdent P 8) {I : Subgroup Y} (hpI : pSpan P = I) :
    (A.φ.comp (Subgroup.inclusion hpI.symm.le)).range = aeBar8 := by
  have e : aeBar8 = A.φ.range := A.range_eq.symm
  rw [e]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨Subgroup.inclusion hpI.symm.le y, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨⟨z.1, hpI ▸ z.2⟩, rfl⟩

theorem aeIdent_mem_D [Finite Y] {P : Set (Subgroup Y)} (A : AEIdent P 8) {I : Subgroup Y}
    (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) :
    ∀ x : ↥I, (x : Y) ∈ pCoreOf 2 I ↔
      permQ 8 ((A.φ.comp (Subgroup.inclusion hpI.symm.le)) x) = 1 := by
  subst hpI
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : Function.Injective A.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
  intro x
  show (x : Y) ∈ pCoreOf 2 (pSpan P) ↔ permQ 8 (A.φ x) = 1
  constructor
  · intro hx
    have hle : pCoreOf 2 (pSpan P) ≤ pSpan P := CFSG.LieType.BorelTits.pCoreOf_le 2 _
    have hT : ((pCoreOf 2 (pSpan P)).subgroupOf (pSpan P)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hle]
      intro h k hh hk
      have := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (pSpan P) hk
      exact (Subgroup.mem_normalizer_iff.mp this h).mp hh
    have hT2 : IsPGroup 2 ↥((pCoreOf 2 (pSpan P)).subgroupOf (pSpan P)) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (pSpan P)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hle).symm
    have := TL4.AECov.le_ker_permHom_of_normal A (by norm_num) hT hT2
      (show x ∈ (pCoreOf 2 (pSpan P)).subgroupOf (pSpan P) from hx)
    exact (TL4.AECov.mem_ker_permHom A).mp this
  · intro hx
    have hK : ((TL4.AECov.permHom A).ker).Normal := MonoidHom.normal_ker _
    have hK2 : IsPGroup 2 ↥(TL4.AECov.permHom A).ker := by
      intro y
      refine ⟨1, ?_⟩
      have hy := (TL4.AECov.mem_ker_permHom A).mp y.2
      have hyy : A.φ y * A.φ y = 1 :=
        mul_self_of_mem_ker_permQ (MonoidHom.mem_ker.mpr hy)
      have : (y : ↥(pSpan P)) * y = 1 := h1 (by rw [map_mul, hyy, map_one])
      apply Subtype.ext
      show (y : ↥(pSpan P)) ^ 2 ^ 1 = 1
      rw [pow_one, pow_two]
      exact this
    set N : Subgroup Y := (TL4.AECov.permHom A).ker.map (pSpan P).subtype with hN
    have hNle : N ≤ pSpan P := Subgroup.map_subtype_le _
    have hNn : (N.subgroupOf (pSpan P)).Normal := by
      have e : N.subgroupOf (pSpan P) = (TL4.AECov.permHom A).ker :=
        Subgroup.comap_map_eq_self_of_injective (pSpan P).subtype_injective _
      rw [e]
      exact hK
    have hN2 : IsPGroup 2 ↥N := hK2.map _
    have := CFSG.LieType.BorelTits.le_pCoreOf 2 hNle hNn hN2
    exact this ⟨x, (TL4.AECov.mem_ker_permHom A).mpr hx, rfl⟩

noncomputable def e8Pkg_of_aeIdent [Finite Y] {P : Set (Subgroup Y)} (A : AEIdent P 8)
    {I D : Subgroup Y} (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) (hD : pCoreOf 2 I = D) :
    E8Pkg I D where
  φ := A.φ.comp (Subgroup.inclusion hpI.symm.le)
  inj := aeIdent_inj A hpI hker
  range_eq := aeIdent_range A hpI
  le := by
    rw [← hD]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 I
  mem_D := fun x => by
    rw [← hD]
    exact aeIdent_mem_D A hpI hker x

@[expose] def E8Lab {I D : Subgroup Y} (P : E8Pkg I D) (𝒦 : Set (Subgroup Y)) : Prop :=
  ∀ J ∈ 𝒦, ∃ (α : Finset (Fin 8)) (h : α.card = 4) (b : Bool),
    ∀ x : ↥I, (x : Y) ∈ J ↔ P.φ x ∈ memBar α h b

theorem e8Lab_of_aeIdent [Finite Y] {P : Set (Subgroup Y)} (A : AEIdent P 8) {I D : Subgroup Y}
    (hpI : pSpan P = I) (hker : A.φ.ker = ⊥) (hD : pCoreOf 2 I = D) :
    E8Lab (e8Pkg_of_aeIdent A hpI hker hD) P := by
  subst hpI
  intro L hL
  obtain ⟨α, h, b, hlab⟩ := A.label L hL
  refine ⟨α, h, b, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [← hlab]
    exact A.mem_map hL hx
  · have hx' : A.φ x ∈ (L.subgroupOf (pSpan P)).map A.φ := by rw [hlab]; exact hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have h1 : Function.Injective A.φ := (MonoidHom.ker_eq_bot_iff _).mp hker
    have : y = x := h1 hyx
    rw [← this]
    exact Subgroup.mem_subgroupOf.mp hy

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
