module

public import CFSG.GF2Type.Smith1979.CaseI25A4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979

namespace Case25

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions
open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4 CFSG.LargeExtraspecial.S6
  CFSG.LargeExtraspecial.S7 CFSG.LargeExtraspecial.OrthoF2

section Abstract

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {N L : Type*} [Group N] [Group L]

theorem eq_smul_of_mem_span {a w : V} (ε : V →ₗ[ZMod 2] ZMod 2) (hε : ε a = 1)
    (hw : w ∈ (ZMod 2) ∙ a) : w = ε w • a := by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, hε, smul_eq_mul, mul_one]

theorem eps_mul (ψ : N →* (V ≃ₗ[ZMod 2] V)) {a : V} (ε : V →ₗ[ZMod 2] ZMod 2) (hε : ε a = 1)
    (hNa : ∀ n : N, ψ n a = a) (n m : N) (p : V) (hm : ψ m p - p ∈ (ZMod 2) ∙ a) :
    ε (ψ (n * m) p - p) = ε (ψ n p - p) + ε (ψ m p - p) := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
  have hεc : ε (ψ m p - p) = c := by rw [← hc, map_smul, hε, smul_eq_mul, mul_one]
  have h2 : ψ m p = p + c • a := by rw [hc]; abel
  have h4 : ψ (n * m) p - p = (ψ n p - p) + c • a := by
    rw [map_mul, LinearEquiv.mul_apply, h2, map_add, map_smul, hNa n]
    abel
  rw [h4, map_add, map_smul, hε, smul_eq_mul, mul_one, hεc]

theorem exists_extension_of_invariant (ψ : N →* (V ≃ₗ[ZMod 2] V)) (ι : L →* N)
    (cj : N →* MulAut L) (hcj : ∀ (n : N) (l : L), ι (cj n l) = n * ι l * n⁻¹)
    (hcomm : ∀ l l' : L, l * l' = l' * l) (hsq : ∀ l : L, l * l = 1)
    {a : V} (ha : a ≠ 0) (P : Submodule (ZMod 2) V)
    (hPN : ∀ n : N, ∀ p ∈ P, ψ n p ∈ P) (hNa : ∀ n : N, ψ n a = a)
    (hLP : ∀ (l : L), ∀ p ∈ P, ψ (ι l) p - p ∈ (ZMod 2) ∙ a)
    (hfix : ∀ p ∈ P, (∀ l : L, ψ (ι l) p = p) → p ∈ (ZMod 2) ∙ a)
    (hfaith : ∀ l : L, (∀ p ∈ P, ψ (ι l) p = p) → l = 1)
    (f : L →* Multiplicative (ZMod 2)) (hf : ∀ (n : N) (l : L), f (cj n l) = f l) :
    ∃ ν : N →* Multiplicative (ZMod 2), ∀ l : L, ν (ι l) = f l := by
  classical
  letI : CommGroup L := { (inferInstance : Group L) with mul_comm := hcomm }
  letI : Module (ZMod 2) (Additive L) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x)
  obtain ⟨ε, hε⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) ha
  let D : N → Module.Dual (ZMod 2) P := fun n =>
    ε ∘ₗ (((ψ n : V ≃ₗ[ZMod 2] V) : V →ₗ[ZMod 2] V) - LinearMap.id) ∘ₗ P.subtype
  have hD : ∀ n (p : P), D n p = ε (ψ n p - p) := fun n p => rfl
  have hΘ0 : D (ι 1) = 0 := by
    refine LinearMap.ext fun p => ?_
    rw [hD, map_one, map_one]
    simp
  have hΘ : ∀ l l' : L, D (ι (l * l')) = D (ι l) + D (ι l') := by
    intro l l'
    refine LinearMap.ext fun p => ?_
    rw [LinearMap.add_apply, hD, hD, hD, map_mul]
    exact eps_mul ψ ε hε (fun n => hNa n) (ι l) (ι l') p (hLP l' p p.2)
  let Θ : Additive L →+ Module.Dual (ZMod 2) P :=
    { toFun := fun x => D (ι (Additive.toMul x))
      map_zero' := by simpa using hΘ0
      map_add' := fun x y => hΘ (Additive.toMul x) (Additive.toMul y) }
  let Θ' : Additive L →ₗ[ZMod 2] Module.Dual (ZMod 2) P := AddMonoidHom.toZModLinearMap 2 Θ
  have hΘ'apply : ∀ l : L, Θ' (Additive.ofMul l) = D (ι l) := fun l => rfl
  have hinj : Function.Injective Θ' := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have hl : Additive.toMul x = 1 := by
      refine hfaith _ fun p hp => ?_
      have h0 := LinearMap.congr_fun hx ⟨p, hp⟩
      have h1 : ε (ψ (ι (Additive.toMul x)) p - p) = 0 := h0
      have h2 := eq_smul_of_mem_span ε hε (hLP (Additive.toMul x) p hp)
      rw [h1, zero_smul, sub_eq_zero] at h2
      exact h2
    exact Additive.toMul.injective (by simpa using hl)
  let f' : Module.Dual (ZMod 2) (Additive L) :=
    AddMonoidHom.toZModLinearMap 2
      { toFun := fun x => Multiplicative.toAdd (f (Additive.toMul x))
        map_zero' := by simp
        map_add' := fun x y => by simp }
  obtain ⟨ξ, hξ⟩ := LinearMap.dualMap_surjective_of_injective hinj f'
  set p₀' : P := (Module.evalEquiv (ZMod 2) P).symm ξ
  set p₀ : V := (p₀' : V)
  have hp₀P : p₀ ∈ P := p₀'.2
  have hp₀f : ∀ l : L, ε (ψ (ι l) p₀ - p₀) = Multiplicative.toAdd (f l) := by
    intro l
    have h1 := LinearMap.congr_fun hξ (Additive.ofMul l)
    have h2 : (Θ'.dualMap ξ) (Additive.ofMul l) = ξ (D (ι l)) := by
      rw [LinearMap.dualMap_apply, hΘ'apply]
    have h3 : D (ι l) p₀' = ξ (D (ι l)) :=
      Module.apply_evalEquiv_symm_apply (ZMod 2) P (D (ι l)) ξ
    have h4 : f' (Additive.ofMul l) = Multiplicative.toAdd (f l) := rfl
    rw [← h4, ← h1, h2, ← h3]
    rfl
  have hdisp : ∀ n : N, ψ n p₀ - p₀ ∈ (ZMod 2) ∙ a := by
    intro n
    have hdP : ψ n p₀ - p₀ ∈ P := P.sub_mem (hPN n p₀ hp₀P) hp₀P
    refine hfix _ hdP fun l => ?_
    have hιl' : ι (cj n⁻¹ l) = n⁻¹ * ι l * n := by rw [hcj, inv_inv]
    have hnl : ι l * n = n * ι (cj n⁻¹ l) := by rw [hιl']; group
    have hdl : ψ (ι l) p₀ = p₀ + Multiplicative.toAdd (f l) • a := by
      have h := eq_smul_of_mem_span ε hε (hLP l p₀ hp₀P)
      rw [hp₀f] at h
      exact sub_eq_iff_eq_add'.mp h
    have hdl' : ψ (ι (cj n⁻¹ l)) p₀ = p₀ + Multiplicative.toAdd (f l) • a := by
      have h := eq_smul_of_mem_span ε hε (hLP (cj n⁻¹ l) p₀ hp₀P)
      rw [hp₀f, hf] at h
      exact sub_eq_iff_eq_add'.mp h
    have h1 : ψ (ι l) (ψ n p₀) = ψ n p₀ + Multiplicative.toAdd (f l) • a := by
      calc ψ (ι l) (ψ n p₀) = ψ (ι l * n) p₀ := by rw [map_mul, LinearEquiv.mul_apply]
        _ = ψ (n * ι (cj n⁻¹ l)) p₀ := by rw [hnl]
        _ = ψ n (ψ (ι (cj n⁻¹ l)) p₀) := by rw [map_mul, LinearEquiv.mul_apply]
        _ = ψ n p₀ + Multiplicative.toAdd (f l) • a := by
          rw [hdl', map_add, map_smul, hNa n]
    rw [map_sub, h1, hdl]
    abel
  refine ⟨{ toFun := fun n => Multiplicative.ofAdd (ε (ψ n p₀ - p₀))
            map_one' := by simp
            map_mul' := fun n m => by
              rw [eps_mul ψ ε hε (fun n => hNa n) n m p₀ (hdisp m), ofAdd_add] }, ?_⟩
  intro l
  change Multiplicative.ofAdd (ε (ψ (ι l) p₀ - p₀)) = f l
  rw [hp₀f l]
  rfl

end Abstract

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem Lbar_le_NLbar : S.Lbar g ≤ NLbar S g := fun _ hx =>
  ⟨S.Lbar_le_Mbar g hx, le_normalizer (H := S.Lbar g) hx⟩

section Extension

variable (H : Hyp4 S g) (C : Cons311 S g)
include H C

theorem exists_nu_extending (f : S.Lbar g →* Multiplicative (ZMod 2))
    (hf : ∀ (n : NLbar S g) (l : S.Lbar g), f (conjLbar S g n l) = f l) :
    ∃ ν : NLbar S g →* Multiplicative (ZMod 2),
      ∀ (l : S.O) (hl : l ∈ S.Lbar g), ν ⟨l, Lbar_le_NLbar hl⟩ = f ⟨l, hl⟩ := by
  have hfixN : ∀ n : NLbar S g, ((n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) =
      S.cl (g * S.z * g⁻¹) := fun n => fix_of_mem_normalizer H n.2.2
  have hcomm : ∀ a b : S.Lbar g, a * b = b * a := fun a b =>
    Subtype.ext (Lbar_comm S H.conj_mem a.2 b.2)
  have hsq : ∀ a : S.Lbar g, a * a = 1 := fun a =>
    Subtype.ext (mul_self_of_mem_Lbar S H.conj_mem a.2)
  obtain ⟨ν, hν⟩ := exists_extension_of_invariant (V := S.Qt) (N := NLbar S g) (L := S.Lbar g)
    ((S.O.subtype).comp (NLbar S g).subtype) (Subgroup.inclusion Lbar_le_NLbar) (conjLbar S g)
    (fun n l => Subtype.ext rfl) hcomm hsq (cl_conj_z_ne_zero S H.conj_mem H.conj_ne)
    (S.clSub (S.QG ⊓ S.Qa g))
    (fun n p hp => apply_mem_clSub_of_fix H.conj_mem H.conj_ne n.2.1 (hfixN n) hp) hfixN
    (fun l p hp => Lbar_apply_sub_mem_span' H.conj_mem hp l.2)
    (fun p _ h => by
      have : p ∈ fixSub S (S.Lbar g) := (mem_fixSub S).mpr fun x hx => h ⟨x, hx⟩
      rwa [H.fixSub_eq] at this)
    (fun l hl => Subtype.ext (C.faithful l l.2 hl)) f hf
  exact ⟨ν, fun l hl => hν ⟨l, hl⟩⟩

end Extension

section Context

variable (hCE : CentralExtInput.{0}) (H : Hyp4 S g) (hNo : NoA2 S g) (C : Cons311 S g)
  {t : S.O} (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g)
  (hΩ : OmegaCase H C ht ht1 hVQ) (hN : Nbar S g t = zpowers t)
  (h6 : finrank (ZMod 2) (Vt S g t) = 6)
include hCE H hNo C ht ht1 hVQ hΩ hN h6

theorem exists_nu (hΔ : (Delta S g t).ncard = 6) :
    ∃ (f : S.Lbar g →* Multiplicative (ZMod 2)) (ν : NLbar S g →* Multiplicative (ZMod 2)),
      (∀ x (hx : x ∈ Delta S g t), f ⟨x, delta_subset_Lbar ht hx⟩ = Multiplicative.ofAdd 1) ∧
      (∀ (n : NLbar S g) (l : S.Lbar g), f (conjLbar S g n l) = f l) ∧
      f.ker.map (S.Lbar g).subtype = Kbar S g t ∧
      (∀ (l : S.O) (hl : l ∈ S.Lbar g), ν ⟨l, Lbar_le_NLbar hl⟩ = f ⟨l, hl⟩) ∧
      ν ⟨t, Lbar_le_NLbar ht⟩ ≠ 1 := by
  obtain ⟨-, f, hf1, hf2, hKmap, -, hnot, -⟩ :=
    invariant_functional hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  obtain ⟨ν, hν⟩ := exists_nu_extending H C f hf2
  refine ⟨f, ν, hf1, hf2, hKmap, hν, ?_⟩
  rw [hν t ht]
  exact fun h => hnot (MonoidHom.mem_ker.mpr h)

theorem exists_nu_ker (hΔ : (Delta S g t).ncard = 6) :
    ∃ ν : NLbar S g →* Multiplicative (ZMod 2),
      ν ⟨t, Lbar_le_NLbar ht⟩ ≠ 1 ∧
      ∀ (l : S.O) (hl : l ∈ S.Lbar g), ν ⟨l, Lbar_le_NLbar hl⟩ = 1 ↔ l ∈ Kbar S g t := by
  obtain ⟨f, ν, -, -, hKmap, hν, hνt⟩ := exists_nu hCE H hNo C ht ht1 hVQ hΩ hN h6 hΔ
  refine ⟨ν, hνt, fun l hl => ?_⟩
  rw [hν l hl, ← MonoidHom.mem_ker, ← hKmap]
  constructor
  · intro h
    exact ⟨⟨l, hl⟩, h, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

end Context

end Case25

end CFSG.GF2Type.Smith1979
