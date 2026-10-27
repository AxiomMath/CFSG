module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3Delta5

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {P Q : Subgroup G}

omit [Finite G] in
theorem ParabolicFacts.not_isDelta5 (hF : ParabolicFacts P Q) :
    ¬ CFSG.QuasithinUnique.A5.G3.IsDelta5Group ↥(perfectCore P) := by
  rintro ⟨α, β, hαs, hαk, hβ, -⟩
  rcases hF.levi with hPQ | ⟨hgen, -⟩
  ·
    have h2 : IsPGroup 2 ↥(perfectCore P) := hF.pGroup.to_le hPQ
    have hcore : CFSG.pCore 2 ↥(perfectCore P) = ⊤ := by
      rw [eq_top_iff]
      refine le_pCore_of_normal (N := (⊤ : Subgroup ↥(perfectCore P))) fun x => ?_
      obtain ⟨k, hk⟩ := h2 (x : ↥(perfectCore P))
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    obtain ⟨y, hy⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨x, rfl⟩ := hαs y
    apply hy
    exact MonoidHom.mem_ker.1 (hαk ▸ hcore ▸ Subgroup.mem_top x)
  ·
    have hQP : Q ≤ perfectCore P := hgen.trans (by
      refine Subgroup.commutator_le.2 fun q hq x hx => ?_
      have h1 : q * x⁻¹ * q⁻¹ ∈ perfectCore P :=
        (Subgroup.mem_normalizer_iff.1
          (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P
            (Subgroup.le_normalizer (hF.le hq))) x⁻¹).1 ((perfectCore P).inv_mem hx)
      have : ⁅q, x⁆ = (q * x * q⁻¹) * x⁻¹ := by simp [commutatorElement_def]
      rw [this]
      exact (perfectCore P).mul_mem
        ((Subgroup.mem_normalizer_iff.1
          (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P
            (Subgroup.le_normalizer (hF.le hq))) x).1 hx)
        ((perfectCore P).inv_mem hx))
    obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
    have hPinf : perfectCore P ≤ Subgroup.normalizer (Q : Set G) :=
      (perfectCore_le P).trans hF.normalizes
    have hnorm : (Q.subgroupOf (perfectCore P)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2 hPinf
    have hQ2 : IsPGroup 2 (Q.subgroupOf (perfectCore P)) :=
      hF.pGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
    have hle : Q.subgroupOf (perfectCore P) ≤ CFSG.pCore 2 ↥(perfectCore P) :=
      le_pCore_of_normal hQ2
    let u : ↥(CFSG.pCore 2 ↥(perfectCore P)) :=
      ⟨⟨x, hQP hx⟩, hle (Subgroup.mem_subgroupOf.2 hx)⟩
    let v : ↥(CFSG.pCore 2 ↥(perfectCore P)) :=
      ⟨⟨y, hQP hy⟩, hle (Subgroup.mem_subgroupOf.2 hy)⟩
    have hcomm : u * v = v * u := by
      apply hβ.1
      rw [map_mul, map_mul, mul_comm]
    apply hxy
    have := congrArg (fun w : ↥(CFSG.pCore 2 ↥(perfectCore P)) =>
      ((w : ↥(perfectCore P)) : G)) hcomm
    simpa using this

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
