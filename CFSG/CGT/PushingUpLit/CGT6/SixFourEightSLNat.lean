module

public import CFSG.CGT.PushingUpLit.CGT6.SixTwoNat
public import CFSG.CGT.PushingUpLit.BHS6.BlockModule

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUp CFSG.CGT.PushingUpLit
open CFSG.CGT.PushingUpLit.BHS CFSG.CGT.PushingUpLit.BHS6 CFSG.Quasithin CFSG.Quasithin.G6
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {X : Subgroup G}

theorem inf_centralizer_blockU_eq_SL {n : ℕ} (hX : IsShortGroup ↥X)
    (hnat : IsNaturalSLTwoModule ↥X n) :
    X ⊓ Subgroup.centralizer (blockU X : Set G) = oTwoIn X := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
    set x' : ↥X := ⟨x, hxX⟩ with hx'
    set M : Matrix (Fin 2) (Fin 2) (GaloisField 2 n) :=
      ((φ (QuotientGroup.mk x' : ↥X ⧸ pCore 2 ↥X) :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) with hM
    have hcomm : ∀ u : ↥(shortU ↥X), x' * (u : ↥X) = (u : ↥X) * x' := by
      intro u
      apply Subtype.ext
      have huU : ((u : ↥X) : G) ∈ blockU X := by
        rw [← map_shortU_subtype]
        exact ⟨u, u.2, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hxC _ huU).symm
    have hfix : ∀ v : Fin 2 → GaloisField 2 n, M.mulVec v = v := by
      intro v
      obtain ⟨u, hu⟩ := hψs (Multiplicative.ofAdd v)
      have e : x' * (u : ↥X) * x'⁻¹ = (u : ↥X) := by
        rw [hcomm u]
        group
      have hu' : x' * (u : ↥X) * x'⁻¹ ∈ shortU ↥X := by
        rw [e]
        exact u.2
      have key := hψe x' u u.2 hu'
      have e2 : (⟨x' * (u : ↥X) * x'⁻¹, hu'⟩ : ↥(shortU ↥X)) = u := Subtype.ext e
      rw [e2] at key
      have hu2 : ψ ⟨(u : ↥X), u.2⟩ = Multiplicative.ofAdd v := hu
      rw [hu2] at key
      exact (Multiplicative.ofAdd.injective key).symm
    have hone : M = 1 := by
      ext i j
      have := congrFun (hfix (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one] at this
      simpa [Matrix.one_apply, Pi.single_apply, eq_comm] using this
    have hφ1 : φ (QuotientGroup.mk x') = 1 := Subtype.ext hone
    have hq : QuotientGroup.mk x' = (1 : ↥X ⧸ pCore 2 ↥X) := (MulEquiv.map_eq_one_iff φ).mp hφ1
    have hxp : x' ∈ pCore 2 ↥X := (QuotientGroup.eq_one_iff x').mp hq
    exact ⟨x', hxp, rfl⟩
  · intro r hr
    refine Subgroup.mem_inf.mpr ⟨oTwoIn_le X hr, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact blockU_comm_of_short hX u hu r hr

theorem isNatSL_blockU {n : ℕ} (hX : IsShortGroup ↥X) (hnat : IsNaturalSLTwoModule ↥X n) :
    IsNatSL X (blockU X) n := by
  classical
  have hC := inf_centralizer_blockU_eq_SL hX hnat
  obtain ⟨φ, ψ, hψs, hψk, hψe⟩ := hnat
  let eU := blockUEquiv X
  let β : ↥(blockU X) →* Multiplicative (Fin 2 → GaloisField 2 n) :=
    ψ.comp eU.symm.toMonoidHom
  have hcoe : ∀ w : ↥(blockU X), (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) = (w : G) := by
    intro w
    have := blockUEquiv_coe X (eU.symm w)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  let φ' : ↥X →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n) :=
    (φ : (↥X ⧸ pCore 2 ↥X) →* _).comp (QuotientGroup.mk' (pCore 2 ↥X))
  have hφ'k : φ'.ker = pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker]
    show φ (QuotientGroup.mk x) = 1 ↔ x ∈ pCore 2 ↥X
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  refine ⟨φ', β, φ.surjective.comp (QuotientGroup.mk'_surjective _), ?_,
    hψs.comp eU.symm.surjective, ?_, ?_⟩
  · ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hC]
    constructor
    · intro hx
      have : x ∈ φ'.ker := hx
      rw [hφ'k] at this
      exact ⟨x, this, rfl⟩
    · rintro ⟨x', hx', hxx'⟩
      have : x' = x := Subtype.ext hxx'
      rw [← this] at *
      show x' ∈ φ'.ker
      rw [hφ'k]
      exact hx'
  · ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : β w = 1 ↔ eU.symm w ∈ ψ.ker := Iff.rfl
    rw [h1, hψk, Subgroup.mem_subgroupOf]
    constructor
    · intro hs
      have hs' : (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) ∈ blockZ X := by
        rw [← map_shortC_subtype]
        exact Subgroup.mem_map_of_mem _ hs
      rw [hcoe w] at hs'
      exact hs'
    · intro hw
      have : (((eU.symm w : ↥(shortU ↥X)) : ↥X) : G) ∈ blockZ X := by rw [hcoe w]; exact hw
      rw [← map_shortC_subtype] at this
      obtain ⟨c, hc, hcx⟩ := this
      have : c = ((eU.symm w : ↥(shortU ↥X)) : ↥X) := Subtype.ext hcx
      rwa [← this]
  · intro e w hw
    set u : ↥(shortU ↥X) := eU.symm w with hu
    have hu1 : ((u : ↥X) : G) = (w : G) := hcoe w
    have hu' : e * (u : ↥X) * e⁻¹ ∈ shortU ↥X := by
      rw [← Subgroup.mem_map_iff_mem X.subtype_injective, map_shortU_subtype]
      show (e : G) * ((u : ↥X) : G) * (e : G)⁻¹ ∈ blockU X
      rw [hu1]
      exact hw
    have hsub : eU.symm ⟨(e : G) * w * (e : G)⁻¹, hw⟩ = ⟨e * (u : ↥X) * e⁻¹, hu'⟩ := by
      rw [MulEquiv.symm_apply_eq]
      apply Subtype.ext
      show (e : G) * (w : G) * (e : G)⁻¹ = (e : G) * ((u : ↥X) : G) * (e : G)⁻¹
      rw [hu1]
    have key := hψe e u u.2 hu'
    show ψ (eU.symm ⟨(e : G) * w * (e : G)⁻¹, hw⟩) = _
    rw [hsub, key]
    rfl

theorem nonempty_slNatData_blockU {n : ℕ} (hX : IsShortGroup ↥X) (hperf : ⁅X, X⁆ = X)
    (hnat : IsNaturalSLTwoModule ↥X n) (hU2 : CFSG.Open.IsElemAbelian 2 (blockU X)) :
    Nonempty (@SLNatData ↥(blockU X) (commGroupOfElemAbelian hU2) (autOn X (blockU X))
      (GaloisField 2 n) _) := by
  refine nonempty_slNatData hU2 (le_normalizer_blockU X) ?_ (isNatSL_blockU hX hnat)
  exact le_antisymm (commutator_le_of_le_normalizer (le_normalizer_blockU X))
    (blockU_le_commutator hperf)

end CFSG.CGT.PushingUpLit.CGT6
