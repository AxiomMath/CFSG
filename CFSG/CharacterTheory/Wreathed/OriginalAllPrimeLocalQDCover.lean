module

public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeLocalQDCharPower
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeTIFactsModel
public import CFSG.CharacterTheory.Wreathed.OriginalAllPrimeModelSignalizersBasic

public section

namespace CFSG.Wreathed.OriginalAllPrime.LocalQD

open CFSG.ABGTheoremB CFSG.QuasiDihedralFusion CFSG.ABGQGroups
open CFSG.Wreathed.CyclicCentralSL2Extension CFSG.Wreathed.CentralSL2Abelianization
open scoped Pointwise

section Setting

variable {G : Type} [Group G]

@[expose] def centralizerToN (σ : Setting G) {H : Subgroup G} (hxH : σ.x ∈ H) :
    Subgroup.centralizer ({⟨σ.x, hxH⟩} : Set H) →* σ.N where
  toFun k := ⟨((k : H) : G), by
    have hk := Subgroup.mem_centralizer_singleton_iff.mp k.2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hk)⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem centralizerToN_coe (σ : Setting G) {H : Subgroup G} (hxH : σ.x ∈ H)
    (k : Subgroup.centralizer ({⟨σ.x, hxH⟩} : Set H)) :
    ((centralizerToN σ hxH k : σ.N) : G) = ((k : H) : G) :=
  rfl

theorem centralizerToN_injective (σ : Setting G) {H : Subgroup G} (hxH : σ.x ∈ H) :
    Function.Injective (centralizerToN σ hxH) := by
  intro a b h
  have h' : ((a : H) : G) = ((b : H) : G) := congrArg (fun z : σ.N => (z : G)) h
  exact Subtype.ext (Subtype.ext h')

variable {X : Type} [Group X] {σ : Setting G} {φ : σ.N →* X} {M : Subgroup X} {y : X}

theorem subset_mul_ON_of_modelLayer_le (hφ : TIFacts.IsModelMap σ φ M y) {K : Subgroup G}
    {K₀ : Type*} [Group K₀] (ι : K₀ →* σ.N) (hι : ∀ k, ((ι k : σ.N) : G) ∈ K)
    (hM : M ≤ (φ.comp ι).range) : (σ.L₀ : Set G) ⊆ (K : Set G) * (σ.ON : Set G) := by
  intro g hg
  have hgN : g ∈ σ.N := hφ.L₀_le hg
  have hgM : φ ⟨g, hgN⟩ ∈ M := by
    rw [← hφ.map_L₀]
    exact ⟨⟨g, hgN⟩, hg, rfl⟩
  obtain ⟨k, hk⟩ := hM hgM
  have hker : (ι k)⁻¹ * ⟨g, hgN⟩ ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    rw [MonoidHom.comp_apply] at hk
    rw [hk, inv_mul_cancel]
  rw [hφ.ker_eq, Subgroup.mem_subgroupOf] at hker
  refine Set.mem_mul.mpr ⟨((ι k : σ.N) : G), hι k, (((ι k)⁻¹ * ⟨g, hgN⟩ : σ.N) : G), hker, ?_⟩
  simp

theorem odd_card_ker_comp [Finite G] (hφ : TIFacts.IsModelMap σ φ M y) {K₀ : Type*} [Group K₀]
    (ι : K₀ →* σ.N) (hι : Function.Injective ι) : Odd (Nat.card (φ.comp ι).ker) := by
  rw [← MonoidHom.comap_ker]
  exact hφ.odd_card_ker.of_dvd_nat (Subgroup.card_comap_dvd_of_injective _ _ hι)

theorem centralizer_inf_le_range [Finite G] (hφ : TIFacts.IsModelMap σ φ M y)
    (hx₂L : σ.x₂ ∈ σ.L) {B : Subgroup X} (hB : B ≤ (σ.L.subgroupOf σ.N).map φ)
    {H : Subgroup G} (hxH : σ.x ∈ H)
    (hcov : ((σ.C ⊓ σ.L : Subgroup G) : Set G) ⊆
      (H : Set G) * ((σ.C ⊓ σ.ON : Subgroup G) : Set G)) :
    Subgroup.centralizer {y} ⊓ B ≤ (φ.comp (centralizerToN σ hxH)).range := by
  intro w hw
  obtain ⟨hwc, hwB⟩ := Subgroup.mem_inf.mp hw
  obtain ⟨g, hgL, rfl⟩ := hB hwB
  have hx₂ : (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N) * ⟨σ.x₂, hφ.x₂_mem⟩ = 1 := Subtype.ext hφ.x₂_mul_self
  have hU : ∀ u ∈ σ.L.subgroupOf σ.N, (⟨σ.x₂, hφ.x₂_mem⟩ : σ.N) * u * ⟨σ.x₂, hφ.x₂_mem⟩⁻¹ ∈
      σ.L.subgroupOf σ.N := by
    intro u hu
    rw [Subgroup.mem_subgroupOf] at hu ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact σ.L.mul_mem (σ.L.mul_mem hx₂L hu) (σ.L.inv_mem hx₂L)
  have hc : φ g * φ ⟨σ.x₂, hφ.x₂_mem⟩ = φ ⟨σ.x₂, hφ.x₂_mem⟩ * φ g := by
    rw [hφ.map_x₂]
    exact Subgroup.mem_centralizer_singleton_iff.mp hwc
  obtain ⟨u, huL, hφu, hux⟩ := TIFacts.exists_commute_lift φ hφ.odd_card_ker hx₂ hU hgL hc
  have huC : (u : G) ∈ σ.C := (TIFacts.mem_C_iff σ u.2).mpr (congrArg Subtype.val hux)
  obtain ⟨h, hh, c, hc', hhc⟩ := Set.mem_mul.mp (hcov (Subgroup.mem_inf.mpr ⟨huC, huL⟩))
  obtain ⟨-, hcO⟩ := Subgroup.mem_inf.mp hc'
  have hcN : c ∈ σ.N := TIFacts.ON_le_N σ hcO
  have hhN : h ∈ σ.N := by
    rw [eq_mul_inv_of_mul_eq hhc]
    exact σ.N.mul_mem u.2 (σ.N.inv_mem hcN)
  have hhK : (⟨h, hh⟩ : H) ∈ Subgroup.centralizer ({⟨σ.x, hxH⟩} : Set H) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hhN)
  refine ⟨⟨⟨h, hh⟩, hhK⟩, ?_⟩
  have hφc : φ ⟨c, hcN⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hφ.ker_eq, Subgroup.mem_subgroupOf]
    exact hcO
  have huhc : u = ⟨h, hhN⟩ * ⟨c, hcN⟩ := Subtype.ext hhc.symm
  change φ ⟨h, hhN⟩ = φ g
  rw [← hφu, huhc, map_mul, hφc, mul_one]

theorem dvd_of_hasQCharPower [Finite G] (σ : Setting G) (φ : σ.N →* X)
    (hker : φ.ker ≤ σ.ON.subgroupOf σ.N)
    {F : Type} [Field F] [Finite F] {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hcard : Nat.card F = p ^ f)
    (j : Matrix.SpecialLinearGroup (Fin 2) F →* X) (hj : Function.Injective j)
    (hcomm : commutator X ≤ j.range)
    {H : Subgroup G} (hxH : σ.x ∈ H) {r : ℕ}
    (hr : HasQCharPower (Subgroup.centralizer ({⟨σ.x, hxH⟩} : Set H)) r)
    (h3 : r ≠ 3) (h5 : r ≠ 5) : r ∣ p ^ f := by
  classical
  set K := Subgroup.centralizer ({⟨σ.x, hxH⟩} : Set H) with hKdef
  obtain ⟨-, hrodd, L', F', hF', hfin', hL'n, hF'card, ⟨eL'⟩⟩ := hr
  have h7 : 7 ≤ Nat.card F' := by
    have h1 : 1 < Nat.card F' := Finite.one_lt_card
    obtain ⟨k, hk⟩ := hrodd
    omega
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) F') := isPerfect_sl2 (by omega)
  have : Group.IsPerfect L' :=
    Group.IsPerfect.ofSurjective (f := eL'.symm.toMonoidHom) eL'.symm.surjective
  obtain ⟨P₀, hP₀, hP₀map⟩ := exists_perfect_map_eq (QuotientGroup.mk' (CFSG.oddCore K))
    (QuotientGroup.mk'_surjective _) L'
  let ι := centralizerToN σ hxH
  have hON : Odd (Nat.card (σ.ON.subgroupOf σ.N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (TIFacts.ON_le_N σ)).toEquiv]
    exact odd_card_oddCoreIn σ.N
  have hθodd : Odd (Nat.card (φ.comp ι).ker) := by
    rw [← MonoidHom.comap_ker]
    exact (hON.of_dvd_nat (Subgroup.card_dvd_of_le hker)).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ (centralizerToN_injective σ hxH))
  have hθO : (φ.comp ι).ker ≤ CFSG.oddCore K := le_oddCore_of_normal inferInstance hθodd
  let α₀ : P₀ →* X := (φ.comp ι).comp P₀.subtype
  have hα₀ : α₀.range ≤ j.range := by
    have : Group.IsPerfect α₀.range := Group.IsPerfect.ofSurjective α₀.rangeRestrict_surjective
    calc α₀.range = ⁅α₀.range, α₀.range⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(⊤ : Subgroup X), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator X := (commutator_def X).symm
      _ ≤ j.range := hcomm
  let α : P₀ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective hj).symm.toMonoidHom.comp
      (α₀.codRestrict j.range (fun x => hα₀ ⟨x, rfl⟩))
  have hβmem : ∀ x : P₀, QuotientGroup.mk' (CFSG.oddCore K) (x : K) ∈ L' := by
    intro x
    rw [← hP₀map]
    exact ⟨x, x.2, rfl⟩
  let β : P₀ →* Matrix.SpecialLinearGroup (Fin 2) F' :=
    eL'.toMonoidHom.comp (((QuotientGroup.mk' (CFSG.oddCore K)).comp P₀.subtype).codRestrict L'
      hβmem)
  have hβ : ∀ x : P₀, β x = 1 ↔ (x : K) ∈ CFSG.oddCore K := by
    intro x
    change eL' _ = 1 ↔ _
    rw [MulEquiv.map_eq_one_iff]
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (x : K)).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (x : K)).mpr h)
  have hβs : Function.Surjective β := by
    intro z
    obtain ⟨l, rfl⟩ := eL'.surjective z
    have hl : (l : K ⧸ CFSG.oddCore K) ∈ P₀.map (QuotientGroup.mk' (CFSG.oddCore K)) := by
      rw [hP₀map]
      exact l.2
    obtain ⟨k, hk, hkl⟩ := hl
    refine ⟨⟨k, hk⟩, ?_⟩
    change eL' _ = eL' l
    congr 1
    exact Subtype.ext hkl
  have hker' : α.ker ≤ β.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    change (MonoidHom.ofInjective hj).symm _ = 1 at hx
    rw [MulEquiv.symm_apply_eq, map_one] at hx
    have h1 : (φ.comp ι) (x : K) = 1 := congrArg Subtype.val hx
    exact (hβ x).mpr (hθO h1)
  have hβker : β.ker = (CFSG.oddCore K).comap P₀.subtype := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact hβ x
  have hβodd : Odd (Nat.card β.ker) := by
    rw [hβker]
    exact (CFSG.ABGDGroups.odd_card_oddCore K).of_dvd_nat
      (Subgroup.card_comap_dvd_of_injective _ _ P₀.subtype_injective)
  have hdvd := card_dvd_of_perfect_of_ker_le hp hpodd hf hcard h7 α β hβs hker' hβodd
  rwa [hF'card] at hdvd

end Setting

section Model

variable {F : Type} [Field F] [Finite F] {b : Fˣ} {m : ℕ} {hm : 0 < m} {heven : Even m}
  {Sigma : Subgroup (F ≃+* F)} {hSigma : ∀ σ ∈ Sigma, σ (b : F) = b}

theorem hasNormalSL2_of_modelLayer_le (hF : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F))
    {K : Type} [Group K] [Finite K] (θ : K →* SemilinearExtension F b m hm heven Sigma hSigma)
    (hker : θ.ker ≤ CFSG.oddCore K)
    (hM : ModelSignalizers.modelLayer b m hm heven Sigma hSigma ≤ θ.range) :
    HasNormalSL2 (K ⧸ CFSG.oddCore K) (Nat.card F) := by
  set j := matrixInclusion F b m hm heven Sigma hSigma with hjdef
  have hjinj : Function.Injective j := matrixInclusion_injective F b m hm heven Sigma hSigma
  have hML : ModelSignalizers.modelLayer b m hm heven Sigma hSigma = j.range :=
    ModelSignalizers.modelLayer_eq_matrixLayer
  let Λ : Subgroup K := j.range.comap θ
  have hΛ : Λ.Normal := (matrixLayer_normal F b m hm heven Sigma hSigma).comap θ
  let ψ : Λ →* Matrix.SpecialLinearGroup (Fin 2) F :=
    (MonoidHom.ofInjective hjinj).symm.toMonoidHom.comp
      ((θ.comp Λ.subtype).codRestrict j.range (fun l => l.2))
  have hψ : Function.Surjective ψ := by
    intro Z
    have hZ : j Z ∈ θ.range := hM (hML ▸ ⟨Z, rfl⟩)
    obtain ⟨k, hk⟩ := hZ
    refine ⟨⟨k, ⟨Z, hk.symm⟩⟩, ?_⟩
    change (MonoidHom.ofInjective hjinj).symm _ = Z
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply]
    exact hk
  have hkerψ : ψ.ker ≤ (CFSG.oddCore K).subgroupOf Λ := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    change (MonoidHom.ofInjective hjinj).symm _ = 1 at hl
    rw [MulEquiv.symm_apply_eq, map_one] at hl
    have h1 : θ l = 1 := congrArg Subtype.val hl
    exact hker h1
  exact hasNormalSL2_of_surjective hF hΛ ψ hψ hkerψ

end Model

section Wreathed

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem exists_modelMap
    (hnonab : ∃ a b : G, a * b ≠ b * a)
    {n : ℕ} {hn : 2 ≤ n} {S : Sylow 2 G} {e : S ≃* Wreath (2 ^ n)}
    (hfour : ¬ Nonempty (centralizerFullQuotient n hn S e ≃* Equiv.Perm (Fin 4)))
    {p f : ℕ} (hp : p.Prime) (hpodd : Odd p) (hf : 1 ≤ f)
    (hlocal : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (centralizerSimpleLayer n hn S e) .PSL 2 p f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (Sigma : Subgroup (F ≃+* F)) (b : Fˣ)
      (hSigma : ∀ σ ∈ Sigma, σ (b : F) = b)
      (φ : (wreathedSetting n S e p f).N →* SemilinearExtension F b (2 ^ n) (wreathModulus_pos n)
        (wreathModulus_even hn) Sigma hSigma),
      Nat.card F = p ^ f ∧ Odd (Nat.card Sigma) ∧ ¬ IsSquare b ∧
        TIFacts.IsModelMap (wreathedSetting n S e p f) φ
          (ModelSignalizers.modelLayer b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn)
            Sigma hSigma)
          (ModelSignalizers.modelY b (2 ^ n) (wreathModulus_pos n) (wreathModulus_even hn) Sigma
            hSigma) := by
  have hp2 : p ≠ 2 := fun h => (by decide : ¬ Odd 2) (h ▸ hpodd)
  obtain ⟨F, hfield, hfinite, Sigma, b, hSigma, ρ, Ψ, hdata⟩ :=
    exists_conditionalCompatibleModelData hnonab n hn S e hfour p f hp hp2 hf hlocal
  let : Field F := hfield
  let : Finite F := hfinite
  obtain ⟨h, hh⟩ := TIFacts.exists_liftMap_eq_modelY hnonab hfour hp hpodd hf hlocal hdata
  exact ⟨F, hfield, hfinite, Sigma, b, hSigma, _, hdata.card, hdata.sigma_odd, hdata.nonsquare,
    TIFacts.liftMap_isModelMap hnonab hfour hp hpodd hf hlocal hdata hh⟩

end Wreathed

end CFSG.Wreathed.OriginalAllPrime.LocalQD
