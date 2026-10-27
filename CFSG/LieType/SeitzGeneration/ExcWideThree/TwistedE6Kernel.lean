module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwistedE6
public import CFSG.Monster.B.E6.StdF4RadicalRoots

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration CFSG.LieType.SeitzGeneration.ExcOuterLeOne
  CFSG.RankThree.PartOne.CTP CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.Fischer TauCeti
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.LieType.Steinberg.Adjoint

section Kernel

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K}

theorem exists_fixSigma_not_fixEta (hS : TwE6Setup K σ η 3) :
    ∃ t : K, σ t = t ∧ η t ≠ t := by
  by_contra hcon
  push Not at hcon
  have h1 : fixSubfieldRestrict η σ = 1 :=
    RingEquiv.ext fun c => Subtype.ext (hcon c ((mem_fixSubfield σ).1 c.2))
  have h3 := hS.orderOf_restrict
  rw [h1, orderOf_one] at h3
  exact absurd h3 (by norm_num)

theorem two_lt_card_fix_pair {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hcorner : ¬ (ℓ = 2 ∧ f = 3))
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (hS : TwE6Setup K σ η 3) :
    2 < Nat.card {c : K // σ c = c ∧ η c = c} := by
  have hord : orderOf σ = 2 := orderOf_eq_prime hS.sigma_sq hS.sigma_ne_one
  have hk : Nat.card (fixSubfield σ) = ℓ ^ f := by
    have h1 := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
    rw [hord, hK] at h1
    exact (Nat.pow_left_injective (by norm_num : 2 ≠ 0) h1).symm
  have hη' : orderOf (fixSubfieldRestrict η σ) = 3 := hS.orderOf_restrict
  have hk₀ : Nat.card (fixSubfield σ) = Nat.card (fixSubfield (fixSubfieldRestrict η σ)) ^ 3 := by
    have h1 := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow
      (fixSubfieldRestrict η σ)
    rwa [hη'] at h1
  have h3 : 3 ≤ Nat.card (fixSubfield (fixSubfieldRestrict η σ)) := by
    by_contra hlt
    push Not at hlt
    have h2 : 1 < Nat.card (fixSubfield (fixSubfieldRestrict η σ)) :=
      Finite.one_lt_card
    have h8 : ℓ ^ f = 2 ^ 3 := by
      rw [← hk, hk₀, show Nat.card (fixSubfield (fixSubfieldRestrict η σ)) = 2 by omega]
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    obtain ⟨h1, h2⟩ := Nat.Prime.pow_inj hℓ Nat.prime_two
      (by simpa using h8 : ℓ ^ (f' + 1) = 2 ^ (2 + 1))
    exact hcorner ⟨h1, by omega⟩
  let φ : fixSubfield (fixSubfieldRestrict η σ) → {c : K // σ c = c ∧ η c = c} := fun c =>
    ⟨((c : fixSubfield σ) : K), (mem_fixSubfield σ).1 (c : fixSubfield σ).2,
      congrArg (fun z : fixSubfield σ => (z : K)) ((mem_fixSubfield _).1 c.2)⟩
  have hφ : Function.Injective φ := by
    intro a b h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : {c : K // σ c = c ∧ η c = c} => (z : K)) h
  have := Nat.card_le_card_of_injective φ hφ
  omega

abbrev toE6 (g : ModGL TwistTag.E6.tag K) : ModGL Tag.E6 K := g

theorem exists_matrix_of_mem_inn_sup_diag (σ : K ≃+* K) (ι : MulAut (twistedE6RootGroup K σ))
    (hι : ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ) :
    ∃ y : ModGL Tag.E6 K, ∀ x : twistedE6RootGroup K σ,
      ((twIncl σ (ι x) : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        y * ((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * y⁻¹ := by
  obtain ⟨_, ⟨g, rfl⟩, _, ⟨u, rfl⟩, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hι
  refine ⟨toE6 ((g : ModGL TwistTag.E6.tag K) *
    rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u)), fun x => ?_⟩
  have h : (((MulAut.conj g * compatDiagAutHom TwistTag.E6 K σ.toRingHom u) x :
        twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
      (g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u) *
        (x : ModGL TwistTag.E6.tag K) *
        ((g : ModGL TwistTag.E6.tag K) *
          rootDiagUnit TwistTag.E6.tag (compatDiag TwistTag.E6 σ.toRingHom u))⁻¹ := by
    rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      coe_compatDiagAutHom, Subgroup.coe_inv]
    simp only [mul_assoc, mul_inv_rev]
  exact h

theorem endHom_xE6_simple (i : Fin Tag.E6.rank) (c : K) :
    endHom K (xE6 (Pi.single i 1) c) = xOp Tag.E6 K i c := by
  rw [xE6, xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.E6).elt_simple]

theorem twistedE6_kernel_of_ne_corner {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hcorner : ¬ (ℓ = 2 ∧ f = 3)) (hK : Nat.card K = ℓ ^ (2 * f))
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (hη : orderOf η = 3) (ι : MulAut (twistedE6RootGroup K σ))
    (hι : ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ)
    (hfix : ∀ x ∈ fixedSubgroup (fieldActor (t := TwistTag.E6) σ η), ι x = x) : ι = 1 := by
  classical
  have hK2 : Nat.card K = (ℓ ^ f) ^ 2 := by rw [hK, ← pow_mul, mul_comm]
  have hS : TwE6Setup K σ η 3 :=
    TwE6Setup.of_data hℓ hf hK2 hσ Nat.prime_three (by norm_num) (fun h => hℓ3 h.symm) hη
  have hcard := two_lt_card_fix_pair hℓ hf hcorner hK2 hS
  obtain ⟨y, hy⟩ := exists_matrix_of_mem_inn_sup_diag σ ι hι
  have hyR : ∀ x : twistedE6RootGroup K σ, ι x = x →
      y * ((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        ((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * y := fun x hx => by
    have h := hy x
    rw [hx] at h
    exact mul_inv_eq_iff_eq_mul.1 h.symm
  have hc3 : ∀ c : K, σ c = c → η c = c →
      (y : Module.End K (RootModule Tag.E6 K)) * xOp Tag.E6 K 3 c =
        xOp Tag.E6 K 3 c * (y : Module.End K (RootModule Tag.E6 K)) := by
    intro c hσc hηc
    obtain ⟨x, hxR, hxeq⟩ := Subgroup.mem_map.1 ((twR_gens hS).fixedX 3 (by decide) c hσc hηc)
    have h1 := congrArg Units.val (hyR x (hfix x hxR))
    have h2 : (((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) = xOp Tag.E6 K 3 c :=
      (congrArg (endHom K) hxeq).trans (endHom_xE6_simple 3 c)
    rwa [Units.val_mul, Units.val_mul, h2] at h1
  have hc3all : ∀ t : K, (y : Module.End K (RootModule Tag.E6 K)) * xOp Tag.E6 K 3 t =
      xOp Tag.E6 K 3 t * (y : Module.End K (RootModule Tag.E6 K)) := by
    intro t
    haveI : Fintype {c : K // σ c = c ∧ η c = c} := Fintype.ofFinite _
    have hD : entryDegreeBound Tag.E6 = 2 := by simp [entryDegreeBound]
    refine commute_of_polynomial_entries (F := xOp Tag.E6 K 3) (D := entryDegreeBound Tag.E6)
      (fun a b => ?_) _ (Subtype.val : {c : K // σ c = c ∧ η c = c} → K) Subtype.val_injective
      ?_ (fun j => hc3 j.1 j.2.1 j.2.2) t
    · obtain ⟨p, q, hp, hq, hpq⟩ :=
        exists_entry_polynomial (R := K) Tag.E6 (3 : Fin Tag.E6.rank) a b
      exact ⟨p, hp, fun c => (hpq c).1⟩
    · rw [hD, ← Nat.card_eq_fintype_card]
      exact hcard
  obtain ⟨t, hσt, hηt⟩ := exists_fixSigma_not_fixEta hS
  have hρ3 : permLattice TwistTag.E6.perm (Pi.single 3 1 : Fin Tag.E6.rank → ℤ) =
      Pi.single 3 1 := by decide
  obtain ⟨x, hx⟩ := xPar_fixed_mem_twIncl_range σ (isRoot_single Tag.E6 (3 : Fin Tag.E6.rank))
    hρ3 hσt
  have hxfix : ι x = x := by
    refine twIncl_injective σ (Subtype.ext ?_)
    rw [hy x]
    have h2 : (((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) :
        Module.End K (RootModule Tag.E6 K)) = xOp Tag.E6 K 3 t :=
      (congrArg (endHom K) hx).trans (endHom_xE6_simple 3 t)
    have hcomm : y * ((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) =
        ((twIncl σ x : adjointGroup Tag.E6 K) : ModGL Tag.E6 K) * y := by
      refine Units.ext ?_
      rw [Units.val_mul, Units.val_mul, h2]
      exact hc3all t
    rw [hcomm, mul_inv_cancel_right]
  set H : Subgroup (twistedE6RootGroup K σ) := CFSG.RankThree.PartOne.CTP.fixedSubgroup ι
    with hHdef
  have hRH : twR σ η ≤ H := fun x hx => hfix x hx
  have hmem : xE6 (Pi.single 3 1) t ∈ H.map (twIncl σ) := ⟨x, hxfix, hx⟩
  have htop : H = ⊤ :=
    twE6_eq_top_of_twFull σ hS.sigma_sq _ (twE6_twFull_of_irrational hS H hRH hσt hηt hmem)
  exact MulEquiv.ext fun z => (htop ▸ Subgroup.mem_top z : z ∈ H)

@[expose] def TwistedE6KernelCorner : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ (2 * 3) → ∀ σ : K ≃+* K,
    (∀ c, σ c = c ^ (2 ^ 3)) → ∀ η : K ≃+* K, orderOf η = 3 →
    ∀ ι : MulAut (twistedE6RootGroup K σ), ι ∈ twistedE6Inn K σ ⊔ twistedE6Diag K σ →
      (∀ x ∈ fixedSubgroup (fieldActor (t := TwistTag.E6) σ η), ι x = x) → ι = 1

theorem twistedE6KernelLemma_of_corner (hcorner : TwistedE6KernelCorner) :
    TwistedE6KernelLemma := by
  intro ℓ f hℓ hℓ3 hf K _ _ hK σ hσ η hη ι hι hfix
  by_cases h : ℓ = 2 ∧ f = 3
  · obtain ⟨rfl, rfl⟩ := h
    exact hcorner K hK σ hσ η hη ι hι hfix
  · exact twistedE6_kernel_of_ne_corner hℓ hℓ3 hf h hK hσ hη ι hι hfix

end Kernel

end CFSG.LieType.SeitzGeneration.ExcWideThree
