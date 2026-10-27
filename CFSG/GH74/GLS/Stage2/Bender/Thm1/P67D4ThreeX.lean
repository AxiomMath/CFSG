module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeTC
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeRigid
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeP
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67D4ThreeField
public import CFSG.RankThree.PartOne.KGD.D4T36Plane
public import CFSG.GH74.GLS.IVK.Proofs2.OddTools
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der61a
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Der69
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67G2FieldAux
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Prop67
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Statements
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.Stmt7
public import CFSG.GH74.GLS.Stage2.Local.P34Main
public import CFSG.GH74.GLS.Stage2.Local.P34S5A
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87CoatomAbs
public import CFSG.LinearAlgebra.OddSolvableUnitary.HomologySaturation
public import CFSG.RankThree.Chevalley.SteinbergCDTrialityThreeSixLocalCore
public import CFSG.RankThree.Chevalley.SteinbergCFOddG2SplitInnerActor
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import CFSG.Sporadic.ThSchreier.AutCore

public section

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.LocalRank CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold
  CFSG.RankThree.PartOne.KGD
open scoped Matrix Pointwise

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem cartan_perm_symm_pow_D4 (k : ℕ) (i j : Fin TwistTag.D4.tag.rank) :
    TwistTag.D4.tag.cartan (((TwistTag.D4.perm.symm) ^ k) i) (((TwistTag.D4.perm.symm) ^ k) j) =
      TwistTag.D4.tag.cartan i j := by
  have h1 : ∀ i j : Fin TwistTag.D4.tag.rank,
      TwistTag.D4.tag.cartan (TwistTag.D4.perm.symm i) (TwistTag.D4.perm.symm j) =
        TwistTag.D4.tag.cartan i j :=
    cartan_perm_symm (TwistTag.D4.cartan_perm)
  induction k generalizing i j with
  | zero => simp
  | succ k ih =>
    exact (ih (TwistTag.D4.perm.symm i) (TwistTag.D4.perm.symm j)).trans (h1 i j)

theorem phi36_false_of_outer_fixing_plane {ℓ f : ℕ} [Fact ℓ.Prime] (hf : 1 ≤ f) (K : Type)
    [Field K] [Finite K] (hK : Nat.card K = (ℓ ^ f) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {r : ℕ} (hr : r.Prime)
    (hr5 : 5 ≤ r) (hrd : (r : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1)
    (E : Subgroup 𝒞[K, σ]) (hE : IsElementaryAbelian r E) (hEcard : Nat.card E = r ^ 2)
    (φ : MulAut 𝒞[K, σ]) (hφ3 : φ ^ 3 = 1)
    (hφout : φ ∉ (MulAut.conj : 𝒞[K, σ] →* MulAut 𝒞[K, σ]).range)
    (hfix : ∀ a ∈ E, φ a = a) : False := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : Fact r.Prime := ⟨hr⟩
  have hK3 : Nat.card K = ℓ ^ (3 * f) := by rw [hK, ← pow_mul, mul_comm]
  have : CharP K ℓ := finite_field_prime_power_characteristic hℓ (by omega) hK3
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  obtain ⟨n, hn, w₀, hnw, hw₀, g0, hg0C, hg0, hperf, hconj⟩ :=
    d4T36_frame hf K hK σ hσ hε hr (by omega) hrd L
  have hinj0 : Function.Injective (rootDiagUnitHom TwistTag.D4.tag L) := rootDiagUnit_injective
  have hFr : ∀ c : L, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hT := twistedTorus_D4_eq_map_of_weylImage (iterateFrobenius L ℓ f) hn w₀ hnw (d4T36M ε) hw₀
  obtain ⟨y, m, hm, hφ⟩ := outer_order_three_normal_form hℓ hf K hK σ hσ φ hφ3 hφout
  have hpg : IsPGroup r E := IsPGroup.of_card hEcard
  have hEexp : ∀ q ∈ E, q ^ r = 1 := fun q hq =>
    congrArg Subtype.val (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p r E) ⟨q, hq⟩)
  obtain ⟨c, hc⟩ := hconj E hpg
  let ψ : E →* ModGL TwistTag.D4.tag L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((triEmb K σ L).comp ((MulAut.conj c).toMonoidHom.comp E.subtype))
  have hψ : ∀ q : E, ψ q = g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 := fun q => by
    change (MulAut.conj g0⁻¹ : MulAut (ModGL TwistTag.D4.tag L))
      (triEmb K σ L ((MulAut.conj c : MulAut 𝒞[K, σ]) (q : 𝒞[K, σ]))) = _
    rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv]
  have hψT : ∀ q : E, ψ q ∈ twistedTorusOf n
      (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f)) := fun q => by
    rw [hψ]
    exact hc q q.2
  choose β hβ using fun q : E =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hψT q)).1 :
      ∃ b : Fin TwistTag.D4.tag.rank → Lˣ, ψ q = rootDiagUnit TwistTag.D4.tag b)
  have hβmul : ∀ q q' : E, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  let βh : E →* (Fin TwistTag.D4.tag.rank → Lˣ) :=
    { toFun := β, map_one' := hβone, map_mul' := hβmul }
  have hβF : ∀ q : E, β q ∈ fixedCharTuples (d4T36M ε) (iterateFrobenius L ℓ f) := by
    intro q
    have h := hψT q
    rw [hT] at h
    obtain ⟨a', ha', haφ⟩ := h
    have : a' = β q := rootDiagUnit_injective (haφ.trans (hβ q))
    exact this ▸ ha'
  have hβpow : ∀ q : E, β q ^ r = 1 := by
    intro q
    have h1 : rootDiagUnit TwistTag.D4.tag (β q) ^ r = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ r = 1 := Subtype.ext (hEexp q q.2)
      rw [this, map_one]
    apply hinj0
    rw [map_pow, map_one]
    exact h1
  have hβr : ∀ (q : E) (u : Fin TwistTag.D4.tag.rank → ℤ), rootChar (β q) u ^ r = 1 := fun q u =>
    CTTorus.rootChar_pow_eq_one (fun i => congrFun (hβpow q) i) u
  have hβinj : ∀ q : E, β q = 1 → q = 1 := by
    intro q hq
    have h1 : g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0 = 1 := by
      rw [← hψ, hβ, hq, rootDiagUnit_one]
    have h2 : triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) = triEmb K σ L 1 := by
      rw [map_one]
      calc triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹)
          = g0 * (g0⁻¹ * triEmb K σ L (c * (q : 𝒞[K, σ]) * c⁻¹) * g0) * g0⁻¹ := by group
        _ = 1 := by rw [h1]; group
    have h3 := triEmb_injective h2
    refine Subtype.ext ?_
    calc (q : 𝒞[K, σ]) = c⁻¹ * (c * (q : 𝒞[K, σ]) * c⁻¹) * c := by group
      _ = 1 := by rw [h3]; group
  have hker : ∀ i : Fin TwistTag.D4.tag.rank, ∃ q : E, q ≠ 1 ∧ β q i = 1 := by
    intro i
    let χ : E →* Lˣ :=
      { toFun := fun q => β q i
        map_one' := by rw [hβone]; rfl
        map_mul' := fun q q' => by rw [hβmul]; rfl }
    refine d4Q_exists_ne_one_ker_of_card_sq hr hEcard χ fun q => ?_
    exact congrFun (hβpow q) i
  have hdiff : ∀ i : Fin 4, ¬ ((Pi.single (⟨0, by decide⟩ : Fin Tag.D4.rank) (1 : ℤ) :
      Fin Tag.D4.rank → ℤ) ∈ trialitySigmaList i ∧
      (Pi.single (⟨1, by decide⟩ : Fin Tag.D4.rank) (1 : ℤ) : Fin Tag.D4.rank → ℤ) ∈
        trialitySigmaList i) := by
    decide +kernel
  have hsing : ∀ q : E, q ≠ 1 → ∀ j : Fin TwistTag.D4.tag.rank, β q j = 1 →
      ∃ i : Fin 4, rootCharKernel (β q) = trialitySigma i ∧
        (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ trialitySigma i := by
    intro q hq1 j hj
    have hc1 : rootChar (β q) (Pi.single j 1) = 1 := by rw [CTTorus.rootChar_single]; exact hj
    have hmem : (Pi.single j 1 : Fin TwistTag.D4.tag.rank → ℤ) ∈ rootCharKernel (β q) :=
      ⟨IsRoot.basis _, hc1⟩
    rcases d4T36_rootCharKernel_cases hε (hβF q) (fun h => hq1 (hβinj q h)) with h | ⟨i, hi⟩
    · rw [h] at hmem
      exact absurd hmem (Set.notMem_empty _)
    · refine ⟨i, hi, ?_⟩
      rw [← hi]
      exact hmem
  obtain ⟨q₁, hq₁1, hq₁⟩ := hker ⟨0, by decide⟩
  obtain ⟨q₂, hq₂1, hq₂⟩ := hker ⟨1, by decide⟩
  obtain ⟨i₁, hk₁, hm₁⟩ := hsing q₁ hq₁1 _ hq₁
  obtain ⟨i₂, hk₂, hm₂⟩ := hsing q₂ hq₂1 _ hq₂
  have hi : i₁ ≠ i₂ := by
    rintro rfl
    exact hdiff i₁ ⟨mem_trialitySigma.1 hm₁, mem_trialitySigma.1 hm₂⟩
  obtain ⟨e₀, he₀'⟩ := exists_regular_of_two_singular hε hr hr5 hEcard βh hβF hi hk₁ hk₂
  have he₀ : rootCharKernel (β e₀) = ∅ := he₀'
  set P : ModGL TwistTag.D4.tag L := diagramMap TwistTag.D4 L with hP
  set ι := triEmb K σ L with hι
  have hcomm_y : ∀ q : E, ι y * P ^ m * ι (q : 𝒞[K, σ]) = ι (q : 𝒞[K, σ]) * (ι y * P ^ m) :=
    fun q => commute_of_fixes_element σ hm L y q (by rw [← hφ]; exact hfix q q.2)
  set ν' : ModGL TwistTag.D4.tag L := g0⁻¹ * (ι c * (ι y * P ^ m) * (ι c)⁻¹) * g0 with hν'
  have hcommν : ∀ q : E, ν' * rootDiagUnit TwistTag.D4.tag (β q) =
      rootDiagUnit TwistTag.D4.tag (β q) * ν' := by
    intro q
    rw [← hβ, hψ, map_mul, map_mul, map_inv]
    have h := hcomm_y q
    calc ν' * (g0⁻¹ * (ι c * ι (q : 𝒞[K, σ]) * (ι c)⁻¹) * g0) =
          g0⁻¹ * ι c * ((ι y * P ^ m) * ι (q : 𝒞[K, σ])) * (ι c)⁻¹ * g0 := by
          rw [hν']; group
      _ = g0⁻¹ * ι c * (ι (q : 𝒞[K, σ]) * (ι y * P ^ m)) * (ι c)⁻¹ * g0 := by rw [h]
      _ = (g0⁻¹ * (ι c * ι (q : 𝒞[K, σ]) * (ι c)⁻¹) * g0) * ν' := by
          rw [hν']; group
  have hgG : ν' * (P ^ m)⁻¹ ∈ adjointGroup TwistTag.D4.tag L := by
    have e : ν' * (P ^ m)⁻¹ = g0⁻¹ * (ι c * ι y) * (P ^ m * (ι c)⁻¹ * (P ^ m)⁻¹) *
        (P ^ m * g0 * (P ^ m)⁻¹) := by
      rw [hν']; group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem hg0C)
      (mul_mem (triEmb_mem_adjointGroup c) (triEmb_mem_adjointGroup y)))
      (conj_diagramMap_pow_mem_adjointGroup m (inv_mem (triEmb_mem_adjointGroup c))))
      (conj_diagramMap_pow_mem_adjointGroup m hg0C)
  set π : Equiv.Perm (Fin TwistTag.D4.tag.rank) := (TwistTag.D4.perm.symm) ^ m with hπ
  have hπc : ∀ i j, TwistTag.D4.tag.cartan (π i) (π j) = TwistTag.D4.tag.cartan i j :=
    cartan_perm_symm_pow_D4 m
  have hπc' : ∀ i j, TwistTag.D4.tag.cartan (π.symm i) (π.symm j) =
      TwistTag.D4.tag.cartan i j := cartan_perm_symm hπc
  have hb₀ : rootCharKernel (fun i => β e₀ (π i)) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun α hα => ?_
    obtain ⟨hαr, hα1⟩ := hα
    have h1 : rootChar (β e₀) (permLattice π α) = 1 := by
      rw [rootChar_permLattice]
      exact hα1
    have h2 : permLattice π α ∈ rootCharKernel (β e₀) := ⟨hαr.permLattice hπc, h1⟩
    rw [he₀] at h2
    exact Set.notMem_empty _ h2
  have hconj_d : rootDiagUnit TwistTag.D4.tag (β e₀) * (ν' * (P ^ m)⁻¹) =
      (ν' * (P ^ m)⁻¹) * rootDiagUnit TwistTag.D4.tag (fun i => β e₀ (π i)) := by
    have h1 := hcommν e₀
    have h2 := diagramMap_pow_conj_rootDiagUnit (L := L) (β e₀) m
    rw [← hP] at h2
    rw [← h2]
    calc rootDiagUnit TwistTag.D4.tag (β e₀) * (ν' * (P ^ m)⁻¹) =
          (rootDiagUnit TwistTag.D4.tag (β e₀) * ν') * (P ^ m)⁻¹ := by group
      _ = (ν' * rootDiagUnit TwistTag.D4.tag (β e₀)) * (P ^ m)⁻¹ := by rw [h1]
      _ = ν' * (P ^ m)⁻¹ * (P ^ m * rootDiagUnit TwistTag.D4.tag (β e₀) * (P ^ m)⁻¹) := by group
  obtain ⟨w, h, hh, hgw, -⟩ := exists_weyl_of_conj_regular (β e₀) (fun i => β e₀ (π i)) he₀ hb₀
    hgG hconj_d
  have hν : ν' = h * canonicalRep (coxeterSystem TwistTag.D4.tag) L w * P ^ m := by
    have : ν' = (ν' * (P ^ m)⁻¹) * P ^ m := by group
    rw [this, hgw]
  have hall : ∀ q : E, weylTuple w (fun i => β q (π i)) = β q := by
    intro q
    apply rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L)
    have h1 := hcommν q
    have h2 := diagramMap_pow_conj_rootDiagUnit (L := L) (β q) m
    rw [← hP] at h2
    have h3 := canonicalRep_conj_rootDiagUnit (K := L) w (fun i => β q (π i))
    have h4 := rootDiagUnit_mul_comm_of_mem_torusGroup
      (weylTuple w (fun i => β q (π i))) hh
    set n := canonicalRep (coxeterSystem TwistTag.D4.tag) L w with hn'
    have e1 : rootDiagUnit TwistTag.D4.tag (β q) =
        h * rootDiagUnit TwistTag.D4.tag (weylTuple w (fun i => β q (π i))) * h⁻¹ := by
      calc rootDiagUnit TwistTag.D4.tag (β q) =
            ν' * rootDiagUnit TwistTag.D4.tag (β q) * ν'⁻¹ := by rw [h1]; group
        _ = h * (n * (P ^ m * rootDiagUnit TwistTag.D4.tag (β q) * (P ^ m)⁻¹) * n⁻¹) * h⁻¹ := by
            rw [hν]; group
        _ = h * rootDiagUnit TwistTag.D4.tag (weylTuple w (fun i => β q (π i))) * h⁻¹ := by
            rw [h2, h3]
    have e2 : h * rootDiagUnit TwistTag.D4.tag (weylTuple w (fun i => β q (π i))) * h⁻¹ =
        rootDiagUnit TwistTag.D4.tag (weylTuple w (fun i => β q (π i))) := by
      rw [mul_inv_eq_iff_eq_mul, ← h4]
    exact (e1.trans e2).symm
  have hchar : ∀ (q : E) (x : Fin TwistTag.D4.tag.rank → ℤ),
      rootChar (β q) (w • x) = rootChar (β q) (permLattice π x) := by
    intro q x
    have h1 := rootChar_weylTuple w (fun i => β q (π i)) (w • x)
    rw [hall q, inv_smul_smul, ← rootChar_permLattice] at h1
    exact h1
  let yadd : (Fin TwistTag.D4.tag.rank → ℤ) →+ (Fin TwistTag.D4.tag.rank → ℤ) :=
    AddMonoidHom.mk' (fun u => w • permLattice π.symm u) (fun u v => by
      rw [permLattice_add, smul_add])
  have hyadd : ∀ u, yadd u = w • permLattice π.symm u := fun u => rfl
  have hy : ∀ α, IsRoot TwistTag.D4.tag α → IsRoot TwistTag.D4.tag (yadd α) := fun α hα =>
    IsRoot.smul (hα.permLattice hπc') w
  have hychar : ∀ (q : E) (u : Fin TwistTag.D4.tag.rank → ℤ),
      rootChar (β q) (yadd u) = rootChar (β q) u := by
    intro q u
    rw [hyadd, hchar q, CFSG.LieType.Chevalley.permLattice_permLattice_symm]
  have hid := eq_id_of_two_characters hFr hε hr hr5 hrd (hβF q₁) (hβF q₂) (hβr q₁) (hβr q₂) hi
    hk₁ hk₂ yadd hy (hychar q₁) (hychar q₂)
  have hw_eq : ∀ x : Fin TwistTag.D4.tag.rank → ℤ, w • x = permLattice π x := by
    intro x
    have := hid (permLattice π x)
    rw [hyadd, CFSG.LieType.Chevalley.permLattice_symm_permLattice] at this
    exact this
  have hπ1 : π = 1 := perm_eq_one_of_weyl_eq_permLattice w π hw_eq
  rcases hm with hm1 | hm2
  · rw [hπ, hm1] at hπ1
    exact absurd hπ1 (by decide)
  · rw [hπ, hm2] at hπ1
    exact absurd hπ1 (by decide)

end CFSG.GH74.GLS.Stage2.Bender.Thm1
