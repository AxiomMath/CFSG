module

public import CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBoundSylow
public import CFSG.LocalAnalysis.ComponentInitial.EvenPairingSuzuki

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBound

open CFSG.Blueprint CFSG.LieType.Ree
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Dual

variable {K : Type*} [Field K] [Finite K]

theorem card_le_two_pow_finrank {C : Type*} [Group C] [Finite C]
    (hcomm : ∀ x y : C, x * y = y * x) (hsq : ∀ x : C, x ^ 2 = 1)
    (P : Submodule (ZMod 2) (K →+ K →+ ZMod 2)) (β : K → K → C)
    (hspan : ∀ ℓ : Additive C →+ ZMod 2, (∀ w v, ℓ (Additive.ofMul (β w v)) = 0) → ℓ = 0)
    (hP : ∀ ℓ : Additive C →+ ZMod 2, ∃ b ∈ P, ∀ w v, b w v = ℓ (Additive.ofMul (β w v))) :
    Nat.card C ≤ 2 ^ Module.finrank (ZMod 2) P := by
  let _ : CommGroup C := { (inferInstance : Group C) with mul_comm := hcomm }
  have h2 : ∀ x : Additive C, 2 • x = 0 := fun x => by
    change Additive.ofMul (Additive.toMul x ^ 2) = Additive.ofMul 1
    rw [hsq]
  let _ : Module (ZMod 2) (Additive C) := AddCommGroup.zmodModule h2
  have : Finite (K →+ ZMod 2) := FunLike.finite _
  have : Finite (K →+ K →+ ZMod 2) := FunLike.finite _
  have : Module.Finite (ZMod 2) P := Module.Finite.of_finite
  have : Module.Finite (ZMod 2) (Additive C) := Module.Finite.of_finite
  choose b hbP hb using hP
  let Φ : Module.Dual (ZMod 2) (Additive C) →ₗ[ZMod 2] P :=
    { toFun := fun ℓ => ⟨b ℓ.toAddMonoidHom, hbP _⟩
      map_add' := fun ℓ ℓ' => Subtype.ext (by
        ext w v
        simp only [Submodule.coe_add, AddMonoidHom.add_apply, hb, LinearMap.toAddMonoidHom_coe,
          LinearMap.add_apply])
      map_smul' := fun c ℓ => Subtype.ext (by
        ext w v
        simp only [Submodule.coe_smul, AddMonoidHom.smul_apply, hb, LinearMap.toAddMonoidHom_coe,
          LinearMap.smul_apply, RingHom.id_apply]) }
  have hinj : Function.Injective Φ := by
    intro ℓ ℓ' h
    have h' : ∀ w v, (ℓ - ℓ').toAddMonoidHom (Additive.ofMul (β w v)) = 0 := fun w v => by
      have := congrArg (fun x : P => (x : K →+ K →+ ZMod 2) w v) h
      simp only [Φ, LinearMap.coe_mk, AddHom.coe_mk, hb, LinearMap.toAddMonoidHom_coe] at this
      rw [LinearMap.toAddMonoidHom_coe, LinearMap.sub_apply, this, sub_self]
    have h0 := hspan _ h'
    refine sub_eq_zero.mp (LinearMap.ext fun x => ?_)
    have := DFunLike.congr_fun h0 x
    simp only [LinearMap.toAddMonoidHom_coe, AddMonoidHom.zero_apply] at this
    rw [this, LinearMap.zero_apply]
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Subspace.dual_finrank_eq] at hle
  have hcard := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive C)
  rw [Nat.card_zmod] at hcard
  calc Nat.card C = Nat.card (Additive C) := rfl
    _ = 2 ^ Module.finrank (ZMod 2) (Additive C) := hcard
    _ ≤ 2 ^ Module.finrank (ZMod 2) P := Nat.pow_le_pow_right (by norm_num) hle

end Dual

variable {a : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))

include hK in
theorem card_ker_le (ha : 1 ≤ a) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (θ : E →* suzukiGroup a K) (hθ : Function.Surjective θ) (hC : θ.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 θ.ker) :
    CFSG.Assembly.IsElemAbelian 2 θ.ker ∧
      Nat.card θ.ker ≤ 2 ^ Module.finrank (ZMod 2) (suzukiPairingSpace a K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUp, hUidx⟩ := suzukiU_isPGroup_index hK
  obtain ⟨-, -, hTcard, hTnorm, -⟩ := suzuki_borel_structure hK
  have hTodd : Odd (Nat.card (suzukiT a K)) := by
    rw [hTcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow
      ((Nat.even_pow' (by omega)).mpr even_two) odd_one
  have key := even_central_two_cover_class_three_kernel_pairing θ hθ hC h2 (hUp.toSylow hUidx)
    (nilpotencyClass_suzukiU_le hK) (isElemAbelian_commutator_suzukiU hK ha)
    (isElemAbelian_abelianization_suzukiU hK ha) (suzukiT a K) hTnorm hTodd
    (suzukiU_pairing_eq_zero hK ha)
  rw [IsPGroup.toSylow_coe] at key
  obtain ⟨-, hCe, -, -, -, β, -, hβ₁, hβ₂, hspan, hβT, hβJ⟩ := key
  refine ⟨hCe, ?_⟩
  have hW : ∀ w : K, suzukiSElt a K 0 w ∈ ⁅suzukiU a K, suzukiU a K⁆ :=
    suzukiSElt_zero_mem_commutator hK ha
  obtain ⟨β', hβ'⟩ : ∃ β' : K → K → θ.ker, ∀ w v,
      β' w v = β ⟨suzukiSElt a K 0 w, hW w⟩ (Abelianization.of (sU (a := a) v)) :=
    ⟨_, fun _ _ => rfl⟩
  have hβ'₁ : ∀ w w' v, β' (w + w') v = β' w v * β' w' v := fun w w' v => by
    rw [hβ', hβ', hβ', ← hβ₁]
    congr 1
    exact Subtype.ext (suzukiSElt_zero_mul hK w w').symm
  have hβ'₂ : ∀ w v v', β' w (v + v') = β' w v * β' w v' := fun w v v' => by
    rw [hβ', hβ', hβ', ← hβ₂, of_sU_add hK ha]
  have hβ'T : ∀ (l : Kˣ) (w v : K),
      β' ((l : K) ^ (2 ^ (a + 1) + 1) * w) ((l : K) * v) = β' w v := fun l w v => by
    have ht : (suzukiDElt a K l)⁻¹ ∈ suzukiT a K := inv_mem (suzukiDElt_mem_suzukiT a K l)
    have e1 : (suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 w * ((suzukiDElt a K l)⁻¹)⁻¹ =
        suzukiSElt a K 0 ((l : K) ^ (2 ^ (a + 1) + 1) * w) := by
      rw [suzukiDElt_inv_conj hK, mul_zero]
    have e2 := conj_sU hK l v
    have h := hβT _ ht (suzukiSElt a K 0 w) (hW w) (by rw [e1]; exact hW _)
      (suzukiSElt a K v 0) (suzukiSElt_mem_suzukiU a K v 0)
      (by rw [e2]; exact suzukiSElt_mem_suzukiU a K _ 0)
    have h1 : (⟨(suzukiDElt a K l)⁻¹ * suzukiSElt a K 0 w * ((suzukiDElt a K l)⁻¹)⁻¹, by
        rw [e1]; exact hW _⟩ : ↥⁅suzukiU a K, suzukiU a K⁆) =
          ⟨suzukiSElt a K 0 ((l : K) ^ (2 ^ (a + 1) + 1) * w), hW _⟩ := Subtype.ext e1
    have h2 : (⟨(suzukiDElt a K l)⁻¹ * suzukiSElt a K v 0 * ((suzukiDElt a K l)⁻¹)⁻¹, by
        rw [e2]; exact suzukiSElt_mem_suzukiU a K _ 0⟩ : suzukiU a K) =
          sU ((l : K) * v) := Subtype.ext e2
    rw [h1, h2] at h
    rw [hβ', hβ']
    exact h
  have hβ'J : ∀ x y z : K,
      β' (x ^ 2 ^ (a + 1) * y + y ^ 2 ^ (a + 1) * x) z *
        β' (y ^ 2 ^ (a + 1) * z + z ^ 2 ^ (a + 1) * y) x *
          β' (z ^ 2 ^ (a + 1) * x + x ^ 2 ^ (a + 1) * z) y = 1 := fun x y z => by
    have hc : ∀ u c : K, ⁅suzukiSElt a K u 0, suzukiSElt a K c 0⁆ =
        suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * c + c ^ 2 ^ (a + 1) * u) := fun u c =>
      commutatorElement_suzukiSElt hK u 0 c 0
    have h := hβJ (suzukiSElt a K x 0) (suzukiSElt a K y 0) (suzukiSElt a K z 0)
      (suzukiSElt_mem_suzukiU a K x 0) (suzukiSElt_mem_suzukiU a K y 0)
      (suzukiSElt_mem_suzukiU a K z 0) (by rw [hc]; exact hW _) (by rw [hc]; exact hW _)
      (by rw [hc]; exact hW _)
    have e : ∀ (u c : K) (huc : ⁅suzukiSElt a K u 0, suzukiSElt a K c 0⁆ ∈
        ⁅suzukiU a K, suzukiU a K⁆),
        (⟨_, huc⟩ : ↥⁅suzukiU a K, suzukiU a K⁆) =
          ⟨suzukiSElt a K 0 (u ^ 2 ^ (a + 1) * c + c ^ 2 ^ (a + 1) * u), hW _⟩ :=
      fun u c _ => Subtype.ext (hc u c)
    rw [e x y, e y z, e z x] at h
    rw [hβ', hβ', hβ']
    exact h
  have hsq : ∀ x : θ.ker, x ^ 2 = 1 := fun x => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hCe.2 x x.2)
  refine card_le_two_pow_finrank (fun x y => Subtype.ext (Subgroup.mem_center_iff.mp (hC y.2) x))
    hsq (suzukiPairingSpace a K) β' (fun ℓ hℓ => ?_) (fun ℓ => ?_)
  ·
    set ψ : θ.ker →* Multiplicative (ZMod 2) := AddMonoidHom.toMultiplicativeRight ℓ with hψ
    have hle : θ.ker ≤ ψ.ker.map θ.ker.subtype := by
      refine hspan.ge.trans (Subgroup.closure_le _ |>.mpr ?_)
      rintro _ ⟨⟨p₁, p₂⟩, rfl⟩
      obtain ⟨w, hw⟩ := (mem_commutator_suzukiU_iff hK ha).mp p₁.2
      obtain ⟨v, hv⟩ := exists_of_eq_of_sU hK ha p₂
      have hp₁ : p₁ = ⟨suzukiSElt a K 0 w, hW w⟩ := Subtype.ext hw.symm
      refine ⟨β p₁ p₂, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ, AddMonoidHom.toMultiplicativeRight_apply_apply,
        ← hv, hp₁, ← hβ']
      exact ofAdd_eq_one.mpr (hℓ w v)
    refine AddMonoidHom.ext fun x => ?_
    obtain ⟨y, hy, hyx⟩ := hle (Additive.toMul x).2
    have hyx' : y = Additive.toMul x := Subtype.ext hyx
    rw [SetLike.mem_coe, MonoidHom.mem_ker, hψ, AddMonoidHom.toMultiplicativeRight_apply_apply,
      hyx'] at hy
    exact ofAdd_eq_one.mp hy
  ·
    refine ⟨AddMonoidHom.mk' (fun w => AddMonoidHom.mk' (fun v => ℓ (Additive.ofMul (β' w v)))
      fun v v' => by rw [hβ'₂, ofMul_mul, map_add]) fun w w' => ?_, ?_, fun w v => rfl⟩
    · ext v
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hβ'₁, ofMul_mul, map_add]
    · refine mem_suzukiPairingSpace.mpr ⟨fun l w v => ?_, fun x y z => ?_⟩
      · simp only [AddMonoidHom.mk'_apply]
        rw [hβ'T]
      · simp only [AddMonoidHom.mk'_apply]
        rw [← map_add, ← map_add, ← ofMul_mul, ← ofMul_mul, hβ'J, ofMul_one, map_zero]

end CFSG.LocalAnalysis.ComponentInitial.SuzukiCoverBound

namespace CFSG.LocalAnalysis.ComponentInitial

open CFSG.Blueprint CFSG.LieType.Ree SuzukiCoverBound

theorem even_Suzuki_catalog_perfect_central_two_kernel_bound {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 η.ker)
    {f : ℕ} (hJ : CFSG.Blueprint.LieModel J .twistedB2 0 2 f) :
    CFSG.IsElementaryAbelian 2 η.ker ∧ (f ≠ 3 → η.ker = ⊥) ∧ (f = 3 → Nat.card η.ker ≤ 4) ∧
      (IsCyclic η.ker → η.ker ≠ ⊥ → f = 3 ∧ Nat.card η.ker = 2) := by
  rcases hJ with ⟨ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, -, hS⟩
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  · exact absurd ht (by decide)
  obtain ⟨-, a, ha, K, _, _, hf, hcard, ⟨e⟩⟩ := hS
  have hK : Nat.card K = 2 ^ (2 * a + 1) := by rw [hcard, hf]
  obtain ⟨hchar, -⟩ := suzuki_frobenius_exponents a K hK
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨hbot, hone⟩ := even_suzuki_torus_invariant_jacobi_pairings ha hK
  set η' : E →* suzukiGroup a K := e.toMonoidHom.comp η with hη'
  have hker : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  obtain ⟨hCe, hcardC⟩ := card_ker_le hK ha η' (e.surjective.comp hη) (hker ▸ hC) (hker ▸ h2)
  rw [hker] at hCe hcardC
  have hEA : CFSG.IsElementaryAbelian 2 η.ker :=
    { is_comm := ⟨fun u v => Subtype.ext (Subgroup.mem_center_iff.mp (hC v.2) u)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hCe.2 x x.2) }
  have hne : f ≠ 3 → η.ker = ⊥ := fun hf3 => by
    have ha2 : 2 ≤ a := by omega
    rw [hbot ha2, finrank_bot, pow_zero] at hcardC
    exact Subgroup.eq_bot_of_card_le _ hcardC
  have h3 : f = 3 → Nat.card η.ker ≤ 4 := fun hf3 => by
    have ha1 : a = 1 := by omega
    rw [(hone ha1).2.2.1] at hcardC
    exact hcardC
  refine ⟨hEA, hne, h3, fun hcyc hnt => ?_⟩
  have hf3 : f = 3 := by
    by_contra hf3
    exact hnt (hne hf3)
  refine ⟨hf3, ?_⟩
  have hdvd : Nat.card η.ker ∣ 2 := by
    rw [← IsCyclic.exponent_eq_card]
    exact IsElementaryAbelian.exponent_dvd_p 2 η.ker
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact absurd (Subgroup.card_eq_one.mp h1) hnt
  · exact h1

end CFSG.LocalAnalysis.ComponentInitial
