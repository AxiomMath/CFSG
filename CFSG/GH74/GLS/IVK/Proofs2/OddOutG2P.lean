module

public import CFSG.GH74.GLS.IVK.Proofs2.OddOutG2Stmt
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413Gen
public import CFSG.LieType.Chevalley.DiagonalFieldActorData

public section

namespace CFSG.GH74.Ivk413

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.IVK

section Aux

variable {F : Type} [Field F]

theorem sigma_eq_one_of_trace {F : Type} [Field F] (hF2 : ringChar F ≠ 2) (σ : F ≃+* F) {m : ℕ}
    (hm : Odd m) (hσm : σ ^ m = 1)
    (h : ∀ u : Fˣ, σ ((u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹)) =
      (u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹)) : σ = 1 := by
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    apply hF2
    have : CharP F 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h0)
    exact ringChar.eq F 2
  have hs : ∀ u : Fˣ, σ ((u : F) + (u : F)⁻¹) = (u : F) + (u : F)⁻¹ := by
    intro u
    set s : F := (u : F) + (u : F)⁻¹ with hsdef
    have hu : (u : F) ≠ 0 := u.ne_zero
    have hT : (u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹) = (s + 2) ^ 2 - 6 := by
      rw [hsdef]; field_simp; ring
    have h1 := h u
    rw [hT, map_sub, map_pow, map_add, map_ofNat, map_ofNat] at h1
    have hw : (σ s + 2) ^ 2 = (s + 2) ^ 2 := sub_left_inj.1 h1
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hw with h' | h'
    · exact add_right_cancel h'
    · have hσw : σ (s + 2) = -(s + 2) := by rw [map_add, map_ofNat]; exact h'
      have hk : ∀ k : ℕ, (σ ^ k) (s + 2) = (-1) ^ k * (s + 2) := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          have e : (σ ^ (k + 1)) (s + 2) = (σ ^ k) (σ (s + 2)) := by rw [pow_succ]; rfl
          rw [e, hσw, map_neg, ih, pow_succ]
          ring
      have h3 := hk m
      rw [hσm, hm.neg_one_pow] at h3
      have h4 : (s + 2) = 0 := by
        have h5 : (2 : F) * (s + 2) = 0 := by
          have : (1 : F ≃+* F) (s + 2) = s + 2 := rfl
          rw [this] at h3
          linear_combination h3
        exact (mul_eq_zero.1 h5).resolve_left h2
      rw [h4] at h'
      have : σ s + 2 = 0 := by rw [h']; ring
      have h6 : σ s = s := by
        have e1 : σ s = -2 := by linear_combination this
        have e2 : s = -2 := by linear_combination h4
        rw [e1, e2]
      exact h6
  have hσσ : ∀ x : F, σ (σ x) = x := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · set u : Fˣ := Units.mk0 x hx with hu
      have hux : (u : F) = x := rfl
      have hsu := hs u
      rw [map_add, map_inv₀, hux] at hsu
      have hσx : σ x ≠ 0 := by simpa using hx
      have key : (σ x - x) * (σ x * x - 1) = 0 := by
        have e : σ x * x * (σ x + (σ x)⁻¹) = σ x * x * (x + x⁻¹) := by rw [hsu]
        field_simp at e
        linear_combination e
      rcases mul_eq_zero.1 key with h' | h'
      · rw [sub_eq_zero.1 h']
        exact sub_eq_zero.1 h'
      · have h'' : σ x = x⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination h')
        rw [h'', map_inv₀, h'', inv_inv]
  have hsq : σ ^ 2 = 1 := RingEquiv.ext fun x => by
    rw [sq]
    exact hσσ x
  obtain ⟨j, rfl⟩ := hm
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at hσm
  exact hσm

theorem root_vals : ∀ k : Fin 12,
    (Tag.G2.rootCertificate.root k) ⟨0, by decide⟩ =
      (![1, 0, -1, 1, 1, 0, -1, 2, 1, -1, -2, -1] : Fin 12 → ℤ) k ∧
    (Tag.G2.rootCertificate.root k) ⟨1, by decide⟩ =
      (![0, 1, 0, 3, 1, -1, -3, 3, 2, -1, -3, -2] : Fin 12 → ℤ) k := by
  decide +kernel

theorem root_inj : ∀ k k' : Fin 12,
    Tag.G2.rootCertificate.root k = Tag.G2.rootCertificate.root k' → k = k' := by
  decide +kernel

def rootDiagEv {τ : Tag} (b : Fin τ.rank → Fˣ) : Label τ → F
  | Sum.inl _ => 1
  | Sum.inr α => ((∏ i, b i ^ α.1 i : Fˣ) : F)

theorem trace_rootDiag_eq_sum {τ : Tag} [Fintype (Label τ)] (b : Fin τ.rank → Fˣ) :
    LinearMap.trace F (RootModule τ F) (rootDiag b) = ∑ l : Label τ, rootDiagEv b l := by
  classical
  rw [LinearMap.trace_eq_matrix_trace F (Finsupp.basisSingleOne (R := F) (ι := Label τ))]
  unfold Matrix.trace
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  simp only [Finsupp.coe_basisSingleOne, Finsupp.basisSingleOne_repr, LinearEquiv.refl_apply]
  rcases l with k | γ
  · rw [rootDiag_single_inl]; simp [rootDiagEv]
  · rw [rootDiag_single_inr]; simp [rootDiagEv]

theorem trace_conj_unit {τ : Tag} (g : ModGL τ F) (A : Module.End F (RootModule τ F)) :
    LinearMap.trace F (RootModule τ F)
      ((g : Module.End F (RootModule τ F)) * A * ((g⁻¹ : ModGL τ F) : Module.End F (RootModule τ F))) =
        LinearMap.trace F (RootModule τ F) A := by
  rw [LinearMap.trace_mul_comm, ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]

section G2

noncomputable local instance fintypeRootG2 : Fintype {v : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 v} :=
  Fintype.ofFinite _

noncomputable def rootEquivG2 : Fin 12 ≃ {v : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 v} :=
  Equiv.ofBijective (fun k => ⟨Tag.G2.rootCertificate.root k, isRoot_G2_iff.2 ⟨k, rfl⟩⟩)
    ⟨fun k k' h => root_inj k k' (congrArg Subtype.val h), fun ⟨v, hv⟩ => by
      obtain ⟨k, hk⟩ := isRoot_G2_iff.1 hv
      exact ⟨k, Subtype.ext hk⟩⟩

def torusTupleG2 (u : Fˣ) : Fin Tag.G2.rank → Fˣ := ![u ^ 2, u⁻¹]

theorem sum_rootDiagEv_G2 (u : Fˣ) :
    ∑ l : Label .G2, rootDiagEv (F := F) (torusTupleG2 u) l =
      (u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹) + 4 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ i : Fin Tag.G2.rank, rootDiagEv (F := F) (torusTupleG2 u) (Sum.inl i) = 2 := by
    simp [rootDiagEv]
    show ((2 : ℕ) : F) = 2
    norm_num
  have hprod : ∀ v : Fin Tag.G2.rank → ℤ, (∏ i, torusTupleG2 u i ^ v i : Fˣ) =
      (u ^ 2) ^ (v ⟨0, by decide⟩) * (u⁻¹) ^ (v ⟨1, by decide⟩) := by
    intro v
    show (∏ i : Fin 2, (![u ^ 2, u⁻¹] : Fin 2 → Fˣ) i ^ v i) = _
    rw [Fin.prod_univ_two]
    rfl
  have h2 : ∑ α : {v : Fin Tag.G2.rank → ℤ // IsRoot Tag.G2 v}, rootDiagEv (F := F) (torusTupleG2 u) (Sum.inr α) =
      (u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹) + 2 := by
    rw [← Equiv.sum_comp rootEquivG2]
    have hk : ∀ k : Fin 12, rootDiagEv (F := F) (torusTupleG2 u) (Sum.inr (rootEquivG2 k)) =
        (((u ^ 2) ^ (![1, 0, -1, 1, 1, 0, -1, 2, 1, -1, -2, -1] : Fin 12 → ℤ) k *
          (u⁻¹) ^ (![0, 1, 0, 3, 1, -1, -3, 3, 2, -1, -3, -2] : Fin 12 → ℤ) k : Fˣ) : F) := by
      intro k
      show ((∏ i, torusTupleG2 u i ^ (Tag.G2.rootCertificate.root k) i : Fˣ) : F) = _
      rw [hprod, (root_vals k).1, (root_vals k).2]
    simp only [hk]
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
    simp
    have hu : (u : F) ≠ 0 := u.ne_zero
    field_simp
    ring
  rw [h1, h2]
  ring

theorem trace_rootDiag_G2 (u : Fˣ) :
    LinearMap.trace F (RootModule .G2 F) (rootDiag (torusTupleG2 u)) =
      (u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹) + 4 := by
  rw [trace_rootDiag_eq_sum, sum_rootDiagEv_G2]

end G2

end Aux

section NormalForm

open CFSG.LieType.Ree CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem g2_odd_normal_form
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = p ^ f) (α' : MulAut (adjointGroup ReeTag.G2.tag F)) (hodd : Odd (orderOf α')) :
    ∃ (g : adjointGroup ReeTag.G2.tag F) (σ : F ≃+* F), σ ^ orderOf α' = 1 ∧
      ∀ h : adjointGroup ReeTag.G2.tag F, (α' h : ModGL ReeTag.G2.tag F) =
        (g : ModGL ReeTag.G2.tag F) * Units.map (entrywiseHom σ.toRingHom) (h : ModGL ReeTag.G2.tag F) *
          (g : ModGL ReeTag.G2.tag F)⁻¹ := by
  by_cases hp3 : p = 3
  · subst hp3
    have : CharP F 3 := finite_field_prime_power_characteristic hp hf hcard
    have : CharP F ReeTag.G2.prime := ‹CharP F 3›
    obtain ⟨-, -, ⟨Θ, hΘ1, -, -⟩, -⟩ := G2_three_exact_automorphism_normal_form hf F hcard
    obtain ⟨g, k, hk⟩ := G2_exists_conj_mul_pow hf hcard α'
    have hΘk := hΘ1 α' g k hk
    set m := orderOf α' with hm
    have h1 : (Multiplicative.ofAdd (k : ZMod (2 * f))) ^ m = 1 := by
      rw [← hΘk, ← map_pow, hm, pow_orderOf_eq_one, map_one]
    have h2 : ((m * k : ℕ) : ZMod (2 * f)) = 0 := by
      have h3 : m • (k : ZMod (2 * f)) = 0 := by
        rw [← ofAdd_nsmul] at h1
        exact Multiplicative.ofAdd.injective h1
      simpa [nsmul_eq_mul] using h3
    have h4 : 2 * f ∣ m * k := (ZMod.natCast_eq_zero_iff _ _).1 h2
    have h5 : 2 ∣ k := by
      have : 2 ∣ m * k := (dvd_mul_right 2 f).trans h4
      exact Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_left.2 hodd) this
    obtain ⟨j, rfl⟩ := h5
    obtain ⟨fr, hfr, hfrord, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_three hf hcard
    refine ⟨g, fr ^ j, ?_, ?_⟩
    · have h6 : f ∣ m * j := by
        have : 2 * f ∣ 2 * (m * j) := by
          have e : m * (2 * j) = 2 * (m * j) := by ring
          rwa [e] at h4
        exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
      rw [← pow_mul, mul_comm]
      exact orderOf_dvd_iff_pow_eq_one.1 (by rw [hfrord]; exact h6)
    · intro h
      have e1 : α' = MulAut.conj g * ReeTag.G2.finiteExceptionalAut F ^ (2 * j) := hk
      have e2 : ReeTag.G2.finiteExceptionalAut F ^ (2 * j) =
          exactNormalAut ReeTag.G2.tag F 1 (fr ^ j) 0 := by
        rw [finiteExceptionalAut_pow_two_mul,
          exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2
            (ringAut_pow_apply_of_frobenius hfr j)]
      rw [e1, e2, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one, Subgroup.coe_inv]
  · obtain ⟨hex, Θ, hΘ, -, -, -⟩ :=
      odd_F4_and_nonexceptional_G2_automorphism_normal_form hp hp2 hf F hcard ReeTag.G2.tag
        (Or.inr ⟨rfl, hp3⟩)
    obtain ⟨⟨g, σ⟩, hgσ, -⟩ := hex α'
    refine ⟨g, σ, ?_, hgσ⟩
    rw [← hΘ α' g σ hgσ, ← map_pow, pow_orderOf_eq_one, map_one]

theorem g2_odd_normal_form_native
    {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = p ^ f) (α' : MulAut (adjointGroup Tag.G2 F)) (hodd : Odd (orderOf α')) :
    ∃ (g : adjointGroup Tag.G2 F) (σ : F ≃+* F), σ ^ orderOf α' = 1 ∧
      ∀ h : adjointGroup Tag.G2 F, (α' h : ModGL Tag.G2 F) = (g : ModGL Tag.G2 F) *
        Units.map (entrywiseHom σ.toRingHom) (h : ModGL Tag.G2 F) * (g : ModGL Tag.G2 F)⁻¹ :=
  g2_odd_normal_form hp hp2 hf hcard α' hodd

end NormalForm

end CFSG.GH74.Ivk413

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.GH74.GLS.IVK

open CFSG.GH74.Ivk413

section Main

theorem oddOutG2_proved :
    OddOutG2 := by
  intro K _ _ p f hp hp2 hLie hq3 z hz α hαodd hαfix
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq3
    · exact h
  obtain ⟨F, hF, hFin, hcard, ⟨φ⟩⟩ := Ivk47ab.exists_equiv_of_lieModel hLie
  have hodd : Odd (Nat.card F) := Ivk47ab.odd_card_of_model hp hp2 hcard
  have hchar : ringChar F ≠ 2 := CFSG.ABGLocalTools.ringChar_ne_two_of_odd_card hodd
  have hconj : IsConj (φ z) (Ivk47ab.z₀ F) :=
    CFSG.LieType.HighestRoot.g2_involutions_isConj hchar (φ z) (Ivk47ab.z₀ F)
      (by rw [MulEquiv.orderOf_eq]; exact hz) (Ivk47ab.orderOf_z₀ hchar)
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  let ψ : K ≃* Ivk47ab.G2g F := φ.trans (MulAut.conj c)
  have hψz : ψ z = Ivk47ab.z₀ F := by simpa [ψ] using hc
  let α' : MulAut (Ivk47ab.G2g F) := MulAut.congr ψ α
  have hα' : ∀ x : K, α' (ψ x) = ψ (α x) := fun x => by simp [α', MulAut.congr_apply]
  have hα'fix : ∀ y ∈ centralizer ({Ivk47ab.z₀ F} : Set (Ivk47ab.G2g F)), α' y = y := by
    intro y hy
    obtain ⟨x, rfl⟩ := ψ.surjective y
    rw [hα']
    congr 1
    apply hαfix
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    apply ψ.injective
    rw [map_mul, map_mul, hψz]
    exact hy
  have hmodd : Odd (orderOf α') := by
    have : orderOf α' = orderOf α := MulEquiv.orderOf_eq (MulAut.congr ψ) α
    rw [this]
    exact hαodd
  obtain ⟨g, σ, hσm, hgσ⟩ := g2_odd_normal_form_native hp hp2 hf hcard α' hmodd
  set m : ℕ := orderOf α' with hm
  have hα'm : α' ^ m = 1 := pow_orderOf_eq_one α'
  have hT : ∀ u : Fˣ, σ ((u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹)) =
      (u : F) ^ 2 + ((u : F)⁻¹) ^ 2 + 4 * ((u : F) + (u : F)⁻¹) := by
    intro u
    let dU : Ivk47ab.G2g F := ⟨rootDiagUnit .G2 (torusTupleG2 u), Ivk47ab.rootDiagUnit_mem_adjoint _⟩
    have hdU : dU ∈ centralizer ({Ivk47ab.z₀ F} : Set (Ivk47ab.G2g F)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      show rootDiagUnit .G2 (torusTupleG2 u) * rootDiagUnit .G2 (Ivk47ab.a₀ F) =
        rootDiagUnit .G2 (Ivk47ab.a₀ F) * rootDiagUnit .G2 (torusTupleG2 u)
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
    have h1 := hgσ dU
    rw [hα'fix dU hdU] at h1
    have hbσ : (fun i => Units.map σ.toRingHom.toMonoidHom (torusTupleG2 u i)) =
        torusTupleG2 (Units.map σ.toRingHom.toMonoidHom u) := by
      funext i
      fin_cases i
      · show Units.map σ.toRingHom.toMonoidHom (u ^ 2) = (Units.map σ.toRingHom.toMonoidHom u) ^ 2
        rw [map_pow]
      · show Units.map σ.toRingHom.toMonoidHom (u⁻¹) = (Units.map σ.toRingHom.toMonoidHom u)⁻¹
        rw [map_inv]
    have h2 : (rootDiagUnit .G2 (torusTupleG2 u) : ModGL .G2 F) =
        (g : ModGL .G2 F) * rootDiagUnit .G2 (torusTupleG2 (Units.map σ.toRingHom.toMonoidHom u)) *
          (g : ModGL .G2 F)⁻¹ := by
      have := h1
      change (rootDiagUnit .G2 (torusTupleG2 u) : ModGL .G2 F) = _ at this
      rw [units_map_entrywiseHom_rootDiagUnit_ringEquiv, hbσ] at this
      exact this
    have h3 := congrArg (fun x : ModGL .G2 F => LinearMap.trace F (RootModule .G2 F)
      (x : Module.End F (RootModule .G2 F))) h2
    simp only [Units.val_mul] at h3
    have h4 : LinearMap.trace F (RootModule .G2 F) (rootDiag (torusTupleG2 u)) =
        LinearMap.trace F (RootModule .G2 F) (rootDiag (torusTupleG2 (Units.map σ.toRingHom.toMonoidHom u))) := by
      rw [← trace_conj_unit (g : ModGL .G2 F) (rootDiag (torusTupleG2 (Units.map σ.toRingHom.toMonoidHom u)))]
      exact h3
    rw [trace_rootDiag_G2, trace_rootDiag_G2] at h4
    have e1 : ((Units.map σ.toRingHom.toMonoidHom u : Fˣ) : F) = σ (u : F) := rfl
    rw [e1] at h4
    simp only [map_add, map_pow, map_mul, map_inv₀, map_ofNat]
    linear_combination h4.symm
  have hσ1 : σ = 1 := sigma_eq_one_of_trace hchar σ hmodd hσm hT
  subst hσ1
  have hα'g : ∀ h : Ivk47ab.G2g F, α' h = g * h * g⁻¹ := by
    intro h
    apply Subtype.ext
    have h1 := hgσ h
    change ((α' h : Ivk47ab.G2g F) : ModGL .G2 F) = (g : ModGL .G2 F) *
      Units.map (entrywiseHom (1 : F ≃+* F).toRingHom) (h : ModGL .G2 F) * (g : ModGL .G2 F)⁻¹ at h1
    rw [units_map_entrywiseHom_one_ringEquiv] at h1
    rw [h1]
    simp
  let gK : K := ψ.symm g
  have hαg : ∀ x : K, α x = gK * x * gK⁻¹ := by
    intro x
    apply ψ.injective
    rw [← hα' x, hα'g, map_mul, map_mul, map_inv]
    simp [gK]
  have hgcen : ∀ x ∈ centralizer ({z} : Set K), gK * x = x * gK := by
    intro x hx
    have h1 := hαfix x hx
    rw [hαg] at h1
    calc gK * x = gK * x * gK⁻¹ * gK := by group
      _ = x * gK := by rw [h1]
  have hgC : gK ∈ centralizer ({z} : Set K) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hgcen z (Subgroup.mem_centralizer_singleton_iff.2 rfl)
  have hgm : g ^ m = 1 := by
    have hconj_eq : α' = MulAut.conj g := MulEquiv.ext fun h => by
      rw [hα'g]; simp [MulAut.conj_apply]
    have h1 : MulAut.conj (g ^ m) = (1 : MulAut (Ivk47ab.G2g F)) := by
      rw [map_pow, ← hconj_eq]; exact hα'm
    have hmem : g ^ m ∈ Subgroup.center (Ivk47ab.G2g F) := by
      rw [Subgroup.mem_center_iff]
      intro h
      have h2 := congrArg (fun a : MulAut (Ivk47ab.G2g F) => a h) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h2
      calc h * g ^ m = (g ^ m * h * (g ^ m)⁻¹) * g ^ m := by rw [h2]
        _ = g ^ m * h := by group
    have hZ : Subgroup.center (Ivk47ab.G2g F) = ⊥ := center_adjointGroup_eq_bot
    rw [hZ] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hgKm : gK ^ m = 1 := by
    apply ψ.injective
    rw [map_pow, map_one]
    simpa [gK] using hgm
  have hgKodd : Odd (orderOf gK) := Odd.of_dvd_nat hmodd (orderOf_dvd_of_pow_eq_one hgKm)
  obtain ⟨F', _, _, Sh, hcard', -⟩ := GHInv.exists_shape_G2 hp hp2 hLie z hz
  have hodd' : Odd (Nat.card F') := by rw [hcard']; exact (hp.odd_of_ne_two hp2).pow
  have h3' : 3 ≤ Nat.card F' := by rw [hcard']; omega
  have hbot : pPrimeCore 2 ↥(centralizer ({z} : Set K)) = ⊥ :=
    Ivk413.pPrimeCore_shape_eq_bot Sh hodd' h3' hodd' h3'
  let gC : ↥(centralizer ({z} : Set K)) := ⟨gK, hgC⟩
  have hgCc : ∀ y : ↥(centralizer ({z} : Set K)), y * gC = gC * y := fun y =>
    Subtype.ext (hgcen y y.2).symm
  have hN : (Subgroup.zpowers gC).Normal := by
    refine ⟨fun n hn y => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have hc : Commute y gC := hgCc y
    have : y * gC ^ k * y⁻¹ = gC ^ k := by
      rw [(hc.zpow_right k).eq]; group
    rw [this]
    exact Subgroup.zpow_mem_zpowers gC k
  have hcop : Nat.Coprime 2 (Nat.card (Subgroup.zpowers gC)) := by
    rw [Nat.card_zpowers]
    have : orderOf gC = orderOf gK := Subgroup.orderOf_mk gK hgC
    rw [this]
    exact Nat.coprime_two_left.2 hgKodd
  have hle := le_pPrimeCore_of_normal_coprime hN hcop
  rw [hbot] at hle
  have hgC1 : gC = 1 := by
    have := hle (Subgroup.mem_zpowers gC)
    simpa using this
  have hgK1 : gK = 1 := congrArg Subtype.val hgC1
  apply MulEquiv.ext
  intro x
  rw [hαg, hgK1]
  simp

end Main

end CFSG.GH74.GLS.IVK.Proofs2
