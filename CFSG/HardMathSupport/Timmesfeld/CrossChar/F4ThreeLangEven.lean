module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidF4Even
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.BadThreeLang
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.SteinbergLangRigid

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.LocalTwo CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.RankThree.PartOne.KE CFSG.HardMathSupport.Timmesfeld.DefChar CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Ree

set_option linter.unusedSectionVars false

theorem steinbergLang_eq_one_of_fieldType {τ : Tag} {L : Type} [Field L] [IsAlgClosed L] {p : ℕ}
    (S : LangSetup τ L p) {K : Type} [Field K] [Finite K] [Algebra K L] {p₀ f : ℕ}
    (hp₀ : p₀.Prime) (hf : 1 ≤ f) (hK : Nat.card K = p₀ ^ f) (hq : Nat.card K = S.D.q)
    [CharP L p₀] (e : adjointGroup τ K ≃* S.Γ)
    (he : ∀ h : adjointGroup τ K, (e h : ModGL τ L) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K L) (h : ModGL τ K) * S.D.g0)
    {D₁ : Subgroup (ModGL τ L)} (hD₁E : D₁ ≤ S.E) (hF : NoFrobeniusInner S D₁)
    (hI : CentralizerTrivial S D₁) (δ : MulAut S.Γ)
    (hfix : ∀ x : S.Γ, (x : ModGL τ L) ∈ rigidTestSet S D₁ → δ x = x)
    (y : ModGL τ K) (σ : K ≃+* K) (hyC : baseChangeGL (algebraMap K L) y ∈ adjointGroup τ L)
    (hy : ∀ h : adjointGroup τ K, (((e.trans δ).trans e.symm) h : ModGL τ K) =
      y * Units.map (entrywiseHom σ.toRingHom) (h : ModGL τ K) * y⁻¹) : δ = 1 := by
  classical
  have : ExpChar L p₀ := ExpChar.prime hp₀
  have hg0C := S.D.g0_mem
  obtain ⟨j, hj, hσj⟩ := CFSG.GH74.GLS.Stage2.OddAut.exists_frobenius_pow hp₀ hf hK σ
  obtain ⟨σ', hσ'⟩ : ∃ σ' : L →+* L, σ' = iterateFrobenius L p₀ j := ⟨_, rfl⟩
  have hσ'ι : ∀ c : K, σ' (algebraMap K L c) = algebraMap K L (σ.toRingHom c) := fun c => by
    rw [hσ', iterateFrobenius_def, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, hσj, map_pow]
  have hbase : ∀ g : ModGL τ K,
      baseChangeGL (algebraMap K L) (Units.map (entrywiseHom σ.toRingHom) g) =
        Units.map (entrywiseHom σ') (baseChangeGL (algebraMap K L) g) := fun g => by
    have h1 : σ'.comp (algebraMap K L) = (algebraMap K L).comp σ.toRingHom := RingHom.ext hσ'ι
    rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, h1]
  obtain ⟨z, hz⟩ : ∃ z : ModGL τ L, z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y *
      Units.map (entrywiseHom σ') S.D.g0 := ⟨_, rfl⟩
  have hδx : ∀ x : S.Γ, (δ x : ModGL τ L) = z * Units.map (entrywiseHom σ') x * z⁻¹ := by
    intro x
    obtain ⟨h, rfl⟩ := e.surjective x
    have h1 : δ (e h) = e (((e.trans δ).trans e.symm) h) := by simp
    have h2 : baseChangeGL (algebraMap K L) (h : ModGL τ K) =
        S.D.g0 * (e h : ModGL τ L) * S.D.g0⁻¹ := by
      rw [he]
      group
    rw [h1, he, hy, map_mul, map_mul, map_inv, hbase, h2, map_mul, map_mul, map_inv, hz]
    group
  have hfix' : ∀ x ∈ rigidTestSet S D₁, z * Units.map (entrywiseHom σ') x * z⁻¹ = x := by
    intro x hx
    have hxΓ : x ∈ S.Γ := rigidTestSet_subset_Γ S hD₁E hx
    have h2 := hδx ⟨x, hxΓ⟩
    rw [hfix ⟨x, hxΓ⟩ hx] at h2
    exact h2.symm
  have hj0 : j = 0 := by
    by_contra hj0
    exact hF p₀ f j hp₀ (hq.symm.trans hK) (Nat.pos_of_ne_zero hj0) hj z
      (by rw [hσ'] at hfix'; exact hfix')
  have hF1 : ∀ x : ModGL τ L, Units.map (entrywiseHom σ') x = x := fun x => by
    rw [hσ', hj0, iterateFrobenius_zero]
    exact Units.ext (entrywise_id _)
  have hzC : z ∈ adjointGroup τ L := by
    have : z = S.D.g0⁻¹ * baseChangeGL (algebraMap K L) y * S.D.g0 := by rw [hz, hF1]
    rw [this]
    exact mul_mem (mul_mem (inv_mem hg0C) hyC) hg0C
  have hcomm : ∀ x ∈ rigidTestSet S D₁, Commute z x := by
    intro x hx
    have h1 := hfix' x hx
    rw [hF1] at h1
    show z * x = x * z
    calc z * (x : ModGL τ L) = z * x * z⁻¹ * z := by group
      _ = x * z := by rw [h1]
  have hz1 := hI z hzC hcomm
  refine MulEquiv.ext fun x => Subtype.ext ?_
  rw [hδx, hF1, hz1, MulAut.one_apply]
  group

@[expose] def F4ThreeEvenGraphRigid : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (m : ℕ), 1 ≤ m → Nat.card K = 2 ^ (2 * m + 1) →
    ∀ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
      (w : WeylGroup Tag.F4) (g0 : ModGL Tag.F4 (AlgebraicClosure K))
      (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
      (hg0 : Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
      (S : LangSetup Tag.F4 (AlgebraicClosure K) 3),
      S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0 →
    ∀ D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)), D₁ ≤ S.E → Nat.card D₁ = 3 ^ 2 →
    ∀ δ : MulAut S.Γ, δ ^ 2 = 1 → δ ∉ (MulAut.conj : S.Γ →* MulAut S.Γ).range →
      ¬ ∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ → δ x = x

section Rigid

variable (K : Type) [Field K] [Finite K] {Fr : AlgebraicClosure K →+* AlgebraicClosure K}
  (hFr : ∀ c, Fr c = c ^ Nat.card K) {w : WeylGroup Tag.F4}
  {g0 : ModGL Tag.F4 (AlgebraicClosure K)} (hg0C : g0 ∈ adjointGroup Tag.F4 (AlgebraicClosure K))
  (hg0 : Units.map (entrywiseHom Fr) g0 =
    g0 * canonicalRep (coxeterSystem Tag.F4) (AlgebraicClosure K) w)
  (S : LangSetup Tag.F4 (AlgebraicClosure K) 3)
  (hSD : S.D = LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0C hg0)

include hSD in
theorem f4Three_setupRigid_even_of
    (hQ : ThreeLargeQ (Nat.card K)) (hev : Even (Nat.card K))
    (hgraph : ∀ m : ℕ, 1 ≤ m → Nat.card K = 2 ^ (2 * m + 1) →
      ∀ D₁ : Subgroup (ModGL Tag.F4 (AlgebraicClosure K)), D₁ ≤ S.E → Nat.card D₁ = 3 ^ 2 →
      ∀ δ : MulAut S.Γ, δ ^ 2 = 1 → δ ∉ (MulAut.conj : S.Γ →* MulAut S.Γ).range →
        ¬ ∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ → δ x = x) :
    SetupRigid S := by
  classical
  obtain ⟨p₀, f, hp₀, hf, hK, hchar⟩ := exists_char_data K (AlgebraicClosure K)
  have hp₀2 : p₀ = 2 := by
    by_contra hne
    have hodd : Odd (p₀ ^ f) := (hp₀.odd_of_ne_two hne).pow
    rw [← hK] at hodd
    exact (Nat.not_even_iff_odd.2 hodd) hev
  subst hp₀2
  have : CharP K 2 := finite_field_prime_power_characteristic hp₀ hf hK
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq := steinbergLang_q_eq K hFr hg0C hg0 S hSD
  obtain ⟨h3, h2, h4⟩ := hQ
  have hf3 : 3 ≤ f := by
    by_contra hlt
    have : f = 1 ∨ f = 2 := by omega
    rcases this with rfl | rfl
    · exact h2 (by rw [hK]; norm_num)
    · exact h4 (by rw [hK]; norm_num)
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hqp : Nat.card K % 3 = 1 ∨ Nat.card K % 3 = 3 - 1 := by omega
  have hst : ∀ b : Fin Tag.F4.rank → (AlgebraicClosure K)ˣ, (∀ i, b i ^ 3 = 1) →
      rootCharStabilizerSubgroup b ≤ kernelReflectionGroup b := fun b hb =>
    (Steinberg.rootCharStabilizerSubgroup_eq_kernelReflectionGroup_F4_three b hb).le
  have hdeg : entryDegreeBound Tag.F4 < Nat.card K := by
    simp [entryDegreeBound]
    omega
  have hd := langDescent_ofFrobenius (Or.inl rfl) w K hFr hg0C hg0
  rw [← hSD] at hd
  have hι : Function.Injective ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      (adjointGroup Tag.F4 K).subtype) :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  set e : adjointGroup Tag.F4 K ≃* S.Γ := hd.mulEquiv' hι with he_def
  have he : ∀ h : adjointGroup Tag.F4 K, (e h : ModGL Tag.F4 (AlgebraicClosure K)) =
      S.D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (h : ModGL Tag.F4 K) *
        S.D.g0 :=
    fun h => hd.coe_mulEquiv' hι h
  set φ : MulAut (adjointGroup Tag.F4 K) := ReeTag.F4.finiteExceptionalAut K with hφ
  obtain ⟨-, hNF, -, hINV, -, -, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  have hNF' : ∀ α : MulAut (adjointGroup Tag.F4 K),
      ∃! gk : adjointGroup Tag.F4 K × Fin (2 * f), α = MulAut.conj gk.1 * φ ^ (gk.2 : ℕ) := hNF
  have hINV' : ∀ (α : MulAut (adjointGroup Tag.F4 K)) (g : adjointGroup Tag.F4 K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * φ ^ k → α ^ 2 = 1 → k = 0 ∨ k = f := hINV
  have hpow2 : ∀ (j : ℕ) {σ : K ≃+* K}, (∀ c, σ c = c ^ 2 ^ j) → ∀ h : adjointGroup Tag.F4 K,
      ((φ ^ (2 * j)) h : ModGL Tag.F4 K) = Units.map (entrywiseHom σ.toRingHom) h :=
    fun j _ hσ h => coe_finiteExceptionalAut_pow_two_mul j hσ h
  intro D₁ hD₁E hD₁c δ _ hfixD hfixX
  have hF : NoFrobeniusInner S D₁ := steinbergLang_noFrobeniusInner K hFr hg0C hg0 S hSD
    (by decide) Nat.prime_three hst f4Neg_smul hqp hK4 (Or.inl h4) hD₁E hD₁c
  have hI : CentralizerTrivial S D₁ := steinbergLang_centralizerTrivial K hFr hg0C hg0 S hSD
    Nat.prime_three hst f4Neg_smul hqp hK4 hdeg hD₁E hD₁c
  have hfix : ∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ →
      δ x = x := fun x hx => by
    rcases hx with hx | hx
    · exact hfixX x hx
    · exact hfixD x hx
  have hfieldtype : ∀ δ' : MulAut S.Γ,
      (∀ x : S.Γ, (x : ModGL Tag.F4 (AlgebraicClosure K)) ∈ rigidTestSet S D₁ → δ' x = x) →
      ∀ (g : adjointGroup Tag.F4 K) (j : ℕ),
        (e.trans δ').trans e.symm = MulAut.conj g * φ ^ (2 * j) → δ' = 1 := by
    intro δ' hδ' g j hα
    obtain ⟨σ, hσ⟩ := CFSG.RankThree.Chevalley.exists_frobenius_pow (L := K) (ℓ := 2) j
    refine steinbergLang_eq_one_of_fieldType S hp₀ hf hK hq.symm e he hD₁E hF hI δ' hδ'
      (g : ModGL Tag.F4 K) σ (LieType.Chevalley.baseChangeGL_mem_adjointGroup _ g.2)
      fun h => ?_
    rw [hα, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
      Subgroup.coe_inv, hpow2 j hσ h]
  set α := (e.trans δ).trans e.symm with hαdef
  obtain ⟨⟨g, k⟩, hgk, huniq⟩ := hNF' α
  simp only at hgk
  rcases Nat.even_or_odd (k : ℕ) with ⟨m, hm⟩ | hodd
  · exact hfieldtype δ hfix g m (hgk.trans (by rw [hm, ← two_mul]))
  exfalso
  have hconj : ∀ (ψ : MulAut (adjointGroup Tag.F4 K)) (x : adjointGroup Tag.F4 K),
      ψ * MulAut.conj x = MulAut.conj (ψ x) * ψ := fun ψ x => by
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
  set k₀ : ℕ := (k : ℕ) with hk₀
  have hα2form : α ^ 2 = MulAut.conj (g * (φ ^ k₀) g) * φ ^ (2 * k₀) := by
    rw [hgk, pow_two, mul_assoc, ← mul_assoc (φ ^ k₀), hconj, mul_assoc, ← pow_add,
      ← mul_assoc, ← map_mul, ← two_mul]
  have hsq : (e.trans (δ ^ 2)).trans e.symm = α ^ 2 := by
    ext h
    simp only [hαdef, pow_two, MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  have hδ2 : δ ^ 2 = 1 := hfieldtype (δ ^ 2)
    (fun x hx => by rw [pow_two, MulAut.mul_apply, hfix x hx, hfix x hx])
    (g * (φ ^ k₀) g) k₀ (by rw [hsq, hα2form])
  have hα2 : α ^ 2 = 1 := by
    rw [← hsq, hδ2]
    ext h
    simp
  have hkf : k₀ = f := (hINV' α g k₀ k.2 hgk hα2).resolve_left (by obtain ⟨r, hr⟩ := hodd; omega)
  obtain ⟨m', hm'⟩ : ∃ m', f = 2 * m' + 1 := by
    obtain ⟨r, hr⟩ := hodd
    exact ⟨r, by omega⟩
  have hαo : α ∉ (MulAut.conj : adjointGroup Tag.F4 K →* MulAut (adjointGroup Tag.F4 K)).range := by
    rintro ⟨x, hx⟩
    have h0 := huniq ⟨x, ⟨0, by omega⟩⟩ (by
      change α = MulAut.conj x * φ ^ (0 : ℕ)
      rw [pow_zero, mul_one, hx])
    have h1 := congrArg (fun z : adjointGroup Tag.F4 K × Fin (2 * f) => (z.2 : ℕ)) h0
    simp only at h1
    omega
  have hδo : δ ∉ (MulAut.conj : S.Γ →* MulAut S.Γ).range := by
    rintro ⟨x, hx⟩
    refine hαo ⟨e.symm x, ?_⟩
    ext h
    simp only [hαdef, ← hx, MulAut.conj_apply, MulEquiv.trans_apply, map_mul, map_inv,
      MulEquiv.symm_apply_apply]
  exact hgraph m' (by omega) (by rw [hK, hm']) D₁ hD₁E hD₁c δ hδ2 hδo hfix

include hSD in
theorem f4Three_setupRigid_even
    (hgraph : F4ThreeEvenGraphRigid) (hQ : ThreeLargeQ (Nat.card K)) (hev : Even (Nat.card K)) :
    SetupRigid S :=
  f4Three_setupRigid_even_of K hFr hg0C hg0 S hSD hQ hev fun m hm hK =>
    hgraph K m hm hK Fr hFr w g0 hg0C hg0 S hSD

end Rigid

section Balance

variable
  (hsub : LangSubnormal) (hin : LangComponentsQuasisimple .inner)
  (hsu : LangComponentsQuasisimple .suN) (htw : LangComponentsQuasisimple .twoD)
  (hex : LangComponentsQuasisimple .exc)

include hsub hin hsu htw hex

theorem f4Three_langTorusPlaneBalance_even (hgraph : F4ThreeEvenGraphRigid)
    (w : WeylGroup Tag.F4) :
    LangTorusPlaneBalance Tag.F4 w 3 fun q => ThreeLargeQ q ∧ Even q :=
  langTorusPlaneBalance_of_setupRigidAt (Or.inl rfl)
    (fun K _ _ => commutator_adjointGroup_F4_eq_top K) w Nat.prime_three
    (fun q hq2 hQ => ⟨hQ.1.1, Or.inr (by
      obtain ⟨⟨h3, h2, h4⟩, -⟩ := hQ
      omega)⟩)
    (fun K _ _ Fr hFr g0 hg0C hg0 S hSD hQK => by
      have : IsAlgClosed (AlgebraicClosure K) := IsAlgClosure.isAlgClosed K
      exact f4Three_setupRigid_even K hFr hg0C hg0 S hSD hgraph hQK.1 hQK.2)
    hsub hin hsu htw hex

end Balance

end CFSG.HardMathSupport.Timmesfeld.CrossChar
