module

public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267ModelGenB

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_conj_entrywise_excE_of_not_innerDiag {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {β : MulAut (adjointGroup τ K)} (hβp : β ^ p = 1)
    (hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
      β ≠ MulAut.conj g * rootDiagAut τ K a) :
    ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
      δ * β * δ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  haveI : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  obtain ⟨-, T, r, j, ψ, -, -, -, -, hTj, hαβ, hψ⟩ :=
    CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag τ hτ n.pos K hK
      hp hp2 β hβp hnd
  refine ⟨T ^ j, ψ, hTj, ?_⟩
  conv_lhs => rw [← hαβ]
  rw [← conj_pow, hψ, ← entrywiseAdjointAut_pow]

theorem exists_conj_entrywise_excE {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type}
    [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : τ = .E6 → p ≠ 3)
    {β : MulAut (adjointGroup τ K)} (hβp : β ^ p = 1)
    (hβ : β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
      δ * β * δ⁻¹ = entrywiseAdjointAut τ σ := by
  have hdet : ¬ p ∣ τ.cartan.det.natAbs := by
    rcases hτ with rfl | rfl | rfl
    · rw [det_cartan_E6]
      exact fun h => hp3 rfl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
    · rw [det_cartan_E7]
      exact fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    · rw [det_cartan_E8]
      exact hp.not_dvd_one
  exact exists_conj_entrywise_excE_of_not_innerDiag hτ hp hp2 hβp fun g a h => hdet
    (CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hτ K hp g a β h hβp hβ).1

theorem exists_conj_entrywise_excF4 {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2)
    {p : ℕ} (hp : p.Prime) {β : MulAut (adjointGroup .F4 K)} (hβp : β ^ p = 1)
    (hβ : β ∉ (MulAut.conj : adjointGroup .F4 K →* MulAut (adjointGroup .F4 K)).range) :
    ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup .F4 K)), orderOf σ = p ∧
      δ * β * δ⁻¹ = entrywiseAdjointAut .F4 σ := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
  haveI : Fact p.Prime := ⟨hp⟩
  have hβo : orderOf β = p := orderOf_eq_prime hβp fun h => hβ ⟨1, by rw [h, map_one]⟩
  obtain ⟨-, σ, δ, hσ, -, hδ, -⟩ := odd_F4_prime_field_coset_descent hℓ hK2 n.pos K hK hp β hβo hβ
  exact ⟨σ, δ, hσ, hδ⟩

theorem exists_conj_entrywise_exc {τ : Tag} (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {K : Type} [Field K] [Finite K] (hK2 : ringChar K ≠ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : τ = .E6 → p ≠ 3) {β : MulAut (adjointGroup τ K)} (hβp : β ^ p = 1)
    (hβ : β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range) :
    ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
      δ * β * δ⁻¹ = entrywiseAdjointAut τ σ := by
  rcases hτ with rfl | hE
  · exact exists_conj_entrywise_excF4 hK2 hp hβp hβ
  · exact exists_conj_entrywise_excE hE hp hp2 hp3 hβp hβ

variable {Ω : Type} [Group Ω] {S : Subgroup Ω}

theorem exists_fieldTransport_of_nf {τ : Tag} {K : Type} [Field K] {p : ℕ}
    (hNF : ∀ β : MulAut (adjointGroup τ K), β ^ p = 1 →
      β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
        δ * β * δ⁻¹ = entrywiseAdjointAut τ σ)
    {φ : adjointGroup τ K →* Ω} (hφ : Function.Injective φ)
    (hφS : φ.range = S) {b : Ω} (hbp : b ^ p = 1) {β : MulAut (adjointGroup τ K)}
    (hβ : β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hβφ : ∀ x, φ (β x) = b * φ x * b⁻¹) :
    ∃ (σ : K ≃+* K) (φ' : adjointGroup τ K →* Ω), orderOf σ = p ∧
      entrywiseAdjointAut τ σ ∉
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range ∧
      Function.Injective φ' ∧ φ'.range = S ∧
      ∀ x, b * φ' x * b⁻¹ = φ' (entrywiseAdjointAut τ σ x) := by
  have hβk : ∀ k : ℕ, ∀ x, φ ((β ^ k) x) = b ^ k * φ x * (b ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      rw [pow_succ β k, MulAut.mul_apply, ih, hβφ, pow_succ b k]
      group
  have hβp : β ^ p = 1 := by
    refine MulEquiv.ext fun x => hφ ?_
    rw [hβk p x, hbp, one_mul, inv_one, mul_one, MulAut.one_apply]
  obtain ⟨σ, δ, hσ, hδ⟩ := hNF β hβp hβ
  refine ⟨σ, φ.comp δ.symm.toMonoidHom, hσ, ?_, hφ.comp δ.symm.injective, ?_, fun x => ?_⟩
  · rintro ⟨g, hg⟩
    refine hβ ⟨δ⁻¹ g, MulEquiv.ext fun x => ?_⟩
    have h1 : β = δ⁻¹ * entrywiseAdjointAut τ σ * δ := by rw [← hδ]; group
    rw [h1, ← hg, MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_apply,
      map_mul, map_mul, map_inv, MulAut.inv_apply_self]
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 δ.symm.surjective,
      ← MonoidHom.range_eq_map, hφS]
  · rw [← hδ, MulAut.mul_apply, MulAut.mul_apply]
    change b * φ (δ.symm x) * b⁻¹ = φ (δ.symm (δ (β (δ⁻¹ x))))
    rw [MulEquiv.symm_apply_apply, hβφ]
    rfl

theorem concA_of_outer_of_nf [Finite Ω] {B : Subgroup Ω} {τ : Tag} {K : Type} [Field K]
    {p n : ℕ} (hp : p.Prime)
    (hNF : ∀ β : MulAut (adjointGroup τ K), β ^ p = 1 →
      β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ∃ (σ : K ≃+* K) (δ : MulAut (adjointGroup τ K)), orderOf σ = p ∧
        δ * β * δ⁻¹ = entrywiseAdjointAut τ σ)
    (hn : 2 ≤ n) (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBn : Nat.card B ≤ p ^ (n + 2))
    {φ : adjointGroup τ K →* Ω} (hφ : Function.Injective φ) (hφS : φ.range = S) {b : Ω}
    (hb : b ∈ B) {β : MulAut (adjointGroup τ K)}
    (hβ : β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hβφ : ∀ x, φ (β x) = b * φ x * b⁻¹)
    (hM : ∀ σ : K ≃+* K, orderOf σ = p → entrywiseAdjointAut τ σ ∉
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ModelGen.ModelBGen p n (adjointGroup τ K) (entrywiseAdjointAut τ σ)) :
    S267ConcA p S B := by
  have : Finite ↥(adjointGroup τ K) := Finite.of_injective φ hφ
  obtain ⟨σ, φ', hσ, hout, hφ', hφ'S, hbφ'⟩ :=
    exists_fieldTransport_of_nf hNF hφ hφS (hB.2 b hb) hβ hβφ
  exact ModelGen.concA_of_modelBGen hp hn hSn hcore hZ hB hBC hBn φ' hφ' hφ'S (hB.2 b hb)
    (fun c hc => congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨c, hc.1⟩)) hbφ'
    (hM σ hσ hout)

theorem concA_of_outer_exc [Finite Ω] {B : Subgroup Ω} {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : τ = .E6 → p ≠ 3)
    (hn : 2 ≤ n) (hSn : S.Normal) (hcore : GLAPPrimeCore p ↥S = ⊥)
    (hZ : Subgroup.center ↥S = ⊥) (hB : IsElemAbelian p B)
    (hBC : Nat.card ↥(B ⊓ centModSubgroup p S) = p) (hBn : Nat.card B ≤ p ^ (n + 2))
    {φ : adjointGroup τ K →* Ω} (hφ : Function.Injective φ) (hφS : φ.range = S) {b : Ω}
    (hb : b ∈ B) {β : MulAut (adjointGroup τ K)}
    (hβ : β ∉ (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hβφ : ∀ x, φ (β x) = b * φ x * b⁻¹)
    (hM : ∀ σ : K ≃+* K, orderOf σ = p → entrywiseAdjointAut τ σ ∉
        (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range →
      ModelGen.ModelBGen p n (adjointGroup τ K) (entrywiseAdjointAut τ σ)) :
    S267ConcA p S B :=
  concA_of_outer_of_nf hp (fun _ h1 h2 => exists_conj_entrywise_exc hτ hK2 hp hp2 hp3 h1 h2) hn
    hSn hcore hZ hB hBC hBn hφ hφS hb hβ hβφ hM

end CFSG.LocalAnalysis.GLTheoremA.S267.BadExc

end
