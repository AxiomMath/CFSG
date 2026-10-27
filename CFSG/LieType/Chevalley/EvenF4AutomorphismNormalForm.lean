module

public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm
public import CFSG.LieType.Chevalley.EvenF4SimplePairs
import CFSG.LieType.Chevalley.EvenF4RawBorel
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.B3Unconditional
public import CFSG.LieType.AlgebraicGroups.FrobeniusDiagramRealized
import CFSG.LocalAnalysis.EvenBN.G2.Automorphisms
import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.CenterProofFastPart2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutDiagBasic
public import CFSG.LieType.Chevalley.RootCommutatorPairTable

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Ree RootOps
open scoped commutatorElement

section Generic

variable {K : Type} [Field K] [Finite K] (t : ReeTag) [CharP K t.prime]

theorem ree_two_mul_dvd_of_pow_eq_conj
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = t.prime ^ f)
    {i₀ : Fin t.tag.rank} (hi₀ : t.perm i₀ ≠ i₀) {k : ℕ} {h : adjointGroup t.tag K}
    (hk : t.finiteExceptionalAut K ^ k = MulAut.conj h) : 2 * f ∣ k := by
  have hp : t.prime.Prime := Fact.out
  have hA : MulAut.conj h ∈ unipotentPairAut t.tag K :=
    hk ▸ pow_mem (finiteExceptionalAut_mem_unipotentPairAut t) k
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · obtain ⟨fr, hfr, hord, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
    rw [finiteExceptionalAut_pow_two_mul, ← exactNormalAut_one_eq_finiteFrobeniusAut_pow
      t (σ := fr ^ j) (ringAut_pow_apply_of_frobenius hfr j), hb] at hk
    obtain ⟨-, h1⟩ := exactNormalAut_zero_injective hk
    exact Nat.mul_dvd_mul_left 2 (hord ▸ orderOf_dvd_of_pow_eq_one h1)
  · exfalso
    have e := congrArg (fun α : MulAut (adjointGroup t.tag K) => α (adjX t.tag K i₀ 1)) hk
    simp only [hb, exactNormalAut_zero_adjX] at e
    rw [pow_succ', MulAut.mul_apply, finiteExceptionalAut_pow_two_mul] at e
    have e2 : (t.finiteFrobeniusAut K ^ j) (adjX t.tag K i₀ 1) = adjX t.tag K i₀ 1 := by
      change (t.finiteFrobeniusAut K ^ j) (xElement _ 1) = xElement _ 1
      rw [ReeTag.finiteFrobeniusAut_pow_xElement, one_pow]
    have e3 : t.finiteExceptionalAut K (adjX t.tag K i₀ 1) = adjX t.tag K (t.perm i₀) 1 := by
      change t.finiteExceptionalAut K (xElement _ 1) = xElement _ 1
      rw [ReeTag.finiteExceptionalAut_xElement, one_pow]
    rw [e2, e3] at e
    have e' : xUnit t.tag K (t.perm i₀) 1 =
        xUnit t.tag K i₀ ((b i₀ : K) * (1 : K ≃+* K) 1) := congrArg Subtype.val e
    apply not_commute_xUnit_yUnit (τ := t.tag) (K := K) (t.perm i₀)
    rw [e']
    exact commute_xUnit_yUnit_of_ne' (Ne.symm hi₀) _ 1

theorem ree_exists_conj_mul_pow
    {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = t.prime ^ f)
    (hperm : ∀ β ∈ unipotentPairAut t.tag K, ∀ π : Equiv.Perm (Fin t.tag.rank),
      (∀ i, (simplePosSubgroup t.tag K i).map β.toMonoidHom = simplePosSubgroup t.tag K (π i) ∧
        (simpleNegSubgroup t.tag K i).map β.toMonoidHom = simpleNegSubgroup t.tag K (π i)) →
      π = 1 ∨ π = t.perm)
    (hdC : ∀ a : Fin t.tag.rank → Kˣ, rootDiagUnit t.tag a ∈ adjointGroup t.tag K)
    (α : MulAut (adjointGroup t.tag K)) :
    ∃ (g : adjointGroup t.tag K) (k : ℕ), α = MulAut.conj g * t.finiteExceptionalAut K ^ k := by
  have hp : t.prime.Prime := Fact.out
  have hφ2f : t.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card t hK
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem t.tag).length
  obtain ⟨c, β, hβ, rfl⟩ : ∃ (c : adjointGroup t.tag K)
      (β : MulAut (adjointGroup t.tag K)),
      β ∈ unipotentPairAut t.tag K ∧ α = MulAut.conj c * β := by
    by_cases ht : t = ReeTag.F4
    · subst t
      exact f4_exists_conj_mul_unipotentPair 2 w₀ hw₀ α
    · obtain ⟨c, β, hU, hV, hα⟩ :=
        (exceptional_ordinary_Sylow_opposition t.tag K t.prime w₀ hw₀).2.2.2.2.2 α
      exact ⟨c, β, ⟨hU, hV⟩, hα⟩
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin t.tag.rank), ∀ i,
      (simplePosSubgroup t.tag K i).map β.toMonoidHom = simplePosSubgroup t.tag K (π i) ∧
      (simpleNegSubgroup t.tag K i).map β.toMonoidHom = simpleNegSubgroup t.tag K (π i) := by
    by_cases ht : t = ReeTag.F4
    · subst t
      exact f4_exists_perm_map_simple hβ
    · exact exists_perm_map_simple hβ
  obtain ⟨ζ, ε, hζ, rfl⟩ : ∃ (ζ : MulAut (adjointGroup t.tag K)) (ε : ℕ),
      ζ ∈ rootPairAut t.tag K ∧ β = ζ * t.finiteExceptionalAut K ^ ε := by
    rcases hperm β hβ π hπ with rfl | rfl
    · exact ⟨β, 0, mem_rootPairAut.2 fun i => ⟨(hπ i).1, (hπ i).2⟩, by rw [pow_zero, mul_one]⟩
    · refine ⟨β * t.finiteExceptionalAut K, 2 * f - 1,
        mem_rootPairAut.2 fun i => ⟨?_, ?_⟩, ?_⟩
      · rw [map_toMonoidHom_mul_mulAut, map_simplePosSubgroup_finiteExceptionalAut, (hπ _).1,
          ReeTag.perm_perm]
      · rw [map_toMonoidHom_mul_mulAut, map_simpleNegSubgroup_finiteExceptionalAut, (hπ _).2,
          ReeTag.perm_perm]
      · rw [mul_assoc, ← pow_succ', Nat.sub_add_cancel (by omega), hφ2f, mul_one]
  obtain ⟨p, hp', -⟩ :=
    (ordinary_Chevalley_root_pair_common_field_parameter t.tag K).1 ζ hζ
  have hζN : ζ = exactNormalAut t.tag K p.1 p.2 0 :=
    mulAut_ext_adjX_adjY (fun i c => by rw [(hp' i).1, exactNormalAut_zero_adjX])
      fun i c => by rw [(hp' i).2.1, exactNormalAut_zero_adjY]
  obtain ⟨fr, hfr, hord, htop, -⟩ := finite_field_automorphism_fixed_field_cardinality hp hf hK
  have hfin : IsOfFinOrder fr := orderOf_pos_iff.1 (by rw [hord]; omega)
  obtain ⟨m, hm⟩ := (Submonoid.mem_powers_iff _ _).1
    (hfin.mem_powers_iff_mem_zpowers.2 (by rw [htop]; exact Subgroup.mem_top p.2))
  have hN : exactNormalAut t.tag K p.1 p.2 0 =
      MulAut.conj (⟨rootDiagUnit t.tag p.1, hdC p.1⟩ : adjointGroup t.tag K) *
        t.finiteExceptionalAut K ^ (2 * m) := by
    calc exactNormalAut t.tag K p.1 p.2 0 = exactNormalAut t.tag K (p.1 * 1) p.2 0 := by
          rw [mul_one]
      _ = exactNormalAut t.tag K p.1 1 0 * exactNormalAut t.tag K 1 p.2 0 :=
          (exactNormalAut_diag_mul _ _ _ _).symm
      _ = _ := by
          rw [exactNormalAut_diag_eq_conj _ (hdC p.1), ← hm,
            exactNormalAut_one_eq_finiteFrobeniusAut_pow t (ringAut_pow_apply_of_frobenius hfr m),
            finiteExceptionalAut_pow_two_mul]
  refine ⟨c * ⟨rootDiagUnit t.tag p.1, hdC p.1⟩, 2 * m + ε, ?_⟩
  rw [hζN, hN, map_mul, pow_add]
  simp only [mul_assoc]

theorem ree_exact_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = t.prime ^ f)
    (hperm : ∀ β ∈ unipotentPairAut t.tag K, ∀ π : Equiv.Perm (Fin t.tag.rank),
      (∀ i, (simplePosSubgroup t.tag K i).map β.toMonoidHom = simplePosSubgroup t.tag K (π i) ∧
        (simpleNegSubgroup t.tag K i).map β.toMonoidHom = simpleNegSubgroup t.tag K (π i)) →
      π = 1 ∨ π = t.perm)
    (hdC : ∀ a : Fin t.tag.rank → Kˣ, rootDiagUnit t.tag a ∈ adjointGroup t.tag K)
    {i₀ : Fin t.tag.rank} (hi₀ : t.perm i₀ ≠ i₀) :
    orderOf (t.finiteExceptionalAut K) = 2 * f ∧
    (∀ α : MulAut (adjointGroup t.tag K),
      ∃! gk : adjointGroup t.tag K × Fin (2 * f),
        α = MulAut.conj gk.1 * t.finiteExceptionalAut K ^ (gk.2 : ℕ)) ∧
    (∃ Θ : MulAut (adjointGroup t.tag K) →* Multiplicative (ZMod (2 * f)),
      (∀ (α : MulAut (adjointGroup t.tag K)) (g : adjointGroup t.tag K) (k : ℕ),
        α = MulAut.conj g * t.finiteExceptionalAut K ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f))) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup t.tag K →* MulAut (adjointGroup t.tag K)).range) ∧
    (∀ (α : MulAut (adjointGroup t.tag K)) (g : adjointGroup t.tag K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * t.finiteExceptionalAut K ^ k → α ^ 2 = 1 →
        k = 0 ∨ k = f) ∧
    ((t.finiteExceptionalAut K ^ f) ^ 2 = 1 ∧ t.finiteExceptionalAut K ^ f ≠ 1) ∧
    (∀ e : ℕ, f = 2 * e → t.finiteExceptionalAut K ^ f = t.finiteFrobeniusAut K ^ e) ∧
    ∀ a : ℕ, f = 2 * a + 1 →
      t.finiteExceptionalAut K ^ f = t.finiteExceptionalAut K * t.finiteFrobeniusAut K ^ a ∧
        t.finiteExceptionalAut K ^ f = t.finiteReeAut K a ∧
        ∀ g : adjointGroup t.tag K,
          g ∈ t.finiteReeFixedGroup K a ↔ (t.finiteExceptionalAut K ^ f) g = g := by
  have hφ2f : t.finiteExceptionalAut K ^ (2 * f) = 1 := by
    rw [finiteExceptionalAut_pow_two_mul]
    exact finiteFrobeniusAut_pow_card t hK
  obtain ⟨hord, hNF, hΘ, hinv⟩ := mulAut_cyclic_complement_normal_form center_adjointGroup_eq_bot
    (t.finiteExceptionalAut K) (by omega) hφ2f (ree_exists_conj_mul_pow t hf hK hperm hdC)
    fun k h hk => ree_two_mul_dvd_of_pow_eq_conj t hf hK hi₀ hk
  refine ⟨hord, hNF, hΘ, fun α g k hk hα h2 => ?_, ⟨?_, ?_⟩, fun e he => ?_, fun a ha => ?_⟩
  ·
    obtain ⟨m, rfl⟩ := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).1 (hinv α g k hα h2)
    have hm : m < 2 := Nat.lt_of_mul_lt_mul_left (by linarith : f * m < f * 2)
    interval_cases m <;> simp
  · rw [← pow_mul, mul_comm, hφ2f]
  · intro h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hord] at this
    exact absurd (Nat.le_of_dvd (by omega) this) (by omega)
  · rw [he]
    exact finiteExceptionalAut_pow_two_mul t e
  · have hφf : t.finiteExceptionalAut K ^ f =
        t.finiteExceptionalAut K * t.finiteFrobeniusAut K ^ a := by
      rw [ha, pow_succ', finiteExceptionalAut_pow_two_mul]
    exact ⟨hφf, hφf, fun g => by rw [hφf]; exact Iff.rfl⟩

end Generic

section F4

variable {K : Type} [Field K]

theorem orbitCertRoot_F4_simple :
    ∀ i : Fin Tag.F4.rank, orbitCertRoot .F4 (![33, 27, 25, 24] i) = Pi.single i 1 := by
  decide

theorem list_prod_pinnedX_one_ne_one
    (τ : Tag) {m : ℕ} (hm : 0 < m)
    (α : Fin m → Fin τ.rank → ℤ) (hα : Function.Injective α)
    (hpos : ∀ i, IsRoot τ (α i) ∧ 0 < height (α i)) :
    (List.ofFn fun i => pinnedX τ K (α i) 1).prod ≠ 1 := by
  intro h
  have h0 : (List.ofFn fun i => pinnedX τ K (α i) ((0 : Fin m → K) i)).prod = 1 := by
    simp [pinnedX_zero]
  have h1 := (positive_root_product_injectivity τ K α hα hpos).2 (h.trans h0.symm)
  exact one_ne_zero (congrFun h1 ⟨0, hm⟩)

variable [CharP K 2]

omit [CharP K 2] in
theorem xUnit_F4_eq_pinnedX
    {l : Fin Tag.F4.rank} {k : ℕ} (hk : orbitCertRoot .F4 k = Pi.single l 1)
    (c : K) : xUnit .F4 K l c = pinnedX .F4 K (orbitCertRoot .F4 k) c := by
  rw [hk, pinnedX_single]


end F4

theorem even_F4_exact_automorphism_normal_form
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K]
    [Finite K] [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) :
    orderOf (ReeTag.F4.finiteExceptionalAut K) = 2 * f ∧
    (∀ α : MulAut (adjointGroup ReeTag.F4.tag K),
      ∃! gk : adjointGroup ReeTag.F4.tag K × Fin (2 * f),
        α = MulAut.conj gk.1 * ReeTag.F4.finiteExceptionalAut K ^ (gk.2 : ℕ)) ∧
    (∃ Θ : MulAut (adjointGroup ReeTag.F4.tag K) →* Multiplicative (ZMod (2 * f)),
      (∀ (α : MulAut (adjointGroup ReeTag.F4.tag K)) (g : adjointGroup ReeTag.F4.tag K) (k : ℕ),
        α = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ k →
          Θ α = Multiplicative.ofAdd (k : ZMod (2 * f))) ∧
      Function.Surjective Θ ∧
      Θ.ker = (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
        MulAut (adjointGroup ReeTag.F4.tag K)).range) ∧
    (∀ (α : MulAut (adjointGroup ReeTag.F4.tag K)) (g : adjointGroup ReeTag.F4.tag K) (k : ℕ),
      k < 2 * f → α = MulAut.conj g * ReeTag.F4.finiteExceptionalAut K ^ k → α ^ 2 = 1 →
        k = 0 ∨ k = f) ∧
    ((ReeTag.F4.finiteExceptionalAut K ^ f) ^ 2 = 1 ∧ ReeTag.F4.finiteExceptionalAut K ^ f ≠ 1) ∧
    (∀ e : ℕ, f = 2 * e →
      ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteFrobeniusAut K ^ e) ∧
    ∀ m : ℕ, f = 2 * m + 1 →
      ReeTag.F4.finiteExceptionalAut K ^ f =
          ReeTag.F4.finiteExceptionalAut K * ReeTag.F4.finiteFrobeniusAut K ^ m ∧
        ReeTag.F4.finiteExceptionalAut K ^ f = ReeTag.F4.finiteReeAut K m ∧
        ∀ g : adjointGroup ReeTag.F4.tag K,
          g ∈ ReeTag.F4.finiteReeFixedGroup K m ↔ (ReeTag.F4.finiteExceptionalAut K ^ f) g = g := by
  have hperm : ∀ β ∈ unipotentPairAut ReeTag.F4.tag K, ∀ π : Equiv.Perm (Fin ReeTag.F4.tag.rank),
      (∀ i, (simplePosSubgroup ReeTag.F4.tag K i).map β.toMonoidHom =
          simplePosSubgroup ReeTag.F4.tag K (π i) ∧
        (simpleNegSubgroup ReeTag.F4.tag K i).map β.toMonoidHom =
          simpleNegSubgroup ReeTag.F4.tag K (π i)) →
      π = 1 ∨ π = ReeTag.F4.perm := by
    intro β _ π hπ
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact f4_even_simple_pair_perm fun i => (hπ i).1
  obtain ⟨⟨B, hB, -⟩, hrest⟩ := G2_F4_root_character_diagonals_inner ReeTag.F4.tag (Or.inr rfl) K
  exact ree_exact_automorphism_normal_form ReeTag.F4 hf hK hperm (fun a => (hrest B hB a).2.2.1)
    (i₀ := ⟨0, by decide⟩) (by decide)

namespace F4NativeNormalForm

open CFSG.Blueprint
  CFSG.StandardType.F4ExplicitPos.B3Pinned
  CFSG.StandardType.F4ExplicitPos.B3Unconditional
  CFSG.StandardType.F4ExplicitPos.LangPosition
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.EvenBN.G2
  CFSG.ComponentClassification.OuterAutomorphisms

section

variable {K : Type} [Field K] [Finite K] [CharP K 2]


private theorem f4_rootChar_single (b : Fin ReeTag.F4.tag.rank → Kˣ)
    (i : Fin ReeTag.F4.tag.rank) : rootChar b (Pi.single i 1) = b i := by
  simpa only [one_smul, pow_one] using rootChar_nsmul_single b i 1

private theorem f4_entrywise_injective (σ : K →+* K) :
    Function.Injective (entrywise (τ := ReeTag.F4.tag) σ) := by
  intro A B h
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
  have hb := LinearMap.congr_fun h (Finsupp.single b 1)
  rw [entrywise_single, entrywise_single] at hb
  exact Finsupp.mapRange_injective σ σ.map_zero σ.injective hb

@[expose] noncomputable def f4FrobTwist (e : ℕ) :
    adjointGroup Tag.F4 K →* adjointGroup Tag.F4 K :=
  ((entrywiseFrobGL Tag.F4 K 2 e).comp (adjointGroup Tag.F4 K).subtype).codRestrict
    (adjointGroup Tag.F4 K) fun g => entrywiseFrobGL_mem_adjointGroup_no117 2 e g.2

private theorem f4_rootDiagUnit_mem (b : Fin ReeTag.F4.tag.rank → Kˣ) :
    rootDiagUnit ReeTag.F4.tag b ∈ adjointGroup ReeTag.F4.tag K := by
  obtain ⟨B, hB, -⟩ := (G2_F4_root_character_diagonals_inner ReeTag.F4.tag (Or.inr rfl) K).1
  exact ((G2_F4_root_character_diagonals_inner ReeTag.F4.tag (Or.inr rfl) K).2 B hB b).2.2.1

private theorem f4DiagAut_adjX (b : Fin ReeTag.F4.tag.rank → Kˣ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    rootDiagAut ReeTag.F4.tag K b (adjX ReeTag.F4.tag K i c) =
      adjX ReeTag.F4.tag K i (((rootChar b (Pi.single i 1) : Kˣ) : K) * c) := by
  apply Subtype.ext
  change rootDiagUnit ReeTag.F4.tag b * (adjX ReeTag.F4.tag K i c : ModGL ReeTag.F4.tag K) *
      (rootDiagUnit ReeTag.F4.tag b)⁻¹ =
    (adjX ReeTag.F4.tag K i (((rootChar b (Pi.single i 1) : Kˣ) : K) * c) : ModGL ReeTag.F4.tag K)
  rw [show (adjX ReeTag.F4.tag K i c : ModGL ReeTag.F4.tag K) = xUnit ReeTag.F4.tag K i c from rfl,
    show (adjX ReeTag.F4.tag K i (((rootChar b (Pi.single i 1) : Kˣ) : K) * c) : ModGL ReeTag.F4.tag K) =
      xUnit ReeTag.F4.tag K i (((rootChar b (Pi.single i 1) : Kˣ) : K) * c) from rfl]
  rw [← pinnedX_single, ← pinnedX_single, rootDiagUnit_conj_pinnedX b (isRoot_single ReeTag.F4.tag i) c,
    f4_rootChar_single]

private theorem f4DiagAut_adjY (b : Fin ReeTag.F4.tag.rank → Kˣ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    rootDiagAut ReeTag.F4.tag K b (adjY ReeTag.F4.tag K i c) =
      adjY ReeTag.F4.tag K i (((rootChar b (-Pi.single i 1) : Kˣ) : K) * c) := by
  apply Subtype.ext
  change rootDiagUnit ReeTag.F4.tag b * (adjY ReeTag.F4.tag K i c : ModGL ReeTag.F4.tag K) *
      (rootDiagUnit ReeTag.F4.tag b)⁻¹ =
    (adjY ReeTag.F4.tag K i (((rootChar b (-Pi.single i 1) : Kˣ) : K) * c) : ModGL ReeTag.F4.tag K)
  rw [show (adjY ReeTag.F4.tag K i c : ModGL ReeTag.F4.tag K) = yUnit ReeTag.F4.tag K i c from rfl,
    show (adjY ReeTag.F4.tag K i (((rootChar b (-Pi.single i 1) : Kˣ) : K) * c) : ModGL ReeTag.F4.tag K) =
      yUnit ReeTag.F4.tag K i (((rootChar b (-Pi.single i 1) : Kˣ) : K) * c) from rfl]
  rw [← pinnedX_neg_single, ← pinnedX_neg_single,
    rootDiagUnit_conj_pinnedX b (isRoot_neg_single ReeTag.F4.tag i) c]



private noncomputable def f4FrobAut (e : ℕ) : MulAut (adjointGroup ReeTag.F4.tag K) :=
  MulEquiv.ofBijective (f4FrobTwist e) (by
    haveI : Finite (adjointGroup ReeTag.F4.tag K) := generated_group_finite ReeTag.F4.tag K
    haveI : Fintype (adjointGroup ReeTag.F4.tag K) := Fintype.ofFinite _
    have hinj : Function.Injective (f4FrobTwist (K := K) e) := by
      intro x y h
      apply Subtype.ext
      apply Units.ext
      apply f4_entrywise_injective (σ := iterateFrobenius K 2 e)
      exact congrArg Units.val (congrArg Subtype.val h)
    exact hinj.bijective_of_finite)

private theorem f4FrobAut_apply (e : ℕ) (g : adjointGroup ReeTag.F4.tag K) :
    (f4FrobAut e g : ModGL ReeTag.F4.tag K) = entrywiseFrobGL ReeTag.F4.tag K 2 e g := by
  rfl

private theorem f4FrobAut_xUnit (e : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4FrobAut e ⟨xUnit ReeTag.F4.tag K i c, xUnit_mem_adjointGroup i c⟩ =
      ⟨xUnit ReeTag.F4.tag K i (c ^ 2 ^ e), xUnit_mem_adjointGroup i _⟩ := by
  apply Subtype.ext
  rw [f4FrobAut_apply, entrywiseFrobGL_xUnit_no117]

private theorem f4FrobAut_yUnit (e : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4FrobAut e ⟨yUnit ReeTag.F4.tag K i c, yUnit_mem_adjointGroup i c⟩ =
      ⟨yUnit ReeTag.F4.tag K i (c ^ 2 ^ e), yUnit_mem_adjointGroup i _⟩ := by
  apply Subtype.ext
  rw [f4FrobAut_apply, entrywiseFrobGL_yUnit_no117]


private theorem f4_exceptionalAut_xElement (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4_exceptionalAut K (xElement (τ := ReeTag.F4.tag) (K := K) i c) =
      xElement (τ := ReeTag.F4.tag) (K := K) (ReeTag.F4.perm i)
        (c ^ ReeTag.F4.exponent i) := by
  rw [f4_exceptionalAut_apply]
  exact f4_exceptionalEndo_xElement i c

private theorem f4_exceptionalAut_yElement (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4_exceptionalAut K (yElement (τ := ReeTag.F4.tag) (K := K) i c) =
      yElement (τ := ReeTag.F4.tag) (K := K) (ReeTag.F4.perm i)
        (c ^ ReeTag.F4.exponent i) := by
  rw [f4_exceptionalAut_apply]
  exact f4_exceptionalEndo_yElement i c

private theorem f4_exceptionalAut_adjX (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4_exceptionalAut K (adjX ReeTag.F4.tag K i c) =
      adjX ReeTag.F4.tag K (ReeTag.F4.perm i) (c ^ ReeTag.F4.exponent i) := by
  change f4_exceptionalAut K (xElement (τ := ReeTag.F4.tag) (K := K) i c) =
    xElement (τ := ReeTag.F4.tag) (K := K) (ReeTag.F4.perm i)
      (c ^ ReeTag.F4.exponent i)
  exact f4_exceptionalAut_xElement i c

private theorem f4_exceptionalAut_adjY (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4_exceptionalAut K (adjY ReeTag.F4.tag K i c) =
      adjY ReeTag.F4.tag K (ReeTag.F4.perm i) (c ^ ReeTag.F4.exponent i) := by
  change f4_exceptionalAut K (yElement (τ := ReeTag.F4.tag) (K := K) i c) =
    yElement (τ := ReeTag.F4.tag) (K := K) (ReeTag.F4.perm i)
      (c ^ ReeTag.F4.exponent i)
  exact f4_exceptionalAut_yElement i c

private theorem f4_perm_perm (i : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.perm (ReeTag.F4.perm i) = i := by
  have hsq : (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) *
      (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) = 1 := by
    ext j
    fin_cases j <;> rfl
  have hperm : ReeTag.F4.perm =
      (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) := rfl
  rw [hperm]
  have hsq' : ∀ j, (Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4))
      ((Equiv.swap 0 3 * Equiv.swap 1 2 : Equiv.Perm (Fin 4)) j) = j := by
    intro j
    exact congrArg (fun e : Equiv.Perm (Fin 4) => e j) hsq
  exact hsq' i

private theorem f4FrobAut_adjX (e : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4FrobAut e (adjX ReeTag.F4.tag K i c) =
      adjX ReeTag.F4.tag K i (c ^ 2 ^ e) := by
  simpa [adjX, xElement] using f4FrobAut_xUnit (K := K) e i c

private theorem f4FrobAut_adjY (e : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    f4FrobAut e (adjY ReeTag.F4.tag K i c) =
      adjY ReeTag.F4.tag K i (c ^ 2 ^ e) := by
  simpa [adjY, yElement] using f4FrobAut_yUnit (K := K) e i c

private theorem f4FrobAutOne_pow_adjX (j : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    ((f4FrobAut 1) ^ j) (adjX ReeTag.F4.tag K i c) =
      adjX ReeTag.F4.tag K i (c ^ 2 ^ j) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, MulAut.mul_apply, f4FrobAut_adjX]
      rw [show c ^ 2 ^ 1 = c ^ 2 by norm_num]
      rw [ih (c ^ 2)]
      congr 1
      rw [← pow_mul]
      congr 1
      rw [Nat.pow_succ]
      ring

private theorem f4FrobAutOne_pow_adjY (j : ℕ) (i : Fin ReeTag.F4.tag.rank) (c : K) :
    ((f4FrobAut 1) ^ j) (adjY ReeTag.F4.tag K i c) =
      adjY ReeTag.F4.tag K i (c ^ 2 ^ j) := by
  induction j generalizing c with
  | zero => simp
  | succ j ih =>
      rw [pow_succ, MulAut.mul_apply, f4FrobAut_adjY]
      rw [show c ^ 2 ^ 1 = c ^ 2 by norm_num]
      rw [ih (c ^ 2)]
      congr 1
      rw [← pow_mul]
      congr 1
      rw [Nat.pow_succ]
      ring

private theorem f4_exponent_mul_perm (i : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.exponent i * ReeTag.F4.exponent (ReeTag.F4.perm i) = 2 := by
  fin_cases i <;> decide

private theorem f4_exceptionalAut_mul_self :
    f4_exceptionalAut K * f4_exceptionalAut K = f4FrobAut 1 := by
  apply mulAut_ext_adjX_adjY
  · intro i c
    change (f4_exceptionalAut K * f4_exceptionalAut K) (adjX ReeTag.F4.tag K i c) =
      f4FrobAut 1 (adjX ReeTag.F4.tag K i c)
    rw [MulAut.mul_apply, f4_exceptionalAut_adjX, f4_exceptionalAut_adjX,
      f4_perm_perm, f4FrobAut_adjX]
    congr 1
    rw [← pow_mul, f4_exponent_mul_perm]
    norm_num
  · intro i c
    change (f4_exceptionalAut K * f4_exceptionalAut K) (adjY ReeTag.F4.tag K i c) =
      f4FrobAut 1 (adjY ReeTag.F4.tag K i c)
    rw [MulAut.mul_apply, f4_exceptionalAut_adjY, f4_exceptionalAut_adjY,
      f4_perm_perm, f4FrobAut_adjY]
    congr 1
    rw [← pow_mul, f4_exponent_mul_perm]
    norm_num

private theorem f4_exceptionalAut_pow_two_mul (j : ℕ) :
    f4_exceptionalAut K ^ (2 * j) = (f4FrobAut 1) ^ j := by
  rw [pow_mul, sq, f4_exceptionalAut_mul_self]



private theorem f4_exponent_pow_surjective (i : Fin ReeTag.F4.tag.rank) :
    Function.Surjective (fun c : K => c ^ ReeTag.F4.exponent i) := by
  have hcases : ReeTag.F4.exponent i = 1 ∨ ReeTag.F4.exponent i = 2 := by
    fin_cases i <;> decide
  rintro d
  rcases hcases with h1 | h2
  · exact ⟨d, by simp [h1]⟩
  · refine ⟨(frobeniusEquiv K 2).symm d, ?_⟩
    have h := (frobeniusEquiv K 2).apply_symm_apply d
    rw [h2]
    simpa [frobeniusEquiv_pow_apply] using h

private theorem f4_rootChar_neg_single (b : Fin ReeTag.F4.tag.rank → Kˣ) (i : Fin ReeTag.F4.tag.rank) :
    rootChar b (-Pi.single i 1) = (b i)⁻¹ := by
  rw [show (-Pi.single i 1 : Fin ReeTag.F4.tag.rank → ℤ) = 0 - Pi.single i 1 by
      ext j
      simp,
    rootChar_sub, rootChar_zero, one_mul, f4_rootChar_single]

private theorem f4_rootPairAut_eq_diag_mul_frob (ζ : rootPairAut ReeTag.F4.tag K) :
    ∃ a : Fin ReeTag.F4.tag.rank → Kˣ, ∃ m : ℕ,
      (ζ : MulAut (adjointGroup ReeTag.F4.tag K)) = rootDiagAut ReeTag.F4.tag K a * (f4FrobAut 1) ^ m := by
  obtain ⟨p, hp⟩ := exists_common_params ζ.2
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  have hnpos : 1 ≤ (n : ℕ) := n.pos
  have hK' : Nat.card K = 2 ^ (n : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hK
  obtain ⟨m, -, hm⟩ := exists_eq_frobeniusEquiv_pow hK' hnpos p.2
  let A : MulAut (adjointGroup ReeTag.F4.tag K) :=
    (rootDiagAut ReeTag.F4.tag K p.1 : MulAut (adjointGroup ReeTag.F4.tag K)) *
      ((f4FrobAut 1 : MulAut (adjointGroup ReeTag.F4.tag K)) ^ m)
  refine ⟨p.1, m, ?_⟩
  change (ζ : MulAut (adjointGroup ReeTag.F4.tag K)) = A
  apply mulAut_ext_adjX_adjY
  · intro i c
    change (ζ : MulAut (adjointGroup ReeTag.F4.tag K)) (adjX ReeTag.F4.tag K i c) =
      A (adjX ReeTag.F4.tag K i c)
    calc
      (ζ : MulAut (adjointGroup ReeTag.F4.tag K)) (adjX ReeTag.F4.tag K i c) =
          adjX ReeTag.F4.tag K i (p.1 i * p.2 c) := by
        simpa [adjX] using (hp i).1 c
      _ = adjX ReeTag.F4.tag K i (p.1 i * (frobeniusEquiv K 2 ^ m) c) := by rw [hm]
      _ = adjX ReeTag.F4.tag K i (p.1 i * c ^ 2 ^ m) := by rw [frobeniusEquiv_pow_apply]
      _ = A (adjX ReeTag.F4.tag K i c) := by
        dsimp [A]
        rw [f4FrobAutOne_pow_adjX, f4DiagAut_adjX, f4_rootChar_single]
  · intro i c
    change (ζ : MulAut (adjointGroup ReeTag.F4.tag K)) (adjY ReeTag.F4.tag K i c) =
      A (adjY ReeTag.F4.tag K i c)
    calc
      (ζ : MulAut (adjointGroup ReeTag.F4.tag K)) (adjY ReeTag.F4.tag K i c) =
          adjY ReeTag.F4.tag K i ((((p.1 i)⁻¹ : Kˣ) : K) * p.2 c) := by
        simpa [adjY] using (hp i).2.1 c
      _ = adjY ReeTag.F4.tag K i ((((p.1 i)⁻¹ : Kˣ) : K) * (frobeniusEquiv K 2 ^ m) c) := by
        rw [hm]
      _ = adjY ReeTag.F4.tag K i ((((p.1 i)⁻¹ : Kˣ) : K) * c ^ 2 ^ m) := by
        rw [frobeniusEquiv_pow_apply]
      _ = A (adjY ReeTag.F4.tag K i c) := by
        dsimp [A]
        rw [f4FrobAutOne_pow_adjY, f4DiagAut_adjY, f4_rootChar_neg_single]


private theorem f4_map_simplePosSubgroup_exceptional (i : Fin ReeTag.F4.tag.rank) :
    (simplePosSubgroup ReeTag.F4.tag K i).map (f4_exceptionalAut K).toMonoidHom =
      simplePosSubgroup ReeTag.F4.tag K (ReeTag.F4.perm i) := by
  have hφ : ∀ c, f4_exceptionalAut K (adjX ReeTag.F4.tag K i c) =
      adjX ReeTag.F4.tag K (ReeTag.F4.perm i) (c ^ ReeTag.F4.exponent i) := by
    intro c
    simpa using f4_exceptionalAut_adjX (K := K) i c
  ext x
  simp only [Subgroup.mem_map, mem_simplePosSubgroup]
  constructor
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    have hy : y = adjX ReeTag.F4.tag K i c := Subtype.ext hc
    refine ⟨c ^ ReeTag.F4.exponent i, ?_⟩
    rw [hy]
    simpa [adjX] using congrArg Subtype.val (hφ c)
  · rintro ⟨d, hd⟩
    have hx : x = adjX ReeTag.F4.tag K (ReeTag.F4.perm i) d := Subtype.ext hd
    obtain ⟨c, hc⟩ :=
      f4_exponent_pow_surjective (K := K) i d
    refine ⟨adjX ReeTag.F4.tag K i c, ⟨c, rfl⟩, ?_⟩
    rw [hx, ← hc]
    exact hφ c

private theorem f4_map_simpleNegSubgroup_exceptional (i : Fin ReeTag.F4.tag.rank) :
    (simpleNegSubgroup ReeTag.F4.tag K i).map (f4_exceptionalAut K).toMonoidHom =
      simpleNegSubgroup ReeTag.F4.tag K (ReeTag.F4.perm i) := by
  have hφ : ∀ c, f4_exceptionalAut K (adjY ReeTag.F4.tag K i c) =
      adjY ReeTag.F4.tag K (ReeTag.F4.perm i) (c ^ ReeTag.F4.exponent i) := by
    intro c
    simpa using f4_exceptionalAut_adjY (K := K) i c
  ext x
  simp only [Subgroup.mem_map, mem_simpleNegSubgroup]
  constructor
  · rintro ⟨y, ⟨c, hc⟩, rfl⟩
    have hy : y = adjY ReeTag.F4.tag K i c := Subtype.ext hc
    refine ⟨c ^ ReeTag.F4.exponent i, ?_⟩
    rw [hy]
    simpa [adjY] using congrArg Subtype.val (hφ c)
  · rintro ⟨d, hd⟩
    have hx : x = adjY ReeTag.F4.tag K (ReeTag.F4.perm i) d := Subtype.ext hd
    obtain ⟨c, hc⟩ :=
      f4_exponent_pow_surjective (K := K) i d
    refine ⟨adjY ReeTag.F4.tag K i c, ⟨c, rfl⟩, ?_⟩
    rw [hx, ← hc]
    exact hφ c

private theorem f4_map_inv_of_map_eq {H K' : Subgroup (adjointGroup ReeTag.F4.tag K)}
    (h : H.map (f4_exceptionalAut K).toMonoidHom = K') :
    K'.map (f4_exceptionalAut K)⁻¹.toMonoidHom = H := by
  rw [← h]
  ext x
  constructor
  · rintro ⟨y, ⟨a, ha, rfl⟩, hxy⟩
    have hx : x = a := by
      rw [← hxy]
      exact (f4_exceptionalAut K).symm_apply_apply a
    simpa [hx] using ha
  · intro hx
    refine ⟨f4_exceptionalAut K x, ?_, ?_⟩
    · exact ⟨x, hx, rfl⟩
    · exact (f4_exceptionalAut K).symm_apply_apply x

theorem f4_exists_conj_mul_pow (α : MulAut (adjointGroup ReeTag.F4.tag K)) :
    ∃ (g : adjointGroup ReeTag.F4.tag K) (k : ℕ),
      α = MulAut.conj g * f4_exceptionalAut K ^ k := by
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem ReeTag.F4.tag).length
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, β, hβ, hα⟩ :=
    f4_exists_conj_mul_unipotentPair (K := K) 2 w₀ hw₀ α
  let c' : adjointGroup ReeTag.F4.tag K := c
  let β' : MulAut (adjointGroup ReeTag.F4.tag K) := β
  have hα' : α = MulAut.conj c' * β' := by
    exact hα
  obtain ⟨π, hπ⟩ := f4_exists_perm_map_simple hβ
  rcases f4_even_simple_pair_perm (hπ := fun i => (hπ i).1) with hπ1 | hπρ
  · have hβroot : β' ∈ rootPairAut ReeTag.F4.tag K := by
      rw [mem_rootPairAut]
      intro i
      constructor
      · change (simplePosSubgroup Tag.F4 K i).map β.toMonoidHom =
          simplePosSubgroup Tag.F4 K i
        have h := (hπ i).1
        rw [hπ1] at h
        have hone : (1 : Equiv.Perm (Fin Tag.F4.rank)) i = i := rfl
        rw [hone] at h
        exact h
      · change (simpleNegSubgroup Tag.F4 K i).map β.toMonoidHom =
          simpleNegSubgroup Tag.F4 K i
        have h := (hπ i).2
        rw [hπ1] at h
        have hone : (1 : Equiv.Perm (Fin Tag.F4.rank)) i = i := rfl
        rw [hone] at h
        exact h
    obtain ⟨a, m, hβeq⟩ := f4_rootPairAut_eq_diag_mul_frob ⟨β', hβroot⟩
    have hβeq' : β' = rootDiagAut ReeTag.F4.tag K a * (f4FrobAut 1) ^ m := by
      simpa using hβeq
    let D : adjointGroup ReeTag.F4.tag K :=
      ⟨rootDiagUnit ReeTag.F4.tag a, f4_rootDiagUnit_mem a⟩
    refine ⟨c' * D, 2 * m, ?_⟩
    calc
      α = MulAut.conj c' * β' := hα'
      _ = MulAut.conj c' * (MulAut.conj D * (f4FrobAut 1) ^ m) := by
        rw [hβeq']
        congr 1
      _ = (MulAut.conj c' * MulAut.conj D) * (f4FrobAut 1) ^ m := by group
      _ = MulAut.conj (c' * D) * (f4FrobAut 1) ^ m := by rw [← map_mul]
      _ = MulAut.conj (c' * D) * f4_exceptionalAut K ^ (2 * m) := by
        rw [f4_exceptionalAut_pow_two_mul]
  · have hφinv_pos : ∀ i,
        (simplePosSubgroup ReeTag.F4.tag K i).map (f4_exceptionalAut K)⁻¹.toMonoidHom =
          simplePosSubgroup ReeTag.F4.tag K (ReeTag.F4.perm i) := by
      intro i
      have h := f4_map_simplePosSubgroup_exceptional (K := K) (ReeTag.F4.perm i)
      rw [f4_perm_perm] at h
      exact f4_map_inv_of_map_eq h
    have hφinv_neg : ∀ i,
        (simpleNegSubgroup ReeTag.F4.tag K i).map (f4_exceptionalAut K)⁻¹.toMonoidHom =
          simpleNegSubgroup ReeTag.F4.tag K (ReeTag.F4.perm i) := by
      intro i
      have h := f4_map_simpleNegSubgroup_exceptional (K := K) (ReeTag.F4.perm i)
      rw [f4_perm_perm] at h
      exact f4_map_inv_of_map_eq h
    have hπpos' : ∀ i, (simplePosSubgroup ReeTag.F4.tag K i).map β'.toMonoidHom =
        simplePosSubgroup ReeTag.F4.tag K (π i) := by
      intro i
      change (simplePosSubgroup Tag.F4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.F4 K (π i)
      exact (hπ i).1
    have hπneg' : ∀ i, (simpleNegSubgroup ReeTag.F4.tag K i).map β'.toMonoidHom =
        simpleNegSubgroup ReeTag.F4.tag K (π i) := by
      intro i
      change (simpleNegSubgroup Tag.F4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.F4 K (π i)
      exact (hπ i).2
    have hζ : β' * (f4_exceptionalAut K)⁻¹ ∈ rootPairAut ReeTag.F4.tag K := by
      rw [mem_rootPairAut]
      intro i
      constructor
      · change (simplePosSubgroup ReeTag.F4.tag K i).map
            (β' * (f4_exceptionalAut K)⁻¹).toMonoidHom =
          simplePosSubgroup ReeTag.F4.tag K i
        rw [show (β' * (f4_exceptionalAut K)⁻¹).toMonoidHom =
              β'.toMonoidHom.comp ((f4_exceptionalAut K)⁻¹).toMonoidHom from rfl,
            ← Subgroup.map_map, hφinv_pos i, hπpos' (ReeTag.F4.perm i), hπρ]
        exact congrArg (simplePosSubgroup ReeTag.F4.tag K) (f4_perm_perm i)
      · change (simpleNegSubgroup ReeTag.F4.tag K i).map
            (β' * (f4_exceptionalAut K)⁻¹).toMonoidHom =
          simpleNegSubgroup ReeTag.F4.tag K i
        rw [show (β' * (f4_exceptionalAut K)⁻¹).toMonoidHom =
              β'.toMonoidHom.comp ((f4_exceptionalAut K)⁻¹).toMonoidHom from rfl,
            ← Subgroup.map_map, hφinv_neg i, hπneg' (ReeTag.F4.perm i), hπρ]
        exact congrArg (simpleNegSubgroup ReeTag.F4.tag K) (f4_perm_perm i)
    obtain ⟨a, m, hζeq⟩ := f4_rootPairAut_eq_diag_mul_frob ⟨β' * (f4_exceptionalAut K)⁻¹, hζ⟩
    have hζeq' : β' * (f4_exceptionalAut K)⁻¹ = rootDiagAut ReeTag.F4.tag K a * (f4FrobAut 1) ^ m := by
      simpa using hζeq
    let D : adjointGroup ReeTag.F4.tag K :=
      ⟨rootDiagUnit ReeTag.F4.tag a, f4_rootDiagUnit_mem a⟩
    refine ⟨c' * D, 2 * m + 1, ?_⟩
    have hβeq : β' = (MulAut.conj D * (f4FrobAut 1) ^ m) * f4_exceptionalAut K := by
      have h := congrArg (fun x : MulAut (adjointGroup ReeTag.F4.tag K) =>
        x * f4_exceptionalAut K) hζeq'
      have hdiag : rootDiagAut ReeTag.F4.tag K a = MulAut.conj D :=
        MulEquiv.ext fun z => Subtype.ext rfl
      rw [hdiag] at h
      simpa only [inv_mul_cancel_right] using h
    calc
      α = MulAut.conj c' * β' := hα'
      _ = MulAut.conj c' * ((MulAut.conj D * (f4FrobAut 1) ^ m) * f4_exceptionalAut K) := by
        rw [hβeq]
      _ = (MulAut.conj c' * MulAut.conj D) * ((f4FrobAut 1) ^ m * f4_exceptionalAut K) := by
        group
      _ = MulAut.conj (c' * D) * (f4_exceptionalAut K ^ (2 * m) * f4_exceptionalAut K) := by
        rw [← map_mul, f4_exceptionalAut_pow_two_mul]
      _ = MulAut.conj (c' * D) * f4_exceptionalAut K ^ (2 * m + 1) := by
        rw [pow_succ]

theorem f4_exists_conj_mul_pow_tag (α : MulAut (adjointGroup Tag.F4 K)) :
    ∃ (g : adjointGroup Tag.F4 K) (k : ℕ),
      α = MulAut.conj g *
        (show MulAut (adjointGroup Tag.F4 K) from
          CFSG.StandardType.F4ExplicitPos.B3Unconditional.f4_exceptionalAut K) ^ k := by
  change ∃ (g : adjointGroup ReeTag.F4.tag K) (k : ℕ),
      α = MulAut.conj g * f4_exceptionalAut K ^ k
  exact f4_exists_conj_mul_pow (K := K) α

private theorem f4_outer_isCyclic_aux :
    IsCyclic (Outer (adjointGroup ReeTag.F4.tag K)) := by
  rw [isCyclic_iff_exists_zpowers_eq_top]
  let φ : MulAut (adjointGroup ReeTag.F4.tag K) := f4_exceptionalAut K
  let q : MulAut (adjointGroup ReeTag.F4.tag K) →*
      Outer (adjointGroup ReeTag.F4.tag K) :=
    QuotientGroup.mk' (inner (adjointGroup ReeTag.F4.tag K))
  refine ⟨q φ, ?_⟩
  rw [eq_top_iff]
  intro x _
  obtain ⟨α, rfl⟩ :=
    QuotientGroup.mk'_surjective (inner (adjointGroup ReeTag.F4.tag K)) x
  obtain ⟨g, k, hα⟩ := f4_exists_conj_mul_pow (K := K) α
  rw [hα]
  have hconj : q (MulAut.conj g) = 1 := by
    change QuotientGroup.mk' (inner (adjointGroup ReeTag.F4.tag K)) (MulAut.conj g) = 1
    rw [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    exact ⟨g, rfl⟩
  rw [map_mul, hconj, one_mul, map_pow]
  exact Subgroup.npow_mem_zpowers (q φ) k

theorem f4_outer_isCyclic :
    IsCyclic (Outer (adjointGroup Tag.F4 K)) := by
  change IsCyclic (Outer (adjointGroup ReeTag.F4.tag K))
  exact f4_outer_isCyclic_aux (K := K)

private theorem f4_outer_isSolvable_aux :
    Group.IsSolvable (Outer (adjointGroup ReeTag.F4.tag K)) := by
  letI : IsCyclic (Outer (adjointGroup ReeTag.F4.tag K)) := f4_outer_isCyclic_aux
  letI : CommGroup (Outer (adjointGroup ReeTag.F4.tag K)) := IsCyclic.commGroup
  exact Group.isSolvable_of_comm (fun a b => mul_comm a b)

theorem f4_outer_isSolvable :
    Group.IsSolvable (Outer (adjointGroup Tag.F4 K)) := by
  change Group.IsSolvable (Outer (adjointGroup ReeTag.F4.tag K))
  exact f4_outer_isSolvable_aux (K := K)

theorem f4_outer_isSolvable_of_perfect_centralCover
    {Y : Type} [Group Y] [Group.IsPerfect Y]
    (psi : Y →* ModGL Tag.F4 K)
    (hpsi_range : psi.range = adjointGroup Tag.F4 K)
    (hpsi_ker : psi.ker ≤ Subgroup.center Y) :
    Group.IsSolvable (Outer Y) := by
  let f : Y →* adjointGroup Tag.F4 K := psi.codRestrict _ (fun y => by
    rw [← hpsi_range]
    exact ⟨y, rfl⟩)
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨y, hy⟩ := (show a.val ∈ psi.range by rw [hpsi_range]; exact a.property)
    exact ⟨y, Subtype.ext hy⟩
  have hker : f.ker ≤ Subgroup.center Y := by
    intro y hy
    apply hpsi_ker
    change psi y = 1
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
  obtain ⟨e⟩ := CFSG.AGLEmbedding.LieOut.quotCenter_mulEquiv f hf hker
    (show ⁅(⊤ : Subgroup Y), ⊤⁆ = ⊤ from Group.IsPerfect.commutator_eq_top)
  let e0 : adjointGroup Tag.F4 K ⧸ Subgroup.center (adjointGroup Tag.F4 K) ≃*
      adjointGroup Tag.F4 K :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.StandardType.F4ExplicitPos.CenterProofFast.center_adjointGroup_F4_charTwo_eq_bot
        (K := K))).trans QuotientGroup.quotientBot
  letI : Group.IsSolvable (Outer (adjointGroup Tag.F4 K)) := f4_outer_isSolvable
  letI : Group.IsSolvable (Outer (Y ⧸ Subgroup.center Y)) :=
    solvable_of_equiv (e.trans e0).symm
  exact solvable_of_centerQuotient Y

private theorem f4FrobAut_one_pow (m : ℕ) :
    f4FrobAut (K := K) m = (f4FrobAut (K := K) 1) ^ m := by
  apply mulAut_ext_adjX_adjY
  · intro i c
    rw [f4FrobAut_adjX, f4FrobAutOne_pow_adjX]
  · intro i c
    rw [f4FrobAut_adjY, f4FrobAutOne_pow_adjY]

omit [Finite K] [CharP K 2] in
private theorem f4_raw_borel_ree {g : adjointGroup ReeTag.F4.tag K} (σ : K ≃+* K)
    (hσ : ∀ (i : Fin ReeTag.F4.tag.rank) (c : K),
      MulAut.conj g (adjX ReeTag.F4.tag K i c) = adjX ReeTag.F4.tag K i (σ c)) :
    σ = 1 := by
  have hσ' : ∀ (i : Fin Tag.F4.rank) (c : K),
      MulAut.conj (g : adjointGroup Tag.F4 K) (adjX Tag.F4 K i c) =
        adjX Tag.F4 K i (σ c) := by
    intro i c
    exact hσ i c
  exact (f4_mem_borelGroup_of_raw (K := K) (g := (g : adjointGroup Tag.F4 K)) σ hσ').1

private theorem f4_field_form_with_inner_factor_ree
    (α : MulAut (adjointGroup ReeTag.F4.tag K))
    (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ h : adjointGroup ReeTag.F4.tag K, α ≠ MulAut.conj h) :
    ∃ (σ : K ≃+* K) (h : adjointGroup ReeTag.F4.tag K),
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧
      ∀ z : adjointGroup ReeTag.F4.tag K,
        (α z : ModGL ReeTag.F4.tag K) =
          (h : ModGL ReeTag.F4.tag K) *
            Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) *
              (h : ModGL ReeTag.F4.tag K)⁻¹ := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hnprime, hKcard⟩ := FiniteField.card K 2
  have hnpos : 1 ≤ (n : ℕ) := n.pos
  let φ : MulAut (adjointGroup ReeTag.F4.tag K) := f4_exceptionalAut K
  let F : MulAut (adjointGroup ReeTag.F4.tag K) := f4FrobAut (K := K) 1
  have hφ2 : φ * φ = F := by
    simpa [φ, F] using f4_exceptionalAut_mul_self (K := K)
  have hFn : F ^ (n : ℕ) = 1 := by
    apply mulAut_ext_adjX_adjY
    · intro i c
      rw [show F = f4FrobAut (K := K) 1 by rfl]
      rw [f4FrobAutOne_pow_adjX]
      congr 1
      rw [← hKcard]
      exact FiniteField.pow_card c
    · intro i c
      rw [show F = f4FrobAut (K := K) 1 by rfl]
      rw [f4FrobAutOne_pow_adjY]
      congr 1
      rw [← hKcard]
      exact FiniteField.pow_card c
  obtain ⟨c₀, k, hα⟩ := f4_exists_conj_mul_pow (K := K) α
  let q : MulAut (adjointGroup ReeTag.F4.tag K) →*
      Outer (adjointGroup ReeTag.F4.tag K) :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (adjointGroup ReeTag.F4.tag K))
  let φbar : Outer (adjointGroup ReeTag.F4.tag K) := q φ
  let Fbar : Outer (adjointGroup ReeTag.F4.tag K) := q F
  let αbar : Outer (adjointGroup ReeTag.F4.tag K) := q α
  have hqconj : ∀ x : adjointGroup ReeTag.F4.tag K,
      q (MulAut.conj x) = 1 := by
    intro x
    change QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup ReeTag.F4.tag K)) (MulAut.conj x) = 1
    rw [QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq_one_iff]
    exact ⟨x, rfl⟩
  have hφbar_sq : φbar ^ 2 = Fbar := by
    calc
      φbar ^ 2 = q (φ ^ 2) := by rw [map_pow]
      _ = q (φ * φ) := by rw [pow_two]
      _ = q F := by rw [hφ2]
      _ = Fbar := rfl
  have hFbar_n : Fbar ^ (n : ℕ) = 1 := by
    calc
      Fbar ^ (n : ℕ) = q (F ^ (n : ℕ)) := by rw [map_pow]
      _ = q 1 := by rw [hFn]
      _ = 1 := by rw [map_one]
  have hφbar_2n : φbar ^ (2 * (n : ℕ)) = 1 := by
    calc
      φbar ^ (2 * (n : ℕ)) = (φbar ^ 2) ^ (n : ℕ) := by rw [pow_mul]
      _ = Fbar ^ (n : ℕ) := by rw [hφbar_sq]
      _ = 1 := hFbar_n
  have hαbar_eq : αbar = φbar ^ k := by
    have h := congrArg q hα
    simpa [αbar, φbar, q, map_mul, map_pow, hqconj] using h
  have hαbar5 : αbar ^ 5 = 1 := by
    have h := congrArg q hα5
    simpa [αbar, q, map_pow] using h
  have hαbar_ne : αbar ≠ 1 := by
    intro h
    have hq : q α = 1 := by simpa [αbar, q] using h
    have hin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup ReeTag.F4.tag K) :=
      (QuotientGroup.eq_one_iff α).mp hq
    rcases hin with ⟨x, hx⟩
    exact hnoninner x hx.symm
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have horderα : orderOf αbar = 5 :=
    orderOf_eq_prime hαbar5 hαbar_ne
  have h5dvd_orderφ : 5 ∣ orderOf φbar := by
    have hdiv : orderOf αbar ∣ orderOf φbar := by
      rw [hαbar_eq]
      exact orderOf_pow_dvd k
    rw [horderα] at hdiv
    exact hdiv
  have horderφ_dvd : orderOf φbar ∣ 2 * (n : ℕ) :=
    orderOf_dvd_of_pow_eq_one hφbar_2n
  have h5dvd_n : 5 ∣ (n : ℕ) := by
    have h52n : 5 ∣ 2 * (n : ℕ) := h5dvd_orderφ.trans horderφ_dvd
    have hp5 : Nat.Prime 5 := by norm_num
    rcases (hp5.dvd_mul).mp h52n with h5 | h5
    · norm_num at h5
    · exact h5
  have hαbar_sq_eq : αbar ^ 2 = Fbar ^ k := by
    calc
      αbar ^ 2 = (φbar ^ k) ^ 2 := by rw [hαbar_eq]
      _ = φbar ^ (k * 2) := by rw [pow_mul]
      _ = φbar ^ (2 * k) := by rw [Nat.mul_comm k 2]
      _ = (φbar ^ 2) ^ k := by rw [pow_mul]
      _ = Fbar ^ k := by rw [hφbar_sq]
  have hαbar_sq_mem : αbar ^ 2 ∈ Subgroup.zpowers Fbar := by
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨(k : ℤ), by simpa using hαbar_sq_eq.symm⟩
  have hαbar_mem_sq : αbar ∈ Subgroup.zpowers (αbar ^ 2) := by
    rw [mem_zpowers_pow_iff]
    rw [horderα]
    norm_num
  have hαbar_mem : αbar ∈ Subgroup.zpowers Fbar :=
    Subgroup.zpowers_le.mpr hαbar_sq_mem hαbar_mem_sq
  have hpow_mem : αbar ∈ Submonoid.powers Fbar :=
    mem_powers_iff_mem_zpowers.mpr hαbar_mem
  obtain ⟨m, hm⟩ : ∃ m : ℕ, Fbar ^ m = αbar := hpow_mem
  let d : ℤ := (k : ℤ) - 2 * (m : ℤ)
  have hφbar_eq : φbar ^ k = φbar ^ (2 * m) := by
    calc
      φbar ^ k = αbar := hαbar_eq.symm
      _ = Fbar ^ m := hm.symm
      _ = (φbar ^ 2) ^ m := by rw [← hφbar_sq]
      _ = φbar ^ (2 * m) := by rw [pow_mul]
  have hφbar_d : φbar ^ d = 1 := by
    have hz : φbar ^ (k : ℤ) = φbar ^ (2 * (m : ℤ)) := by
      rw [zpow_natCast, hφbar_eq]
      rw [show (2 * (m : ℤ)) = ((2 * m : ℕ) : ℤ) by norm_num, zpow_natCast]
    have h := congrArg (fun x : Outer (adjointGroup ReeTag.F4.tag K) =>
      x * (φbar ^ (2 * (m : ℤ)))⁻¹) hz
    simpa [d, zpow_sub] using h
  have hinner : φ ^ d ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (adjointGroup ReeTag.F4.tag K) := by
    have hq : q (φ ^ d) = 1 := by
      simpa [φbar, q, map_zpow] using hφbar_d
    exact (QuotientGroup.eq_one_iff (φ ^ d)).mp hq
  obtain ⟨y, hy⟩ := hinner
  have hφpow_eq : φ ^ k = φ ^ d * φ ^ (2 * m) := by
    have hd : d + (2 * (m : ℤ)) = (k : ℤ) := by
      dsimp [d]
      omega
    calc
      φ ^ k = φ ^ (k : ℤ) := by rw [zpow_natCast]
      _ = φ ^ (d + (2 * (m : ℤ))) := by rw [← hd]
      _ = φ ^ d * φ ^ (2 * (m : ℤ)) := by rw [zpow_add]
      _ = φ ^ d * φ ^ (2 * m) := by
        rw [show (2 * (m : ℤ)) = ((2 * m : ℕ) : ℤ) by norm_num, zpow_natCast]
  have hα_eq : α = MulAut.conj (c₀ * y) * φ ^ (2 * m) := by
    calc
      α = MulAut.conj c₀ * φ ^ k := hα
      _ = MulAut.conj c₀ * (φ ^ d * φ ^ (2 * m)) := by rw [hφpow_eq]
      _ = MulAut.conj c₀ * (MulAut.conj y * φ ^ (2 * m)) := by rw [← hy]
      _ = (MulAut.conj c₀ * MulAut.conj y) * φ ^ (2 * m) := by group
      _ = MulAut.conj (c₀ * y) * φ ^ (2 * m) := by rw [← map_mul]
  have hφpow : φ ^ (2 * m) = F ^ m := by
    rw [pow_mul]
    rw [pow_two, hφ2]
  let T : MulAut (adjointGroup ReeTag.F4.tag K) := F ^ m
  let N : adjointGroup ReeTag.F4.tag K :=
    ((List.range 5).map fun i => (T ^ i) (c₀ * y)).prod
  have hα_eq' : α = MulAut.conj (c₀ * y) * T := by
    rw [hα_eq, hφpow]
  have hα5' : (MulAut.conj (c₀ * y) * T) ^ 5 = 1 := by
    rw [← hα_eq']
    exact hα5
  have hconjpow := conj_mul_pow (c₀ * y) T 5
  rw [hconjpow] at hα5'
  have hT5eq : T ^ 5 = MulAut.conj (N⁻¹) := by
    have h := congrArg (fun z : MulAut (adjointGroup ReeTag.F4.tag K) =>
      (MulAut.conj N)⁻¹ * z) hα5'
    simpa [N, map_inv, mul_assoc] using h
  have hT5pow : T ^ 5 = F ^ (5 * m) := by
    dsimp [T]
    calc
      (F ^ m) ^ 5 = F ^ (m * 5) := by rw [pow_mul]
      _ = F ^ (5 * m) := by rw [Nat.mul_comm]
  let σ : K ≃+* K := iterateFrobeniusEquiv K 2 m
  let σ5 : K ≃+* K := iterateFrobeniusEquiv K 2 (5 * m)
  have hσ5_adjX : ∀ (i : Fin ReeTag.F4.tag.rank) (c : K),
      MulAut.conj (N⁻¹) (adjX ReeTag.F4.tag K i c) = adjX ReeTag.F4.tag K i (σ5 c) := by
    intro i c
    calc
      MulAut.conj (N⁻¹) (adjX ReeTag.F4.tag K i c) = (T ^ 5) (adjX ReeTag.F4.tag K i c) := by
        rw [← hT5eq]
      _ = (F ^ (5 * m)) (adjX ReeTag.F4.tag K i c) := by rw [hT5pow]
      _ = adjX ReeTag.F4.tag K i (c ^ 2 ^ (5 * m)) := by
        simpa [F] using f4FrobAutOne_pow_adjX (K := K) (5 * m) i c
      _ = adjX ReeTag.F4.tag K i (σ5 c) := by rw [iterateFrobeniusEquiv_def]
  have hσ5_one : σ5 = 1 :=
    f4_raw_borel_ree (K := K) (g := N⁻¹) σ5 hσ5_adjX
  have hσpow : σ ^ 5 = σ5 := by
    dsimp [σ, σ5]
    rw [iterateFrobeniusEquiv_eq_pow]
    rw [← pow_mul, iterateFrobeniusEquiv_eq_pow]
    congr 1
    omega
  have hσpow_one : σ ^ 5 = 1 := by
    rw [hσpow, hσ5_one]
  have hσne : σ ≠ 1 := by
    intro hσone
    have hFm1 : F ^ m = 1 := by
      apply mulAut_ext_adjX_adjY
      · intro i c
        have hc : c ^ 2 ^ m = c := by
          have h := congrArg (fun e : K ≃+* K => e c) hσone
          simpa [σ, iterateFrobeniusEquiv_def, iterateFrobenius_def] using h
        rw [f4FrobAutOne_pow_adjX, hc]
        rfl
      · intro i c
        have hc : c ^ 2 ^ m = c := by
          have h := congrArg (fun e : K ≃+* K => e c) hσone
          simpa [σ, iterateFrobeniusEquiv_def, iterateFrobenius_def] using h
        rw [f4FrobAutOne_pow_adjY, hc]
        rfl
    have hT1 : T = 1 := by
      simpa [T] using hFm1
    have hαinner : α = MulAut.conj (c₀ * y) := by
      rw [hα_eq', hT1, mul_one]
    exact hnoninner (c₀ * y) hαinner
  refine ⟨σ, c₀ * y, hσne, hσpow_one, ?_⟩
  intro z
  calc
    (α z : ModGL ReeTag.F4.tag K) =
        ((MulAut.conj (c₀ * y) * F ^ m) z : ModGL ReeTag.F4.tag K) := by
      rw [hα_eq', show T = F ^ m by rfl]
    _ = (c₀ * y : ModGL ReeTag.F4.tag K) * ((F ^ m) z : ModGL ReeTag.F4.tag K) *
        (c₀ * y : ModGL ReeTag.F4.tag K)⁻¹ := by
      rw [MulAut.mul_apply, MulAut.conj_apply]
      simp
    _ = (c₀ * y : ModGL ReeTag.F4.tag K) *
        Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) *
        (c₀ * y : ModGL ReeTag.F4.tag K)⁻¹ := by
      congr 2
      rw [← f4FrobAut_one_pow m, f4FrobAut_apply]
      rfl



theorem f4_field_form_with_inner_factor
    (α : MulAut (adjointGroup Tag.F4 K))
    (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ h : adjointGroup Tag.F4 K, α ≠ MulAut.conj h) :
    ∃ (σ : K ≃+* K) (h : adjointGroup Tag.F4 K),
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧
      ∀ z : adjointGroup Tag.F4 K,
        (α z : ModGL Tag.F4 K) =
          (h : ModGL Tag.F4 K) *
            Units.map (entrywiseHom σ.toRingHom) (z : ModGL Tag.F4 K) *
              (h : ModGL Tag.F4 K)⁻¹ := by
  exact f4_field_form_with_inner_factor_ree (K := K) α hα5 hnoninner


theorem f4_field_form_with_inner_factor_order
    (α : MulAut (adjointGroup Tag.F4 K))
    (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ h : adjointGroup Tag.F4 K, α ≠ MulAut.conj h) :
    ∃ (σ : K ≃+* K) (h : adjointGroup Tag.F4 K),
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧ orderOf σ = 5 ∧
      ∀ z : adjointGroup Tag.F4 K,
        (α z : ModGL Tag.F4 K) =
          (h : ModGL Tag.F4 K) *
            Units.map (entrywiseHom σ.toRingHom) (z : ModGL Tag.F4 K) *
              (h : ModGL Tag.F4 K)⁻¹ := by
  obtain ⟨σ, h, hσne, hσ5, hσact⟩ :=
    f4_field_form_with_inner_factor (K := K) α hα5 hnoninner
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact ⟨σ, h, hσne, hσ5, orderOf_eq_prime hσ5 hσne, hσact⟩



private noncomputable instance f4PacketFactPrimeFive : Fact (Nat.Prime 5) :=
  ⟨by norm_num⟩

private noncomputable instance f4PacketFintypeK : Fintype K :=
  Fintype.ofFinite K

private theorem f4FrobAut_eq_of_eq_add_mul_card [Fintype K]
    (d e t : ℕ) (hcardF : Fintype.card K = 2 ^ (5 * d)) :
    f4FrobAut (e + (5 * d) * t) = f4FrobAut (K := K) e := by
  apply mulAut_ext_adjX_adjY
  · intro i c
    rw [f4FrobAut_adjX, f4FrobAut_adjX]
    congr 1
    rw [Nat.pow_add]
    rw [show (2 : ℕ) ^ ((5 * d) * t) = ((2 : ℕ) ^ (5 * d)) ^ t by rw [pow_mul]]
    rw [← hcardF]
    rw [show c ^ (2 ^ e * Fintype.card K ^ t) =
        (c ^ 2 ^ e) ^ (Fintype.card K ^ t) by rw [pow_mul]]
    exact FiniteField.pow_card_pow t (c ^ 2 ^ e)
  · intro i c
    rw [f4FrobAut_adjY, f4FrobAut_adjY]
    congr 1
    rw [Nat.pow_add]
    rw [show (2 : ℕ) ^ ((5 * d) * t) = ((2 : ℕ) ^ (5 * d)) ^ t by rw [pow_mul]]
    rw [← hcardF]
    rw [show c ^ (2 ^ e * Fintype.card K ^ t) =
        (c ^ 2 ^ e) ^ (Fintype.card K ^ t) by rw [pow_mul]]
    exact FiniteField.pow_card_pow t (c ^ 2 ^ e)

private theorem f4FrobAut_pow_five_of_card [Fintype K]
    (d : ℕ) (hcardF : Fintype.card K = 2 ^ (5 * d)) :
    (f4FrobAut (K := K) d) ^ 5 = 1 := by
  have hF5d : (f4FrobAut (K := K) 1) ^ (5 * d) = 1 := by
    have h := f4FrobAut_eq_of_eq_add_mul_card (K := K) d 0 1 hcardF
    rw [show 0 + (5 * d) * 1 = 5 * d by ring] at h
    rw [← f4FrobAut_one_pow (5 * d), h, f4FrobAut_one_pow 0, pow_zero]
  calc
    (f4FrobAut (K := K) d) ^ 5 =
        (f4FrobAut (K := K) 1) ^ (d * 5) := by
      rw [f4FrobAut_one_pow, pow_mul]
    _ = (f4FrobAut (K := K) 1) ^ (5 * d) := by
      rw [show d * 5 = 5 * d by ring]
    _ = 1 := hF5d

omit [Finite K] in
private theorem packet_center_ree :
    Subgroup.center (adjointGroup ReeTag.F4.tag K) = ⊥ := by
  change Subgroup.center (adjointGroup Tag.F4 K) = ⊥
  exact CFSG.StandardType.F4ExplicitPos.CenterProofFast.center_adjointGroup_F4_charTwo_eq_bot
    (K := K)

omit [Finite K] in
private theorem f4_norm_one_of_order_five
    (A : MulAut (adjointGroup ReeTag.F4.tag K))
    (h : adjointGroup ReeTag.F4.tag K)
    (hA5 : A ^ 5 = 1)
    (hβ5 : (MulAut.conj h * A) ^ 5 = 1) :
    ((List.range 5).map fun i => (A ^ i) h).prod = 1 := by
  let N : adjointGroup ReeTag.F4.tag K :=
    ((List.range 5).map fun i => (A ^ i) h).prod
  have hconj := conj_mul_pow h A 5
  rw [hconj] at hβ5
  have hc : MulAut.conj N = 1 := by
    dsimp [N]
    simpa [hA5] using hβ5
  have hcenter := packet_center_ree (K := K)
  have hNcenter : N ∈ Subgroup.center (adjointGroup ReeTag.F4.tag K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz := congrArg (fun f : MulAut (adjointGroup ReeTag.F4.tag K) => f z) hc
    have hz' : N * z * N⁻¹ = z := by
      simpa [MulAut.conj_apply] using hz
    have hz'' : N * z = z * N := by
      simpa [mul_assoc] using congrArg (fun t => t * N) hz'
    exact hz''.symm
  rw [hcenter] at hNcenter
  have hN1 : N = 1 := by simpa using hNcenter
  simpa [N] using hN1

theorem f4_field_decomposition (σ : K ≃+* K)
    (hσ5 : σ ^ 5 = 1) (hσne : σ ≠ 1) :
    ∃ d : ℕ, 1 ≤ d ∧
      Nat.card K = 2 ^ (5 * d) ∧
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ 4 ∧
        σ = (frobeniusEquiv K 2) ^ (d * j) := by
  obtain ⟨n, -, hKcard⟩ := FiniteField.card K 2
  have hnpos : 1 ≤ (n : ℕ) := n.pos
  have hKnat : Nat.card K = 2 ^ (n : ℕ) := by
    simpa [Nat.card_eq_fintype_card] using hKcard
  have hordFrob : orderOf (frobeniusEquiv K 2) = (n : ℕ) :=
    CFSG.LocalAnalysis.EvenBN.G2.orderOf_frobeniusEquiv (K := K) hKnat hnpos
  obtain ⟨s, hslt, hseq⟩ :=
    CFSG.LocalAnalysis.EvenBN.G2.exists_eq_frobeniusEquiv_pow (K := K) hKnat hnpos σ
  have hσord : orderOf σ = 5 := orderOf_eq_prime hσ5 hσne
  have hordpow : orderOf (frobeniusEquiv K 2 ^ s) = 5 := by
    rw [← hseq, hσord]
  rw [orderOf_pow, hordFrob] at hordpow
  let d : ℕ := Nat.gcd (n : ℕ) s
  have hdpos : 1 ≤ d := by
    dsimp [d]
    exact Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left (n : ℕ) s) n.pos
  have hn_eq : (n : ℕ) = 5 * d := by
    calc
      (n : ℕ) = ((n : ℕ) / Nat.gcd (n : ℕ) s) * Nat.gcd (n : ℕ) s :=
        (Nat.div_mul_cancel (Nat.gcd_dvd_left (n : ℕ) s)).symm
      _ = 5 * Nat.gcd (n : ℕ) s := by rw [hordpow]
      _ = 5 * d := by rfl
  refine ⟨d, hdpos, ?_, ?_⟩
  · rw [hKnat, hn_eq]
  · have hdvd : d ∣ s := by
      dsimp [d]
      exact Nat.gcd_dvd_right (n : ℕ) s
    let j : ℕ := s / d
    have hs_eq : s = d * j := by
      dsimp [j]
      calc
        s = (s / d) * d := (Nat.div_mul_cancel hdvd).symm
        _ = d * (s / d) := by rw [Nat.mul_comm]
    refine ⟨j, ?_, ?_, ?_⟩
    · have hsne : s ≠ 0 := by
        intro hs0
        have h1 : orderOf σ = 1 := by
          rw [hseq, hs0, pow_zero, orderOf_one]
        rw [hσord] at h1
        norm_num at h1
      have hjne : j ≠ 0 := by
        intro hj0
        have hs0 : s = 0 := by rw [hs_eq, hj0, mul_zero]
        exact hsne hs0
      exact Nat.pos_of_ne_zero hjne
    · have hs_lt_5d : s < 5 * d := by
        have h := hslt
        rw [hn_eq] at h
        exact h
      have hdj_lt : d * j < d * 5 := by
        rw [hs_eq] at hs_lt_5d
        simpa [Nat.mul_comm] using hs_lt_5d
      have hjlt : j < 5 := Nat.lt_of_mul_lt_mul_left hdj_lt
      omega
    · calc
        σ = frobeniusEquiv K 2 ^ s := hseq
        _ = frobeniusEquiv K 2 ^ (d * j) := by rw [hs_eq]

private def packetInverseModFive (j : ℕ) : ℕ :=
  match j with
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | _ => 4

private theorem packetInverseModFive_spec (j : ℕ) (h1 : 1 ≤ j) (h4 : j ≤ 4) :
    1 ≤ packetInverseModFive j ∧ packetInverseModFive j ≤ 4 ∧
      j * packetInverseModFive j % 5 = 1 := by
  interval_cases j <;> norm_num [packetInverseModFive]

private theorem packet_eq_one_add_five_of_mod {n : ℕ}
    (h : n % 5 = 1) : ∃ t : ℕ, n = 1 + 5 * t := by
  refine ⟨n / 5, ?_⟩
  have hdecomp := Nat.div_add_mod n 5
  omega

theorem f4_field_form_with_inner_factor_norm
    (α : MulAut (adjointGroup Tag.F4 K))
    (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ h : adjointGroup Tag.F4 K, α ≠ MulAut.conj h) :
    ∃ (σ : K ≃+* K) (h : adjointGroup Tag.F4 K)
        (sigmaAut : MulAut (adjointGroup Tag.F4 K)),
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧
      (∀ z : adjointGroup Tag.F4 K,
        (sigmaAut z : ModGL Tag.F4 K) =
          Units.map (entrywiseHom σ.toRingHom) (z : ModGL Tag.F4 K)) ∧
      ((List.range 5).map fun i => (sigmaAut ^ i) h).prod = 1 ∧
      ∀ z : adjointGroup Tag.F4 K,
        (α z : ModGL Tag.F4 K) =
          (h : ModGL Tag.F4 K) *
            Units.map (entrywiseHom σ.toRingHom) (z : ModGL Tag.F4 K) *
              (h : ModGL Tag.F4 K)⁻¹ := by
  obtain ⟨σ, h, hσne, hσ5, hαact⟩ :=
    CFSG.LieType.Chevalley.F4NativeNormalForm.f4_field_form_with_inner_factor
      (K := K) α hα5 hnoninner
  obtain ⟨d, hdpos, hcard, j, hjpos, hjle, hσdecomp⟩ :=
    f4_field_decomposition (K := K) σ hσ5 hσne
  let αR : MulAut (adjointGroup ReeTag.F4.tag K) := α
  let hR : adjointGroup ReeTag.F4.tag K := h
  let sigmaAut : MulAut (adjointGroup ReeTag.F4.tag K) := f4FrobAut (d * j)
  have hcardF : Fintype.card K = 2 ^ (5 * d) := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hσring : (σ : K →+* K) = iterateFrobenius K 2 (d * j) := by
    ext c
    change σ c = iterateFrobenius K 2 (d * j) c
    rw [hσdecomp, frobeniusEquiv_pow_apply, iterateFrobenius_def]
  have hact : ∀ z : adjointGroup ReeTag.F4.tag K,
      (sigmaAut z : ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) := by
    intro z
    dsimp [sigmaAut]
    rw [f4FrobAut_apply, hσring]
  let D : MulAut (adjointGroup ReeTag.F4.tag K) := f4FrobAut d
  have hS_rel : sigmaAut = D ^ j := by
    dsimp [sigmaAut, D]
    rw [f4FrobAut_one_pow d, ← pow_mul, ← f4FrobAut_one_pow (d * j)]
  have hD5 : D ^ 5 = 1 := by
    dsimp [D]
    exact f4FrobAut_pow_five_of_card (K := K) d hcardF
  have hA5 : sigmaAut ^ 5 = 1 := by
    rw [hS_rel, ← pow_mul, show j * 5 = 5 * j by ring, pow_mul, hD5, one_pow]
  have hαact' : ∀ z : adjointGroup ReeTag.F4.tag K,
      (αR z : ModGL ReeTag.F4.tag K) =
        (hR : ModGL ReeTag.F4.tag K) *
          Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) *
            (hR : ModGL ReeTag.F4.tag K)⁻¹ := by
    intro z
    dsimp [αR, hR]
    exact hαact z
  have hαeq : αR = MulAut.conj hR * sigmaAut := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (αR z : ModGL ReeTag.F4.tag K) =
      ((MulAut.conj hR * sigmaAut) z : ModGL ReeTag.F4.tag K)
    simp [MulAut.mul_apply, MulAut.conj_apply, hαact' z, hact z]
  have hα5R : αR ^ 5 = 1 := by
    dsimp [αR]
    exact hα5
  have hβ5 : (MulAut.conj hR * sigmaAut) ^ 5 = 1 := by
    rw [← hαeq]
    exact hα5R
  have hnorm : ((List.range 5).map fun i => (sigmaAut ^ i) hR).prod = 1 :=
    f4_norm_one_of_order_five sigmaAut hR hA5 hβ5
  refine ⟨σ, hR, sigmaAut, hσne, hσ5, hact, hnorm, hαact⟩

theorem f4_field_form_coprime_power_ree
    (α : MulAut (adjointGroup ReeTag.F4.tag K))
    (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ h : adjointGroup ReeTag.F4.tag K, α ≠ MulAut.conj h) :
    ∃ (d j r : ℕ) (σ : K ≃+* K)
      (h h' : adjointGroup ReeTag.F4.tag K)
      (S D : MulAut (adjointGroup ReeTag.F4.tag K)),
      1 ≤ d ∧ 1 ≤ j ∧ j ≤ 4 ∧ 1 ≤ r ∧ r ≤ 4 ∧ j * r % 5 = 1 ∧
      Nat.card K = 2 ^ (5 * d) ∧
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧
      (∀ z : adjointGroup ReeTag.F4.tag K,
        (S z : ModGL ReeTag.F4.tag K) =
          Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K)) ∧
      (∀ z : adjointGroup ReeTag.F4.tag K,
        (D z : ModGL ReeTag.F4.tag K) =
          Units.map (entrywiseHom ((frobeniusEquiv K 2) ^ d).toRingHom)
            (z : ModGL ReeTag.F4.tag K)) ∧
      (α = MulAut.conj h * S) ∧
      S = D ^ j ∧
      ((List.range 5).map fun i => (S ^ i) h).prod = 1 ∧
      (α ^ r = MulAut.conj h' * D) ∧
      ((List.range 5).map fun i => (D ^ i) h').prod = 1 := by
  let αTag : MulAut (adjointGroup Tag.F4 K) := α
  have hα5Tag : αTag ^ 5 = 1 := by
    dsimp [αTag]
    exact hα5
  have hnoninnerTag : ∀ h : adjointGroup Tag.F4 K, αTag ≠ MulAut.conj h := by
    intro h
    exact hnoninner h
  obtain ⟨σ, h, S₀, hσne, hσ5, hS₀act, hnorm₀, hαact⟩ :=
    f4_field_form_with_inner_factor_norm (K := K) αTag hα5Tag hnoninnerTag
  obtain ⟨d, hdpos, hcard, j, hjpos, hjle, hσdecomp⟩ :=
    f4_field_decomposition (K := K) σ hσ5 hσne
  let αR : MulAut (adjointGroup ReeTag.F4.tag K) := α
  let hR : adjointGroup ReeTag.F4.tag K := h
  let S₀R : MulAut (adjointGroup ReeTag.F4.tag K) := S₀
  let S : MulAut (adjointGroup ReeTag.F4.tag K) := f4FrobAut (d * j)
  let D : MulAut (adjointGroup ReeTag.F4.tag K) := f4FrobAut d
  let r : ℕ := packetInverseModFive j
  have hcardF : Fintype.card K = 2 ^ (5 * d) := by
    simpa [Nat.card_eq_fintype_card] using hcard
  have hα5R : αR ^ 5 = 1 := by
    dsimp [αR]
    exact hα5
  have hσring : (σ : K →+* K) = iterateFrobenius K 2 (d * j) := by
    ext c
    change σ c = iterateFrobenius K 2 (d * j) c
    rw [hσdecomp, frobeniusEquiv_pow_apply, iterateFrobenius_def]
  have hSact : ∀ z : adjointGroup ReeTag.F4.tag K,
      (S z : ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) := by
    intro z
    dsimp [S]
    rw [f4FrobAut_apply, hσring]
  have hS₀actR : ∀ z : adjointGroup ReeTag.F4.tag K,
      (S₀R z : ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) := by
    intro z
    dsimp [S₀R]
    exact hS₀act z
  have hαactR : ∀ z : adjointGroup ReeTag.F4.tag K,
      (αR z : ModGL ReeTag.F4.tag K) =
        (hR : ModGL ReeTag.F4.tag K) *
          Units.map (entrywiseHom σ.toRingHom) (z : ModGL ReeTag.F4.tag K) *
            (hR : ModGL ReeTag.F4.tag K)⁻¹ := by
    intro z
    dsimp [αR, hR]
    exact hαact z
  have hS_eq : S₀R = S := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    rw [hS₀actR z, hSact z]
  have hαeq : αR = MulAut.conj hR * S := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change (αR z : ModGL ReeTag.F4.tag K) =
      ((MulAut.conj hR * S) z : ModGL ReeTag.F4.tag K)
    simp [MulAut.mul_apply, MulAut.conj_apply, hαactR z, hSact z]
  have hS_rel : S = D ^ j := by
    dsimp [S, D]
    rw [f4FrobAut_one_pow d, ← pow_mul, ← f4FrobAut_one_pow (d * j)]
  have hD5 : D ^ 5 = 1 := f4FrobAut_pow_five_of_card (K := K) d hcardF
  have hA5S : S ^ 5 = 1 := by
    rw [hS_rel, ← pow_mul, show j * 5 = 5 * j by ring, pow_mul, hD5, one_pow]
  have hβ5S : (MulAut.conj hR * S) ^ 5 = 1 := by
    rw [← hαeq]
    exact hα5R
  have hnormS : ((List.range 5).map fun i => (S ^ i) hR).prod = 1 :=
    f4_norm_one_of_order_five S hR hA5S hβ5S
  have hrspec := packetInverseModFive_spec j hjpos hjle
  have hrpos : 1 ≤ r := hrspec.1
  have hrle : r ≤ 4 := hrspec.2.1
  have hjr : j * r % 5 = 1 := hrspec.2.2
  obtain ⟨t, ht⟩ := packet_eq_one_add_five_of_mod hjr
  have hmul_exp : (d * j) * r = d + (5 * d) * t := by
    calc
      (d * j) * r = d * (j * r) := by ring
      _ = d * (1 + 5 * t) := by rw [ht]
      _ = d + (5 * d) * t := by ring
  have hDact : ∀ z : adjointGroup ReeTag.F4.tag K,
      (D z : ModGL ReeTag.F4.tag K) =
        Units.map (entrywiseHom ((frobeniusEquiv K 2) ^ d).toRingHom)
          (z : ModGL ReeTag.F4.tag K) := by
    intro z
    have hringD : ((frobeniusEquiv K 2) ^ d).toRingHom =
        iterateFrobenius K 2 d := by
      ext c
      change ((frobeniusEquiv K 2) ^ d) c = iterateFrobenius K 2 d c
      rw [frobeniusEquiv_pow_apply, iterateFrobenius_def]
    have hringD' : (↑((frobeniusEquiv K 2) ^ d) : K →+* K) =
        iterateFrobenius K 2 d := hringD
    dsimp [D]
    rw [f4FrobAut_apply, hringD']
  have hS_pow : S ^ r = D := by
    dsimp [S, D]
    rw [f4FrobAut_one_pow, ← pow_mul, ← f4FrobAut_one_pow ((d * j) * r)]
    rw [hmul_exp]
    exact f4FrobAut_eq_of_eq_add_mul_card (K := K) d d t hcardF
  let h' : adjointGroup ReeTag.F4.tag K :=
    ((List.range r).map fun i => (S ^ i) hR).prod
  have hαr : αR ^ r = MulAut.conj h' * S ^ r := by
    calc
      αR ^ r = (MulAut.conj hR * S) ^ r := by rw [hαeq]
      _ = MulAut.conj h' * S ^ r := conj_mul_pow hR S r
  have hαr' : αR ^ r = MulAut.conj h' * D := by
    rw [hαr, hS_pow]
  have hαr5 : (αR ^ r) ^ 5 = 1 := by
    calc
      (αR ^ r) ^ 5 = αR ^ (r * 5) := by rw [← pow_mul]
      _ = 1 := by rw [show r * 5 = 5 * r by ring, pow_mul, hα5R, one_pow]
  have hβ5 : (MulAut.conj h' * D) ^ 5 = 1 := by
    simpa [hαr'] using hαr5
  have hnorm' : ((List.range 5).map fun i => (D ^ i) h').prod = 1 :=
    f4_norm_one_of_order_five D h' hD5 hβ5
  exact ⟨d, j, r, σ, hR, h', S, D, hdpos, hjpos, hjle, hrpos, hrle, hjr,
    hcard, hσne, hσ5, hSact, hDact, hαeq, hS_rel, hnormS, hαr', hnorm'⟩

theorem f4_field_form_coprime_power
    (α : MulAut (adjointGroup Tag.F4 K))
    (hα5 : α ^ 5 = 1)
    (hnoninner : ∀ h : adjointGroup Tag.F4 K, α ≠ MulAut.conj h) :
    ∃ (d j r : ℕ) (σ : K ≃+* K)
      (h h' : adjointGroup Tag.F4 K)
      (S D : MulAut (adjointGroup Tag.F4 K)),
      1 ≤ d ∧ 1 ≤ j ∧ j ≤ 4 ∧ 1 ≤ r ∧ r ≤ 4 ∧ j * r % 5 = 1 ∧
      Nat.card K = 2 ^ (5 * d) ∧
      σ ≠ 1 ∧ σ ^ 5 = 1 ∧
      (∀ z : adjointGroup Tag.F4 K,
        (S z : ModGL Tag.F4 K) =
          Units.map (entrywiseHom σ.toRingHom) (z : ModGL Tag.F4 K)) ∧
      (∀ z : adjointGroup Tag.F4 K,
        (D z : ModGL Tag.F4 K) =
          Units.map (entrywiseHom ((frobeniusEquiv K 2) ^ d).toRingHom)
            (z : ModGL Tag.F4 K)) ∧
      (α = MulAut.conj h * S) ∧
      S = D ^ j ∧
      ((List.range 5).map fun i => (S ^ i) h).prod = 1 ∧
      (α ^ r = MulAut.conj h' * D) ∧
      ((List.range 5).map fun i => (D ^ i) h').prod = 1 := by
  let αR : MulAut (adjointGroup ReeTag.F4.tag K) := α
  have hα5R : αR ^ 5 = 1 := by
    dsimp [αR]
    exact hα5
  have hnoninnerR : ∀ h : adjointGroup ReeTag.F4.tag K, αR ≠ MulAut.conj h := by
    intro h
    exact hnoninner h
  obtain ⟨d, j, r, σ, h, h', S, D, hd, hj, hj4, hr, hr4, hjr,
    hcard, hσne, hσ5, hSact, hDact, hαeq, hSrel, hnormS, hαr, hnorm'⟩ :=
    f4_field_form_coprime_power_ree (K := K) αR hα5R hnoninnerR
  exact ⟨d, j, r, σ, h, h', S, D, hd, hj, hj4, hr, hr4, hjr,
    hcard, hσne, hσ5, hSact, hDact, hαeq, hSrel, hnormS, hαr, hnorm'⟩

omit [Finite K] [CharP K 2] in
theorem f4_conjugacy_of_coprime_power
    (α : MulAut (adjointGroup Tag.F4 K))
    (hα5 : α ^ 5 = 1)
    (S D : MulAut (adjointGroup Tag.F4 K)) (j r : ℕ)
    (hS : S = D ^ j)
    (hjr : j * r % 5 = 1)
    (T : MulAut (adjointGroup Tag.F4 K))
    (hT : T * α ^ r * T⁻¹ = D) :
    T * α * T⁻¹ = S := by
  obtain ⟨t, ht⟩ := packet_eq_one_add_five_of_mod hjr
  have hαr : α = (α ^ r) ^ j := by
    rw [← pow_mul, Nat.mul_comm r j, ht]
    rw [pow_add, pow_mul, hα5, one_pow, mul_one, pow_one]
  have hT' : MulAut.conj T (α ^ r) = D := by
    simpa [MulAut.conj_apply] using hT
  calc
    T * α * T⁻¹ = MulAut.conj T α := by rw [MulAut.conj_apply]
    _ = MulAut.conj T ((α ^ r) ^ j) := congrArg (MulAut.conj T) hαr
    _ = (MulAut.conj T (α ^ r)) ^ j := by rw [map_pow]
    _ = D ^ j := by rw [hT']
    _ = S := hS.symm


end

end F4NativeNormalForm

end CFSG.LieType.Chevalley
