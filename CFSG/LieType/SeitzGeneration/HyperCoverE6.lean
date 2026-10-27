module

public import CFSG.LieType.SeitzGeneration.HyperCoverLift
public import CFSG.LieType.SeitzGeneration.HyperExCubeTw
public import CFSG.LocalAnalysis.ComponentClassification.TBLitInputs
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCoverRankFiveCensus
import CFSG.RankThree.PartOne.K133B.NC5Cover
import CFSG.RankThree.PartTwo.Sec4.Census.Item43Narrow

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.TauCetiBridge
  CFSG.Open CFSG.AGLEmbedding TauCeti CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLAY
  CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)


@[expose] def RootInvariantHyperGenerationR {G : Type*} [Group G] (N : Subgroup G) (r p : ℕ) :
    Prop :=
  ∀ A R : Subgroup G, A ≤ N → IsElementaryAbelian p ↥A → A ≠ ⊥ → R ≤ N →
    IsPGroup r ↥R → R ≠ ⊥ → A ≤ Subgroup.normalizer (R : Set G) →
    N ≤ Subgroup.closure (hyperRSet N A r p)

theorem closure_hyperRSet_of_native {C G : Type*} [Group C] [Group G] {N : Subgroup G}
    (e : C ≃* N) {r p : ℕ} (hgen : RootInvariantHyperGenerationR N r p) {E : Subgroup C}
    (hE : IsElemAbelian p E) (hE1 : E ≠ ⊥)
    (hR : ∃ R : Subgroup C, R ≠ ⊥ ∧ IsPGroup r ↥R ∧
      ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R) :
    (⊤ : Subgroup C) ≤ Subgroup.closure (hyperRSet ⊤ E r p) := by
  obtain ⟨R, hR1, hRp, hRn⟩ := hR
  let ι : C →* G := N.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hιN : ∀ c, ι c ∈ N := fun c => (e c).2
  set A : Subgroup G := E.map ι with hA
  set R' : Subgroup G := R.map ι with hR'
  have hAN : A ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hR'N : R' ≤ N := by
    rintro _ ⟨c, -, rfl⟩
    exact hιN c
  have hAel : IsElementaryAbelian p ↥A :=
    isElementaryAbelian_of_isElemAbelian
      (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE ι)
  have hA1 : A ≠ ⊥ := fun h => hE1 ((Subgroup.map_eq_bot_iff_of_injective E hι).mp h)
  have hR'p : IsPGroup r ↥R' :=
    hRp.of_surjective (ι.subgroupMap R) (ι.subgroupMap_surjective R)
  have hR'1 : R' ≠ ⊥ := fun h => hR1 ((Subgroup.map_eq_bot_iff_of_injective R hι).mp h)
  have hnormC : ∀ c ∈ E, ∀ x : C, x ∈ R ↔ c * x * c⁻¹ ∈ R := by
    intro c hc x
    have hRc : R.map (MulAut.conj c).toMonoidHom = R := hRn c hc
    constructor
    · intro hx
      rw [← hRc]
      exact ⟨x, hx, rfl⟩
    · intro hx
      rw [← hRc] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := by
        have h2 : c * y * c⁻¹ = c * x * c⁻¹ := hyx
        simpa using h2
      rw [← this]
      exact hy
  have hAnorm : A ≤ Subgroup.normalizer (R' : Set G) := by
    rintro _ ⟨c, hc, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c * x * c⁻¹, (hnormC c hc x).mp hx, by simp [map_mul]⟩
    · rintro ⟨y, hy, hyh⟩
      refine ⟨c⁻¹ * y * c, ?_, ?_⟩
      · have := (hnormC c⁻¹ (E.inv_mem hc) y).mp hy
        simpa using this
      · have h2 : ι y = ι c * h * (ι c)⁻¹ := hyh
        have h3 : h = (ι c)⁻¹ * ι y * ι c := by
          rw [h2]
          group
        rw [h3]
        simp [map_mul, map_inv]
  have hgenA := hgen A R' hAN hAel hA1 hR'N hR'p hR'1 hAnorm
  have hS : hyperRSet N A r p ⊆ ι '' hyperRSet ⊤ E r p := by
    rintro z ⟨hzN, ⟨n, hn⟩, B, hBA, hBi, hzB⟩
    obtain ⟨c, hc⟩ := e.surjective ⟨z, hzN⟩
    have hcz : ι c = z := congrArg Subtype.val hc
    refine ⟨c, ⟨Subgroup.mem_top c, ⟨n, hι ?_⟩, B.comap ι, ?_, ?_, ?_⟩, hcz⟩
    · rw [map_pow, hcz, hn, map_one]
    · intro y hy
      obtain ⟨y', hy', hyy'⟩ := hBA hy
      rw [← hι hyy']
      exact hy'
    · rw [Subgroup.relIndex_comap]
      exact hBi
    · rw [Subgroup.mem_centralizer_iff]
      intro f hf
      apply hι
      rw [map_mul, map_mul, hcz]
      exact Subgroup.mem_centralizer_iff.1 hzB (ι f) hf
  have hle : N ≤ (Subgroup.closure (hyperRSet ⊤ E r p)).map ι := by
    rw [MonoidHom.map_closure]
    exact hgenA.trans (Subgroup.closure_mono hS)
  intro c _
  obtain ⟨y, hy, hyc⟩ := hle (hιN c)
  rw [← hι hyc]
  exact hy

theorem exists_sl2_three_inv (k : Type) [Field k] [Fintype k] (h3 : (3 : k) ≠ 0) :
    ∃ A : SL2 k, A ^ 3 = 1 ∧ A ≠ 1 ∧ WSL * A * WSL⁻¹ = A⁻¹ := by
  obtain ⟨α, β, h⟩ : ∃ α β : k, α ^ 2 + α + 1 + β ^ 2 = 0 := by
    by_cases h2 : ringChar k = 2
    · refine ⟨0, 1, ?_⟩
      have h20 : (2 : k) = 0 := by
        have := (ringChar.spec k 2).2 (by rw [h2])
        exact_mod_cast this
      linear_combination h20
    · have hodd : Fintype.card k % 2 = 1 := by
        have := (FiniteField.even_card_iff_char_two (F := k)).not.1 h2
        omega
      obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
        (f := Polynomial.X ^ 2 + Polynomial.X + 1) (g := Polynomial.X ^ 2)
        (by compute_degree!) (Polynomial.degree_X_pow 2) hodd
      refine ⟨a, b, ?_⟩
      simpa using hab
  let A : SL2 k := ⟨!![α, β; β, -1 - α], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : k) * h⟩
  let M : SL2 k := ⟨!![-1 - α, -β; -β, α], by
    rw [Matrix.det_fin_two_of]
    linear_combination (-1 : k) * h⟩
  have hAA : A * A = M := by
    apply Subtype.ext
    change !![α, β; β, -1 - α] * !![α, β; β, -1 - α] = !![-1 - α, -β; -β, α]
    rw [Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination h
  have hMA : M * A = 1 := by
    apply Subtype.ext
    change !![-1 - α, -β; -β, α] * !![α, β; β, -1 - α] = (1 : Matrix (Fin 2) (Fin 2) k)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp <;> first | ring1 | linear_combination (-1 : k) * h
  have hWA : WSL * A = M * WSL := by
    apply Subtype.ext
    change !![0, 1; -1, 0] * !![α, β; β, -1 - α] = !![-1 - α, -β; -β, α] * !![0, 1; -1, 0]
    rw [Matrix.mul_fin_two, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  refine ⟨A, ?_, fun h1 => ?_, ?_⟩
  · rw [pow_succ, sq, hAA, hMA]
  · have h00 := congrArg (fun g : SL2 k => (g : Matrix (Fin 2) (Fin 2) k) 0 0) h1
    have h11 := congrArg (fun g : SL2 k => (g : Matrix (Fin 2) (Fin 2) k) 1 1) h1
    simp only [A, Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply_eq] at h00 h11
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one] at h00 h11
    apply h3
    linear_combination -h00 - h11
  · rw [mul_inv_eq_of_eq_mul hWA]
    exact eq_inv_of_mul_eq_one_left hMA

theorem exists_rSub_of_commute_sl2 {S : Type*} [Group S] {k : Type} [Field k] {r : ℕ}
    [Fact r.Prime] [CharP k r] (ρ : SL2 k →* S) (hρ : Function.Injective ρ)
    {E : Subgroup S} (hE : ∀ x ∈ E, ∀ A, Commute x (ρ A)) :
    ∃ R : Subgroup S, R ≠ ⊥ ∧ IsPGroup r ↥R ∧
      ∀ x ∈ E, R.map (MulAut.conj x).toMonoidHom = R := by
  refine ⟨(ρ.comp (uSLHom k)).range, ?_, ?_, ?_⟩
  · intro h
    have h1 : ρ (uSL 1) ∈ (ρ.comp (uSLHom k)).range := ⟨Multiplicative.ofAdd 1, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact uSL_one_ne_one' (hρ (h1.trans (map_one ρ).symm))
  · have hK : IsPGroup r (Multiplicative k) := fun c => ⟨1, by
      rw [pow_one, ← ofAdd_toAdd c, ← ofAdd_nsmul, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      rfl⟩
    exact hK.of_surjective _ (ρ.comp (uSLHom k)).rangeRestrict_surjective
  · intro x hx
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨c, rfl⟩ := hz
      change x * ρ (uSL (Multiplicative.toAdd c)) * x⁻¹ ∈ _
      rw [(hE x hx _).eq, mul_inv_cancel_right]
      exact ⟨c, rfl⟩
    · rintro ⟨c, rfl⟩
      refine ⟨ρ (uSL (Multiplicative.toAdd c)), ⟨c, rfl⟩, ?_⟩
      change x * ρ (uSL (Multiplicative.toAdd c)) * x⁻¹ = _
      rw [(hE x hx _).eq, mul_inv_cancel_right]
      rfl

theorem exists_hyperGen_cover_of_four_sl2 {K S : Type} [Group K] [Group S] [Finite K]
    [Group.IsPerfect K] (ρ : K →* S) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center K) (hz : 3 ∣ Nat.card ρ.ker) {k : Type} [Field k]
    [Finite k] {r : ℕ} (hr : r.Prime) [CharP k r] (hr3 : r ≠ 3) (ψ : Fin 4 → SL2 k →* S)
    (hinj : ∀ i, Function.Injective (ψ i))
    (hcomm : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B))
    (hgen : ∀ D : Subgroup S, IsElemAbelian 3 D → D ≠ ⊥ →
      (∃ R : Subgroup S, R ≠ ⊥ ∧ IsPGroup r ↥R ∧
        ∀ x ∈ D, R.map (MulAut.conj x).toMonoidHom = R) →
      (⊤ : Subgroup S) ≤ Subgroup.closure (hyperRSet ⊤ D r 3)) :
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ HyperGen 3 ⊤ E := by
  have : Fact r.Prime := ⟨hr⟩
  have := Fintype.ofFinite k
  have h3 : (3 : k) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k r] at h'
    exact hr3 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h')
  obtain ⟨A, hA3, hA1, hWA⟩ := exists_sl2_three_inv k h3
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have hab : Commute (ψ 0 A) (ψ 1 A) := hcomm 0 1 h01 A A
  have ha : ψ 0 A ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
  have hb : ψ 1 A ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
  have hn : ψ 0 WSL * ψ 0 A * (ψ 0 WSL)⁻¹ = (ψ 0 A)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hWA, map_inv]
  have hmb : ψ 1 WSL * ψ 1 A * (ψ 1 WSL)⁻¹ = (ψ 1 A)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, hWA, map_inv]
  have hma : Commute (ψ 1 WSL) (ψ 0 A) := hcomm 1 0 h01.symm WSL A
  have hoA : orderOf A = 3 := orderOf_eq_prime hA3 hA1
  have key : ∀ (i : Fin 4) (t : ℤ), (∀ B, Commute (ψ i (A ^ t)) (ψ i B)) → (3 : ℤ) ∣ t := by
    intro i t h
    have hcomm' : ∀ B, Commute (A ^ t) B := fun B =>
      hinj i (by rw [map_mul, map_mul]; exact (h B).eq)
    have hAt : A ^ t = 1 := eq_one_of_commute_uSL_vSL Nat.prime_three (by norm_num)
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hA3, one_zpow])
      (hcomm' _) (hcomm' _)
    have h := orderOf_dvd_iff_zpow_eq_one.2 hAt
    rw [hoA] at h
    exact_mod_cast h
  have hind : ∀ i j : ℤ, ψ 0 A ^ i * ψ 1 A ^ j = 1 → (3 : ℤ) ∣ i ∧ (3 : ℤ) ∣ j := by
    intro i j hij
    have hi : (3 : ℤ) ∣ i := by
      refine key 0 i fun B => ?_
      have he : ψ 0 (A ^ i) = (ψ 1 A ^ j)⁻¹ := by
        rw [map_zpow]
        exact eq_inv_of_mul_eq_one_left hij
      rw [he]
      exact ((hcomm 0 1 h01 B A).symm.zpow_left j).inv_left
    refine ⟨hi, ?_⟩
    rw [zpow_eq_one_of_dvd_exp ha hi, one_mul] at hij
    refine key 1 j fun B => ?_
    rw [map_zpow, hij]
    exact Commute.one_left _
  obtain ⟨D, hD, hDc, hDgen, haD, -⟩ := exists_plane_of_two Nat.prime_three hab ha hb hind
  have hD1 : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at haD
    exact hA1 (hinj 0 (haD.trans (map_one _).symm))
  have hD3 : ∀ x ∈ D, ∀ B, Commute x (ψ 3 B) := by
    intro x hx B
    obtain ⟨i, j, rfl⟩ := hDgen x hx
    exact ((hcomm 0 3 (by decide) A B).zpow_left i).mul_left
      ((hcomm 1 3 (by decide) A B).zpow_left j)
  have hgenD := hgen D hD hD1 (exists_rSub_of_commute_sl2 (ψ 3) (hinj 3) hD3)
  exact exists_hyperGen_of_cover ρ hρ hker Nat.prime_three (by norm_num) hr hr3 hz ha hb hab
    hind hn hma hmb hDgen hDc hgenD

section Families


theorem exists_hyperGen_cover_E6 (q : PrimePower) (hv : (LieTypeIndex.E6 q).Valid)
    (hq3 : q.p ≠ 3) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.E6 q, hv⟩) (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ HyperGen 3 ⊤ E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  obtain ⟨k, _, _, -, hkc, ⟨φ⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have : IsSimpleGroup ↥(adjointGroup .E6 k) := isSimpleGroup_adjointGroup_of_isQuasisimple
    (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 k)
  let ρ : K →* ↥(adjointGroup .E6 k) :=
    (φ.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ :=
    (φ.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center K := by
    ext x
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨ψ, hinj, hcomm⟩ := exists_four_sl2_of_frame frameE6 (by norm_num) k
  refine exists_hyperGen_cover_of_four_sl2 ρ hρs hker.le (by rw [hker]; exact hz) q.prime_p
    hq3 ψ hinj hcomm fun D hD hD1 hR => ?_
  refine closure_hyperRSet_of_native (MulEquiv.refl _) (fun A R hAC hA hA1 hRC hRr hR1 hAR => ?_)
    hD hD1 hR
  have := hA
  exact ordinary_root_invariant_prime_subgroup_hyperplane_generation_r .E6 k q.p 3 hq3 A hAC hA1
    R hRC hRr hR1 hAR

theorem isSimpleGroup_cat_twistedE6' {q : PrimePower} (hv : (LieTypeIndex.twistedE6 q).Valid) :
    IsSimpleGroup (Cat ⟨.twistedE6 q, hv⟩) := by
  obtain ⟨K, _, _, hK, -⟩ := exists_field_pow q (m := TwistTag.E6.order) TwistTag.E6.order_pos
  rw [PrimePower.card_def] at hK
  obtain ⟨σ, hσ, -⟩ := finite_graph_field_parameter_fields TwistTag.E6 q.prime_p q.exponent_pos K hK
  have hσ'' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => by
    rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, hσ]
  have hσ' : ∀ x, σ.toRingHom x = x ^ q.card := fun x => by
    rw [PrimePower.card_def]
    exact hσ'' x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv K
    (by rw [PrimePower.card_def]; exact hK) σ.toRingHom hσ'
  exact (CFSG.LieType.Simplicity.fam_2e6_simplicity _ q.p q.exponent
    ⟨⟨q.prime_p, q.exponent_pos, rfl⟩, K, inferInstance, inferInstance, hK, σ.toRingHom,
      hσ'', ⟨φ.symm⟩⟩).2

theorem exists_hyperGen_cover_twistedE6 (q : PrimePower) (hv : (LieTypeIndex.twistedE6 q).Valid)
    (hq3 : q.p ≠ 3) {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* Cat ⟨.twistedE6 q, hv⟩)
    (hz : 3 ∣ Nat.card (Subgroup.center K)) :
    ∃ E : Subgroup K, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧ HyperGen 3 ⊤ E := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hK.1
  obtain ⟨L, _, σ, hL, hσ, ⟨φ⟩⟩ := exists_catEquiv_twistedE6 q hv
  have : Finite L := Nat.finite_of_card_ne_zero (by
    rw [hL]
    exact pow_ne_zero 2 (pow_ne_zero _ q.prime_p.ne_zero))
  have := Fintype.ofFinite L
  have hLc : CharP L q.p := charP_of_card_eq_prime_pow (f := q.exponent * 2) (by
    rw [← Nat.card_eq_fintype_card, hL, pow_mul])
  have hσ' : ∀ x, σ.toRingHom x = x ^ (q.p ^ q.exponent) := fun x => hσ x
  have hcl := (finite_fixed_root_group_perfect TwistTag.E6 q.prime_p q.exponent_pos L hL
    σ.toRingHom hσ').2.2.1
  obtain ⟨ψ, hinj, hcomm⟩ := exists_four_sl2_twistedE6 (fixSubfield σ).subtype σ.toRingHom
    (fun c => c.2) hcl
  have hk : Nat.card (fixSubfield σ) = q.card := by
    rw [card_fixSubfield_sq q.prime_p q.exponent_pos hL σ hσ, PrimePower.card_def]
  have : Finite (fixSubfield σ) := Nat.finite_of_card_ne_zero (by
    rw [hk, PrimePower.card_def]
    exact pow_ne_zero _ q.prime_p.ne_zero)
  have : CharP (fixSubfield σ) q.p := ⟨fun x => by
    rw [← CharP.cast_eq_zero_iff L q.p x, ← map_natCast (fixSubfield σ).subtype x,
      map_eq_zero_iff _ Subtype.val_injective]⟩
  have : IsSimpleGroup ↥(graphFixedRootGroup TwistTag.E6 L σ.toRingHom) :=
    @MulEquiv.isSimpleGroup _ _ _ _ (isSimpleGroup_cat_twistedE6' hv) φ.symm
  have hσ2 : σ ^ TwistTag.E6.order = 1 := by
    rw [show TwistTag.E6.order = 2 from rfl]
    refine RingEquiv.ext fun x => ?_
    rw [RingAut.one_apply, sq, RingAut.mul_apply, hσ, hσ, ← pow_mul, ← sq, ← hL,
      Nat.card_eq_fintype_card, FiniteField.pow_card]
  let ρ : K →* ↥(graphFixedRootGroup TwistTag.E6 L σ.toRingHom) :=
    (φ.toMonoidHom.comp e.toMonoidHom).comp (QuotientGroup.mk' (Subgroup.center K))
  have hρs : Function.Surjective ρ :=
    (φ.surjective.comp e.surjective).comp (QuotientGroup.mk'_surjective _)
  have hker : ρ.ker = Subgroup.center K := by
    ext x
    simp only [ρ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine exists_hyperGen_cover_of_four_sl2 ρ hρs hker.le (by rw [hker]; exact hz) q.prime_p
    hq3 ψ hinj hcomm fun D hD hD1 hR => ?_
  refine closure_hyperRSet_of_native (MulEquiv.refl _) (fun A R hAC hA hA1 hRC hRr hR1 hAR => ?_)
    hD hD1 hR
  have := hA
  exact fixed_root_invariant_prime_subgroup_hyperplane_generation_r TwistTag.E6 L q.p 3 hq3 σ hσ2
    A hAC hA1 R hRC hRr hR1 hAR

end Families

theorem exc_cover_cases (hGA : GriessMultipliersAllModels) {K : Type} [Group K] [Finite K]
    (hK : Open.IsQuasisimple K) (d : ValidLieTypeIndex) (hd : ¬ IsClassicalIndex d.1)
    (e : K ⧸ Subgroup.center K ≃* Cat d) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ≠ d.1.characteristic) (hz : p ∣ Nat.card (Subgroup.center K)) :
    p = 3 ∧ ((∃ q, d.1 = .E6 q) ∨ (∃ q, d.1 = .twistedE6 q)) := by
  have hq' : CFSG.IsQuasisimple K :=
    CFSG.AGLEmbedding.KFactProofs.CoverFive.isQuasisimple_of_open hK
  obtain ⟨dd, hv⟩ := d
  by_cases h3 : p = 3
  · subst h3
    refine ⟨rfl, ?_⟩
    have hidx := CFSG.RankThree.PartTwo.Sec4.Census.tripleCoverLie_of_griess hGA ⟨dd, hv⟩ K
      ⟨hq', hz, ⟨e⟩⟩
    cases dd with
    | E6 q => exact Or.inl ⟨q, rfl⟩
    | twistedE6 q => exact Or.inr ⟨q, rfl⟩
    | G2 q =>
      exfalso
      have hq : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1
        (by
          rw [← (hidx : q.card = 3), PrimePower.card_def]
          exact dvd_pow_self _ q.exponent_pos.ne')
      exact hpd (by rw [LieTypeIndex.characteristic_G2, hq])
    | _ => first | exact (hd trivial).elim | exact hidx.elim
  · exfalso
    have hidx : CFSG.RankThree.PartOne.N143.PrimeCoverLieIndex p dd := by
      by_cases h5 : p = 5
      · subst h5
        exact CFSG.RankThree.PartOne.K133B.primeCoverLie_five hGA ⟨dd, hv⟩ hq' e hz
      · have h7 : 7 ≤ p := by
          have h2 := hp.two_le
          by_contra hlt
          have h4 : p ≠ 4 := by
            rintro rfl
            exact absurd hp (by norm_num)
          have h6 : p ≠ 6 := by
            rintro rfl
            exact absurd hp (by norm_num)
          omega
        exact CFSG.RankThree.PartOne.N143.primeCoverLie_of_griess hGA hp h7 ⟨dd, hv⟩ hq' e hz
    cases dd with
    | A r q => exact hd trivial
    | twistedA r q => exact hd trivial
    | _ => exact hidx.elim

@[expose] def HyperExCoverFor (Fam : ValidLieTypeIndex → Prop) : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (K : Type) [Group K] [Finite K], Open.IsQuasisimple K →
    ∀ d : ValidLieTypeIndex, Fam d →
    Nonempty (K ⧸ Subgroup.center K ≃* (TauCeti.CFSGIndex.lie d).Group) →
    p ≠ d.1.characteristic → ¬ P1ThreeLieList p d → p ∣ Nat.card (Subgroup.center K) →
    ∃ E : Subgroup K, IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ HyperGen p ⊤ E

section Exceptional


theorem hyperExCoverFor_exc (hGA : GriessMultipliersAllModels) :
    HyperExCoverFor fun d => ¬ IsClassicalIndex d.1 := by
  intro p hp hp2 K _ _ hK d hd ⟨e⟩ hpd _ hz
  obtain ⟨rfl, ⟨q, hq⟩ | ⟨q, hq⟩⟩ := exc_cover_cases hGA hK d hd e hp hp2 hpd hz
  · obtain ⟨dd, hv⟩ := d
    simp only at hq
    subst hq
    exact exists_hyperGen_cover_E6 q hv
      (fun h => hpd (by rw [LieTypeIndex.characteristic_E6, h])) hK e hz
  · obtain ⟨dd, hv⟩ := d
    simp only at hq
    subst hq
    exact exists_hyperGen_cover_twistedE6 q hv
      (fun h => hpd (by rw [LieTypeIndex.characteristic_twistedE6, h])) hK e hz

end Exceptional

end CFSG.LieType.SeitzGeneration
