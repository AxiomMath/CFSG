module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4OuterBound
public import CFSG.LocalAnalysis.StandardType.GGD4AdjointOm8
public import CFSG.HardMathSupport.Dickson.Sec6.I1431D4Aux.FieldPart.NormalForm
public import CFSG.LieType.ChevTwo.OppCl.D4Normal

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.Universal.Spin CFSG.QuasithinUnique.Setup CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem eq_one_or_eq_one_or_eq_of_cartan {x y : Equiv.Perm (Fin Tag.D4.rank)}
    (hx : ∀ i j, Tag.D4.cartan (x i) (x j) = Tag.D4.cartan i j)
    (hy : ∀ i j, Tag.D4.cartan (y i) (y j) = Tag.D4.cartan i j)
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hxy : x * y = y * x) : x = 1 ∨ y = 1 ∨ x = y := by
  let M : Fin 4 → Fin 4 → ℤ :=
    ![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]]
  have key : ∀ x y : Equiv.Perm (Fin 4), (∀ i j : Fin 4, M (x i) (x j) = M i j) →
      (∀ i j : Fin 4, M (y i) (y j) = M i j) →
      x * x = 1 → y * y = 1 → x * y = y * x → x = 1 ∨ y = 1 ∨ x = y := by
    decide +kernel
  have hc : ∀ i j : Fin 4, Tag.D4.cartan i j = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  exact key x y (fun i j => by rw [← hc, ← hc]; exact hx i j)
    (fun i j => by rw [← hc, ← hc]; exact hy i j) hx2 hy2 hxy

private theorem card_le_two_of_cartan {R : Subgroup (Equiv.Perm (Fin Tag.D4.rank))}
    (hR : ∀ x ∈ R, ∀ i j, Tag.D4.cartan (x i) (x j) = Tag.D4.cartan i j)
    (hR2 : ∀ x ∈ R, x * x = 1) (hRc : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x) : Nat.card R ≤ 2 := by
  classical
  rcases Subgroup.bot_or_exists_ne_one R with hbot | ⟨x₀, hx₀R, hx₀⟩
  · simp [hbot]
  · have hsub : (R : Set (Equiv.Perm (Fin Tag.D4.rank))) ⊆ {1, x₀} := by
      intro x hx
      rcases eq_one_or_eq_one_or_eq_of_cartan (hR x hx) (hR x₀ hx₀R) (hR2 x hx)
        (hR2 x₀ hx₀R) (hRc x hx x₀ hx₀R) with h | h | h
      · exact Or.inl h
      · exact absurd h hx₀
      · exact Or.inr h
    have hmono : Nat.card R ≤
        Nat.card ({1, x₀} : Set (Equiv.Perm (Fin Tag.D4.rank))) :=
      Nat.card_mono (Set.toFinite _) hsub
    have hpair : Nat.card ({1, x₀} : Set (Equiv.Perm (Fin Tag.D4.rank))) = 2 := by
      rw [Nat.card_coe_set_eq, Set.ncard_pair (a := 1) (b := x₀) hx₀.symm]
    exact hmono.trans (le_of_eq hpair)

private theorem card_le_of_ringEquiv_sq {K : Type} [Field K] [Finite K] {R : Subgroup (K ≃+* K)}
    (hR2 : ∀ σ ∈ R, σ * σ = 1) :
    Nat.card R ≤ 2 ∧ ∀ f : ℕ, Odd f → Nat.card K = 2 ^ f → Nat.card R ≤ 1 := by
  have hcyc : IsCyclic (K ≃+* K) := ringAut_isCyclic
  have hcycR : IsCyclic R := Subgroup.isCyclic R
  have hneR : Nonempty R := ⟨1⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := R)
  have hg2 : g ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (by simpa using hR2 g.1 g.2)
  have hle : Nat.card R ≤ 2 := by
    rw [← hg]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hg2)
  refine ⟨hle, fun f hf hK => ?_⟩
  obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic (p := 2) (n := f) (by norm_num) K hK
  have hdvd : Nat.card R ∣ f := by
    have h := Subgroup.card_subgroup_dvd_card R
    rwa [hcard] at h
  have hne : Nat.card R ≠ 2 := Odd.ne_two_of_dvd_nat hf hdvd
  have hpos : 0 < Nat.card R := Nat.card_pos
  omega

section GraphPart

variable {K : Type} [Field K] [Finite K]

private theorem exists_conj_mul_mem_unipotentPairAut (α : MulAut (adjointGroup Tag.D4 K)) :
    ∃ (c : adjointGroup Tag.D4 K) (β : MulAut (adjointGroup Tag.D4 K)),
      β ∈ unipotentPairAut Tag.D4 K ∧ α = MulAut.conj c * β := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  exact ⟨c, β, ⟨hU, hV⟩, rfl⟩

omit [Finite K] in
private theorem simplePermHom_conj_eq_one {h : adjointGroup Tag.D4 K}
    (hA : MulAut.conj h ∈ unipotentPairAut Tag.D4 K) :
    simplePermHom Tag.D4 K ⟨MulAut.conj h, hA⟩ = 1 := by
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag hA
  refine perm_map_simple_unique (α := MulAut.conj h)
    (fun i => (simplePerm_spec (τ := Tag.D4) (K := K) ⟨MulAut.conj h, hA⟩ i).1) (fun i => ?_)
  rw [hb, map_simplePosSubgroup_exactNormalAut b 1 0 i]
  rfl

omit [Finite K] in
private theorem simplePermHom_eq_of_conj_mul_eq {c c' : adjointGroup Tag.D4 K}
    {β β' : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ unipotentPairAut Tag.D4 K)
    (hβ' : β' ∈ unipotentPairAut Tag.D4 K) (h : MulAut.conj c * β = MulAut.conj c' * β') :
    simplePermHom Tag.D4 K ⟨β, hβ⟩ = simplePermHom Tag.D4 K ⟨β', hβ'⟩ := by
  have hkey : (MulAut.conj c')⁻¹ * MulAut.conj c = β' * β⁻¹ := by
    have := congrArg (fun x => (MulAut.conj c')⁻¹ * x * β⁻¹) h
    simpa [mul_assoc] using this
  have hA : MulAut.conj (c'⁻¹ * c) ∈ unipotentPairAut Tag.D4 K := by
    rw [map_mul, map_inv, hkey]
    exact mul_mem hβ' (inv_mem hβ)
  have hsub : (⟨β', hβ'⟩ : unipotentPairAut Tag.D4 K) =
      ⟨MulAut.conj (c'⁻¹ * c), hA⟩ * ⟨β, hβ⟩ := by
    refine Subtype.ext ?_
    show β' = MulAut.conj (c'⁻¹ * c) * β
    rw [map_mul, map_inv, hkey]
    group
  rw [hsub, map_mul, simplePermHom_conj_eq_one hA, one_mul]

private noncomputable def graphPartFn (α : MulAut (adjointGroup Tag.D4 K)) :
    Equiv.Perm (Fin Tag.D4.rank) :=
  simplePermHom Tag.D4 K ⟨(exists_conj_mul_mem_unipotentPairAut α).choose_spec.choose,
    (exists_conj_mul_mem_unipotentPairAut α).choose_spec.choose_spec.1⟩

private theorem graphPartFn_eq {α : MulAut (adjointGroup Tag.D4 K)} {c : adjointGroup Tag.D4 K}
    {β : MulAut (adjointGroup Tag.D4 K)} (hβ : β ∈ unipotentPairAut Tag.D4 K)
    (h : α = MulAut.conj c * β) : graphPartFn α = simplePermHom Tag.D4 K ⟨β, hβ⟩ :=
  simplePermHom_eq_of_conj_mul_eq
    (exists_conj_mul_mem_unipotentPairAut α).choose_spec.choose_spec.1 hβ
    ((exists_conj_mul_mem_unipotentPairAut α).choose_spec.choose_spec.2.symm.trans h)

private noncomputable def graphPart :
    MulAut (adjointGroup Tag.D4 K) →* Equiv.Perm (Fin Tag.D4.rank) where
  toFun := graphPartFn
  map_one' := by
    rw [graphPartFn_eq (β := 1) (c := 1) (one_mem _) (by simp)]
    exact map_one (simplePermHom Tag.D4 K)
  map_mul' := by
    intro α α'
    obtain ⟨c, β, hβ, hα⟩ := exists_conj_mul_mem_unipotentPairAut α
    obtain ⟨c', β', hβ', hα'⟩ := exists_conj_mul_mem_unipotentPairAut α'
    have hmul : α * α' = MulAut.conj (c * β c') * (β * β') := by
      rw [hα, hα']
      calc MulAut.conj c * β * (MulAut.conj c' * β')
          = MulAut.conj c * (β * MulAut.conj c') * β' := by group
        _ = MulAut.conj c * (MulAut.conj (β c') * β) * β' := by
            rw [CFSG.HardMathSupport.Lang.D4Three.mul_conj_eq]
        _ = MulAut.conj (c * β c') * (β * β') := by rw [map_mul]; group
    rw [graphPartFn_eq hβ hα, graphPartFn_eq hβ' hα',
      graphPartFn_eq (mul_mem hβ hβ') hmul]
    exact map_mul (simplePermHom Tag.D4 K) ⟨β, hβ⟩ ⟨β', hβ'⟩

private theorem graphPart_conj (g : adjointGroup Tag.D4 K) : graphPart (MulAut.conj g) = 1 := by
  rw [show graphPart (MulAut.conj g) = simplePermHom Tag.D4 K ⟨1, one_mem _⟩ from
    graphPartFn_eq (β := 1) (c := g) (one_mem _) (by simp)]
  exact map_one (simplePermHom Tag.D4 K)

private theorem cartan_graphPart (α : MulAut (adjointGroup Tag.D4 K)) (i j : Fin Tag.D4.rank) :
    Tag.D4.cartan (graphPart α i) (graphPart α j) = Tag.D4.cartan i j := by
  obtain ⟨c, β, hβ, hα⟩ := exists_conj_mul_mem_unipotentPairAut α
  have hπ : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
      simplePosSubgroup Tag.D4 K (simplePermHom Tag.D4 K ⟨β, hβ⟩ i) := fun i =>
    (simplePerm_spec ⟨β, hβ⟩ i).1
  change Tag.D4.cartan (graphPartFn α i) (graphPartFn α j) = Tag.D4.cartan i j
  rw [graphPartFn_eq hβ hα]
  exact CFSG.HardMathSupport.Lang.D4Three.cartan_perm_eq_D4 hπ i j

private theorem exists_eq_conj_of_graphPart_eq_one [CharP K 2]
    {α : MulAut (adjointGroup Tag.D4 K)} (hg : graphPart α = 1)
    (hf : CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart α = 1) :
    ∃ g : adjointGroup Tag.D4 K, α = MulAut.conj g := by
  obtain ⟨c, β, hβ, hα⟩ := exists_conj_mul_mem_unipotentPairAut α
  have hpermH : simplePermHom Tag.D4 K ⟨β, hβ⟩ = 1 := by
    rw [← graphPartFn_eq hβ hα]
    exact hg
  have hperm : simplePerm Tag.D4 K ⟨β, hβ⟩ = 1 := hpermH
  have hmap : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ 0) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((CFSG.HardMathSupport.Lang.D4Three.d4Rho ^ 0) i) := by
    intro i
    have hsp := simplePerm_spec ⟨β, hβ⟩ i
    rw [hperm] at hsp
    simpa using hsp
  obtain ⟨a, σ, hβeq⟩ := CFSG.HardMathSupport.Lang.D4Three.exists_normalAut_mul_graph
    (ε := 0) hmap
  have hσ : σ = 1 := by
    have h := hf
    rw [hα, map_mul, CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart_conj,
      one_mul, hβeq, CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart_normalForm] at h
    exact h
  rw [hσ, CFSG.HardMathSupport.Lang.E6Descent.d4Graph_zero, mul_one] at hβeq
  obtain ⟨d, hd⟩ : ∃ d : adjointGroup Tag.D4 K,
      exactNormalAut Tag.D4 K a 1 0 = MulAut.conj d :=
    ⟨⟨rootDiagUnit Tag.D4 a,
        CFSG.LieType.ChevTwo.Semi.rootDiagUnit_mem_adjointGroup_D4 (ringChar.eq K 2) a⟩,
      exactNormalAut_diag_eq_conj a
        (CFSG.LieType.ChevTwo.Semi.rootDiagUnit_mem_adjointGroup_D4 (ringChar.eq K 2) a)⟩
  refine ⟨c * d, ?_⟩
  rw [hα, hβeq, hd, map_mul]

end GraphPart

private theorem nonempty_adjointGroup_equiv {K : Type} [Field K]
    [Finite K] [CharP K 2] :
    Nonempty (adjointGroup .D4 K ≃* orthElementaryGroup (quadPlus 4 K)) := by
  obtain ⟨Φ, -⟩ := CFSG.StandardType.TriBridge.d4_adjoint_equiv_om8 (K := K)
  exact ⟨Φ.trans ((CFSG.ComponentClassification.CatalogueBOrthogonalPointReindexCovariance.statedDerivedReindexEquiv
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.plusIndexEquiv 4) (quadPlus 4 K)
    (coe_quadPlus 4 K)).symm.trans
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel.plusDerivedEquiv 4 K
      (by norm_num)))⟩

private theorem card_le_mul_card_inf
    {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (L E : Subgroup (MulAut V))
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) (m : ℕ)
    (hm : ∀ R : Subgroup (K ≃+* K), (∀ σ ∈ R, σ * σ = 1) → Nat.card R ≤ m) :
    Nat.card E ≤ 2 * m * Nat.card (E ⊓ L : Subgroup (MulAut V)) := by
  classical
  have : Finite (MulAut V) :=
    Finite.of_injective (fun e : MulAut V => (e : V → V)) fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨η⟩ := nonempty_adjointGroup_equiv (K := K)
  let ψ : adjointGroup .D4 K ≃* ↥L := η.trans θ.symm
  let Ψ : ↥E →* MulAut (adjointGroup .D4 K) :=
    { toFun := fun e => (ψ.trans (X1.conjAut L (hEN e.2))).trans ψ.symm
      map_one' := by
        apply MulEquiv.ext
        intro x
        change ψ.symm (X1.conjAut L (hEN (1 : ↥E).2) (ψ x)) = x
        have h1 : X1.conjAut L (hEN (1 : ↥E).2) (ψ x) = ψ x := by
          apply Subtype.ext
          simp [X1.coe_conjAut]
        rw [h1, MulEquiv.symm_apply_apply]
      map_mul' := by
        intro e₁ e₂
        apply MulEquiv.ext
        intro x
        simp only [MulAut.mul_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        apply ψ.injective
        simp only [MulEquiv.apply_symm_apply]
        apply Subtype.ext
        simp only [X1.coe_conjAut, Subgroup.coe_mul]
        group }
  let Φ : ↥E →* Equiv.Perm (Fin Tag.D4.rank) × (K ≃+* K) :=
    (MonoidHom.prod (graphPart (K := K))
      (CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart (K := K))).comp Ψ
  have hker : Φ.ker = (E ⊓ L).subgroupOf E := by
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro he
      have hpair : (graphPart (Ψ e),
          CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart (Ψ e)) =
          ((1 : Equiv.Perm (Fin Tag.D4.rank)), (1 : K ≃+* K)) := by
        have h := he
        simp only [Φ, MonoidHom.comp_apply, MonoidHom.prod_apply] at h
        simpa using h
      have hge : graphPart (Ψ e) = 1 := by
        have := congrArg Prod.fst hpair
        simpa using this
      have hfe : CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart (Ψ e) = 1 := by
        have := congrArg Prod.snd hpair
        simpa using this
      obtain ⟨g, hg⟩ := exists_eq_conj_of_graphPart_eq_one hge hfe
      have hl : ∀ x : ↥L, X1.conjAut L (hEN e.2) x = ψ g * x * (ψ g)⁻¹ := by
        intro x
        have hx : ψ (Ψ e (ψ.symm x)) = X1.conjAut L (hEN e.2) x := by
          change ψ ((ψ.trans (X1.conjAut L (hEN e.2))).trans ψ.symm (ψ.symm x)) =
            X1.conjAut L (hEN e.2) x
          simp only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
        calc X1.conjAut L (hEN e.2) x = ψ (Ψ e (ψ.symm x)) := hx.symm
          _ = ψ (MulAut.conj g (ψ.symm x)) := by rw [hg]
          _ = ψ g * x * (ψ g)⁻¹ := by
              rw [MulAut.conj_apply]
              simp only [map_mul, map_inv, MulEquiv.apply_symm_apply]
      have he2 : (e : MulAut V) * (e : MulAut V) = 1 := by
        have h := hEel.2 (e : MulAut V) e.2
        simpa [pow_two] using h
      exact ⟨e.2, mem_of_conjAut_eq_conj hV hirr (hEN e.2) he2 (ψ g) hl⟩
    · rintro he
      have heL : (e : MulAut V) ∈ L := (Subgroup.mem_inf.1 he).2
      have hΨ : Ψ e = MulAut.conj (ψ.symm ⟨(e : MulAut V), heL⟩) := by
        apply MulEquiv.ext
        intro y
        change ψ.symm (X1.conjAut L (hEN e.2) (ψ y)) =
          MulAut.conj (ψ.symm ⟨(e : MulAut V), heL⟩) y
        have hstep : X1.conjAut L (hEN e.2) (ψ y) =
            ⟨(e : MulAut V), heL⟩ * ψ y * ⟨(e : MulAut V), heL⟩⁻¹ := rfl
        rw [hstep, MulAut.conj_apply]
        simp only [map_mul, map_inv, MulEquiv.symm_apply_apply]
      have h1 : (graphPart (Ψ e),
          CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart (Ψ e)) =
          ((1 : Equiv.Perm (Fin Tag.D4.rank)), (1 : K ≃+* K)) := by
        rw [hΨ, graphPart_conj, CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart_conj]
      simpa [Φ, MonoidHom.comp_apply, MonoidHom.prod_apply] using h1
  have hkercard : Nat.card Φ.ker = Nat.card ↥(E ⊓ L) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : E ⊓ L ≤ E)).toEquiv
  have hRg : Nat.card (Φ.range.map (MonoidHom.fst _ _)) ≤ 2 := by
    refine card_le_two_of_cartan ?_ ?_ ?_
    · intro x hx i j
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hy
      rw [← he]
      exact cartan_graphPart (Ψ e) i j
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hy
      rw [← he]
      have hee : (e : ↥E) * e = 1 := by
        apply Subtype.ext
        have h := hEel.2 (e : MulAut V) e.2
        simpa [pow_two] using h
      change graphPart (Ψ e) * graphPart (Ψ e) = 1
      rw [← map_mul, ← map_mul, hee, map_one, map_one]
    · intro x hx y hy
      obtain ⟨y₁, hy₁, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨y₂, hy₂, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨e₁, he₁⟩ := MonoidHom.mem_range.mp hy₁
      obtain ⟨e₂, he₂⟩ := MonoidHom.mem_range.mp hy₂
      rw [← he₁, ← he₂]
      have hc : (e₁ : ↥E) * e₂ = e₂ * e₁ := by
        apply Subtype.ext
        exact hEel.1 (e₁ : MulAut V) e₁.2 (e₂ : MulAut V) e₂.2
      change graphPart (Ψ e₁) * graphPart (Ψ e₂) = graphPart (Ψ e₂) * graphPart (Ψ e₁)
      rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hc]
  have hRf : Nat.card (Φ.range.map (MonoidHom.snd _ _)) ≤ m := by
    apply hm
    intro σ hσ
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hσ
    obtain ⟨e, he⟩ := MonoidHom.mem_range.mp hy
    rw [← he]
    have hee : (e : ↥E) * e = 1 := by
      apply Subtype.ext
      have h := hEel.2 (e : MulAut V) e.2
      simpa [pow_two] using h
    change CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart (Ψ e) *
      CFSG.HardMathSupport.Dickson.Sec6.I1431.FieldPart.fieldPart (Ψ e) = 1
    rw [← map_mul, ← map_mul, hee, map_one, map_one]
  have hle : Φ.range ≤
      (Φ.range.map (MonoidHom.fst _ _)).prod (Φ.range.map (MonoidHom.snd _ _)) := by
    intro x hx
    rw [Subgroup.mem_prod]
    exact ⟨Subgroup.mem_map_of_mem _ hx, Subgroup.mem_map_of_mem _ hx⟩
  have hprod : Nat.card ↥((Φ.range.map (MonoidHom.fst _ _)).prod
        (Φ.range.map (MonoidHom.snd _ _))) =
      Nat.card (Φ.range.map (MonoidHom.fst _ _)) *
        Nat.card (Φ.range.map (MonoidHom.snd _ _)) := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv
  have hrange : Nat.card Φ.range ≤ 2 * m := by
    calc Nat.card Φ.range
        ≤ Nat.card ↥((Φ.range.map (MonoidHom.fst _ _)).prod
            (Φ.range.map (MonoidHom.snd _ _))) := Subgroup.card_le_of_le hle
      _ = Nat.card (Φ.range.map (MonoidHom.fst _ _)) *
            Nat.card (Φ.range.map (MonoidHom.snd _ _)) := hprod
      _ ≤ 2 * m := Nat.mul_le_mul hRg hRf
  have hcard := Subgroup.card_ker_mul_card_range Φ
  calc Nat.card E = Nat.card Φ.ker * Nat.card Φ.range := hcard.symm
    _ = Nat.card ↥(E ⊓ L) * Nat.card Φ.range := by rw [hkercard]
    _ ≤ Nat.card ↥(E ⊓ L) * (2 * m) := Nat.mul_le_mul_left _ hrange
    _ = 2 * m * Nat.card ↥(E ⊓ L) := Nat.mul_comm _ _

theorem card_le_four_mul_card_inf
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) (L E : Subgroup (MulAut V))
    (θ : L ≃* orthElementaryGroup (quadPlus 4 K)) (hirr : X1.IsIrrOn L)
    (hEN : E ≤ Subgroup.normalizer (L : Set (MulAut V))) (hEel : IsElemAbelian2 E) :
    Nat.card E ≤ 4 * Nat.card (E ⊓ L : Subgroup (MulAut V)) := by
  have h := card_le_mul_card_inf hV L E θ hirr hEN hEel 2 fun R hR =>
    (card_le_of_ringEquiv_sq hR).1
  simpa using h

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
