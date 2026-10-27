module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthBig
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthClifford
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalOrthList

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CliffordAlgebra QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution.Models.OrthogonalPairs (neg_one_ne_one)

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Clifford

theorem prod_map_ι_mul_prod_map_ι_of_orth {x y : List V} (h : ∀ a ∈ x, ∀ b ∈ y, Q.IsOrtho a b) :
    (x.map (ι Q)).prod * (y.map (ι Q)).prod =
      ((-1 : F) ^ (x.length * y.length)) • ((y.map (ι Q)).prod * (x.map (ι Q)).prod) := by
  induction y with
  | nil => simp
  | cons b y ih =>
    have hb : ∀ a ∈ x, Q.IsOrtho a b := fun a ha => h a ha b List.mem_cons_self
    have hy : ∀ a ∈ x, ∀ b' ∈ y, Q.IsOrtho a b' := fun a ha b' hb' =>
      h a ha b' (List.mem_cons_of_mem _ hb')
    have hxb := prod_map_ι_mul_ι_of_forall_isOrtho (Q := Q) hb
    calc (x.map (ι Q)).prod * ((b :: y).map (ι Q)).prod
        = ((x.map (ι Q)).prod * ι Q b) * (y.map (ι Q)).prod := by
          simp only [List.map_cons, List.prod_cons, mul_assoc]
      _ = ((-1 : F) ^ x.length) • (ι Q b * ((x.map (ι Q)).prod * (y.map (ι Q)).prod)) := by
          rw [hxb, smul_mul_assoc, mul_assoc]
      _ = ((-1 : F) ^ x.length) • (ι Q b * (((-1 : F) ^ (x.length * y.length)) •
            ((y.map (ι Q)).prod * (x.map (ι Q)).prod))) := by rw [ih hy]
      _ = ((-1 : F) ^ (x.length * (b :: y).length)) •
            (((b :: y).map (ι Q)).prod * (x.map (ι Q)).prod) := by
          rw [mul_smul_comm, smul_smul, List.length_cons, mul_add, mul_one, pow_add, mul_comm]
          simp only [List.map_cons, List.prod_cons, mul_assoc]

end Clifford

section Parity

omit [Field F] in
theorem polarNondegOn_of_sup_orth {F V : Type} [Field F] [AddCommGroup V] [Module F V]
    {Q : QuadraticForm F V} {W U U' : Submodule F V} (hW : PolarNondegOn Q W)
    (hsp : W = U ⊔ U') (horth : ∀ x ∈ U, ∀ y ∈ U', polar Q x y = 0) : PolarNondegOn Q U := by
  intro x hx h
  refine hW x (hsp ▸ Submodule.mem_sup_left hx) fun w hw => ?_
  rw [hsp] at hw
  obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hw
  rw [polar_add_right, h u hu, horth x hx u' hu', add_zero]

theorem isOrtho_of_polar_eq_zero {a b : V} (h : polar Q a b = 0) : Q.IsOrtho a b :=
  isOrtho_polarBilin.mp (by simpa [polarBilin_apply_apply] using h)

theorem even_of_parities {a b c : ℕ} (h₁ : Even (a + b)) (h₂ : Even (a + c))
    (h : Even (b * a + (c * a + c * b))) : Even a := by
  simp only [Nat.even_add, Nat.even_mul] at h₁ h₂ h ⊢
  tauto

variable [FiniteDimensional F V] [Invertible (2 : F)]

theorem even_finrank_inf_minusSp_of_spin_commute (hQ : (polarBilin Q).Nondegenerate)
    {z₁ z₂ : spinGroup Q} (hz : z₁ * z₂ = z₂ * z₁)
    (hii₁ : spinAction Q z₁ * spinAction Q z₁ = 1) (hii₂ : spinAction Q z₂ * spinAction Q z₂ = 1)
    (he₁ : Even (Module.finrank F (minusSp (spinAction Q z₁))))
    (he₂ : Even (Module.finrank F (minusSp (spinAction Q z₂)))) :
    Even (Module.finrank F ↥(minusSp (spinAction Q z₁) ⊓ minusSp (spinAction Q z₂))) := by
  have h2 : (2 : F) ≠ 0 := (isUnit_of_invertible (2 : F)).ne_zero
  have hQnd : Q.Nondegenerate := QuadraticMap.nondegenerate_polar_iff.mp hQ
  generalize hi₁ : spinAction Q z₁ = i₁ at hii₁ he₁ ⊢
  generalize hi₂ : spinAction Q z₂ = i₂ at hii₂ he₂ ⊢
  have hO₁ : i₁ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hi₁ ▸ TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ z₁ v
  have hO₂ : i₂ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    hi₂ ▸ TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => map_spinAction _ z₂ v
  have hcomm : i₂ * i₁ = i₁ * i₂ := by
    rw [← hi₁, ← hi₂, ← map_mul, ← map_mul, hz]
  set A := minusSp i₁ ⊓ minusSp i₂ with hA
  set B := minusSp i₁ ⊓ plusSp i₂ with hB
  set C := plusSp i₁ ⊓ minusSp i₂ with hC
  have hAB : ∀ x ∈ A, ∀ y ∈ B, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]
    exact polar_plusSp_minusSp h2 hO₂ hy.2 hx.2
  have hAC : ∀ x ∈ A, ∀ y ∈ C, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]
    exact polar_plusSp_minusSp h2 hO₁ hy.1 hx.1
  have hBC : ∀ x ∈ B, ∀ y ∈ C, polar Q x y = 0 := fun x hx y hy => by
    rw [polar_comm]
    exact polar_plusSp_minusSp h2 hO₁ hy.1 hx.1
  have hdec₁ : minusSp i₁ = A ⊔ B := by
    refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
    intro x hx
    have hx' : i₂ x ∈ minusSp i₁ := map_mem_minusSp hcomm hx
    have hM : projM i₂ x ∈ A := by
      refine ⟨?_, projM_mem hii₂ x⟩
      rw [projM_apply]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx hx')
    have hP : projP i₂ x ∈ B := by
      refine ⟨?_, projP_mem hii₂ x⟩
      rw [projP_apply]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx hx')
    rw [← projP_add_projM h2 (i := i₂) x]
    exact Submodule.add_mem _ (Submodule.mem_sup_right hP) (Submodule.mem_sup_left hM)
  have hdec₂ : minusSp i₂ = A ⊔ C := by
    refine le_antisymm ?_ (sup_le inf_le_right inf_le_right)
    intro x hx
    have hx' : i₁ x ∈ minusSp i₂ := map_mem_minusSp hcomm.symm hx
    have hM : projM i₁ x ∈ A := by
      refine ⟨projM_mem hii₁ x, ?_⟩
      rw [projM_apply]
      exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx hx')
    have hP : projP i₁ x ∈ C := by
      refine ⟨projP_mem hii₁ x, ?_⟩
      rw [projP_apply]
      exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx hx')
    rw [← projP_add_projM h2 (i := i₁) x]
    exact Submodule.add_mem _ (Submodule.mem_sup_right hP) (Submodule.mem_sup_left hM)
  have hdisAB : Disjoint A B := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.mp (isCompl_plusSp_minusSp h2 hii₂).disjoint x hx'.2 hx.2
  have hdisAC : Disjoint A C := by
    rw [Submodule.disjoint_def]
    intro x hx hx'
    exact Submodule.disjoint_def.mp (isCompl_plusSp_minusSp h2 hii₁).disjoint x hx'.1 hx.1
  have hfr₁ : Module.finrank F (minusSp i₁) = Module.finrank F A + Module.finrank F B := by
    have := Submodule.finrank_sup_add_finrank_inf_eq A B
    rw [hdisAB.eq_bot, finrank_bot, add_zero, ← hdec₁] at this
    exact this
  have hfr₂ : Module.finrank F (minusSp i₂) = Module.finrank F A + Module.finrank F C := by
    have := Submodule.finrank_sup_add_finrank_inf_eq A C
    rw [hdisAC.eq_bot, finrank_bot, add_zero, ← hdec₂] at this
    exact this
  have hnd₁ := polarNondegOn_minusSp h2 hQ hO₁ hii₁
  have hnd₂ := polarNondegOn_minusSp h2 hQ hO₂ hii₂
  have hndA : PolarNondegOn Q A := polarNondegOn_of_sup_orth hnd₁ hdec₁ hAB
  have hndB : PolarNondegOn Q B := polarNondegOn_of_sup_orth hnd₁ (hdec₁.trans (sup_comm _ _))
    fun x hx y hy => by rw [polar_comm]; exact hAB y hy x hx
  have hndC : PolarNondegOn Q C := polarNondegOn_of_sup_orth hnd₂ (hdec₂.trans (sup_comm _ _))
    fun x hx y hy => by rw [polar_comm]; exact hAC y hy x hx
  have hres : ∀ W : Submodule F V, PolarNondegOn Q W → (Q.restrict W).Nondegenerate :=
    fun W hW => QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hW)
  obtain ⟨lA, hlAlen, hlAo, hlAq, hlAs, -⟩ := exists_orthogonal_list_restrict Q A (hres A hndA)
  obtain ⟨lB, hlBlen, hlBo, hlBq, hlBs, -⟩ := exists_orthogonal_list_restrict Q B (hres B hndB)
  obtain ⟨lC, hlClen, hlCo, hlCq, hlCs, -⟩ := exists_orthogonal_list_restrict Q C (hres C hndC)
  have hmem : ∀ {W : Submodule F V} {l : List V}, Submodule.span F {x : V | x ∈ l} = W →
      ∀ x ∈ l, x ∈ W := fun hs x hx => hs ▸ Submodule.subset_span hx
  have oAB : ∀ a ∈ lA, ∀ b ∈ lB, Q.IsOrtho a b := fun a ha b hb =>
    isOrtho_of_polar_eq_zero (hAB a (hmem hlAs a ha) b (hmem hlBs b hb))
  have oAC : ∀ a ∈ lA, ∀ c ∈ lC, Q.IsOrtho a c := fun a ha c hc =>
    isOrtho_of_polar_eq_zero (hAC a (hmem hlAs a ha) c (hmem hlCs c hc))
  have oBC : ∀ b ∈ lB, ∀ c ∈ lC, Q.IsOrtho b c := fun b hb c hc =>
    isOrtho_of_polar_eq_zero (hBC b (hmem hlBs b hb) c (hmem hlCs c hc))
  have hl₁o : (lA ++ lB).Pairwise Q.IsOrtho := List.pairwise_append.mpr ⟨hlAo, hlBo, oAB⟩
  have hl₂o : (lA ++ lC).Pairwise Q.IsOrtho := List.pairwise_append.mpr ⟨hlAo, hlCo, oAC⟩
  have hl₁len : Even (lA ++ lB).length := by
    rw [List.length_append, hlAlen, hlBlen, ← hfr₁]; exact he₁
  have hl₂len : Even (lA ++ lC).length := by
    rw [List.length_append, hlAlen, hlClen, ← hfr₂]; exact he₂
  have hl₁span : Submodule.span F {x : V | x ∈ lA ++ lB} = minusSp i₁ := by
    have : {x : V | x ∈ lA ++ lB} = {x | x ∈ lA} ∪ {x | x ∈ lB} := by ext; simp
    rw [this, Submodule.span_union, hlAs, hlBs, hdec₁]
  have hl₂span : Submodule.span F {x : V | x ∈ lA ++ lC} = minusSp i₂ := by
    have : {x : V | x ∈ lA ++ lC} = {x | x ∈ lA} ∪ {x | x ∈ lC} := by ext; simp
    rw [this, Submodule.span_union, hlAs, hlCs, hdec₂]
  have hl₁q : ∀ x ∈ lA ++ lB, Q x ≠ 0 := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    exacts [hlAq x h, hlBq x h]
  have hl₂q : ∀ x ∈ lA ++ lC, Q x ≠ 0 := fun x hx => by
    rcases List.mem_append.mp hx with h | h
    exacts [hlAq x h, hlCq x h]
  obtain ⟨c₁, hc₁⟩ := exists_eq_smul_prod_map_ι hQnd hO₁ hii₁ hi₁ hl₁o hl₁len hl₁span hl₁q
  obtain ⟨c₂, hc₂⟩ := exists_eq_smul_prod_map_ι hQnd hO₂ hii₂ hi₂ hl₂o hl₂len hl₂span hl₂q
  have hne : ∀ (z : spinGroup Q) (c : F) (ω : CliffordAlgebra Q),
      (z : CliffordAlgebra Q) = c • ω → c ≠ 0 := by
    rintro z c ω h rfl
    have := spinGroup.star_mul_self_of_mem z.2
    rw [h, zero_smul, star_zero, zero_mul] at this
    exact zero_ne_one this
  have hc₁0 := hne z₁ c₁ _ hc₁
  have hc₂0 := hne z₂ c₂ _ hc₂
  have hzCl : (z₁ : CliffordAlgebra Q) * z₂ = z₂ * z₁ := by
    have := congrArg (fun x : spinGroup Q => (x : CliffordAlgebra Q)) hz
    simpa using this
  set ωA := (lA.map (ι Q)).prod with hωA
  set ωB := (lB.map (ι Q)).prod with hωB
  set ωC := (lC.map (ι Q)).prod with hωC
  have hω₁ : ((lA ++ lB).map (ι Q)).prod = ωA * ωB := by rw [List.map_append, List.prod_append]
  have hω₂ : ((lA ++ lC).map (ι Q)).prod = ωA * ωC := by rw [List.map_append, List.prod_append]
  have hBA : ωB * ωA = ((-1 : F) ^ (lB.length * lA.length)) • (ωA * ωB) :=
    prod_map_ι_mul_prod_map_ι_of_orth fun b hb a ha => (oAB a ha b hb).symm
  have hCA : ωC * ωA = ((-1 : F) ^ (lC.length * lA.length)) • (ωA * ωC) :=
    prod_map_ι_mul_prod_map_ι_of_orth fun c hc a ha => (oAC a ha c hc).symm
  have hCB : ωC * ωB = ((-1 : F) ^ (lC.length * lB.length)) • (ωB * ωC) :=
    prod_map_ι_mul_prod_map_ι_of_orth fun c hc b hb => (oBC b hb c hc).symm
  set U := (ωA * ωA) * (ωB * ωC) with hU
  have e₁ : (ωA * ωB) * (ωA * ωC) = ((-1 : F) ^ (lB.length * lA.length)) • U := by
    calc (ωA * ωB) * (ωA * ωC) = ωA * ((ωB * ωA) * ωC) := by simp only [mul_assoc]
      _ = ωA * ((((-1 : F) ^ (lB.length * lA.length)) • (ωA * ωB)) * ωC) := by rw [hBA]
      _ = ((-1 : F) ^ (lB.length * lA.length)) • U := by
          rw [smul_mul_assoc, mul_smul_comm, hU]
          simp only [mul_assoc]
  have e₂ : (ωA * ωC) * (ωA * ωB) =
      ((-1 : F) ^ (lC.length * lA.length + lC.length * lB.length)) • U := by
    calc (ωA * ωC) * (ωA * ωB) = ωA * ((ωC * ωA) * ωB) := by simp only [mul_assoc]
      _ = ωA * ((((-1 : F) ^ (lC.length * lA.length)) • (ωA * ωC)) * ωB) := by rw [hCA]
      _ = ((-1 : F) ^ (lC.length * lA.length)) • ((ωA * ωA) * (ωC * ωB)) := by
          rw [smul_mul_assoc, mul_smul_comm]
          simp only [mul_assoc]
      _ = ((-1 : F) ^ (lC.length * lA.length)) •
            ((ωA * ωA) * (((-1 : F) ^ (lC.length * lB.length)) • (ωB * ωC))) := by rw [hCB]
      _ = ((-1 : F) ^ (lC.length * lA.length + lC.length * lB.length)) • U := by
          rw [mul_smul_comm, smul_smul, ← pow_add, hU]
  have hprod_ne : ∀ l : List V, (∀ x ∈ l, Q x ≠ 0) → (l.map Q).prod ≠ 0 := fun l hl => by
    rw [Ne, List.prod_eq_zero_iff]
    intro h0
    obtain ⟨x, hx, hx0⟩ := List.mem_map.mp h0
    exact hl x hx hx0
  have hωAA : ωA * ωA = algebraMap F (CliffordAlgebra Q)
      (((-1 : F) ^ lA.length.choose 2) * (lA.map Q).prod) := prod_map_ι_sq_scalar hlAo
  have hUA : IsUnit (ωA * ωA) := by
    rw [hωAA]
    exact (isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (hprod_ne lA hlAq))).map _
  have hUB : IsUnit ωB := isUnit_prod_map_ι (isUnit_iff_ne_zero.mpr (hprod_ne lB hlBq))
  have hUC : IsUnit ωC := isUnit_prod_map_ι (isUnit_iff_ne_zero.mpr (hprod_ne lC hlCq))
  have hUU : IsUnit U := hUA.mul (hUB.mul hUC)
  have hkey : (c₁ * c₂) • (ωA * ωB * (ωA * ωC)) = (c₁ * c₂) • (ωA * ωC * (ωA * ωB)) := by
    have := hzCl
    rw [hc₁, hc₂, hω₁, hω₂, smul_mul_smul_comm, smul_mul_smul_comm, mul_comm c₂ c₁] at this
    exact this
  have hω : ωA * ωB * (ωA * ωC) = ωA * ωC * (ωA * ωB) :=
    smul_right_injective _ (mul_ne_zero hc₁0 hc₂0) hkey
  rw [e₁, e₂] at hω
  have hsc : (-1 : F) ^ (lB.length * lA.length) =
      (-1 : F) ^ (lC.length * lA.length + lC.length * lB.length) := by
    have h1 : algebraMap F (CliffordAlgebra Q) ((-1 : F) ^ (lB.length * lA.length)) * U =
        algebraMap F (CliffordAlgebra Q)
          ((-1 : F) ^ (lC.length * lA.length + lC.length * lB.length)) * U := by
      simpa [Algebra.smul_def] using hω
    exact algebraMap_injective' Q ((hUU.mul_left_inj).mp h1)
  have hev : Even (lB.length * lA.length +
      (lC.length * lA.length + lC.length * lB.length)) := by
    have h1 : (-1 : F) ^ (lB.length * lA.length +
        (lC.length * lA.length + lC.length * lB.length)) = 1 := by
      rw [pow_add, ← hsc, ← pow_add, ← two_mul, pow_mul]
      simp
    exact (neg_one_pow_eq_one_iff_even (neg_one_ne_one h2)).mp h1
  rw [← hlAlen]
  exact even_of_parities (by simpa [List.length_append] using hl₁len)
    (by simpa [List.length_append] using hl₂len) hev

end Parity

end CFSG.ClassicalInvolution.ModelFacts
