module

public import CFSG.LieType.Chevalley.OrdinaryEFieldGraphQuotient

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.D4Three

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley
open scoped commutatorElement

theorem cartanD4_symm (i j : Fin Tag.D4.rank) : Tag.D4.cartan i j = Tag.D4.cartan j i := by
  fin_cases i <;> fin_cases j <;> decide

theorem cartanD4_offdiag (i j : Fin Tag.D4.rank) (hij : i ≠ j) :
    Tag.D4.cartan i j = 0 ∨ Tag.D4.cartan i j = -1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem perm_pow_of_cartanD4 (π : Equiv.Perm (Fin Tag.D4.rank))
    (hπ : ∀ i j, Tag.D4.cartan (π i) (π j) = Tag.D4.cartan i j) (h3 : π ^ 3 = 1) :
    π = 1 ∨ π = TwistTag.D4.perm ∨ π = TwistTag.D4.perm ^ 2 := by
  have key : ∀ π : Equiv.Perm (Fin 4),
      (∀ i j : Fin 4, (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) (π i) (π j) =
        (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
          Fin 4 → Fin 4 → ℤ) i j) → π ^ 3 = 1 →
      π = 1 ∨ π = (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ∨
        π = (Equiv.swap 0 1 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ^ 2 := by
    decide +kernel
  have hc : ∀ i j : Fin 4, Tag.D4.cartan i j =
      (![![2, 0, -1, 0], ![0, 2, -1, 0], ![-1, -1, 2, -1], ![0, 0, -1, 2]] :
        Fin 4 → Fin 4 → ℤ) i j := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  exact key π (fun i j => by rw [← hc, ← hc]; exact hπ i j) h3


variable {K : Type} [Field K]

theorem symmetrizedCartan_D4 : Tag.D4.symmetrizedCartan = Tag.D4.cartan := by
  simp [Tag.symmetrizedCartan, Tag.symmetrizer]

open Matrix in
theorem simplePos_commute_iff_D4 {i j : Fin Tag.D4.rank} (hij : i ≠ j) :
    (∀ x ∈ simplePosSubgroup Tag.D4 K i, ∀ y ∈ simplePosSubgroup Tag.D4 K j, Commute x y) ↔
      Tag.D4.cartan i j ≠ -1 := by
  constructor
  · intro h hc
    have hcji : Tag.D4.cartan j i = -1 := by rw [← cartanD4_symm]; exact hc
    have h1 := congrArg Subtype.val ((h (adjX Tag.D4 K i 1) ⟨1, rfl⟩ (adjX Tag.D4 K j 1)
      ⟨1, rfl⟩).eq)
    change xUnit Tag.D4 K i 1 * xUnit Tag.D4 K j 1 = xUnit Tag.D4 K j 1 * xUnit Tag.D4 K i 1 at h1
    have h2 := (a2_simple_root_commutatorElement K hc hcji 1 1).1
    rw [commutatorElement_eq_one_iff_mul_comm.2 h1, mul_one] at h2
    have h3 : xUnit Tag.D4 K j 1 = xUnit Tag.D4 K j 0 := by
      rw [xUnit_zero]
      have := congrArg (fun g => (weylElt Tag.D4 K i 1)⁻¹ * g * weylElt Tag.D4 K i 1) h2
      simpa [mul_assoc] using this.symm
    exact one_ne_zero (adjX_injective j (Subtype.ext h3))
  · intro hc x hx y hy
    have h0 : Tag.D4.cartan i j = 0 := (cartanD4_offdiag i j hij).resolve_right hc
    obtain ⟨c, hcx⟩ := hx
    obtain ⟨d, hdy⟩ := hy
    have hτ' : Tag.D4 = .D4 ∨ Tag.D4 = .E6 ∨ Tag.D4 = .E7 ∨ Tag.D4 = .E8 := Or.inl rfl
    have hform : (Pi.single i 1 : Fin Tag.D4.rank → ℤ) ⬝ᵥ
        (Tag.D4.symmetrizedCartan *ᵥ Pi.single j 1) = 0 := by
      rw [single_dotProduct, one_mul, mulVec_single_one, symmetrizedCartan_D4]
      exact h0
    have hxy := (simply_laced_orthogonal_root_commutation Tag.D4 hτ').2 K _ _
      (isRoot_single Tag.D4 i) (isRoot_single Tag.D4 j) hform (xUnit Tag.D4 K i c)
      (mem_rootSubgroup.2 ⟨c, by rw [pinnedX_single]⟩) (xUnit Tag.D4 K j d)
      (mem_rootSubgroup.2 ⟨d, by rw [pinnedX_single]⟩)
    apply Subtype.ext
    change (x : ModGL Tag.D4 K) * y = y * x
    rw [hcx, hdy]
    exact hxy

theorem cartan_perm_eq_D4 {α : MulAut (adjointGroup Tag.D4 K)} {π : Equiv.Perm (Fin Tag.D4.rank)}
    (hπ : ∀ i, (simplePosSubgroup Tag.D4 K i).map α.toMonoidHom =
      simplePosSubgroup Tag.D4 K (π i)) (i j : Fin Tag.D4.rank) :
    Tag.D4.cartan (π i) (π j) = Tag.D4.cartan i j := by
  by_cases hij : i = j
  · subst hij
    rw [Tag.cartan_self, Tag.cartan_self]
  have hπij : π i ≠ π j := π.injective.ne hij
  have htr := commute_simplePos_transport (hπ i) (hπ j)
  have h1 := simplePos_commute_iff_D4 (K := K) hij
  have h2 := simplePos_commute_iff_D4 (K := K) hπij
  rcases cartanD4_offdiag i j hij with h | h <;> rcases cartanD4_offdiag (π i) (π j) hπij with h' | h'
  · rw [h, h']
  · exact absurd h' (h2.1 (htr.1 (h1.2 (by rw [h]; decide))))
  · exact absurd h (h1.1 (htr.2 (h2.2 (by rw [h']; decide))))
  · rw [h, h']

variable (K) in
@[expose] def d4Graph (ε : ℕ) : MulAut (adjointGroup Tag.D4 K) :=
  mulAutRestrict (adjointGroup Tag.D4 K) (MulAut.conj (diagramMap TwistTag.D4 K ^ ε))
    (map_conj_pow_of_map_conj (diagramMap TwistTag.D4 K)
      (map_conj_diagramMap TwistTag.D4 K (Or.inl rfl)) ε)

@[expose] def d4Rho : Equiv.Perm (Fin Tag.D4.rank) := TwistTag.D4.perm

@[expose] def d4P (K : Type) [Field K] : ModGL Tag.D4 K := diagramMap TwistTag.D4 K

theorem coe_d4Graph (ε : ℕ) (h : adjointGroup Tag.D4 K) :
    (d4Graph K ε h : ModGL Tag.D4 K) = d4P K ^ ε * (h : ModGL Tag.D4 K) * (d4P K ^ ε)⁻¹ :=
  rfl

theorem d4Graph_mem (ε : ℕ) : d4Graph K ε ∈ unipotentPairAut Tag.D4 K :=
  ⟨map_subgroupOf_mulAutRestrict _ (map_conj_pow_of_map_conj (diagramMap TwistTag.D4 K)
      (map_conj_diagramMap TwistTag.D4 K (Or.inr (Or.inl rfl))) ε),
    map_subgroupOf_mulAutRestrict _ (map_conj_pow_of_map_conj (diagramMap TwistTag.D4 K)
      (map_conj_diagramMap TwistTag.D4 K (Or.inr (Or.inr rfl))) ε)⟩

theorem d4Graph_adjX (ε : ℕ) (i : Fin Tag.D4.rank) (c : K) :
    d4Graph K ε (adjX Tag.D4 K i c) = adjX Tag.D4 K ((d4Rho ^ ε) i) c :=
  Subtype.ext (diagramMap_pow_mul_xUnit_mul_inv TwistTag.D4 K ε i c)

theorem d4Graph_adjY (ε : ℕ) (i : Fin Tag.D4.rank) (c : K) :
    d4Graph K ε (adjY Tag.D4 K i c) = adjY Tag.D4 K ((d4Rho ^ ε) i) c :=
  Subtype.ext (diagramMap_pow_mul_yUnit_mul_inv TwistTag.D4 K ε i c)

theorem map_simplePosSubgroup_d4Graph (ε : ℕ) (i : Fin Tag.D4.rank) :
    (simplePosSubgroup Tag.D4 K i).map (d4Graph K ε).toMonoidHom =
      simplePosSubgroup Tag.D4 K ((d4Rho ^ ε) i) :=
  map_simplePosSubgroup_of_adjX (f := fun c => c) Function.surjective_id (d4Graph_adjX ε i)

theorem map_simpleNegSubgroup_d4Graph (ε : ℕ) (i : Fin Tag.D4.rank) :
    (simpleNegSubgroup Tag.D4 K i).map (d4Graph K ε).toMonoidHom =
      simpleNegSubgroup Tag.D4 K ((d4Rho ^ ε) i) :=
  map_simpleNegSubgroup_of_adjY (f := fun c => c) Function.surjective_id (d4Graph_adjY ε i)

variable [Finite K]

theorem exists_normalAut_mul_graph {β : MulAut (adjointGroup Tag.D4 K)} {ε : ℕ}
    (hε : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
        simplePosSubgroup Tag.D4 K ((d4Rho ^ ε) i) ∧
      (simpleNegSubgroup Tag.D4 K i).map β.toMonoidHom =
        simpleNegSubgroup Tag.D4 K ((d4Rho ^ ε) i)) :
    ∃ (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K),
      β = exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε := by
  have hζ : β * (d4Graph K ε)⁻¹ ∈ rootPairAut Tag.D4 K := by
    refine mem_rootPairAut.2 fun i => ?_
    obtain ⟨j, rfl⟩ := ((d4Rho ^ ε : Equiv.Perm (Fin Tag.D4.rank))).surjective i
    refine ⟨?_, ?_⟩
    · rw [map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq
        (map_simplePosSubgroup_d4Graph ε j), (hε j).1]
    · rw [map_toMonoidHom_mul_mulAut, map_inv_toMonoidHom_of_map_eq
        (map_simpleNegSubgroup_d4Graph ε j), (hε j).2]
  obtain ⟨p, hp, -⟩ := (ordinary_Chevalley_root_pair_common_field_parameter Tag.D4 K).1 _ hζ
  refine ⟨p.1, p.2, mulAut_ext_adjX_adjY (fun i c => ?_) fun i c => ?_⟩
  · have e : β (adjX Tag.D4 K i c) = (β * (d4Graph K ε)⁻¹) (d4Graph K ε (adjX Tag.D4 K i c)) := by
      rw [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e, d4Graph_adjX, (hp _).1, MulAut.mul_apply, d4Graph_adjX, exactNormalAut_adjX]
    rfl
  · have e : β (adjY Tag.D4 K i c) = (β * (d4Graph K ε)⁻¹) (d4Graph K ε (adjY Tag.D4 K i c)) := by
      rw [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [e, d4Graph_adjY, (hp _).2.1, MulAut.mul_apply, d4Graph_adjY, exactNormalAut_adjY]
    rfl

theorem mul_conj_eq {G : Type*} [Group G] (β : MulAut G) (g : G) :
    β * MulAut.conj g = MulAut.conj (β g) * β := by
  ext x
  simp [MulAut.mul_apply, MulAut.conj_apply]

theorem map_simplePos_pow {β : MulAut (adjointGroup Tag.D4 K)} {π : Equiv.Perm (Fin Tag.D4.rank)}
    (h : ∀ i, (simplePosSubgroup Tag.D4 K i).map β.toMonoidHom =
      simplePosSubgroup Tag.D4 K (π i)) (n : ℕ) (i : Fin Tag.D4.rank) :
    (simplePosSubgroup Tag.D4 K i).map (β ^ n).toMonoidHom =
      simplePosSubgroup Tag.D4 K ((π ^ n) i) := by
  induction n generalizing i with
  | zero => simpa using map_mulAut_one _
  | succ n ih =>
    rw [pow_succ, map_toMonoidHom_mul_mulAut, h i, ih, pow_succ, Equiv.Perm.mul_apply]

theorem normalGraph_apply_adjX (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (i : Fin Tag.D4.rank) (c : K) :
    (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) (adjX Tag.D4 K i c) =
      adjX Tag.D4 K ((d4Rho ^ ε) i) ((a ((d4Rho ^ ε) i) : K) * σ c) := by
  rw [MulAut.mul_apply, d4Graph_adjX, exactNormalAut_adjX]
  rfl

theorem d4Rho_pow_three' : d4Rho ^ 3 = 1 := by decide

theorem pow_three_apply_monomial {G ι : Type*} [Group G] (ν : MulAut G) (π : Equiv.Perm ι)
    (f : ι → K) (σ : K ≃+* K) (adj : ι → K → G)
    (h1 : ∀ j c, ν (adj j c) = adj (π j) (f (π j) * σ c)) (hπ : ∀ i, π (π (π i)) = i) (i : ι)
    (c : K) :
    (ν ^ 3) (adj i c) =
      adj i ((f i * σ (f (π (π i))) * σ (σ (f (π i)))) * σ (σ (σ c))) := by
  have e : ν ^ 3 = ν * ν * ν := by simp [pow_succ]
  rw [e, MulAut.mul_apply, MulAut.mul_apply, h1, h1, h1, hπ]
  congr 1
  simp only [map_mul]
  ring

theorem normalGraph_pow_three_adjX (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ)
    (i : Fin Tag.D4.rank) :
    ∃ m : K, ∀ c : K, ((exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ^ 3) (adjX Tag.D4 K i c) =
      adjX Tag.D4 K i (m * σ (σ (σ c))) := by
  have hπ3 : (d4Rho ^ ε) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, d4Rho_pow_three', one_pow]
  have hπ : ∀ j, (d4Rho ^ ε) ((d4Rho ^ ε) ((d4Rho ^ ε) j)) = j := fun j => by
    have := congrArg (fun f : Equiv.Perm (Fin Tag.D4.rank) => f j) hπ3
    simpa [pow_succ] using this
  exact ⟨_, pow_three_apply_monomial (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) (d4Rho ^ ε)
    (fun j => (a j : K)) σ (adjX Tag.D4 K) (fun j c => normalGraph_apply_adjX a σ ε j c) hπ i⟩

theorem exists_cube_normal_form_sigma (α : MulAut (adjointGroup Tag.D4 K)) (hα : α ^ 3 = 1) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε < 3 ∧
      σ ^ 3 = 1 ∧ α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
  have : Fact (ringChar K).Prime := ⟨CharP.char_is_prime K _⟩
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨c, β, hU, hV, rfl⟩ :=
    (exceptional_ordinary_Sylow_opposition Tag.D4 K (ringChar K) w₀ hw₀).2.2.2.2.2 α
  have hA : β ∈ unipotentPairAut Tag.D4 K := ⟨hU, hV⟩
  obtain ⟨π, hπ⟩ := exists_perm_map_simple hA
  have hcart := cartan_perm_eq_D4 (K := K) (fun i => (hπ i).1)
  have hβ3 : β ^ 3 = MulAut.conj (c * β c * β (β c))⁻¹ := by
    refine MulEquiv.ext fun x => ?_
    have h1 : ((MulAut.conj c * β) ^ 3) x =
        (c * β c * β (β c)) * (β ^ 3) x * (c * β c * β (β c))⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply, MulAut.conj_apply, map_mul,
        map_inv]
      group
    rw [hα, MulAut.one_apply] at h1
    rw [MulAut.conj_apply, inv_inv]
    calc (β ^ 3) x = (c * β c * β (β c))⁻¹ * ((c * β c * β (β c)) * (β ^ 3) x *
          (c * β c * β (β c))⁻¹) * (c * β c * β (β c)) := by group
      _ = (c * β c * β (β c))⁻¹ * x * (c * β c * β (β c)) := by rw [← h1]
  have hβ3A : β ^ 3 ∈ unipotentPairAut Tag.D4 K := pow_mem hA 3
  obtain ⟨b, hb⟩ := exists_conj_eq_exactNormalAut_diag (hβ3 ▸ hβ3A)
  have hπ3 : π ^ 3 = 1 := by
    refine perm_map_simple_unique (α := β ^ 3) (π := π ^ 3) (π' := 1)
      (fun i => map_simplePos_pow (fun j => (hπ j).1) 3 i) (fun i => ?_)
    rw [hβ3, hb, map_simplePosSubgroup_exactNormalAut b 1 0 i]
    rfl
  have hcases := perm_pow_of_cartanD4 π hcart hπ3
  have hex : ∃ ε : ℕ, ε < 3 ∧ π = d4Rho ^ ε := by
    rcases hcases with h | h | h
    · exact ⟨0, by norm_num, by rw [h]; rfl⟩
    · exact ⟨1, by norm_num, by rw [h]; exact (pow_one _).symm⟩
    · exact ⟨2, by norm_num, h⟩
  obtain ⟨ε, hε3, rfl⟩ := hex
  obtain ⟨a, σ, hβ⟩ := exists_normalAut_mul_graph (K := K) hπ
  have hβ3' : β ^ 3 = exactNormalAut Tag.D4 K b 1 0 := hβ3.trans hb
  have hσ3 : σ ^ 3 = 1 := by
    obtain ⟨m, hm⟩ := normalGraph_pow_three_adjX (K := K) a σ ε ⟨0, by decide⟩
    have hm' : ∀ c : K, ((exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) ^ 3)
        (adjX Tag.D4 K ⟨0, by decide⟩ c) =
        adjX Tag.D4 K ⟨0, by decide⟩ ((b ⟨0, by decide⟩ : K) * c) := by
      intro c
      rw [← hβ, hβ3', exactNormalAut_adjX]
      rfl
    have hmc : ∀ c : K, m * σ (σ (σ c)) = (b ⟨0, by decide⟩ : K) * c := fun c =>
      adjX_injective ⟨0, by decide⟩ ((hm c).symm.trans (hm' c))
    have hm1 : m = (b ⟨0, by decide⟩ : K) := by simpa using hmc 1
    refine RingEquiv.ext fun c => ?_
    have := hmc c
    rw [hm1] at this
    have hb0 : ((b ⟨0, by decide⟩ : Kˣ) : K) ≠ 0 := Units.ne_zero _
    have h3 : σ (σ (σ c)) = c := mul_left_cancel₀ hb0 this
    simpa [pow_succ] using h3
  exact ⟨c, a, σ, ε, hε3, hσ3, by rw [hβ]⟩

theorem exists_cube_normal_form (α : MulAut (adjointGroup Tag.D4 K)) (hα : α ^ 3 = 1) :
    ∃ (g : adjointGroup Tag.D4 K) (a : Fin Tag.D4.rank → Kˣ) (σ : K ≃+* K) (ε : ℕ), ε < 3 ∧
      α = MulAut.conj g * (exactNormalAut Tag.D4 K a σ 0 * d4Graph K ε) := by
  obtain ⟨g, a, σ, ε, h3, -, h⟩ := exists_cube_normal_form_sigma α hα
  exact ⟨g, a, σ, ε, h3, h⟩

end CFSG.HardMathSupport.Lang.D4Three
