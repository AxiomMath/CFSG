module

public import CFSG.ClassicalInvolution.ModelFacts.ChevAutMain
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutTorusDiag
public import CFSG.ClassicalInvolution.RouteD.LocalTwinWeyl

public section

namespace CFSG.ClassicalInvolution.ModelFacts.ChevAut

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.CentralExt
  CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.RootSystem CFSG.LieType.CurtisTits

section Instances

variable (F : Type) [Field F]

theorem torusSetup_E6 : TorusSetup (e6Datum F) (e6Data_valid.xm F) (e6Data_valid.nm F)
    (e6Data_valid.torus F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e6Datum F).isFiniteType
    (Dv := (e6Datum F).divisible) rfl
  exact ⟨⟨_, O, e6_chevalleyExtras F O _
      (e6Data_valid.commutatorFormula_commC F posDef_cartan_E6 _
        (roots_eq isFiniteType_cartan_E6) O)⟩,
    e6Datum_isCTGroupDatum F, e6Datum_steinbergExtras F, e6Datum_bruhatExtras F,
    fun _ => rfl, fun _ _ => ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩,
    fun i s s' => e6Data_valid.hm_mul F i s s', rfl⟩

theorem torusSetup_E7 : TorusSetup (e7Datum F) (e7Data_valid.xm F) (e7Data_valid.nm F)
    (e7Data_valid.torus F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (e7Datum F).isFiniteType
    (Dv := (e7Datum F).divisible) rfl
  exact ⟨⟨_, O, e7_chevalleyExtras F O _
      (e7Data_valid.commutatorFormula_commC F posDef_cartan_E7 _
        (roots_eq isFiniteType_cartan_E7) O)⟩,
    e7Datum_isCTGroupDatum F, e7Datum_steinbergExtras F, e7Datum_bruhatExtras F,
    fun _ => rfl, fun _ _ => ⟨fun ⟨s, hs⟩ => ⟨s, hs.symm⟩, fun ⟨s, hs⟩ => ⟨s, hs.symm⟩⟩,
    fun i s s' => e7Data_valid.hm_mul F i s s', rfl⟩


theorem torusGen_e8 (i : Fin Tag.E8.rank) (t : Fˣ) :
    torusGen (Adjoint.e8Par F) i t = Adjoint.torusHom F i t := by
  unfold torusGen
  rw [Adjoint.e8Par, Adjoint.weylElement_xPar (F := rootOperatorFamily .E8) i t,
    Adjoint.weylElement_xPar (F := rootOperatorFamily .E8) i 1]
  rw [Adjoint.torusElement_one_eq, one_mul, mul_inv_cancel_right]
  rfl

theorem torusSetup_E8 : TorusSetup (Adjoint.e8Datum F) (Adjoint.e8Par F)
    (CFSG.LieType.Chevalley.weylElement .E8 F) (Adjoint.torus (τ := .E8) F) := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (Adjoint.e8Datum F).isFiniteType
    (Dv := (Adjoint.e8Datum F).divisible) rfl
  obtain ⟨C, -, hC⟩ := Adjoint.e8_commutatorFormula F O
  refine ⟨⟨C, O, Adjoint.e8_chevalleyExtras F O C hC⟩, Adjoint.e8_isCTGroupDatum F,
    Adjoint.e8_steinbergExtras F, Adjoint.e8_bruhatExtras F, fun i =>
      Adjoint.weylElement_eq_xPar (rootOperatorFamily .E8) i, fun i y => ?_, fun i s s' => ?_, rfl⟩
  · constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, (torusGen_e8 F i s).symm⟩
    · rintro ⟨s, rfl⟩
      exact ⟨s, (torusGen_e8 F i s).symm⟩
  · rw [torusGen_e8, torusGen_e8, torusGen_e8, map_mul]

end Instances

section Sign

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]

open Classical in
theorem diagChar_eq_one_iff (h2 : (2 : F) ≠ 0) {b : Fin D.rank → Fˣ}
    (hb : ∀ i, b i = 1 ∨ b i = -1) (γ : Fin D.rank → ℤ) :
    diagChar b γ = 1 ↔ ∑ i, (γ i : ZMod 2) * (if b i = 1 then 0 else 1) = 0 := by
  have hne : (-1 : Fˣ) ≠ 1 := by
    intro h
    apply h2
    have := congrArg (fun u : Fˣ => (u : F)) h
    simp only [Units.val_neg, Units.val_one] at this
    linear_combination -this
  have h1 : diagChar b γ = (-1 : Fˣ) ^ (∑ i, γ i * (if b i = 1 then (0 : ℤ) else 1)) := by
    rw [diagChar, ← Finset.prod_zpow_eq_zpow_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases hb i with h | h
    · rw [h]
      simp
    · rw [h]
      simp [hne]
  have h4 : ∀ M : ℤ, (-1 : Fˣ) ^ M = 1 ↔ Even M := by
    intro M
    rw [neg_one_zpow_eq_ite]
    by_cases he : Even M
    · simp [he]
    · simp [he, hne]
  rw [h1, h4]
  have h3 : ((∑ i, γ i * (if b i = 1 then (0 : ℤ) else 1) : ℤ) : ZMod 2) =
      ∑ i, (γ i : ZMod 2) * (if b i = 1 then 0 else 1) := by
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [← h3, ZMod.intCast_eq_zero_iff_even]

end Sign

section Fixed

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem eq_of_map_eq {p : ℕ} [Fact p.Prime] [CharP F p] (hS : TorusSetup D x n H)
    {X : Type} [Group X] (θ : K →* X) (hker : θ.ker ≤ Subgroup.center K)
    (hC : ¬ p ∣ Nat.card θ.ker) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) {c c' : F}
    (h : θ (x γ c) = θ (x γ c')) : c = c' := by
  obtain ⟨C, O, hE⟩ := hS.chev
  exact (hE.param γ hγ).2.2 (CFSG.LieType.CentralExt.eq_of_pElement (π := θ) hker hC h
    (exists_orderOf_param hE.param hγ c) (exists_orderOf_param hE.param hγ c'))

theorem fixes_iff_charOf {p : ℕ} [Fact p.Prime] [CharP F p] (hS : TorusSetup D x n H)
    (hp2 : p ≠ 2) {X : Type} [Group X] (θ : K →* X) (hker : θ.ker ≤ Subgroup.center K)
    (hC : ¬ p ∣ Nat.card θ.ker) (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (α : K →* K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) (b : Fin D.rank → Fˣ)
    (hb : ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c)) :
    ∃ v : Fin D.rank → ZMod 2, ∀ γ ∈ D.roots,
      ((∀ y ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map θ, σ y = y) ↔
        ∑ i, (γ i : ZMod 2) * v i = 0) := by
  classical
  obtain ⟨C, O, hE⟩ := hS.chev
  have h2 : (2 : F) ≠ 0 := by
    intro h0
    have := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h0)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 this)
  have hroot : ∀ i, (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := fun i =>
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : ∀ γ ∈ D.roots, -γ ∈ D.roots := fun γ hγ =>
    CFSG.LieType.Steinberg.OfCartan.neg_mem_roots D.isFiniteType hγ
  have hbpm : ∀ i, b i = 1 ∨ b i = -1 := by
    intro i
    have h1 := hb (Pi.single i 1) (hroot i) 1
    rw [diagChar_single] at h1
    have h2' := hb (Pi.single i 1) (hroot i) ((b i : F) * 1)
    rw [diagChar_single] at h2'
    have h3 : θ (x (Pi.single i 1) ((b i : F) * ((b i : F) * 1))) = θ (x (Pi.single i 1) 1) :=
      calc θ (x (Pi.single i 1) ((b i : F) * ((b i : F) * 1)))
          = θ (α (α (x (Pi.single i 1) 1))) := by rw [h1, h2']
        _ = σ (θ (α (x (Pi.single i 1) 1))) := hαθ _
        _ = σ (σ (θ (x (Pi.single i 1) 1))) := by rw [hαθ]
        _ = θ (x (Pi.single i 1) 1) := hσ2 _
    have h4 := eq_of_map_eq hS θ hker hC (hroot i) h3
    have h5 : (b i : F) * (b i : F) = 1 := by simpa using h4
    rcases mul_self_eq_one_iff.1 h5 with h | h
    · exact Or.inl (Units.ext (by simpa using h))
    · exact Or.inr (Units.ext (by simpa using h))
  refine ⟨fun i => if b i = 1 then 0 else 1, fun γ hγ => ?_⟩
  rw [← diagChar_eq_one_iff h2 hbpm γ]
  constructor
  · intro hall
    have hmem : θ (x γ 1) ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map θ :=
      ⟨x γ 1, Subgroup.mem_sup_left (((hE.param γ hγ).1 _).2 ⟨1, rfl⟩), rfl⟩
    have h1 := hall _ hmem
    rw [← hαθ, hb γ hγ 1] at h1
    have h3 := eq_of_map_eq hS θ hker hC hγ h1
    exact Units.ext (by simpa using h3)
  · intro hd y hy
    obtain ⟨k, hk, rfl⟩ := hy
    have hα1 : ∀ c, α (x γ c) = x γ c := fun c => by
      rw [hb γ hγ c, hd]
      simp
    have hα2 : ∀ c, α (x (-γ) c) = x (-γ) c := fun c => by
      rw [hb (-γ) (hneg γ hγ) c, diagChar_neg, hd]
      simp
    have hle : (D.rootGroup γ ⊔ D.rootGroup (-γ)) ≤ MonoidHom.eqLocus α (MonoidHom.id K) := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 g).1 hg
        exact hα1 c
      · obtain ⟨c, rfl⟩ := ((hE.param (-γ) (hneg γ hγ)).1 g).1 hg
        exact hα2 c
    have hk' : α k = k := hle hk
    calc σ (θ k) = θ (α k) := (hαθ k).symm
      _ = θ k := by rw [hk']

end Fixed

section Lift

variable {K : Type} [Group K] (D : UniversalRootDatum K) {F : Type} [Field F]

@[expose] def LiftsToNormalForm (x : (Fin D.rank → ℤ) → F → K) : Prop :=
  ∀ {X : Type} [Group X] (θ : K →* X), Function.Surjective θ → θ.ker ≤ Subgroup.center K →
    ∀ σ : X ≃* X, ∃ (α : K ≃* K) (g : K) (a : Fin D.rank → Fˣ) (φ : F ≃+* F)
      (π : Equiv.Perm (Fin D.rank)), (∀ y, θ (α y) = σ (θ y)) ∧
      NormalForm x α.toMonoidHom g a φ π ∧ ∀ j l, D.cartan (π j) (π l) = D.cartan j l

end Lift

section Toral

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F]
  {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}

theorem mul_inv_mem_center_of_fix {X : Type} [Group X] (θ : K →* X)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) (α : K →* K)
    (hαθ : ∀ y, θ (α y) = σ (θ y)) {t : K} (ht : σ (θ t) = θ t) :
    α t * t⁻¹ ∈ Subgroup.center K := by
  apply hker
  rw [MonoidHom.mem_ker, map_mul, map_inv, hαθ, ht, mul_inv_cancel]

theorem exists_diag_of_central_quotient [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (hlift : LiftsToNormalForm D x) (hp2 : p ≠ 2)
    (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    {X : Type} [Group X] (θ : K →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X)
    (hfix : ∀ i s, σ (θ (torusGen x i s)) = θ (torusGen x i s)) :
    ∃ (α : K ≃* K) (b : Fin D.rank → Fˣ), (∀ y, θ (α y) = σ (θ y)) ∧
      ∀ γ ∈ D.roots, ∀ c, α (x γ c) = x γ ((diagChar b γ : F) * c) := by
  obtain ⟨α, g, a, φ, π, hαθ, hN, hπ⟩ := hlift θ hθ hker σ
  obtain ⟨b, hb⟩ := exists_diag_of_fixes_torus (p := p) hS hp2 hq hr hlong hnb hAij hπ hN
    (fun i s => mul_inv_mem_center_of_fix θ hker σ α.toMonoidHom hαθ (hfix i s))
  exact ⟨α, b, hαθ, hb⟩

theorem toral_central_quotient [Finite F] {p : ℕ} [Fact p.Prime] [CharP F p]
    (hS : TorusSetup D x n H) (hlift : LiftsToNormalForm D x) (hp2 : p ≠ 2)
    (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (hC : ∀ N : Subgroup K, N ≤ Subgroup.center K → ¬ p ∣ Nat.card N)
    {X : Type} [Group X] (θ : K →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center K) (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y)
    (hfix : ∀ i s, σ (θ (torusGen x i s)) = θ (torusGen x i s)) :
    ∃ v : Fin D.rank → ZMod 2, ∀ γ ∈ D.roots,
      ((∀ y ∈ (D.rootGroup γ ⊔ D.rootGroup (-γ)).map θ, σ y = y) ↔
        ∑ i, (γ i : ZMod 2) * v i = 0) := by
  obtain ⟨α, b, hαθ, hb⟩ := exists_diag_of_central_quotient hS hlift hp2 hq hr hlong hnb hAij θ hθ
    hker σ hfix
  exact fixes_iff_charOf hS hp2 θ hker (hC _ hker) σ hσ2 α.toMonoidHom hαθ b hb

end Toral

section Ambient

variable {K : Type} [Group K] {D : UniversalRootDatum K} {F : Type} [Field F] [Finite F]
  {p : ℕ} [Fact p.Prime] [CharP F p] {x : (Fin D.rank → ℤ) → F → K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem toral_ambient (hS : TorusSetup D x n H) (hlift : LiftsToNormalForm D x) (hp2 : p ≠ 2)
    (hq : 5 ≤ Nat.card F) (hr : 0 < D.rank)
    (hlong : ∀ k, IsLongest D.isFiniteType ∅ (Pi.single k 1))
    (hnb : ∀ k, ∃ j, D.cartan j k = -1)
    (hAij : ∀ i j, i ≠ j → D.cartan i j = 0 ∨ D.cartan i j = -1)
    (hC : ∀ N : Subgroup K, N ≤ Subgroup.center K → ¬ p ∣ Nat.card N)
    {Y : Type} [Group Y] (ψ : K →* Y) (hψ : ψ.ker ≤ Subgroup.center K) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : K)
    (hfix : ∀ i s, σ (ψ (k₀ * torusGen x i s * k₀⁻¹)) = ψ (k₀ * torusGen x i s * k₀⁻¹)) :
    ∃ v : Fin D.rank → ZMod 2, ∀ γ ∈ D.roots,
      ((∀ y ∈ ((D.rootGroup γ ⊔ D.rootGroup (-γ)).map (MulAut.conj k₀).toMonoidHom).map ψ,
          σ y = y) ↔ ∑ i, (γ i : ZMod 2) * v i = 0) := by
  set θ₁ : K →* Y := ψ.comp (MulAut.conj k₀).toMonoidHom with hθ₁
  have hθ₁ap : ∀ k, θ₁ k = ψ (k₀ * k * k₀⁻¹) := fun k => rfl
  have hrange : ∀ k, ψ k ∈ θ₁.range := fun k => ⟨k₀⁻¹ * k * k₀, by
    rw [hθ₁ap]
    congr 1
    group⟩
  have hσR : ∀ r ∈ θ₁.range, σ r ∈ θ₁.range := by
    rintro r ⟨k, rfl⟩
    obtain ⟨k', hk'⟩ := hσr (k₀ * k * k₀⁻¹)
    rw [hθ₁ap, ← hk']
    exact hrange k'
  let σR : θ₁.range ≃* θ₁.range :=
    { toFun := fun r => ⟨σ r, hσR r r.2⟩
      invFun := fun r => ⟨σ r, hσR r r.2⟩
      left_inv := fun r => Subtype.ext (hσ2 r)
      right_inv := fun r => Subtype.ext (hσ2 r)
      map_mul' := fun a b => Subtype.ext (map_mul σ (a : Y) (b : Y)) }
  have hkerθ : θ₁.rangeRestrict.ker ≤ Subgroup.center K := by
    intro y hy
    have h1 : θ₁ y = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
    have hz : k₀ * y * k₀⁻¹ ∈ Subgroup.center K := hψ (MonoidHom.mem_ker.2 (by rwa [hθ₁ap] at h1))
    have hy' : y = k₀ * y * k₀⁻¹ := by
      have := Subgroup.mem_center_iff.1 hz k₀⁻¹
      calc y = k₀⁻¹ * (k₀ * y * k₀⁻¹) * k₀ := by group
        _ = (k₀ * y * k₀⁻¹) * k₀⁻¹ * k₀ := by rw [this]
        _ = k₀ * y * k₀⁻¹ := by group
    rw [hy']
    exact hz
  obtain ⟨v, hv⟩ := toral_central_quotient hS hlift hp2 hq hr hlong hnb hAij hC θ₁.rangeRestrict
    θ₁.rangeRestrict_surjective hkerθ σR (fun r => Subtype.ext (hσ2 r))
    (fun i s => Subtype.ext (hfix i s))
  refine ⟨v, fun γ hγ => ?_⟩
  rw [← hv γ hγ]
  constructor
  · intro h y hy
    obtain ⟨s, hs, rfl⟩ := hy
    exact Subtype.ext (h _ ⟨_, ⟨s, hs, rfl⟩, rfl⟩)
  · intro h y hy
    obtain ⟨_, ⟨s, hs, rfl⟩, rfl⟩ := hy
    exact congrArg Subtype.val (h _ ⟨s, hs, rfl⟩)

end Ambient

section Families

open CFSG.ClassicalInvolution.RouteD (charOf)
open CFSG.ClassicalInvolution.Generic (conjSub)

theorem cartanE6_nb : ∀ k : Fin 6, ∃ j : Fin 6, Tag.cartan .E6 j k = -1 := by decide
theorem cartanE7_nb : ∀ k : Fin 7, ∃ j : Fin 7, Tag.cartan .E7 j k = -1 := by decide
theorem cartanE8_nb : ∀ k : Fin 8, ∃ j : Fin 8, Tag.cartan .E8 j k = -1 := by decide

theorem cartanE6_offDiag :
    ∀ i j : Fin 6, i ≠ j → Tag.cartan .E6 i j = 0 ∨ Tag.cartan .E6 i j = -1 := by
  intro i j hij
  have h : i = j ∨ Tag.cartan .E6 i j = 0 ∨ Tag.cartan .E6 i j = -1 := by
    fin_cases i <;> fin_cases j <;> decide
  exact h.resolve_left hij

theorem cartanE7_offDiag :
    ∀ i j : Fin 7, i ≠ j → Tag.cartan .E7 i j = 0 ∨ Tag.cartan .E7 i j = -1 := by
  intro i j hij
  have h : i = j ∨ Tag.cartan .E7 i j = 0 ∨ Tag.cartan .E7 i j = -1 := by
    fin_cases i <;> fin_cases j <;> decide
  exact h.resolve_left hij

theorem cartanE8_offDiag :
    ∀ i j : Fin 8, i ≠ j → Tag.cartan .E8 i j = 0 ∨ Tag.cartan .E8 i j = -1 := by
  intro i j hij
  have h : i = j ∨ Tag.cartan .E8 i j = 0 ∨ Tag.cartan .E8 i j = -1 := by
    fin_cases i <;> fin_cases j <;> decide
  exact h.resolve_left hij

theorem cartan_exactPerm_E6 (ε : ℕ) (hε : ε < 2) (j l : Fin 6) :
    Tag.cartan .E6 (exactPerm Tag.E6 ε j) (exactPerm Tag.E6 ε l) = Tag.cartan .E6 j l := by
  interval_cases ε <;> (fin_cases j <;> fin_cases l <;> decide)

variable (F : Type) [Field F] [Finite F]

theorem liftsToNormalForm_E6 {p : ℕ} [Fact p.Prime] [CharP F p] :
    LiftsToNormalForm (e6Datum F) (e6Data_valid.xm F) := by
  intro X _ θ hθ hker σ
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E6 (p := p) θ hθ hker σ
  exact ⟨α, g, a, φ, exactPerm Tag.E6 ε, hαθ, ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩,
    fun j l => cartan_exactPerm_E6 ε ε.isLt j l⟩

theorem liftsToNormalForm_E7 {p : ℕ} [Fact p.Prime] [CharP F p] :
    LiftsToNormalForm (e7Datum F) (e7Data_valid.xm F) := by
  intro X _ θ hθ hker σ
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E7 (p := p) θ hθ hker σ
  exact ⟨α, g, a, φ, exactPerm Tag.E7 ε, hαθ, ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩,
    fun j l => rfl⟩

theorem liftsToNormalForm_E8 {p : ℕ} [Fact p.Prime] [CharP F p] :
    LiftsToNormalForm (Adjoint.e8Datum F) (Adjoint.e8Par F) := by
  intro X _ θ hθ hker σ
  obtain ⟨α, g, a, φ, ε, hαθ, h⟩ := excAut_E8 (p := p) θ hθ hker σ
  exact ⟨α, g, a, φ, exactPerm Tag.E8 ε, hαθ, ⟨fun i c => (h i c).1, fun i c => (h i c).2⟩,
    fun j l => rfl⟩

theorem hC_E6 {p : ℕ} [Fact p.Prime] [CharP F p] :
    ∀ N : Subgroup ↥(e6Data_valid.minGroup F), N ≤ Subgroup.center _ → ¬ p ∣ Nat.card N := by
  intro N hN
  have := finite_minGroup e6Data_valid F
  exact not_dvd_card_of_forall_pow_card_sub_one (F := F) fun z hz =>
    center_pow_eq_one (e6Datum_isCTGroupDatum F) (e6Datum_steinbergExtras F)
      (e6Datum_bruhatExtras F) (fun i h hh => torus_pow_card_sub_one e6Data_valid F i hh) z
      (hN hz)

theorem hC_E7 {p : ℕ} [Fact p.Prime] [CharP F p] :
    ∀ N : Subgroup ↥(e7Data_valid.minGroup F), N ≤ Subgroup.center _ → ¬ p ∣ Nat.card N := by
  intro N hN
  have := finite_minGroup e7Data_valid F
  exact not_dvd_card_of_forall_pow_card_sub_one (F := F) fun z hz =>
    center_pow_eq_one (e7Datum_isCTGroupDatum F) (e7Datum_steinbergExtras F)
      (e7Datum_bruhatExtras F) (fun i h hh => torus_pow_card_sub_one e7Data_valid F i hh) z
      (hN hz)

theorem hC_E8 {p : ℕ} [Fact p.Prime] :
    ∀ N : Subgroup ↥(adjointGroup Tag.E8 F), N ≤ Subgroup.center _ → ¬ p ∣ Nat.card N := by
  intro N hN
  have hZ : Subgroup.center ↥(adjointGroup Tag.E8 F) = ⊥ := center_adjointGroup_eq_bot
  have : N = ⊥ := le_bot_iff.1 (hZ ▸ hN)
  rw [this, Subgroup.card_bot]
  exact (Fact.out : p.Prime).not_dvd_one

theorem toral_E6 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : ↥(e6Data_valid.minGroup F) →* Y)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup F)) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : ↥(e6Data_valid.minGroup F))
    (hfix : ∀ i, ∀ h ∈ e6Data_valid.torus F i, σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹)) :
    ∃ v : Fin Tag.E6.rank → ZMod 2, ∀ γ ∈ (e6Datum F).roots,
      ((∀ y ∈ (conjSub k₀ ((e6Datum F).rootGroup γ ⊔ (e6Datum F).rootGroup (-γ))).map ψ,
          σ y = y) ↔ charOf v γ = 0) := by
  have hS := torusSetup_E6 F
  have hfin := finite_minGroup e6Data_valid F
  exact toral_ambient (p := p) hS (liftsToNormalForm_E6 F) hp2 hq (by show 0 < 6; norm_num)
    (fun k => isLongest_single_E6 rfl _ k) cartanE6_nb cartanE6_offDiag (hC_E6 F) ψ hψ σ hσ2 hσr
    k₀ (fun i s => hfix i _ ((hS.H_iff i _).2 ⟨s, rfl⟩))

theorem toral_E7 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : ↥(e7Data_valid.minGroup F) →* Y)
    (hψ : ψ.ker ≤ Subgroup.center ↥(e7Data_valid.minGroup F)) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : ↥(e7Data_valid.minGroup F))
    (hfix : ∀ i, ∀ h ∈ e7Data_valid.torus F i, σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹)) :
    ∃ v : Fin Tag.E7.rank → ZMod 2, ∀ γ ∈ (e7Datum F).roots,
      ((∀ y ∈ (conjSub k₀ ((e7Datum F).rootGroup γ ⊔ (e7Datum F).rootGroup (-γ))).map ψ,
          σ y = y) ↔ charOf v γ = 0) := by
  have hS := torusSetup_E7 F
  have hfin := finite_minGroup e7Data_valid F
  exact toral_ambient (p := p) hS (liftsToNormalForm_E7 F) hp2 hq (by show 0 < 7; norm_num)
    (fun k => isLongest_single_E7 rfl _ k) cartanE7_nb cartanE7_offDiag (hC_E7 F) ψ hψ σ hσ2 hσr
    k₀ (fun i s => hfix i _ ((hS.H_iff i _).2 ⟨s, rfl⟩))

theorem toral_E8 {p : ℕ} [Fact p.Prime] [CharP F p] (hp2 : p ≠ 2) (hq : 5 ≤ Nat.card F)
    {Y : Type} [Group Y] (ψ : ↥(adjointGroup Tag.E8 F) →* Y)
    (hψ : ψ.ker ≤ Subgroup.center ↥(adjointGroup Tag.E8 F)) (σ : Y ≃* Y)
    (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (ψ k) ∈ ψ.range) (k₀ : ↥(adjointGroup Tag.E8 F))
    (hfix : ∀ i, ∀ h ∈ Adjoint.torus (τ := Tag.E8) F i,
      σ (ψ (k₀ * h * k₀⁻¹)) = ψ (k₀ * h * k₀⁻¹)) :
    ∃ v : Fin Tag.E8.rank → ZMod 2, ∀ γ ∈ (Adjoint.e8Datum F).roots,
      ((∀ y ∈ (conjSub k₀ ((Adjoint.e8Datum F).rootGroup γ ⊔
          (Adjoint.e8Datum F).rootGroup (-γ))).map ψ, σ y = y) ↔ charOf v γ = 0) := by
  have hS := torusSetup_E8 F
  exact toral_ambient (p := p) hS (liftsToNormalForm_E8 F) hp2 hq (by show 0 < 8; norm_num)
    (fun k => isLongest_single_E8 rfl _ k) cartanE8_nb cartanE8_offDiag (hC_E8 F) ψ hψ σ hσ2 hσr
    k₀ (fun i s => hfix i _ ((hS.H_iff i _).2 ⟨s, rfl⟩))

end Families

end CFSG.ClassicalInvolution.ModelFacts.ChevAut
