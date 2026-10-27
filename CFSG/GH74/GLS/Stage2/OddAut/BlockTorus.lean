module

public import CFSG.GroupTheory.WeirSylow.GL
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87GenCell

public section

namespace CFSG.GH74.GLS.Stage2.OddAut.BlockTorus

open Module Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section Torus

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

abbrev Lq := FiniteField.Extension K p 2

abbrev Em := (Lq K p × Lq K p) × (Fin s → K)

@[expose] noncomputable def torEnd (u w : Lq K p) : Module.End K (Em K p s) :=
  ((LinearMap.mulLeft K u).prodMap (LinearMap.mulLeft K w)).prodMap LinearMap.id

theorem torEnd_apply (u w : Lq K p) (x y : Lq K p) (z : Fin s → K) :
    torEnd K p s u w ((x, y), z) = ((u * x, w * y), z) := rfl

theorem torEnd_mul (u w u' w' : Lq K p) :
    torEnd K p s u w * torEnd K p s u' w' = torEnd K p s (u * u') (w * w') := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [torEnd_apply, mul_assoc]

theorem torEnd_one : torEnd K p s 1 1 = 1 := by
  refine LinearMap.ext fun ⟨⟨x, y⟩, z⟩ => ?_
  simp [torEnd_apply]

@[expose] noncomputable def torUnit (u w : (Lq K p)ˣ) : (Module.End K (Em K p s))ˣ where
  val := torEnd K p s u w
  inv := torEnd K p s (u⁻¹ : (Lq K p)ˣ) (w⁻¹ : (Lq K p)ˣ)
  val_inv := by rw [torEnd_mul]; simp [torEnd_one]
  inv_val := by rw [torEnd_mul]; simp [torEnd_one]

@[expose] noncomputable def torHom : (Lq K p)ˣ × (Lq K p)ˣ →* (Module.End K (Em K p s))ˣ where
  toFun uw := torUnit K p s uw.1 uw.2
  map_one' := by
    apply Units.ext
    exact torEnd_one K p s
  map_mul' a b := by
    apply Units.ext
    exact (torEnd_mul K p s _ _ _ _).symm

theorem torHom_injective : Function.Injective (torHom K p s) := by
  intro a b h
  have h1 := congrArg (fun U : (Module.End K (Em K p s))ˣ =>
    (U : Module.End K (Em K p s)) (((1 : Lq K p), (1 : Lq K p)), 0)) h
  simp only [torHom, MonoidHom.coe_mk, OneHom.coe_mk, torUnit, torEnd_apply, mul_one] at h1
  have e1 := congrArg (fun t => t.1.1) h1
  have e2 := congrArg (fun t => t.1.2) h1
  exact Prod.ext (Units.ext e1) (Units.ext e2)

end Torus

section Sylow

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] noncomputable def bEm : Module.Basis (Fin (4 + s)) K (Em K p s) :=
  ((Module.finBasisOfFinrankEq K (Lq K p) (FiniteField.finrank_extension K p 2)).prod
    (Module.finBasisOfFinrankEq K (Lq K p) (FiniteField.finrank_extension K p 2))).prod
    (Pi.basisFun K (Fin s)) |>.reindex ((finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv)

@[expose] noncomputable def ΦA : Matrix (Fin (4 + s)) (Fin (4 + s)) K ≃ₐ[K] Module.End K (Em K p s) :=
  Matrix.toLinAlgEquiv'.trans (((bEm K p s).equivFun.symm).conjAlgEquiv K)

@[expose] noncomputable def Φ : GL (Fin (4 + s)) K ≃* (Module.End K (Em K p s))ˣ :=
  Units.mapEquiv (ΦA K p s).toMulEquiv

theorem Φ_val (x : GL (Fin (4 + s)) K) :
    ((Φ K p s x : (Module.End K (Em K p s))ˣ) : Module.End K (Em K p s)) =
      ΦA K p s (x : Matrix (Fin (4 + s)) (Fin (4 + s)) K) := rfl

end Sylow

section Sylow2

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] noncomputable def torRange (ζ : (Lq K p)ˣ) : Subgroup (Module.End K (Em K p s))ˣ :=
  ((torHom K p s).comp ((Subgroup.zpowers ζ).subtype.prodMap (Subgroup.zpowers ζ).subtype)).range

theorem card_torRange (ζ : (Lq K p)ˣ) :
    Nat.card (torRange K p s ζ) = orderOf ζ ^ 2 := by
  unfold torRange
  have hinj : Function.Injective ((torHom K p s).comp
      ((Subgroup.zpowers ζ).subtype.prodMap (Subgroup.zpowers ζ).subtype)) := by
    refine (torHom_injective K p s).comp ?_
    intro a b h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, Nat.card_zpowers, sq]

theorem mem_torRange {ζ : (Lq K p)ˣ} {g : (Module.End K (Em K p s))ˣ} (hg : g ∈ torRange K p s ζ) :
    ∃ u w : (Lq K p)ˣ, g = torHom K p s (u, w) := by
  obtain ⟨⟨u, w⟩, rfl⟩ := hg
  exact ⟨u, w, rfl⟩

end Sylow2

section Sylow3

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem exists_conj_le_of_isPGroup {G : Type*} [Group G] [Finite G] {r : ℕ} [Fact r.Prime]
    {S W : Subgroup G} (hSp : IsPGroup r S) (hS : ¬ r ∣ S.index) (hW : IsPGroup r W) :
    ∃ g : G, ∀ x ∈ W, g⁻¹ * x * g ∈ S := by
  obtain ⟨Q, hQ⟩ := hW.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G (hSp.toSylow hS) Q
  refine ⟨g, fun x hx => ?_⟩
  have h1 : x ∈ ((g • hSp.toSylow hS : Sylow r G) : Subgroup G) := by rw [hg]; exact hQ hx
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at h1
  obtain ⟨s, hs, rfl⟩ := h1
  have hs' : s ∈ S := by simpa using hs
  have : g⁻¹ * (MulAut.conj g • s) * g = s := by
    simp [MulAut.smul_def, MulAut.conj_apply, mul_assoc]
  rw [this]; exact hs'

omit [Field K] [Finite K] in
theorem orderOf_card_eq_two {r : ℕ} [Fact r.Prime] (hr2 : Odd r)
    (hrq : (Nat.card K : ZMod r) = -1) : orderOf (Nat.card K : ZMod r) = 2 := by
  rw [hrq]
  have hne : ringChar (ZMod r) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    rintro rfl
    exact absurd hr2 (by decide)
  simp [hne]

end Sylow3

section Sylow4

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem torus_conj {r : ℕ} [Fact r.Prime] (hr2 : Odd r) (hrq : (Nat.card K : ZMod r) = -1)
    (hs : s ≤ 1) (W : Subgroup (GL (Fin (4 + s)) K)) (hW : IsPGroup r W) :
    ∃ g : GL (Fin (4 + s)) K, ∀ x ∈ W, ∃ u w : (Lq K p)ˣ,
      Φ K p s (g⁻¹ * x * g) = torHom K p s (u, w) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hr : r.Prime := Fact.out
  have hrK : ¬ r ∣ Fintype.card K := by
    intro h
    have h0 : ((Fintype.card K : ℕ) : ZMod r) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h
    rw [Fintype.card_eq_nat_card, hrq] at h0
    have : (1 : ZMod r) = 0 := neg_eq_zero.mp h0
    exact one_ne_zero this
  set a := padicValNat r (Nat.card K ^ 2 - 1) with ha
  have hdvd : r ^ a ∣ Nat.card (Lq K p) - 1 := by
    rw [FiniteField.natCard_extension]
    exact pow_padicValNat_dvd
  obtain ⟨ζ, hζ⟩ := CFSG.GroupTheory.WeirSylow.exists_units_orderOf_eq (L := Lq K p) hdvd
  set S := torRange K p s ζ with hS
  have hScard : Nat.card S = r ^ (2 * a) := by
    rw [hS, card_torRange, hζ, ← pow_mul]; ring_nf
  have hSp : IsPGroup r S := IsPGroup.of_card hScard
  have : Finite (Module.End K (Em K p s))ˣ := Finite.of_equiv _ (Φ K p s).toEquiv
  have hG : Nat.card (Module.End K (Em K p s))ˣ = Nat.card (GL (Fin (4 + s)) K) :=
    (Nat.card_congr (Φ K p s).toEquiv).symm
  have hfac : (Nat.card (GL (Fin (4 + s)) K)).factorization r = 2 * a := by
    have h := CFSG.GroupTheory.WeirSylow.factorization_card_GL hr2 K hrK (4 + s)
    simp only [Fintype.card_eq_nat_card] at h
    rw [orderOf_card_eq_two K hr2 hrq] at h
    have h42 : (4 + s) / 2 = 2 := by omega
    rw [h42] at h
    rw [h]
    have h2 : padicValNat r (Nat.factorial 2) = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro hd
      have : r ∣ 2 := by simpa [Nat.factorial] using hd
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp this
      subst this
      exact absurd hr2 (by decide)
    rw [h2, add_zero, mul_comm]
  have hidx : ¬ r ∣ S.index := by
    have h1 := Subgroup.card_mul_index S
    rw [hG] at h1
    have hS0 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 := congrArg (fun n => n.factorization r) h1
    rw [Nat.factorization_mul (by rw [hScard]; exact pow_ne_zero _ hr.ne_zero) hS0, hScard,
      Nat.factorization_pow, hfac] at h2
    simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, hr.factorization_self] at h2
    rw [hr.dvd_iff_one_le_factorization hS0]
    omega
  have hWG : IsPGroup r (W.map (Φ K p s).toMonoidHom) :=
    hW.of_equiv (Subgroup.equivMapOfInjective W (Φ K p s).toMonoidHom (Φ K p s).injective)
  obtain ⟨gG, hgG⟩ := exists_conj_le_of_isPGroup hSp hidx hWG
  refine ⟨(Φ K p s).symm gG, fun x hx => ?_⟩
  have h1 := hgG (Φ K p s x) ⟨x, hx, rfl⟩
  have h2 : Φ K p s (((Φ K p s).symm gG)⁻¹ * x * (Φ K p s).symm gG) =
      gG⁻¹ * Φ K p s x * gG := by
    simp [map_mul, map_inv]
  rw [h2]
  exact mem_torRange K p s h1

end Sylow4

section Coord

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem ΦA_apply (M : Matrix (Fin (4 + s)) (Fin (4 + s)) K) (v : Em K p s) :
    ΦA K p s M v = (bEm K p s).equivFun.symm (M *ᵥ (bEm K p s).equivFun v) := by
  simp [ΦA, LinearEquiv.conjAlgEquiv_apply, Matrix.toLinAlgEquiv'_apply]

theorem ΦA_single (i j : Fin (4 + s)) (t : K) :
    ΦA K p s (Matrix.single i j t) = t • ((bEm K p s).coord j).smulRight ((bEm K p s) i) := by
  refine LinearMap.ext fun v => ?_
  rw [ΦA_apply]
  simp only [Matrix.single_mulVec, LinearMap.smul_apply, LinearMap.smulRight_apply,
    Module.Basis.coord_apply, Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_apply]
  rw [Finset.sum_eq_single i]
  · simp [mul_smul]
  · intro k _ hk
    simp [Function.update_of_ne hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

end Coord

section SLE

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem det_ΦA (M : Matrix (Fin (4 + s)) (Fin (4 + s)) K) :
    LinearMap.det (ΦA K p s M) = M.det := by
  have h := LinearMap.det_conj (Matrix.toLin' M) ((bEm K p s).equivFun.symm)
  rw [LinearMap.det_toLin'] at h
  simp only [ΦA, AlgEquiv.trans_apply, LinearEquiv.conjAlgEquiv_apply]
  exact h

end SLE

section SLE2

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

@[expose] noncomputable def SLE : Subgroup (Module.End K (Em K p s))ˣ where
  carrier := {f | LinearMap.det (f : Module.End K (Em K p s)) = 1}
  mul_mem' := fun {f g} hf hg => by
    have hf' : LinearMap.det (f : Module.End K (Em K p s)) = 1 := hf
    have hg' : LinearMap.det (g : Module.End K (Em K p s)) = 1 := hg
    show LinearMap.det ((f * g : (Module.End K (Em K p s))ˣ) : Module.End K (Em K p s)) = 1
    rw [Units.val_mul, map_mul, hf', hg', one_mul]
  one_mem' := by
    show LinearMap.det (((1 : (Module.End K (Em K p s))ˣ)) : Module.End K (Em K p s)) = 1
    simp
  inv_mem' := fun {f} hf => by
    have hf' : LinearMap.det (f : Module.End K (Em K p s)) = 1 := hf
    show LinearMap.det ((f⁻¹ : (Module.End K (Em K p s))ˣ) : Module.End K (Em K p s)) = 1
    have h := congrArg (LinearMap.det : Module.End K (Em K p s) →* K)
      (show ((f⁻¹ : (Module.End K (Em K p s))ˣ) : Module.End K (Em K p s)) * (f : Module.End K (Em K p s)) = 1 from by
        rw [← Units.val_mul, inv_mul_cancel, Units.val_one])
    rw [map_mul, hf', mul_one, map_one] at h
    exact h

theorem mem_SLE {f : (Module.End K (Em K p s))ˣ} :
    f ∈ SLE K p s ↔ LinearMap.det (f : Module.End K (Em K p s)) = 1 := Iff.rfl

theorem det_symm_ΦA (f : Module.End K (Em K p s)) :
    ((ΦA K p s).symm f).det = LinearMap.det f := by
  have := det_ΦA K p s ((ΦA K p s).symm f)
  rw [AlgEquiv.apply_symm_apply] at this
  exact this.symm

@[expose] noncomputable def mkSL (f : SLE K p s) : Matrix.SpecialLinearGroup (Fin (4 + s)) K :=
  ⟨(ΦA K p s).symm (f.1 : Module.End K (Em K p s)), by rw [det_symm_ΦA]; exact f.2⟩

theorem coe_mkSL (f : SLE K p s) :
    (mkSL K p s f : Matrix (Fin (4 + s)) (Fin (4 + s)) K) =
      (ΦA K p s).symm (f.1 : Module.End K (Em K p s)) := rfl

@[expose] noncomputable def toSL : SLE K p s →* Matrix.SpecialLinearGroup (Fin (4 + s)) K where
  toFun := mkSL K p s
  map_one' := Subtype.ext (by rw [coe_mkSL]; simp)
  map_mul' f g := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, coe_mkSL, coe_mkSL, coe_mkSL, Subgroup.coe_mul,
      Units.val_mul, map_mul])

theorem ΦA_toSL (f : SLE K p s) :
    ΦA K p s ((toSL K p s f : Matrix.SpecialLinearGroup (Fin (4 + s)) K) :
      Matrix (Fin (4 + s)) (Fin (4 + s)) K) = (f.1 : Module.End K (Em K p s)) := by
  show ΦA K p s (mkSL K p s f : Matrix (Fin (4 + s)) (Fin (4 + s)) K) = _
  rw [coe_mkSL]; simp

@[expose] noncomputable def rho (g : GL (Fin (4 + s)) K) : SLE K p s →* projectiveSL (4 + s) K :=
  ((conjAut (4 + s) K g).toMonoidHom).comp ((proj (4 + s) K).comp (toSL K p s))

end SLE2

section Fixing

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

theorem rho_mem_fixSub (g x : GL (Fin (4 + s)) K) (f : SLE K p s)
    (hcomm : (Φ K p s (g⁻¹ * x * g) : Module.End K (Em K p s)) * (f.1 : Module.End K (Em K p s)) =
      (f.1 : Module.End K (Em K p s)) * (Φ K p s (g⁻¹ * x * g) : Module.End K (Em K p s))) :
    rho K p s g f ∈ fixSub (conjAut (4 + s) K x) := by
  rw [mem_fixSub]
  show conjAut (4 + s) K x (conjAut (4 + s) K g (proj (4 + s) K (toSL K p s f))) =
    conjAut (4 + s) K g (proj (4 + s) K (toSL K p s f))
  set x' : GL (Fin (4 + s)) K := g⁻¹ * x * g with hx'
  set M := toSL K p s f with hM
  have hx : x = g * x' * g⁻¹ := by rw [hx']; group
  have hcm : (x' : Matrix (Fin (4 + s)) (Fin (4 + s)) K) *
      (M : Matrix (Fin (4 + s)) (Fin (4 + s)) K) =
      (M : Matrix (Fin (4 + s)) (Fin (4 + s)) K) * (x' : Matrix (Fin (4 + s)) (Fin (4 + s)) K) := by
    apply (ΦA K p s).injective
    rw [map_mul, map_mul, hM, ΦA_toSL]
    exact hcomm
  have hconj : conjAut (4 + s) K x' (proj (4 + s) K M) = proj (4 + s) K M := by
    rw [conjAut_proj]
    congr 1
    apply Subtype.ext
    rw [coe_slConjugation, Units.mul_inv_eq_iff_eq_mul]
    exact hcm
  rw [hx, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, map_inv, MulAut.inv_apply_self,
    hconj]

end Fixing


section Blocks

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p] (s : ℕ)

noncomputable abbrev bLq : Module.Basis (Fin 2) K (Lq K p) :=
  Module.finBasisOfFinrankEq K (Lq K p) (FiniteField.finrank_extension K p 2)

@[expose] noncomputable def Bs : Module.Basis ((Fin 2 ⊕ Fin 2) ⊕ Fin s) K (Em K p s) :=
  ((bLq K p).prod (bLq K p)).prod (Pi.basisFun K (Fin s))

@[expose] def eSum : ((Fin 2 ⊕ Fin 2) ⊕ Fin s) ≃ Fin (4 + s) :=
  (finSumFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv

theorem bEm_eq : bEm K p s = (Bs K p s).reindex (eSum s) := rfl

theorem ΦA_single' (a b : (Fin 2 ⊕ Fin 2) ⊕ Fin s) (t : K) :
    ΦA K p s (Matrix.single (eSum s a) (eSum s b) t) =
      t • ((Bs K p s).coord b).smulRight ((Bs K p s) a) := by
  rw [ΦA_single, bEm_eq]
  have h1 : ((Bs K p s).reindex (eSum s)).coord (eSum s b) = (Bs K p s).coord b := by
    refine LinearMap.ext fun v => ?_
    simp [Module.Basis.coord_apply]
  rw [h1, Module.Basis.reindex_apply, Equiv.symm_apply_apply]

end Blocks

end CFSG.GH74.GLS.Stage2.OddAut.BlockTorus
