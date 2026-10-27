module

public import CFSG.GH74.GLS.IVK.Proofs2.Stmt111c

public section

namespace CFSG.GH74.GLS.SP.Local

open CFSG.GH74.GLS CFSG.GH74.GLS.IVK

theorem exists_addEquiv_of_resRep_asModule_equiv {k : Type} [CommSemiring k] {G : Type} [Group G]
    {A A' : Type} [AddCommGroup A] [AddCommGroup A'] [Module k A] [Module k A']
    (ρ : Representation k G A) (ρ' : Representation k G A') (S : Subgroup G)
    (e : (resRep ρ S).asModule ≃ₗ[MonoidAlgebra k S] (resRep ρ' S).asModule) :
    ∃ φ : A ≃+ A', ∀ (s : S) (a : A), φ (ρ s a) = ρ' s (φ a) := by
  refine ⟨((resRep ρ S).asModuleEquiv.symm.toAddEquiv.trans e.toAddEquiv).trans
    (resRep ρ' S).asModuleEquiv.toAddEquiv, ?_⟩
  intro s a
  have h1 : (resRep ρ S).asModuleEquiv.symm (ρ s a) =
      MonoidAlgebra.of k S s • (resRep ρ S).asModuleEquiv.symm a :=
    Representation.asModuleEquiv_symm_map_rho (resRep ρ S) s a
  show (resRep ρ' S).asModuleEquiv (e ((resRep ρ S).asModuleEquiv.symm (ρ s a))) =
    ρ' s ((resRep ρ' S).asModuleEquiv (e ((resRep ρ S).asModuleEquiv.symm a)))
  rw [h1, map_smul, Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_of]
  rfl

theorem natural_module_of_11_1b (h11 : CFSG.GH74.GLS.IVK.Proofs2.IVK_11_1b_nat) {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {Fq : Type} [Field Fq] [Finite Fq] (hq : Nat.card Fq = p ^ n)
    {K : Type} [Group K] (ε : K ≃* Matrix.SpecialLinearGroup (Fin 2) Fq)
    {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ p = 1)
    (hcard : Nat.card V = p ^ (2 * n))
    (ρ : K →* MulAut V) (hfaith : Function.Injective ρ) :
    ∃ τ : V ≃* Multiplicative (Fin 2 → Fq), ∀ (k : K) (v : V),
      τ (ρ k v) = Multiplicative.ofAdd
        (((ε k : Matrix.SpecialLinearGroup (Fin 2) Fq) : Matrix (Fin 2) (Fin 2) Fq).mulVec
          (Multiplicative.toAdd (τ v))) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have hchar : CharP Fq p := by
    have : Fintype Fq := Fintype.ofFinite Fq
    exact charP_of_card_eq_prime_pow (p := p) (f := n) (by rw [← Nat.card_eq_fintype_card, hq])
  have hKfin : Finite K := Finite.of_equiv _ ε.symm.toEquiv
  have hmodV : ∀ x : Additive V, p • x = 0 := by
    intro x
    have := hexp (Additive.toMul x)
    simpa using congrArg Additive.ofMul this
  have hmodF : ∀ x : Fin 2 → Fq, p • x = 0 := by
    intro x
    ext i
    simp [nsmul_eq_mul]
  let _ : Module (ZMod p) (Additive V) := AddCommGroup.zmodModule (n := p) hmodV
  let _ : Module (ZMod p) (Fin 2 → Fq) := AddCommGroup.zmodModule (n := p) hmodF
  have hrk1 : Module.finrank (ZMod p) (Additive V) = 2 * n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Additive V)
    rw [Nat.card_zmod] at h
    have h2 : Nat.card (Additive V) = p ^ (2 * n) := by
      rw [← hcard]
      exact Nat.card_congr Additive.toMul
    rw [h2] at h
    exact Nat.pow_right_injective hp.two_le h.symm
  have hrk2 : Module.finrank (ZMod p) (Fin 2 → Fq) = 2 * n := by
    have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := Fin 2 → Fq)
    rw [Nat.card_zmod, Nat.card_fun, hq, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin,
      ← pow_mul, mul_comm] at h
    exact Nat.pow_right_injective hp.two_le h.symm
  let ρ' : Representation (ZMod p) K (Additive V) :=
    { toFun := fun k => ((MulEquiv.toAdditive (ρ k)).toAddMonoidHom).toZModLinearMap p
      map_one' := by
        ext x
        simp
      map_mul' := fun k l => by
        ext x
        simp }
  let ρ'' : Representation (ZMod p) K (Fin 2 → Fq) :=
    { toFun := fun k => ((Matrix.mulVecLin ((ε k : Matrix.SpecialLinearGroup (Fin 2) Fq) :
          Matrix (Fin 2) (Fin 2) Fq)).toAddMonoidHom).toZModLinearMap p
      map_one' := by
        ext x : 1
        simp
      map_mul' := fun k l => by
        ext x : 1
        simp }
  have hρ' : ∀ (k : K) (x : Additive V), ρ' k x = Additive.ofMul (ρ k (Additive.toMul x)) :=
    fun k x => rfl
  have hρ'' : ∀ (k : K) (x : Fin 2 → Fq), ρ'' k x =
      (((ε k : Matrix.SpecialLinearGroup (Fin 2) Fq) : Matrix (Fin 2) (Fin 2) Fq)).mulVec x :=
    fun k x => rfl
  have hinj' : Function.Injective ρ' := by
    intro k l hkl
    apply hfaith
    ext v
    have := congrArg (fun f => Additive.toMul (f (Additive.ofMul v))) hkl
    simpa [hρ'] using this
  have hinj'' : Function.Injective ρ'' := by
    intro k l hkl
    apply ε.injective
    apply Subtype.ext
    rw [Matrix.ext_iff_mulVec]
    intro v
    have := congrArg (fun f => f v) hkl
    simpa [hρ''] using this
  have hmodel : HasSL2Model ↥(⊤ : Subgroup K) (fun r => r = p ^ n) :=
    ⟨Fq, inferInstance, inferInstance, hq,
      ⟨(Subgroup.topEquiv.trans ε).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 Fq)⟩⟩
  obtain ⟨-, -, huniq⟩ := h11 p n hp hp2 K ⊤ hmodel (Additive V) ρ' hinj' hrk1
  obtain ⟨e⟩ := huniq (Fin 2 → Fq) ρ'' hinj'' hrk2
  obtain ⟨φ, hφ⟩ := exists_addEquiv_of_resRep_asModule_equiv ρ' ρ'' ⊤ e
  refine ⟨AddEquiv.toMultiplicativeRight φ, fun k v => ?_⟩
  exact congrArg Multiplicative.ofAdd (hφ ⟨k, Subgroup.mem_top k⟩ (Additive.ofMul v))

end CFSG.GH74.GLS.SP.Local
