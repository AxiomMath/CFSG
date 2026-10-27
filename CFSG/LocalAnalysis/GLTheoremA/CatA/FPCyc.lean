module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS09Field
public import CFSG.LocalAnalysis.GLTheoremA.CatA.MIBase

public section

namespace CFSG.LocalAnalysis.GLTheoremA

namespace FP

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA.YS09Field

section Graph

variable {M R S : Type*} [Group M] [Group R] [Group S]

theorem graph_mul (H : Subgroup M) (π : H →* R) (act : S → M → M)
    (hactmul : ∀ a b x, act (a * b) x = act a (act b x)) (hstab : ∀ a (h : H), act a h ∈ H)
    (rel : S → H → H → Prop) (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h)
    {a b : S} {f g : MulAut R} (hf : LargeEvenGraphAut π (rel a) f)
    (hg : LargeEvenGraphAut π (rel b) g) : LargeEvenGraphAut π (rel (a * b)) (f * g) := by
  intro h h' hh'
  let h1 : H := ⟨act b h, hstab _ h⟩
  have e1 : g (π h) = π h1 := hg h h1 ((hrel b h h1).2 rfl)
  let h2 : H := ⟨act a h1, hstab _ h1⟩
  have e2 : f (π h1) = π h2 := hf h1 h2 ((hrel a h1 h2).2 rfl)
  have e3 : h' = h2 := Subtype.ext (by
    show (h' : M) = act a (act b h)
    rw [(hrel _ _ _).1 hh', hactmul])
  rw [MulAut.mul_apply, e1, e2, e3]

theorem graph_unique (H : Subgroup M) (π : H →* R) (hπ : Function.Surjective π) (act : S → M → M)
    (hstab : ∀ a (h : H), act a h ∈ H) (rel : S → H → H → Prop)
    (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h) {a : S} {f g : MulAut R}
    (hf : LargeEvenGraphAut π (rel a) f) (hg : LargeEvenGraphAut π (rel a) g) : f = g := by
  ext y
  obtain ⟨h, rfl⟩ := hπ y
  let h' : H := ⟨act a h, hstab a h⟩
  rw [hf h h' ((hrel a h h').2 rfl), hg h h' ((hrel a h h').2 rfl)]

theorem graph_cyclic [Finite S] [IsCyclic S] (H : Subgroup M) (π : H →* R)
    (hπ : Function.Surjective π) (act : S → M → M) (hact1 : ∀ x, act 1 x = x)
    (hactmul : ∀ a b x, act (a * b) x = act a (act b x)) (hstab : ∀ a (h : H), act a h ∈ H)
    (rel : S → H → H → Prop) (hrel : ∀ a h h', rel a h h' ↔ (h' : M) = act a h) :
    ∃ f₀ : MulAut R, ∀ f : MulAut R, (∃ a : S, LargeEvenGraphAut π (rel a) f) →
      f ∈ Subgroup.zpowers f₀ := by
  let T : Submonoid S :=
    { carrier := {a | ∃ f : MulAut R, LargeEvenGraphAut π (rel a) f}
      mul_mem' := fun {a b} ⟨f, hf⟩ ⟨g, hg⟩ => ⟨f * g, graph_mul H π act hactmul hstab rel hrel hf hg⟩
      one_mem' := ⟨1, fun h h' hh' => by
        have : (h' : M) = h := by rw [(hrel _ _ _).1 hh', hact1]
        have e : h' = h := Subtype.ext this
        rw [e]; rfl⟩ }
  let T' : Subgroup S :=
    { T with
      inv_mem' := fun {a} ha => by
        have hpos : 0 < orderOf a := orderOf_pos a
        have h1 : a⁻¹ = a ^ (orderOf a - 1) := by
          apply inv_eq_of_mul_eq_one_right
          rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        rw [h1]
        exact T.pow_mem ha _ }
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := T')
  obtain ⟨f₀, hf₀⟩ := t.2
  refine ⟨f₀, fun f ⟨a, hfa⟩ => ?_⟩
  have haT : a ∈ T' := ⟨f, hfa⟩
  have hmem : (⟨a, haT⟩ : T') ∈ Subgroup.zpowers t := ht _
  obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).1 ((mem_powers_iff_mem_zpowers).2 hmem)
  have hka : (t : S) ^ k = a := congrArg Subtype.val hk
  have h1 := graph_pow (S := S) H π act hact1 hactmul hstab rel hrel (t : S) f₀ hf₀ k
  rw [hka] at h1
  have h2 := graph_unique H π hπ act hstab rel hrel hfa h1
  rw [h2]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers f₀) k

end Graph

section Field

open scoped Matrix

theorem isCyclic_ringEquiv (K : Type) [Field K] [Finite K] : IsCyclic (K ≃+* K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨p, -, n, hp, hK⟩ := FiniteField.card' K
  have hK' : Nat.card K = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hK]
  exact (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K hK').2

theorem finite_ringEquiv (K : Type) [Field K] [Finite K] : Finite (K ≃+* K) :=
  Finite.of_injective (fun σ : K ≃+* K => (σ : K → K)) DFunLike.coe_injective

theorem matField_cyclic {ι K R : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K] [Group R]
    (H : Subgroup (GL ι K))
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ H)
    (π : H →* R) (hπ : Function.Surjective π) :
    ∃ f₀ : MulAut R, ∀ f ∈ LargeEvenMatFieldImage π, f ∈ Subgroup.zpowers f₀ := by
  haveI := isCyclic_ringEquiv K
  haveI := finite_ringEquiv K
  obtain ⟨f₀, hf₀⟩ := graph_cyclic (S := K ≃+* K) H π hπ
    (fun τ g => Matrix.GeneralLinearGroup.map τ.toRingHom g) glMap_one glMap_mul
    (fun τ h => hH τ h h.2)
    (fun τ h h' => ((h' : GL ι K) : Matrix ι ι K) = ((h : GL ι K) : Matrix ι ι K).map τ.toRingHom)
    (fun τ h h' => by rw [Units.ext_iff, coe_glMap])
  exact ⟨f₀, fun f ⟨σ, hσ⟩ => hf₀ f ⟨σ, hσ⟩⟩

theorem chevField_cyclic {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (K : Type) [Field K] [Finite K]
    (H : Subgroup (LargeEvenChevGL A K)) (hH : ∀ σ : K ≃+* K, ∀ h ∈ H, chevAct A K σ h ∈ H) :
    ∃ f₀ : MulAut (LargeEvenCenterQuot H), ∀ f ∈ LargeEvenChevFieldImage A K H,
      f ∈ Subgroup.zpowers f₀ := by
  haveI := isCyclic_ringEquiv K
  haveI := finite_ringEquiv K
  obtain ⟨f₀, hf₀⟩ := graph_cyclic (S := K ≃+* K) H (LargeEvenCenterMk H)
    (QuotientGroup.mk'_surjective _) (fun τ g => chevAct A K τ g) (chevAct_one A K)
    (fun a b x => chevAct_mul A K a b x) (fun τ h => hH τ h h.2)
    (fun τ h h' => ((h' : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)) =
      LargeEvenEntrywise A K τ (map_zero τ)
        ((h : LargeEvenChevGL A K) : Module.End K (LargeEvenChevModule A K)))
    (fun τ h h' => by rw [Units.ext_iff, chevAct_val])
  exact ⟨f₀, fun f ⟨σ, hσ⟩ => hf₀ f ⟨σ, hσ⟩⟩

theorem phiQ_cyclic {n : ℕ} (hn4 : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ f₀ : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))),
      ∀ f ∈ LargeEvenPhiQ (n - 1) b c
        (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus (n - 1) b c))),
        f ∈ Subgroup.zpowers f₀ := by
  obtain ⟨φ, -, hφe⟩ :=
    CFSG.StandardType.RecipeFieldOmega.exists_mem_phi_congr_minusEquiv hn4 hirr 1
  refine ⟨φ, fun f hf => ?_⟩
  obtain ⟨k, hk⟩ := CFSG.StandardType.RecipeFieldOmega.congr_minusEquiv_of_mem_phi hn4 hirr hf
  refine Subgroup.mem_zpowers_iff.2 ⟨(k : ℤ), ?_⟩
  apply (MulAut.congr (CFSG.StandardType.RecipeFieldOmega.minusEquiv hn4 b c)).injective
  rw [zpow_natCast, map_pow, hφe, hk, pow_one]

end Field

section Dispatch

@[expose] def FieldCyc : LargeEvenRawCont := fun R _ _ F =>
  ∃ f₀ : MulAut R, ∀ f ∈ F, f ∈ Subgroup.zpowers f₀

abbrev CycCont (Q : LargeEvenRawCont) : LargeEvenRawCont :=
  fun R _ I F => Q R I F ∧ FieldCyc R I F

theorem recLinear_cyc {d N : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, matField_cyclic _ (fun σ g hg => sl_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _)⟩⟩

theorem recUnitary_cyc {d q : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeUnitary d q Q) :
    LargeEvenRecipeUnitary d q (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, matField_cyclic _ (fun σ g hg => su_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _)⟩⟩

theorem recSymplectic_cyc {m q : ℕ} (derived : Bool) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeSymplectic m q derived Q) :
    LargeEvenRecipeSymplectic m q derived (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  have hH : ∀ σ : K ≃+* K, ∀ g ∈ (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆
      else LargeEvenSpGroup K m), Matrix.GeneralLinearGroup.map σ.toRingHom g ∈
      (if derived then ⁅LargeEvenSpGroup K m, LargeEvenSpGroup K m⁆ else LargeEvenSpGroup K m) := by
    intro σ g hg
    cases derived
    · exact sp_map_mem σ g hg
    · exact derived_stable _ _ (fun x hx => sp_map_mem σ x hx) hg
  exact ⟨K, hF, hfin, hK, ⟨hQ, matField_cyclic _ hH _ (QuotientGroup.mk'_surjective _)⟩⟩

theorem recOmegaPlus_cyc {m q : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeOmegaPlus m q Q) :
    LargeEvenRecipeOmegaPlus m q (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, matField_cyclic _ (fun σ g hg => omegaPlus_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _)⟩⟩

theorem recSuzuki_cyc {a : ℕ} (Q : LargeEvenRawCont) (h : LargeEvenRecipeSuzuki a Q) :
    LargeEvenRecipeSuzuki a (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, matField_cyclic _ (fun σ g hg => sz_map_mem σ g hg) _
    (QuotientGroup.mk'_surjective _)⟩⟩

theorem recOmegaMinus_cyc {n j : ℕ} (hn4 : 4 ≤ n) (Q : LargeEvenRawCont)
    (h : LargeEvenRecipeOmegaMinus (n - 1) (2 ^ j) Q) :
    LargeEvenRecipeOmegaMinus (n - 1) (2 ^ j) (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, b, c, hirr, hQ⟩ := h
  haveI : CharP K 2 := charP_two_of_card_two_pow hK
  exact ⟨K, hF, hfin, hK, b, c, hirr, ⟨hQ, phiQ_cyclic hn4 hirr⟩⟩

theorem recChevalley_cyc {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) {q : ℕ} (derived : Bool)
    (Q : LargeEvenRawCont) (h : LargeEvenRecipeChevalley A q derived Q) :
    LargeEvenRecipeChevalley A q derived (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, chevField_cyclic A K _ (fun σ h hh => chevH_stable A K derived σ h hh)⟩⟩

theorem recG2Derived_cyc (Q : LargeEvenRawCont) (h : LargeEvenRecipeG2Derived Q) :
    LargeEvenRecipeG2Derived (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, chevField_cyclic LargeEvenCartanG2 K _
    (fun σ h hh => chevH_stable LargeEvenCartanG2 K true σ h hh)⟩⟩

theorem recTwisted_cyc {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ) (ρ : Equiv.Perm (Fin r))
    (m n : ℕ) (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwisted A ρ m n Q) :
    LargeEvenRecipeTwisted A ρ m n (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, chevField_cyclic A K _ (fun σ h hh => twisted_map_mem A K ρ n σ h hh)⟩⟩

theorem recTwF4Inherited_cyc (a : ℕ) (Q : LargeEvenRawCont) (h : LargeEvenRecipeTwF4Inherited a Q) :
    LargeEvenRecipeTwF4Inherited a (CycCont Q) := by
  obtain ⟨K, hF, hfin, hK, hQ⟩ := h
  exact ⟨K, hF, hfin, hK, ⟨hQ, chevField_cyclic LargeEvenCartanF4 K _
    (fun σ h hh => twF4H_map_mem K a σ h hh)⟩⟩

theorem canonFieldCyc {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) :
    MI.CAll lab FieldCyc := by
  intro Q h
  obtain ⟨tag, rank, n⟩ := lab
  cases tag
  case A => exact recLinear_cyc _ h
  case twA => exact recUnitary_cyc _ h
  case B => exact recSymplectic_cyc false _ h
  case C => exact recSymplectic_cyc false _ h
  case D =>
    unfold LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢
    · exact recLinear_cyc _ h
    · exact recOmegaPlus_cyc _ h
  case twD =>
    have h2 : 2 ≤ rank := hlab.2
    unfold LargeEvenRawDatum at h ⊢
    dsimp only at h ⊢
    split_ifs at h ⊢ with h2' h3'
    · exact recLinear_cyc _ h
    · exact recUnitary_cyc _ h
    · exact recOmegaMinus_cyc (n := rank) (by omega) _ h
  case E6 => exact recChevalley_cyc (LargeEvenCartanE 6) false _ h
  case E7 => exact recChevalley_cyc (LargeEvenCartanE 7) false _ h
  case E8 => exact recChevalley_cyc (LargeEvenCartanE 8) false _ h
  case F4 => exact recChevalley_cyc LargeEvenCartanF4 false _ h
  case twE6 => exact recTwisted_cyc (LargeEvenCartanE 6) LargeEvenRhoE6 2 n _ h
  case triD4 => exact recTwisted_cyc LargeEvenCartanD4 LargeEvenRhoD4 3 n _ h
  case G2 => exact recChevalley_cyc LargeEvenCartanG2 false _ h
  case twB2 => exact recSuzuki_cyc _ h
  case twF4 => exact recTwF4Inherited_cyc _ _ h
  case B2der => exact recSymplectic_cyc true _ h
  case G2der => exact recG2Derived_cyc _ h
  case twF4der => exact recTwF4Inherited_cyc _ _ h

end Dispatch

end FP

end CFSG.LocalAnalysis.GLTheoremA
