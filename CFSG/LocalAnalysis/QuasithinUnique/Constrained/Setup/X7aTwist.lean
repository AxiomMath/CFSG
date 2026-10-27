module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aGLTwist
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aSelfDualRank

public section

namespace CFSG.QuasithinUnique.Setup.X7a

open scoped MatrixGroups Matrix

open CFSG.QuasithinUnique.Setup.X7 (matRep matRep_apply matMap matMap_apply MatIso dualMat
  dualMat_apply)

section Descent2

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem exists_fixed_mem {ι : Type} (hF : Fintype.card F = 2 ^ f) (S : Submodule F (ι → F))
    (hΦ : ∀ v ∈ S, (fun i => v i ^ 2) ∈ S) (hS : S ≠ ⊥) :
    ∃ y : ι → ZMod 2, y ≠ 0 ∧ (fun i => ZMod.castHom (dvd_refl 2) F (y i)) ∈ S := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  obtain ⟨v, hvM, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, v i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  obtain ⟨b, hb⟩ := trace_exists hF
  set lam : F := b / v i₀ with hlam
  have hw : ∀ j : ℕ, (fun i => (lam * v i) ^ 2 ^ j) ∈ S := by
    intro j
    induction j with
    | zero =>
      have : (fun i => (lam * v i) ^ 2 ^ 0) = lam • v := by
        funext i
        simp
      rw [this]
      exact S.smul_mem lam hvM
    | succ j ih =>
      have := hΦ _ ih
      convert this using 1
      funext i
      rw [← pow_mul, pow_succ]
  set u : ι → F := fun i => ∑ j ∈ Finset.range f, (lam * v i) ^ 2 ^ j with hu
  have huS : u ∈ S := by
    have : u = ∑ j ∈ Finset.range f, (fun i => (lam * v i) ^ 2 ^ j) := by
      funext i
      simp [hu, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun j _ => hw j
  have hu0 : u i₀ ≠ 0 := by
    have : lam * v i₀ = b := by
      rw [hlam, div_mul_cancel₀ _ hi₀]
    simpa [hu, this] using hb
  have hu2 : ∀ i, u i ^ 2 = u i := fun i => trace_sq hF _
  let y : ι → ZMod 2 := fun i => if u i = 0 then 0 else 1
  have hy : (fun i => φ (y i)) = u := by
    funext i
    by_cases h : u i = 0
    · simp [y, h]
    · have h1 : u i = 1 := by
        have : u i * (u i - 1) = 0 := by
          rw [mul_sub, mul_one, ← sq, hu2, sub_self]
        rcases mul_eq_zero.mp this with h2 | h2
        · exact absurd h2 h
        · exact sub_eq_zero.mp h2
      simp [y, h1]
  refine ⟨y, ?_, by rw [hy]; exact huS⟩
  intro h0
  apply hu0
  rw [← hy]
  simp [h0]

theorem exists_zmod_intertwiner {G : Type} [Group G] {n : ℕ} (hF : Fintype.card F = 2 ^ f)
    (R₁ R₂ : G →* Matrix (Fin n) (Fin n) (ZMod 2)) (M : Matrix (Fin n) (Fin n) F) (hM0 : M ≠ 0)
    (hM : ∀ g, M * (R₁ g).map (ZMod.castHom (dvd_refl 2) F) =
      (R₂ g).map (ZMod.castHom (dvd_refl 2) F) * M) :
    ∃ M₀ : Matrix (Fin n) (Fin n) (ZMod 2), M₀ ≠ 0 ∧ ∀ g, M₀ * R₁ g = R₂ g * M₀ := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  let S : Submodule F (Fin n × Fin n → F) :=
    { carrier := {v | ∀ g, Matrix.of (fun a b => v (a, b)) * (R₁ g).map φ =
        (R₂ g).map φ * Matrix.of (fun a b => v (a, b))}
      add_mem' := fun {v w} hv hw g => by
        have e : Matrix.of (fun a b => (v + w) (a, b)) =
            Matrix.of (fun a b => v (a, b)) + Matrix.of (fun a b => w (a, b)) := by
          ext a b
          rfl
        rw [e, Matrix.add_mul, Matrix.mul_add, hv g, hw g]
      zero_mem' := fun g => by
        have e : Matrix.of (fun a b => (0 : Fin n × Fin n → F) (a, b)) = 0 := by
          ext a b
          rfl
        rw [e, Matrix.zero_mul, Matrix.mul_zero]
      smul_mem' := fun c v hv g => by
        have e : Matrix.of (fun a b => (c • v) (a, b)) =
            c • Matrix.of (fun a b => v (a, b)) := by
          ext a b
          rfl
        rw [e, Matrix.smul_mul, Matrix.mul_smul, hv g] }
  let sq : F →+* F := frobeniusEquiv F 2
  have hsqφ : ⇑sq ∘ ⇑φ = ⇑φ := by
    rw [← RingHom.coe_comp, RingHom.ext_zmod (sq.comp φ) φ]
  have hΦ : ∀ v ∈ S, (fun i => v i ^ 2) ∈ S := by
    intro v hv g
    have h1 := congrArg (fun N : Matrix (Fin n) (Fin n) F => N.map sq) (hv g)
    simp only [Matrix.map_mul] at h1
    have h2 : ((R₁ g).map φ).map sq = (R₁ g).map φ := by
      rw [Matrix.map_map, hsqφ]
    have h3 : ((R₂ g).map φ).map sq = (R₂ g).map φ := by
      rw [Matrix.map_map, hsqφ]
    rw [h2, h3] at h1
    have e : Matrix.of (fun a b => (fun i => v i ^ 2) (a, b)) =
        (Matrix.of (fun a b => v (a, b))).map sq := by
      ext a b
      rfl
    rw [e]
    exact h1
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hmem : (fun p : Fin n × Fin n => M p.1 p.2) ∈ S := fun g => hM g
    rw [hbot] at hmem
    apply hM0
    ext a b
    exact congrFun (Submodule.mem_bot F |>.mp hmem) (a, b)
  obtain ⟨y, hy0, hyS⟩ := exists_fixed_mem hF S hΦ hSne
  refine ⟨Matrix.of fun a b => y (a, b), ?_, fun g => ?_⟩
  · intro h
    apply hy0
    funext p
    exact congrFun (congrFun h p.1) p.2
  · have h1 := hyS g
    have e : (Matrix.of fun a b => φ (y (a, b))) = (Matrix.of fun a b => y (a, b)).map φ := rfl
    have h2 : (Matrix.of fun a b => (fun i => φ (y i)) (a, b)) =
        (Matrix.of fun a b => y (a, b)).map φ := rfl
    rw [h2, ← Matrix.map_mul, ← Matrix.map_mul] at h1
    exact Matrix.map_injective φ.injective h1

end Descent2

section Linear

variable {k H : Type} [Field k] [Group H]

theorem exists_matrix_intertwiner {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (R₁ : H →* Matrix κ κ k) (R₂ : H →* Matrix κ' κ' k)
    (T : (κ → k) →ₗ[k] (κ' → k)) (hT : T ≠ 0)
    (hTc : ∀ h v, T ((R₁ h).mulVec v) = (R₂ h).mulVec (T v)) :
    ∃ M : Matrix κ' κ k, M ≠ 0 ∧ ∀ h, M * R₁ h = R₂ h * M := by
  refine ⟨LinearMap.toMatrix' T, fun h0 => hT ?_, fun h => ?_⟩
  · rw [← Matrix.toLin'_toMatrix' T, h0, map_zero]
  · refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact hTc h v

theorem isUnit_of_twist_intertwiner {G : Type} [Group G] {n : ℕ} (R : G →* Matrix (Fin n) (Fin n) k)
    (hirr : ∀ N : Submodule k (Fin n → k), (∀ g, ∀ v ∈ N, (R g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (R₂ : H →* Matrix (Fin n) (Fin n) k) (α : H →* G) (hα : Function.Surjective α)
    (M : Matrix (Fin n) (Fin n) k) (hM0 : M ≠ 0) (hM : ∀ h, M * R (α h) = R₂ h * M) :
    IsUnit M := by
  let N : Submodule k (Fin n → k) := LinearMap.ker M.mulVecLin
  have hN : ∀ g, ∀ v ∈ N, (R g).mulVec v ∈ N := by
    intro g v hv
    obtain ⟨h, rfl⟩ := hα g
    have hv' : M.mulVec v = 0 := hv
    show M.mulVec ((R (α h)).mulVec v) = 0
    rw [Matrix.mulVec_mulVec, hM h, ← Matrix.mulVec_mulVec, hv', Matrix.mulVec_zero]
  rcases hirr N hN with h0 | h1
  · rw [← Matrix.mulVec_injective_iff_isUnit]
    intro x y hxy
    have hxy' : x - y ∈ N := by
      show M.mulVec (x - y) = 0
      rw [Matrix.mulVec_sub, hxy, sub_self]
    rw [h0, Submodule.mem_bot] at hxy'
    exact sub_eq_zero.mp hxy'
  · exfalso
    apply hM0
    ext i j
    have hj : (Pi.single j (1 : k) : Fin n → k) ∈ N := by rw [h1]; trivial
    have h2 : M.mulVec (Pi.single j 1) = 0 := hj
    simpa [Matrix.mulVec_single_one] using congrFun h2 i

end Linear

section Hom

variable {k G : Type} [Field k] [Group G] {V E : Type} [AddCommGroup V] [Module k V]
  [AddCommGroup E] [Module k E]

theorem exists_twist_hom [Nontrivial E] (ρ : Representation k G V) (σ : Representation k G E)
    (α : G →* G) (π : Representation.IntertwiningMap ρ σ) (hπ : Function.Surjective π)
    (W : Subrepresentation ρ) (e : Representation.Equiv (σ.comp α) W.toRepresentation) :
    ∃ T : V →ₗ[k] V, T ≠ 0 ∧ ∀ g v, T (ρ (α g) v) = ρ g (T v) := by
  refine ⟨W.toSubmodule.subtype ∘ₗ e.toLinearEquiv.toLinearMap ∘ₗ π.toLinearMap, ?_, fun g v => ?_⟩
  · intro h
    obtain ⟨x, y, hxy⟩ := exists_pair_ne E
    obtain ⟨v, hv⟩ := hπ (x - y)
    have h1 := LinearMap.congr_fun h v
    have h2 : ((e (π v) : W.toSubmodule) : V) = 0 := h1
    have h3 : e (π v) = 0 := Subtype.ext h2
    have h4 : π v = 0 := by
      have := congrArg e.symm h3
      rwa [Representation.Equiv.symm_apply_apply, map_zero] at this
    rw [hv] at h4
    exact hxy (sub_eq_zero.mp h4)
  · show ((e (π (ρ (α g) v)) : W.toSubmodule) : V) = ρ g ((e (π v) : W.toSubmodule) : V)
    rw [Representation.IntertwiningMap.isIntertwining ρ σ π (α g) v]
    exact congrArg Subtype.val
      (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g (π v))

end Hom

section Galois

open CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7b (TwistEquiv matRepTwist toMatRep matRepEquiv quotProj
  exists_isCoatom_subrep quotient_isIrreducible_of_isCoatom)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f n : ℕ}

theorem exists_galois_family (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (ρ₀ : SL(3, F) →* Matrix (Fin n) (Fin n) (ZMod 2)) (hn : 0 < n)
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) :
    ∃ (a b : Fin f → Bool) (Wj : ℕ → Subrepresentation
        (matRep (matMap (ZMod.castHom (dvd_refl 2) F) ρ₀))),
      (∀ j, (Wj j).toRepresentation.IsIrreducible) ∧
      (∀ j, Nonempty (Representation.Equiv (Wj j).toRepresentation
        (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))))) ∧
      ⨆ j, (Wj j).toSubmodule = ⊤ := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set PF := matMap φ ρ₀ with hPF
  have hτ : ∀ j : ℕ, matMap (frobPowEquiv F j : F →+* F) PF = PF := by
    intro j
    rw [hPF, ← matMap_comp_ringHom]
    congr 1
    exact RingHom.ext_zmod _ _
  let Ψ : ∀ j : ℕ, TwistEquiv (frobPowEquiv F j) (matRep PF) (matRep PF) := fun j =>
    { e := (matRepTwist (frobPowEquiv F j) PF).e
      comm := fun g v => by
        have hent : ∀ i' j', (frobPowEquiv F j) (PF g i' j') = PF g i' j' := fun i' j' =>
          congrFun (congrFun (congrArg (fun R => R g) (hτ j)) i') j'
        funext i
        show frobPowEquiv F j ((PF g).mulVec v i) =
          (PF g).mulVec (fun i' => frobPowEquiv F j (v i')) i
        simp [Matrix.mulVec, dotProduct, map_sum, hent] }
  have hΨ : ∀ (j : ℕ) (w : Fin n → F) (i : Fin n), (Ψ j).e w i = w i ^ 2 ^ j := fun j w i =>
    frobPowEquiv_apply j (w i)
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨W, hW⟩ := exists_atom_subrep (matRep PF)
  have hWirr := isIrreducible_of_atom (matRep PF) W hW
  obtain ⟨a, b, ⟨eW⟩⟩ := exists_T3_equiv F hF hf W.toRepresentation hWirr
  let Wj : ℕ → Subrepresentation (matRep PF) := fun j => (Ψ j).mapSub W
  have hWj : ∀ j, (Wj j).toRepresentation.IsIrreducible := fun j =>
    ((Ψ j).sub W).isIrreducible hWirr
  have heq : ∀ j : ℕ, Nonempty (Representation.Equiv (Wj j).toRepresentation
      (matRep (tensorRep (F := F) F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)))) := by
    intro j
    have h1 := ((Ψ j).sub W).nonempty_equiv_iff
      (matRepTwist (frobPowEquiv F j) (tensorRep (F := F) F a b))
    have h2 : Nonempty (Representation.Equiv (Wj j).toRepresentation
        (matRep (CFSG.QuasithinUnique.Setup.X7.matMap (frobPowEquiv F j : F →+* F)
          (tensorRep (F := F) F a b)))) := h1.mpr ⟨eW.symm⟩
    rw [matMap_frobPowEquiv_tensorRep] at h2
    obtain ⟨P', Q', hM⟩ := tensorRep_comp_frobPow F hF j a b
    exact ⟨h2.some.trans hM.equiv.some⟩
  let M : Submodule F (Fin n → F) := ⨆ j, (Wj j).toSubmodule
  have hG : ∀ g, ∀ v ∈ M, ((ρ₀ g).map φ).mulVec v ∈ M := by
    intro g v hv
    refine Submodule.iSup_induction (fun j => (Wj j).toSubmodule)
      (motive := fun v => ((ρ₀ g).map φ).mulVec v ∈ M) hv
      (fun j v hv => Submodule.mem_iSup_of_mem j ((Wj j).apply_mem_toSubmodule g hv))
      (by simp) (fun x y hx hy => by rw [Matrix.mulVec_add]; exact M.add_mem hx hy)
  have hΦ : ∀ v ∈ M, (fun i => v i ^ 2) ∈ M := by
    intro v hv
    refine Submodule.iSup_induction (fun j => (Wj j).toSubmodule)
      (motive := fun v => (fun i => v i ^ 2) ∈ M) hv ?_ ?_ ?_
    · intro j v hv
      obtain ⟨w, hw, rfl⟩ := hv
      have h1 : (fun i => ((Ψ j).e w) i ^ 2) = (Ψ (j + 1)).e w := by
        funext i
        rw [hΨ, hΨ, ← pow_mul, pow_succ]
      show (fun i => ((Ψ j).e w) i ^ 2) ∈ M
      rw [h1]
      exact Submodule.mem_iSup_of_mem (j + 1) (Submodule.mem_map_of_mem hw)
    · have : (fun i : Fin n => (0 : Fin n → F) i ^ 2) = 0 := by
        funext i
        simp
      rw [this]
      exact M.zero_mem
    · intro x y hx hy
      have : (fun i => (x + y) i ^ 2) = (fun i => x i ^ 2) + (fun i => y i ^ 2) := by
        funext i
        simp [CharTwo.add_sq]
      rw [this]
      exact M.add_mem hx hy
  have hWne : W.toSubmodule ≠ ⊥ := fun h => hW.1 (Subrepresentation.toSubmodule_injective h)
  have hMne : M ≠ ⊥ := by
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
    have hmem : (Ψ 0).e w ∈ M :=
      Submodule.mem_iSup_of_mem 0 (Submodule.mem_map_of_mem hwW)
    have hne : (Ψ 0).e w ≠ 0 := fun h => hw0 ((Ψ 0).e.injective (by rw [h, map_zero]))
    exact fun h => hne ((Submodule.mem_bot F).mp (h ▸ hmem))
  exact ⟨a, b, Wj, hWj, heq, descent hF ρ₀ hirr M hG hΦ hMne⟩

theorem exists_simple_quotient (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (PF : SL(3, F) →* Matrix (Fin n) (Fin n) F) (hn : 0 < n) :
    ∃ (a b : Fin f → Bool) (π : Representation.IntertwiningMap (matRep PF)
        (matRep (tensorRep (F := F) F a b))), Function.Surjective π := by
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨Wc, hWc⟩ := exists_isCoatom_subrep (matRep PF)
  have hq := quotient_isIrreducible_of_isCoatom (matRep PF) Wc hWc
  obtain ⟨a, b, ⟨e⟩⟩ := exists_T3_equiv F hF hf Wc.quotient hq
  refine ⟨a, b, e.symm.toIntertwiningMap.comp (quotProj (matRep PF) Wc), fun y => ?_⟩
  obtain ⟨v, hv⟩ := Submodule.mkQ_surjective Wc.toSubmodule (e y)
  refine ⟨v, ?_⟩
  show e.symm (Wc.toSubmodule.mkQ v) = y
  rw [hv]
  exact e.symm_apply_apply y

end Galois

section Intertwiners

open CFSG.Semidihedral.Principal
open CFSG.QuasithinUnique.Setup.X7b (toMatRep matRepEquiv)

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f n : ℕ}

theorem exists_twist_intertwiner (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (ρ₀ : SL(3, F) →* Matrix (Fin n) (Fin n) (ZMod 2)) (hn : 0 < n)
    (hirr : ∀ N : Submodule (ZMod 2) (Fin n → ZMod 2),
      (∀ g, ∀ v ∈ N, (ρ₀ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤)
    (α : SL(3, F) →* SL(3, F)) (j : ℕ)
    (hα : ∀ a b : Fin f → Bool, ∃ (P : Matrix (TIdx f ((shiftBits f)^[j] a) ((shiftBits f)^[j] b))
        (TIdx f a b) F) (Q : Matrix (TIdx f a b) (TIdx f ((shiftBits f)^[j] a)
          ((shiftBits f)^[j] b)) F),
      MatIso ((tensorRep (F := F) F a b).comp α)
        (tensorRep F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)) P Q) :
    ∃ M : Matrix (Fin n) (Fin n) F, M ≠ 0 ∧ ∀ g : SL(3, F),
      M * (ρ₀ (α g)).map (ZMod.castHom (dvd_refl 2) F) =
        (ρ₀ g).map (ZMod.castHom (dvd_refl 2) F) * M := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set PF := matMap φ ρ₀ with hPF
  obtain ⟨a, b, Wj, hWj, heq, hMtop⟩ := exists_galois_family hF hf ρ₀ hn hirr
  obtain ⟨a₁, b₁, π, hπ⟩ := exists_simple_quotient hF hf PF hn
  have hirrT := ((tensorRep_absolutely_irreducible_and_distinct F hF hf).1 a₁ b₁).1
  have hnt : Nontrivial (TIdx f a₁ b₁ → F) := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hirrT).1
  obtain ⟨j₁, ⟨e₂⟩⟩ := exists_iso_of_surj_onto_irred hirrT π hπ Wj hWj hMtop
  obtain ⟨e₁⟩ := heq j₁
  have hlast := (tensorRep_absolutely_irreducible_and_distinct F hF hf).2 _ _ _ _
    ⟨e₁.symm.trans e₂⟩
  obtain ⟨rfl, rfl⟩ := hlast
  obtain ⟨P, Q, hX⟩ := hα ((shiftBits f)^[j₁] a) ((shiftBits f)^[j₁] b)
  obtain ⟨e'⟩ := heq (j + j₁)
  rw [Function.iterate_add_apply, Function.iterate_add_apply] at e'
  obtain ⟨T, hT0, hTc⟩ := exists_twist_hom (matRep PF) _ α π hπ (Wj (j + j₁))
    (hX.equiv.some.trans e'.symm)
  obtain ⟨M, hM0, hM⟩ := exists_matrix_intertwiner (PF.comp α) PF T hT0 (fun g v => hTc g v)
  exact ⟨M, hM0, hM⟩

theorem exists_tau_intertwiner (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f)
    (ρ₀ : SL(3, F) →* Matrix (Fin n) (Fin n) (ZMod 2)) (hn : 0 < n) :
    ∃ M : Matrix (Fin n) (Fin n) F, M ≠ 0 ∧ ∀ g : SL(3, F),
      M * (ρ₀ (tauSL F g)).map (ZMod.castHom (dvd_refl 2) F) =
        (dualMat ρ₀ g).map (ZMod.castHom (dvd_refl 2) F) * M := by
  classical
  set φ : ZMod 2 →+* F := ZMod.castHom (dvd_refl 2) F with hφ
  set PF := matMap φ ρ₀ with hPF
  obtain ⟨a, b, π, hπ⟩ := exists_simple_quotient hF hf PF hn
  have hirrT := ((tensorRep_absolutely_irreducible_and_distinct F hF hf).1 a b).1
  have hκ : Nonempty (TIdx f a b) := by
    by_contra hne
    have : IsEmpty (TIdx f a b) := not_nonempty_iff.mp hne
    obtain ⟨x, y, hxy⟩ := (((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff _).mp hirrT).1).exists_pair_ne
    exact hxy (Subsingleton.elim x y)
  let Pm : Matrix (TIdx f a b) (Fin n) F := LinearMap.toMatrix' π.toLinearMap
  have hPmv : ∀ v, Pm.mulVec v = π v := fun v => LinearMap.toMatrix'_mulVec π.toLinearMap v
  have hPm : ∀ g, Pm * PF g = tensorRep (F := F) F a b g * Pm := by
    intro g
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      hPmv, hPmv]
    exact Representation.IntertwiningMap.isIntertwining _ _ π g v
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin n) (TIdx f a b) F, Pm * S = 1 :=
    Matrix.mulVec_surjective_iff_exists_right_inverse.mp fun y => by
      obtain ⟨v, hv⟩ := hπ y
      exact ⟨v, by rw [hPmv]; exact hv⟩
  obtain ⟨X, Y, h⟩ : ∃ (X Y : Matrix (TIdx f a b) (TIdx f a b) F),
      MatIso ((tensorRep (F := F) F a b).comp (tauSL F)) (dualMat (tensorRep (F := F) F a b)) X Y :=
    ⟨_, _, (tensorRep_comp_tau (F := F) F a b).trans (tensorRep_dual_iso (F := F) F a b).symm⟩
  have hcomm : ∀ g, Pmᵀ * X * Pm * PF (tauSL F g) = dualMat PF g * (Pmᵀ * X * Pm) := by
    intro g
    have e1 : Pm * PF (tauSL F g) = tensorRep (F := F) F a b (tauSL F g) * Pm := hPm _
    have e2 : X * tensorRep (F := F) F a b (tauSL F g) =
        dualMat (tensorRep (F := F) F a b) g * X := h.comm g
    have e3 : Pmᵀ * dualMat (tensorRep (F := F) F a b) g = dualMat PF g * Pmᵀ := by
      rw [dualMat_apply, dualMat_apply, ← Matrix.transpose_mul, ← Matrix.transpose_mul, hPm g⁻¹]
    calc Pmᵀ * X * Pm * PF (tauSL F g) = Pmᵀ * X * (Pm * PF (tauSL F g)) := by
          rw [Matrix.mul_assoc _ Pm]
      _ = Pmᵀ * X * (tensorRep (F := F) F a b (tauSL F g) * Pm) := by rw [e1]
      _ = Pmᵀ * (X * tensorRep (F := F) F a b (tauSL F g)) * Pm := by
          simp only [Matrix.mul_assoc]
      _ = Pmᵀ * (dualMat (tensorRep (F := F) F a b) g * X) * Pm := by rw [e2]
      _ = (Pmᵀ * dualMat (tensorRep (F := F) F a b) g) * X * Pm := by
          simp only [Matrix.mul_assoc]
      _ = (dualMat PF g * Pmᵀ) * X * Pm := by rw [e3]
      _ = dualMat PF g * (Pmᵀ * X * Pm) := by simp only [Matrix.mul_assoc]
  have hM0 : Pmᵀ * X * Pm ≠ 0 := by
    intro h0
    have hSS : Sᵀ * (Pmᵀ * X * Pm) * S = X := by
      calc Sᵀ * (Pmᵀ * X * Pm) * S = (Sᵀ * Pmᵀ) * X * (Pm * S) := by simp only [Matrix.mul_assoc]
        _ = X := by
          rw [← Matrix.transpose_mul, hS, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul] at hSS
    have h1 : (1 : Matrix (TIdx f a b) (TIdx f a b) F) = 0 := by
      rw [← h.mul_inv, ← hSS, Matrix.zero_mul]
    exact one_ne_zero h1
  have hdm : ∀ g, dualMat PF g = (dualMat ρ₀ g).map φ := by
    intro g
    rw [dualMat_apply, dualMat_apply, Matrix.transpose_map]
    rfl
  refine ⟨Pmᵀ * X * Pm, hM0, fun g => ?_⟩
  rw [← hdm g]
  exact hcomm g

end Intertwiners

section Assembly

open CFSG.QuasithinUnique.Setup.X7b (toMatRep matRepEquiv)
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation slConjugation_matrix)

section Surjective

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem frobSL_surjective (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) :
    Function.Surjective (frobSL F) := by
  intro g
  obtain ⟨m, rfl⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
  refine ⟨(frobSL F)^[m] g, ?_⟩
  have h := frobSL_iterate_card hF g
  rwa [Function.iterate_succ_apply'] at h

theorem frobPow_surjective (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) (j : ℕ) :
    Function.Surjective (frobPow F j) := by
  induction j with
  | zero => exact Function.surjective_id
  | succ r ih => exact (frobSL_surjective hF hf).comp ih

omit [CharP F 2] [Fintype F] in
theorem tauSL_surjective : Function.Surjective (tauSL F) :=
  fun g => ⟨tauSL F g, tauSL_tauSL g⟩

end Surjective

section Conj

variable {F : Type} [Field F]

@[expose] def glTrInv (A : GL (Fin 3) F) : GL (Fin 3) F where
  val := ((A⁻¹ : GL (Fin 3) F).val)ᵀ
  inv := (A.val)ᵀ
  val_inv := by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one]
  inv_val := by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]

theorem slConj_comp_tau (A : GL (Fin 3) F) :
    (slConjugation 3 F A).toMonoidHom.comp (tauSL F) =
      (tauSL F).comp (slConjugation 3 F (glTrInv A)).toMonoidHom := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  show ((slConjugation 3 F A (tauSL F g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
    ((tauSL F (slConjugation 3 F (glTrInv A) g) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)
  have h1 : ((slConjugation 3 F (glTrInv A) g)⁻¹ : SL(3, F)) =
      slConjugation 3 F (glTrInv A) g⁻¹ := (map_inv _ g).symm
  have hB : (glTrInv A).val = ((A⁻¹ : GL (Fin 3) F).val)ᵀ := rfl
  have hB' : ((glTrInv A)⁻¹ : GL (Fin 3) F).val = (A.val)ᵀ := rfl
  rw [slConjugation_matrix, tauSL_coe, tauSL_coe, trInvMat, trInvMat, h1, slConjugation_matrix, hB,
    hB']
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

end Conj

section Equivs

variable {k G U : Type} [Field k] [Group G] [AddCommGroup U] [Module k U] {n : ℕ}

theorem equiv_of_matIso (ρ : Representation k G U) (bas : Module.Basis (Fin n) k U) (β : G →* G)
    {P Q : Matrix (Fin n) (Fin n) k}
    (h : MatIso ((toMatRep ρ bas).comp β) (toMatRep ρ bas) P Q) :
    Nonempty (Representation.Equiv (ρ.comp β) ρ) := by
  obtain ⟨e⟩ := h.equiv
  exact ⟨((matRepEquiv (ρ.comp β) bas).trans e).trans (matRepEquiv ρ bas).symm⟩

theorem equiv_dual_of_matIso (ρ : Representation k G U) (bas : Module.Basis (Fin n) k U)
    (β : G →* G) {P Q : Matrix (Fin n) (Fin n) k}
    (h : MatIso ((toMatRep ρ bas).comp β) (dualMat (toMatRep ρ bas)) P Q) :
    Nonempty (Representation.Equiv (ρ.comp β) ρ.dual) := by
  have h' : MatIso (toMatRep (ρ.comp β) bas) (toMatRep ρ.dual bas.dualBasis) P Q := by
    rw [toMatRep_dual]
    exact h
  obtain ⟨e⟩ := h'.equiv
  exact ⟨((matRepEquiv (ρ.comp β) bas).trans e).trans (matRepEquiv ρ.dual bas.dualBasis).symm⟩

end Equivs

section Main

variable {F : Type} [Field F] [CharP F 2] [Fintype F] {f : ℕ}

theorem twist_equiv (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U] (ρ : Representation (ZMod 2) SL(3, F) U)
    (hirr : ρ.IsIrreducible) (A : GL (Fin 3) F) (j : ℕ) :
    Nonempty (Representation.Equiv
      (ρ.comp ((slConjugation 3 F A).toMonoidHom.comp (frobPow F j))) ρ) := by
  classical
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hnt : Nontrivial U := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
  let n := Module.finrank (ZMod 2) U
  let bas : Module.Basis (Fin n) (ZMod 2) U := Module.finBasis (ZMod 2) U
  have hirr₀ := invariant_dichotomy ρ hirr bas
  have hn : 0 < n := Module.finrank_pos
  let α : SL(3, F) →* SL(3, F) := (slConjugation 3 F A).toMonoidHom.comp (frobPow F j)
  have hαs : Function.Surjective α := by
    intro g
    obtain ⟨h, hh⟩ := frobPow_surjective hF hf j ((slConjugation 3 F A).symm g)
    refine ⟨h, ?_⟩
    show slConjugation 3 F A (frobPow F j h) = g
    rw [hh, MulEquiv.apply_symm_apply]
  have hMat : ∀ a b : Fin f → Bool,
      ∃ (P : Matrix (TIdx f ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)) (TIdx f a b) F)
        (Q : Matrix (TIdx f a b) (TIdx f ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)) F),
        MatIso ((tensorRep (F := F) F a b).comp α)
          (tensorRep F ((shiftBits f)^[j] a) ((shiftBits f)^[j] b)) P Q := by
    intro a b
    obtain ⟨P₁, Q₁, h₁⟩ := tensorRep_comp_frobPow F hF j a b
    have h₂ := (tensorRep_comp_conj F A a b).comp (frobPow F j)
    exact ⟨_, _, h₂.trans h₁⟩
  obtain ⟨M, hM0, hM⟩ := exists_twist_intertwiner hF hf (toMatRep ρ bas) hn hirr₀ α j hMat
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_zmod_intertwiner hF ((toMatRep ρ bas).comp α) (toMatRep ρ bas) M
    hM0 hM
  have hu := isUnit_of_twist_intertwiner (toMatRep ρ bas) hirr₀ (toMatRep ρ bas) α hαs M₀ hM₀0 hM₀
  have hdet := (Matrix.isUnit_iff_isUnit_det M₀).mp hu
  exact equiv_of_matIso ρ bas α
    ⟨Matrix.mul_nonsing_inv M₀ hdet, Matrix.nonsing_inv_mul M₀ hdet, hM₀⟩

theorem tau_equiv (hF : Fintype.card F = 2 ^ f) (hf : 1 ≤ f) {U : Type} [AddCommGroup U]
    [Module (ZMod 2) U] [Finite U] (ρ : Representation (ZMod 2) SL(3, F) U)
    (hirr : ρ.IsIrreducible) : Nonempty (Representation.Equiv (ρ.comp (tauSL F)) ρ.dual) := by
  classical
  have hfin : Module.Finite (ZMod 2) U := Module.Finite.of_finite
  have hnt : Nontrivial U := ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).1
  let n := Module.finrank (ZMod 2) U
  let bas : Module.Basis (Fin n) (ZMod 2) U := Module.finBasis (ZMod 2) U
  have hirr₀ := invariant_dichotomy ρ hirr bas
  have hn : 0 < n := Module.finrank_pos
  obtain ⟨M, hM0, hM⟩ := exists_tau_intertwiner hF hf (toMatRep ρ bas) hn
  obtain ⟨M₀, hM₀0, hM₀⟩ := exists_zmod_intertwiner hF ((toMatRep ρ bas).comp (tauSL F))
    (dualMat (toMatRep ρ bas)) M hM0 hM
  have hu := isUnit_of_twist_intertwiner (toMatRep ρ bas) hirr₀ (dualMat (toMatRep ρ bas))
    (tauSL F) tauSL_surjective M₀ hM₀0 hM₀
  have hdet := (Matrix.isUnit_iff_isUnit_det M₀).mp hu
  exact equiv_dual_of_matIso ρ bas (tauSL F)
    ⟨Matrix.mul_nonsing_inv M₀ hdet, Matrix.nonsing_inv_mul M₀ hdet, hM₀⟩

end Main

theorem graphFieldTwistsDual :
    ∀ (f : ℕ) (F : Type) [Field F] [Fintype F] [CharP F 2], 1 ≤ f → Fintype.card F = 2 ^ f →
      ∀ (U : Type) [AddCommGroup U] [Module (ZMod 2) U] [Finite U]
        (ρ : Representation (ZMod 2) SL(3, F) U), ρ.IsIrreducible →
        ∀ (A : GL (Fin 3) F) (j : ℕ),
          Nonempty (Representation.Equiv (ρ.comp ((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
            3 F A).toMonoidHom.comp (frobPow F j))) ρ) ∧
          Nonempty (Representation.Equiv (ρ.comp (((CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
            3 F A).toMonoidHom.comp (tauSL F)).comp (frobPow F j))) ρ.dual) := by
  intro f F _ _ _ hf hF U _ _ _ ρ hirr A j
  refine ⟨twist_equiv hF hf ρ hirr A j, ?_⟩
  have hirr' : Representation.IsIrreducible (ρ.comp (tauSL F)) :=
    CFSG.QuasithinUnique.Setup.X7b.isIrreducible_comp (tauSL F) tauSL_surjective ρ hirr
  obtain ⟨e⟩ := twist_equiv hF hf (ρ.comp (tauSL F)) hirr' (glTrInv A) j
  obtain ⟨e'⟩ := tau_equiv hF hf ρ hirr
  have hcomm : ((slConjugation 3 F A).toMonoidHom.comp (tauSL F)).comp (frobPow F j) =
      (tauSL F).comp ((slConjugation 3 F (glTrInv A)).toMonoidHom.comp (frobPow F j)) := by
    rw [slConj_comp_tau, MonoidHom.comp_assoc]
  rw [hcomm]
  exact ⟨e.trans e'⟩

end Assembly

end CFSG.QuasithinUnique.Setup.X7a
