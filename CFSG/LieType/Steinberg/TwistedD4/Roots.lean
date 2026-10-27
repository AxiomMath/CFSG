module

public import CFSG.LieType.Steinberg.TwistedD4.Defs

public noncomputable section

namespace CFSG.LieType.Steinberg.TwistedD4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
open CFSG.LieType.Steinberg.Adjoint

theorem addMonoidHom_ext_single {m n : ℕ} {f g : (Fin m → ℤ) →+ (Fin n → ℤ)}
    (h : ∀ l, f (Pi.single l 1) = g (Pi.single l 1)) : f = g := by
  refine AddMonoidHom.functions_ext _ f g fun l x => ?_
  have hx : (Pi.single l x : Fin m → ℤ) = x • Pi.single l 1 := by
    ext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  rw [hx, map_zsmul, map_zsmul, h l]

@[expose] def proj : (Fin d4.rank → ℤ) →+ (Fin (Tag.rank .G2) → ℤ) where
  toFun := orbitSum orbitMap
  map_zero' := by
    funext c
    simp [orbitSum]
  map_add' v w := by
    funext c
    simp [orbitSum, Finset.sum_add_distrib]

theorem proj_apply (v : Fin d4.rank → ℤ) : proj v = orbitSum orbitMap v := rfl

@[expose] def rhoHom : (Fin d4.rank → ℤ) →+ (Fin d4.rank → ℤ) where
  toFun := rho
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def twReflectHom (i : Fin (Tag.rank .G2)) :
    (Fin d4.rank → ℤ) →+ (Fin d4.rank → ℤ) :=
  match (i : ℕ) with
  | 0 => reflectHom d4 (nd 2)
  | _ => (reflectHom d4 (nd 0)).comp ((reflectHom d4 (nd 1)).comp (reflectHom d4 (nd 3)))

theorem twReflectHom_zero (v : Fin d4.rank → ℤ) : twReflectHom (ng 0) v = reflect d4 (nd 2) v :=
  rfl

theorem twReflectHom_one (v : Fin d4.rank → ℤ) :
    twReflectHom (ng 1) v = reflect d4 (nd 0) (reflect d4 (nd 1) (reflect d4 (nd 3) v)) :=
  rfl

theorem proj_rho (v : Fin d4.rank → ℤ) : proj (rho v) = proj v := by
  have h : proj.comp rhoHom = proj := addMonoidHom_ext_single fun l => by
    revert l
    decide
  exact DFunLike.congr_fun h v

theorem ht_proj (v : Fin d4.rank → ℤ) : ht (proj v) = ht v := by
  simp only [ht, proj_apply, orbitSum]
  exact Finset.sum_fiberwise Finset.univ orbitMap v

theorem proj_twReflect
    (i : Fin (Tag.rank .G2)) (v : Fin d4.rank → ℤ) :
    proj (twReflectHom i v) = reflect .G2 i (proj v) := by
  have h : proj.comp (twReflectHom i) = (reflectHom .G2 i).comp proj :=
    addMonoidHom_ext_single fun l => by
      revert i l
      decide
  have := DFunLike.congr_fun h v
  simpa [reflectHom_apply] using this

theorem twReflect_rho (i : Fin (Tag.rank .G2)) (v : Fin d4.rank → ℤ) :
    twReflectHom i (rho v) = rho (twReflectHom i v) := by
  have h : (twReflectHom i).comp rhoHom = rhoHom.comp (twReflectHom i) :=
    addMonoidHom_ext_single fun l => by
      revert i l
      decide
  exact DFunLike.congr_fun h v

theorem isRoot_twReflect (i : Fin (Tag.rank .G2)) {v : Fin d4.rank → ℤ} (hv : IsRoot d4 v) :
    IsRoot d4 (twReflectHom i v) := by
  match i with
  | ⟨0, _⟩ => exact hv.reflect (nd 2)
  | ⟨1, _⟩ => exact ((hv.reflect (nd 3)).reflect (nd 1)).reflect (nd 0)

abbrev d4Root (k : ℕ) : Fin d4.rank → ℤ := (Tag.rootCertificate d4).root k

abbrev g2Root (m : ℕ) : Fin (Tag.rank .G2) → ℤ := (Tag.rootCertificate .G2).root m

@[expose] def checkProjRoot : Bool :=
  (List.range (Tag.rootCertificate d4).roots.length).all fun k =>
    (Tag.stringData .G2).memDec (Tag.rootCertificate .G2) (proj (d4Root k))

@[expose] def checkProjSurj : Bool :=
  (List.range (Tag.rootCertificate .G2).roots.length).all fun m =>
    (List.range (Tag.rootCertificate d4).roots.length).any fun k =>
      List.ofFn (proj (d4Root k)) == List.ofFn (g2Root m)

@[expose] def checkFibres : Bool :=
  (List.range (Tag.rootCertificate d4).roots.length).all fun k =>
    (List.range (Tag.rootCertificate d4).roots.length).all fun l =>
      (List.ofFn (proj (d4Root k)) == List.ofFn (proj (d4Root l))) ==
        (List.ofFn (d4Root l) == List.ofFn (d4Root k) ||
          List.ofFn (d4Root l) == List.ofFn (rho (d4Root k)) ||
          List.ofFn (d4Root l) == List.ofFn (rho (rho (d4Root k))))

@[expose] def checkPairs : Bool :=
  (List.range (Tag.rootCertificate d4).roots.length).all fun k =>
    List.ofFn (rho (d4Root k)) == List.ofFn (d4Root k) ||
      (!(Tag.stringData d4).memDec (Tag.rootCertificate d4) (d4Root k + rho (d4Root k)) &&
        !(List.ofFn (d4Root k + rho (d4Root k))).all (· == 0))

theorem checkProjRoot_eq : checkProjRoot = true := by decide +kernel

theorem checkProjSurj_eq : checkProjSurj = true := by decide +kernel

theorem checkFibres_eq : checkFibres = true := by decide +kernel

theorem checkPairs_eq : checkPairs = true := by decide +kernel

theorem isRoot_proj
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) : IsRoot .G2 (proj α) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check d4) hα
  have h := checkProjRoot_eq
  simp only [checkProjRoot, List.all_eq_true, List.mem_range] at h
  exact (StringData.memDec_iff (Tag.rootCertificate_check .G2) (Tag.stringData_check .G2)).1
    (h k hk)

theorem exists_proj_eq
    {β : Fin (Tag.rank .G2) → ℤ} (hβ : IsRoot .G2 β) :
    ∃ α, IsRoot d4 α ∧ proj α = β := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hβ
  have h := checkProjSurj_eq
  simp only [checkProjSurj, List.all_eq_true, List.mem_range, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨k, hk, hkm⟩ := h m hm
  exact ⟨d4Root k, RootCertificate.isRoot_root (Tag.rootCertificate_check d4) k hk,
    List.ofFn_injective hkm⟩

theorem proj_eq_proj_iff
    {α α' : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hα' : IsRoot d4 α') :
    proj α = proj α' ↔ α' = α ∨ α' = rho α ∨ α' = rho (rho α) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check d4) hα
  obtain ⟨l, hl, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check d4) hα'
  have h := checkFibres_eq
  simp only [checkFibres, List.all_eq_true, List.mem_range] at h
  have h := h k hk l hl
  constructor
  · intro heq
    have : (List.ofFn (proj (d4Root k)) == List.ofFn (proj (d4Root l))) = true := by
      simp [heq]
    rw [this] at h
    simp only [Bool.true_eq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with (h | h) | h
    · exact Or.inl (List.ofFn_injective h)
    · exact Or.inr (Or.inl (List.ofFn_injective h))
    · exact Or.inr (Or.inr (List.ofFn_injective h))
  · rintro (h' | h' | h')
    · rw [h']
    · rw [h', proj_rho]
    · rw [h', proj_rho, proj_rho]

private theorem pairs_spec
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) :
    ¬ IsRoot d4 (α + rho α) ∧ α + rho α ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check d4) hα
  have h := checkPairs_eq
  simp only [checkPairs, List.all_eq_true, List.mem_range] at h
  have h := h k hk
  have hne' : (List.ofFn (rho (d4Root k)) == List.ofFn (d4Root k)) = false := by
    rw [beq_eq_false_iff_ne]
    exact fun h' => hne (List.ofFn_injective h')
  simp only [hne', Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨h1, h3⟩ := h
  refine ⟨fun hr => ?_, fun h0 => ?_⟩
  · rw [(StringData.memDec_iff (Tag.rootCertificate_check d4) (Tag.stringData_check d4)).2 hr]
      at h1
    exact absurd h1 (by simp)
  · rw [h0] at h3
    revert h3
    decide

theorem not_isRoot_add_rho
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) :
    ¬ IsRoot d4 (α + rho α) :=
  (pairs_spec hα hne).1

theorem add_rho_ne_zero
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) :
    α + rho α ≠ 0 :=
  (pairs_spec hα hne).2

theorem rho_rho_ne {α : Fin d4.rank → ℤ} (hne : rho α ≠ α) : rho (rho α) ≠ α := fun h => by
  apply hne
  calc rho α = rho (rho (rho α)) := by rw [h]
    _ = α := rho_rho_rho α

theorem rho_rho_ne_rho
    {α : Fin d4.rank → ℤ} (hne : rho α ≠ α) : rho (rho α) ≠ rho α :=
  fun h => hne (permLattice_injective rhoPerm h)

theorem eq_one_of_proj_eq_nsmul
    {α α' : Fin d4.rank → ℤ} (hα : IsRoot d4 α)
    (hα' : IsRoot d4 α') {c : ℕ} (hc : 0 < c) (h : proj α = c • proj α') : c = 1 := by
  have hβ := isRoot_proj hα
  have hβ' := isRoot_proj hα'
  have hdep : ¬ LinIndepPair (proj α) (proj α') := fun hl => by
    have := hl 1 (-(c : ℤ)) (by rw [h, one_smul, neg_smul, natCast_zsmul, add_neg_cancel])
    exact one_ne_zero this.1
  rcases TagRoots.eq_or_eq_neg_of_not_linIndepPair hβ hβ' hdep with h' | h'
  · rw [h'] at h
    have h0 : (c - 1 : ℤ) • proj α' = 0 := by
      rw [sub_smul, one_smul, natCast_zsmul, ← h, sub_self]
    rcases smul_eq_zero.1 h0 with h1 | h1
    · omega
    · exact absurd h1 hβ'.ne_zero
  · rw [h'] at h
    have h0 : ((c : ℤ) + 1) • proj α' = 0 := by
      rw [add_smul, one_smul, natCast_zsmul, ← h, neg_add_cancel]
    rcases smul_eq_zero.1 h0 with h1 | h1
    · omega
    · exact absurd h1 hβ'.ne_zero

section Commute

variable {K : Type} [Field K]

theorem commute_of_mem_rootGroup_rho
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    {x y : adjointGroup d4 K} (hx : x ∈ rootGroup (rootOperatorFamily d4) K α)
    (hy : y ∈ rootGroup (rootOperatorFamily d4) K (rho α)) : Commute x y := by
  refine commute_of_mem_rootGroup hα (isRoot_rho hα) (Ne.symm hne) (fun h => ?_)
    (not_isRoot_add_rho hα hne) hx hy
  exact add_rho_ne_zero hα hne (by nth_rewrite 1 [h]; exact neg_add_cancel _)

theorem commute_xPar_rho
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α) (c d : K) :
    Commute (xPar (rootOperatorFamily d4) α c) (xPar (rootOperatorFamily d4) (rho α) d) :=
  commute_of_mem_rootGroup_rho hα hne (xPar_mem hα c) (xPar_mem (isRoot_rho hα) d)

theorem commute_xPar_rho_rho
    {α : Fin d4.rank → ℤ} (hα : IsRoot d4 α) (hne : rho α ≠ α)
    (c d : K) :
    Commute (xPar (rootOperatorFamily d4) α c) (xPar (rootOperatorFamily d4) (rho (rho α)) d) := by
  have hr := isRoot_rho (isRoot_rho hα)
  have h := (commute_xPar_rho hr (rho_rho_ne_rho (rho_rho_ne_rho hne)) d c).symm
  rwa [rho_rho_rho] at h

end Commute

section Sign

variable {K : Type} [Field K] (σ : K →+* K)

theorem twistC_twistC_twistC
    (hσ : ∀ c, σ (σ (σ c)) = c) (g : adjointGroup d4 K) :
    twistC .D4 K σ (twistC .D4 K σ (twistC .D4 K σ g)) = g := by
  set S : Set (ModGL d4 K) := {g | ∃ (i : Fin d4.rank) (c : K),
    (g : Module.End K (RootModule d4 K)) = xOp d4 K i c ∨
      (g : Module.End K (RootModule d4 K)) = yOp d4 K i c}
  have hcl : Subgroup.closure (((↑) : adjointGroup d4 K → ModGL d4 K) ⁻¹' S) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  have hle : Subgroup.closure (((↑) : adjointGroup d4 K → ModGL d4 K) ⁻¹' S) ≤
      MonoidHom.eqLocus ((twistC .D4 K σ).comp ((twistC .D4 K σ).comp (twistC .D4 K σ)))
        (MonoidHom.id _) := by
    rw [Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have e : g = xElement i c := Subtype.ext (Units.ext hg)
      subst e
      change twistC .D4 K σ (twistC .D4 K σ (twistC .D4 K σ (xElement i c))) = xElement i c
      rw [twistC_xElement, twistC_xElement, twistC_xElement, hσ]
      congr 1
      exact rhoPerm_rhoPerm_rhoPerm i
    · have e : g = yElement i c := Subtype.ext (Units.ext hg)
      subst e
      change twistC .D4 K σ (twistC .D4 K σ (twistC .D4 K σ (yElement i c))) = yElement i c
      rw [twistC_yElement, twistC_yElement, twistC_yElement, hσ]
      congr 1
      exact rhoPerm_rhoPerm_rhoPerm i
  rw [hcl] at hle
  exact hle (Subgroup.mem_top g)

open _root_.Classical in
@[expose] noncomputable def twistSign
    (γ : Fin d4.rank → ℤ) : K :=
  if h : IsRoot d4 γ then
    (((rootOperatorFamily d4).exists_twistC_eltElement .D4 K σ ⟨γ, h⟩).choose : K)
  else 1

theorem twistSign_spec
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) :
    (twistSign σ γ = 1 ∨ twistSign σ γ = -1) ∧ ∀ c : K,
      twistC .D4 K σ (xPar (rootOperatorFamily d4) γ c) =
        xPar (rootOperatorFamily d4) (rho γ) (twistSign σ γ * σ c) := by
  classical
  have hs := ((rootOperatorFamily d4).exists_twistC_eltElement .D4 K σ ⟨γ, hγ⟩).choose_spec
  have e : twistSign σ γ =
      (((rootOperatorFamily d4).exists_twistC_eltElement .D4 K σ ⟨γ, hγ⟩).choose : K) := by
    rw [twistSign, dite_eq_left hγ]
  refine ⟨?_, fun c => ?_⟩
  · rw [e]
    rcases hs.1 with h | h <;> rw [h] <;> simp
  · rw [e, xPar_of_isRoot hγ, xPar_of_isRoot (isRoot_rho hγ), hs.2 c]
    rfl

theorem twistSign_eq_one_or
    (γ : Fin d4.rank → ℤ) :
    twistSign σ γ = 1 ∨ twistSign σ γ = -1 := by
  by_cases hγ : IsRoot d4 γ
  · exact (twistSign_spec σ hγ).1
  · classical
    left
    rw [twistSign, dite_eq_right hγ]

theorem twistC_xPar
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    twistC .D4 K σ (xPar (rootOperatorFamily d4) γ c) =
      xPar (rootOperatorFamily d4) (rho γ) (twistSign σ γ * σ c) :=
  (twistSign_spec σ hγ).2 c

theorem map_sign {ε : K} (hε : ε = 1 ∨ ε = -1) : σ ε = ε := by
  rcases hε with rfl | rfl <;> simp

theorem twistC_mem_rootGroup
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) {x : adjointGroup d4 K}
    (hx : x ∈ rootGroup (rootOperatorFamily d4) K γ) :
    twistC .D4 K σ x ∈ rootGroup (rootOperatorFamily d4) K (rho γ) := by
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ x).1 hx
  rw [twistC_xPar σ hγ]
  exact xPar_mem (isRoot_rho hγ) _

theorem twistC_three_xPar
    {γ : Fin d4.rank → ℤ} (hγ : IsRoot d4 γ) (c : K) :
    twistC .D4 K σ (twistC .D4 K σ (twistC .D4 K σ (xPar (rootOperatorFamily d4) γ c))) =
      xPar (rootOperatorFamily d4) γ (twistSign σ γ * twistSign σ (rho γ) *
        twistSign σ (rho (rho γ)) * σ (σ (σ c))) := by
  have h1 := isRoot_rho hγ
  have h2 := isRoot_rho h1
  rw [twistC_xPar σ hγ, twistC_xPar σ h1, twistC_xPar σ h2, rho_rho_rho, map_mul, map_mul,
    map_mul, map_sign σ (twistSign_eq_one_or σ γ), map_sign σ (twistSign_eq_one_or σ γ),
    map_sign σ (twistSign_eq_one_or σ (rho γ))]
  congr 1
  ring

theorem twistSign_mul_rho
    (hσ : ∀ c, σ (σ (σ c)) = c) {γ : Fin d4.rank → ℤ}
    (hγ : IsRoot d4 γ) :
    twistSign σ γ * twistSign σ (rho γ) * twistSign σ (rho (rho γ)) = 1 := by
  have h := twistC_three_xPar σ hγ 1
  rw [twistC_twistC_twistC σ hσ, map_one, map_one, map_one, mul_one] at h
  exact (xPar_injective hγ h).symm

theorem twistSign_of_rho_eq
    (hσ : ∀ c, σ (σ (σ c)) = c) {γ : Fin d4.rank → ℤ}
    (hγ : IsRoot d4 γ) (hfix : rho γ = γ) : twistSign σ γ = 1 := by
  have h := twistSign_mul_rho σ hσ hγ
  rw [hfix, hfix] at h
  rcases twistSign_eq_one_or σ γ with h' | h'
  · exact h'
  · rw [h'] at h ⊢
    have : (-1 : K) = 1 := by linear_combination h
    exact this

end Sign

end CFSG.LieType.Steinberg.TwistedD4
