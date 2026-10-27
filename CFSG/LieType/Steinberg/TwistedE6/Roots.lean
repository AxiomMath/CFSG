module

public import CFSG.LieType.Steinberg.TwistedE6.Defs
public import CFSG.LieType.Steinberg.TypeExceptional
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate123

public section

namespace CFSG.LieType.Steinberg.TwistedE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule

theorem addMonoidHom_ext_single {m n : ℕ} {f g : (Fin m → ℤ) →+ (Fin n → ℤ)}
    (h : ∀ l, f (Pi.single l 1) = g (Pi.single l 1)) : f = g := by
  refine AddMonoidHom.functions_ext _ f g fun l x => ?_
  have hx : (Pi.single l x : Fin m → ℤ) = x • Pi.single l 1 := by
    ext j
    by_cases hj : j = l
    · subst hj; simp
    · simp [hj]
  rw [hx, map_zsmul, map_zsmul, h l]

@[expose] def proj : (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .F4) → ℤ) where
  toFun := orbitSum orbitMap
  map_zero' := by
    funext c
    simp [orbitSum]
  map_add' v w := by
    funext c
    simp [orbitSum, Finset.sum_add_distrib]

theorem proj_apply (v : Fin (Tag.rank .E6) → ℤ) : proj v = orbitSum orbitMap v := rfl

@[expose] def rhoHom : (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ) where
  toFun := rho
  map_zero' := rfl
  map_add' _ _ := rfl

@[expose] def twReflectHom (i : Fin (Tag.rank .F4)) :
    (Fin (Tag.rank .E6) → ℤ) →+ (Fin (Tag.rank .E6) → ℤ) :=
  match (i : ℕ) with
  | 0 => reflectHom .E6 (1 : Fin 6)
  | 1 => reflectHom .E6 (3 : Fin 6)
  | 2 => (reflectHom .E6 (2 : Fin 6)).comp (reflectHom .E6 (4 : Fin 6))
  | _ => (reflectHom .E6 (0 : Fin 6)).comp (reflectHom .E6 (5 : Fin 6))

theorem proj_rho (v : Fin (Tag.rank .E6) → ℤ) : proj (rho v) = proj v := by
  have h : proj.comp rhoHom = proj := addMonoidHom_ext_single fun l => by
    revert l
    decide
  exact DFunLike.congr_fun h v

theorem ht_proj (v : Fin (Tag.rank .E6) → ℤ) : ht (proj v) = ht v := by
  simp only [ht, proj_apply, orbitSum]
  exact Finset.sum_fiberwise Finset.univ orbitMap v

theorem proj_twReflect (i : Fin (Tag.rank .F4)) (v : Fin (Tag.rank .E6) → ℤ) :
    proj (twReflectHom i v) = reflect .F4 i (proj v) := by
  have h : proj.comp (twReflectHom i) = (reflectHom .F4 i).comp proj :=
    addMonoidHom_ext_single fun l => by
      revert i l
      decide
  have := DFunLike.congr_fun h v
  simpa [reflectHom_apply] using this

abbrev e6Root (k : ℕ) : Fin (Tag.rank .E6) → ℤ := (Tag.rootCertificate .E6).root k

abbrev f4Root (m : ℕ) : Fin (Tag.rank .F4) → ℤ := (Tag.rootCertificate .F4).root m

@[expose] def checkProjRoot : Bool :=
  (List.range (Tag.rootCertificate .E6).roots.length).all fun k =>
    (Tag.stringData .F4).memDec (Tag.rootCertificate .F4) (proj (e6Root k))

@[expose] def checkProjSurj : Bool :=
  (List.range (Tag.rootCertificate .F4).roots.length).all fun m =>
    (List.range (Tag.rootCertificate .E6).roots.length).any fun k =>
      List.ofFn (proj (e6Root k)) == List.ofFn (f4Root m)

@[expose] def checkFibres : Bool :=
  (List.range (Tag.rootCertificate .E6).roots.length).all fun k =>
    (List.range (Tag.rootCertificate .E6).roots.length).all fun l =>
      (List.ofFn (proj (e6Root k)) == List.ofFn (proj (e6Root l))) == (l == k || l == rhoIdx k)

@[expose] def checkPairs : Bool :=
  (List.range (Tag.rootCertificate .E6).roots.length).all fun k =>
    rhoIdx k == k ||
      (!(Tag.stringData .E6).memDec (Tag.rootCertificate .E6) (e6Root k + e6Root (rhoIdx k)) &&
        !(Tag.stringData .E6).memDec (Tag.rootCertificate .E6) (e6Root k - e6Root (rhoIdx k)) &&
        !(List.ofFn (e6Root k + e6Root (rhoIdx k))).all (· == 0))

@[expose] def checkEps : Bool :=
  (List.range (Tag.rootCertificate .E6).roots.length).all fun k =>
    epsBit (rhoIdx k) == epsBit k && (rhoIdx k != k || !epsBit k)

theorem checkProjRoot_eq : checkProjRoot = true := by decide +kernel

theorem checkProjSurj_eq : checkProjSurj = true := by decide +kernel

theorem checkFibres_eq : checkFibres = true := by decide +kernel

theorem checkPairs_eq : checkPairs = true := by decide +kernel

theorem checkEps_eq : checkEps = true := by decide +kernel

theorem rho_rho (v : Fin (Tag.rank .E6) → ℤ) : rho (rho v) = v := by
  funext j
  change Fin 6 at j
  fin_cases j <;> rfl

theorem isRoot_proj {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) : IsRoot .F4 (proj α) := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hα
  have h := checkProjRoot_eq
  simp only [checkProjRoot, List.all_eq_true, List.mem_range] at h
  exact (StringData.memDec_iff (Tag.rootCertificate_check .F4) (Tag.stringData_check .F4)).1
    (h k hk)

theorem exists_proj_eq {β : Fin (Tag.rank .F4) → ℤ} (hβ : IsRoot .F4 β) :
    ∃ α, IsRoot .E6 α ∧ proj α = β := by
  obtain ⟨m, hm, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .F4) hβ
  have h := checkProjSurj_eq
  simp only [checkProjSurj, List.all_eq_true, List.mem_range, List.any_eq_true,
    beq_iff_eq] at h
  obtain ⟨k, hk, hkm⟩ := h m hm
  exact ⟨e6Root k, RootCertificate.isRoot_root (Tag.rootCertificate_check .E6) k hk,
    List.ofFn_injective hkm⟩

theorem proj_eq_proj_iff {α α' : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hα' : IsRoot .E6 α') : proj α = proj α' ↔ α' = α ∨ α' = rho α := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hα
  obtain ⟨l, hl, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hα'
  have h := checkFibres_eq
  simp only [checkFibres, List.all_eq_true, List.mem_range] at h
  have h := h k hk l hl
  have hρ := (rhoIdx_spec hk).2
  constructor
  · intro heq
    have : (List.ofFn (proj (e6Root k)) == List.ofFn (proj (e6Root l))) = true := by
      simp [heq]
    rw [this] at h
    simp only [Bool.true_eq, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with h | h
    · left; rw [h]
    · right; rw [h, hρ]
  · rintro (h' | h')
    · rw [h']
    · rw [h', proj_rho]

theorem rho_eq_self_iff {k : ℕ} (hk : k < (Tag.rootCertificate .E6).roots.length) :
    rho (e6Root k) = e6Root k ↔ rhoIdx k = k := by
  rw [← (rhoIdx_spec hk).2]
  exact ⟨fun h => MinData.root_injOn (rhoIdx_spec hk).1 hk h, fun h => by rw [h]⟩

private theorem pairs_spec {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) :
    ¬ IsRoot .E6 (α + rho α) ∧ ¬ IsRoot .E6 (α - rho α) ∧ α + rho α ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hα
  have h := checkPairs_eq
  simp only [checkPairs, List.all_eq_true, List.mem_range] at h
  have h := h k hk
  have hne' : rhoIdx k ≠ k := fun h' => hne ((rho_eq_self_iff hk).2 h')
  simp only [Bool.or_eq_true, beq_iff_eq, hne', false_or, Bool.and_eq_true, Bool.not_eq_true',
    ] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [e6Root] at h1 h2 h3
  rw [(rhoIdx_spec hk).2] at h1 h2 h3
  refine ⟨fun hr => ?_, fun hr => ?_, fun h0 => ?_⟩
  · rw [(StringData.memDec_iff (Tag.rootCertificate_check .E6) (Tag.stringData_check .E6)).2 hr]
      at h1
    exact absurd h1 (by simp)
  · rw [(StringData.memDec_iff (Tag.rootCertificate_check .E6) (Tag.stringData_check .E6)).2 hr]
      at h2
    exact absurd h2 (by simp)
  · rw [h0] at h3
    revert h3
    decide

theorem not_isRoot_add_rho {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) :
    ¬ IsRoot .E6 (α + rho α) :=
  (pairs_spec hα hne).1

theorem not_isRoot_sub_rho {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) :
    ¬ IsRoot .E6 (α - rho α) :=
  (pairs_spec hα hne).2.1

theorem add_rho_ne_zero {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (hne : rho α ≠ α) :
    α + rho α ≠ 0 :=
  (pairs_spec hα hne).2.2

theorem eq_one_of_proj_eq_nsmul {α α' : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α)
    (hα' : IsRoot .E6 α') {c : ℕ} (hc : 0 < c) (h : proj α = c • proj α') : c = 1 := by
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

@[expose] noncomputable def twistSign (α : Fin (Tag.rank .E6) → ℤ) : ℤ := by
  classical
  exact if h : ∃ k, k < (Tag.rootCertificate .E6).roots.length ∧ e6Root k = α then
    (if epsBit (Nat.find h) then -1 else 1) else 1

theorem twistSign_root {k : ℕ} (hk : k < (Tag.rootCertificate .E6).roots.length) :
    twistSign (e6Root k) = if epsBit k then -1 else 1 := by
  classical
  have h : ∃ k', k' < (Tag.rootCertificate .E6).roots.length ∧ e6Root k' = e6Root k :=
    ⟨k, hk, rfl⟩
  rw [twistSign, dite_eq_left h]
  rw [MinData.root_injOn (Nat.find_spec h).1 hk (Nat.find_spec h).2]

theorem twistSign_eq_one_or (α : Fin (Tag.rank .E6) → ℤ) :
    twistSign α = 1 ∨ twistSign α = -1 := by
  unfold twistSign
  split_ifs <;> simp

theorem twistSign_rho {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) :
    twistSign (rho α) = twistSign α := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hα
  have h := checkEps_eq
  simp only [checkEps, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq] at h
  rw [← (rhoIdx_spec hk).2, twistSign_root (rhoIdx_spec hk).1, twistSign_root hk, (h k hk).1]

theorem twistSign_of_rho_eq {α : Fin (Tag.rank .E6) → ℤ} (hα : IsRoot .E6 α) (h : rho α = α) :
    twistSign α = 1 := by
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hα
  have hc := checkEps_eq
  simp only [checkEps, List.all_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
    Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hc
  have hfix := (rho_eq_self_iff hk).1 h
  rcases (hc k hk).2 with h' | h'
  · exact absurd hfix h'
  · rw [twistSign_root hk, h']
    rfl

theorem twistSign_single (i : Fin (Tag.rank .E6)) : twistSign (Pi.single i 1) = 1 := by
  rw [← MinData.root_basis i, twistSign_root (lt_of_lt_of_le i.2 MinData.rank_le_length),
    epsBit_single]
  rfl

theorem twistSign_neg_single (i : Fin (Tag.rank .E6)) : twistSign (-Pi.single i 1) = 1 := by
  rw [← MinData.root_image_self i,
    twistSign_root (MinData.image_lt (lt_of_lt_of_le i.2 MinData.rank_le_length) i),
    epsBit_image_self]
  rfl

section Sigma

variable {k : Type*} [Field k]

theorem sigmaGL_xu_eq (θ : k →+* k) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    sigmaGL k θ (e6Data_valid.xu k γ c) =
      e6Data_valid.xu k (rho γ) ((twistSign γ : k) * θ c) := by
  obtain ⟨j, hj, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .E6) hγ
  rw [sigmaGL_xu_root θ hj, twistSign_root hj]
  split_ifs <;> simp

theorem sigma_xm (θ : k →+* k) {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) (c : k) :
    sigma k θ (e6Data_valid.xm k γ c) =
      e6Data_valid.xm k (rho γ) ((twistSign γ : k) * θ c) :=
  Subtype.ext (sigmaGL_xu_eq θ hγ c)

theorem map_sigma_rootGroup (θ : k →+* k) (hθ : Function.Surjective θ)
    {γ : Fin (Tag.rank .E6) → ℤ} (hγ : IsRoot .E6 γ) :
    (e6Data_valid.rootGroup k γ).map (sigma k θ) = e6Data_valid.rootGroup k (rho γ) := by
  ext g
  simp only [Subgroup.mem_map, MinData.Valid.mem_rootGroup]
  constructor
  · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
    exact ⟨_, (sigma_xm θ hγ c).symm⟩
  · rintro ⟨c, rfl⟩
    obtain ⟨d, hd⟩ := hθ ((twistSign γ : k) * c)
    refine ⟨_, ⟨d, rfl⟩, ?_⟩
    rw [sigma_xm θ hγ d, hd, ← mul_assoc]
    rcases twistSign_eq_one_or γ with h | h <;> simp [h]

end Sigma

end CFSG.LieType.Steinberg.TwistedE6
