module

public import CFSG.LieType.Chevalley.SignCharacterCertificates

public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix RootCertificate

variable {τ : Tag}

structure WitEntry where
  root : ℕ
  kind : ℕ
  other : ℕ
  word : List ℕ

structure WitCert where
  mask : List Bool
  rho : ℕ
  sigma : ℕ
  wits : List WitEntry

end CFSG.LieType.Chevalley

namespace CFSG.Blueprint.Chevalley.RootCertificate

open CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint

variable {τ : Tag} (C : RootCertificate τ)

@[expose] def evenIdx (m : List Bool) (k : ℕ) : Bool :=
  decide (Even (maskPairing (listMask m) (C.root k)))

@[expose] def wordImage (ω : List ℕ) (k : ℕ) : ℕ :=
  (toFinWord (τ := τ) ω).foldr (fun i k => C.image k i) k

variable {C}

theorem wordImage_spec
    (hC : C.check = true) (ω : List ℕ) {k : ℕ} (hk : k < C.roots.length) :
    C.wordImage ω k < C.roots.length ∧
      C.root (C.wordImage ω k) = (coxeterSystem τ).wordProd (toFinWord ω) • C.root k := by
  unfold wordImage
  induction toFinWord (τ := τ) ω with
  | nil => exact ⟨hk, by simp⟩
  | cons i l ih =>
    obtain ⟨h1, h2⟩ := ih
    obtain ⟨h3, h4⟩ := image_spec hC h1 i
    refine ⟨h3, ?_⟩
    rw [List.foldr_cons, h4, h2, CoxeterSystem.wordProd_cons, mul_smul, simple_smul]

end CFSG.Blueprint.Chevalley.RootCertificate

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint Matrix RootCertificate

variable {τ : Tag}

namespace WitEntry

variable (C : RootCertificate τ) (m : List Bool) (kρ kσ : ℕ) (e : WitEntry)

@[expose] def valid : Bool :=
  match e.kind with
  | 0 => (List.range C.roots.length).all fun k => !(C.evenIdx m k) ||
      (List.ofFn (C.root k) == List.ofFn (C.root e.root)) ||
      (List.ofFn (C.root k) == List.ofFn (-C.root e.root)) ||
      decide (iform (C.root e.root) (C.root k) = 0)
  | 1 => decide (e.other < C.roots.length) && C.evenIdx m e.other &&
      decide (2 * iform (C.root e.other) (C.root e.root) %
        iform (C.root e.other) (C.root e.other) = 0) &&
      decide (Odd (2 * iform (C.root e.other) (C.root e.root) /
        iform (C.root e.other) (C.root e.other)))
  | 2 => decide (τ = .F4) && C.evenIdx m (C.wordImage e.word kρ) &&
      C.evenIdx m (C.wordImage e.word kσ) &&
      (List.ofFn (C.root (C.wordImage e.word kρ) + C.root (C.wordImage e.word kσ)) ==
        List.ofFn (C.root e.root)) &&
      decide (iform (C.root (C.wordImage e.word kρ)) (C.root e.root) ≠ 0) &&
      decide (iform (C.root (C.wordImage e.word kσ)) (C.root e.root) ≠ 0)
  | _ => false

end WitEntry

namespace WitCert

variable (C : RootCertificate τ) (S : WitCert)

@[expose] def check : Bool :=
  decide (S.rho < C.roots.length) && decide (S.sigma < C.roots.length) &&
  (List.range C.roots.length).all fun k => !(C.evenIdx S.mask k) ||
    S.wits.any fun e => (e.root == k) && e.valid C S.mask S.rho S.sigma

variable {C S}

theorem mem_kernelRoots_of_evenIdx (hC : C.check = true) {k : ℕ} (hk : k < C.roots.length)
    (h : C.evenIdx S.mask k = true) : C.root k ∈ kernelRoots (maskChar (listMask S.mask)) :=
  mem_kernelRoots_maskChar.2 ⟨isRoot_root hC k hk, by simpa [evenIdx] using h⟩

theorem witness_of_check
    (hC : C.check = true) (hS : S.check C = true) {α : Fin τ.rank → ℤ}
    (hα : α ∈ kernelRoots (maskChar (τ := τ) (listMask S.mask))) :
    (∀ γ ∈ kernelRoots (maskChar (τ := τ) (listMask S.mask)), γ = α ∨ γ = -α ∨
        iform α γ = 0) ∨
    (∃ β ∈ kernelRoots (maskChar (τ := τ) (listMask S.mask)), ∃ n : ℤ, Odd n ∧
      n * iform β β = 2 * iform β α) ∨
    (τ = .F4 ∧ ∃ w : WeylGroup τ,
      w • C.root S.rho ∈ kernelRoots (maskChar (τ := τ) (listMask S.mask)) ∧
      w • C.root S.sigma ∈ kernelRoots (maskChar (τ := τ) (listMask S.mask)) ∧
      α = w • C.root S.rho + w • C.root S.sigma ∧
      iform (w • C.root S.rho) α ≠ 0 ∧ iform (w • C.root S.sigma) α ≠ 0) := by
  simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true, beq_iff_eq] at hS
  obtain ⟨⟨hρ, hσ⟩, hall⟩ := hS
  obtain ⟨k, hk, rfl⟩ := RootCertificate.exists_root_eq hC hα.1
  have hev : C.evenIdx S.mask k = true := by
    simpa [evenIdx] using (mem_kernelRoots_maskChar.1 hα).2
  rcases hall k hk with h | ⟨e, he, hek, hval⟩
  · rw [hev] at h
    exact absurd h (by decide)
  subst hek
  unfold WitEntry.valid at hval
  split at hval
  ·
    left
    intro γ hγ
    obtain ⟨k', hk', rfl⟩ := RootCertificate.exists_root_eq hC hγ.1
    simp only [List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
      beq_iff_eq, decide_eq_true_eq] at hval
    rcases hval k' hk' with ((h | h) | h) | h
    · have : C.evenIdx S.mask k' = true := by
        simpa [evenIdx] using (mem_kernelRoots_maskChar.1 hγ).2
      rw [this] at h
      exact absurd h (by decide)
    · exact Or.inl (List.ofFn_injective h)
    · exact Or.inr (Or.inl (List.ofFn_injective h))
    · exact Or.inr (Or.inr h)
  ·
    right; left
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hval
    obtain ⟨⟨⟨hlt, hev'⟩, hdvd⟩, hodd⟩ := hval
    refine ⟨C.root e.other, mem_kernelRoots_of_evenIdx hC hlt hev', _, hodd, ?_⟩
    exact Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero hdvd)
  ·
    right; right
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hval
    obtain ⟨⟨⟨⟨⟨hF4, h1⟩, h2⟩, hsum⟩, hne1⟩, hne2⟩ := hval
    obtain ⟨hρ1, hρ2⟩ := wordImage_spec hC e.word hρ
    obtain ⟨hσ1, hσ2⟩ := wordImage_spec hC e.word hσ
    refine ⟨hF4, (coxeterSystem τ).wordProd (toFinWord e.word), ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hρ2]
      exact mem_kernelRoots_of_evenIdx hC hρ1 h1
    · rw [← hσ2]
      exact mem_kernelRoots_of_evenIdx hC hσ1 h2
    · rw [← hρ2, ← hσ2]
      exact (List.ofFn_injective hsum).symm
    · rw [← hρ2]
      exact hne1
    · rw [← hσ2]
      exact hne2
  · exact absurd hval (by decide)

end WitCert

@[expose] def f4Rho : Fin τ.rank → ℤ :=
  fun j => ([-1, -2, -3, -2] : List ℤ).getD j 0

@[expose] def f4Sigma : Fin τ.rank → ℤ :=
  fun j => ([-1, -1, -1, 0] : List ℤ).getD j 0

@[expose] def KernelRootWitness
    (χ : Multiplicative (Fin τ.rank → ℤ) →* ℤˣ)
    (α : Fin τ.rank → ℤ) : Prop :=
  (∀ γ ∈ kernelRoots χ, γ = α ∨ γ = -α ∨ iform α γ = 0) ∨
  (∃ β ∈ kernelRoots χ, ∃ n : ℤ, Odd n ∧ n * iform β β = 2 * iform β α) ∨
  (τ = .F4 ∧ ∃ w : WeylGroup τ, w • f4Rho ∈ kernelRoots χ ∧ w • f4Sigma ∈ kernelRoots χ ∧
    α = w • f4Rho + w • f4Sigma ∧ iform (w • f4Rho) α ≠ 0 ∧ iform (w • f4Sigma) α ≠ 0)

theorem WitCert.kernelRootWitness_of_check
    {C : RootCertificate τ} {S : WitCert}
    (hC : C.check = true) (hS : S.check C = true)
    (hρ : τ = .F4 → C.root S.rho = f4Rho) (hσ : τ = .F4 → C.root S.sigma = f4Sigma)
    {α : Fin τ.rank → ℤ} (hα : α ∈ kernelRoots (maskChar (τ := τ) (listMask S.mask))) :
    KernelRootWitness (maskChar (listMask S.mask)) α := by
  rcases WitCert.witness_of_check hC hS hα with h | h | ⟨hF4, h⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rw [hρ hF4, hσ hF4] at h
    exact Or.inr (Or.inr ⟨hF4, h⟩)

end CFSG.LieType.Chevalley
