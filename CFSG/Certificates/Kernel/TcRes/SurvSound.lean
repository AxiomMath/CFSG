module

public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4RCore
public import CFSG.LocalAnalysis.StandardType.GGSixTCWP4Orbit
public import CFSG.Certificates.Kernel.TcRes.RootSound
public import Certificates.Data.Kernel.TcRes.C3

public section

namespace CFSG.KC.TcRes

open Certificates.TcRes CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
open CFSG.Assembly (LargeEvenLabel LargeEvenSplit LargeEvenHalfSplit)
open CFSG.StandardType (GGLabelIso)

theorem surv_lines {τ : Tag} {p : ℕ} [Fact p.Prime] {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {F f' : ℕ} (hflag : FlagTransfer p F f') (P : Submodule (ZMod p) (Fin τ.rank → ZMod p))
    (iJ : KernelComponent (tcChiPl τ p P)) {dJ : TcrCData}
    (hdJ : TcDataOK ρ (componentRoots (tcChiPl τ p P) iJ) dJ) {γ0 : Fin τ.rank → ℤ}
    (hγ0 : γ0 ∈ componentRoots (tcChiPl τ p P) iJ) {n : ℕ} (xv : ℕ → Fin τ.rank → ZMod p)
    (hxv : ∀ y < n, xv y ∈ P ∧ xv y ≠ 0)
    (hcover : ∀ v ∈ P, v ≠ 0 → ∃ y < n, ∃ c : ZMod p, c ≠ 0 ∧ v = c • xv y)
    (Ψ : ℕ → Set (Fin τ.rank → ℤ)) (ds : ℕ → TcrCData)
    (hΨ : ∀ y < n, ∃ i : KernelComponent (tcChiLn τ p (xv y)),
      Ψ y = componentRoots (tcChiLn τ p (xv y)) i)
    (hγΨ : ∀ y < n, γ0 ∈ Ψ y) (hds : ∀ y < n, TcDataOK ρ (Ψ y) (ds y))
    {x : Fin τ.rank → ZMod p} (hxP : x ∈ P) (hx0 : x ≠ 0) (ix : KernelComponent (tcChiLn τ p x))
    (hJx : componentRoots (tcChiPl τ p P) iJ ⊆ componentRoots (tcChiLn τ p x) ix)
    (hne : componentRoots (tcChiLn τ p x) ix ≠ componentRoots (tcChiPl τ p P) iJ)
    (hsplit : ∃ lab', GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn τ p x) ix)) ∧
      LargeEvenSplit p lab')
    (hoth : ∀ d ∈ P, d ≠ 0 → (∀ c : ZMod p, d ≠ c • x) → ∀ i : KernelComponent (tcChiLn τ p d),
      componentRoots (tcChiPl τ p P) iJ ⊆ componentRoots (tcChiLn τ p d) i →
      GGLabelIso (LabAt ρ F (componentRoots (tcChiLn τ p d) i))
        (LabAt ρ F (componentRoots (tcChiPl τ p P) iJ)) ∨
      ∃ (c : Prop) (lab' : LargeEvenLabel),
        GGLabelIso lab' (LabAt ρ F (componentRoots (tcChiLn τ p d) i)) ∧
        LargeEvenHalfSplit p lab' c) :
    ∃ y < n, Ψ y = componentRoots (tcChiLn τ p x) ix ∧
      Ψ y ≠ componentRoots (tcChiPl τ p P) iJ ∧
      (tcrLabsOf (ds y) f').any (tcrSplitT p) = true ∧
      ∀ z < n, z ≠ y →
        (tcrLabsOf (ds z) f').any (fun l => (tcrLabsOf dJ f').contains l) = true ∨
        (tcrLabsOf (ds z) f').any (tcrHalfSplitT p) = true := by
  have hγx : γ0 ∈ componentRoots (tcChiLn τ p x) ix := hJx hγ0
  have hcomp : ∀ y < n, ∀ c : ZMod p, c ≠ 0 → c • x = xv y →
      Ψ y = componentRoots (tcChiLn τ p x) ix := by
    intro y hy c hc hcy
    obtain ⟨i, hi⟩ := hΨ y hy
    have hker : kernelRoots (tcChiLn τ p (xv y)) = kernelRoots (tcChiLn τ p x) := by
      rw [← hcy]
      exact kernelRoots_chiQ_smul c hc x
    have h2 : γ0 ∈ componentRoots (tcChiLn τ p (xv y)) i := hi ▸ hγΨ y hy
    rw [hi]
    exact Set.Subset.antisymm (componentRoots_subset_of_kernel_subset hker.le h2 hγx)
      (componentRoots_subset_of_kernel_subset hker.ge hγx h2)
  obtain ⟨y, hy, c, hc0, hxc⟩ := hcover x hxP hx0
  have hΨy : Ψ y = componentRoots (tcChiLn τ p x) ix :=
    hcomp y hy c⁻¹ (inv_ne_zero hc0) (by rw [hxc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  have hdx : TcDataOK ρ (componentRoots (tcChiLn τ p x) ix) (ds y) := hΨy ▸ hds y hy
  refine ⟨y, hy, hΨy, hΨy ▸ hne, (hflag (ds y)).1 (tcrLabs_split_of hdx hsplit), ?_⟩
  intro z hz hzy
  obtain ⟨hzP, hz0⟩ := hxv z hz
  by_cases hprop : ∃ c : ZMod p, xv z = c • x
  · obtain ⟨c', hc'⟩ := hprop
    have hc'0 : c' ≠ 0 := by
      rintro rfl
      exact hz0 (by simpa using hc')
    have hΨz := hcomp z hz c' hc'0 hc'.symm
    have hdd : TcDataOK ρ (componentRoots (tcChiLn τ p x) ix) (ds z) := hΨz ▸ hds z hz
    right
    have h3 := tcrLabs_split_of hdd hsplit
    have h4 : (tcrLabsOf (ds z) F).any (tcrHalfSplitT p) = true := by
      rw [List.any_eq_true] at h3 ⊢
      obtain ⟨l, hl, hs⟩ := h3
      exact ⟨l, hl, tcrSplit_half l hs⟩
    exact (hflag (ds z)).2.1 h4
  · push Not at hprop
    obtain ⟨i, hi⟩ := hΨ z hz
    have h2 : γ0 ∈ componentRoots (tcChiLn τ p (xv z)) i := hi ▸ hγΨ z hz
    have hsub : componentRoots (tcChiPl τ p P) iJ ⊆ componentRoots (tcChiLn τ p (xv z)) i := by
      have hker : kernelRoots (tcChiPl τ p P) ⊆ kernelRoots (tcChiLn τ p (xv z)) :=
        kernelRoots_chiQ_mono (Set.singleton_subset_iff.2 hzP)
      exact componentRoots_subset_of_kernel_subset hker hγ0 h2
    have hdd : TcDataOK ρ (componentRoots (tcChiLn τ p (xv z)) i) (ds z) := hi ▸ hds z hz
    rcases hoth _ hzP hz0 hprop i hsub with hov | hhalf
    · left
      exact (hflag dJ).2.2 (ds z) (tcrLabs_overlap_of hdd hdJ hov)
    · right
      exact (hflag (ds z)).2.1 (tcrLabs_half_of hdd hhalf)

theorem image_eq_kernelRoots {τ : Tag} {p N : ℕ} {vec : ℕ → Fin τ.rank → ℤ} {rt : ℕ → ℕ → ℕ}
    {adj : ℕ → ℕ → Bool} {neg : ℕ → ℕ} (hD : DatumRaw τ N vec rt adj neg)
    (Q : Set (Fin τ.rank → ZMod p)) (Φ : Set ℕ)
    (hΦ : ∀ g, g ∈ Φ ↔ g < N ∧ ∀ v ∈ Q, ∑ m, v m * ((vec g m : ℤ) : ZMod p) = 0) :
    vec '' Φ = kernelRoots (tcChiQ τ p Q) := by
  ext γ
  rw [mem_kernelRoots_chiQ]
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨hgN, hv⟩ := (hΦ g).1 hg
    refine ⟨hD.isRoot g hgN, fun v hvQ => ?_⟩
    rw [← hv v hvQ]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _
  · rintro ⟨hγ, hv⟩
    obtain ⟨g, hgN, rfl⟩ := hD.exists_eq hγ
    refine ⟨g, (hΦ g).2 ⟨hgN, fun v hvQ => ?_⟩, rfl⟩
    rw [← hv v hvQ]
    exact Finset.sum_congr rfl fun m _ => mul_comm _ _

theorem plane_cond {n p : ℕ} {u1 u2 : Fin n → ZMod p} {P : Submodule (ZMod p) (Fin n → ZMod p)}
    (hP : ∀ v, v ∈ P ↔ ∃ s t : ZMod p, v = s • u1 + t • u2) (w : Fin n → ZMod p) :
    (∀ v ∈ (P : Set (Fin n → ZMod p)), ∑ m, v m * w m = 0) ↔
      (∑ m, u1 m * w m = 0 ∧ ∑ m, u2 m * w m = 0) := by
  constructor
  · intro h
    exact ⟨h u1 ((hP u1).2 ⟨1, 0, by simp⟩), h u2 ((hP u2).2 ⟨0, 1, by simp⟩)⟩
  · rintro ⟨h1, h2⟩ v hv
    obtain ⟨s, t, rfl⟩ := (hP v).1 hv
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, Finset.sum_add_distrib,
      mul_assoc, ← Finset.mul_sum, h1, h2, mul_zero, add_zero]

end CFSG.KC.TcRes

end
