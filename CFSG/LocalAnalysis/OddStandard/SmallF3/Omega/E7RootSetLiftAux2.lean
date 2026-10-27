module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.E7RootSetLiftAux

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.OddStandard.SmallF3.Omega CFSG.OddStandard.SmallF3.Omega.E7RootSet Certificates.OmegaSevenMax
open CFSG.HardMathSupport.Timmesfeld.RootAut CFSG.HardMathSupport.Timmesfeld.LangTorus


private abbrev e7LiftP11_Ψ : Set (Fin Tag.E7.rank → ℤ) := {γ | IsRoot Tag.E7 γ}

private theorem e7LiftP11_Ψ_finite : (e7LiftP11_Ψ).Finite := finite_setOf_isRoot Tag.E7

private theorem e7LiftP11_redV_neg (v : Fin Tag.E7.rank → ℤ) : redV (-v) = -redV v := by
  funext i; exact Int.cast_neg (v i)

private theorem e7LiftP11_redV_add (u v : Fin Tag.E7.rank → ℤ) :
    redV (u + v) = redV u + redV v := by
  funext i; exact Int.cast_add (u i) (v i)

private theorem e7LiftP11_redV_zsmul (c : ℤ) (v : Fin Tag.E7.rank → ℤ) :
    redV (c • v) = c • redV v := by
  funext i
  show ((c * v i : ℤ) : ZMod 3) = c • ((v i : ℤ) : ZMod 3)
  rw [Int.cast_mul, zsmul_eq_mul]

private theorem e7LiftP11_redV_sum {ι : Type*} (s : Finset ι) (f : ι → Fin Tag.E7.rank → ℤ) :
    redV (∑ i ∈ s, f i) = ∑ i ∈ s, redV (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => funext i; exact Int.cast_zero
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, e7LiftP11_redV_add, ih]

private theorem e7LiftP11_iform_self (γ : Fin Tag.E7.rank → ℤ) (hγ : IsRoot Tag.E7 γ) :
    iform γ γ = 2 := by
  obtain ⟨j, hj⟩ := iform_self_of_isRoot hγ
  rw [hj]; norm_num [Tag.symmetrizer]

private theorem e7LiftP11_iform_neg_self (γ : Fin Tag.E7.rank → ℤ) (hγ : IsRoot Tag.E7 γ) :
    iform γ (-γ) = -2 := by
  rw [show -γ = (-1 : ℤ) • γ by simp, iform_smul_right, e7LiftP11_iform_self γ hγ]; ring

private theorem e7LiftP11_mem_neg_one_zero_one {a : ℤ} (h : a ^ 2 < 4) :
    a = -1 ∨ a = 0 ∨ a = 1 := by
  have h1 : -2 < a := by nlinarith [sq_nonneg (a + 1)]
  have h2 : a < 2 := by nlinarith [sq_nonneg (a - 1)]
  omega

private theorem e7LiftP11_int_eq_of_zmod_eq {a b : ℤ}
    (ha : a = -1 ∨ a = 0 ∨ a = 1) (hb : b = -1 ∨ b = 0 ∨ b = 1)
    (h : (a : ZMod 3) = (b : ZMod 3)) : a = b := by
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
    first | rfl | (exfalso; revert h; decide)

theorem e7LiftP11_exists_weyl_of_image_rootSet (g : OGroup qForm)
    (hg : rootSet.image (g : V ≃ₗ[ZMod 3] V) = rootSet) :
    ∃ w : WeylGroup Tag.E7, ∀ v : Fin Tag.E7.rank → ℤ,
      (g : V ≃ₗ[ZMod 3] V) (redV v) = redV (w • v) := by
  classical
  have hgmem : ∀ x ∈ rootSet, (g : V ≃ₗ[ZMod 3] V) x ∈ rootSet := by
    intro x hx
    have h := congrArg (fun s : Finset V => (↑s : Set V)) hg
    have h1 : (g : V ≃ₗ[ZMod 3] V) x ∈
        (↑(rootSet.image (g : V ≃ₗ[ZMod 3] V)) : Set V) :=
      Finset.mem_image.2 ⟨x, hx, rfl⟩
    rwa [h] at h1
  have hred_mem : ∀ γ ∈ e7LiftP11_Ψ, redV γ ∈ rootSet := by
    intro γ hγ
    rw [← SetLike.mem_coe, rootSet_eq_image]
    exact ⟨γ, hγ, rfl⟩
  have hex : ∀ γ ∈ e7LiftP11_Ψ,
      ∃ β, IsRoot Tag.E7 β ∧ redV β = (g : V ≃ₗ[ZMod 3] V) (redV γ) := by
    intro γ hγ
    have h := hgmem (redV γ) (hred_mem γ hγ)
    rw [← SetLike.mem_coe, rootSet_eq_image] at h
    exact h
  let f : (Fin Tag.E7.rank → ℤ) → (Fin Tag.E7.rank → ℤ) := fun γ =>
    if h : γ ∈ e7LiftP11_Ψ then Classical.choose (hex γ h) else 0
  have hf_red : ∀ γ (h : γ ∈ e7LiftP11_Ψ),
      redV (f γ) = (g : V ≃ₗ[ZMod 3] V) (redV γ) := by
    intro γ h
    simp only [f, dif_pos h]
    exact (Classical.choose_spec (hex γ h)).2
  have hf_root : ∀ γ (h : γ ∈ e7LiftP11_Ψ), f γ ∈ e7LiftP11_Ψ := by
    intro γ h
    have h' : f γ = Classical.choose (hex γ h) := by simp only [f, dif_pos h]
    rw [h']
    exact (Classical.choose_spec (hex γ h)).1
  have hmaps : Set.MapsTo f e7LiftP11_Ψ e7LiftP11_Ψ := fun γ h => hf_root γ h
  have hinj : Set.InjOn f e7LiftP11_Ψ := by
    intro γ hγ δ hδ h
    refine redV_injOn_roots hγ hδ ((g : V ≃ₗ[ZMod 3] V).injective ?_)
    rw [← hf_red γ hγ, ← hf_red δ hδ, h]
  have hbij : Set.BijOn f e7LiftP11_Ψ e7LiftP11_Ψ :=
    (Set.Finite.injOn_iff_bijOn_of_mapsTo e7LiftP11_Ψ_finite (f := f) hmaps).1 hinj
  have hneg : ∀ γ ∈ e7LiftP11_Ψ, f (-γ) = -f γ := by
    intro γ hγ
    refine redV_injOn_roots (hf_root (-γ) (IsRoot.neg hγ)) (IsRoot.neg (hf_root γ hγ)) ?_
    rw [hf_red (-γ) (IsRoot.neg hγ), e7LiftP11_redV_neg, map_neg, e7LiftP11_redV_neg,
      hf_red γ hγ]
  have hiform_eq : ∀ γ ∈ e7LiftP11_Ψ, ∀ δ ∈ e7LiftP11_Ψ,
      iform (f γ) (f δ) = iform γ δ := by
    intro γ hγ δ hδ
    by_cases h1 : δ = γ
    · rw [h1, e7LiftP11_iform_self _ (hf_root γ hγ), e7LiftP11_iform_self _ hγ]
    by_cases h2 : δ = -γ
    · rw [h2, hneg γ hγ]
      have ha := e7LiftP11_iform_neg_self (f γ) (hf_root γ hγ)
      have hb := e7LiftP11_iform_neg_self γ hγ
      rw [ha, hb]
    · have hcong : ((iform (f γ) (f δ) : ℤ) : ZMod 3) = ((iform γ δ : ℤ) : ZMod 3) := by
        rw [← e7LiftP11_polarV_redV (f γ) (f δ), hf_red γ hγ, hf_red δ hδ,
          CFSG.ClassicalGroups.Orthogonal.polar_map_of_mem g.2, e7LiftP11_polarV_redV γ δ]
      have hne : γ ≠ δ := fun h => h1 h.symm
      have hne' : γ ≠ -δ := fun h => h2 (by rw [h]; simp)
      have hb1 := e7LiftP11_mem_neg_one_zero_one (a := iform γ δ) (by
        have hsq := iform_sq_lt hγ hδ hne hne'
        rw [e7LiftP11_iform_self γ hγ, e7LiftP11_iform_self δ hδ] at hsq
        nlinarith)
      have hfne : f γ ≠ f δ := fun h => hne (hinj hγ hδ h)
      have hfne' : f γ ≠ -f δ := by
        intro h
        have h' : f γ = f (-δ) := by rw [hneg δ hδ]; exact h
        exact hne' (hinj hγ (IsRoot.neg hδ) h')
      have hb2 := e7LiftP11_mem_neg_one_zero_one (a := iform (f γ) (f δ)) (by
        have hsq := iform_sq_lt (hf_root γ hγ) (hf_root δ hδ) hfne hfne'
        rw [e7LiftP11_iform_self _ (hf_root γ hγ), e7LiftP11_iform_self _ (hf_root δ hδ)] at hsq
        nlinarith)
      exact e7LiftP11_int_eq_of_zmod_eq hb2 hb1 hcong
  have hiso : IsIsometry e7LiftP11_Ψ f := ⟨hbij, hiform_eq, hneg⟩
  have hcomp : IsRootComponent e7LiftP11_Ψ := e7LiftP11_isRootComponent
  have hne : e7LiftP11_Ψ.Nonempty := ⟨Pi.single 0 1, isRoot_single Tag.E7 0⟩
  obtain ⟨w, hw, hpos⟩ := exists_mem_componentWeylGroup_posRoots hcomp hiso
  have hiso' : IsIsometry e7LiftP11_Ψ (fun γ => f (w • γ)) := hiso.comp_smul hcomp hw
  have hΔ : ∀ β ∈ simpleRoots e7LiftP11_Ψ, f (w • β) ∈ simpleRoots e7LiftP11_Ψ :=
    fun β hβ => hiso'.apply_mem_simpleRoots hcomp hpos hβ
  have hΔinj : Function.Injective
      (fun β : simpleRoots e7LiftP11_Ψ => (⟨f (w • (β : Fin Tag.E7.rank → ℤ)), hΔ β β.2⟩ :
        simpleRoots e7LiftP11_Ψ)) := by
    intro β γ h
    have h' : f (w • (β : Fin Tag.E7.rank → ℤ)) = f (w • (γ : Fin Tag.E7.rank → ℤ)) :=
      congrArg Subtype.val h
    have hwβ : w • (β : Fin Tag.E7.rank → ℤ) ∈ e7LiftP11_Ψ :=
      smul_mem_of_mem_componentWeylGroup hcomp hw _ (simpleRoots_subset β.2)
    have hwγ : w • (γ : Fin Tag.E7.rank → ℤ) ∈ e7LiftP11_Ψ :=
      smul_mem_of_mem_componentWeylGroup hcomp hw _ (simpleRoots_subset γ.2)
    have := hinj hwβ hwγ h'
    exact Subtype.ext (smul_left_cancel w this)
  let π : simpleRoots e7LiftP11_Ψ ≃ simpleRoots e7LiftP11_Ψ :=
    Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hΔinj)
  obtain ⟨t, e, ht, hts, he, hcard, hncard⟩ :=
    exists_dynkinType (Or.inr (Or.inr (Or.inl rfl))) hcomp hne
  have htE7 : t = .E7 := e7LiftP11_dynkinType_E7 t ht hts (by rw [← hncard]; exact e7LiftP11_ncard)
  subst htE7
  have hσM : ∀ i j, CartanMatrix.E 7 ((e.symm.trans π).trans e i) ((e.symm.trans π).trans e j) =
      CartanMatrix.E 7 i j := by
    intro i j
    have hi := simpleRoots_subset (e.symm i).2
    have hj := simpleRoots_subset (e.symm j).2
    have he' : ∀ β γ : simpleRoots e7LiftP11_Ψ,
        iform (β : Fin Tag.E7.rank → ℤ) γ = CartanMatrix.E 7 (e β) (e γ) := by
      intro β γ
      rw [he β γ, TauCeti.DynkinType.cartanMatrix_E7]
    calc CartanMatrix.E 7 ((e.symm.trans π).trans e i) ((e.symm.trans π).trans e j)
        = CartanMatrix.E 7 (e (π (e.symm i))) (e (π (e.symm j))) := rfl
      _ = iform ((π (e.symm i) : simpleRoots e7LiftP11_Ψ) : Fin Tag.E7.rank → ℤ)
            (π (e.symm j)) := (he' _ _).symm
      _ = iform (f (w • ((e.symm i : simpleRoots e7LiftP11_Ψ) : Fin Tag.E7.rank → ℤ)))
            (f (w • (e.symm j))) := rfl
      _ = iform ((e.symm i : simpleRoots e7LiftP11_Ψ) : Fin Tag.E7.rank → ℤ) (e.symm j) :=
            hiso'.iform_eq _ hi _ hj
      _ = CartanMatrix.E 7 (e (e.symm i)) (e (e.symm j)) := he' _ _
      _ = CartanMatrix.E 7 i j := by rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hσ1 : (e.symm.trans π).trans e = 1 := e7LiftP11_rigidity _ hσM
  have hfix : ∀ β ∈ simpleRoots e7LiftP11_Ψ, f (w • β) = β := by
    intro β hβ
    have h2 := Equiv.congr_fun hσ1 (e ⟨β, hβ⟩)
    have h2' : e (π ⟨β, hβ⟩) = e ⟨β, hβ⟩ := by
      rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.symm_apply_apply,
        Equiv.Perm.one_apply] at h2
      exact h2
    have h3 : π ⟨β, hβ⟩ = ⟨β, hβ⟩ := e.injective h2'
    have h4 : (π ⟨β, hβ⟩ : Fin Tag.E7.rank → ℤ) = (⟨β, hβ⟩ : simpleRoots e7LiftP11_Ψ) :=
      congrArg Subtype.val h3
    simpa [π, Equiv.ofBijective_apply] using h4
  obtain ⟨u, hu, hfu⟩ := exists_smul_eq_of_isIsometry hcomp hiso hw hfix
  refine ⟨u, fun v => ?_⟩
  have hv : v = ∑ i, v i • (Pi.single i 1 : Fin Tag.E7.rank → ℤ) := by
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single j (fun k _ hk => by rw [Pi.single_eq_of_ne (Ne.symm hk), mul_zero])
      (fun h => absurd (Finset.mem_univ j) h), Pi.single_eq_same, mul_one]
  have hredv : redV v = ∑ i, v i • redV (Pi.single i 1 : Fin Tag.E7.rank → ℤ) := by
    calc redV v = redV (∑ i, v i • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) := congrArg redV hv
      _ = ∑ i, redV (v i • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) := e7LiftP11_redV_sum _ _
      _ = ∑ i, v i • redV (Pi.single i 1 : Fin Tag.E7.rank → ℤ) :=
          Finset.sum_congr rfl fun i _ => e7LiftP11_redV_zsmul (v i) _
  have hgsum : (g : V ≃ₗ[ZMod 3] V) (redV v) =
      ∑ i, v i • redV (f (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) := by
    rw [hredv, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hf_red _ (isRoot_single Tag.E7 i)]
  have hfsum : ∑ i, v i • redV (f (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) =
      redV (u • v) := by
    have h1 : ∀ i, f (Pi.single i 1 : Fin Tag.E7.rank → ℤ) = u • Pi.single i 1 :=
      fun i => hfu _ (isRoot_single Tag.E7 i)
    have h2 : ∑ i, v i • redV (f (Pi.single i 1)) =
        ∑ i, redV (v i • f (Pi.single i 1)) :=
      Finset.sum_congr rfl fun i _ => (e7LiftP11_redV_zsmul (v i) _).symm
    rw [h2, ← e7LiftP11_redV_sum]
    have h3 : ∑ i, v i • f (Pi.single i 1 : Fin Tag.E7.rank → ℤ) = u • v := by
      have h4 : u • v = u • (∑ i, v i • (Pi.single i 1 : Fin Tag.E7.rank → ℤ)) :=
        congrArg (fun x => u • x) hv
      rw [h4, Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [h1 i, smul_comm]
    rw [h3]
  rw [hgsum, hfsum]

end CFSG.StandardType

end
