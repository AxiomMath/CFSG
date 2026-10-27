module

public import CFSG.ClassicalInvolution.Q3.TL4E3S3OM1RB

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.Blueprint

namespace E3S3O

variable {W : Type} [Group W] [Finite W] {Φ : Set (Subgroup W)} {K K' : Subgroup W} {k k' : W}
  {Q : Type} [Group Q]

theorem fix_of_fix_map (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) {σ : MulAut W}
    (hperm : ∀ M ∈ Φ, M.map σ.toMonoidHom ∈ Φ) (hσ : f.ker.map σ.toMonoidHom = f.ker) (g : W)
    (hfix : ∀ c ∈ (conjSub g K).map f, descend f hf σ hσ c = c) :
    ∀ x ∈ conjSub g K, σ x = x := by
  have hcl := h.fam.hyp.conjInvariant
  have hker := ker_eq_center_of_simple h f hf hf2 hs
  obtain ⟨hquat, hinf, -⟩ := members_of_simple h f hf hf2 hs hOS
  have hσb : ∀ w, descend f hf σ hσ (f w) = f (σ w) := descend_apply f hf σ hσ
  have hcomp : f.comp σ.toMonoidHom = (descend f hf σ hσ).toMonoidHom.comp f := by
    ext w
    exact (hσb w).symm
  have hMσ : (conjSub g K).map σ.toMonoidHom = conjSub g K := by
    refine eq_of_map_eq h.fam hker.le (hperm _ (hcl g K h.memK)) (hcl g K h.memK)
      (hquat g).some ?_
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
    ext y
    refine ⟨?_, fun hy => ⟨y, hy, hfix y hy⟩⟩
    rintro ⟨z, hz, rfl⟩
    show descend f hf σ hσ z ∈ _
    rw [hfix z hz]
    exact hz
  intro x hx
  have h1 : σ x ∈ conjSub g K := by
    have := Subgroup.mem_map_of_mem σ.toMonoidHom hx
    rw [hMσ] at this
    exact this
  have h3 : f (σ x) = f x := by
    rw [← hσb]
    exact hfix _ (Subgroup.mem_map_of_mem f hx)
  have h4 : x⁻¹ * σ x ∈ conjSub g K ⊓ f.ker :=
    ⟨(conjSub g K).mul_mem ((conjSub g K).inv_mem hx) h1, by
      show x⁻¹ * σ x ∈ f.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, h3, inv_mul_cancel]⟩
  rw [hinf g, Subgroup.mem_bot] at h4
  exact (inv_mul_eq_one.mp h4).symm

theorem mem_omegaNbr_of_map (h : TwinBase3 Φ K K' k k') (f : W →* Q)
    (hf : Function.Surjective f) (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) (g : W)
    (hne : (conjSub g K).map f ≠ K.map f)
    (hle : (conjSub g K).map f ≤ Subgroup.normalizer (K.map f : Set Q)) :
    conjSub g K ∈ omegaNbr Φ K := by
  have hcl := h.fam.hyp.conjInvariant
  obtain ⟨-, -, heq⟩ := members_of_simple h f hf hf2 hs hOS
  have h2 := isPGroup_conj_of_simple h f hf hf2 hs hOS g
  refine ⟨hcl g K h.memK, fun h1 => hne (by rw [h1]), conjSub g K,
    mem_RSet_of_isSylow2In (hcl g K h.memK) ⟨le_rfl, h2, fun _ hV _ hle => le_antisymm hV hle⟩,
    le_rfl, fun m hm => ?_⟩
  rw [mem_normalizer_iff_conjSub_eq]
  have h1 : f m ∈ Subgroup.normalizer (K.map f : Set Q) := hle (Subgroup.mem_map_of_mem f hm)
  rw [mem_normalizer_iff_conjSub_eq] at h1
  simpa only [conjSub_one] using heq m 1 (by rw [AscQuot.map_conjSub, conjSub_one]; exact h1)

theorem map_sigmaFixGen (h : TwinBase3 Φ K K' k k') (f : W →* Q) (hf : Function.Surjective f)
    (hf2 : IsPGroup 2 ↥f.ker) (hs : IsSimpleGroup Q)
    (hOS : Balance.oddCoreIn (Subgroup.centralizer ({f k} : Set Q)) = ⊥) {σ : MulAut W}
    (hperm : ∀ M ∈ Φ, M.map σ.toMonoidHom ∈ Φ) (hσ : f.ker.map σ.toMonoidHom = f.ker) :
    (sigmaFixGen K σ).map f = sigmaFixGen (K.map f) (descend f hf σ hσ) := by
  have hσb : ∀ w, descend f hf σ hσ (f w) = f (σ w) := descend_apply f hf σ hσ
  rw [sigmaFixGen, sigmaFixGen, Subgroup.map_iSup]
  refine le_antisymm (iSup_le fun M => ?_) (iSup₂_le fun C hC => ?_)
  · rw [Subgroup.map_iSup]
    refine iSup_le fun hM => ?_
    obtain ⟨⟨g, hg⟩, hfixM⟩ := hM
    have hg' : conjSub g K = M := hg
    subst hg'
    refine le_iSup₂ (f := fun C (_ : C ∈ {C : Subgroup Q | C ∈ CoreAssembly.conjClass (K.map f) ∧
      ∀ x ∈ C, descend f hf σ hσ x = x}) => C) _ ⟨⟨f g, (AscQuot.map_conjSub f g K).symm⟩, ?_⟩
    rintro _ ⟨x, hx, rfl⟩
    rw [hσb, hfixM x hx]
  · obtain ⟨⟨q, hq⟩, hfixC⟩ := hC
    have hq' : conjSub q (K.map f) = C := hq
    subst hq'
    obtain ⟨g, rfl⟩ := hf q
    rw [← AscQuot.map_conjSub] at hfixC ⊢
    have hfixM := fix_of_fix_map h f hf hf2 hs hOS hperm hσ g hfixC
    refine Subgroup.map_mono ?_ |>.trans (le_iSup (fun M => (⨆ (_ : M ∈ {M : Subgroup W |
      M ∈ CoreAssembly.conjClass K ∧ ∀ x ∈ M, σ x = x}), M).map f) (conjSub g K))
    exact le_iSup (fun (_ : conjSub g K ∈ {M : Subgroup W | M ∈ CoreAssembly.conjClass K ∧
      ∀ x ∈ M, σ x = x}) => conjSub g K) ⟨⟨g, rfl⟩, hfixM⟩

end E3S3O

end CFSG.ClassicalInvolution.Q3.TL4
