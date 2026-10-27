module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoComb
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFMonoDef

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V] [FiniteDimensional (ZMod 3) V]
  {Q : QuadraticForm (ZMod 3) V} {c : ZMod 3}

@[expose] noncomputable def ffRhoUFun (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U) : Equiv.Perm (Fin 6) :=
  Classical.choose ((mem_ffP0_iff hQ fr).mp (hUle u.2))

 theorem ffRhoUFun_spec (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U) :
    ∃ J : Finset (Fin 6), Even J.card ∧
      (u : OGroup Q) = fr.permOrth (ffRhoUFun hQ fr U hUle u) * fr.signChange J := by
  obtain ⟨-, J, hJ, heq⟩ := Classical.choose_spec ((mem_ffP0_iff hQ fr).mp (hUle u.2))
  exact ⟨J, hJ, heq⟩

 theorem ffRhoUFun_eq_of (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U)
    {σ : Equiv.Perm (Fin 6)} {J : Finset (Fin 6)}
    (h : (u : OGroup Q) = fr.permOrth σ * fr.signChange J) :
    ffRhoUFun hQ fr U hUle u = σ := by
  obtain ⟨J', -, h'⟩ := ffRhoUFun_spec hQ fr U hUle u
  exact (ffMono_unique fr (h'.symm.trans h)).1

 theorem ffRhoUFun_mul (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (a b : ↥U) :
    ffRhoUFun hQ fr U hUle (a * b) =
      ffRhoUFun hQ fr U hUle a * ffRhoUFun hQ fr U hUle b := by
  obtain ⟨J, -, ha⟩ := ffRhoUFun_spec hQ fr U hUle a
  obtain ⟨K, -, hb⟩ := ffRhoUFun_spec hQ fr U hUle b
  apply ffRhoUFun_eq_of
  rw [Submonoid.coe_mul, ha, hb, ffMono_mul]

 theorem ffRhoUFun_one (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) :
    ffRhoUFun hQ fr U hUle (1 : ↥U) = 1 := by
  apply ffRhoUFun_eq_of (J := ∅)
  simp [fr.permOrth_one, fr.signChange_empty]

@[expose] noncomputable def ffRhoU (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) : ↥U →* Equiv.Perm (Fin 6) where
  toFun := ffRhoUFun hQ fr U hUle
  map_one' := ffRhoUFun_one hQ fr U hUle
  map_mul' := ffRhoUFun_mul hQ fr U hUle

 theorem ffRhoU_apply (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U) :
    ffRhoU hQ fr U hUle u = ffRhoUFun hQ fr U hUle u := rfl

 theorem ffRhoU_spec (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U) :
    ∃ J : Finset (Fin 6), Even J.card ∧
      (u : OGroup Q) = fr.permOrth (ffRhoU hQ fr U hUle u) * fr.signChange J := by
  obtain ⟨J, hJ, h⟩ := ffRhoUFun_spec hQ fr U hUle u
  rw [← ffRhoU_apply] at h
  exact ⟨J, hJ, h⟩

 theorem ffRhoU_eq_of (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U)
    {σ : Equiv.Perm (Fin 6)} {J : Finset (Fin 6)}
    (h : (u : OGroup Q) = fr.permOrth σ * fr.signChange J) :
    ffRhoU hQ fr U hUle u = σ := by
  rw [ffRhoU_apply]
  exact ffRhoUFun_eq_of hQ fr U hUle u h

 theorem ffRhoU_signChange (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (K : Finset (Fin 6))
    (hK : fr.signChange K ∈ U) :
    ffRhoU hQ fr U hUle ⟨fr.signChange K, hK⟩ = 1 :=
  ffRhoU_eq_of hQ fr U hUle _ (σ := 1) (J := K) (by rw [fr.permOrth_one, one_mul])

 theorem ffRhoU_mem_monoD (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) (u : ↥U) :
    ffRhoU hQ fr U hUle u ∈ monoD := by
  obtain ⟨J, -, heq⟩ := ffRhoU_spec hQ fr U hUle u
  obtain ⟨σ, hσ, J', -, heq'⟩ := (mem_ffP0_iff hQ fr).mp (hUle u.2)
  have h := (ffMono_unique fr (heq.symm.trans heq')).1
  rwa [h]

 theorem ffRhoU_mul_self (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr)
    (hsq : ∀ u ∈ U, u * u = 1 ∨ u * u = piOrth Q) (u : ↥U) :
    ffRhoU hQ fr U hUle u * ffRhoU hQ fr U hUle u = 1 := by
  obtain ⟨J, -, heq⟩ := ffRhoU_spec hQ fr U hUle u
  have hcomp : (u : OGroup Q) * u =
      fr.permOrth (ffRhoU hQ fr U hUle u * ffRhoU hQ fr U hUle u) *
        fr.signChange (symmDiff (J.map (ffRhoU hQ fr U hUle u)⁻¹.toEmbedding) J) := by
    rw [heq, ffMono_mul]
  rcases hsq u u.2 with h | h
  · have h1 : (1 : OGroup Q) = fr.permOrth 1 * fr.signChange (∅ : Finset (Fin 6)) := by
      rw [fr.permOrth_one, fr.signChange_empty, one_mul]
    exact (ffMono_unique fr (hcomp.symm.trans (h.trans h1))).1
  · have hpi : piOrth Q = fr.permOrth 1 * fr.signChange (Finset.univ : Finset (Fin 6)) := by
      rw [fr.permOrth_one, one_mul, fr.piOrth_eq_signChange_univ]
    exact (ffMono_unique fr (hcomp.symm.trans (h.trans hpi))).1

@[expose] noncomputable def ffFU (fr : NFrame Q (Fin 6) c) (U : Subgroup (OGroup Q)) :
    Finset (Finset (Fin 6)) := by
  classical
  exact Finset.univ.filter fun K => Even K.card ∧ fr.signChange K ∈ U

 theorem mem_ffFU_iff {fr : NFrame Q (Fin 6) c} {U : Subgroup (OGroup Q)}
    {K : Finset (Fin 6)} : K ∈ ffFU fr U ↔ Even K.card ∧ fr.signChange K ∈ U := by
  classical
  simp [ffFU]

@[expose] noncomputable def ffFUtoKer (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) :
    ↥(ffFU fr U) → ↥(ffRhoU hQ fr U hUle).ker := fun K =>
  ⟨⟨fr.signChange K.1, (mem_ffFU_iff.mp K.2).2⟩,
    ffRhoU_signChange hQ fr U hUle K.1 (mem_ffFU_iff.mp K.2).2⟩

 theorem ffFUtoKer_injective (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) :
    Function.Injective (ffFUtoKer hQ fr U hUle) := by
  intro K L h
  apply Subtype.ext
  apply fr.signChange_injective
  exact congrArg (fun x : ↥(ffRhoU hQ fr U hUle).ker => (x.1.1 : OGroup Q)) h

 theorem ffFUtoKer_surjective (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) :
    Function.Surjective (ffFUtoKer hQ fr U hUle) := by
  intro v
  obtain ⟨J, hJ, heq⟩ := ffRhoU_spec hQ fr U hUle v.1
  rw [v.2, fr.permOrth_one, one_mul] at heq
  refine ⟨⟨J, (mem_ffFU_iff).mpr ⟨hJ, ?_⟩⟩, ?_⟩
  · rw [← heq]; exact v.1.2
  · apply Subtype.ext
    apply Subtype.ext
    exact heq.symm

 theorem ffRhoU_ker_card (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr) :
    Nat.card (ffRhoU hQ fr U hUle).ker = (ffFU fr U).card := by
  have e : ↥(ffFU fr U) ≃ ↥(ffRhoU hQ fr U hUle).ker :=
    Equiv.ofBijective (ffFUtoKer hQ fr U hUle)
      ⟨ffFUtoKer_injective hQ fr U hUle, ffFUtoKer_surjective hQ fr U hUle⟩
  calc Nat.card (ffRhoU hQ fr U hUle).ker
      = Nat.card ↥(ffFU fr U) := (Nat.card_congr e).symm
    _ = (ffFU fr U).card := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_coe (ffFU fr U)

 theorem eq_compl_of_symmDiff_eq_univ {A J : Finset (Fin 6)}
    (h : symmDiff A J = Finset.univ) : A = Jᶜ := by
  ext i
  have hi : i ∈ symmDiff A J := by rw [h]; exact Finset.mem_univ i
  rw [Finset.mem_symmDiff] at hi
  simp only [Finset.mem_compl]
  tauto

 theorem ffFU_subset_ffF (hQ : Q.Nondegenerate) (fr : NFrame Q (Fin 6) c)
    (U : Subgroup (OGroup Q)) (hUle : U ≤ ffP0 hQ fr)
    (hcomm : ∀ u ∈ U, ∀ v ∈ U, u * v = v * u ∨ u * v = piOrth Q * (v * u))
    {σ : Equiv.Perm (Fin 6)} (hσR : σ ∈ (ffRhoU hQ fr U hUle).range) :
    ffFU fr U ⊆ ffF σ := by
  intro K hK
  obtain ⟨hKeven, hKU⟩ := (mem_ffFU_iff).mp hK
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.mp hσR
  obtain ⟨J, -, heq⟩ := ffRhoU_spec hQ fr U hUle v
  rw [hv] at heq
  have hconj : (v : OGroup Q) * fr.signChange K =
      fr.signChange (K.map σ.toEmbedding) * v := by
    have h := ffMono_conj_signChange fr σ J K
    rw [← heq] at h
    calc (v : OGroup Q) * fr.signChange K
        = ((v : OGroup Q) * fr.signChange K * (v : OGroup Q)⁻¹) * v := by group
      _ = fr.signChange (K.map σ.toEmbedding) * v := by rw [h]
  have hmap : K.map σ.toEmbedding = K ∨ K.map σ.toEmbedding = Kᶜ := by
    rcases hcomm v v.2 (fr.signChange K) hKU with hcase | hcase
    · left
      have h : fr.signChange (K.map σ.toEmbedding) * v = fr.signChange K * v := by
        rw [← hconj, hcase]
      exact fr.signChange_injective (mul_right_cancel h)
    · right
      have hπK : piOrth Q * fr.signChange K = fr.signChange Kᶜ := by
        rw [fr.piOrth_eq_signChange_univ, fr.signChange_mul]
        congr 1
        ext i
        simp [Finset.mem_symmDiff]
      have h : fr.signChange (K.map σ.toEmbedding) * v = fr.signChange Kᶜ * v := by
        rw [← hconj, hcase, ← mul_assoc, hπK]
      exact fr.signChange_injective (mul_right_cancel h)
  rw [ffF, Finset.mem_filter]
  exact ⟨Finset.mem_univ K, hKeven, hmap⟩

end CFSG.OddStandard.SmallF3.Omega
