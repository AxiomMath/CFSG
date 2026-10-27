module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockInvThreeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertA5
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertL32
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverCertU33

public section

namespace CFSG.AGLEmbedding.ParabHub.ParabThreeInv

open Equiv CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge.Over CFSG.QuasithinUnique.L246C127
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat CFSG.QuasithinUnique.Unc25K1.Six

@[expose] def InvOver (S : Type) [Group S] : Prop :=
  ∀ T J : Subgroup S, IsSylowTwoOf T ⊤ → Subgroup.normalizer (T : Set S) ≤ J →
    J ≠ Subgroup.normalizer (T : Set S) → InvThree J

theorem InvOver.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S')
    (h : InvOver S) : InvOver S' := by
  intro T J hT hNJ hne
  have hT' : IsSylowTwoOf (T.map e.symm.toMonoidHom) ⊤ := by
    have := (Setup.Layer.isSylowTwoOf_map_mulEquiv e.symm (X := T) (Y := ⊤)).2 hT
    simpa [Subgroup.map_top_of_surjective e.symm.toMonoidHom e.symm.surjective] using this
  have hN : (Subgroup.normalizer (T : Set S')).map e.symm.toMonoidHom =
      Subgroup.normalizer ((T.map e.symm.toMonoidHom : Subgroup S) : Set S) :=
    Subgroup.map_equiv_normalizer_eq T e.symm
  have hNJ' : Subgroup.normalizer ((T.map e.symm.toMonoidHom : Subgroup S) : Set S) ≤
      J.map e.symm.toMonoidHom := hN ▸ Subgroup.map_mono hNJ
  have hne' : J.map e.symm.toMonoidHom ≠
      Subgroup.normalizer ((T.map e.symm.toMonoidHom : Subgroup S) : Set S) := fun h' =>
    hne (Subgroup.map_injective e.symm.injective (h'.trans hN.symm))
  have := (h _ _ hT' hNJ' hne').map_injective e.toMonoidHom e.injective
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ by
    ext x; simp, Subgroup.map_id] at this

theorem InvOver.of_sylow {S : Type} [Group S] [Finite S] (T₀ : Subgroup S)
    (hT₀ : IsSylowTwoOf T₀ ⊤) (h : ∀ J : Subgroup S, Subgroup.normalizer (T₀ : Set S) ≤ J →
      J ≠ Subgroup.normalizer (T₀ : Set S) → InvThree J) : InvOver S := by
  intro T J hT hTJ hne
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf' hT₀ hT
  set e : S ≃* S := MulAut.conj g with he
  have hTe : T.map e.symm.toMonoidHom = T₀ := by
    rw [← hg, map_map_symm']
  have hN : (Subgroup.normalizer (T : Set S)).map e.symm.toMonoidHom =
      Subgroup.normalizer (T₀ : Set S) := by
    rw [Subgroup.map_equiv_normalizer_eq T e.symm, hTe]
  have hT₀J : Subgroup.normalizer (T₀ : Set S) ≤ J.map e.symm.toMonoidHom := by
    rw [← hN]
    exact Subgroup.map_mono hTJ
  have hne' : J.map e.symm.toMonoidHom ≠ Subgroup.normalizer (T₀ : Set S) := fun h' =>
    hne (Subgroup.map_injective e.symm.injective (h'.trans hN.symm))
  have := (h _ hT₀J hne').map_injective e.toMonoidHom e.injective
  rwa [Subgroup.map_map, show e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id _ by
    ext x; simp, Subgroup.map_id] at this

theorem invThree_of_words {n : ℕ} {A : Subgroup (Perm (Fin n))} (L : List (Perm (Fin n)))
    (hLA : Subgroup.closure {g | g ∈ L} ≤ A) (wa wg : List ℕ)
    (h3 : evalW L wa * evalW L wa * evalW L wa = 1) (h1 : evalW L wa ≠ 1)
    (hinv : evalW L wg * evalW L wa * (evalW L wg)⁻¹ = (evalW L wa)⁻¹) :
    InvThree ((Subgroup.closure {g | g ∈ L}).subgroupOf A) := by
  have ha := evalW_mem_closure L wa
  have hg := evalW_mem_closure L wg
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ⟨⟨evalW L wa, hLA ha⟩, Subgroup.mem_subgroupOf.mpr ha, ⟨evalW L wg, hLA hg⟩,
    Subgroup.mem_subgroupOf.mpr hg, ?_, Subtype.ext (by simpa using hinv)⟩
  refine orderOf_eq_prime (Subtype.ext ?_) (fun h => h1 (congrArg Subtype.val h))
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [pow_succ, pow_two, h3]

theorem invThree_of_latCert {n : ℕ} {A : Subgroup (Perm (Fin n))} (c : LatCert (Perm (Fin n)))
    (hM : Subgroup.closure {g | g ∈ c.mGens} = A)
    (hTA : Subgroup.closure {g | g ∈ c.tGens} ≤ A) (hc : c.check RN.enc = true)
    (hwit : ∀ L ∈ c.lat, Subgroup.closure {g | g ∈ L} ≤ A →
      InvThree ((Subgroup.closure {g | g ∈ L}).subgroupOf A) ∨
      (Subgroup.closure {g | g ∈ L}).subgroupOf A ≤ Subgroup.normalizer
        (((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A : Subgroup ↥A) : Set ↥A))
    (Y : Subgroup ↥A) (hNY : Subgroup.normalizer
      (((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A : Subgroup ↥A) : Set ↥A) ≤ Y)
    (hne : Y ≠ Subgroup.normalizer
      (((Subgroup.closure {g | g ∈ c.tGens}).subgroupOf A : Subgroup ↥A) : Set ↥A)) :
    InvThree Y := by
  subst hM
  have hTY := Subgroup.le_normalizer.trans hNY
  obtain ⟨L, hL, hLM, hYL, -⟩ := c.overgroup_cases (rawIsEnc n) hc Y hTY
  rcases List.mem_cons.mp hL with rfl | hL'
  · exact absurd (le_antisymm (hYL ▸ Subgroup.le_normalizer) hNY) hne
  · rcases hwit L hL' hLM with h | h
    · rw [hYL]
      exact h
    · exact absurd (le_antisymm (hYL ▸ h) hNY) hne

theorem mem_normalizer_closure_list_of_conj {n : ℕ} {S : List (Perm (Fin n))}
    {x : Perm (Fin n)} (h : ∀ t ∈ S, x * t * x⁻¹ ∈ Subgroup.closure {g | g ∈ S}) :
    x ∈ Subgroup.normalizer
      ((Subgroup.closure {g | g ∈ S} : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) := by
  apply Subgroup.mem_normalizer_fintype
  intro m hm
  induction hm using Subgroup.closure_induction with
  | mem t ht => exact h t ht
  | one => simp
  | mul a b _ _ ha hb =>
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
    have e : x * a⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ ha

theorem le_N_certA5 :
    (Subgroup.closure {g | g ∈ CertA5.L1}).subgroupOf (alternatingGroup (Fin 5)) ≤
      Subgroup.normalizer (((Subgroup.closure {g | g ∈ CertA5.cert.tGens}).subgroupOf
        (alternatingGroup (Fin 5)) : Subgroup ↥(alternatingGroup (Fin 5))) :
          Set ↥(alternatingGroup (Fin 5))) := by
  rw [← Subgroup.subgroupOf_normalizer_eq (show Subgroup.closure {g | g ∈ CertA5.cert.tGens} ≤
    alternatingGroup (Fin 5) from CertA5.D_le)]
  intro x hx
  refine Subgroup.mem_subgroupOf.mpr ?_
  have hx' := Subgroup.mem_subgroupOf.mp hx
  refine (Subgroup.closure_le _).mpr ?_ hx'
  intro y hy
  have hy' : y ∈ CertA5.L1 := hy
  simp only [CertA5.L1, List.mem_cons, List.not_mem_nil, or_false] at hy'
  rcases hy' with rfl | rfl | rfl
  · exact Subgroup.le_normalizer
      (Subgroup.subset_closure (show _ ∈ CertA5.tGens by decide +kernel))
  · exact Subgroup.le_normalizer
      (Subgroup.subset_closure (show _ ∈ CertA5.tGens by decide +kernel))
  · apply mem_normalizer_closure_list_of_conj
    intro t ht
    have ht' : t ∈ CertA5.tGens := ht
    simp only [CertA5.tGens, List.mem_cons, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl
    · rw [show permOf 5 [[2, 3, 4]] * permOf 5 [[1, 2], [3, 4]] * (permOf 5 [[2, 3, 4]])⁻¹ =
          evalW CertA5.tGens [1] by decide +kernel]
      exact evalW_mem_closure _ _
    · rw [show permOf 5 [[2, 3, 4]] * permOf 5 [[1, 3], [2, 4]] * (permOf 5 [[2, 3, 4]])⁻¹ =
          evalW CertA5.tGens [0, 1] by decide +kernel]
      exact evalW_mem_closure _ _

theorem invOver_alt_five :
    InvOver ↥(alternatingGroup (Fin 5)) :=
  InvOver.of_sylow _ CertA5.isSylow_D fun J hJ hne =>
    invThree_of_latCert CertA5.cert CertA5.closure_mGens CertA5.D_le CertA5.cert_check
      (fun L hL hLA => by
        have hL' : L ∈ [CertA5.L1, CertA5.L2] := hL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hL'
        rcases hL' with rfl | rfl
        · exact Or.inr le_N_certA5
        · exact Or.inl (invThree_of_words _ hLA [0, 2] [0] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
      ) J hJ hne

theorem invOver_alt_six : InvOver ↥(alternatingGroup (Fin 6)) :=
  InvOver.of_sylow _ Even6.isSylow_D fun J hJ hne =>
    invThree_of_latCert Even6.cert Even6.closure_mGens Even6.D_le Even6.cert_check
      (fun L hL hLA => by
        have hL' : L ∈ [Even6.L1, Even6.L2, Even6.L3] := hL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hL'
        rcases hL' with rfl | rfl | rfl
        · exact Or.inl (invThree_of_words _ hLA [1, 2] [1] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [0, 2] [0] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [2] [0] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
      ) J hJ hne

theorem invOver_alt_eight :
    InvOver ↥(alternatingGroup (Fin 8)) :=
  InvOver.of_sylow _ Even8.isSylow_D fun J hJ hne =>
    invThree_of_latCert Even8.cert Even8.closure_mGens Even8.D_le Even8.cert_check
      (fun L hL hLA => by
        have hL' : L ∈ [Even8.L1, Even8.L2, Even8.L3, Even8.L4, Even8.L5, Even8.L6,
          Even8.L7] := hL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hL'
        rcases hL' with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact Or.inl (invThree_of_words _ hLA [1, 3] [1] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [0, 2, 3] [0, 1, 2] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [0, 2, 3] [0, 1, 2] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [3] [2, 0, 1] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [3] [0, 1, 3, 0, 3, 2] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [3] [2, 1, 3, 0, 3, 1] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [0, 3, 0, 3] [0, 1, 2] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
      ) J hJ hne

theorem invOver_z8 :
    InvOver ↥(Vol2Native.A312L.Seven.Z 8) :=
  InvOver.of_sylow _ CertL32.isSylow_D fun J hJ hne =>
    invThree_of_latCert CertL32.cert CertL32.closure_mGens CertL32.D_le CertL32.cert_check
      (fun L hL hLA => by
        have hL' : L ∈ [CertL32.L1, CertL32.L2, CertL32.L3] := hL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hL'
        rcases hL' with rfl | rfl | rfl
        · exact Or.inl (invThree_of_words _ hLA [0, 2] [0] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [1, 2] [1] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [2] [1, 0, 2, 0, 1, 0, 2, 0]
            (by decide +kernel) (by decide +kernel) (by decide +kernel))
      ) J hJ hne

theorem invOver_u33 :
    InvOver ↥CFSG.GH74.KGroups.U33.QP.originalSubgroup :=
  InvOver.of_sylow _ CertU33.isSylow_D fun J hJ hne =>
    invThree_of_latCert CertU33.cert CertU33.closure_mGens CertU33.D_le CertU33.cert_check
      (fun L hL hLA => by
        have hL' : L ∈ [CertU33.L1, CertU33.L2, CertU33.L3] := hL
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hL'
        rcases hL' with rfl | rfl | rfl
        · exact Or.inl (invThree_of_words _ hLA [0, 2, 1] [2] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [0, 2] [0] (by decide +kernel)
            (by decide +kernel) (by decide +kernel))
        · exact Or.inl (invThree_of_words _ hLA [0, 2, 1] [1, 2, 1, 2, 0, 1, 2]
            (by decide +kernel) (by decide +kernel) (by decide +kernel))
      ) J hJ hne

end CFSG.AGLEmbedding.ParabHub.ParabThreeInv
