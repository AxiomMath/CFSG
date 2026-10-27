module

public import CFSG.GroupTheory.SubgroupOfQuotientMap
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.SignalizerFunctorTheorem.McBride
open scoped commutatorElement

variable {G Γ : Type*} [Group G] [Group Γ] {X D : Subgroup G} {ψ : ↥X →* Γ}

private lemma subgroupOf_map_conj_eq (x : ↥X) (K : Subgroup G) :
    (K.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf X =
      (K.subgroupOf X).map (MulAut.conj x).toMonoidHom := by
  ext a
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, MulAut.conj_apply,
    MulEquiv.coe_toMonoidHom]
  constructor
  · rintro ⟨k, hkK, hk⟩
    refine ⟨⟨(x : G)⁻¹ * (a : G) * (x : G), ?_⟩, ?_, ?_⟩
    · exact X.mul_mem (X.mul_mem (X.inv_mem x.2) a.2) x.2
    · show (x : G)⁻¹ * (a : G) * (x : G) ∈ K
      rw [show (x : G)⁻¹ * (a : G) * (x : G) = k by rw [← hk]; group]
      exact hkK
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  · rintro ⟨b, hbK, hb⟩
    exact ⟨(b : G), hbK, by
      have h := congrArg (Subtype.val) hb
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using h⟩

private lemma map_conj_mul (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private lemma map_subgroupOf_sSup (T : Set (Subgroup G)) (hT : ∀ K ∈ T, K ≤ X) :
    ((sSup T).subgroupOf X).map ψ =
      sSup ((fun K : Subgroup G => (K.subgroupOf X).map ψ) '' T) := by
  have hsub : (sSup T).subgroupOf X =
      sSup ((fun K : Subgroup G => K.subgroupOf X) '' T) := by
    apply Subgroup.map_injective X.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le (sSup_le hT),
      GaloisConnection.l_sSup_eq_sSup_image (Subgroup.gc_map_comap X.subtype)]
    congr 1
    apply Set.Subset.antisymm
    · intro H hH
      exact ⟨H.subgroupOf X, ⟨H, hH, rfl⟩, Subgroup.map_subgroupOf_eq_of_le (hT H hH)⟩
    · rintro H ⟨A, hA, rfl⟩
      obtain ⟨K, hK, rfl⟩ := hA
      rwa [Subgroup.map_subgroupOf_eq_of_le (hT K hK)]
  rw [hsub, GaloisConnection.l_sSup_eq_sSup_image (Subgroup.gc_map_comap ψ)]
  congr 1
  apply Set.Subset.antisymm
  · rintro H ⟨A, ⟨K, hK, rfl⟩, rfl⟩
    exact ⟨K, hK, rfl⟩
  · rintro H ⟨K, hK, rfl⟩
    exact ⟨K.subgroupOf X, ⟨K, hK, rfl⟩, rfl⟩

theorem map_subgroupOf_map_conj (x : ↥X) (K : Subgroup G) :
    ((K.map (MulAut.conj (x : G)).toMonoidHom).subgroupOf X).map ψ =
      ((K.subgroupOf X).map ψ).map (MulAut.conj (ψ x)).toMonoidHom := by
  rw [subgroupOf_map_conj_eq x K]
  simp only [Subgroup.map_map]
  congr 1
  ext a
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul,
    map_inv]

theorem forall_map_conj_mem_of_le_sup [Finite G] {𝒦 : Set (Subgroup G)} {P H : Subgroup G}
    (hP : ∀ p ∈ P, ∀ K ∈ 𝒦, K.map (MulAut.conj p).toMonoidHom ∈ 𝒦)
    (hH : ∀ h ∈ H, ∀ K ∈ 𝒦, K.map (MulAut.conj h).toMonoidHom ∈ 𝒦) :
    ∀ x ∈ P ⊔ H, ∀ K ∈ 𝒦, K.map (MulAut.conj x).toMonoidHom ∈ 𝒦 := by
  let M : Set G := {g | ∀ K ∈ 𝒦, K.map (MulAut.conj g).toMonoidHom ∈ 𝒦}
  have hM1 : (1 : G) ∈ M := by
    change ∀ K ∈ 𝒦, K.map (MulAut.conj (1 : G)).toMonoidHom ∈ 𝒦
    intro K hK
    simpa [MulAut.one_def] using hK
  have hMmul : ∀ a ∈ M, ∀ b ∈ M, a * b ∈ M := by
    intro a ha b hb
    change ∀ K ∈ 𝒦, K.map (MulAut.conj a).toMonoidHom ∈ 𝒦 at ha
    change ∀ K ∈ 𝒦, K.map (MulAut.conj b).toMonoidHom ∈ 𝒦 at hb
    change ∀ K ∈ 𝒦, K.map (MulAut.conj (a * b)).toMonoidHom ∈ 𝒦
    intro K hK
    have h2 : (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom ∈ 𝒦 :=
      ha _ (hb K hK)
    rwa [map_conj_mul] at h2
  have hMinv : ∀ g ∈ M, g⁻¹ ∈ M := by
    intro g hg
    change ∀ K ∈ 𝒦, K.map (MulAut.conj g⁻¹).toMonoidHom ∈ 𝒦
    have hpow : ∀ n : ℕ, g ^ n ∈ M := by
      intro n
      induction n with
      | zero => simpa using hM1
      | succ n ih =>
        rw [pow_succ]
        exact hMmul _ ih _ hg
    have heq : g ^ (orderOf g - 1) = g⁻¹ := by
      have h1 : g ^ (orderOf g - 1) * g = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_of_lt (orderOf_pos g)), pow_orderOf_eq_one]
      exact eq_inv_of_mul_eq_one_left h1
    rw [← heq]
    exact hpow _
  let M' : Subgroup G :=
    { carrier := M
      mul_mem' := fun {a b} ha hb => hMmul a ha b hb
      one_mem' := hM1
      inv_mem' := fun {g} hg => hMinv g hg }
  have hPM : P ≤ M' := fun p hp => by
    change ∀ K ∈ 𝒦, K.map (MulAut.conj p).toMonoidHom ∈ 𝒦
    exact hP p hp
  have hHM : H ≤ M' := fun h hh => by
    change ∀ K ∈ 𝒦, K.map (MulAut.conj h).toMonoidHom ∈ 𝒦
    exact hH h hh
  intro x hx K hK
  have hxM : x ∈ M := sup_le hPM hHM hx
  exact hxM K hK

theorem map_conj_mem_image_of_forall (hψ : Function.Surjective ψ) {𝒦 : Set (Subgroup G)}
    (h : ∀ x ∈ X, ∀ K ∈ 𝒦, K.map (MulAut.conj x).toMonoidHom ∈ 𝒦) (g : Γ) {J : Subgroup Γ}
    (hJ : J ∈ (fun K : Subgroup G => (K.subgroupOf X).map ψ) '' 𝒦) :
    J.map (MulAut.conj g).toMonoidHom ∈ (fun K : Subgroup G => (K.subgroupOf X).map ψ) '' 𝒦 := by
  obtain ⟨K, hK, rfl⟩ := hJ
  obtain ⟨x, rfl⟩ := hψ g
  exact ⟨K.map (MulAut.conj (x : G)).toMonoidHom, h x x.2 K hK, map_subgroupOf_map_conj x K⟩

theorem isDirectProduct_image (hker : ψ.ker = D.subgroupOf X) {𝒦 : Set (Subgroup G)}
    (hle : ∀ K ∈ 𝒦, D ≤ K ∧ K ≤ X)
    (hcomm : ∀ K₁ ∈ 𝒦, ∀ K₂ ∈ 𝒦, K₁ ≠ K₂ → ⁅K₁, K₂⁆ ≤ D)
    (hind : ∀ K ∈ 𝒦, K ⊓ sSup (𝒦 \ {K}) ≤ D) :
    IsDirectProduct ((fun K : Subgroup G => (K.subgroupOf X).map ψ) '' 𝒦)
      (((sSup 𝒦).subgroupOf X).map ψ) := by
  let f : Subgroup G → Subgroup Γ := fun K => (K.subgroupOf X).map ψ
  change IsDirectProduct (f '' 𝒦) (((sSup 𝒦).subgroupOf X).map ψ)
  refine ⟨?_, ?_, ?_⟩
  · rintro J hJ L hL hJL u hu v hv
    obtain ⟨K₁, hK₁, rfl⟩ := hJ
    obtain ⟨K₂, hK₂, rfl⟩ := hL
    have hne : K₁ ≠ K₂ := fun h => hJL (by rw [h])
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hv
    have hcommG : ⁅(a : G), (b : G)⁆ ∈ D :=
      hcomm K₁ hK₁ K₂ hK₂ hne (Subgroup.commutator_mem_commutator
        (Subgroup.mem_subgroupOf.mp ha) (Subgroup.mem_subgroupOf.mp hb))
    have hXcomm : ⁅(a : G), (b : G)⁆ ∈ X := (hle K₁ hK₁).2 ((hle K₁ hK₁).1 hcommG)
    have hker_mem : (⟨⁅(a : G), (b : G)⁆, hXcomm⟩ : ↥X) ∈ ψ.ker := by
      rw [hker]
      exact hcommG
    have h1 : ψ ⁅a, b⁆ = 1 := by
      have h := MonoidHom.mem_ker.mp hker_mem
      rwa [show (⟨⁅(a : G), (b : G)⁆, hXcomm⟩ : ↥X) = ⁅a, b⁆ from
        Subtype.ext (map_commutatorElement (f := X.subtype) (g₁ := a) (g₂ := b)).symm] at h
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_commute.mp h1
  · intro J hJ
    obtain ⟨K, hK, rfl⟩ := hJ
    rw [disjoint_iff, ← le_bot_iff]
    have hsub : (f '' 𝒦 \ {f K}) ⊆ f '' (𝒦 \ {K}) := by
      rintro J ⟨hJ, hJne⟩
      obtain ⟨K', hK', rfl⟩ := hJ
      refine ⟨K', ⟨hK', ?_⟩, rfl⟩
      simp only [Set.mem_singleton_iff] at hJne ⊢
      exact fun h => hJne (by rw [h])
    have hsupK : ((sSup (𝒦 \ {K})).subgroupOf X).map ψ = sSup (f '' (𝒦 \ {K})) :=
      map_subgroupOf_sSup (𝒦 \ {K}) (fun L hL => (hle L hL.1).2)
    have hbig : f K ⊓ sSup (f '' (𝒦 \ {K})) = ⊥ := by
      have hK' : f K = (K.subgroupOf X).map ψ := rfl
      rw [hsupK.symm, hK', inf_comm,
        ← map_subgroupOf_inf hker (sSup (𝒦 \ {K})) (hle K hK).1]
      exact map_subgroupOf_eq_bot hker (by simpa [inf_comm] using hind K hK)
    calc f K ⊓ sSup (f '' 𝒦 \ {f K})
        ≤ f K ⊓ sSup (f '' (𝒦 \ {K})) := inf_le_inf_left _ (sSup_le_sSup hsub)
      _ = ⊥ := hbig
  · exact (map_subgroupOf_sSup 𝒦 (fun K hK => (hle K hK).2)).symm

end CFSG.GroupTheory
