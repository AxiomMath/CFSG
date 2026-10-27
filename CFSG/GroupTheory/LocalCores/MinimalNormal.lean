module

public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.LocalCores

open Subgroup
open scoped commutatorElement

section Independence

variable {A : Type*} [Group A]

theorem disjoint_sup_of_normal {T X N : Subgroup A} [N.Normal] (hTX : Disjoint T X)
    (hN : Disjoint N (T ⊔ X)) : Disjoint T (N ⊔ X) := by
  rw [Subgroup.disjoint_def] at hTX hN ⊢
  intro t ht htNX
  rw [← SetLike.mem_coe, Subgroup.normal_mul, Set.mem_mul] at htNX
  obtain ⟨n, hn, x, hx, rfl⟩ := htNX
  have hn1 : n = 1 := hN hn (by
    have h : n = n * x * x⁻¹ := by group
    rw [h]
    exact mul_mem (mem_sup_left ht) (inv_mem (mem_sup_right hx)))
  subst hn1
  rw [one_mul] at ht ⊢
  exact hTX ht hx

theorem sSupIndep_insert_of_normal {𝒯 : Set (Subgroup A)} (h𝒯 : sSupIndep 𝒯)
    {N : Subgroup A} [N.Normal] (hN : Disjoint N (sSup 𝒯)) : sSupIndep (insert N 𝒯) := by
  intro a ha
  rcases ha with rfl | haT
  · refine hN.mono_right (sSup_le_sSup ?_)
    rintro x ⟨hx1, hx2⟩
    rcases hx1 with rfl | hx1
    · exact absurd rfl hx2
    · exact hx1
  · have hle : sSup (insert N 𝒯 \ {a}) ≤ N ⊔ sSup (𝒯 \ {a}) := by
      refine sSup_le fun x hx => ?_
      rcases hx with ⟨hx1, hx2⟩
      rcases hx1 with rfl | hx1
      · exact le_sup_left
      · exact le_sup_of_le_right (le_sSup ⟨hx1, hx2⟩)
    refine (disjoint_sup_of_normal (h𝒯 haT) (hN.mono_right ?_)).mono_right hle
    exact sup_le (le_sSup haT) (sSup_le_sSup Set.sdiff_subset)

theorem inf_eq_bot_of_minimal_normal {N₁ N₂ : Subgroup A}
    (h₁ : N₁.Normal ∧ N₁ ≠ ⊥ ∧ ∀ M : Subgroup A, M.Normal → M ≤ N₁ → M = ⊥ ∨ M = N₁)
    (h₂ : N₂.Normal ∧ N₂ ≠ ⊥ ∧ ∀ M : Subgroup A, M.Normal → M ≤ N₂ → M = ⊥ ∨ M = N₂)
    (hne : N₁ ≠ N₂) : N₁ ⊓ N₂ = ⊥ := by
  have : N₁.Normal := h₁.1
  have : N₂.Normal := h₂.1
  rcases h₁.2.2 (N₁ ⊓ N₂) inferInstance inf_le_left with h | h
  · exact h
  · exfalso
    have hle : N₁ ≤ N₂ := h ▸ inf_le_right
    rcases h₂.2.2 N₁ h₁.1 hle with h' | h'
    · exact h₁.2.1 h'
    · exact hne h'

theorem commute_of_normal_of_inf_eq_bot {N₁ N₂ : Subgroup A} [N₁.Normal] [N₂.Normal]
    (h : N₁ ⊓ N₂ = ⊥) {x y : A} (hx : x ∈ N₁) (hy : y ∈ N₂) : Commute x y := by
  have hmem : ⁅x, y⁆ ∈ ⁅N₁, N₂⁆ := Subgroup.commutator_mem_commutator hx hy
  have hc : ⁅N₁, N₂⁆ = ⊥ := le_bot_iff.mp ((Subgroup.commutator_le_inf N₁ N₂).trans h.le)
  rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
  exact hmem

theorem exists_sSupIndep_subset_sSup_eq [Finite A] (𝒮 : Set (Subgroup A))
    (h𝒮 : ∀ N ∈ 𝒮, N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup A, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    ∃ 𝒯 ⊆ 𝒮, sSupIndep 𝒯 ∧ sSup 𝒯 = sSup 𝒮 := by
  let 𝒞 : Set (Set (Subgroup A)) := {𝒯 | 𝒯 ⊆ 𝒮 ∧ sSupIndep 𝒯}
  obtain ⟨𝒯, ⟨h𝒯𝒮, h𝒯ind⟩, hmax⟩ :=
    (Set.toFinite 𝒞).exists_maximal ⟨∅, Set.empty_subset _, sSupIndep_empty⟩
  refine ⟨𝒯, h𝒯𝒮, h𝒯ind, le_antisymm (sSup_le_sSup h𝒯𝒮) (sSup_le fun N hN => ?_)⟩
  by_contra hle
  have : N.Normal := (h𝒮 N hN).1
  have : (sSup 𝒯).Normal := Subgroup.sSup_normal _ fun T hT => (h𝒮 T (h𝒯𝒮 hT)).1
  rcases (h𝒮 N hN).2.2 (N ⊓ sSup 𝒯) inferInstance inf_le_left with h | h
  · have hins : insert N 𝒯 ∈ 𝒞 :=
      ⟨Set.insert_subset hN h𝒯𝒮, sSupIndep_insert_of_normal h𝒯ind (disjoint_iff.mpr h)⟩
    exact hle (le_sSup (hmax hins (Set.subset_insert N 𝒯) (Set.mem_insert N 𝒯)))
  · exact hle (h ▸ inf_le_right)

theorem exists_mulEquiv_pi_iSup {ι : Type*} [Finite ι] (H : ι → Subgroup A)
    (hcomm : Pairwise fun i j => ∀ x y : A, x ∈ H i → y ∈ H j → Commute x y)
    (hind : iSupIndep H) :
    ∃ e : ((i : ι) → H i) ≃* ↥(⨆ i, H i),
      ∀ (i : ι) (x : (j : ι) → H j), (∀ j, j ≠ i → x j = 1) → (e x : A) = x i := by
  classical
  have := Fintype.ofFinite ι
  let ϕ := Subgroup.noncommPiCoprod hcomm
  have hrange : ϕ.range = ⨆ i, H i := Subgroup.noncommPiCoprod_range
  have hmem : ∀ x, ϕ x ∈ ⨆ i, H i := fun x => hrange ▸ ⟨x, rfl⟩
  let ϕ' := ϕ.codRestrict _ hmem
  have hinj : Function.Injective ϕ' := fun x y h =>
    Subgroup.injective_noncommPiCoprod_of_iSupIndep hind (congrArg Subtype.val h)
  have hsurj : Function.Surjective ϕ' := by
    rintro ⟨y, hy⟩
    rw [← hrange] at hy
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  refine ⟨MulEquiv.ofBijective ϕ' ⟨hinj, hsurj⟩, fun i x hx => ?_⟩
  have hx' : x = Pi.mulSingle i (x i) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [hx j hj, Pi.mulSingle_eq_of_ne hj]
  change ϕ x = x i
  rw [hx']
  simp only [ϕ, Subgroup.noncommPiCoprod_mulSingle, Pi.mulSingle_eq_same]

theorem iSupIndep_map_of_injective {ι : Type*} {B : Type*} [Group B] {f : A →* B}
    (hf : Function.Injective f) {H : ι → Subgroup A} (hH : iSupIndep H) :
    iSupIndep fun i => (H i).map f := by
  intro i
  rw [disjoint_iff]
  have h1 : (⨆ j, ⨆ (_ : j ≠ i), (H j).map f) = (⨆ j, ⨆ (_ : j ≠ i), H j).map f := by
    rw [Subgroup.map_iSup]
    congr 1
    funext j
    rw [Subgroup.map_iSup]
  change (H i).map f ⊓ (⨆ j, ⨆ (_ : j ≠ i), (H j).map f) = ⊥
  rw [h1, ← Subgroup.map_inf_eq _ _ f hf, disjoint_iff.mp (hH i), Subgroup.map_bot]

end Independence

section Conjugate

variable {G : Type*} [Group G]

theorem conjugate_conjugate (H : Subgroup G) (a b : G) :
    conjugate (conjugate H a) b = conjugate H (a * b) := by
  unfold conjugate
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

end Conjugate

variable {G : Type*} [Group G]

theorem minimal_normal_product [Finite G] (𝒮 : Set (Subgroup G))
    (h𝒮 : ∀ N ∈ 𝒮, N.Normal ∧ N ≠ ⊥ ∧ ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    ∃ 𝒯 ⊆ 𝒮, ∃ e : ((N : 𝒯) → (N : Subgroup G)) ≃* ↥(sSup 𝒮),
      ∀ (N : 𝒯) (x : (M : 𝒯) → (M : Subgroup G)), (∀ M, M ≠ N → x M = 1) →
        (e x : G) = x N := by
  obtain ⟨𝒯, h𝒯𝒮, hind, hsup⟩ := exists_sSupIndep_subset_sSup_eq 𝒮 h𝒮
  have hcomm : Pairwise fun M M' : 𝒯 =>
      ∀ x y : G, x ∈ (M : Subgroup G) → y ∈ (M' : Subgroup G) → Commute x y := by
    intro M M' hMM' x y hx hy
    have h1 := h𝒮 M (h𝒯𝒮 M.2)
    have h2 := h𝒮 M' (h𝒯𝒮 M'.2)
    have : (M : Subgroup G).Normal := h1.1
    have : (M' : Subgroup G).Normal := h2.1
    exact commute_of_normal_of_inf_eq_bot
      (inf_eq_bot_of_minimal_normal h1 h2 fun h => hMM' (Subtype.ext h)) hx hy
  obtain ⟨e, he⟩ := exists_mulEquiv_pi_iSup (fun M : 𝒯 => (M : Subgroup G)) hcomm
    ((sSupIndep_iff 𝒯).mp hind)
  have heq : (⨆ M : 𝒯, (M : Subgroup G)) = sSup 𝒮 := by rw [← sSup_eq_iSup', hsup]
  exact ⟨𝒯, h𝒯𝒮, e.trans (MulEquiv.subgroupCongr heq), fun N x hx => he N x hx⟩

theorem minimal_normal_simple_factors [Finite G] {N : Subgroup G} (hN : N.Normal) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N) :
    ∃ (r : ℕ) (S : Fin r → Subgroup G), 1 ≤ r ∧ (∀ i, S i ≤ N) ∧ (∀ i, IsSimpleGroup (S i)) ∧
      (∀ i j, ∃ g : G, S j = conjugate (S i) g) ∧ (∀ i, ((S i).subgroupOf N).Normal) ∧
      ∃ e : ((i : Fin r) → S i) ≃* N,
        ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : G) = x i := by
  classical
  have : N.Normal := hN
  have : Nontrivial N := (Subgroup.nontrivial_iff_ne_bot N).mpr hN1
  obtain ⟨S', ⟨hS'n, hS'ne⟩, hS'min⟩ :=
    (Set.toFinite {M : Subgroup N | M.Normal ∧ M ≠ ⊥}).exists_minimal
      ⟨⊤, inferInstance, top_ne_bot⟩
  have hS'minimal : ∀ M : Subgroup N, M.Normal → M ≤ S' → M = ⊥ ∨ M = S' := fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hS'min ⟨hM, hM1⟩ hle)
  let φ : G →* MulAut N := MulAut.conjNormal
  have hφmul : ∀ g h : G,
      (φ (g * h)).toMonoidHom = (φ g).toMonoidHom.comp (φ h).toMonoidHom := by
    intro g h
    ext x
    simp [map_mul, MulAut.mul_apply]
  let 𝒮 : Set (Subgroup N) := Set.range fun g : G => S'.map (φ g).toMonoidHom
  have h𝒮 : ∀ T ∈ 𝒮, T.Normal ∧ T ≠ ⊥ ∧
      ∀ M : Subgroup N, M.Normal → M ≤ T → M = ⊥ ∨ M = T := by
    rintro _ ⟨g, rfl⟩
    refine ⟨hS'n.map _ (φ g).surjective,
      fun h => hS'ne ((Subgroup.map_eq_bot_iff_of_injective _ (φ g).injective).mp h),
      fun M hM hle => ?_⟩
    have hle' : M.map (φ g).symm.toMonoidHom ≤ S' := by
      have := Subgroup.map_mono (f := (φ g).symm.toMonoidHom) hle
      rwa [map_map_symm] at this
    have hMeq : (M.map (φ g).symm.toMonoidHom).map (φ g).toMonoidHom = M := by
      simpa using map_map_symm (φ g).symm M
    rcases hS'minimal _ (hM.map _ (φ g).symm.surjective) hle' with h | h
    · left
      rw [← hMeq, h, Subgroup.map_bot]
    · right
      rw [← hMeq, h]
  have hS'mem : S' ∈ 𝒮 := ⟨1, by
    have : (φ 1).toMonoidHom = MonoidHom.id N := by
      ext x
      simp
    change S'.map (φ 1).toMonoidHom = S'
    rw [this, Subgroup.map_id]⟩
  have hinv : ∀ g : G, (sSup 𝒮).map (φ g).toMonoidHom ≤ sSup 𝒮 := by
    intro g
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le ?_
    rintro _ ⟨h, rfl⟩
    rw [← Subgroup.map_le_iff_le_comap, Subgroup.map_map, ← hφmul]
    exact le_sSup ⟨g * h, rfl⟩
  have hsup𝒮 : sSup 𝒮 = ⊤ := by
    have hYn : ((sSup 𝒮).map N.subtype).Normal := by
      refine ⟨fun y hy g => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      refine ⟨φ g x, hinv g (Subgroup.mem_map_of_mem _ hx), ?_⟩
      simp [φ, MulAut.conjNormal_apply]
    rcases hmin _ hYn (Subgroup.map_subtype_le _) with h | h
    · exfalso
      have hbot : sSup 𝒮 = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h
      exact hS'ne (le_bot_iff.mp (hbot ▸ le_sSup hS'mem))
    · apply Subgroup.map_injective N.subtype_injective
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  obtain ⟨𝒯, h𝒯𝒮, hind, hsup⟩ := exists_sSupIndep_subset_sSup_eq 𝒮 h𝒮
  have hcomm𝒯 : ∀ T₁ ∈ 𝒯, ∀ T₂ ∈ 𝒯, T₁ ≠ T₂ → ∀ x y : N, x ∈ T₁ → y ∈ T₂ → Commute x y := by
    intro T₁ h₁ T₂ h₂ hne x y hx hy
    have := (h𝒮 T₁ (h𝒯𝒮 h₁)).1
    have := (h𝒮 T₂ (h𝒯𝒮 h₂)).1
    exact commute_of_normal_of_inf_eq_bot
      (inf_eq_bot_of_minimal_normal (h𝒮 T₁ (h𝒯𝒮 h₁)) (h𝒮 T₂ (h𝒯𝒮 h₂)) hne) hx hy
  have hsimple : ∀ T ∈ 𝒯, IsSimpleGroup T := by
    intro T hT
    obtain ⟨-, hTne, hTmin⟩ := h𝒮 T (h𝒯𝒮 hT)
    have : Nontrivial T := (Subgroup.nontrivial_iff_ne_bot T).mpr hTne
    refine ⟨fun K hK => ?_⟩
    have hK'T : K.map T.subtype ≤ T := Subgroup.map_subtype_le K
    have hfwd : ∀ s ∈ T, ∀ h ∈ K.map T.subtype, s * h * s⁻¹ ∈ K.map T.subtype := by
      intro s hs h hh
      obtain ⟨k, hk, rfl⟩ := hh
      exact ⟨⟨s, hs⟩ * k * ⟨s, hs⟩⁻¹, hK.conj_mem k hk ⟨s, hs⟩, by simp⟩
    have hK'n : (K.map T.subtype).Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hsup𝒮, ← hsup]
      refine sSup_le fun U hU => ?_
      by_cases hUT : U = T
      · subst hUT
        intro t ht
        rw [Subgroup.mem_normalizer_iff]
        intro h
        refine ⟨hfwd t ht h, fun hh => ?_⟩
        have := hfwd t⁻¹ (inv_mem ht) _ hh
        simpa [mul_assoc] using this
      · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
        intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact (hcomm𝒯 T hT U hU (Ne.symm hUT) k u (hK'T hk) hu).eq
    rcases hTmin _ hK'n hK'T with h | h
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective _ T.subtype_injective).mp h)
    · right
      apply Subgroup.map_injective T.subtype_injective
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have h𝒯ne : 𝒯.Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    rintro rfl
    rw [sSup_empty, hsup𝒮] at hsup
    exact bot_ne_top hsup
  let r := Nat.card 𝒯
  let e₀ : 𝒯 ≃ Fin r := Finite.equivFin 𝒯
  let T : Fin r → Subgroup N := fun i => (e₀.symm i : Subgroup N)
  let S : Fin r → Subgroup G := fun i => (T i).map N.subtype
  have hT𝒯 : ∀ i, T i ∈ 𝒯 := fun i => (e₀.symm i).2
  have hTinj : Function.Injective T := fun i j h => e₀.symm.injective (Subtype.ext h)
  have hconjS : ∀ g : G, (S'.map (φ g).toMonoidHom).map N.subtype =
      conjugate (S'.map N.subtype) g⁻¹ := by
    intro g
    unfold conjugate
    rw [Subgroup.map_map, Subgroup.map_map, inv_inv]
    congr 1
  have hSconj : ∀ i, ∃ g : G, S i = conjugate (S'.map N.subtype) g := by
    intro i
    obtain ⟨g, hg⟩ := h𝒯𝒮 (hT𝒯 i)
    refine ⟨g⁻¹, ?_⟩
    change (T i).map N.subtype = _
    rw [← hg, hconjS]
  refine ⟨r, S, Finite.card_pos_iff.mpr h𝒯ne.to_subtype, fun i => Subgroup.map_subtype_le _,
    fun i => ?_, fun i j => ?_, fun i => ?_, ?_⟩
  · have := hsimple (T i) (hT𝒯 i)
    exact MulEquiv.isSimpleGroup ((T i).equivMapOfInjective N.subtype N.subtype_injective).symm
  · obtain ⟨a, ha⟩ := hSconj i
    obtain ⟨b, hb⟩ := hSconj j
    exact ⟨a⁻¹ * b, by rw [hb, ha, conjugate_conjugate, mul_inv_cancel_left]⟩
  · have hsub : (S i).subgroupOf N = T i :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective (T i)
    rw [hsub]
    exact (h𝒮 (T i) (h𝒯𝒮 (hT𝒯 i))).1
  · have hcommS : Pairwise fun i j => ∀ x y : G, x ∈ S i → y ∈ S j → Commute x y := by
      intro i j hij x y hx hy
      obtain ⟨x', hx', rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hy
      exact (hcomm𝒯 (T i) (hT𝒯 i) (T j) (hT𝒯 j) (fun h => hij (hTinj h)) x' y' hx'
        hy').map N.subtype
    have hindT : iSupIndep T := ((sSupIndep_iff 𝒯).mp hind).comp e₀.symm.injective
    have hindS : iSupIndep S := iSupIndep_map_of_injective N.subtype_injective hindT
    have hsupS : (⨆ i, S i) = N := by
      have h1 : (⨆ i, T i) = ⊤ := by
        rw [← hsup𝒮, ← hsup, sSup_eq_iSup']
        exact Equiv.iSup_comp (g := fun M : 𝒯 => (M : Subgroup N)) e₀.symm
      change (⨆ i, (T i).map N.subtype) = N
      rw [← Subgroup.map_iSup, h1, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    obtain ⟨e, he⟩ := exists_mulEquiv_pi_iSup S hcommS hindS
    exact ⟨e.trans (MulEquiv.subgroupCongr hsupS), fun i x hx => he i x hx⟩

end CFSG.LocalCores
