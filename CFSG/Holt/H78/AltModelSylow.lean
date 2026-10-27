module

public import CFSG.Holt.H78.AltModel
import CFSG.Holt.Induced

public section

namespace CFSG.Holt.H78

open Equiv Equiv.Perm MulAction CFSG.Holt CFSG.Open

variable {Δ : Type*} [Fintype Δ] [DecidableEq Δ]

section FixedPoints

private theorem natCard_compl_singleton (α : Δ) :
    Nat.card (({α}ᶜ : Set Δ)) = Fintype.card Δ - 1 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_compl_set]
  simp

theorem fixSet_eq_singleton_of_fusionIsSylowIn_alternatingGroup (hodd : Odd (Fintype.card Δ))
    (h5 : 5 ≤ Fintype.card Δ) {α : Δ} {P : Subgroup (Perm Δ)}
    (hP : fusionIsSylowIn 2 P (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α)) :
    fixSet Δ P = {α} := by
  rw [Nat.odd_iff] at hodd
  ext β
  rw [Set.mem_singleton_iff]
  constructor
  · intro hβ
    by_contra hne
    have h := not_dvd_card_orbit_of_fusionIsSylowIn hP hβ
    rw [orbit_alternatingGroup_inf_stabilizer (by omega) hne, natCard_compl_singleton] at h
    omega
  · rintro rfl y hy
    exact (Subgroup.mem_inf.1 (hP.1 hy)).2

theorem fusionIsSylowIn_alternatingGroup_of_stabilizer (hodd : Odd (Fintype.card Δ))
    (h3 : 3 ≤ Fintype.card Δ) {α : Δ} {P : Subgroup (Perm Δ)}
    (hP : fusionIsSylowIn 2 P (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α)) :
    fusionIsSylowIn 2 P (alternatingGroup Δ) := by
  set A := alternatingGroup Δ
  set K := A ⊓ stabilizer (Perm Δ) α
  have hPK : P ≤ K := hP.1
  have hKA : K ≤ A := inf_le_left
  obtain ⟨T, hT⟩ := exists_sylow_map_eq_of_fusionIsSylowIn hP
  have hTP : (T : Subgroup K) = P.subgroupOf K := by
    rw [← hT]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  have hPKodd : ¬ 2 ∣ P.relIndex K := by
    rw [Subgroup.relIndex, ← hTP]
    exact T.not_dvd_index
  have hPAodd : ¬ 2 ∣ (P.subgroupOf A).index := by
    rw [← Subgroup.relIndex, ← Subgroup.relIndex_mul_relIndex P K A hPK hKA,
      relIndex_alternatingGroup_inf_stabilizer h3 α]
    rw [Nat.odd_iff] at hodd
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h with h | h
    · exact hPKodd h
    · omega
  let S : Sylow 2 A := (hP.2.1.comap_of_injective A.subtype A.subtype_injective).toSylow hPAodd
  refine ⟨hPK.trans hKA, hP.2.1, fun Q hQA hQ hPQ => ?_⟩
  have hle : (S : Subgroup A) ≤ Q.subgroupOf A := fun x hx => hPQ hx
  have hS := S.is_maximal' (hQ.comap_of_injective A.subtype A.subtype_injective) hle
  apply le_antisymm _ hPQ
  intro x hx
  have hxS : (⟨x, hQA hx⟩ : A) ∈ (S : Subgroup A) := by
    rw [← hS]
    exact hx
  exact hxS

end FixedPoints

section Stabilizer

theorem map_ofSubtype_alternatingGroup (α : Δ) :
    (alternatingGroup {x // x ≠ α}).map (ofSubtype : Perm {x // x ≠ α} →* Perm Δ) =
      alternatingGroup Δ ⊓ stabilizer (Perm Δ) α := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_inf, mem_alternatingGroup, mem_stabilizer_iff,
    Perm.smul_def]
  constructor
  · rintro ⟨f, hf, rfl⟩
    rw [mem_alternatingGroup] at hf
    exact ⟨by rw [sign_ofSubtype, hf], ofSubtype_apply_of_not_mem f (not_not.2 rfl)⟩
  · rintro ⟨hsign, hα⟩
    have h₁ : ∀ x, g x ≠ α ↔ x ≠ α := fun x =>
      not_congr ⟨fun h => g.injective (h.trans hα.symm), fun h => by rw [h, hα]⟩
    have h₂ : ∀ x, g x ≠ x → x ≠ α := by
      rintro x hx rfl
      exact hx hα
    refine ⟨subtypePerm g h₁, ?_, ofSubtype_subtypePerm h₁ h₂⟩
    rw [mem_alternatingGroup, ← sign_ofSubtype, ofSubtype_subtypePerm h₁ h₂, hsign]

noncomputable def alternatingGroupStabilizerEquiv (α : Δ) :
    alternatingGroup {x // x ≠ α} ≃*
      (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α : Subgroup (Perm Δ)) :=
  ((alternatingGroup {x // x ≠ α}).equivMapOfInjective ofSubtype ofSubtype_injective).trans
    (MulEquiv.subgroupCongr (map_ofSubtype_alternatingGroup α))

@[simp] theorem coe_alternatingGroupStabilizerEquiv_apply (α : Δ)
    (f : alternatingGroup {x // x ≠ α}) :
    ((alternatingGroupStabilizerEquiv α f : _) : Perm Δ) = ofSubtype (f : Perm {x // x ≠ α}) := by
  simp only [alternatingGroupStabilizerEquiv, MulEquiv.trans_apply]
  rfl

private theorem card_subtype_ne (α : Δ) : Fintype.card {x // x ≠ α} = Fintype.card Δ - 1 := by
  simp

theorem two_mul_card_alternatingGroup_inf_stabilizer (h3 : 3 ≤ Fintype.card Δ) (α : Δ) :
    2 * Nat.card (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α : Subgroup (Perm Δ)) =
      (Fintype.card Δ - 1).factorial := by
  have : Nontrivial {x // x ≠ α} :=
    Fintype.one_lt_card_iff_nontrivial.1 (by rw [card_subtype_ne]; omega)
  rw [← Nat.card_congr (alternatingGroupStabilizerEquiv α).toEquiv, Nat.card_eq_fintype_card,
    two_mul_card_alternatingGroup, Fintype.card_perm, card_subtype_ne]

theorem isSimpleGroup_alternatingGroup_inf_stabilizer (h6 : 6 ≤ Fintype.card Δ) (α : Δ) :
    IsSimpleGroup (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α : Subgroup (Perm Δ)) := by
  have : IsSimpleGroup (alternatingGroup {x // x ≠ α}) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, card_subtype_ne]; omega)
  exact (alternatingGroupStabilizerEquiv α).symm.isSimpleGroup

theorem isPerfect_alternatingGroup_inf_stabilizer (h6 : 6 ≤ Fintype.card Δ) (α : Δ) :
    Group.IsPerfect (alternatingGroup Δ ⊓ stabilizer (Perm Δ) α : Subgroup (Perm Δ)) := by
  have : Group.IsPerfect (alternatingGroup {x // x ≠ α}) :=
    ⟨commutator_alternatingGroup_eq_top (by rw [Nat.card_eq_fintype_card, card_subtype_ne]; omega)⟩
  exact Group.IsPerfect.ofSurjective (f := (alternatingGroupStabilizerEquiv α).toMonoidHom)
    (alternatingGroupStabilizerEquiv α).surjective

theorem closure_mul_longInvAt_perm_eq (hodd : Odd (Fintype.card Δ)) (h7 : 7 ≤ Fintype.card Δ)
    (α : Δ) :
    Subgroup.closure {g : Perm Δ | ∃ u ∈ longInvAt (Perm Δ) Δ α, ∃ v ∈ longInvAt (Perm Δ) Δ α,
      u * v = g} = alternatingGroup Δ ⊓ stabilizer (Perm Δ) α := by
  set W := alternatingGroup Δ ⊓ stabilizer (Perm Δ) α
  set S := {g : Perm Δ | ∃ u ∈ longInvAt (Perm Δ) Δ α, ∃ v ∈ longInvAt (Perm Δ) Δ α, u * v = g}
  have hSW : S ⊆ W := by
    rintro _ ⟨u, hu, v, hv, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · rw [mem_alternatingGroup, Perm.sign_mul, sign_eq_of_mem_longInv_perm hu.1 hv.1,
        Int.units_mul_self]
    · rw [mem_stabilizer_iff, Perm.smul_def, Perm.mul_apply, show v α = α from hv.2,
        show u α = α from hu.2]
  refine le_antisymm ((Subgroup.closure_le _).2 hSW) ?_
  have hconj : ∀ w ∈ W, ∀ g ∈ Subgroup.closure S, w * g * w⁻¹ ∈ Subgroup.closure S := by
    intro w hw g hg
    have hwα : w α = α := (Subgroup.mem_inf.1 hw).2
    have hmap : (Subgroup.closure S).map (MulAut.conj w).toMonoidHom ≤ Subgroup.closure S := by
      rw [MonoidHom.map_closure]
      apply Subgroup.closure_mono
      rintro _ ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
      have hu' := conj_mem_longInvAt_perm hu w
      have hv' := conj_mem_longInvAt_perm hv w
      rw [hwα] at hu' hv'
      exact ⟨_, hu', _, hv', by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
    exact hmap ⟨g, hg, rfl⟩
  have : IsSimpleGroup W := isSimpleGroup_alternatingGroup_inf_stabilizer (by omega) α
  have hN : ((Subgroup.closure S).subgroupOf W).Normal := ⟨fun n hn w => hconj w w.2 n hn⟩
  obtain ⟨u, hu⟩ := exists_mem_longInvAt_perm hodd (by omega) α
  obtain ⟨x, hx⟩ := Fintype.exists_ne_of_one_lt_card (by omega) α
  obtain ⟨y, -, hy⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({α, x, u x} : Finset Δ)) (t := Finset.univ)
    (by rw [Finset.card_univ]; exact Finset.card_le_three.trans_lt (by omega))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
  obtain ⟨v, hv, hvx⟩ := exists_mem_longInvAt_perm_apply_eq hu hx hy.1 hy.2.1
  have huv : u * v ≠ 1 := by
    intro h
    have hu2 : u ^ 2 = 1 := hu.1.1 ▸ pow_orderOf_eq_one u
    have hvu : v = u := by
      rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hu2)]
    exact hy.2.2 (by rw [← hvx, hvu])
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((Subgroup.closure S).subgroupOf W) with h | h
  · exfalso
    have hmem : (⟨u * v, hSW ⟨u, hu, v, hv, rfl⟩⟩ : W) ∈ (Subgroup.closure S).subgroupOf W :=
      Subgroup.subset_closure ⟨u, hu, v, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    exact huv (congrArg Subtype.val hmem)
  · exact Subgroup.subgroupOf_eq_top.1 h

theorem map_closure_mul_longInvAt_eq_of_alternatingGroup_le (h7 : 7 ≤ Fintype.card Δ)
    {M : Subgroup (Perm Δ)} (hM : alternatingGroup Δ ≤ M) {s : Perm Δ} (hsM : s ∈ M)
    (hs : s ∈ longInv (Perm Δ) Δ) (α : Δ) :
    (Subgroup.closure {g : M | ∃ u ∈ longInvAt M Δ α, ∃ v ∈ longInvAt M Δ α, u * v = g}).map
      M.subtype = alternatingGroup Δ ⊓ stabilizer (Perm Δ) α := by
  have hJ := longInv_perm_subset_of_alternatingGroup_le hM hsM hs
  rw [MonoidHom.map_closure, ← closure_mul_longInvAt_perm_eq (odd_card_of_mem_longInv_perm hs)
    h7 α]
  congr 1
  ext g
  constructor
  · rintro ⟨_, ⟨u, hu, v, hv, rfl⟩, rfl⟩
    exact ⟨u, mem_longInvAt_subgroup_perm_iff.1 hu, v, mem_longInvAt_subgroup_perm_iff.1 hv, rfl⟩
  · rintro ⟨u, hu, v, hv, rfl⟩
    exact ⟨⟨u, hJ hu.1⟩ * ⟨v, hJ hv.1⟩, ⟨⟨u, hJ hu.1⟩, mem_longInvAt_subgroup_perm_iff.2 hu,
      ⟨v, hJ hv.1⟩, mem_longInvAt_subgroup_perm_iff.2 hv, rfl⟩, rfl⟩

end Stabilizer

section TripleFixed

private theorem exists_perm_of_cycleType {X : Type*} [Fintype X] [DecidableEq X]
    (ct : Multiset ℕ) (hsum : ct.sum = Fintype.card X) (h2 : 2 ∈ ct)
    (h24 : ∀ k ∈ ct, k = 2 ∨ k = 4) (heven : Even (ct.sum + Multiset.card ct)) :
    ∃ σ : Perm X, (∀ x, σ x ≠ x) ∧ σ ^ 4 = 1 ∧ sign σ = 1 ∧
      ∃ c : Perm X, sign c = -1 ∧ Commute c σ := by
  obtain ⟨σ, hσ⟩ := (exists_with_cycleType_iff X).2
    ⟨hsum.le, fun a ha => by rcases h24 a ha with rfl | rfl <;> norm_num⟩
  refine ⟨σ, fun x => ?_, ?_, ?_, ?_⟩
  · have hsupp : σ.support = Finset.univ := by
      apply Finset.eq_univ_of_card
      rw [← sum_cycleType, hσ, hsum]
    rw [← Perm.mem_support, hsupp]
    exact Finset.mem_univ x
  · apply orderOf_dvd_iff_pow_eq_one.1
    rw [← lcm_cycleType, hσ, Multiset.lcm_dvd]
    intro b hb
    rcases h24 b hb with rfl | rfl <;> norm_num
  · rw [sign_of_cycleType, hσ, heven.neg_one_pow]
  · obtain ⟨c, τ, hστ, hdisj, -, hc2⟩ := mem_cycleType_iff.1 (by rw [hσ]; exact h2)
    refine ⟨c, (card_support_eq_two.1 hc2).sign_eq, ?_⟩
    rw [hστ]
    exact (Commute.refl c).mul_right hdisj.commute

private theorem exists_perm_compl_three (hodd : Odd (Fintype.card Δ)) (h7 : 7 ≤ Fintype.card Δ)
    {s : Finset Δ} (hs : s.card = 3) :
    ∃ σ : Perm {x // x ∉ s}, (∀ x, σ x ≠ x) ∧ σ ^ 4 = 1 ∧ sign σ = 1 ∧
      ∃ c : Perm {x // x ∉ s}, sign c = -1 ∧ Commute c σ := by
  have hX : Fintype.card {x // x ∉ s} = Fintype.card Δ - 3 := by
    rw [← hs]
    simp
  rw [Nat.odd_iff] at hodd
  by_cases h4 : (Fintype.card Δ - 3) % 4 = 0
  · refine exists_perm_of_cycleType (Multiset.replicate ((Fintype.card Δ - 3) / 2) 2) ?_ ?_
      (fun k hk => Or.inl (Multiset.eq_of_mem_replicate hk)) ?_
    · rw [Multiset.sum_replicate, smul_eq_mul, hX]
      omega
    · exact Multiset.mem_replicate.2 ⟨by omega, rfl⟩
    · rw [Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul, Nat.even_iff]
      omega
  · refine exists_perm_of_cycleType (4 ::ₘ Multiset.replicate ((Fintype.card Δ - 7) / 2) 2)
      ?_ ?_ ?_ ?_
    · rw [Multiset.sum_cons, Multiset.sum_replicate, smul_eq_mul, hX]
      omega
    · exact Multiset.mem_cons_of_mem (Multiset.mem_replicate.2 ⟨by omega, rfl⟩)
    · intro k hk
      rcases Multiset.mem_cons.1 hk with rfl | hk
      · exact Or.inr rfl
      · exact Or.inl (Multiset.eq_of_mem_replicate hk)
    · rw [Multiset.sum_cons, Multiset.card_cons, Multiset.sum_replicate, Multiset.card_replicate,
        smul_eq_mul, Nat.even_iff]
      omega

theorem exists_isPGroup_fixSet_eq_triple (hodd : Odd (Fintype.card Δ)) (h7 : 7 ≤ Fintype.card Δ)
    {a b c : Δ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ S : Subgroup (Perm Δ), IsPGroup 2 S ∧ S ≤ alternatingGroup Δ ∧ fixSet Δ S = {a, b, c} ∧
      ∀ π : Perm Δ, (∀ x, x ≠ a → x ≠ b → x ≠ c → π x = x) →
        ∃ g ∈ alternatingGroup Δ ⊓ Subgroup.centralizer (S : Set (Perm Δ)),
          g a = π a ∧ g b = π b ∧ g c = π c := by
  have hs : ({a, b, c} : Finset Δ).card = 3 := Finset.card_eq_three.2 ⟨a, b, c, hab, hac, hbc, rfl⟩
  obtain ⟨σ₀, hfree, h4, hsign, c₀, hc₀, hcomm⟩ := exists_perm_compl_three hodd h7 hs
  have hmem : ∀ x, x ∈ ({a, b, c} : Finset Δ) ↔ x = a ∨ x = b ∨ x = c := fun x => by simp
  set σ : Perm Δ := ofSubtype σ₀ with hσdef
  have hσfix : ∀ x, σ x = x ↔ x ∈ ({a, b, c} : Finset Δ) := by
    intro x
    by_cases hx : x ∈ ({a, b, c} : Finset Δ)
    · simp only [hx, iff_true]
      exact ofSubtype_apply_of_not_mem σ₀ (not_not.2 hx)
    · simp only [hx, iff_false]
      intro h
      apply hfree ⟨x, hx⟩
      apply Subtype.ext
      rw [← ofSubtype_apply_coe]
      exact h
  have hσA : σ ∈ alternatingGroup Δ := by rw [mem_alternatingGroup, sign_ofSubtype, hsign]
  have hσ4 : σ ^ 4 = 1 := by rw [hσdef, ← map_pow, h4, map_one]
  have hτ : sign (ofSubtype c₀ : Perm Δ) = -1 := by rw [sign_ofSubtype, hc₀]
  have hτfix : ∀ x ∈ ({a, b, c} : Finset Δ), (ofSubtype c₀ : Perm Δ) x = x :=
    fun x hx => ofSubtype_apply_of_not_mem c₀ (not_not.2 hx)
  have hτσ : Commute (ofSubtype c₀ : Perm Δ) σ := hcomm.map ofSubtype
  have hcent : ∀ g : Perm Δ, Commute g σ →
      g ∈ Subgroup.centralizer (Subgroup.zpowers σ : Set (Perm Δ)) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hg.symm.zpow_left j).eq
  refine ⟨Subgroup.zpowers σ, ?_, Subgroup.zpowers_le.2 hσA, ?_, ?_⟩
  · have hd : orderOf σ ∣ 2 ^ 2 := orderOf_dvd_of_pow_eq_one hσ4
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  · ext x
    rw [fixSet_zpowers, mem_fixedBy, Perm.smul_def, hσfix, hmem]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  · intro π hπ
    have hπσ : Commute π σ := by
      apply Perm.Disjoint.commute
      intro x
      by_cases hx : x ∈ ({a, b, c} : Finset Δ)
      · exact Or.inr ((hσfix x).2 hx)
      · rw [hmem, not_or, not_or] at hx
        exact Or.inl (hπ x hx.1 hx.2.1 hx.2.2)
    by_cases hπA : π ∈ alternatingGroup Δ
    · exact ⟨π, Subgroup.mem_inf.2 ⟨hπA, hcent π hπσ⟩, rfl, rfl, rfl⟩
    refine ⟨π * ofSubtype c₀, Subgroup.mem_inf.2 ⟨?_, hcent _ (hπσ.mul_left hτσ)⟩, ?_, ?_, ?_⟩
    · rw [mem_alternatingGroup] at hπA ⊢
      rw [Perm.sign_mul, hτ, (Int.units_eq_one_or _).resolve_left hπA, Int.units_mul_self]
    · rw [Perm.mul_apply, hτfix a ((hmem a).2 (Or.inl rfl))]
    · rw [Perm.mul_apply, hτfix b ((hmem b).2 (Or.inr (Or.inl rfl)))]
    · rw [Perm.mul_apply, hτfix c ((hmem c).2 (Or.inr (Or.inr rfl)))]

end TripleFixed

end CFSG.Holt.H78
