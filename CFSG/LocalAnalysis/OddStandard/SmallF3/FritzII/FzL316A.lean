module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzDefs

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def fzlPhi (H : Subgroup G) : Subgroup G :=
  ⁅H, H⁆ ⊔ closure ((fun g : G => g ^ 2) '' (H : Set G))

@[expose] def FzCanon (T S : Subgroup G) : Prop :=
  ∀ α : G ≃* G, (∀ g, g ∈ T ↔ α g ∈ T) → ∀ g, g ∈ S ↔ α g ∈ S

theorem fzl_canon_self (T : Subgroup G) : FzCanon T T :=
  fun _ h g => h g

theorem fzl_sq_mem_phi {H : Subgroup G} {g : G} (hg : g ∈ H) : g ^ 2 ∈ fzlPhi H :=
  Subgroup.mem_sup_right (Subgroup.subset_closure ⟨g, hg, rfl⟩)

theorem fzl_comm_mem_phi {H : Subgroup G} {a b : G} (ha : a ∈ H) (hb : b ∈ H) :
    ⁅a, b⁆ ∈ fzlPhi H :=
  Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator ha hb)

theorem fzl_phi_mono {H K : Subgroup G} (h : H ≤ K) : fzlPhi H ≤ fzlPhi K :=
  sup_le_sup (Subgroup.commutator_mono h h)
    (Subgroup.closure_mono (Set.image_mono (fun _ hg => h hg)))

theorem fzl_phi_le_of_elem {T Q : Subgroup G} (hc : ∀ g ∈ T, ∀ h ∈ T, ⁅g, h⁆ ∈ Q)
    (hs : ∀ g ∈ T, g ^ 2 ∈ Q) : fzlPhi T ≤ Q := by
  refine sup_le (Subgroup.commutator_le.mpr hc) ?_
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hg, rfl⟩
  exact hs g hg

theorem fzl_comm_mem_of_sq {N : Subgroup G} {g g' : G} (hg : g ^ 2 ∈ N) (hg' : g' ^ 2 ∈ N)
    (hgg : (g * g') ^ 2 ∈ N) (hn : ∀ n ∈ N, g'⁻¹ * n * g' ∈ N) : ⁅g, g'⁆ ∈ N := by
  have key : ⁅g, g'⁆ =
      (g * g') ^ 2 * (g'⁻¹ * (g ^ 2)⁻¹ * g') * (g' ^ 2)⁻¹ := by
    simp only [commutatorElement_def, pow_two]
    group
  rw [key]
  exact N.mul_mem (N.mul_mem hgg (hn _ (N.inv_mem hg))) (N.inv_mem hg')

theorem fzl_phi_map {G' : Type} [Group G'] (f : G →* G') (H : Subgroup G) :
    (fzlPhi H).map f = fzlPhi (H.map f) := by
  unfold fzlPhi
  rw [Subgroup.map_sup, Subgroup.map_commutator, MonoidHom.map_closure, Set.image_image]
  congr 2
  ext x
  simp [Set.mem_image, Subgroup.mem_map, map_pow]

private theorem fzl_map_eq_self {T S : Subgroup G} (h : FzCanon T S) (α : G ≃* G)
    (hα : ∀ g, g ∈ T ↔ α g ∈ T) : S.map α.toMonoidHom = S := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact (h α hα s).mp hs
  · intro hx
    exact ⟨α⁻¹ x, (h α hα (α⁻¹ x)).mpr (by simpa using hx), by simp⟩

theorem fzl_canon_phi {T S : Subgroup G} (h : FzCanon T S) : FzCanon T (fzlPhi S) := by
  intro α hα g
  have hmap : (fzlPhi S).map α.toMonoidHom = fzlPhi S := by
    rw [fzl_phi_map, fzl_map_eq_self h α hα]
  constructor
  · intro hg
    rw [← hmap]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← hmap] at hg
    obtain ⟨s, hs, hsg⟩ := hg
    rwa [α.injective hsg] at hs

theorem fzl_canon_cent {T S S' : Subgroup G} (h : FzCanon T S)
    (hS' : ∀ g, g ∈ S' ↔ g ∈ T ∧ ∀ s ∈ S, g * s = s * g) : FzCanon T S' := by
  intro α hα g
  have hS : ∀ x, x ∈ S ↔ α x ∈ S := h α hα
  rw [hS' g, hS' (α g)]
  constructor
  · rintro ⟨hgT, hcomm⟩
    refine ⟨(hα g).mp hgT, ?_⟩
    intro s hs
    have hs' : α⁻¹ s ∈ S := (hS (α⁻¹ s)).mpr (by simpa using hs)
    have h := hcomm (α⁻¹ s) hs'
    have h2 : α (g * α⁻¹ s) = α (α⁻¹ s * g) := congrArg α h
    simpa using h2
  · rintro ⟨hgT, hcomm⟩
    refine ⟨(hα g).mpr hgT, ?_⟩
    intro s hs
    have hs' : α s ∈ S := (hS s).mp hs
    exact α.injective (by simpa using hcomm (α s) hs')

theorem fzl_canon_pow {T S S' : Subgroup G} (h : FzCanon T S) (k : ℕ)
    (hS' : ∀ g, g ∈ S' ↔ g ∈ S ∧ g ^ k = 1) : FzCanon T S' := by
  intro α hα g
  have hS : ∀ x, x ∈ S ↔ α x ∈ S := h α hα
  rw [hS' g, hS' (α g), hS g, ← map_pow, α.map_eq_one_iff]

theorem fzl_canon_pow_comm {T S S₂ S' : Subgroup G} (h : FzCanon T S) (h₂ : FzCanon T S₂)
    (k : ℕ) (hS' : ∀ g, g ∈ S' ↔ g ∈ S ∧ g ^ k = 1 ∧ ∀ s ∈ S₂, g * s = s * g) :
    FzCanon T S' := by
  intro α hα g
  have hS : ∀ x, x ∈ S ↔ α x ∈ S := h α hα
  have hS₂ : ∀ x, x ∈ S₂ ↔ α x ∈ S₂ := h₂ α hα
  rw [hS' g, hS' (α g), hS g, ← map_pow, α.map_eq_one_iff]
  constructor
  · rintro ⟨hgS, hgk, hcomm⟩
    refine ⟨hgS, hgk, ?_⟩
    intro s hs
    have hs' : α⁻¹ s ∈ S₂ := (hS₂ (α⁻¹ s)).mpr (by simpa using hs)
    have h := hcomm (α⁻¹ s) hs'
    have h2 : α (g * α⁻¹ s) = α (α⁻¹ s * g) := congrArg α h
    simpa using h2
  · rintro ⟨hgS, hgk, hcomm⟩
    refine ⟨hgS, hgk, ?_⟩
    intro s hs
    have hs' : α s ∈ S₂ := (hS₂ s).mp hs
    exact α.injective (by simpa using hcomm (α s) hs')

theorem fzl_sylow_of_normalizer_le [Finite G] {N T : Subgroup G} (hTN : T ≤ N)
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.relIndex N)
    (hN : ∀ g : G, g ∈ normalizer (T : Set G) → g ∈ N) : FzSylow T := by
  refine ⟨hT, ?_⟩
  obtain ⟨P, hTP⟩ := hT.exists_le_sylow (p := 2)
  have hPT : (P : Subgroup G) = T := by
    by_contra hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let H : Subgroup (P : Subgroup G) := T.subgroupOf P
    have hHtop : H ≠ ⊤ := by
      intro htop
      exact hne (le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hTP)
    have hHlt : H < ⊤ := lt_top_iff_ne_top.mpr hHtop
    haveI hfin : Finite (P : Subgroup G) := inferInstance
    haveI hnil : Group.IsNilpotent (P : Subgroup G) := P.isPGroup'.isNilpotent
    have hnc : NormalizerCondition (P : Subgroup G) :=
      Group.normalizerCondition_of_isNilpotent
    obtain ⟨x, hxN, hxH⟩ := SetLike.exists_of_lt (hnc H hHlt)
    have hxN' : ∀ y : (P : Subgroup G), y ∈ H ↔ x * y * x⁻¹ ∈ H :=
      Subgroup.mem_normalizer_iff.mp hxN
    let g : G := x
    have hgP : g ∈ P := x.2
    have hgmem : g ∈ normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hyT
        have hyH : (⟨y, hTP hyT⟩ : (P : Subgroup G)) ∈ H := hyT
        have hconj : x * ⟨y, hTP hyT⟩ * x⁻¹ ∈ H := (hxN' _).mp hyH
        simpa [H, g, Subgroup.mem_subgroupOf] using hconj
      · intro hyT
        have hyP : y ∈ P := by
          have hgPg : g * y * g⁻¹ ∈ P := hTP hyT
          have : g⁻¹ * (g * y * g⁻¹) * g ∈ P :=
            P.mul_mem (P.mul_mem (P.inv_mem hgP) hgPg) hgP
          simpa [mul_assoc] using this
        have hyH : (⟨y, hyP⟩ : (P : Subgroup G)) ∈ H :=
          (hxN' _).mpr (by simpa [H, g, Subgroup.mem_subgroupOf] using hyT)
        exact hyH
    have hgN : g ∈ N := hN g hgmem
    let M : Subgroup G := P ⊓ N
    have hTM : T ≤ M := le_inf hTP hTN
    have hMN : M ≤ N := inf_le_right
    have hMP : M ≤ P := inf_le_left
    have hM2 : IsPGroup 2 M := P.isPGroup'.to_le hMP
    obtain ⟨k, hk⟩ := hM2.exists_card_eq
    have hcard : T.relIndex M ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card (H := T) (K := M)
    have hidx_dvd : T.relIndex M ∣ T.relIndex N :=
      ⟨M.relIndex N, (Subgroup.relIndex_mul_relIndex T M N hTM hMN).symm⟩
    have hoddM : ¬ 2 ∣ T.relIndex M := fun h2 => hodd (h2.trans hidx_dvd)
    have hrel : T.relIndex M = 1 := by
      obtain ⟨j, _hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hcard
      rw [hj] at hoddM ⊢
      by_cases hj0 : j = 0
      · simp [hj0]
      · exact absurd (dvd_pow_self 2 hj0) hoddM
    have hMT : M ≤ T := Subgroup.relIndex_eq_one.mp hrel
    have hgT : g ∈ T := hMT ⟨hgP, hgN⟩
    exact hxH (by simpa [H, g, Subgroup.mem_subgroupOf] using hgT)
  rw [← hPT]
  exact P.not_dvd_index

theorem fzl_sylow_of_canon [Finite G] {W T : Subgroup G} (hTN : T ≤ normalizer (W : Set G))
    (hT : IsPGroup 2 T) (hodd : ¬ 2 ∣ T.relIndex (normalizer (W : Set G)))
    (hW : FzCanon T W) : FzSylow T := by
  refine fzl_sylow_of_normalizer_le hTN hT hodd ?_
  intro g hg
  have hα : ∀ x, x ∈ T ↔ MulAut.conj g x ∈ T := by
    intro x
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hg) x
  have hWg : ∀ w, w ∈ W ↔ g * w * g⁻¹ ∈ W := by
    intro w
    have := hW (MulAut.conj g) hα w
    rwa [MulAut.conj_apply] at this
  exact Subgroup.mem_normalizer_iff.mpr hWg

end CFSG.OddStandard.SmallF3.FritzII
