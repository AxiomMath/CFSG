module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenFamData
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenSylow
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenType

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B2F CFSG.Quasithin.E2 Equiv
  Equiv.Perm

variable {G : Type} [Group G] [Finite G]

theorem exists_genFamData {H T M V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hmin : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hS : SymCaseGen H T V hV) :
    ∃ m : ℕ, 2 ≤ m ∧ Nonempty (GenFamData (2 ^ m + 1) H T V hV) := by
  classical
  obtain ⟨-, I, hfam, m, hm, hall⟩ := hS
  obtain ⟨hne, hJH, hcomm, hconj, -, -, h3⟩ := hfam
  obtain ⟨hbaum, hJTeq, hcl⟩ := h3 m hm hall
  have hHN : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTH : T ≤ H := hmin.isSylow.1
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hN5 : 5 ≤ 2 ^ m + 1 := by omega
  have hNodd : Odd (2 ^ m + 1) := (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  obtain ⟨L, hL⟩ := hne
  obtain ⟨θ, β, hβ, hW⟩ := hcl L hL
  have hLN : L ≤ autI hV (thompsonJ H) := by
    rw [hJH]
    exact le_iSup₂ (f := fun L _ => L) L hL
  have hNL : autI hV (thompsonJ H) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) := by
    rw [hJH]
    have := iSup_inf_le_normalizer' I hcomm hL (le_refl L) ⊤
      (by simpa using Subgroup.le_normalizer)
    simpa using this
  have hTs : IsSylowTwoOf (autI hV T) (autI hV H) := isSylowTwoOf_autI hV hHN hmin.isSylow
  have hNH : autI hV (thompsonJ H) ≤ autI hV H := autI_mono hV (thompsonJ_le_self H)
  have hHsN := autI_le_normalizer_autI' hV (B6.le_normalizer_thompsonJ H)
  have hSylN : IsSylowTwoOf (autI hV T ⊓ autI hV (thompsonJ H)) (autI hV (thompsonJ H)) :=
    B6.isSylowTwoOf_inf_normal hTs hNH hHsN
  have hSylL : IsSylowTwoOf (autI hV T ⊓ L) L := by
    have := B6.isSylowTwoOf_inf_normal hSylN hLN hNL
    rwa [inf_assoc, inf_eq_right.2 hLN] at this
  set D : Subgroup (Perm (Fin (2 ^ m + 1))) :=
    ((autI hV T ⊓ L).subgroupOf L).map θ.toMonoidHom with hD
  have hDcard : Nat.card D = 2 ^ padicValNat 2 (2 ^ m + 1).factorial := by
    rw [hD, Subgroup.card_map_of_injective (by exact θ.injective),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right :
        autI hV T ⊓ L ≤ L)).toEquiv, hSylL.card_eq]
    unfold twoPart
    rw [card_of_isSymCoreModule ⟨θ, β, hβ⟩, Nat.factorization_def _ Nat.prime_two]
  have hDp : IsPGroup 2 ↥D := IsPGroup.of_card hDcard
  have hJTne : autI hV (thompsonJ T) ≠ ⊥ := fun h =>
    hJ ((autI_eq_bot_iff hV ((thompsonJ_le_self T).trans (hTH.trans hHN))).1 h)
  have hLJne : L ⊓ autI hV (thompsonJ T) ≠ ⊥ := by
    obtain ⟨L', hL', hne'⟩ : ∃ L' ∈ I, L' ⊓ autI hV (thompsonJ T) ≠ ⊥ := by
      by_contra hcon
      push Not at hcon
      apply hJTne
      rw [hJTeq]
      exact eq_bot_iff.2 (iSup₂_le fun L' hL' => (hcon L' hL').le)
    obtain ⟨t, htT, htL⟩ := hconj L' hL' L hL
    have h1 : B1.conjAut t (L' ⊓ autI hV (thompsonJ T)) = L ⊓ autI hV (thompsonJ T) := by
      ext x
      have h2 := conjAut_autI_thompsonJ (hV := hV) (H := T) htT
      have h5 : x ∈ B1.conjAut t (autI hV (thompsonJ T)) ↔ x ∈ autI hV (thompsonJ T) := by
        rw [h2]
      have h6 : x ∈ B1.conjAut t L' ↔ x ∈ L := by rw [htL]
      rw [B1.mem_conjAut] at h5 h6
      simp only [B1.mem_conjAut, Subgroup.mem_inf]
      rw [h5, h6]
    rw [← h1]
    exact B1.conjAut_ne_bot hne'
  obtain ⟨x₀, hx₀L, hx₀T, a, b, hab, hx₀θ⟩ : ∃ x, ∃ hx : x ∈ L, x ∈ autI hV T ∧
      ∃ a b : Fin (2 ^ m + 1), a ≠ b ∧ θ ⟨x, hx⟩ = swap a b := by
    by_contra hcon
    push Not at hcon
    apply hLJne
    rw [hW]
    refine eq_bot_iff.2 ((Subgroup.closure_le _).2 fun x hx => ?_)
    obtain ⟨hxL, hxT, u, v, huv, hxuv⟩ := hx
    exact absurd hxuv (hcon x hxL hxT u v huv)
  have hx₀J : x₀ ∈ autI hV (thompsonJ T) := by
    have : x₀ ∈ L ⊓ autI hV (thompsonJ T) := by
      rw [hW]
      exact Subgroup.subset_closure ⟨hx₀L, hx₀T, a, b, hab, hx₀θ⟩
    exact this.2
  have hswD : swap a b ∈ D := hx₀θ ▸ ⟨⟨x₀, hx₀L⟩, Subgroup.mem_subgroupOf.2 ⟨hx₀T, hx₀L⟩, rfl⟩
  have hnd : ¬ 2 ∣ Nat.card (Fin (2 ^ m + 1)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    exact Nat.not_even_iff_odd.mpr hNodd ∘ even_iff_two_dvd.mpr
  obtain ⟨p, hp⟩ := hDp.nonempty_fixed_point_of_prime_not_dvd_card (Fin (2 ^ m + 1)) hnd
  have hpD : ∀ d ∈ D, d p = p := fun d hd => hp ⟨d, hd⟩
  have hsp := hpD _ hswD
  have hap : a ≠ p := fun h => by
    rw [← h, swap_apply_left] at hsp
    exact hab hsp.symm
  have hbp : b ≠ p := fun h => by
    rw [← h, swap_apply_right] at hsp
    exact hab hsp
  have hgen : ∀ (x : MulAut (IntMod V hV)) (hx : x ∈ L), x ∈ autI hV T →
      (θ ⟨x, hx⟩).IsSwap → θ ⟨x, hx⟩ ∈
        Subgroup.normalizer (Subgroup.closure {c3 a b p} : Set (Perm (Fin (2 ^ m + 1)))) := by
    intro x hx hxT hsw
    obtain ⟨u, v, huv, hxuv⟩ := hsw
    have hxD : θ ⟨x, hx⟩ ∈ D := ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.2 ⟨hxT, hx⟩, rfl⟩
    rw [hxuv] at hxD ⊢
    rcases eq_or_nodup_of_swaps hDp hab huv hswD hxD with heq | hnodup
    · rw [← heq]
      refine mem_normalizer_closure_of_conj ?_
      have : swap a b * c3 a b p * (swap a b)⁻¹ = (c3 a b p)⁻¹ := by
        rw [swap_inv]
        exact swap_c3_swap a b p
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    · have hup := hpD _ hxD
      have hu : u ≠ p := fun h => by
        rw [h, swap_apply_left] at hup
        exact huv (by rw [h]; exact hup.symm)
      have hv : v ≠ p := fun h => by
        rw [h, swap_apply_right] at hup
        exact huv (hup.trans h.symm)
      have hau : a ≠ u := fun h => by
        rw [h] at hnodup
        simp at hnodup
      have hav : a ≠ v := fun h => by
        rw [h] at hnodup
        simp at hnodup
      have hbu : b ≠ u := fun h => by
        rw [h] at hnodup
        simp at hnodup
      have hbv : b ≠ v := fun h => by
        rw [h] at hnodup
        simp at hnodup
      have hc : swap u v * c3 a b p = c3 a b p * swap u v := by
        refine swap_commute_c3 ?_ ?_
        · simp [List.nodup_cons, huv, hau.symm, hav.symm, hbu.symm, hbv.symm, hab]
        · simp [List.nodup_cons, huv, hu, hv, hbu.symm, hbv.symm, hbp]
      refine mem_normalizer_closure_of_conj ?_
      have : swap u v * c3 a b p * (swap u v)⁻¹ = c3 a b p := by
        rw [hc, mul_inv_cancel_right]
      rw [this]
      exact Subgroup.mem_zpowers _
  set C : Subgroup (MulAut (IntMod V hV)) := (Subgroup.closure {c3 a b p}).map (embL L θ) with hC
  have hCL : C ≤ L := by
    rintro _ ⟨x, -, rfl⟩
    exact embL_mem L θ x
  have hCθ : ∀ φ ∈ C, ∃ hφ : φ ∈ L, θ ⟨φ, hφ⟩ ∈ Subgroup.closure {c3 a b p} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨embL_mem L θ x, ?_⟩
    have : θ ⟨embL L θ x, embL_mem L θ x⟩ = x := by simp [embL_apply]
    rw [this]
    exact hx
  have hWstN : L ⊓ autI hV (thompsonJ T) ≤
      Subgroup.normalizer (C : Set (MulAut (IntMod V hV))) := by
    intro x hx
    rw [hW] at hx
    have key : ∀ y ∈ Subgroup.closure {x | ∃ hx : x ∈ L, x ∈ autI hV T ∧ (θ ⟨x, hx⟩).IsSwap},
        ∃ hyL : y ∈ L, θ ⟨y, hyL⟩ ∈ Subgroup.normalizer
          (Subgroup.closure {c3 a b p} : Set (Perm (Fin (2 ^ m + 1)))) := by
      intro y hy
      refine Subgroup.closure_induction (p := fun y _ => ∃ hyL : y ∈ L, θ ⟨y, hyL⟩ ∈
        Subgroup.normalizer (Subgroup.closure {c3 a b p} : Set (Perm (Fin (2 ^ m + 1)))))
        ?_ ?_ ?_ ?_ hy
      · rintro x ⟨hxL, hxT, hsw⟩
        exact ⟨hxL, hgen x hxL hxT hsw⟩
      · refine ⟨L.one_mem, ?_⟩
        have : (⟨1, L.one_mem⟩ : ↥L) = 1 := rfl
        rw [this, map_one]
        exact Subgroup.one_mem _
      · rintro x y - - ⟨hxL, hx⟩ ⟨hyL, hy⟩
        refine ⟨L.mul_mem hxL hyL, ?_⟩
        have : (⟨x * y, L.mul_mem hxL hyL⟩ : ↥L) = ⟨x, hxL⟩ * ⟨y, hyL⟩ := rfl
        rw [this, map_mul]
        exact Subgroup.mul_mem _ hx hy
      · rintro x - ⟨hxL, hx⟩
        refine ⟨L.inv_mem hxL, ?_⟩
        have : (⟨x⁻¹, L.inv_mem hxL⟩ : ↥L) = ⟨x, hxL⟩⁻¹ := rfl
        rw [this, map_inv]
        exact Subgroup.inv_mem _ hx
    obtain ⟨hxL, hxN⟩ := key x hx
    exact mem_normalizer_map_embL hxL hxN
  have hJTC : autI hV (thompsonJ T) ≤ Subgroup.normalizer (C : Set (MulAut (IntMod V hV))) :=
    hJTeq.le.trans (iSup_inf_le_normalizer' I hcomm hL hCL (autI hV (thompsonJ T)) hWstN)
  have hDtop : D ⊔ Subgroup.closure {c3 a b p} = ⊤ :=
    sup_c3_eq_top hm D hDcard hab hap hpD hswD
  refine ⟨m, hm, ⟨⟨hN5, hNodd, L, θ, β, hβ, a, b, p, hab, hbp, hap, C, ?_, hCL, hCθ, hLN, hNL, hJTC,
    hbaum.le.trans hJTC, ?_, ?_, ?_⟩⟩⟩
  · rw [hC, Subgroup.card_map_of_injective (embL_injective L θ), card_closure_c3 hab hbp hap]
  · intro X hTX hCX
    set E : Subgroup (Perm (Fin (2 ^ m + 1))) := (X.subgroupOf L).map θ.toMonoidHom with hE
    have hDE : D ≤ E := by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hTX hy.1, rfl⟩
    have hcE : Subgroup.closure {c3 a b p} ≤ E := by
      rw [Subgroup.closure_le]
      rintro _ rfl
      exact ⟨θ.symm (c3 a b p), hCX ⟨c3 a b p, Subgroup.subset_closure rfl, rfl⟩, by simp⟩
    have hEtop : E = ⊤ := top_le_iff.1 (hDtop ▸ sup_le hDE hcE)
    intro x hx
    have : θ ⟨x, hx⟩ ∈ E := hEtop ▸ Subgroup.mem_top _
    obtain ⟨y, hy, hyx⟩ := this
    have hyx' : y = ⟨x, hx⟩ := θ.injective hyx
    subst hyx'
    exact hy
  · intro X hTX hLX
    rw [hJH]
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨t, htT, ht⟩ := hconj L hL L' hL'
    intro x hx
    rw [← ht, B1.mem_conjAut] at hx
    have h1 : t⁻¹ * x * t ∈ X := hLX hx
    have h2 : t ∈ X := hTX htT
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact X.mul_mem (X.mul_mem h2 h1) (X.inv_mem h2)
  · exact ⟨x₀, hx₀J, hx₀L, hx₀θ⟩

end CFSG.AGLEmbeddingD2.GN
