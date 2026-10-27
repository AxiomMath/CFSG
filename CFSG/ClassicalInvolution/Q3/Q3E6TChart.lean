module

public import CFSG.ClassicalInvolution.Q3.Q3URTriple

public section

namespace CFSG.ClassicalInvolution.Q3.Q3E6T

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.Models.TwistedPairs CFSG.ClassicalInvolution.Phan
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Steinberg.Exceptional
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Models.Transfer
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

structure TE6Chart3 (c : UCtx3 5 Ω K z) (nd : UNodes3 c)
    (Θ : Su (GaloisField 3 2) 3 1 6 →* G) : Prop where
  ker_le : Θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 6)
  block : ∀ i : Fin 5, (blockEmb2 (GaloisField 3 2) 3 1 5 i).range.map Θ = nd.j i.val
  range_eq : Θ.range = ⨆ i : Fin 5, nd.j i.val
  member : ∀ R ∈ longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1)
      (by norm_num : 2 ≤ 6), R.map Θ ∈ centralizingMembers Ω {z} ∧ R.map Θ ≠ K
  cover : ∀ L ∈ centralizingMembers Ω {z}, L ≠ K → ∃ R ∈ longRootSetU
      (K := GaloisField 3 2) (p := 3) (f := 1) (by norm_num : 2 ≤ 6), L = R.map Θ

namespace TE6Chart3

variable {c : UCtx3 5 Ω K z} {nd : UNodes3 c} {Θ : Su (GaloisField 3 2) 3 1 6 →* G}

theorem commutes_K_range (hΘ : TE6Chart3 c nd Θ) : Commutes K Θ.range := by
  have : Θ.range ≤ Subgroup.centralizer (K : Set G) := by
    rw [hΘ.range_eq]
    refine iSup_le fun i x hx => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact nd.commK i.val (by omega) k hk x hx
  intro k hk x hx
  exact (Subgroup.mem_centralizer_iff.mp (this hx)) k hk

end TE6Chart3

section Existence

variable [Finite G]

theorem UCtx3.exists_te6Chart3 (hP : Phan3Rec) (c : UCtx3 5 Ω K z) (nd : UNodes3 c) :
    ∃ Θ : Su (GaloisField 3 2) 3 1 6 →* G, TE6Chart3 c nd Θ := by
  classical
  have hiso : ∀ i : Fin (3 + 2), Nonempty (Su (GaloisField 3 2) 3 1 2 ≃* ↥(nd.j i.val)) :=
    fun i => nonempty_su_two_equiv_of_member3 c.hΩ c.hex
      (nd.mem i.val (by have := i.isLt; omega)).1
  have hcomm : ∀ i j : Fin (3 + 2), (i : ℕ) + 1 < j → Commutes (nd.j i.val) (nd.j j.val) :=
    fun i j hij => nd.far i.val (by omega) j.val (by omega) (by omega)
  have hpair : ∀ i j : Fin (3 + 2), (j : ℕ) = i + 1 → ∃ W, UnitaryBlockStandardPair
      (GaloisField 3 2) 3 1 W (nd.j i.val) (nd.j j.val) := by
    intro i j hij
    have := nd.pair i.val (by omega)
    rwa [← hij] at this
  have htriple : ∀ i j k : Fin (3 + 2), (j : ℕ) = i + 1 → (k : ℕ) = j + 1 →
      ∃ θ : Su (GaloisField 3 2) 3 1 4 →* G,
        θ.range = (nd.j i.val ⊔ nd.j j.val) ⊔ (nd.j j.val ⊔ nd.j k.val) ∧
          θ.ker ≤ Subgroup.center (Su (GaloisField 3 2) 3 1 4) ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 0).range.map θ = nd.j i.val ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 1).range.map θ = nd.j j.val ∧
          (blockEmb2 (GaloisField 3 2) 3 1 3 2).range.map θ = nd.j k.val := by
    intro i j k hj hk
    have hjv : j.val = i.val + 1 := hj
    have hkv : k.val = i.val + 2 := by omega
    have h := c.node_triple nd noCover_su4_three (by norm_num : 3 ≤ 5) (a := i.val) (by omega)
    rw [hjv, hkv]
    exact h
  obtain ⟨Θ, hker, hrange, hblk⟩ := exists_psi_of_chainU3 hP (m := 3) (by norm_num)
    (U := fun i : Fin (3 + 2) => nd.j i.val) hiso hcomm hpair htriple
  have hn6 : 2 ≤ 6 := by norm_num
  set T : Set (Subgroup (Su (GaloisField 3 2) 3 1 6)) :=
    longRootSetU (K := GaloisField 3 2) (p := 3) (f := 1) hn6 with hT
  have h0 : (rootSU2 (GaloisField 3 2) 3 1 hn6).map Θ = nd.j 0 := hblk ⟨0, by norm_num⟩
  have hconj : ∀ R ∈ T, ∃ g, R.map Θ = conjSub (Θ g) (nd.j 0) := by
    intro R hR
    obtain ⟨g, hg⟩ := (mem_longRootSetU_iff hn6).mp hR
    refine ⟨g, ?_⟩
    rw [hg, ← h0, conjSub_map]
    rfl
  have hmemΩ : ∀ R ∈ T, R.map Θ ∈ Ω := by
    intro R hR
    obtain ⟨g, hg⟩ := hconj R hR
    rw [hg]
    exact c.hΩ.conjInvariant _ _ (nd.mem 0 (by norm_num)).1
  have hRange_cz : Θ.range ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hrange]
    exact iSup_le fun i => (nd.mem i.val (by omega)).2
  have hKc : Commutes K Θ.range := by
    have : Θ.range ≤ Subgroup.centralizer (K : Set G) := by
      rw [hrange]
      refine iSup_le fun i x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact nd.commK i.val (by omega) k hk x hx
    intro k hk x hx
    exact (Subgroup.mem_centralizer_iff.mp (this hx)) k hk
  set B : Set (Subgroup G) := centralizingMembers Ω {z} \ {K} with hB
  set A : Set (Subgroup G) := (fun R => R.map Θ) '' T with hA
  have hAB : A ⊆ B := by
    rintro _ ⟨R, hR, rfl⟩
    refine ⟨⟨hmemΩ R hR, (Subgroup.map_le_range Θ R).trans hRange_cz⟩, fun hRK => ?_⟩
    have hRK' : R.map Θ = K := hRK
    refine not_commutes_self3 c.hz ?_
    intro k hk k' hk'
    rw [← hRK'] at hk'
    exact hKc k hk k' (Subgroup.map_le_range Θ R hk')
  have hinj : Set.InjOn (fun R => R.map Θ) T := by
    rintro R ⟨i, hi⟩ R' ⟨i', hi'⟩ h
    have hRi : IsLongRootSU2Image Θ hn6 (R.map Θ) (Θ i) := ⟨R, i, hi, rfl, rfl⟩
    have hRi' : IsLongRootSU2Image Θ hn6 (R'.map Θ) (Θ i') := ⟨R', i', hi', rfl, rfl⟩
    have h1 : Θ i' = Θ i :=
      eq_of_orderOf_eq_two_of_image3 (by norm_num) hker hRi
        (by
          have : Θ i' ∈ R'.map Θ := Subgroup.mem_map_of_mem Θ hi'.mem
          exact (show R.map Θ = R'.map Θ from h) ▸ this)
        (orderOf_eq_two_of_image3 (by norm_num) hker hRi')
    have h2 : i = i' :=
      eq_of_map_eq_of_isLongRootSU2_3 (by norm_num) hi hi' hker (Or.inl (by norm_num)) h1.symm
    rw [hi.eq_longRootGroupSU two_ne_zero_gf9, hi'.eq_longRootGroupSU two_ne_zero_gf9, h2]
  have hBle : B.ncard ≤ T.ncard := by
    set T' : Set (Subgroup (locQuot Ω z)) := (fun R => R.map c.d.ψ) '' T with hT'
    have h1 : ∀ L ∈ B, locImg Ω z L ∈ T' := by
      rintro L ⟨hL, hLK⟩
      obtain ⟨R, hR, hLR⟩ := exists_root_of_neU3 c.hm c.hΩ c.hex c.hK c.hz c.hP1 c.hO3 c.d hL hLK
      exact ⟨R, hR, hLR.symm⟩
    have h2 : Set.InjOn (fun L => locImg Ω z L) B := fun L hL L' hL' h =>
      locImg_injOn3 c.hΩ c.hex c.hP1 c.hO3 hL.1 hL'.1 h
    calc B.ncard ≤ T'.ncard := Set.ncard_le_ncard_of_injOn _ h1 h2 (Set.toFinite _)
      _ ≤ T.ncard := Set.ncard_image_le (Set.toFinite _)
  have hAeq : A = B := by
    refine Set.eq_of_subset_of_ncard_le hAB ?_ (Set.toFinite _)
    rw [hA, hinj.ncard_image]
    exact hBle
  refine ⟨Θ, hker, hblk, hrange, fun R hR => ?_, fun L hL hLK => ?_⟩
  · exact hAB ⟨R, hR, rfl⟩
  · have hLB : L ∈ B := ⟨hL, hLK⟩
    rw [← hAeq] at hLB
    obtain ⟨R, hR, rfl⟩ := hLB
    exact ⟨R, hR, rfl⟩

end Existence

section Base

theorem TE6Chart3.isTE6Base {c : UCtx3 5 Ω K z} {nd : UNodes3 c}
    {Θ : Su (GaloisField 3 2) 3 1 6 →* G} (hΘ : TE6Chart3 c nd Θ) (F : SU6Frame 3 1 le_rfl) :
    IsTE6Base 3 1 le_rfl Ω K z ![F.R₁.map Θ, F.S₂.map Θ, F.S₃.map Θ] := by
  classical
  have hker := hΘ.ker_le
  have hgenV : F.R₁.map Θ ⊔ F.S₂.map Θ ⊔ F.S₃.map Θ = Θ.range := by
    rw [← Subgroup.map_sup, ← Subgroup.map_sup, F.gen, Subgroup.map_top]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact (hΘ.member F.R₁ F.R₁_mem).1.1
  · exact commutes_map Θ F.commutes_R₁_S₃
  · refine ⟨(Θ.comp F.ι₄).range, ?_, ?_⟩
    · refine ⟨Θ.comp F.ι₄, rfl, RouteD.ker_comp_le_center Θ hker F.ι₄ F.ι₄_injective, ?_, ?_,
        ?_, ?_⟩
      · refine RouteD.injective_comp_of_center Θ hker F.ι₄ (unitaryModel (frobQ 3 1)
          (frobQ_frobQ 3 1 le_rfl)).lb (F.ι₄_injective.comp (ulb_injective _ _)) F.R₁ ?_
          F.R₁_center
        rw [MonoidHom.range_comp, F.ι₄_long]
      · refine RouteD.injective_comp_of_center Θ hker F.ι₄ (unitaryModel (frobQ 3 1)
          (frobQ_frobQ 3 1 le_rfl)).sb (F.ι₄_injective.comp (usb_injective _ _)) F.S₂ ?_
          F.S₂_center
        rw [MonoidHom.range_comp, F.ι₄_short]
      · rw [← Subgroup.map_map, F.ι₄_long]
        rfl
      · rw [← Subgroup.map_map, F.ι₄_short]
        rfl
    · show (Θ.comp F.ι₄).range ≤ F.R₁.map Θ ⊔ F.S₂.map Θ ⊔ F.S₃.map Θ
      rw [hgenV]
      rintro _ ⟨x, rfl⟩
      exact ⟨F.ι₄ x, rfl⟩
  · refine ⟨(Θ.comp F.ι₃).range, Θ.comp F.ι₃, 1, rfl,
      RouteD.ker_comp_le_center Θ hker F.ι₃ F.ι₃_injective, Or.inr ⟨?_, ?_⟩⟩
    · have e : (MulAut.conj (1 : SL(3, GaloisField 3 (2 * 1)))⁻¹).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [e, Subgroup.map_id, ← Subgroup.map_map, F.ι₃_B12]
      rfl
    · have e : (MulAut.conj (1 : SL(3, GaloisField 3 (2 * 1)))⁻¹).toMonoidHom = MonoidHom.id _ := by
        ext x
        simp
      rw [e, Subgroup.map_id, ← Subgroup.map_map, F.ι₃_B23]
      rfl
  · intro L hL hLK
    obtain ⟨R, hR, rfl⟩ := hΘ.cover L hL hLK
    obtain ⟨i, hi⟩ := hR
    obtain ⟨i₁, hi₁⟩ := F.R₁_mem
    obtain ⟨g, hg⟩ := CFSG.ClassicalInvolution.ModelFacts.exists_conj_of_isLongRootSU2 hi hi₁
    refine ⟨Θ g, ?_, ?_⟩
    · show Θ g ∈ F.R₁.map Θ ⊔ F.S₂.map Θ ⊔ F.S₃.map Θ
      rw [hgenV]
      exact ⟨g, rfl⟩
    · show R.map Θ = conjSub (Θ g) (F.R₁.map Θ)
      rw [hg, conjSub_map]
      rfl

end Base

end CFSG.ClassicalInvolution.Q3.Q3E6T
