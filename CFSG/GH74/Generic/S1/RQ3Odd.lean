module

public import CFSG.GH74.Generic.S1.SymLayer

public section

namespace CFSG.GH74.Generic.S1

open CFSG CFSG.GH74 CFSG.GH74.L5U5 Subgroup CFSG.GH74.Generic

section OddGen

variable {X Y : Type} [Group X] [Group Y]

theorem oddGenerated_map (f : X →* Y) {P : Subgroup X} (hP : OddGenerated P) :
    OddGenerated (P.map f) := by
  unfold OddGenerated at hP ⊢
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1
  · calc P.map f = (Subgroup.closure {g | g ∈ P ∧ Odd (orderOf g)}).map f := by rw [hP]
      _ = Subgroup.closure (f '' {g | g ∈ P ∧ Odd (orderOf g)}) := MonoidHom.map_closure f _
      _ ≤ _ := Subgroup.closure_mono (by
          rintro _ ⟨g, ⟨hgP, hgodd⟩, rfl⟩
          exact ⟨Subgroup.mem_map_of_mem f hgP, Odd.of_dvd_nat hgodd (orderOf_map_dvd f g)⟩)

theorem oddGenerated_comap {f : X →* Y} (hf : Function.Injective f) {H : Subgroup Y}
    (hH : OddGenerated H) (hle : H ≤ f.range) : OddGenerated (H.comap f) := by
  unfold OddGenerated at hH ⊢
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1
  · have hmap : (H.comap f).map f = H := by
      rw [Subgroup.map_comap_eq]
      exact inf_eq_right.2 hle
    rw [← Subgroup.map_le_map_iff_of_injective hf, hmap]
    calc H = Subgroup.closure {g | g ∈ H ∧ Odd (orderOf g)} := hH.symm
      _ ≤ (Subgroup.closure {g | g ∈ H.comap f ∧ Odd (orderOf g)}).map f := by
          refine (Subgroup.closure_le _).2 ?_
          rintro g ⟨hgH, hgodd⟩
          obtain ⟨s, rfl⟩ := hle hgH
          refine ⟨s, Subgroup.subset_closure ⟨hgH, ?_⟩, rfl⟩
          rwa [orderOf_injective f hf s] at hgodd

end OddGen

section OddRes

variable {G : Type} [Group G]

@[expose] noncomputable def oddRes (T : Set G) : Subgroup G :=
  Subgroup.closure {g : G | g ∈ centralizer T ∧ Odd (orderOf g)}

theorem oddRes_le (T : Set G) : oddRes T ≤ centralizer T :=
  (Subgroup.closure_le _).2 fun _ hg => hg.1

theorem le_oddRes {T : Set G} {P : Subgroup G} (hP : P ≤ centralizer T) (hodd : OddGenerated P) :
    P ≤ oddRes T := by
  calc P = Subgroup.closure {g | g ∈ P ∧ Odd (orderOf g)} := hodd.symm
    _ ≤ oddRes T := Subgroup.closure_mono fun g hg => ⟨hP hg.1, hg.2⟩

theorem oddRes_oddGenerated (T : Set G) : OddGenerated (oddRes T) := by
  unfold OddGenerated
  apply le_antisymm
  · exact (Subgroup.closure_le _).2 fun g hg => hg.1
  · exact Subgroup.closure_mono fun g hg => ⟨Subgroup.subset_closure hg, hg.2⟩

end OddRes

section Blocks

variable (F : Type) [Field F]

structure OddBlockOps (S : Subgroup (GL (Fin 4) F)) where
  blk : Fin 4 → Fin 4 → Subgroup ↥S
  oddGen : ∀ a b, a ≠ b → OddGenerated (blk a b)
  commute : ∀ a b c d, a ≠ b → c ≠ d → a ≠ c → a ≠ d → b ≠ c → b ≠ d →
    ∀ g ∈ blk a b, ∀ h ∈ blk c d, g * h = h * g
  comm_refl : ∀ a b c, a ≠ b → c ≠ a → c ≠ b → ∀ g ∈ blk a b,
    (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F)
  odd_le : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ P : Subgroup ↥S, (∀ g ∈ P, (g : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (g : GL (Fin 4) F) ∧
      (g : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (g : GL (Fin 4) F)) →
      OddGenerated P → P ≤ blk a b

variable {F} {G : Type} [Group G] {S : Subgroup (GL (Fin 4) F)}

structure LayerData3 (y : G) (S : Subgroup (GL (Fin 4) F)) extends LayerData y S where
  inj : Function.Injective (proj y)
  odd_le : ∀ P : Subgroup (CentralizerBar y), OddGenerated P → P ≤ K

namespace LayerData3

variable {y : G} (D : LayerData3 y S) [Finite G]

omit [Finite G] in
theorem comap_perfect : ⁅D.K.comap (proj y), D.K.comap (proj y)⁆ = D.K.comap (proj y) := by
  set M : Subgroup ↥(centralizer ({y} : Set G)) := D.K.comap (proj y) with hM
  have hsurj : Function.Surjective (proj y) := fun b => QuotientGroup.mk_surjective b
  have hMK : M.map (proj y) = D.K := Subgroup.map_comap_eq_self_of_surjective hsurj _
  have hcomm : (⁅M, M⁆).map (proj y) = D.K := by
    rw [Subgroup.map_commutator, hMK]
    exact D.perf
  apply le_antisymm
  · refine Subgroup.commutator_le.2 fun g hg h hh => ?_
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem hg hh) (M.inv_mem hg)) (M.inv_mem hh)
  · intro m hm
    have hmK : proj y m ∈ D.K := hm
    rw [← hcomm] at hmK
    obtain ⟨m', hm', hmm'⟩ := hmK
    have : m' = m := D.inj hmm'
    rw [← this]
    exact hm'

theorem le_range_ι_odd {R : Subgroup G} (hR : OddGenerated R) (hRy : R ≤ centralizer ({y} : Set G)) :
    R ≤ D.ι.range := by
  have hRc : OddGenerated (R.subgroupOf (centralizer ({y} : Set G))) := by
    refine oddGenerated_comap (centralizer ({y} : Set G)).subtype_injective hR ?_
    rw [Subgroup.range_subtype]
    exact hRy
  have hle_K := D.odd_le _ (oddGenerated_map (proj y) hRc)
  have hRc_le : R.subgroupOf (centralizer ({y} : Set G)) ≤ D.K.comap (proj y) :=
    fun r hr => hle_K ⟨r, hr, rfl⟩
  have hRc_liftL : R.subgroupOf (centralizer ({y} : Set G)) ≤ liftL y D.K :=
    hRc_le.trans (perfect_le_liftL le_rfl D.comap_perfect)
  intro g hg
  have hgc : (⟨g, hRy hg⟩ : ↥(centralizer ({y} : Set G))) ∈
      R.subgroupOf (centralizer ({y} : Set G)) := hg
  have hgl := hRc_liftL hgc
  refine ⟨D.liftIso.symm ⟨_, hgl⟩, ?_⟩
  change (((D.liftIso (D.liftIso.symm ⟨_, hgl⟩) : ↥(liftL y D.K)) :
    ↥(centralizer ({y} : Set G))) : G) = g
  rw [MulEquiv.apply_symm_apply]

end LayerData3

theorem oddRes_eq_map (ops : OddBlockOps F S) [Finite G] {y : G} (D : LayerData3 y S) (w : Fin 4 → G)
    (hw : ∀ j, w j ∈ centralizer ({y} : Set G))
    (hact : ∀ j, ActsAsReflOn D.iso (barOf (hw j)) (reflDiag F j))
    {a b c d : Fin 4} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    oddRes ({y, w c, w d} : Set G) = (ops.blk a b).map D.ι := by
  apply le_antisymm
  ·
    have hRodd := oddRes_oddGenerated ({y, w c, w d} : Set G)
    have hRle := oddRes_le ({y, w c, w d} : Set G)
    have hRy : oddRes ({y, w c, w d} : Set G) ≤ centralizer ({y} : Set G) :=
      le_trans hRle (Subgroup.centralizer_le (by simp))
    have hrange := D.le_range_ι_odd hRodd hRy
    set P : Subgroup ↥S := (oddRes ({y, w c, w d} : Set G)).comap D.ι with hP
    have hmapP : P.map D.ι = oddRes ({y, w c, w d} : Set G) := by
      rw [hP, Subgroup.map_comap_eq]
      exact inf_eq_right.2 hrange
    have hPodd : OddGenerated P := oddGenerated_comap D.ι_injective hRodd hrange
    have hPcomm : ∀ t ∈ P, (t : GL (Fin 4) F) * reflDiag F c = reflDiag F c * (t : GL (Fin 4) F) ∧
        (t : GL (Fin 4) F) * reflDiag F d = reflDiag F d * (t : GL (Fin 4) F) := by
      intro t ht
      have ht' : D.ι t ∈ centralizer ({y, w c, w d} : Set G) := hRle ht
      refine ⟨D.comm_of_ι_comm (hw c) (hact c) ?_, D.comm_of_ι_comm (hw d) (hact d) ?_⟩
      · exact (mem_centralizer_iff.1 ht' (w c) (by simp)).symm
      · exact (mem_centralizer_iff.1 ht' (w d) (by simp)).symm
    have hPle : P ≤ ops.blk a b := ops.odd_le a b c d hab hac had hbc hbd hcd P hPcomm hPodd
    rw [← hmapP]
    exact Subgroup.map_mono hPle
  ·
    have hodd : OddGenerated ((ops.blk a b).map D.ι) := oddGenerated_map D.ι (ops.oddGen a b hab)
    refine le_oddRes ?_ hodd
    rintro _ ⟨s, hs, rfl⟩
    rw [mem_centralizer_iff]
    intro h hh
    rcases hh with rfl | rfl | rfl
    · exact (D.ι_comm_self s).symm
    · exact (D.ι_comm_of (hw c) (hact c) (ops.comm_refl a b c hab hac.symm hbc.symm s hs)).symm
    · exact (D.ι_comm_of (hw d) (hact d) (ops.comm_refl a b d hab had.symm hbd.symm s hs)).symm

end Blocks

end CFSG.GH74.Generic.S1
