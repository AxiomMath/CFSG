module

public import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotSwapFactors
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotParam
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open Subgroup CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.SeitzReduction.UnitaryPilot (modelToG symm_mem_modelToG mem_modelToG)

namespace SwapNeighbourParam

section Factors

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G} {k : Fin n} (P : SwapNeighbourParam e t k)

@[expose] noncomputable def fstF (B : Subgroup (StatedSp n K)) : Subgroup G :=
  (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).map (P.Ψ.comp (MonoidHom.inl _ _))

@[expose] noncomputable def sndF (B : Subgroup (StatedSp n K)) : Subgroup G :=
  (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).map (P.Ψ.comp (MonoidHom.inr _ _))

theorem fstF_def (B : Subgroup (StatedSp n K)) :
    P.fstF B = (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).map
      (P.Ψ.comp (MonoidHom.inl _ _)) :=
  rfl

theorem sndF_def (B : Subgroup (StatedSp n K)) :
    P.sndF B = (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).map
      (P.Ψ.comp (MonoidHom.inr _ _)) :=
  rfl

theorem fstF_mono {A B : Subgroup (StatedSp n K)} (h : A ≤ B) : P.fstF A ≤ P.fstF B :=
  map_mono fun _ hx => mem_subgroupOf.2 (h (mem_subgroupOf.1 hx))

theorem sndF_mono {A B : Subgroup (StatedSp n K)} (h : A ≤ B) : P.sndF A ≤ P.sndF B :=
  map_mono fun _ hx => mem_subgroupOf.2 (h (mem_subgroupOf.1 hx))

theorem sndF_le_centralizer_fstF (B B' : Subgroup (StatedSp n K)) :
    P.sndF B' ≤ centralizer (P.fstF B : Set G) := by
  rintro _ ⟨y, -, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨x, -, rfl⟩
  exact (P.commute_inl_inr x y).eq

theorem fstF_le_centralizer_sndF (B B' : Subgroup (StatedSp n K)) :
    P.fstF B' ≤ centralizer (P.sndF B : Set G) :=
  le_centralizer_iff.1 (P.sndF_le_centralizer_fstF B' B)

theorem map_conj_fstF (B : Subgroup (StatedSp n K)) :
    (P.fstF B).map (MulAut.conj t).toMonoidHom = P.sndF B := by
  rw [fstF, sndF, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.swap x 1

theorem map_conj_sndF (B : Subgroup (StatedSp n K)) :
    (P.sndF B).map (MulAut.conj t).toMonoidHom = P.fstF B := by
  rw [fstF, sndF, Subgroup.map_map]
  congr 1
  ext x
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply,
    MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact P.swap 1 x

theorem map_prod_eq_fstF_sup_sndF (B : Subgroup (StatedSp n K)) :
    ((B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))).prod
      (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n))))).map P.Ψ = P.fstF B ⊔ P.sndF B := by
  apply le_antisymm
  · rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    have hxy : ((x, y) : spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n))) =
        (x, 1) * (1, y) := by
      ext <;> simp
    rw [hxy, map_mul]
    exact mul_mem (mem_sup_left ⟨x, hx, rfl⟩) (mem_sup_right ⟨y, hy, rfl⟩)
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨(x, 1), ⟨hx, one_mem _⟩, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨(1, y), ⟨one_mem _, hy⟩, rfl⟩

theorem mul_conj_mem_modelToG_of_mem_fstF {B : Subgroup (StatedSp n K)} {x : G}
    (hx : x ∈ P.fstF B) : x * (t * x * t⁻¹) ∈ modelToG e B := by
  obtain ⟨a, ha, rfl⟩ := hx
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply]
  rw [P.swap, ← map_mul, show ((a, 1) : spBlock K ({k}ᶜ : Finset (Fin n)) ×
    spBlock K ({k}ᶜ : Finset (Fin n))) * (1, a) = (a, a) by ext <;> simp, P.diag]
  exact symm_mem_modelToG e (mem_subgroupOf.1 ha)

theorem exists_mem_fstF_mul_conj_eq {B : Subgroup (StatedSp n K)}
    (hB : B ≤ spBlock K ({k}ᶜ : Finset (Fin n))) {y : G} (hy : y ∈ modelToG e B) :
    ∃ x ∈ P.fstF B, x * (t * x * t⁻¹) = y := by
  obtain ⟨z, hz, rfl⟩ := (mem_modelToG e).1 hy
  set b : spBlock K ({k}ᶜ : Finset (Fin n)) := ⟨z, hB hz⟩
  refine ⟨P.Ψ (b, 1), ⟨b, mem_subgroupOf.2 hz, rfl⟩, ?_⟩
  rw [P.swap, ← map_mul, show ((b, 1) : spBlock K ({k}ᶜ : Finset (Fin n)) ×
    spBlock K ({k}ᶜ : Finset (Fin n))) * (1, b) = (b, b) by ext <;> simp, P.diag]

theorem fstF_inf_sndF_eq_bot [CharP K 2] (A B : Subgroup (StatedSp n K)) :
    P.fstF A ⊓ P.sndF B = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨a, -, rfl⟩, ⟨b, -, hb⟩⟩
  have h := P.injective hb
  simp only [MonoidHom.inr_apply, MonoidHom.inl_apply, Prod.mk.injEq] at h
  rw [mem_bot, ← h.1]
  change P.Ψ ((1 : spBlock K ({k}ᶜ : Finset (Fin n))), (1 : spBlock K ({k}ᶜ : Finset (Fin n)))) = 1
  exact map_one P.Ψ


theorem fstF_sup {X Y : Subgroup (StatedSp n K)} (hX : X ≤ spBlock K ({k}ᶜ : Finset (Fin n)))
    (hY : Y ≤ spBlock K ({k}ᶜ : Finset (Fin n))) : P.fstF (X ⊔ Y) = P.fstF X ⊔ P.fstF Y := by
  rw [fstF, fstF, fstF, subgroupOf_sup hX hY, Subgroup.map_sup]

theorem sndF_sup {X Y : Subgroup (StatedSp n K)} (hX : X ≤ spBlock K ({k}ᶜ : Finset (Fin n)))
    (hY : Y ≤ spBlock K ({k}ᶜ : Finset (Fin n))) : P.sndF (X ⊔ Y) = P.sndF X ⊔ P.sndF Y := by
  rw [sndF, sndF, sndF, subgroupOf_sup hX hY, Subgroup.map_sup]

theorem ker_comp_inl_le_center [CharP K 2] :
    (P.Ψ.comp (MonoidHom.inl _ _)).ker ≤ center (spBlock K ({k}ᶜ : Finset (Fin n))) := by
  intro x hx
  have hx' : P.Ψ (x, 1) = P.Ψ 1 := by
    rw [map_one]
    exact hx
  have h := congrArg Prod.fst (P.injective hx')
  simp only [Prod.fst_one] at h
  rw [h]
  exact one_mem _

theorem fstF_sup_sndF_compl :
    P.fstF (spBlock K ({k}ᶜ : Finset (Fin n))) ⊔ P.sndF (spBlock K ({k}ᶜ : Finset (Fin n))) =
      neighbourCore e k := by
  rw [← map_prod_eq_fstF_sup_sndF, subgroupOf_self, Subgroup.top_prod_top,
    ← MonoidHom.range_eq_map, P.range_eq]

theorem fstF_sup_sndF_eq_planeCore [Finite G] [Finite K] (hK : 4 ≤ Nat.card K)
    {I : Finset (Fin n)} (hk : k ∉ I) :
    P.fstF (spBlock K I) ⊔ P.sndF (spBlock K I) = planeCore e I := by
  rw [← map_prod_eq_fstF_sup_sndF, P.planeCore_eq_map hK hk]

@[expose] noncomputable def prodSwap (K : Type) [Field K] {n : ℕ} (k : Fin n) :
    spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n)) ≃*
      spBlock K ({k}ᶜ : Finset (Fin n)) × spBlock K ({k}ᶜ : Finset (Fin n)) :=
  MulEquiv.prodComm

@[expose] noncomputable def flip [CharP K 2] : SwapNeighbourParam e t k :=
  SwapNeighbourParam.ofNormalized (P.Ψ.comp (prodSwap K k).toMonoidHom)
    (by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (prodSwap K k).surjective,
        ← MonoidHom.range_eq_map, P.range_eq])
    (by
      intro x hx
      have hx' : P.Ψ (prodSwap K k x) = P.Ψ 1 := by
        rw [map_one]
        exact hx
      have h1 : prodSwap K k x = prodSwap K k 1 := by
        rw [P.injective hx', map_one]
      rw [(prodSwap K k).injective h1]
      exact one_mem _)
    (fun x => by
      change P.Ψ (prodSwap K k (x, x)) = _
      exact P.diag x)
    (fun x y => by
      change t * P.Ψ (prodSwap K k (x, y)) * t⁻¹ = P.Ψ (prodSwap K k (y, x))
      exact P.swap y x)

theorem flip_Ψ_apply [CharP K 2] (x : spBlock K ({k}ᶜ : Finset (Fin n)) ×
    spBlock K ({k}ᶜ : Finset (Fin n))) : P.flip.Ψ x = P.Ψ (x.2, x.1) :=
  rfl

theorem flip_fstF [CharP K 2] (B : Subgroup (StatedSp n K)) : P.flip.fstF B = P.sndF B := by
  rw [fstF, sndF]
  rfl

theorem flip_sndF [CharP K 2] (B : Subgroup (StatedSp n K)) : P.flip.sndF B = P.fstF B := by
  rw [fstF, sndF]
  rfl

end Factors

end SwapNeighbourParam

section Dichotomy

variable {G : Type*} [Group G] {L : Subgroup G} {K : Type} [Field K] {n : ℕ}
  {e : L ≃* StatedSp n K} {t : G}

theorem isQuasisimple_spBlock_subgroupOf [Finite K] (hK : 4 ≤ Nat.card K) {I N : Finset (Fin n)}
    (hIN : I ⊆ N) (hI : I.Nonempty) :
    CFSG.Open.IsQuasisimple ((spBlock K I).subgroupOf (spBlock K N)) := by
  have hq : CFSG.IsQuasisimple ((spBlock K I).subgroupOf (spBlock K N)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((spBlockEquiv I).trans (Subgroup.subgroupOfEquivOfLe (spBlock_mono hIN)).symm)
      (CFSG.LieType.Universal.Symplectic.isQuasisimple I.card K (Finset.card_pos.2 hI)
        (Or.inl (Or.inr hK)))
  have := hq.1
  exact ⟨Group.IsPerfect.commutator_eq_top, hq.2.1⟩

theorem isSimpleGroup_statedSp_of_four_le [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) (hn : 1 ≤ n) :
    IsSimpleGroup (StatedSp n K) := by
  have : IsSimpleGroup (StatedSp n K ⧸ center (StatedSp n K)) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple n K hn (Or.inl (Or.inr hK))).2.1
  exact ((QuotientGroup.quotientMulEquivOfEq (center_statedSp_eq_bot n)).trans
    QuotientGroup.quotientBot).symm.isSimpleGroup

theorem SwapNeighbourParam.fstF_props [CharP K 2] {k : Fin n} (P : SwapNeighbourParam e t k)
    {B : Subgroup (StatedSp n K)}
    (hB : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n))))) :
    ⁅P.fstF B, P.fstF B⁆ = P.fstF B ∧ P.fstF B ≠ ⊥ ∧
      ∀ M : Subgroup G, M ≤ P.fstF B → P.fstF B ≤ normalizer (M : Set G) →
        M ≤ centralizer (P.fstF B : Set G) ∨ M = P.fstF B :=
  ⟨UnitaryPilot.commutator_map_eq_of_isQuasisimple hB _,
    UnitaryPilot.map_ne_bot_of_isQuasisimple hB _ P.ker_comp_inl_le_center,
    UnitaryPilot.dichotomy_map_of_isQuasisimple hB _⟩

theorem SwapNeighbourParam.sndF_props [CharP K 2] {k : Fin n} (P : SwapNeighbourParam e t k)
    {B : Subgroup (StatedSp n K)}
    (hB : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n))))) :
    ⁅P.sndF B, P.sndF B⁆ = P.sndF B ∧ P.sndF B ≠ ⊥ ∧
      ∀ M : Subgroup G, M ≤ P.sndF B → P.sndF B ≤ normalizer (M : Set G) →
        M ≤ centralizer (P.sndF B : Set G) ∨ M = P.sndF B := by
  rw [← P.flip_fstF]
  exact P.flip.fstF_props hB

theorem SwapNeighbourParam.fstF_eq_or_eq [CharP K 2] {k k' : Fin n} (P : SwapNeighbourParam e t k)
    (Q : SwapNeighbourParam e t k') {B : Subgroup (StatedSp n K)}
    (hBP : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))))
    (hBQ : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k'}ᶜ : Finset (Fin n)))))
    (hM : P.fstF B ⊔ P.sndF B = Q.fstF B ⊔ Q.sndF B) :
    Q.fstF B = P.fstF B ∨ Q.fstF B = P.sndF B := by
  obtain ⟨-, -, hn₁⟩ := P.fstF_props hBP
  obtain ⟨-, -, hn₂⟩ := P.sndF_props hBP
  obtain ⟨hperf, hbot, hnN⟩ := Q.fstF_props hBQ
  refine F4Pilot.eq_or_eq_of_perfect_of_le_sup (P.sndF_le_centralizer_fstF B B) hn₁ hn₂ hperf
    hbot hnN ?_ ?_
  · rw [hM]
    exact le_sup_left
  · rw [hM]
    exact sup_le le_normalizer
      ((Q.sndF_le_centralizer_fstF B B).trans (centralizer_le_normalizer _))

theorem SwapNeighbourParam.fstF_eq_of_le_of_fstF_eq [CharP K 2] {k k' : Fin n}
    (P : SwapNeighbourParam e t k) (Q : SwapNeighbourParam e t k')
    {A B : Subgroup (StatedSp n K)} (hBA : B ≤ A)
    (hBP : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))))
    (hBQ : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k'}ᶜ : Finset (Fin n)))))
    (hM : P.fstF B ⊔ P.sndF B = Q.fstF B ⊔ Q.sndF B) (hA : Q.fstF A = P.fstF A) :
    Q.fstF B = P.fstF B := by
  rcases P.fstF_eq_or_eq Q hBP hBQ hM with h | h
  · exact h
  · exfalso
    obtain ⟨-, hbot, -⟩ := Q.fstF_props hBQ
    apply hbot
    rw [eq_bot_iff]
    exact (le_inf ((Q.fstF_mono hBA).trans hA.le) h.le).trans (P.fstF_inf_sndF_eq_bot A B).le

theorem SwapNeighbourParam.fstF_eq_sndF_of_le_of_fstF_eq_sndF [CharP K 2] {k k' : Fin n}
    (P : SwapNeighbourParam e t k) (Q : SwapNeighbourParam e t k')
    {A B : Subgroup (StatedSp n K)} (hBA : B ≤ A)
    (hBP : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k}ᶜ : Finset (Fin n)))))
    (hBQ : CFSG.Open.IsQuasisimple (B.subgroupOf (spBlock K ({k'}ᶜ : Finset (Fin n)))))
    (hM : P.fstF B ⊔ P.sndF B = Q.fstF B ⊔ Q.sndF B) (hA : Q.fstF A = P.sndF A) :
    Q.fstF B = P.sndF B := by
  rcases P.fstF_eq_or_eq Q hBP hBQ hM with h | h
  · exfalso
    obtain ⟨-, hbot, -⟩ := Q.fstF_props hBQ
    apply hbot
    rw [eq_bot_iff]
    exact (le_inf h.le ((Q.fstF_mono hBA).trans hA.le)).trans (P.fstF_inf_sndF_eq_bot B A).le
  · exact h

end Dichotomy

end CFSG.SeitzReduction.SymplecticPilot
