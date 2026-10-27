module

public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaLevi
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaPlus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaNormal
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotKindOmegaTorus

public section

namespace CFSG.SeitzReduction.SymplecticPilot

open CFSG Subgroup Matrix
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin (perfectCore)
open CFSG.ClassicalInvolution.WeakCT (B12 B23)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (fieldSp)
open CFSG.SeitzReduction.UnitaryPilot (modelToG)
open CFSG.SeitzReduction.OmegaPilot (diagOmega omegaBlock siegelBlockGL flipGL siegelNode)
open scoped MatrixGroups

section Generic

variable {X Y : Type*} [Group X] [Group Y]

theorem kOmega_map_subtype_subgroupOf {M H : Subgroup X} (h : H ≤ M) :
    (H.subgroupOf M).map M.subtype = H := by
  rw [subgroupOf_map_subtype, inf_eq_left.mpr h]

theorem kOmega_map_subgroupOf_le_centralizer {M H₁ H₂ : Subgroup X}
    (hc : ∀ a ∈ H₁, ∀ b ∈ H₂, Commute a b) (φ : M →* Y) :
    (H₁.subgroupOf M).map φ ≤ centralizer ((H₂.subgroupOf M).map φ : Set Y) := by
  rintro _ ⟨a, ha, rfl⟩
  rw [mem_centralizer_iff]
  rintro _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hc a (mem_subgroupOf.1 ha) b (mem_subgroupOf.1 hb)).eq.symm

theorem kOmega_map_codRestrict {Z : Type*} [Group Z] (θ : Z →* X) {M : Subgroup X}
    (hθ : ∀ z, θ z ∈ M) (H : Subgroup Z) :
    H.map (θ.codRestrict M hθ) = (H.map θ).subgroupOf M := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact mem_subgroupOf.2 ⟨z, hz, rfl⟩
  · intro hx
    obtain ⟨z, hz, hzx⟩ := mem_subgroupOf.1 hx
    exact ⟨z, hz, Subtype.ext hzx⟩

theorem kOmega_exists_theta_map {F : Type} [Field F] {θ₀ : SL(3, F) →* X}
    (hθ₀ : θ₀.ker ≤ center SL(3, F)) {M N₁ N₂ : Subgroup X} (h₁ : (B12 F).map θ₀ = N₁)
    (h₂ : (B23 F).map θ₀ = N₂) (hN₁ : N₁ ≤ M) (hN₂ : N₂ ≤ M) {Ψ : M →* Y}
    (hΨ : Function.Injective Ψ) :
    ∃ θ : SL(3, F) →* Y, θ.ker ≤ center SL(3, F) ∧ (B12 F).map θ = (N₁.subgroupOf M).map Ψ ∧
      (B23 F).map θ = (N₂.subgroupOf M).map Ψ := by
  have hM : ∀ z, θ₀ z ∈ M := by
    intro z
    have hz : θ₀ z ∈ θ₀.range := ⟨z, rfl⟩
    rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.WeakCT.B12_sup_B23, Subgroup.map_sup,
      h₁, h₂] at hz
    exact sup_le hN₁ hN₂ hz
  refine ⟨Ψ.comp (θ₀.codRestrict M hM), ?_, ?_, ?_⟩
  · rw [MonoidHom.ker_comp_of_injective _ _ hΨ, MonoidHom.ker_codRestrict]
    exact hθ₀
  · rw [← Subgroup.map_map, kOmega_map_codRestrict, h₁]
  · rw [← Subgroup.map_map, kOmega_map_codRestrict, h₂]

end Generic

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

theorem kOmega_pieceCore_short_eq_map {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) (k : Fin (r + 1))
    (Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* neighbourCore e k) (σ : K ≃+* K)
    (hΦ : ∀ x : StatedSp r K, ((Φ (kOmegaIota hr hr3 hKc hf x) : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G))
    {j : Fin (r + 1)} (hj : j.val + 1 < r + 1) {a b : Fin r} (ha : k.succAbove a = j)
    (hb : k.succAbove b = ⟨j.val + 1, hj⟩) :
    pieceCore e ({j} : Finset (Fin (r + 1))) =
      ((siegelBlockGL K {a.castSucc, b.castSucc}).subgroupOf
        (StatedOmega (StatedQuadPlus (r + 1) K))).map
          ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hab : a ≠ b := fun h => by
    have := congrArg Fin.val (ha.symm.trans ((congrArg k.succAbove h).trans hb))
    simp at this
  have hkj : k ≠ j := fun h => Fin.succAbove_ne k a (ha.trans h.symm)
  have hkj1 : k ≠ ⟨j.val + 1, hj⟩ := fun h => Fin.succAbove_ne k b (hb.trans h.symm)
  have hk : k ∉ spSupport ({j} : Finset (Fin (r + 1))) := by
    rw [mem_spSupport]
    rintro (h | ⟨j', hj', h⟩)
    · exact hkj (Finset.mem_singleton.1 h)
    · rw [Finset.mem_singleton.1 hj'] at h
      exact hkj1 (Fin.ext h.symm)
  have hP : ∀ t : Fin r → Kˣ, t ∈ kOmegaTorusParam (K := K) k {j} ↔ t a = t b := by
    intro t
    have e1 : kOmegaInsert K k t j = t a := by
      rw [kOmegaInsert_apply, ← ha]
      exact Fin.insertNth_apply_succAbove (α := fun _ => Kˣ) k 1 t a
    have e2 : kOmegaInsert K k t ⟨j.val + 1, hj⟩ = t b := by
      rw [kOmegaInsert_apply, ← hb]
      exact Fin.insertNth_apply_succAbove (α := fun _ => Kˣ) k 1 t b
    rw [mem_kOmegaTorusParam, mem_leviTorusParam]
    constructor
    · intro h
      have h2 := (h j (Finset.mem_singleton_self _)).1 hj
      rwa [e1, e2] at h2
    · intro h j' hj'
      rw [Finset.mem_singleton] at hj'
      subst hj'
      refine ⟨fun _ => ?_, fun h' => absurd h' (by omega)⟩
      rw [e1, e2, h]
  rw [kOmega_pieceCore_eq_map hKc hf hr hr3 e k Φ σ hΦ hk]
  congr 1
  apply Subgroup.map_injective (StatedOmega (StatedQuadPlus (r + 1) K)).subtype_injective
  rw [kOmega_map_subtype_perfectCore_centralizer, perfectCore_kOmega_short hK4 hab hP,
    kOmega_map_subtype_subgroupOf (OmegaPilot.siegelBlockGL_le_statedOmega hK4
      (by rw [Finset.card_pair (fun h => hab (Fin.castSucc_injective r h))]))]

theorem kOmega_pieceCore_long_eq_map {r f : ℕ} (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (hr : 2 ≤ r)
    (hr3 : 3 ≤ r) (e : L ≃* StatedSp (r + 1) K) (k : Fin (r + 1))
    (Φ : StatedOmega (StatedQuadPlus (r + 1) K) ≃* neighbourCore e k) (σ : K ≃+* K)
    (hΦ : ∀ x : StatedSp r K, ((Φ (kOmegaIota hr hr3 hKc hf x) : neighbourCore e k) : G) =
      ((e.symm (complSpEquiv k (fieldSp r K σ x)) : L) : G))
    {c : Fin r} (hc : k.succAbove c = Fin.last r) :
    pieceCore e ({Fin.last r} : Finset (Fin (r + 1))) =
      ((perfectCore (omegaBlock K {c.castSucc, Fin.last r})).subgroupOf
        (StatedOmega (StatedQuadPlus (r + 1) K))).map
          ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hkl : k ≠ Fin.last r := fun h => Fin.succAbove_ne k c (hc.trans h.symm)
  have hk : k ∉ spSupport ({Fin.last r} : Finset (Fin (r + 1))) := by
    rw [mem_spSupport]
    rintro (h | ⟨j', hj', h⟩)
    · exact hkl (Finset.mem_singleton.1 h)
    · rw [Finset.mem_singleton.1 hj', Fin.val_last] at h
      have := k.isLt
      omega
  have hP : ∀ t : Fin r → Kˣ, t ∈ kOmegaTorusParam (K := K) k {Fin.last r} ↔ t c = 1 := by
    intro t
    have hins : kOmegaInsert K k t (Fin.last r) = t c := by
      rw [kOmegaInsert_apply, ← hc]
      exact Fin.insertNth_apply_succAbove (α := fun _ => Kˣ) k 1 t c
    rw [mem_kOmegaTorusParam, mem_leviTorusParam]
    constructor
    · intro h
      have h3 := (h (Fin.last r) (Finset.mem_singleton_self _)).2 (by rw [Fin.val_last])
      rwa [hins] at h3
    · intro h j' hj'
      rw [Finset.mem_singleton] at hj'
      subst hj'
      refine ⟨fun h' => absurd h' (by rw [Fin.val_last]; omega), fun _ => ?_⟩
      rw [hins, h]
  rw [kOmega_pieceCore_eq_map hKc hf hr hr3 e k Φ σ hΦ hk]
  congr 1
  apply Subgroup.map_injective (StatedOmega (StatedQuadPlus (r + 1) K)).subtype_injective
  have hle : perfectCore (omegaBlock K {c.castSucc, Fin.last r}) ≤
      StatedOmega (StatedQuadPlus (r + 1) K) :=
    (CFSG.Quasithin.perfectCore_le _).trans inf_le_left
  rw [kOmega_map_subtype_perfectCore_centralizer, perfectCore_kOmega_long hK4 hP]
  exact (kOmega_map_subtype_subgroupOf hle).symm

end Pieces

section Assembly

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [Finite K]
  [CharP K 2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem kOmega_card_map_subgroupOf {X Y : Type*} [Group X] [Group Y] {M H : Subgroup X} (h : H ≤ M)
    {φ : M →* Y} (hφ : Function.Injective φ) : Nat.card ((H.subgroupOf M).map φ) = Nat.card H := by
  rw [Subgroup.card_map_of_injective hφ]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

omit [Finite G] [Finite K] [CharP K 2] in
theorem kOmega_card_simpleRootSL2 {n : ℕ} (j : Fin n) :
    Nat.card (simpleRootSL2 K j) = Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [simpleRootSL2, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    (simpleRootHom_injective j), Subgroup.card_top]

@[expose] def KOmegaParams {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (e : L ≃* StatedSp (m + 2) K) : Prop :=
  ∀ k : Fin (m + 2), ∃ (Φ : StatedOmega (StatedQuadPlus (m + 2) K) ≃* neighbourCore e k)
    (σ : K ≃+* K), ∀ x : StatedSp (m + 1) K,
      ((Φ (kOmegaIota (r := m + 1) (by omega) (by omega) hKc hf x) : neighbourCore e k) : G) =
        ((e.symm (complSpEquiv k (fieldSp (m + 1) K σ x)) : L) : G)

theorem kOmega_pieceCore_short_eq_modelToG {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K) (hpar : KOmegaParams hm hKc hf e)
    (j : Fin (m + 2)) (hj : j.val + 1 < m + 2) :
    pieceCore e ({j} : Finset (Fin (m + 2))) = modelToG e (simpleRootSL2 K j) := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hcard : ∀ (k : Fin (m + 2)) (a b : Fin (m + 1)), k.succAbove a = j →
      k.succAbove b = ⟨j.val + 1, hj⟩ →
      Nat.card (pieceCore e ({j} : Finset (Fin (m + 2)))) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    intro k a b ha hb
    obtain ⟨Φ, σ, hΦ⟩ := hpar k
    have hab : a ≠ b := fun h => by
      have := congrArg Fin.val (ha.symm.trans ((congrArg k.succAbove h).trans hb))
      simp at this
    have hI : ({a.castSucc, b.castSucc} : Finset (Fin (m + 2))).card = 2 :=
      Finset.card_pair (fun h => hab (Fin.castSucc_injective _ h))
    rw [kOmega_pieceCore_short_eq_map (r := m + 1) hKc hf (by omega) (by omega) e k Φ σ hΦ hj ha hb,
      kOmega_card_map_subgroupOf (OmegaPilot.siegelBlockGL_le_statedOmega hK4 (by rw [hI]))
        ((neighbourCore e k).subtype_injective.comp Φ.injective),
      OmegaPilot.natCard_siegelBlockGL, hI]
  have hc : Nat.card (pieceCore e ({j} : Finset (Fin (m + 2)))) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
    by_cases hj0 : j.val = 0
    · refine hcard (Fin.last (m + 1)) ⟨0, by omega⟩ ⟨1, by omega⟩ ?_ ?_
      · rw [Fin.succAbove_last]
        exact Fin.ext (by simp [hj0])
      · rw [Fin.succAbove_last]
        exact Fin.ext (by simp [hj0])
    · refine hcard 0 ⟨j.val - 1, by omega⟩ ⟨j.val, by omega⟩ ?_ ?_
      · rw [Fin.succAbove_zero]
        exact Fin.ext (by simp; omega)
      · rw [Fin.succAbove_zero]
        exact Fin.ext (by simp)
  refine (Subgroup.eq_of_le_of_card_ge
    (modelToG_simpleRootSL2_le_pieceCore e hK4 (Finset.mem_singleton_self j)) ?_).symm
  rw [hc, UnitaryPilot.card_modelToG, kOmega_card_simpleRootSL2]

omit [Finite G] [Finite K] [CharP K 2] in
theorem kOmega_siegelNode_fork {m : ℕ} (hm : 2 ≤ m) :
    siegelNode K (m + 2) ⟨m - 1, by omega⟩ = siegelBlockGL K {⟨m - 1, by omega⟩, ⟨m, by omega⟩} ∧
      siegelNode K (m + 2) ⟨m, by omega⟩ = siegelBlockGL K {⟨m, by omega⟩, Fin.last (m + 1)} ∧
      siegelNode K (m + 2) (Fin.last (m + 1)) =
        (siegelBlockGL K {⟨m, by omega⟩, Fin.last (m + 1)}).map
          (MulAut.conj (flipGL K {Fin.last (m + 1)})).toMonoidHom := by
  have hflip : ∀ j : Fin (m + 2), j.val + 1 < m + 2 → OmegaPilot.plusNodeFlip (m + 2) j = ∅ := by
    intro j hj
    ext x
    rw [OmegaPilot.mem_plusNodeFlip]
    simp only [Finset.notMem_empty, iff_false, not_and]
    intro h
    omega
  refine ⟨?_, ?_, ?_⟩
  · rw [siegelNode, hflip _ (by simp only; omega), OmegaPilot.flipGL_empty,
      OmegaPilot.map_conj_one_eq]
    congr 1
    ext x
    rw [OmegaPilot.mem_plusNodeSet, Finset.mem_insert, Finset.mem_singleton]
    simp only [Fin.ext_iff]
    have := x.isLt
    omega
  · rw [siegelNode, hflip _ (by simp only; omega), OmegaPilot.flipGL_empty,
      OmegaPilot.map_conj_one_eq]
    congr 1
    ext x
    rw [OmegaPilot.mem_plusNodeSet, Finset.mem_insert, Finset.mem_singleton]
    simp only [Fin.ext_iff, Fin.val_last]
    have := x.isLt
    omega
  · have h1 : OmegaPilot.plusNodeSet (m + 2) (Fin.last (m + 1)) =
        {⟨m, by omega⟩, Fin.last (m + 1)} := by
      ext x
      rw [OmegaPilot.mem_plusNodeSet, Finset.mem_insert, Finset.mem_singleton]
      simp only [Fin.ext_iff, Fin.val_last, true_and]
      have := x.isLt
      omega
    have h2 : OmegaPilot.plusNodeFlip (m + 2) (Fin.last (m + 1)) = {Fin.last (m + 1)} := by
      ext x
      rw [OmegaPilot.mem_plusNodeFlip, Finset.mem_singleton, Fin.ext_iff, Fin.val_last]
      constructor
      · rintro ⟨-, h⟩
        omega
      · intro h
        omega
    rw [siegelNode, h1, h2]

theorem spOmegaPlusPieces_of_params {m f : ℕ} (hm : 2 ≤ m) (hKc : Nat.card K = 2 ^ f)
    (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K) (hpar : KOmegaParams hm hKc hf e) :
    SpOmegaPlusPieces e := by
  have hK4 : 4 ≤ Nat.card K := (LinearPilot.four_le_card_iff_two_le hKc).2 hf
  have hshort := kOmega_pieceCore_short_eq_modelToG hm hKc hf e hpar
  set M := StatedOmega (StatedQuadPlus (m + 2) K) with hMdef
  have hlong : ∀ k : Fin (m + 2), k ≠ Fin.last (m + 1) →
      ∀ (Φ : M ≃* neighbourCore e k) (σ : K ≃+* K), (∀ x : StatedSp (m + 1) K,
        ((Φ (kOmegaIota (r := m + 1) (by omega) (by omega) hKc hf x) : neighbourCore e k) : G) =
          ((e.symm (complSpEquiv k (fieldSp (m + 1) K σ x)) : L) : G)) →
      ∃ c : Fin (m + 1), k.succAbove c = Fin.last (m + 1) ∧
        pieceCore e ({Fin.last (m + 1)} : Finset (Fin (m + 2))) =
          ((perfectCore (omegaBlock K {c.castSucc, Fin.last (m + 1)})).subgroupOf M).map
            ((neighbourCore e k).subtype.comp Φ.toMonoidHom) := by
    intro k hk Φ σ hΦ
    obtain ⟨c, hc⟩ := Fin.exists_succAbove_eq hk.symm
    exact ⟨c, hc, kOmega_pieceCore_long_eq_map (r := m + 1) hKc hf (by omega) (by omega) e k Φ σ
      hΦ hc⟩
  obtain ⟨Φ₀, σ₀, hΦ₀⟩ := hpar 0
  set Ψ₀ : M →* G := (neighbourCore e 0).subtype.comp Φ₀.toMonoidHom with hΨ₀
  have hΨ₀inj : Function.Injective Ψ₀ :=
    (neighbourCore e 0).subtype_injective.comp Φ₀.injective
  set i₀ : Fin (m + 2) := ⟨m, by omega⟩ with hi₀
  have hi₀l : i₀ ≠ Fin.last (m + 1) := fun h => by
    have := congrArg Fin.val h
    simp [hi₀] at this
  obtain ⟨c₀, hc₀, hlast₀⟩ := hlong 0 (fun h => by
    have := congrArg Fin.val h
    simp at this) Φ₀ σ₀ hΦ₀
  have hc₀' : c₀.castSucc = i₀ := by
    have h1 : (0 : Fin (m + 2)).succAbove c₀ = c₀.succ := by rw [Fin.succAbove_zero]
    rw [h1] at hc₀
    apply Fin.ext
    have := congrArg Fin.val hc₀
    simp only [Fin.val_succ, Fin.val_last] at this
    simp [hi₀]
    omega
  rw [hc₀', kOmega_perfectCore_omegaBlock_pair_eq_sup hK4 hi₀l] at hlast₀
  set SA := siegelBlockGL K {i₀, Fin.last (m + 1)} with hSA
  set SB := SA.map (MulAut.conj (flipGL K {Fin.last (m + 1)})).toMonoidHom with hSB
  have hI : ({i₀, Fin.last (m + 1)} : Finset (Fin (m + 2))).card = 2 := Finset.card_pair hi₀l
  have hSAM : SA ≤ M := OmegaPilot.siegelBlockGL_le_statedOmega hK4 (by rw [hI])
  have hSBM : SB ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.1 (OmegaPilot.flipGL_mem_normalizer (F := K) {Fin.last (m + 1)}) x).1
      (hSAM hx)
  have hPB : ({i₀, Fin.last (m + 1)} : Finset (Fin (m + 2))) ∩ {Fin.last (m + 1)} =
      {Fin.last (m + 1)} := by
    rw [Finset.inter_eq_right]
    simp
  have hSAB : ∀ a ∈ SA, ∀ b ∈ SB, Commute a b := fun a ha b hb =>
    OmegaPilot.commute_siegelBlockGL_flip hK4 hI hPB ha hb
  have hjm : (Fin.last m).castSucc.val + 1 < m + 2 := by simp
  have hpm : modelToG e (simpleRootSL2 K (Fin.last m).castSucc) =
      ((siegelBlockGL K {⟨m - 1, by omega⟩, ⟨m, by omega⟩}).subgroupOf M).map Ψ₀ := by
    rw [← hshort _ hjm, kOmega_pieceCore_short_eq_map (r := m + 1) hKc hf (by omega) (by omega) e 0
      Φ₀ σ₀ hΦ₀ hjm (a := ⟨m - 1, by omega⟩) (b := ⟨m, by omega⟩)
      (by rw [Fin.succAbove_zero]; exact Fin.ext (by simp; omega))
      (by rw [Fin.succAbove_zero]; exact Fin.ext (by simp))]
    rfl
  obtain ⟨hn1, hn2, hn3⟩ := kOmega_siegelNode_fork (K := K) hm
  have hle : ∀ j, siegelNode K (m + 2) j ≤ M := fun j =>
    OmegaPilot.siegelNode_le_statedOmega hK4 (by omega) j
  refine ⟨hshort, (SA.subgroupOf M).map Ψ₀, (SB.subgroupOf M).map Ψ₀,
    kOmega_map_subgroupOf_le_centralizer hSAB Ψ₀, ?_, ?_, ?_, ?_⟩
  ·
    rw [hlast₀, subgroupOf_sup hSAM hSBM, Subgroup.map_sup]
  ·
    intro i hi
    have hiv : i.val + 1 < m + 2 := by omega
    rw [← hshort i hiv]
    set k : Fin (m + 2) := if i.val = 0 then ⟨2, by omega⟩ else 0 with hkdef
    obtain ⟨a, b, ha, hb, hab_lt⟩ : ∃ a b : Fin (m + 1), k.succAbove a = i ∧
        k.succAbove b = ⟨i.val + 1, hiv⟩ ∧ a.val < m ∧ b.val < m := by
      by_cases hi0 : i.val = 0
      · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_, ?_, by simp; omega, by simp; omega⟩
        · rw [hkdef, ite_eq_left hi0]
          rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
          exact Fin.ext (by simp [hi0])
        · rw [hkdef, ite_eq_left hi0]
          rw [Fin.succAbove_of_castSucc_lt _ _ (by simp [Fin.lt_def])]
          exact Fin.ext (by simp [hi0])
      · refine ⟨⟨i.val - 1, by omega⟩, ⟨i.val, by omega⟩, ?_, ?_, by simp; omega, by simp; omega⟩
        · rw [hkdef, ite_eq_right hi0, Fin.succAbove_zero]
          exact Fin.ext (by simp; omega)
        · rw [hkdef, ite_eq_right hi0, Fin.succAbove_zero]
          exact Fin.ext (by simp)
    have hkl : k ≠ Fin.last (m + 1) := by
      rw [hkdef]
      split_ifs <;> intro h <;> have := congrArg Fin.val h <;> simp at this
      omega
    obtain ⟨Φ, σ, hΦ⟩ := hpar k
    obtain ⟨c, hc, hlast⟩ := hlong k hkl Φ σ hΦ
    have hcm : c.val = m := by
      by_contra hcm
      have hc' := congrArg Fin.val hc
      rw [Fin.val_last] at hc'
      by_cases hck : c.castSucc < k
      · rw [Fin.succAbove_of_castSucc_lt _ _ hck] at hc'
        simp at hc'
        omega
      · rw [Fin.succAbove_of_le_castSucc _ _ (not_lt.1 hck)] at hc'
        simp at hc'
        omega
    rw [kOmega_pieceCore_short_eq_map (r := m + 1) hKc hf (by omega) (by omega) e k Φ σ hΦ hiv ha
      hb,
      hlast]
    refine kOmega_map_subgroupOf_le_centralizer (fun x hx y hy => ?_) _
    have hdisj : Disjoint ({a.castSucc, b.castSucc} : Finset (Fin (m + 2)))
        {c.castSucc, Fin.last (m + 1)} := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz hz'
      rcases hz with rfl | rfl <;> rcases hz' with h | h <;>
        have := congrArg Fin.val h <;> simp at this <;> omega
    exact OmegaPilot.commute_of_mem_suppGL_of_disjoint (OmegaPilot.disjoint_planeCoords hdisj)
      (OmegaPilot.siegelBlockGL_le_suppGL _ hx)
      (((CFSG.Quasithin.perfectCore_le _).trans inf_le_right) hy)
  ·
    obtain ⟨θ₀, hθ₀, h12, h23⟩ := OmegaPilot.exists_theta_siegelNode (K := K)
      (n := m + 2) (i := ⟨m - 1, by omega⟩) (j := ⟨m, by omega⟩)
      (Or.inl ⟨by simp only; omega, by simp only; omega⟩)
    obtain ⟨θ, hθ, hθ12, hθ23⟩ := kOmega_exists_theta_map hθ₀ h12 h23 (hle _) (hle _) hΨ₀inj
    refine ⟨θ, hθ, ?_, ?_⟩
    · rw [hθ12, hn1, ← hpm]
    · rw [hθ23, hn2]
  ·
    obtain ⟨θ₀, hθ₀, h12, h23⟩ := OmegaPilot.exists_theta_siegelNode (K := K)
      (n := m + 2) (i := ⟨m - 1, by omega⟩) (j := Fin.last (m + 1))
      (Or.inr ⟨by simp only; omega, by simp only [Fin.val_last]⟩)
    obtain ⟨θ, hθ, hθ12, hθ23⟩ := kOmega_exists_theta_map hθ₀ h12 h23 (hle _) (hle _) hΨ₀inj
    refine ⟨θ, hθ, ?_, ?_⟩
    · rw [hθ12, hn1, ← hpm]
    · rw [hθ23, hn3]

theorem kOmegaParams_of_rootKind (hset : SeitzSetting G L) {m f : ℕ} (hm : 2 ≤ m)
    (hKc : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (e : L ≃* StatedSp (m + 2) K) {t : G}
    (htC : t ∈ centralizer (L : Set G)) (ht : orderOf t = 2)
    (hroot : ∀ k : Fin (m + 2), RootKindSp e t f k .omegaPlus) : KOmegaParams hm hKc hf e := by
  intro k
  obtain ⟨Φ, σ, -, hΦ⟩ := exists_kOmegaParam (r := m + 1) hset hKc hf (by omega) (by omega) e
    htC ht k (hroot k)
  exact ⟨Φ, σ, hΦ⟩

theorem spOmegaPlusPieceInput_holds : SpOmegaPlusPieceInput := by
  intro G _ _ L hset m f K _ _ _ hm hKc hf e t ht hKt hroot
  have htC : t ∈ centralizer (L : Set G) := LinearPilot.mem_centralizer_of_inf_eq_zpowers hKt
  exact spOmegaPlusPieces_of_params hm hKc hf e
    (kOmegaParams_of_rootKind hset hm hKc hf e htC ht hroot)

theorem spOmegaKindInput_omegaPlus_holds : SpOmegaKindInput .omegaPlus :=
  spOmegaKindInput_omegaPlus_of_pieceInput spOmegaPlusPieceInput_holds

end Assembly

end CFSG.SeitzReduction.SymplecticPilot
