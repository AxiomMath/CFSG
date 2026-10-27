module

public import CFSG.GF2Type.SmithTypeE.LMod.UaColl
public import CFSG.GF2Type.SmithTypeE.LMod.AutNorm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.LMod

open CFSG.SmithL6
open CFSG.SmithE (applyCols)
open scoped Pointwise

attribute [local irreducible] stabGens elemGens planeImg meetCard dRoot tvIdxTab tvTab tvImg tvList

@[expose] noncomputable def restrW {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)) :
    E →* Equiv.Perm (wPlane i) :=
  (MulAction.toPermHom (MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)) (wPlane i)).comp
    (Subgroup.inclusion hW)

theorem restrW_apply {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)) (π : E) (x : wPlane i) :
    (restrW hW π x).val = (π : Equiv.Perm (Fin 1953)) x.val := rfl

theorem restrW_eq_one_iff {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)) (π : E) :
    restrW hW π = 1 ↔ ∀ p ∈ wPlane i, (π : Equiv.Perm (Fin 1953)) p = p := by
  constructor
  · intro h p hp
    have := congrArg (fun ν : Equiv.Perm (wPlane i) => (ν ⟨p, hp⟩).val) h
    simpa [restrW_apply] using this
  · intro h
    ext x
    rw [restrW_apply, h x.val x.2]
    rfl

theorem restrW_eq_iff {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)) (π ρ : E) :
    restrW hW π = restrW hW ρ ↔
      ∀ p ∈ wPlane i, (π : Equiv.Perm (Fin 1953)) p = (ρ : Equiv.Perm (Fin 1953)) p := by
  constructor
  · intro h p hp
    have := congrArg (fun ν : Equiv.Perm (wPlane i) => (ν ⟨p, hp⟩).val) h
    simpa [restrW_apply] using this
  · intro h
    ext x
    rw [restrW_apply, restrW_apply, h x.val x.2]

theorem card_eq_range_mul_ker {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i)) :
    Nat.card E = Nat.card (restrW hW).range * Nat.card (restrW hW).ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (restrW hW).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange (restrW hW)).toEquiv]

section Hyp

structure ZeroHyp (E : Subgroup (Equiv.Perm (Fin 1953))) : Prop where
  isTv : ∀ π ∈ E, IsTvAut π
  fixW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane 0)
  sq : ∀ π ∈ E, π * π = 1
  comm : ∀ π ∈ E, ∀ ρ ∈ E, π * ρ = ρ * π
  cent : E ⊓ Subgroup.centralizer (UA 0 : Set (Equiv.Perm (Fin 1953))) ≤ UA 0

end Hyp

section Zero

variable
  {E : Subgroup (Equiv.Perm (Fin 1953))}

theorem ZeroHyp.img (H : ZeroHyp E) {π : Equiv.Perm (Fin 1953)} (hπ : π ∈ E) :
    ⇑π '' wPlane 0 = wPlane 0 :=
  mem_stabilizer_wPlane.1 (H.fixW hπ)

theorem ZeroHyp.ker_le (H : ZeroHyp E) {π : E} (hπ : restrW H.fixW π = 1) :
    (π : Equiv.Perm (Fin 1953)) ∈ UA 0 := by
  refine H.cent (Subgroup.mem_inf.2 ⟨π.2, ?_⟩)
  rw [UA, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  rintro _ ⟨p, hp, rfl⟩
  have h := H.isTv π π.2 p
  rw [(restrW_eq_one_iff H.fixW π).1 hπ p hp] at h
  exact (mul_inv_eq_iff_eq_mul.1 h).symm

theorem ZeroHyp.ker_fixed (H : ZeroHyp E) {κ : E} (hκ : restrW H.fixW κ = 1) :
    ∃ a < 512, psi0 a = κ ∧ ∀ π ∈ E, applyCols (colsOf π) a = a := by
  obtain ⟨a, ha, he⟩ := mem_UA_zero.1 (H.ker_le hκ)
  refine ⟨a, ha, he, fun π hπ => ?_⟩
  have hcomm : π * κ = κ * π := H.comm π hπ κ κ.2
  have h1 : π * psi0 a * π⁻¹ = psi0 (applyCols (colsOf π) a) :=
    conj_psi0_gen (H.isTv π hπ) (H.img hπ) a
  have h2 : π * psi0 a * π⁻¹ = psi0 a := by
    rw [he, hcomm, mul_assoc, mul_inv_cancel, mul_one]
  refine psi0_inj (applyCols_lt (colsOf_size π) (fun j hj => colsOf_lt (H.isTv π hπ) (H.img hπ) hj) a)
    ha ?_
  rw [← h1, h2]

theorem ZeroHyp.card_ker_le (H : ZeroHyp E) (T : Finset (Equiv.Perm (Fin 1953)))
    (hT : ∀ π ∈ T, π ∈ E) :
    Nat.card (restrW H.fixW).ker ≤
      ((Finset.range 512).filter fun a => ∀ π ∈ T, applyCols (colsOf π) a = a).card := by
  classical
  have hfix := fun κ : (restrW H.fixW).ker =>
    H.ker_fixed (κ := κ.1) (MonoidHom.mem_ker.1 κ.2)
  let f : (restrW H.fixW).ker →
      ((Finset.range 512).filter fun a => ∀ π ∈ T, applyCols (colsOf π) a = a) :=
    fun κ => ⟨Classical.choose (hfix κ), by
      obtain ⟨ha, -, hfx⟩ := Classical.choose_spec (hfix κ)
      exact Finset.mem_filter.2 ⟨Finset.mem_range.2 ha, fun π hπ => hfx π (hT π hπ)⟩⟩
  have hf : Function.Injective f := by
    intro κ κ' h
    have h' : Classical.choose (hfix κ) = Classical.choose (hfix κ') := congrArg Subtype.val h
    apply Subtype.ext
    apply Subtype.ext
    rw [← (Classical.choose_spec (hfix κ)).2.1, ← (Classical.choose_spec (hfix κ')).2.1, h']
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_le_card_of_injective f hf

end Zero

section Matrices

variable
  {E : Subgroup (Equiv.Perm (Fin 1953))}

theorem ptTab_true {c : ℕ} (hc : c < 512) (h : ∃ k < 49, uco[k]! = c) : collPtTab[c]! = true := by
  have e : collPtTab[c]! = uco.contains c := by
    simp [collPtTab, getElem!_pos, hc]
  rw [e]
  exact (f1_contains_uco c).2 h

theorem ZeroHyp.colsOf_pt (H : ZeroHyp E) {π : Equiv.Perm (Fin 1953)} (hπ : π ∈ E) {k : ℕ}
    (hk : k < 49) : collPtTab[applyCols (colsOf π) uco[k]!]! = true := by
  rw [act_pt (H.isTv π hπ) (H.img hπ) hk]
  have hm : π (pt0 k) ∈ wPlane 0 := by
    rw [← H.img hπ]
    exact Set.mem_image_of_mem _ (pt0_mem hk)
  have hlt := pos0_lt_49_of_mem hm
  exact ptTab_true (uaFacts.uco_parts _ hlt).2 ⟨_, hlt, rfl⟩

theorem ZeroHyp.colsOf_mem (H : ZeroHyp E) {π : Equiv.Perm (Fin 1953)} (hπ : π ∈ E)
    (hne : ∃ p ∈ wPlane 0, π p ≠ p) : colsOf π ∈ collL := by
  refine mem_collL (colsOf_size π) (fun k hk => H.colsOf_pt hπ hk) (fun m hm => ?_) ?_
  · have h1 : (colsOf π)[m]! = applyCols (colsOf π) (2 ^ m) :=
      (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
    rw [h1, ← act_mul (H.isTv π hπ) (H.img hπ) (H.isTv π hπ) (H.img hπ), H.sq π hπ]
    exact act_one _ (two_pow_lt_512 hm)
  · by_contra hcon
    push Not at hcon
    obtain ⟨p, hp, hpne⟩ := hne
    refine hpne ((colsOf_eq_one_iff (H.isTv π hπ) (H.img hπ)).1 (fun m hm => ?_) p hp)
    rw [applyCols_pow (by rw [colsOf_size]; exact hm)]
    exact hcon m hm

theorem ZeroHyp.collComm_colsOf (H : ZeroHyp E) {π ρ : Equiv.Perm (Fin 1953)} (hπ : π ∈ E)
    (hρ : ρ ∈ E) : collComm (colsOf π) (colsOf ρ) = true := by
  unfold collComm
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq]
  intro m hm
  have h1 : (colsOf ρ)[m]! = applyCols (colsOf ρ) (2 ^ m) :=
    (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
  have h2 : (colsOf π)[m]! = applyCols (colsOf π) (2 ^ m) :=
    (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
  rw [h1, h2, ← act_mul (H.isTv π hπ) (H.img hπ) (H.isTv ρ hρ) (H.img hρ),
    ← act_mul (H.isTv ρ hρ) (H.img hρ) (H.isTv π hπ) (H.img hπ), H.comm π hπ ρ hρ]

theorem ZeroHyp.collMul_colsOf (H : ZeroHyp E) {π ρ : Equiv.Perm (Fin 1953)} (hπ : π ∈ E)
    (hρ : ρ ∈ E) : collMul (colsOf π) (colsOf ρ) = colsOf (π * ρ) := by
  apply Array.ext
  · simp [collMul, colsOf_size]
  · intro m hm1 hm2
    have hm : m < 9 := by simpa [collMul] using hm1
    have h1 : (colsOf ρ)[m]! = applyCols (colsOf ρ) (2 ^ m) :=
      (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
    have h3 : (colsOf (π * ρ))[m]! = applyCols (colsOf (π * ρ)) (2 ^ m) :=
      (applyCols_pow (by rw [colsOf_size]; exact hm)).symm
    have key : (collMul (colsOf π) (colsOf ρ))[m]! = (colsOf (π * ρ))[m]! := by
      rw [h3, act_mul (H.isTv π hπ) (H.img hπ) (H.isTv ρ hρ) (H.img hρ), ← h1]
      simp [collMul, getElem!_pos, hm]
    exact (getElem!_pos _ m hm1).symm.trans (key.trans (getElem!_pos _ m hm2))

theorem ZeroHyp.restrW_eq_of_colsOf_eq (H : ZeroHyp E) {π ρ : E}
    (h : colsOf (π : Equiv.Perm (Fin 1953)) = colsOf (ρ : Equiv.Perm (Fin 1953))) :
    restrW H.fixW π = restrW H.fixW ρ := by
  rw [restrW_eq_iff]
  refine apply_eq_of_colsOf_eq (H.isTv _ π.2) (H.img π.2) (H.isTv _ ρ.2) (H.img ρ.2) ?_
  intro m _
  rw [h]

end Matrices

theorem card_le_of_forall_mem_finset {G : Type*} [Group G] [Finite G] (F : Subgroup G)
    (S : Finset G) (h : ∀ x ∈ F, x ∈ S) : Nat.card F ≤ S.card := by
  have e : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq _
  rw [e, ← Set.ncard_coe_finset S]
  exact Set.ncard_le_ncard (fun x hx => Finset.mem_coe.2 (h x hx)) (Finset.finite_toSet _)

theorem card_le_of_injOn_list {G β : Type*} [Group G] [Finite G] (F : Subgroup G) (g : G → β)
    (L : List β) (hg : ∀ x ∈ F, x ≠ 1 → g x ∈ L)
    (hinj : ∀ x ∈ F, ∀ y ∈ F, g x = g y → x = y) : Nat.card F ≤ L.length + 1 := by
  classical
  have hR1 : (1 : G) ∈ (F : Set G) := F.one_mem
  have hle : ((F : Set G) \ {1}).ncard ≤ L.length := by
    refine le_trans (Set.ncard_le_ncard_of_injOn g (t := (L.toFinset : Set β)) ?_ ?_
      (Finset.finite_toSet _)) ?_
    · intro x hx
      rw [Finset.mem_coe, List.mem_toFinset]
      exact hg x hx.1 hx.2
    · intro x hx y hy h
      exact hinj x hx.1 y hy.1 h
    · rw [Set.ncard_coe_finset]
      exact List.toFinset_card_le L
  have h1 := Set.ncard_sdiff_singleton_add_one hR1 (Set.toFinite (F : Set G))
  have e : Nat.card F = (F : Set G).ncard := Nat.card_coe_set_eq _
  omega

section Bound

variable
  {E : Subgroup (Equiv.Perm (Fin 1953))}

@[expose] noncomputable def matOf (ν : Equiv.Perm (wPlane 0)) : Array ℕ :=
  Array.ofFn (n := 9) fun j => uco[pos0 (ν ⟨gen0 j.val, gen0_mem j.val j.2⟩).val.val]!

theorem matOf_restrW {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane 0)) (π : E) :
    matOf (restrW hW π) = colsOf (π : Equiv.Perm (Fin 1953)) := rfl

theorem ZeroHyp.exists_move (H : ZeroHyp E) {π : E} (hπ : restrW H.fixW π ≠ 1) :
    ∃ p ∈ wPlane 0, (π : Equiv.Perm (Fin 1953)) p ≠ p := by
  by_contra h
  simp only [not_exists, not_and, not_not] at h
  exact hπ ((restrW_eq_one_iff H.fixW π).2 h)

theorem ZeroHyp.colsOf_mem_of_ne (H : ZeroHyp E) {π : E} (hπ : restrW H.fixW π ≠ 1) :
    colsOf (π : Equiv.Perm (Fin 1953)) ∈ collL :=
  H.colsOf_mem π.2 (H.exists_move hπ)

theorem ZeroHyp.card_ker_le_64 (H : ZeroHyp E) {π : E} (hπ : restrW H.fixW π ≠ 1) :
    Nat.card (restrW H.fixW).ker ≤ 64 := by
  classical
  refine (H.card_ker_le {(π : Equiv.Perm (Fin 1953))}
    (fun σ hσ => by rw [Finset.mem_singleton.1 hσ]; exact π.2)).trans
    (le_trans (Finset.card_le_card ?_) (fix_le (H.colsOf_mem_of_ne hπ)))
  intro a ha
  simp only [Finset.mem_filter, Finset.mem_singleton, forall_eq] at ha ⊢
  exact ha

theorem ZeroHyp.card_le_of_not_le_UA (H : ZeroHyp E) (hEU : ¬ E ≤ UA 0) : Nat.card E ≤ 384 := by
  classical
  obtain ⟨π₁, hπ₁⟩ : ∃ π₁ : E, restrW H.fixW π₁ ≠ 1 := by
    by_contra h
    push Not at h
    exact hEU fun π hπ => H.ker_le (h ⟨π, hπ⟩)
  rw [card_eq_range_mul_ker H.fixW]
  have hK64 := H.card_ker_le_64 hπ₁
  by_cases h3 : ∃ π₂ : E, restrW H.fixW π₂ ≠ 1 ∧ restrW H.fixW π₂ ≠ restrW H.fixW π₁
  · obtain ⟨π₂, hπ₂, hπ₂₁⟩ := h3
    by_cases h4 : ∃ π₃ : E, restrW H.fixW π₃ ≠ 1 ∧ restrW H.fixW π₃ ≠ restrW H.fixW π₁ ∧
        restrW H.fixW π₃ ≠ restrW H.fixW π₂ ∧
        restrW H.fixW π₃ ≠ restrW H.fixW π₁ * restrW H.fixW π₂
    · obtain ⟨π₃, hπ₃, hπ₃₁, hπ₃₂, hπ₃₁₂⟩ := h4
      have hA := H.colsOf_mem_of_ne hπ₁
      have hB := H.colsOf_mem_of_ne hπ₂
      have hC := H.colsOf_mem_of_ne hπ₃
      have hAB := H.collComm_colsOf π₁.2 π₂.2
      have hAC := H.collComm_colsOf π₁.2 π₃.2
      have hBC := H.collComm_colsOf π₂.2 π₃.2
      have h12 : colsOf (π₁ : Equiv.Perm (Fin 1953)) ≠ colsOf (π₂ : Equiv.Perm (Fin 1953)) :=
        fun h => hπ₂₁ (H.restrW_eq_of_colsOf_eq h).symm
      have h31 : colsOf (π₃ : Equiv.Perm (Fin 1953)) ≠ colsOf (π₁ : Equiv.Perm (Fin 1953)) :=
        fun h => hπ₃₁ (H.restrW_eq_of_colsOf_eq h)
      have h32 : colsOf (π₃ : Equiv.Perm (Fin 1953)) ≠ colsOf (π₂ : Equiv.Perm (Fin 1953)) :=
        fun h => hπ₃₂ (H.restrW_eq_of_colsOf_eq h)
      have h12₃ : collMul (colsOf (π₁ : Equiv.Perm (Fin 1953)))
          (colsOf (π₂ : Equiv.Perm (Fin 1953))) ≠ colsOf (π₃ : Equiv.Perm (Fin 1953)) := by
        intro h
        rw [H.collMul_colsOf π₁.2 π₂.2] at h
        exact hπ₃₁₂ (by rw [← map_mul]; exact (H.restrW_eq_of_colsOf_eq (π := π₁ * π₂) h).symm)
      obtain ⟨hfix3, hcomm3⟩ := triple_bound hA hB hC hAB hAC hBC h12 h31 h32 h12₃
      have hK : Nat.card (restrW H.fixW).ker ≤ 16 := by
        refine (H.card_ker_le {(π₁ : Equiv.Perm (Fin 1953)), (π₂ : Equiv.Perm (Fin 1953)),
          (π₃ : Equiv.Perm (Fin 1953))} ?_).trans (le_trans (Finset.card_le_card ?_) hfix3)
        · intro σ hσ
          simp only [Finset.mem_insert, Finset.mem_singleton] at hσ
          rcases hσ with rfl | rfl | rfl
          exacts [π₁.2, π₂.2, π₃.2]
        · intro a ha
          simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
            forall_eq_or_imp, forall_eq] at ha ⊢
          exact ha
      have hR : Nat.card (restrW H.fixW).range ≤ 24 := by
        have h1 := card_le_of_injOn_list (restrW H.fixW).range matOf
          (collL.toList.filter fun M => collComm (colsOf (π₁ : Equiv.Perm (Fin 1953))) M &&
            collComm (colsOf (π₂ : Equiv.Perm (Fin 1953))) M &&
              collComm (colsOf (π₃ : Equiv.Perm (Fin 1953))) M) ?_ ?_
        · omega
        · intro ν hν hν1
          obtain ⟨π, rfl⟩ := MonoidHom.mem_range.1 hν
          rw [matOf_restrW, List.mem_filter]
          refine ⟨Array.mem_toList_iff.2 (H.colsOf_mem_of_ne hν1), ?_⟩
          simp [H.collComm_colsOf π₁.2 π.2, H.collComm_colsOf π₂.2 π.2,
            H.collComm_colsOf π₃.2 π.2]
        · intro ν hν μ hμ h
          obtain ⟨π, rfl⟩ := MonoidHom.mem_range.1 hν
          obtain ⟨ρ, rfl⟩ := MonoidHom.mem_range.1 hμ
          rw [matOf_restrW, matOf_restrW] at h
          exact H.restrW_eq_of_colsOf_eq h
      calc Nat.card (restrW H.fixW).range * Nat.card (restrW H.fixW).ker ≤ 24 * 16 :=
            Nat.mul_le_mul hR hK
        _ ≤ 384 := by norm_num
    · have hR : Nat.card (restrW H.fixW).range ≤ 4 := by
        refine (card_le_of_forall_mem_finset _ {1, restrW H.fixW π₁, restrW H.fixW π₂,
          restrW H.fixW π₁ * restrW H.fixW π₂} ?_).trans Finset.card_le_four
        intro x hx
        obtain ⟨π, rfl⟩ := MonoidHom.mem_range.1 hx
        by_contra hnot
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
        exact h4 ⟨π, hnot.1, hnot.2.1, hnot.2.2.1, hnot.2.2.2⟩
      calc Nat.card (restrW H.fixW).range * Nat.card (restrW H.fixW).ker ≤ 4 * 64 :=
            Nat.mul_le_mul hR hK64
        _ ≤ 384 := by norm_num
  · have hR : Nat.card (restrW H.fixW).range ≤ 2 := by
      refine (card_le_of_forall_mem_finset _ {1, restrW H.fixW π₁} ?_).trans Finset.card_le_two
      intro x hx
      obtain ⟨π, rfl⟩ := MonoidHom.mem_range.1 hx
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact h3 ⟨π, hnot.1, hnot.2⟩
    calc Nat.card (restrW H.fixW).range * Nat.card (restrW H.fixW).ker ≤ 2 * 64 :=
          Nat.mul_le_mul hR hK64
      _ ≤ 384 := by norm_num

theorem ZeroHyp.card_le (H : ZeroHyp E) : Nat.card E ≤ 2 ^ 9 := by
  by_cases h : E ≤ UA 0
  · exact (Subgroup.card_le_of_le h).trans card_UA_zero.le
  · exact (H.card_le_of_not_le_UA h).trans (by norm_num)

theorem ZeroHyp.eq_UA (H : ZeroHyp E) (hcard : 2 ^ 9 ≤ Nat.card E) : E = UA 0 := by
  have h : E ≤ UA 0 := by
    by_contra h
    have := H.card_le_of_not_le_UA h
    omega
  exact Subgroup.eq_of_le_of_card_ge h (by rw [card_UA_zero]; exact hcard)

end Bound

@[expose] def conjSub (x : Equiv.Perm (Fin 1953)) (E : Subgroup (Equiv.Perm (Fin 1953))) :
    Subgroup (Equiv.Perm (Fin 1953)) :=
  E.map (MulAut.conj x⁻¹).toMonoidHom

theorem mem_conjSub {x π : Equiv.Perm (Fin 1953)} {E : Subgroup (Equiv.Perm (Fin 1953))} :
    π ∈ conjSub x E ↔ x * π * x⁻¹ ∈ E := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have e : x * (x⁻¹ * σ * x⁻¹⁻¹) * x⁻¹ = σ := by group
    show x * ((MulAut.conj x⁻¹) σ) * x⁻¹ ∈ E
    rw [MulAut.conj_apply, e]
    exact hσ
  · intro h
    refine ⟨x * π * x⁻¹, h, ?_⟩
    show (MulAut.conj x⁻¹) (x * π * x⁻¹) = π
    rw [MulAut.conj_apply]
    group

theorem card_conjSub (x : Equiv.Perm (Fin 1953)) (E : Subgroup (Equiv.Perm (Fin 1953))) :
    Nat.card (conjSub x E) = Nat.card E :=
  (Nat.card_congr (E.equivMapOfInjective _ (MulAut.conj x⁻¹).injective).toEquiv).symm

section Transport

theorem zeroHyp_conjSub {i : ℕ} {x : Equiv.Perm (Fin 1953)} (hx : x ∈ T6)
    (hW : ⇑x '' wPlane 0 = wPlane i) {E : Subgroup (Equiv.Perm (Fin 1953))}
    (hN : E ≤ Subgroup.normalizer (T6 : Set (Equiv.Perm (Fin 1953))))
    (hS : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i))
    (hsq : ∀ π ∈ E, π * π = 1) (hcomm : ∀ π ∈ E, ∀ ρ ∈ E, π * ρ = ρ * π)
    (hC : E ⊓ Subgroup.centralizer (UA i : Set (Equiv.Perm (Fin 1953))) ≤ UA i) :
    ZeroHyp (conjSub x E) where
  isTv := fun π hπ => by
    have h1 := isTvAut_of_mem_normalizer (hN (mem_conjSub.1 hπ))
    have hx' := isTvAut_of_mem hx
    have h2 := (hx'.inv.mul h1).mul hx'
    rwa [show x⁻¹ * (x * π * x⁻¹) * x = π by group] at h2
  fixW := fun π hπ => by
    have h2 := mem_stabilizer_wPlane.1 (hS (mem_conjSub.1 hπ))
    rw [mem_stabilizer_wPlane]
    have e : π = x⁻¹ * (x * π * x⁻¹) * x := by group
    rw [e, Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, Set.image_comp, Set.image_comp, hW, h2,
      image_wPlane_inv hW]
  sq := fun π hπ => by
    have h := hsq _ (mem_conjSub.1 hπ)
    calc π * π = x⁻¹ * ((x * π * x⁻¹) * (x * π * x⁻¹)) * x := by group
      _ = 1 := by rw [h]; group
  comm := fun π hπ ρ hρ => by
    have h := hcomm _ (mem_conjSub.1 hπ) _ (mem_conjSub.1 hρ)
    calc π * ρ = x⁻¹ * ((x * π * x⁻¹) * (x * ρ * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * ρ * x⁻¹) * (x * π * x⁻¹)) * x := by rw [h]
      _ = ρ * π := by group
  cent := fun π hπ => by
    obtain ⟨hπE, hπC⟩ := Subgroup.mem_inf.1 hπ
    have hσ := mem_conjSub.1 hπE
    have hσC : x * π * x⁻¹ ∈ Subgroup.centralizer (UA i : Set (Equiv.Perm (Fin 1953))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : x⁻¹ * u * x ∈ UA 0 := (mem_UA_iff_conj hx hW).1 hu
      have h := Subgroup.mem_centralizer_iff.1 hπC _ hu'
      calc u * (x * π * x⁻¹) = x * ((x⁻¹ * u * x) * π) * x⁻¹ := by group
        _ = x * (π * (x⁻¹ * u * x)) * x⁻¹ := by rw [h]
        _ = x * π * x⁻¹ * u := by group
    have h2 := (mem_UA_iff_conj hx hW).1 (hC (Subgroup.mem_inf.2 ⟨hσ, hσC⟩))
    rwa [show x⁻¹ * (x * π * x⁻¹) * x = π by group] at h2

end Transport

section Classification

theorem sq_of_isElementaryAbelian {E : Subgroup (Equiv.Perm (Fin 1953))}
    [CFSG.IsElementaryAbelian 2 E] : ∀ π ∈ E, π * π = 1 := fun π hπ => by
  rw [← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian π hπ

theorem comm_of_isElementaryAbelian {E : Subgroup (Equiv.Perm (Fin 1953))}
    [hE : CFSG.IsElementaryAbelian 2 E] : ∀ π ∈ E, ∀ ρ ∈ E, π * ρ = ρ * π :=
  fun π hπ ρ hρ => congrArg Subtype.val (hE.is_comm.comm ⟨π, hπ⟩ ⟨ρ, hρ⟩)

variable
  {i : ℕ} {E : Subgroup (Equiv.Perm (Fin 1953))} (hi : i < 1395)
  (hN : E ≤ Subgroup.normalizer (T6 : Set (Equiv.Perm (Fin 1953))))
  (hW : E ≤ MulAction.stabilizer (Equiv.Perm (Fin 1953)) (wPlane i))
  [hE : CFSG.IsElementaryAbelian 2 E]
  (hC : E ⊓ Subgroup.centralizer (UA i : Set (Equiv.Perm (Fin 1953))) ≤ UA i)
include hi hN hW hC

theorem rank_le_nine : Nat.card E ≤ 2 ^ 9 := by
  obtain ⟨x, hx, hxW⟩ := exists_image_wPlane_zero hi
  rw [← card_conjSub x E]
  exact (zeroHyp_conjSub hx hxW hN hW sq_of_isElementaryAbelian comm_of_isElementaryAbelian
    hC).card_le

theorem elemAb_eq_UA (hcard : 2 ^ 9 ≤ Nat.card E) : E = UA i := by
  obtain ⟨x, hx, hxW⟩ := exists_image_wPlane_zero hi
  have H := zeroHyp_conjSub hx hxW hN hW sq_of_isElementaryAbelian comm_of_isElementaryAbelian hC
  have h0 : conjSub x E = UA 0 := H.eq_UA (by rw [card_conjSub]; exact hcard)
  have hle : E ≤ UA i := by
    intro π hπ
    have hπ' : x⁻¹ * π * x ∈ conjSub x E :=
      mem_conjSub.2 (by rwa [show x * (x⁻¹ * π * x) * x⁻¹ = π by group])
    rw [h0] at hπ'
    exact (mem_UA_iff_conj hx hxW).2 hπ'
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_UA hi]; exact hcard)

end Classification

end CFSG.GF2Type.SmithTypeE.LMod
