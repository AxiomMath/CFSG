module

public import CFSG.ClassicalInvolution.Q3.TL3Induct

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

namespace Thm4Twin

namespace F2

variable {G : Type} [Group G] [Finite G]

theorem exists_section (K : Subgroup G) :
    ∃ W : Subgroup G, K ≤ W ∧ IsSubnormal W ⊤ ∧ (⨆ x : W, conjSub (x : G) K) = W := by
  classical
  have hne : ({W : Subgroup G | K ≤ W ∧ IsSubnormal W ⊤}).Nonempty :=
    ⟨⊤, le_top, IsSubnormal.refl _⟩
  obtain ⟨W, ⟨hKW, hW⟩, hmin⟩ := Set.exists_min_image {W : Subgroup G | K ≤ W ∧ IsSubnormal W ⊤}
    (fun W : Subgroup G => Nat.card W) (Set.toFinite _) hne
  refine ⟨W, hKW, hW, ?_⟩
  set Y : Subgroup G := ⨆ x : W, conjSub (x : G) K with hY
  have hYW : Y ≤ W := iSup_le fun x =>
    (conjSub_mono hKW).trans (conjSub_eq_self_of_mem x.2).le
  have hKY : K ≤ Y := by
    have := le_iSup (fun x : W => conjSub (x : G) K) 1
    simpa using this
  have hnorm : ∀ k ∈ W, ∀ h ∈ Y, k * h * k⁻¹ ∈ Y := by
    intro k hk h hh
    have hle : conjSub k Y ≤ Y := by
      rw [hY, conjSub, Subgroup.map_iSup]
      refine iSup_le fun x => ?_
      have : (conjSub (x : G) K).map (MulAut.conj k).toMonoidHom = conjSub (k * x) K := by
        rw [conjSub_mul]; rfl
      rw [this]
      exact le_iSup (fun x : W => conjSub (x : G) K) ⟨k * x, W.mul_mem hk x.2⟩
    exact hle (conj_mem_conjSub hh)
  have hYn : (Y.subgroupOf W).Normal :=
    ⟨fun h hh k => by
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact hnorm k k.2 h hh⟩
  have hYsub : IsSubnormal Y ⊤ := isSubnormal_trans (isSubnormal_of_normal_subgroupOf hYW hYn) hW
  have hcard : Nat.card W ≤ Nat.card Y := hmin Y ⟨hKY.trans le_rfl, hYsub⟩
  exact Subgroup.eq_of_le_of_card_ge hYW hcard

theorem exists_normalized_of_normal {H M : Subgroup G} (hHM : H ≤ M) (hn : (H.subgroupOf M).Normal)
    {P : Subgroup G} (hPH : P ≤ H) (hPn : ∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P)
    (hP2 : IsPGroup 2 P) :
    ∃ Q : Subgroup G, P ≤ Q ∧ Q ≤ H ∧ IsPGroup 2 Q ∧ ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup ↥H := pCore 2 ↥H with hC
  refine ⟨C.map H.subtype, ?_, Subgroup.map_subtype_le C, ?_, ?_⟩
  ·
    have hPC : P.subgroupOf H ≤ C := by
      refine le_sSup ⟨?_, ?_⟩
      · refine ⟨fun p hp h => ?_⟩
        rw [Subgroup.mem_subgroupOf] at hp ⊢
        exact hPn h h.2 p hp
      · exact hP2.comap_subtype
    intro p hp
    exact ⟨⟨p, hPH hp⟩, hPC (Subgroup.mem_subgroupOf.mpr hp), rfl⟩
  · exact (pCore_isPGroup (p := 2) (G := ↥H)).of_equiv (C.equivMapOfInjective _ H.subtype_injective)
  · intro m hm q hq
    obtain ⟨x, hx, rfl⟩ := hq
    have hmH : ∀ y : H, m * (y : G) * m⁻¹ ∈ H := fun y => by
      have := (Subgroup.normal_subgroupOf_iff hHM).mp hn (y : G) m y.2 hm
      simpa using this
    have hmH' : ∀ y : H, m⁻¹ * (y : G) * m ∈ H := fun y => by
      have := (Subgroup.normal_subgroupOf_iff hHM).mp hn (y : G) m⁻¹ y.2 (M.inv_mem hm)
      simpa using this
    let φ : ↥H ≃* ↥H :=
      { toFun := fun y => ⟨m * (y : G) * m⁻¹, hmH y⟩
        invFun := fun y => ⟨m⁻¹ * (y : G) * m, hmH' y⟩
        left_inv := fun y => Subtype.ext (by simp [mul_assoc])
        right_inv := fun y => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hφ := Subgroup.characteristic_iff_map_eq.mp
      (pCore_characteristic (p := 2) (G := ↥H)) φ
    have hmem : φ x ∈ C := by
      have h1 : φ x ∈ (pCore 2 ↥H).map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [hφ] at h1
      exact h1
    exact ⟨φ x, hmem, rfl⟩

theorem exists_normalized_of_subnormal {H K : Subgroup G} (hH : IsSubnormal H K) :
    ∀ P : Subgroup G, P ≤ H → (∀ h ∈ H, ∀ p ∈ P, h * p * h⁻¹ ∈ P) → IsPGroup 2 P →
      ∃ Q : Subgroup G, P ≤ Q ∧ IsPGroup 2 Q ∧ ∀ m ∈ K, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := by
  induction hH with
  | refl H => exact fun P _ hn h2 => ⟨P, le_rfl, h2, hn⟩
  | step hHM hN _ ih =>
    intro P hPH hPn hP2
    obtain ⟨Q, hPQ, hQH, hQ2, hQn⟩ := exists_normalized_of_normal hHM hN hPH hPn hP2
    obtain ⟨R, hQR, hR2, hRn⟩ := ih Q (hQH.trans hHM) hQn hQ2
    exact ⟨R, hPQ.trans hQR, hR2, hRn⟩

theorem tightInO2_of_subnormal {W : Subgroup G} (hW : IsSubnormal W ⊤) {z : G} (hzW : z ∈ W)
    (h : TightInO2 (⟨z, hzW⟩ : W)) : TightInO2 z := by
  obtain ⟨P', hPn, hP2, hz⟩ := h
  have hP2' : IsPGroup 2 (P'.map W.subtype) :=
    hP2.of_equiv (P'.equivMapOfInjective _ W.subtype_injective)
  obtain ⟨Q, hPQ, hQ2, hQn⟩ := exists_normalized_of_subnormal hW (P'.map W.subtype)
    (Subgroup.map_subtype_le P') (fun h hh p hp => by
      obtain ⟨x, hx, rfl⟩ := hp
      exact ⟨⟨h, hh⟩ * x * ⟨h, hh⟩⁻¹, hPn.conj_mem x hx _, rfl⟩) hP2'
  refine ⟨Q, ⟨fun q hq g => hQn g (Subgroup.mem_top g) q hq⟩, hQ2, hPQ ⟨_, hz, rfl⟩⟩

theorem isSubnormal_map_hom {G' : Type*} [Group G'] (f : G →* G') {H K : Subgroup G}
    (h : IsSubnormal H K) : IsSubnormal (H.map f) (K.map f) :=
  h.map f

theorem isClassicalMember3_map_subtype {W : Subgroup G} (hW : IsSubnormal W ⊤)
    {M : Subgroup ↥W} {z : ↥W} (h : IsClassicalMember3 M z) :
    IsClassicalMember3 (M.map W.subtype) (z : G) where
  orderOf_eq_two := by rw [Subgroup.orderOf_coe]; exact h.orderOf_eq_two
  mem := Subgroup.mem_map_of_mem _ h.mem
  subnormal := by
    have h1 := isSubnormal_map_hom W.subtype h.subnormal
    have h2 : (Subgroup.centralizer ({z} : Set ↥W)).map W.subtype =
        W ⊓ Subgroup.centralizer ({(z : G)} : Set G) := by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_inf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨y.2, ?_⟩
        have := congrArg Subtype.val hy
        simpa using this
      · rintro ⟨hxW, hx⟩
        refine ⟨⟨x, hxW⟩, Subtype.ext ?_, rfl⟩
        simpa using hx
    rw [h2] at h1
    have h3 := isSubnormal_inf hW (Subgroup.centralizer ({(z : G)} : Set G))
    rw [top_inf_eq] at h3
    exact isSubnormal_trans h1 h3
  nonempty_equiv := by
    obtain ⟨e'⟩ := h.nonempty_equiv
    let e : M ≃* M.map W.subtype := M.equivMapOfInjective W.subtype W.subtype_injective
    have hO : (classicalInvolutionOddCore M).map e.toMonoidHom =
        classicalInvolutionOddCore (M.map W.subtype) :=
      CFSG.ComponentClassification.OddCore.equiv_invariant e
    exact ⟨(QuotientGroup.congr _ _ e hO).symm.trans e'⟩

end F2

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
