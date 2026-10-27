module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7Model
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLNoS3

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

variable {k : ℕ}

section Solvable

theorem permBar_comm_of_ker {x y : AEQ k} (hx : TL4.permBar k x = 1) (hy : TL4.permBar k y = 1) :
    x * y = y * x := by
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective y
  have hu : u.perm = 1 := by
    have h' : TL4.permBar k (mkQ k u) = 1 := hx
    rwa [TL4.permBar_mkQ] at h'
  have hw : w.perm = 1 := by
    have h' : TL4.permBar k (mkQ k w) = 1 := hy
    rwa [TL4.permBar_mkQ] at h'
  show mkQ k u * mkQ k w = mkQ k w * mkQ k u
  rw [← map_mul, ← map_mul]
  congr 1
  refine Wr.ext (funext fun i => ?_) ?_
  · rw [Wr.mul_vec, Wr.mul_vec, hu, hw]
    show u.vec i + w.vec i = w.vec i + u.vec i
    exact add_comm _ _
  · rw [Wr.mul_perm, Wr.mul_perm, hu, hw]

theorem isSolvable_of_permBar_le (E : Subgroup (AEQ k)) (Q : Subgroup (Equiv.Perm (Fin k)))
    [Group.IsSolvable ↥Q] (h : E.map (TL4.permBar k) ≤ Q) : Group.IsSolvable ↥E := by
  let φ : ↥E →* ↥Q := ((TL4.permBar k).comp E.subtype).codRestrict Q (fun x => h ⟨x, x.2, rfl⟩)
  have hker : ∀ a b : ↥φ.ker, a * b = b * a := by
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have ha : TL4.permBar k (((a : ↥φ.ker) : ↥E) : AEQ k) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp a.2)
      simpa [φ] using this
    have hb : TL4.permBar k (((b : ↥φ.ker) : ↥E) : AEQ k) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp b.2)
      simpa [φ] using this
    exact permBar_comm_of_ker ha hb
  haveI : Group.IsSolvable ↥φ.ker := Group.isSolvable_of_comm hker
  exact Group.isSolvable_of_ker_le_range φ.ker.subtype φ (by rw [Subgroup.range_subtype])

theorem V4S_comm (α : Finset (Fin k)) (h : α.card = 4) (b : Bool) :
    ∀ x ∈ V4S α h b, ∀ y ∈ V4S α h b, x * y = y * x := by
  have hv : ∀ δ ∈ v4List, ∀ δ' ∈ v4List, δ * δ' = δ' * δ := by decide +kernel
  intro x hx y hy
  obtain ⟨δ, hδ, rfl⟩ := (mem_V4S_iff α h b x).mp hx
  obtain ⟨δ', hδ', rfl⟩ := (mem_V4S_iff α h b y).mp hy
  rw [← embedPerm_mul, ← embedPerm_mul, hv δ hδ δ' hδ']

theorem isSolvable_Ea_of_uniq {𝒜 : Set (Finset (Fin k))} {a : AEQ k}
    (huniq : ∀ α ∈ 𝒜, ∀ α' ∈ 𝒜, CenSet a α → CenSet a α' → α = α') :
    Group.IsSolvable ↥(Ea (aeMembers k 𝒜) a) := by
  by_cases hc : ∃ α ∈ 𝒜, CenSet a α
  · obtain ⟨α₀, hα₀, h₀, b₀, hM₀⟩ := hc
    haveI : Group.IsSolvable ↥(V4S α₀ h₀ b₀) :=
      Group.isSolvable_of_comm fun x y => Subtype.ext (V4S_comm α₀ h₀ b₀ x x.2 y y.2)
    refine isSolvable_of_permBar_le _ (V4S α₀ h₀ b₀) ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine Ea_le fun M hM hMc => ?_
    obtain ⟨γ, hγ, hγc, b, rfl⟩ := hM
    have hγ0 : γ = α₀ := huniq γ hγ α₀ hα₀ ⟨hγc, b, hMc⟩ ⟨h₀, b₀, hM₀⟩
    subst hγ0
    rw [← Subgroup.map_le_iff_le_comap]
    exact (V4S_bool γ hγc b b₀).le
  · haveI : Group.IsSolvable ↥(⊥ : Subgroup (Equiv.Perm (Fin k))) := inferInstance
    refine isSolvable_of_permBar_le _ ⊥ ?_
    rw [Subgroup.map_le_iff_le_comap]
    refine Ea_le fun M hM hMc => ?_
    obtain ⟨γ, hγ, hγc, b, rfl⟩ := hM
    exact absurd ⟨γ, hγ, hγc, b, hMc⟩ hc

theorem exists_pair_of_not_isSolvable {𝒜 : Set (Finset (Fin k))} {a : AEQ k}
    (hns : ¬ Group.IsSolvable ↥(Ea (aeMembers k 𝒜) a)) :
    ∃ α ∈ 𝒜, ∃ α' ∈ 𝒜, α ≠ α' ∧ CenSet a α ∧ CenSet a α' := by
  by_contra hcon
  refine hns (isSolvable_Ea_of_uniq fun α hα α' hα' h1 h2 => ?_)
  by_contra hne
  exact hcon ⟨α, hα, α', hα', hne, h1, h2⟩

end Solvable

section Levels

theorem perm_eq_one_of_pair (hk7 : k ≤ 7) {w : Wr k} (hsign : Equiv.Perm.sign w.perm = 1)
    {α α' : Finset (Fin k)} (hα : CenSet (mkQ k w) α) (hα' : CenSet (mkQ k w) α') (hne : α ≠ α') :
    w.perm = 1 := by
  by_contra hσ
  obtain ⟨hαc, bα, hMα⟩ := hα
  obtain ⟨hα'c, bα', hMα'⟩ := hα'
  exact false_of_commV_pair hk7 hsign hσ (commV_of_le_centralizer hMα) (commV_of_le_centralizer hMα')
    (by rw [map_univ_emb, map_univ_emb]; exact hne)

theorem exists_level_set (hk5 : 5 ≤ k) (hk7 : k ≤ 7) {w : Wr k} (hw : w.perm = 1)
    {γ δ : Finset (Fin k)} (hγ : CenSet (mkQ k w) γ) (hδ : CenSet (mkQ k w) δ) (hne : γ ≠ δ) :
    5 ≤ (γ ∪ δ).card ∧ ∃ c : ZMod 2, ∀ x ∈ γ ∪ δ, w.vec x = c := by
  obtain ⟨hvals, e, heδ, heγ⟩ := vec_eq_of_cen_pair hk5 hk7 hw hγ hδ hne
  obtain ⟨hγc, bγ, hMγ⟩ := hγ
  have cγ := const_of_le_centralizer hk5 hw hMγ
  obtain ⟨x₀, hx₀⟩ : γ.Nonempty := Finset.card_pos.mp (by omega)
  refine ⟨?_, w.vec x₀, ?_⟩
  · have hsub : insert e γ ⊆ γ ∪ δ := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Finset.mem_union_right _ heδ
      · exact Finset.mem_union_left _ hx
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem heγ, hγc] at h1
    exact h1
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact cγ x hx x₀ hx₀
    · exact (hvals x₀ hx₀ x hx).symm

end Levels

section Weight

theorem weight_dichotomy {w : Wr k} {L : Finset (Fin k)} {c : ZMod 2} (hc : ∀ x ∈ L, w.vec x = c)
    (hsum : wsum w = 0) :
    ∃ T : Finset (Fin k), (∀ x, w.vec x = if x ∈ T then 1 else 0) ∧ Even T.card ∧
      (T.card + L.card ≤ k ∨ L.card ≤ T.card) := by
  classical
  have hz : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  refine ⟨Finset.univ.filter fun x => w.vec x = 1, ?_, ?_, ?_⟩
  · intro x
    rcases hz (w.vec x) with h | h <;> simp [h]
  · have h1 : (∑ x, w.vec x) = ((Finset.univ.filter fun x => w.vec x = 1).card : ZMod 2) := by
      rw [← Finset.sum_boole]
      refine Finset.sum_congr rfl fun x _ => ?_
      rcases hz (w.vec x) with h | h <;> simp [h]
    have h2 : (((Finset.univ.filter fun x => w.vec x = 1).card : ℕ) : ZMod 2) = 0 := by
      rw [← h1]
      exact hsum
    exact (ZMod.natCast_eq_zero_iff_even).mp h2
  · rcases hz c with h | h
    · left
      have hsub : (Finset.univ.filter fun x => w.vec x = 1) ⊆ Lᶜ := by
        intro x hx
        rw [Finset.mem_compl]
        intro hxL
        have := hc x hxL
        rw [Finset.mem_filter] at hx
        rw [hx.2, h] at this
        exact absurd this (by decide)
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_compl, Fintype.card_fin] at h1
      have h2 := Finset.card_le_univ L
      rw [Fintype.card_fin] at h2
      omega
    · right
      have hsub : L ⊆ (Finset.univ.filter fun x => w.vec x = 1) := by
        intro x hxL
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ _, by rw [hc x hxL, h]⟩
      exact Finset.card_le_card hsub

theorem eq_one_of_weight_zero {w : Wr k} (hw : w.perm = 1) {T : Finset (Fin k)}
    (hT : ∀ x, w.vec x = if x ∈ T then 1 else 0) (h0 : T.card = 0) : w = 1 := by
  have hTe : T = ∅ := Finset.card_eq_zero.mp h0
  refine Wr.ext (funext fun x => ?_) hw
  rw [hT x, hTe]
  simp [Wr.one_vec]

theorem mkQ_eq_one_of_weight_full {w : Wr k} (hw : w.perm = 1) {T : Finset (Fin k)}
    (hT : ∀ x, w.vec x = if x ∈ T then 1 else 0) (h0 : T.card = k) : mkQ k w = 1 := by
  have hTe : T = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [h0, Fintype.card_fin]
  have : w = allOnes k := by
    refine Wr.ext (funext fun x => ?_) hw
    rw [hT x, hTe]
    simp [allOnes]
  rw [this]
  exact (QuotientGroup.eq_one_iff _).mpr (Or.inr rfl)

end Weight

section Five

theorem eq_one_of_layer {w : Wr k} (hk5 : 5 ≤ k) (hk6 : k ≤ 6) (hw : w ∈ aeSub k)
    (hns : ¬ Group.IsSolvable ↥(Ea (aeMembers k Set.univ) (mkQ k w))) : mkQ k w = 1 := by
  obtain ⟨α, -, α', -, hne, hα, hα'⟩ := exists_pair_of_not_isSolvable hns
  have hperm : w.perm = 1 := perm_eq_one_of_pair (by omega) hw.2 hα hα' hne
  obtain ⟨hcard, c, hconst⟩ := exists_level_set hk5 (by omega) hperm hα hα' hne
  obtain ⟨T, hT, ⟨m, hm⟩, hdich⟩ := weight_dichotomy hconst hw.1
  have hTle : T.card ≤ k := by
    have := Finset.card_le_univ T
    rwa [Fintype.card_fin] at this
  have hcases : T.card = 0 ∨ T.card = k := by omega
  rcases hcases with h0 | hk
  · rw [eq_one_of_weight_zero hperm hT h0, map_one]
  · exact mkQ_eq_one_of_weight_full hperm hT hk

theorem modelNoLayer_five : ModelNoLayer 5 Set.univ ((AE.aeSub 5).map (AE.mkQ 5)) := by
  rintro a ⟨w, hw, rfl⟩ ⟨hne, -, -, hns⟩
  exact hne (eq_one_of_layer (by norm_num) (by norm_num) hw hns)

theorem modelNoLayer_six : ModelNoLayer 6 Set.univ ((AE.aeSub 6).map (AE.mkQ 6)) := by
  rintro a ⟨w, hw, rfl⟩ ⟨hne, -, -, hns⟩
  exact hne (eq_one_of_layer (by norm_num) (by norm_num) hw hns)

end Five

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7
