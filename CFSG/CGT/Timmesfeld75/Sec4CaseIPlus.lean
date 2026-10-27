module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIFusion2
public import CFSG.CGT.Timmesfeld75.Sec4CaseIFour

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

section Defs

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G}

@[expose] def sec4F (T T₁ T₂ : Subgroup G) : Set G :=
  {z | ∃ g ∈ Subgroup.normalizer (T : Set G), ∃ a ∈ normIn T₁ T, ∃ b ∈ normIn T₂ T,
    z = g * (a * b) * g⁻¹}

theorem sec4F_conj {z n : G} (hz : z ∈ sec4F T T₁ T₂) (hn : n ∈ Subgroup.normalizer (T : Set G)) :
    n * z * n⁻¹ ∈ sec4F T T₁ T₂ := by
  obtain ⟨m, hm, a, ha, b, hb, rfl⟩ := hz
  exact ⟨n * m, (Subgroup.normalizer (T : Set G)).mul_mem hn hm, a, ha, b, hb, by group⟩

@[expose] def Sec4FourHolds (T T₁ T₂ : Subgroup G) : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → sec4R T T₁ T₂ ≤ S →
    Subgroup.closure ((S : Set G) ∩ classD T) = sec4R T T₁ T₂

@[expose] def Sec4PlusHolds (T T₁ T₂ : Subgroup G) : Prop :=
  ∀ S : Subgroup G, IsPGroup 2 S → sec4R T T₁ T₂ ≤ S → S ≤ Subgroup.normalizer (T : Set G) →
    ∀ z ∈ (S : Set G) ∩ sec4F T T₁ T₂, z ∈ sec4R T T₁ T₂

@[expose] def Sec4I5OuterAction : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G], (∃ a b : G, a * b ≠ b * a) →
    SimpleCaseUpTo (Nat.card G) →
    ∀ (T T₁ T₂ : Subgroup G) (a : G), Sec4Hyp T T₁ a T₂ →
    2 * Nat.card (normIn T T₁) < Nat.card T → Nat.card T ≠ 16 →
      ∀ S : Subgroup G, IsPGroup 2 S → sec4R T T₁ T₂ ≤ S → S ≤ Subgroup.normalizer (T : Set G) →
        ∀ w ∈ S, w ∈ sec4F T T₁ T₂ → w ∈ Subgroup.normalizer (sec4R T T₁ T₂ : Set G) →
          w ∉ sec4R T T₁ T₂ → (∀ t ∈ T, ¬ Sec4ActsTriv T T₁ T₂ (w * t)) → False

end Defs

section Plus

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a : G}

theorem Sec4Hyp.sec4FourHolds
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction)
    (hC : Sec4I4OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) :
    Sec4FourHolds T T₁ T₂ := fun _ hS hRS =>
  h.closure_inter_classD_eq hnab hind hAsc hA hC hq h16 hS hRS

theorem Sec4Hyp.sec4PlusHolds
    [IsSimpleGroup G] (hnab : ∃ a b : G, a * b ≠ b * a) (hind : SimpleCaseUpTo (Nat.card G))
    (hAsc : AschbacherNoPolarInput)
    (hA : Sec4I4TrivialAction)
    (hC : Sec4I4OuterAction) (hC' : Sec4I5OuterAction) (h : Sec4Hyp T T₁ a T₂)
    (hq : 2 * Nat.card (normIn T T₁) < Nat.card T) (h16 : Nat.card T ≠ 16) :
    Sec4PlusHolds T T₁ T₂ := by
  intro S hS hRS hSN z hz
  by_contra hzR
  have hTab := h.pair.wc.1
  set Δ : Set G := (S : Set G) ∩ (sec4E T T₁ T₂ ∪ sec4F T T₁ T₂) with hΔdef
  have hΔS : Δ ⊆ (S : Set G) := Set.inter_subset_left
  have hΔ : ∀ s ∈ S, ∀ d ∈ Δ, s * d * s⁻¹ ∈ Δ := fun s hs d hd =>
    ⟨S.mul_mem (S.mul_mem hs hd.1) (S.inv_mem hs), hd.2.elim
      (fun hE => Or.inl (sec4E_conj hE (hSN hs))) (fun hF => Or.inr (sec4F_conj hF (hSN hs)))⟩
  have hR : Subgroup.closure (Δ ∩ (sec4R T T₁ T₂ : Set G)) = sec4R T T₁ T₂ := by
    refine le_antisymm ((Subgroup.closure_le _).2 Set.inter_subset_right) ?_
    calc sec4R T T₁ T₂ = Subgroup.closure ((sec4R T T₁ T₂ : Set G) ∩ classD T) :=
          h.closure_sec4R_inter_eq.symm
      _ ≤ Subgroup.closure (Δ ∩ (sec4R T T₁ T₂ : Set G)) :=
          Subgroup.closure_mono fun d hd => ⟨⟨hRS hd.1, Or.inl (subset_sec4E hd.2 hd.1)⟩, hd.1⟩
  have hne : Subgroup.closure Δ ≠ sec4R T T₁ T₂ := fun hcl =>
    hzR (hcl ▸ Subgroup.subset_closure ⟨hz.1, Or.inr hz.2⟩)
  obtain ⟨w, hwΔ, hwN, hwR⟩ := exists_mem_normalizer_of_closure_ne hS hΔS hΔ hRS hR hne
  have hwS : w ∈ S := hwΔ.1
  have hwT : w ∈ Subgroup.normalizer (T : Set G) := hSN hwS
  rcases hwΔ.2 with hwE | hwF
  · apply hwR
    have hmem : w ∈ Subgroup.closure ((S : Set G) ∩ sec4E T T₁ T₂) :=
      Subgroup.subset_closure ⟨hwS, hwE⟩
    rwa [h.closure_inter_sec4E_eq hnab hind hAsc hA hC hq h16 hS hRS hSN] at hmem
  · by_cases hI : ∃ t ∈ T, Sec4ActsTriv T T₁ T₂ (w * t)
    · obtain ⟨t, htT, hact⟩ := hI
      obtain ⟨g, hg, a', ha, b', hb, hwg⟩ := hwF
      have hwtT : w * t ∈ Subgroup.normalizer (T : Set G) :=
        (Subgroup.normalizer (T : Set G)).mul_mem hwT (Subgroup.le_normalizer htT)
      have hab : a' * b' ∈ sec4N T T₁ T₂ :=
        (sec4N T T₁ T₂).mul_mem (normIn_le_sec4N_mid ha) (normIn_le_sec4N_right hb)
      have hLC : normIn T T₁ ≤ T ⊓ Subgroup.centralizer ({a' * b'} : Set G) := fun l hl =>
        ⟨normIn_le _ _ hl, Subgroup.mem_centralizer_singleton_iff.2
          (elemAbelian_mul_comm h.isElemAbelian_sec4N (normIn_le_sec4N_left hl) hab)⟩
      have hCt : Nat.card (normIn T T₁) ≤
          Nat.card ↥(T ⊓ Subgroup.centralizer ({w * t} : Set G)) := by
        rw [inf_centralizer_mul_eq hTab htT, hwg, card_inf_centralizer_conj_of_mem_normalizer hg]
        exact Subgroup.card_le_of_le hLC
      have hPL := h.commute_sec4N_of_actsTriv hAsc hq hact hwtT hCt
      have hcent : ∀ m ∈ sec4N T T₁ T₂, w * m * w⁻¹ * m⁻¹ ∈ T := by
        intro m hm
        have hm' : t⁻¹ * m * t ∈ sec4N T T₁ T₂ := by
          have := (Subgroup.mem_normalizer_iff.1 (h.left_le_normalizer_sec4N (T.inv_mem htT))
            m).1 hm
          simpa using this
        have e : w * m * w⁻¹ * m⁻¹ = ((w * t) * (t⁻¹ * m * t) * (w * t)⁻¹) * m⁻¹ := by group
        rw [e, hPL _ hm']
        have e2 : t⁻¹ * m * t * m⁻¹ = t⁻¹ * (m * t * m⁻¹) := by group
        rw [e2]
        exact T.mul_mem (T.inv_mem htT)
          (conj_mem_of_mem_normalizer (sec4N_le_normalizer_left hm) htT)
      exact hwR (h.mem_sec4R_of_conj_centralizes hnab hind hAsc hA hC hq h16 hg ha hb hwT hwg hcent)
    · exact hC' G hnab hind T T₁ T₂ a h hq h16 S hS hRS hSN w hwS hwF hwN hwR
        fun t ht hact => hI ⟨t, ht, hact⟩

end Plus

end CFSG.CGT.Timmesfeld75
