module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Simple2S5

@[expose] def IsSylow2In {G : Type*} [Group G] (S T : Subgroup G) : Prop :=
  T ≤ S ∧ IsPGroup 2 ↥T ∧ ¬ 2 ∣ T.relIndex S

theorem isSylow2In_of_card {G : Type*} [Group G] [Finite G] {Y T : Subgroup G} (hTY : T ≤ Y)
    (hT : Nat.card ↥T = 16) (hY : Nat.card ↥Y = 240) : IsSylow2In Y T := by
  refine ⟨hTY, IsPGroup.of_card (n := 4) (by rw [hT]; norm_num), ?_⟩
  have hcard : Nat.card ↥(T.subgroupOf Y) = 16 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTY).toEquiv, hT]
  have hidx : (T.subgroupOf Y).index = 15 := by
    have h := Subgroup.card_mul_index (H := T.subgroupOf Y)
    rw [hcard, hY] at h
    omega
  show ¬ 2 ∣ (T.subgroupOf Y).index
  rw [hidx]
  norm_num

theorem sylow_of_center {G : Type*} [Group G] [Finite G] {S T : Subgroup G} {t₀ : G}
    (hYcard : Nat.card ↥(S ⊓ Subgroup.centralizer ({t₀} : Set G)) = 240)
    (hTY : T ≤ S ⊓ Subgroup.centralizer ({t₀} : Set G)) (hTcard : Nat.card ↥T = 16)
    (ht₀T : t₀ ∈ T) (ht₀1 : t₀ ≠ 1)
    (hcen : ∀ x ∈ T, (∀ y ∈ T, x * y = y * x) → x = 1 ∨ x = t₀) :
    IsSylow2In S T := by
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  let Y : Subgroup G := S ⊓ Subgroup.centralizer ({t₀} : Set G)
  have hYcard' : Nat.card ↥Y = 240 := hYcard
  have hTY' : T ≤ Y := hTY
  have hYS : Y ≤ S := inf_le_left
  have hTS : T ≤ S := hTY'.trans hYS
  refine ⟨hTS, IsPGroup.of_card (n := 4) (by rw [hTcard]; norm_num), ?_⟩
  let T' : Subgroup ↥S := T.subgroupOf S
  have hT'card : Nat.card ↥T' = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTS).toEquiv).trans hTcard
  have hT'p : IsPGroup 2 T' := IsPGroup.of_card (n := 4) (by rw [hT'card]; norm_num)
  obtain ⟨P, hT'P⟩ := hT'p.exists_le_sylow
  have hclaim : T' = (P : Subgroup ↥S) := by
    by_contra hne
    have hnotle : ¬ (P : Subgroup ↥S) ≤ T' := fun hle => hne (le_antisymm hT'P hle)
    let H : Subgroup ↥P := T'.subgroupOf (P : Subgroup ↥S)
    have hHtop : H ≠ ⊤ := fun h => hnotle (Subgroup.subgroupOf_eq_top.mp h)
    have hHlt : H < ⊤ := lt_of_le_of_ne le_top hHtop
    haveI : Group.IsNilpotent ↥P := P.isPGroup'.isNilpotent
    have hnc : NormalizerCondition ↥P := Group.normalizerCondition_of_isNilpotent
    have hproper : H < Subgroup.normalizer H := hnc H hHlt
    obtain ⟨n, hnmem, hnnot⟩ : ∃ n : ↥P, n ∈ Subgroup.normalizer H ∧ n ∉ H := by
      by_contra h
      push Not at h
      exact hproper.ne (le_antisymm Subgroup.le_normalizer h)
    let nS : ↥S := n.1
    let n0 : G := (nS : G)
    have hnS_P : nS ∈ (P : Subgroup ↥S) := n.2
    have hnS_notT' : nS ∉ T' := fun h => hnnot (Subgroup.mem_subgroupOf.mpr h)
    have hn0_S : n0 ∈ S := nS.2
    have hn0_notT : n0 ∉ T := fun h => hnS_notT' (Subgroup.mem_subgroupOf.mpr h)
    have hnS_norm : nS ∈ Subgroup.normalizer T' := by
      have hmap : H.map (P : Subgroup ↥S).subtype = T' := by
        show (T'.subgroupOf (P : Subgroup ↥S)).map (P : Subgroup ↥S).subtype = T'
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT'P]
      have hmem : nS ∈ (Subgroup.normalizer H).map (P : Subgroup ↥S).subtype :=
        ⟨n, hnmem, rfl⟩
      have h := Subgroup.le_normalizer_map (H := H) (f := (P : Subgroup ↥S).subtype) hmem
      rwa [hmap] at h
    have hTmap : T'.map S.subtype = T := Subgroup.map_subgroupOf_eq_of_le hTS
    have hn0_norm : n0 ∈ Subgroup.normalizer T := by
      have hmem : n0 ∈ (Subgroup.normalizer T').map S.subtype := ⟨nS, hnS_norm, rfl⟩
      have h := Subgroup.le_normalizer_map (H := T') (f := S.subtype) hmem
      rwa [hTmap] at h
    have hconj1 : ∀ y : G, y ∈ T → n0 * y * n0⁻¹ ∈ T :=
      fun y hy => (Subgroup.mem_normalizer_iff.mp hn0_norm y).mp hy
    have hconj2 : ∀ y : G, y ∈ T → n0⁻¹ * y * n0 ∈ T := by
      intro y hy
      exact (Subgroup.mem_normalizer_iff.mp hn0_norm (n0⁻¹ * y * n0)).mpr
        (by simpa [mul_assoc] using hy)
    let x : G := n0 * t₀ * n0⁻¹
    have hxT : x ∈ T := hconj1 t₀ ht₀T
    have hx1 : x ≠ 1 := by
      intro hx
      apply ht₀1
      have h := congrArg (fun z => n0⁻¹ * z * n0) hx
      simpa [x, mul_assoc] using h
    have hxcomm : ∀ y ∈ T, x * y = y * x := by
      intro y hy
      have hz : n0⁻¹ * y * n0 ∈ Subgroup.centralizer ({t₀} : Set G) :=
        (hTY' (hconj2 y hy)).2
      have hcy := (Subgroup.mem_centralizer_iff.mp hz) t₀ (Set.mem_singleton t₀)
      have h := congrArg (fun z => n0 * z * n0⁻¹) hcy
      simpa [x, mul_assoc] using h
    have hxeq : x = t₀ := (hcen x hxT hxcomm).resolve_left hx1
    have hn0_t₀_comm : t₀ * n0 = n0 * t₀ := by
      have h4 : n0 * t₀ = t₀ * n0 := by
        have h3 : (n0 * t₀ * n0⁻¹) * n0 = t₀ * n0 := by
          have h := congrArg (fun z : G => z * n0) hxeq
          exact h
        rw [mul_assoc (n0 * t₀) n0⁻¹ n0, inv_mul_cancel n0, mul_one] at h3
        exact h3
      exact h4.symm
    have hn0_cen : n0 ∈ Subgroup.centralizer ({t₀} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact hn0_t₀_comm
    have hn0_Y : n0 ∈ Y := ⟨hn0_S, hn0_cen⟩
    let T₂ : Subgroup G := Subgroup.closure ((T : Set G) ∪ {n0})
    have hTT₂ : T ≤ T₂ := fun z hz => Subgroup.subset_closure (Or.inl hz)
    have hn0_T₂ : n0 ∈ T₂ := Subgroup.subset_closure (Or.inr (Set.mem_singleton n0))
    have hT₂Y : T₂ ≤ Y := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hz | hz
      · exact hTY' hz
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hn0_Y
    let Q : Subgroup G := (P : Subgroup ↥S).map S.subtype
    have hTQ : T ≤ Q := by
      have h := Subgroup.map_mono (f := S.subtype) hT'P
      rwa [hTmap] at h
    have hn0_Q : n0 ∈ Q := ⟨nS, hnS_P, rfl⟩
    have hT₂Q : T₂ ≤ Q := by
      rw [Subgroup.closure_le]
      intro z hz
      rcases hz with hz | hz
      · exact hTQ hz
      · rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hn0_Q
    have hT₂p : IsPGroup 2 T₂ := (P.isPGroup'.map S.subtype).to_le hT₂Q
    have hlt : T < T₂ := lt_of_le_of_ne hTT₂ (fun h => hn0_notT (h ▸ hn0_T₂))
    have hcardlt : Nat.card ↥T < Nat.card ↥T₂ := Subgroup.card_lt_of_lt hlt
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hT₂p
    have hdvd : Nat.card ↥T₂ ∣ Nat.card ↥Y := Subgroup.card_dvd_of_le hT₂Y
    rw [hm, hYcard'] at hdvd
    have hdvd' : 2 ^ m ∣ 16 * 15 := by
      rwa [show (240 : ℕ) = 16 * 15 by norm_num] at hdvd
    have hcop : Nat.Coprime (2 ^ m) 15 :=
      ((by norm_num : Nat.Coprime (2 : ℕ) 15)).pow_left m
    have hdvd16 : 2 ^ m ∣ 16 := hcop.dvd_of_dvd_mul_right hdvd'
    have hle : 2 ^ m ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd16
    rw [hTcard, hm] at hcardlt
    omega
  have hrel : T.relIndex S = (P : Subgroup ↥S).index := by
    change T'.index = (P : Subgroup ↥S).index
    rw [hclaim]
  rw [hrel]
  exact Sylow.not_dvd_index P

theorem IsSylow2In.card_le_of_pGroup {G : Type*} [Group G] [Finite G] {S T R : Subgroup G}
    (h : IsSylow2In S T) (hT : Nat.card ↥T = 16) (hRS : R ≤ S) (hR : IsPGroup 2 ↥R) :
    Nat.card ↥R ≤ 16 := by
  haveI : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hR
  have hcardS : Nat.card ↥S = 16 * (T.subgroupOf S).index := by
    have hc : Nat.card ↥(T.subgroupOf S) = 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.1).toEquiv, hT]
    have hh := Subgroup.card_mul_index (H := T.subgroupOf S)
    rw [hc] at hh
    exact hh.symm
  have hodd : ¬ 2 ∣ (T.subgroupOf S).index := h.2.2
  have hdvd : Nat.card ↥R ∣ Nat.card ↥S := Subgroup.card_dvd_of_le hRS
  rw [hm, hcardS] at hdvd
  have hcop : Nat.Coprime (2 ^ m) (T.subgroupOf S).index :=
    (Nat.prime_two.coprime_iff_not_dvd.mpr hodd).pow_left m
  have hdvd16 : 2 ^ m ∣ 16 := hcop.dvd_of_dvd_mul_right hdvd
  have hle : 2 ^ m ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd16
  rw [hm]
  exact hle

end CFSG.EvenSporadicStandard.HNRecog.Simple2S5
