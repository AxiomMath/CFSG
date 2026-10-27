module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE4T
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R7LemLE64
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23R8L7E4Sp6
public import Certificates.Certificate507402

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.EvenSmallLie.Sp6 CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Co3
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6 CFSG.ClassicalInvolution.Q3.TL4.E4C
  CFSG.ClassicalInvolution.Q3.TL4.E4Sp6Data
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.L7

theorem not_hasS3Quot_of_isPGroup {E : Type} [Group E] (h : IsPGroup 2 E) : ¬ HasS3Quot E := by
  rintro ⟨π, hπ⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := (h.of_surjective π hπ).exists_card_eq
  have h6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm]
    rfl
  rw [h6] at hn
  have h3 : (3 : ℕ) ∣ 2 ^ n := ⟨2, by omega⟩
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem not_hasS3Quot_of_le_commutator {M : Type} [Group M] {H : Subgroup M} (h : H ≤ ⁅H, H⁆) :
    ¬ HasS3Quot ↥H :=
  not_hasS3Quot_of_perfect (commutator_eq_top_of_perfect (le_antisymm (Subgroup.commutator_le_self H) h))

theorem commAll_of_forall_mem {g : Equiv.Perm (Fin 36)} {l l' : List (Equiv.Perm (Fin 36))}
    (h : commAll g l = true) (hl : ∀ x ∈ l', x ∈ l) : commAll g l' = true := by
  simp only [commAll, List.all_eq_true] at h ⊢
  exact fun x hx => h x (hl x hx)

theorem twinPerf_parts :
    (∃ c ∈ enumeration sp6CentQ2, commAll c (L0 ()) = true ∧ commAll c (L1 ()) = true ∧ c ≠ 1 ∧
      ¬ ∀ k < (ws ()).length, k = 0 ∨ k = 11 ∨
        ¬ commAll c (memberElems (L0 ()) ((ws ()).getD k 1)) = true) ∧
    ∀ c ∈ enumeration sp6CentQ2, commAll c (L0 ()) = true → commAll c (L1 ()) = true → c ≠ 1 →
      (¬ ∀ k < (ws ()).length, k = 0 ∨ k = 11 ∨
        ¬ commAll c (memberElems (L0 ()) ((ws ()).getD k 1)) = true) →
      ∀ k < (ws ()).length, commAll c (memberElems (L0 ()) ((ws ()).getD k 1)) = true →
      ∀ x ∈ memberElems (L0 ()) ((ws ()).getD k 1), ∃ e ∈ perfWords,
        commAll c (memberElems (L0 ()) ((ws ()).getD (e.getD 1 0) 1)) = true ∧
        commAll c (memberElems (L0 ()) ((ws ()).getD (e.getD 2 0) 1)) = true ∧
        ∃ y ∈ memberElems (L0 ()) ((ws ()).getD (e.getD 1 0) 1),
          ∃ z ∈ memberElems (L0 ()) ((ws ()).getD (e.getD 2 0) 1), y * z * y⁻¹ * z⁻¹ = x := by
  have h := Certificates.certificate507402
  simp only [twinPerfCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨hne, hall⟩ := h
  refine ⟨?_, fun c hQ hL0 hL1 h1 hw k hk hck x hx => ?_⟩
  · obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ (List.isEmpty_eq_false_iff.mp hne)
    simp only [List.mem_filter, List.mem_map, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at hc
    obtain ⟨⟨⟨a, ha, rfl⟩, hL0, hL1⟩, h1, hw⟩ := hc
    refine ⟨tab a, by rw [tab_eq]; exact ha, hL0, hL1, h1, fun hall => ?_⟩
    rw [Bool.eq_false_iff] at hw
    apply hw
    refine List.all_eq_true.2 fun k hk => ?_
    rcases hall k (List.mem_range.1 hk) with h0 | h11 | hnc
    · simp [h0]
    · simp [h11]
    · rw [Bool.not_eq_true] at hnc
      simp only [hnc, Bool.not_false, Bool.or_true]
  ·
    have hlay : ((∃ a ∈ enumeration sp6CentQ2, tab a = c) ∧ commAll c (L0 ()) = true ∧
        commAll c (L1 ()) = true) ∧ decide (c = 1) = false ∧
        ((List.range (ws ()).length).all fun k =>
          k == 0 || k == 11 || !commAll c (memberElems (L0 ()) ((ws ()).getD k 1))) = false := by
      refine ⟨⟨⟨c, hQ, tab_eq c⟩, hL0, hL1⟩, decide_eq_false h1, ?_⟩
      rw [Bool.eq_false_iff]
      intro hall
      apply hw
      intro k hk
      have := List.all_eq_true.1 hall k (List.mem_range.2 hk)
      simpa only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', Bool.not_eq_true, or_assoc] using this
    simp only [List.all_eq_true, List.mem_filter, List.mem_map, Bool.and_eq_true, Bool.or_eq_true,
      List.any_eq_true, List.mem_range, Bool.not_eq_true', decide_eq_true_eq] at hall
    rcases hall c hlay k hk with h0 | h
    · rw [hck] at h0
      exact absurd h0 (by decide)
    · obtain ⟨e, he, ⟨⟨-, h1⟩, h2⟩, y, hy, z, hz, hyz⟩ := h x hx
      exact ⟨e, he, h1, h2, y, hy, z, hz, hyz⟩

theorem e4S3TwinW_sp6
    {M : Type} [Group M] [Finite M] (hM : CFSG.Blueprint.LieModel M .PSp 3 2 1) : E4S3TwinW M := by
  intro K K' s hq hinv htw hK' hne hle _ a haK haK'
  obtain ⟨y, rfl⟩ := hK'
  obtain ⟨φ, hφ, hrange, hs, hKφ, hK'φ⟩ := exists_twin_emb hM hq hinv htw hne hle
  have hmem : ∀ m, φ m ∈ co3X36 := fun m => hrange ▸ ⟨m, rfl⟩
  obtain ⟨eK⟩ := hq
  have hK2 : IsPGroup 2 ↥K := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr eK.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]; norm_num)
  have hpull : ∀ k, ∃ m, (conjSub m K).map φ = conjSub ((ws ()).getD k 1) K0 := fun k => by
    obtain ⟨m, hm⟩ : ∃ m, φ m = (ws ()).getD k 1 := by
      have := E4Sp6.ws_mem k
      rw [← hrange] at this
      exact this
    exact ⟨m, by rw [AscQuot.map_conjSub, hKφ, hm]⟩
  have hmemb : ∀ {k m} {w : Equiv.Perm (Fin 36)}, (conjSub m K).map φ = conjSub ((ws ()).getD k 1) K0 →
      w ∈ memberElems (L0 ()) ((ws ()).getD k 1) → ∃ w₀ ∈ conjSub m K, φ w₀ = w := by
    intro k m w hm hw
    have : w ∈ (conjSub m K).map φ := by
      rw [hm]
      exact (mem_memberElems_iff _ w).1 hw
    exact this
  by_cases h : ∀ k < (ws ()).length, k = 0 ∨ k = 11 ∨
      ¬ commAll (φ a) (memberElems (L0 ()) ((ws ()).getD k 1)) = true
  ·
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hK2' : IsPGroup 2 ↥(conjSub y K) := Vtx.isPGroup_of_mem_conjClass hK2 ⟨y, rfl⟩
    exact not_hasS3Quot_of_isPGroup
      ((hK2.to_sup_of_normal_left' hK2' hle).to_le (Ea_le_sup hφ hmem hKφ hK'φ h))
  refine not_hasS3Quot_of_le_commutator ?_
  by_cases ha1 : a = 1
  ·
    subst ha1
    obtain ⟨c, hcQ, hcL0, hcL1, hc1, hcw⟩ := twinPerf_parts.1
    obtain ⟨k₀, hk₀, hek₀⟩ := E4Sp6.exists_member (hmem 1)
    rw [map_one, conjSub_one] at hek₀
    have hc0 : commAll c (memberElems (L0 ()) ((ws ()).getD k₀ 1)) = true :=
      commAll_of_forall_mem hcL0 fun w hw => by
        rw [← E4Sp6.mem_K0_iff, hek₀]
        exact (mem_memberElems_iff _ w).1 hw
    refine Ea_le fun J hJ _ => ?_
    obtain ⟨m, rfl⟩ := hJ
    intro x hx
    rw [mem_conjSub_iff] at hx
    have hk0 : φ (m⁻¹ * x * m) ∈ memberElems (L0 ()) ((ws ()).getD k₀ 1) :=
      (mem_memberElems_iff _ _).2 (by rw [← hek₀, ← hKφ]; exact Subgroup.mem_map_of_mem φ hx)
    obtain ⟨e, -, -, -, y', hy', z', hz', hyz⟩ :=
      twinPerf_parts.2 c hcQ hcL0 hcL1 hc1 hcw k₀ hk₀ hc0 _ hk0
    obtain ⟨m₁, hm₁⟩ := hpull (e.getD 1 0)
    obtain ⟨m₂, hm₂⟩ := hpull (e.getD 2 0)
    obtain ⟨y₀, hy₀K, rfl⟩ := hmemb hm₁ hy'
    obtain ⟨z₀, hz₀K, rfl⟩ := hmemb hm₂ hz'
    have hk : m⁻¹ * x * m = y₀ * z₀ * y₀⁻¹ * z₀⁻¹ :=
      hφ (by rw [← hyz]; simp only [map_mul, map_inv])
    have hx' : x = (m * y₀ * m⁻¹) * (m * z₀ * m⁻¹) * (m * y₀ * m⁻¹)⁻¹ * (m * z₀ * m⁻¹)⁻¹ :=
      calc x = m * (m⁻¹ * x * m) * m⁻¹ := by group
        _ = m * (y₀ * z₀ * y₀⁻¹ * z₀⁻¹) * m⁻¹ := by rw [hk]
        _ = _ := by group
    have hcent : ∀ J : Subgroup M, J ≤ Subgroup.centralizer ({1} : Set M) := fun J w _ => by
      rw [Subgroup.mem_centralizer_singleton_iff, one_mul, mul_one]
    have hy1 : m * y₀ * m⁻¹ ∈ Ea (CoreAssembly.conjClass K) 1 := by
      have hJ : conjSub (m * m₁) K ∈ CoreAssembly.conjClass K := ⟨m * m₁, rfl⟩
      refine le_Ea hJ (hcent _) ?_
      rw [conjSub_mul]
      exact conj_mem_conjSub hy₀K
    have hz1 : m * z₀ * m⁻¹ ∈ Ea (CoreAssembly.conjClass K) 1 := by
      have hJ : conjSub (m * m₂) K ∈ CoreAssembly.conjClass K := ⟨m * m₂, rfl⟩
      refine le_Ea hJ (hcent _) ?_
      rw [conjSub_mul]
      exact conj_mem_conjSub hz₀K
    rw [hx']
    exact Subgroup.commutator_mem_commutator hy1 hz1
  ·
    have hQ : φ a ∈ enumeration sp6CentQ2 := by
      refine mem_enumeration_of_comm (hmem a) ?_
      rw [← hs, ← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp (haK hinv.mem)]
    have hL0 : commAll (φ a) (L0 ()) = true := commAll_of_le_centralizer φ haK fun x hx => by
      rw [hKφ]
      exact (E4Sp6.mem_K0_iff x).2 hx
    have hL1 : commAll (φ a) (L1 ()) = true := commAll_of_le_centralizer φ haK' fun x hx => by
      rw [hK'φ]
      exact (mem_L1_iff x).1 hx
    have h1 : φ a ≠ 1 := fun h1 => ha1 (hφ (by rw [h1, map_one]))
    refine Ea_le fun J hJ hJa => ?_
    obtain ⟨m, rfl⟩ := hJ
    have hJφ : (conjSub m K).map φ = conjSub (φ m) K0 := by rw [AscQuot.map_conjSub, hKφ]
    obtain ⟨k, hk, hek⟩ := E4Sp6.exists_member (hmem m)
    have hcomm : commAll (φ a) (memberElems (L0 ()) ((ws ()).getD k 1)) = true :=
      commAll_of_le_centralizer φ hJa fun x hx => by
        rw [hJφ, hek]
        exact (mem_memberElems_iff _ x).1 hx
    intro x hx
    have hxk : φ x ∈ memberElems (L0 ()) ((ws ()).getD k 1) :=
      (mem_memberElems_iff _ _).2 (by rw [← hek, ← hJφ]; exact Subgroup.mem_map_of_mem φ hx)
    obtain ⟨e, -, h1, h2, y', hy', z', hz', hyz⟩ :=
      twinPerf_parts.2 (φ a) hQ hL0 hL1 h1 h k hk hcomm (φ x) hxk
    obtain ⟨m₁, hm₁⟩ := hpull (e.getD 1 0)
    obtain ⟨m₂, hm₂⟩ := hpull (e.getD 2 0)
    have hJ₁ : conjSub m₁ K ≤ Subgroup.centralizer ({a} : Set M) :=
      le_centralizer_of_commAll hφ (fun w hw => (mem_memberElems_iff _ w).2 (by rwa [hm₁] at hw)) h1
    have hJ₂ : conjSub m₂ K ≤ Subgroup.centralizer ({a} : Set M) :=
      le_centralizer_of_commAll hφ (fun w hw => (mem_memberElems_iff _ w).2 (by rwa [hm₂] at hw)) h2
    obtain ⟨y₀, hy₀K, rfl⟩ := hmemb hm₁ hy'
    obtain ⟨z₀, hz₀K, rfl⟩ := hmemb hm₂ hz'
    have hx' : x = y₀ * z₀ * y₀⁻¹ * z₀⁻¹ := hφ (by rw [← hyz]; simp only [map_mul, map_inv])
    have hJm₁ : conjSub m₁ K ∈ CoreAssembly.conjClass K := ⟨m₁, rfl⟩
    have hJm₂ : conjSub m₂ K ∈ CoreAssembly.conjClass K := ⟨m₂, rfl⟩
    rw [hx']
    exact Subgroup.commutator_mem_commutator (le_Ea hJm₁ hJ₁ hy₀K) (le_Ea hJm₂ hJ₂ hz₀K)

theorem e4S3TwinModel_of_certs :
    E4S3TwinModel := by
  intro M _ _ hM
  rcases hM with hM | hM
  · exact e4S3TwinW_sp6 hM
  · intro K K' s hq hinv htw _ _ _ hperp
    obtain ⟨J₁, J₂, hJ₁, hJ₂, hJ₁K, hJ₂K, hJ₁₂, hn₁, hn₂⟩ :=
      TwinDisc.e4O8TwinModel_of_certs M hM K s hq hinv htw
    exact absurd ((hperp J₁ hJ₁ hJ₁K hn₁).trans (hperp J₂ hJ₂ hJ₂K hn₂).symm) hJ₁₂

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.LemL
