module

public import CFSG.ClassicalInvolution.Asc77.AscMuTabAbel
public import CFSG.ClassicalInvolution.Asc77.AscP1SevenGraphAllWire

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Asc77.Thompson

namespace MuTab

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

omit [Finite G] in
theorem mem_omegaNbr_of_commutes {K J : Subgroup G} (hJ : J ∈ Ω) (hne : J ≠ K)
    (h : ∀ a ∈ K, ∀ b ∈ J, a * b = b * a) : J ∈ omegaNbr Ω K := by
  refine ⟨hJ, hne, ?_⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥J) := inferInstance
  refine ⟨Subgroup.map J.subtype (P : Subgroup ↥J), ⟨J, hJ, P, rfl⟩,
    Subgroup.map_subtype_le _, ?_⟩
  rintro _ ⟨r, -, rfl⟩
  refine Subgroup.centralizer_le_normalizer (K : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact h k hk r r.2

noncomputable def memberOf (d : ↥(muGroup Ω W)) : Subgroup G :=
  open Classical in
  if h : d ∈ muDelta Ω W then (Classical.choose (exists_rep_of_mem_muDelta h)).K else ⊥

section Cent

variable (hP : PartIHyp p f Ω) (hW : W ∈ WSet Ω)

include hP hW

theorem memberOf_muTabElt (ρ : Rep Ω W) : memberOf (muTabElt ρ) = ρ.K := by
  classical
  have hm := muTabElt_mem ρ
  unfold memberOf
  simp only [hm, ↓reduceDIte]
  have := Classical.choose_spec (exists_rep_of_mem_muDelta hm)
  exact ((muTabElt_eq_iff hP hW _ ρ).mp this.symm)

theorem ncard_cent_le (ρ : Rep Ω W) {n : ℕ} (hn : (omegaNbr Ω ρ.K).ncard ≤ n) :
    (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard ≤ n + 1 := by
  have hfin : (insert ρ.K (omegaNbr Ω ρ.K)).Finite := Set.toFinite _
  refine le_trans (Set.ncard_le_ncard_of_injOn memberOf (t := insert ρ.K (omegaNbr Ω ρ.K))
    ?_ ?_ hfin) ((Set.ncard_insert_le _ _).trans (by omega))
  · rintro y ⟨hy, hyc⟩
    obtain ⟨τ, rfl⟩ := exists_rep_of_mem_muDelta hy
    rw [memberOf_muTabElt hP hW]
    by_cases hτ : τ.K = ρ.K
    · exact Or.inl hτ
    · exact Or.inr ((muTab_commute_iff hP hW ρ τ (Ne.symm hτ)).mp hyc.symm)
  · rintro y ⟨hy, -⟩ y' ⟨hy', -⟩ hyy'
    obtain ⟨τ, rfl⟩ := exists_rep_of_mem_muDelta hy
    obtain ⟨τ', rfl⟩ := exists_rep_of_mem_muDelta hy'
    rw [memberOf_muTabElt hP hW, memberOf_muTabElt hP hW] at hyy'
    exact (muTabElt_eq_iff hP hW τ τ').mpr hyy'

theorem exists_not_conn_at (hnc : ¬ DbarConnected Ω W) (d : ↥(muGroup Ω W)) :
    ∃ a ∈ muDelta Ω W, ¬ Star3T.Conn (muDelta Ω W) d a := by
  obtain ⟨d₁, hd₁, a₁, ha₁, hc⟩ := exists_not_conn_of_not_connected hP.1 hP.2.1 hP.2.2.1 hW hnc
  by_cases h : Star3T.Conn (muDelta Ω W) d d₁
  · exact ⟨a₁, ha₁, fun h' => hc (h.symm.trans h')⟩
  · exact ⟨d₁, hd₁, h⟩

theorem muIso_of_cent (hnc : ¬ DbarConnected Ω W) (ρ : Rep Ω W) :
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 1 → MuIsoS3 Ω W) ∧
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 2 → MuIsoS4 Ω W) ∧
    ((Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard = 4 → MuIsoWylD4 Ω W) := by
  have hTT := isTT_muDelta hP.1 hP.2.1 hP.2.2.1 hW (thompsonCube G Ω hP W hW)
  have hS := isStar_muDelta hP.1 hP.2.1 hP.2.2.1 hW (thompsonStar G Ω hP W hW)
  obtain ⟨a, ha, hconn⟩ := exists_not_conn_at hP hW hnc (muTabElt ρ)
  have hd := muTabElt_mem ρ
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_three hTT hS hd ha hconn hk
    exact ⟨e⟩
  · obtain ⟨e, -⟩ := Star3T.exists_mulEquiv_perm_four hTT hS hd ha hconn hk
    exact ⟨e⟩
  · rcases thompsonClique G Ω hP W hW hnc (muTabElt ρ) hd with h | h | ⟨-, hcard⟩
    · omega
    · omega
    · exact Star3T.nonempty_mulEquiv_of_card_four hTT hS hd ha hconn hk hcard
        (M := coxeterD4) (fun i j => by fin_cases i <;> fin_cases j <;> rfl)
        coxeterD4.toCoxeterSystem

theorem not_dbarConnected_of_shape {K : Subgroup G} (hK : K ∈ Ω)
    (hne : dComp Ω K ≠ dstarComp Ω K) : ¬ DbarConnected Ω W :=
  thompsonGraphAll G Ω hP hK hne hW

theorem muIsoS3_of_shape (hA : Disconnected.DEdgeless Ω)
    (hstar : ∃ K ∈ Ω, (omegaStarNbr Ω K).Nonempty) : MuIsoS3 Ω W := by
  obtain ⟨K, hK, J, hJ⟩ := hstar
  have hnbr : ∀ M ∈ Ω, omegaNbr Ω M = ∅ := fun M hM => by
    ext N
    refine ⟨fun hN => ?_, fun hN => absurd hN (Set.notMem_empty N)⟩
    exact absurd (Or.inl hN) (hA M hM N hN.1)
  have hnc : ¬ DbarConnected Ω W := by
    refine not_dbarConnected_of_shape hP hW hK (fun h => ?_)
    have hJs : J ∈ dstarComp Ω K :=
      Relation.ReflTransGen.single ⟨hJ.1, Or.inl hJ⟩
    rw [← h] at hJs
    have key : ∀ L, L ∈ dComp Ω K → L = K := by
      intro L hL
      have hL' : Relation.ReflTransGen
          (fun M N : Subgroup G => N ∈ Ω ∧ Disconnected.dAdj Ω M N) K L := hL
      rcases hL'.cases_head with h' | ⟨c, ⟨hcΩ, hc⟩, -⟩
      · exact h'.symm
      · rcases hc with hc | hc
        · rw [hnbr K hK] at hc; exact absurd hc (Set.notMem_empty c)
        · exact absurd (Or.inl hc) (hA c hcΩ K hK)
    exact hJ.2.1 (key J hJs)
  obtain ⟨g, ρ, hρ⟩ := exists_rep hP hW hK
  refine (muIso_of_cent hP hW hnc ρ).1 ?_
  have h1 := ncard_cent_le hP hW ρ (n := 0) (by rw [hnbr _ ρ.hK]; simp)
  have h2 : 0 < (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard :=
    (Set.ncard_pos (Set.toFinite _)).mpr ⟨muTabElt ρ, Star3T.self_mem_cent (muTabElt_mem ρ)⟩
  omega

theorem muIsoS4_of_shape (hone : ∀ K ∈ Ω, ∀ J ∈ omegaNbr Ω K, ∀ L ∈ omegaNbr Ω K, J = L)
    (hedge : ∃ K ∈ Ω, (omegaNbr Ω K).Nonempty) (hcomp : ∃ K ∈ Ω, dComp Ω K ≠ dstarComp Ω K) :
    MuIsoS4 Ω W := by
  obtain ⟨K₁, hK₁, hne⟩ := hcomp
  have hnc := not_dbarConnected_of_shape hP hW hK₁ hne
  obtain ⟨K, hK, J, hJ⟩ := hedge
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := exists_rep_pair_of_omegaNbr hP hW hK hJ
  have hσρ : σ.K ∈ omegaNbr Ω ρ.K := by
    rw [hρ, hσ]
    exact omegaNbr_conj hP.2.2.1.conjInvariant hJ g
  have hne' : ρ.K ≠ σ.K := fun h => hσρ.2.1 h.symm
  refine (muIso_of_cent hP hW hnc ρ).2.1 ?_
  have hle : (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard ≤ 2 := by
    refine ncard_cent_le hP hW ρ (n := 1) ?_
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    exact hone ρ.K ρ.hK a ha b hb
  have hge : 2 ≤ (Star3T.cent (muDelta Ω W) (muTabElt ρ)).ncard := by
    have hd : muTabElt ρ ≠ muTabElt σ := fun h => hne' ((muTabElt_eq_iff hP hW ρ σ).mp h)
    have hsub : ({muTabElt ρ, muTabElt σ} : Set ↥(muGroup Ω W)) ⊆
        Star3T.cent (muDelta Ω W) (muTabElt ρ) := by
      rintro y (rfl | rfl)
      · exact Star3T.self_mem_cent (muTabElt_mem ρ)
      · exact ⟨muTabElt_mem σ, ((muTab_commute_iff hP hW ρ σ hne').mpr hσρ).symm⟩
    calc 2 = ({muTabElt ρ, muTabElt σ} : Set ↥(muGroup Ω W)).ncard := (Set.ncard_pair hd).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

omit hP hW [Finite G] in
theorem le_centralizer_of_commute {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.centralizer (B : Set G) := fun a ha =>
  Subgroup.mem_centralizer_iff.mpr fun b hb => (h a ha b hb).symm

omit hP hW [Finite G] in
theorem commute_conjSub {A B : Subgroup G} (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (g : G) :
    ∀ a ∈ conjSub g A, ∀ b ∈ conjSub g B, a * b = b * a := by
  intro a ha b hb
  rw [mem_conjSub_iff] at ha hb
  have := h _ ha _ hb
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
    _ = b * a := by group

theorem muIsoWylD4_of_shape (hle : ∀ K ∈ Ω, (omegaNbr Ω K).ncard ≤ 3) (K : Fin 4 → Subgroup G)
    (hK : ∀ i, K i ∈ Ω) (hinj : Function.Injective K)
    (hcomm : ∀ i j, i ≠ j → ∀ a ∈ K i, ∀ b ∈ K j, a * b = b * a)
    (hcomp : ∃ M ∈ Ω, dComp Ω M ≠ dstarComp Ω M) : MuIsoWylD4 Ω W := by
  obtain ⟨M, hM, hne⟩ := hcomp
  have hnc := not_dbarConnected_of_shape hP hW hM hne
  choose R hR using fun i => exists_sylow2In (K i)
  have hRle : ∀ i j, i ≠ j → R i ≤ Subgroup.centralizer (R j : Set G) := fun i j hij =>
    le_centralizer_of_commute fun a ha b hb => hcomm i j hij a ((hR i).1 ha) b ((hR j).1 hb)
  have hN : ∀ {A B : Subgroup G}, A ≤ Subgroup.centralizer (B : Set G) →
      A ≤ Subgroup.normalizer (B : Set G) := fun h => h.trans (Subgroup.centralizer_le_normalizer _)
  have h01 : IsPGroup 2 ↥(R 0 ⊔ R 1) :=
    (hR 0).2.1.to_sup_of_normal_right' (hR 1).2.1 (hN (hRle 0 1 (by decide)))
  have h012 : IsPGroup 2 ↥(R 0 ⊔ R 1 ⊔ R 2) :=
    h01.to_sup_of_normal_right' (hR 2).2.1
      (hN (sup_le (hRle 0 2 (by decide)) (hRle 1 2 (by decide))))
  have hQ : IsPGroup 2 ↥(R 0 ⊔ R 1 ⊔ R 2 ⊔ R 3) :=
    h012.to_sup_of_normal_right' (hR 3).2.1
      (hN (sup_le (sup_le (hRle 0 3 (by decide)) (hRle 1 3 (by decide)))
        (hRle 2 3 (by decide))))
  obtain ⟨g, hg⟩ := exists_rep_of_member_sylow hP hW K R hK hR (R 0 ⊔ R 1 ⊔ R 2 ⊔ R 3) hQ (by
    intro i; fin_cases i
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_left)
    · exact le_sup_of_le_left (le_sup_of_le_left le_sup_right)
    · exact le_sup_of_le_left le_sup_right
    · exact le_sup_right)
  choose ρ hρ using hg
  have hKne : ∀ i j, i ≠ j → (ρ i).K ≠ (ρ j).K := fun i j hij h => by
    rw [hρ i, hρ j] at h
    exact hij (hinj ((conjSub_inj g).mp h))
  have hdinj : Function.Injective fun i => muTabElt (ρ i) := fun i j h =>
    by_contra fun hij => hKne i j hij ((muTabElt_eq_iff hP hW _ _).mp h)
  have hmem : ∀ i, i ≠ 0 → (ρ i).K ∈ omegaNbr Ω (ρ 0).K := fun i hi =>
    mem_omegaNbr_of_commutes (ρ i).hK (hKne i 0 hi) (by
      rw [hρ 0, hρ i]
      exact commute_conjSub (hcomm 0 i (Ne.symm hi)) g)
  have hsub : Set.range (fun i => muTabElt (ρ i)) ⊆
      Star3T.cent (muDelta Ω W) (muTabElt (ρ 0)) := by
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0
    · subst hi
      exact Star3T.self_mem_cent (muTabElt_mem _)
    · exact ⟨muTabElt_mem _, ((muTab_commute_iff hP hW (ρ 0) (ρ i)
        (Ne.symm (hKne i 0 hi))).mpr (hmem i hi)).symm⟩
  refine (muIso_of_cent hP hW hnc (ρ 0)).2.2 ?_
  have hge : 4 ≤ (Star3T.cent (muDelta Ω W) (muTabElt (ρ 0))).ncard := by
    have h4 : (Set.range fun i => muTabElt (ρ i)).ncard = 4 := by
      rw [← Set.image_univ, Set.ncard_image_of_injective _ hdinj, Set.ncard_univ]
      simp
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  have hle' := ncard_cent_le hP hW (ρ 0) (n := 3) (hle _ (ρ 0).hK)
  omega

end Cent

end MuTab

end CFSG.ClassicalInvolution.Asc77
