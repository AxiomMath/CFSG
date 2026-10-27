module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinFacts
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinTrans
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinAbs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K421LinSyl

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

namespace K421DataProof

open CFSG.Open K421MonoProof K421OrbProof K421LinProof K421CGProof K421FactsProof K421AbsProof
  K421GrpProof K421TransProof K421SylProof

abbrev GG (e : ℕ) : Type := GL (Fin e ⊕ Idx) (ZMod 2)

theorem card_GG (e : ℕ) : Nat.card (GG e) = glc 2 (e + 6) := by
  rw [card_GL, ZMod.card]
  congr 1
  simp

theorem card_GG_three (e : ℕ) (he : e ≤ 1) : ∃ k, ¬ 3 ∣ k ∧ Nat.card (GG e) = 81 * k := by
  rw [card_GG]
  interval_cases e
  · exact ⟨glc 2 6 / 81, by unfold glc; decide +kernel, by unfold glc; decide +kernel⟩
  · exact ⟨glc 2 7 / 81, by unfold glc; decide +kernel, by unfold glc; decide +kernel⟩

theorem card_GG_seven (e : ℕ) (he : e ≤ 1) : ∃ m, ¬ 7 ∣ m ∧ Nat.card (GG e) = 7 ^ 2 * m := by
  rw [card_GG]
  interval_cases e
  · exact ⟨glc 2 6 / 49, by unfold glc; decide +kernel, by unfold glc; decide +kernel⟩
  · exact ⟨glc 2 7 / 49, by unfold glc; decide +kernel, by unfold glc; decide +kernel⟩

theorem rank_seven_le {e : ℕ} (he : e ≤ 1) {S : Type} [Group S] [Finite S] (ε : S ≃* GG e) :
    CFSG.Open.pRank 7 (⊤ : Subgroup S) ≤ 2 := by
  obtain ⟨m, hm, hcard⟩ := card_GG_seven e he
  rw [← Nat.card_congr ε.toEquiv] at hcard
  exact pRank_le_of_card (by norm_num) hcard hm ⊤

@[expose] def cenOrd (e : ℕ) : Fin 3 → ℕ
  | 0 => glc 2 (e + 4) * glc 4 1
  | 1 => glc 2 (e + 2) * glc 4 2
  | 2 => glc 2 e * glc 4 3

theorem cenOrd_inj (e : ℕ) (he : e ≤ 1) {t₁ t₂ : Fin 3} (h : cenOrd e t₁ = cenOrd e t₂) :
    t₁ = t₂ := by
  revert t₁ t₂ h
  interval_cases e
  · unfold cenOrd glc
    decide +kernel
  · unfold cenOrd glc
    decide +kernel

theorem emb_transport {S G : Type} [Group S] [Group G] (ε : S ≃* G) {x : S} {n : ℕ}
    (φ : GL (Fin n) (ZMod 2) →* G) (hφ : Function.Injective φ)
    (hle : φ.range ≤ Subgroup.centralizer ({ε x} : Set G)) :
    ∃ ψ : GL (Fin n) (ZMod 2) →* S, Function.Injective ψ ∧
      ψ.range ≤ Subgroup.centralizer ({x} : Set S) := by
  refine ⟨ε.symm.toMonoidHom.comp φ, ε.symm.injective.comp hφ, ?_⟩
  rintro _ ⟨s, rfl⟩
  have h1 := centralizer_map_singleton ε.symm (ε x)
  rw [ε.symm_apply_apply] at h1
  rw [← h1]
  exact ⟨φ s, hle ⟨s, rfl⟩, rfl⟩

theorem facts_t0 (e : ℕ) (he : e ≤ 1) {x n : GG e} (hn : n * x * n⁻¹ = gRep e 0) :
    Nat.card (Subgroup.centralizer ({x} : Set (GG e))) = cenOrd e 0 ∧
    ∃ m : ℕ, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ∃ φ : GL (Fin m) (ZMod 2) →* GG e, Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({x} : Set (GG e)) := by
  obtain ⟨hc, φ, hφ, hle⟩ := cen_t0 e he
  refine ⟨?_, e + 4, by omega, emb_conj φ hφ hn hle⟩
  rw [← card_centralizer_conj n x, hn, hc]
  rfl

theorem facts_t1 (e : ℕ) (he : e ≤ 1) {x n : GG e} (hn : n * x * n⁻¹ = gRep e 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (GG e))) = cenOrd e 1 ∧
    (e = 1 → ∃ m : ℕ, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ∃ φ : GL (Fin m) (ZMod 2) →* GG e,
      Function.Injective φ ∧ φ.range ≤ Subgroup.centralizer ({x} : Set (GG e))) := by
  obtain ⟨hc, φ, hφ, hle⟩ := cen_t1 e he
  refine ⟨?_, fun he1 => ⟨e + 2, by omega, emb_conj φ hφ hn hle⟩⟩
  rw [← card_centralizer_conj n x, hn, hc]
  rfl

theorem facts_t2 (e : ℕ) (he : e ≤ 1) {x n : GG e} (hn : n * x * n⁻¹ = gRep e 2) :
    Nat.card (Subgroup.centralizer ({x} : Set (GG e))) = cenOrd e 2 ∧
    ∃ m : ℕ, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ∃ φ : GL (Fin m) (ZMod 2) →* GG e, Function.Injective φ ∧
      φ.range ≤ Subgroup.centralizer ({x} : Set (GG e)) := by
  obtain ⟨hc, φ, hφ, hle⟩ := cen_t2 e he
  refine ⟨?_, 3, by omega, emb_conj φ hφ hn hle⟩
  rw [← card_centralizer_conj n x, hn, hc]
  rfl

theorem facts_of_type (e : ℕ) (he : e ≤ 1) (t : Fin 3) {x : GG e}
    (hty : IsType (monoE (Fin e)) x t) :
    Nat.card (Subgroup.centralizer ({x} : Set (GG e))) = cenOrd e t ∧
    ((t ≠ 1 ∨ e = 1) → ∃ m : ℕ, (m = 3 ∨ m = 4 ∨ m = 5) ∧ ∃ φ : GL (Fin m) (ZMod 2) →* GG e,
      Function.Injective φ ∧ φ.range ≤ Subgroup.centralizer ({x} : Set (GG e))) ∧
    (t = 1 → e = 0 → ∃ A : Subgroup (GG e), IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      A ≤ Subgroup.centralizer ({x} : Set (GG e))) := by
  obtain ⟨n, hn⟩ := hty
  match t, hn with
  | 0, hn =>
    obtain ⟨h1, h2⟩ := facts_t0 e he hn
    exact ⟨h1, fun _ => h2, fun h => absurd h (by decide)⟩
  | 1, hn =>
    obtain ⟨h1, h2⟩ := facts_t1 e he hn
    refine ⟨h1, fun h => ?_, fun _ he0 => ?_⟩
    · rcases h with h | h
      · exact absurd rfl h
      · exact h2 h
    ·
      refine ⟨(monoE (Fin e)).A0.map (MulAut.conj n⁻¹).toMonoidHom,
        K21bTransProof.isElemAbelian_map_inj (MulAut.conj n⁻¹).injective
          (monoE (Fin e)).isElemAbelian_A0, ?_, ?_⟩
      · rw [Subgroup.card_map_of_injective (MulAut.conj n⁻¹).injective]
        exact (monoE (Fin e)).card_A0
      · rintro _ ⟨z, hz, rfl⟩
        obtain ⟨w, rfl⟩ := (monoE (Fin e)).mem_A0_iff.1 hz
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        rw [Set.mem_singleton_iff] at hu
        subst hu
        have hx : u = n⁻¹ * gRep e 1 * n := by
          have hn' : n * u * n⁻¹ = gRep e 1 := hn
          rw [← hn']
          group
        have hcomm : (monoE (Fin e)).av w * gRep e 1 = gRep e 1 * (monoE (Fin e)).av w :=
          (monoE (Fin e)).av_comm w (rep 1)
        show u * (n⁻¹ * (monoE (Fin e)).av w * n) = (n⁻¹ * (monoE (Fin e)).av w * n) * u
        calc u * (n⁻¹ * (monoE (Fin e)).av w * n)
            = n⁻¹ * (gRep e 1 * (monoE (Fin e)).av w) * n := by rw [hx]; group
          _ = n⁻¹ * ((monoE (Fin e)).av w * gRep e 1) * n := by rw [hcomm]
          _ = (n⁻¹ * (monoE (Fin e)).av w * n) * u := by rw [hx]; group
  | 2, hn =>
    obtain ⟨h1, h2⟩ := facts_t2 e he hn
    exact ⟨h1, fun _ => h2, fun h => absurd h (by decide)⟩

theorem data421_of_equiv {e : ℕ} (he : e ≤ 1) {S : Type} [Group S] [Finite S] (ε : S ≃* GG e) :
    Data421 S 7 := by
  obtain ⟨k, hk3, hk⟩ := card_GG_three e he
  have hSP : SignedPerms (monoE (Fin e)) := signedPerms_monoE _
  have hrank := rank_seven_le he ε
  refine ⟨?_, ?_⟩
  · intro Dsub hD
    obtain ⟨x, hx, rfl⟩ := exists_zpowers_of_card_three hD
    have hx' : orderOf (ε x) = 3 := by rw [MulEquiv.orderOf_eq]; exact hx
    obtain ⟨t, hty⟩ := exists_type hk3 hk hSP hx'
    obtain ⟨hcard, hemb, hshape⟩ := facts_of_type e he t hty
    rw [centralizer_zpowers_eq]
    by_cases hc : t ≠ 1 ∨ e = 1
    · left
      obtain ⟨m, hm, φ, hφ, hle⟩ := hemb hc
      obtain ⟨ψ, hψ, hψle⟩ := emb_transport ε φ hφ hle
      exact caseA_of_emb hrank hm ψ hψ hψle
    · right
      have ht : t = 1 := by
        by_contra h
        exact hc (Or.inl h)
      have he0 : e = 0 := by
        by_contra h
        exact hc (Or.inr (by omega))
      obtain ⟨A, hAe, hA27, hAC⟩ := hshape ht he0
      have hcard' : Nat.card (Subgroup.centralizer ({x} : Set S)) = 27 * 40 := by
        rw [← card_centralizer_map ε x, hcard, ht, he0]
        unfold cenOrd glc
        decide +kernel
      have h1 := centralizer_map_singleton ε.symm (ε x)
      rw [ε.symm_apply_apply] at h1
      refine ⟨sylowShape_of_data hx (A := A.map ε.symm.toMonoidHom)
        (K21bTransProof.isElemAbelian_map_inj ε.symm.injective hAe)
        (by rw [Subgroup.card_map_of_injective ε.symm.injective]; exact hA27)
        (by rw [← h1]; exact Subgroup.map_mono hAC) hcard' (by norm_num), ?_⟩
      omega
  · intro E hE h9
    have hE' : IsElemAbelian 3 (E.map ε.toMonoidHom) :=
      K21bTransProof.isElemAbelian_map_inj ε.injective hE
    have h9' : Nat.card (E.map ε.toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective ε.injective, h9]
    obtain ⟨-, c', hc'E, hc'1, t, ht1, hty⟩ := exists_types_of_card_nine hk3 hk hSP hE' h9'
    obtain ⟨c, hcE, rfl⟩ := Subgroup.mem_map.1 hc'E
    have hc3 : c ^ 3 = 1 := hE.2 c hcE
    have hc1 : c ≠ 1 := fun h => hc'1 (by rw [h, map_one])
    have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have hty' : IsType (monoE (Fin e)) (ε c) t := hty
    obtain ⟨-, hemb, -⟩ := facts_of_type e he t hty'
    refine ⟨Subgroup.zpowers c, (Subgroup.zpowers_le).2 hcE, by rw [Nat.card_zpowers, hcord], ?_⟩
    rw [centralizer_zpowers_eq]
    obtain ⟨m, hm, φ, hφ, hle⟩ := hemb (Or.inl ht1)
    obtain ⟨ψ, hψ, hψle⟩ := emb_transport ε φ hφ hle
    exact caseA_of_emb hrank hm ψ hψ hψle

theorem nonTrans_of_equiv {e : ℕ} (he : e ≤ 1) {S : Type} [Group S] [Finite S] (ε : S ≃* GG e) :
    ∀ E : Subgroup S, IsElemAbelian 3 E → Nat.card E = 9 → ∃ a ∈ E, ∃ b ∈ E, a ≠ 1 ∧ b ≠ 1 ∧
      ∀ φ : MulAut S, E.map φ.toMonoidHom = E → φ a ≠ b := by
  obtain ⟨k, hk3, hk⟩ := card_GG_three e he
  have hSP : SignedPerms (monoE (Fin e)) := signedPerms_monoE _
  intro E hE h9
  have hE' : IsElemAbelian 3 (E.map ε.toMonoidHom) :=
    K21bTransProof.isElemAbelian_map_inj ε.injective hE
  have h9' : Nat.card (E.map ε.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective ε.injective, h9]
  obtain ⟨⟨a', ha'E, b', hb'E, ha'1, hb'1, t₁, t₂, ht12, hty₁, hty₂⟩, -⟩ :=
    exists_types_of_card_nine hk3 hk hSP hE' h9'
  obtain ⟨a, haE, rfl⟩ := Subgroup.mem_map.1 ha'E
  obtain ⟨b, hbE, rfl⟩ := Subgroup.mem_map.1 hb'E
  have ha1 : a ≠ 1 := fun h => ha'1 (by rw [h, map_one])
  have hb1 : b ≠ 1 := fun h => hb'1 (by rw [h, map_one])
  refine ⟨a, haE, b, hbE, ha1, hb1, fun φ _ hφ => ?_⟩
  have hty₁' : IsType (monoE (Fin e)) (ε a) t₁ := hty₁
  have hty₂' : IsType (monoE (Fin e)) (ε b) t₂ := hty₂
  obtain ⟨hc₁, -, -⟩ := facts_of_type e he t₁ hty₁'
  obtain ⟨hc₂, -, -⟩ := facts_of_type e he t₂ hty₂'
  have h1 := card_centralizer_map ε a
  have h2 := card_centralizer_map ε b
  have h3 := card_centralizer_map φ a
  rw [hφ] at h3
  apply ht12
  apply cenOrd_inj e he
  rw [← hc₁, ← hc₂, h1, h2, h3]

end K421DataProof

end CFSG.LocalAnalysis.RankThreeUC.S15
