module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Basic

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem exists_extremal_normalizer_conj (T : Sylow 2 G) {a : G}
    (haZ : ∀ s ∈ (T : Subgroup G), a * s = s * a)
    (hne : ∃ g : G, g⁻¹ * a * g ∈ (T : Subgroup G) ∧ g⁻¹ * a * g ≠ a) :
    ∃ b ∈ (T : Subgroup G), b ≠ a ∧ (∃ g : G, b = g⁻¹ * a * g) ∧
      ∃ n ∈ normalizer (((T : Subgroup G) ⊓ centralizer ({b} : Set G) : Subgroup G) : Set G),
        n⁻¹ * b * n = a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Set G := {b | b ∈ (T : Subgroup G) ∧ b ≠ a ∧ ∃ g : G, b = g⁻¹ * a * g} with hCdef
  have hCne : C.Nonempty := by
    obtain ⟨g, hgT, hga⟩ := hne
    exact ⟨_, hgT, hga, g, rfl⟩
  obtain ⟨b, ⟨hbT, hba, g, hg⟩, hmax⟩ := Set.exists_max_image C
    (fun b => Nat.card ↥((T : Subgroup G) ⊓ centralizer ({b} : Set G))) (Set.toFinite C) hCne
  set P : Subgroup G := (T : Subgroup G) ⊓ centralizer ({b} : Set G) with hPdef
  have hbP : b ∈ P := mem_inf.mpr ⟨hbT, mem_centralizer_singleton_iff.mpr rfl⟩
  have hTa : (T : Subgroup G) ≤ centralizer ({a} : Set G) := fun s hs =>
    mem_centralizer_singleton_iff.mpr (haZ s hs).symm
  have hV : P.map (MulAut.conj g).toMonoidHom ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨z, hz, rfl⟩
    have hzb := mem_centralizer_singleton_iff.mp (mem_inf.mp hz).2
    rw [mem_centralizer_singleton_iff]
    change g * z * g⁻¹ * a = a * (g * z * g⁻¹)
    have hga : a = g * b * g⁻¹ := by rw [hg]; group
    rw [hga]
    calc g * z * g⁻¹ * (g * b * g⁻¹) = g * (z * b) * g⁻¹ := by group
      _ = g * (b * z) * g⁻¹ := by rw [hzb]
      _ = g * b * g⁻¹ * (g * z * g⁻¹) := by group
  have hVp : IsPGroup 2 (P.map (MulAut.conj g).toMonoidHom) :=
    (T.isPGroup'.to_le inf_le_left).map _
  obtain ⟨c, hc, hcT⟩ := exists_conj_le_sylow T hTa hV hVp
  have hca : c⁻¹ * a * c = a := by
    have := mem_centralizer_singleton_iff.mp hc
    rw [mul_assoc, ← this, inv_mul_cancel_left]
  set k₀ : G := g⁻¹ * c with hk₀
  have hk₀P : P.map (MulAut.conj k₀⁻¹).toMonoidHom ≤ (T : Subgroup G) := by
    rintro _ ⟨z, hz, rfl⟩
    have h1 := hcT (g * z * g⁻¹) ⟨z, hz, rfl⟩
    change k₀⁻¹ * z * k₀⁻¹⁻¹ ∈ (T : Subgroup G)
    rwa [inv_inv, hk₀, show (g⁻¹ * c)⁻¹ * z * (g⁻¹ * c) = c⁻¹ * (g * z * g⁻¹) * c by group]
  obtain ⟨k, hdec, hk⟩ := RankTwoShapes.alperin_centric_radical_fusion T inf_le_left hk₀P
  have hkb : k⁻¹ * b * k = a := by
    rw [hk b hbP, hk₀, hg, show (g⁻¹ * c)⁻¹ * (g⁻¹ * a * g) * (g⁻¹ * c) = c⁻¹ * a * c by group,
      hca]
  have key : ∀ k' : G, RankTwoShapes.AlperinDecomposition 2 (T : Subgroup G) P k' →
      (k'⁻¹ * b * k' ≠ a ∧ (T : Subgroup G) ⊓ centralizer ({k'⁻¹ * b * k'} : Set G) =
        P.map (MulAut.conj k'⁻¹).toMonoidHom) ∨
      (∃ b' ∈ (T : Subgroup G), b' ≠ a ∧ (∃ g' : G, b' = g'⁻¹ * a * g') ∧
        ∃ n ∈ normalizer (((T : Subgroup G) ⊓ centralizer ({b'} : Set G) : Subgroup G) :
          Set G), n⁻¹ * b' * n = a) := by
    intro k' hk'
    induction hk' with
    | one =>
      left
      have hid : (MulAut.conj (1 : G)⁻¹).toMonoidHom = MonoidHom.id G := by
        ext y
        simp
      rw [hid, Subgroup.map_id]
      exact ⟨by simpa using hba, by simp [hPdef]⟩
    | @step c' n Q hdec' hQ hPQ hn ih =>
      rcases ih with ⟨hb1, hC1⟩ | hdone
      · have hb₁Q : c'⁻¹ * b * c' ∈ Q := by
          apply hPQ
          exact ⟨b, hbP, by simp⟩
        have hb₂Q : n⁻¹ * (c'⁻¹ * b * c') * n ∈ Q := by
          have := (mem_normalizer_iff.mp (inv_mem hn) _).mp hb₁Q
          rwa [inv_inv] at this
        have hb₂eq : (c' * n)⁻¹ * b * (c' * n) = n⁻¹ * (c'⁻¹ * b * c') * n := by group
        rw [hb₂eq]
        by_cases hb₂a : n⁻¹ * (c'⁻¹ * b * c') * n = a
        · right
          refine ⟨c'⁻¹ * b * c', hQ.1 hb₁Q, hb1, ⟨g * c', by rw [hg]; group⟩, n, ?_, hb₂a⟩
          have hQle : Q ≤ (T : Subgroup G) ⊓ centralizer ({c'⁻¹ * b * c'} : Set G) := by
            intro q hq
            refine mem_inf.mpr ⟨hQ.1 hq, mem_centralizer_singleton_iff.mpr ?_⟩
            have hq' : n⁻¹ * q * n ∈ Q := by
              have := (mem_normalizer_iff.mp (inv_mem hn) q).mp hq
              rwa [inv_inv] at this
            have hz := haZ _ (hQ.1 hq')
            have hy : c'⁻¹ * b * c' = n * a * n⁻¹ := by rw [← hb₂a]; group
            rw [hy]
            calc q * (n * a * n⁻¹) = n * ((n⁻¹ * q * n) * a) * n⁻¹ := by group
              _ = n * (a * (n⁻¹ * q * n)) * n⁻¹ := by rw [hz]
              _ = n * a * n⁻¹ * q := by group
          have hge : (T : Subgroup G) ⊓ centralizer ({c'⁻¹ * b * c'} : Set G) ≤ Q := by
            rw [hC1]
            exact hPQ
          rw [le_antisymm hQle hge] at hn
          exact hn
        · left
          refine ⟨hb₂a, ?_⟩
          have hsub : P.map (MulAut.conj (c' * n)⁻¹).toMonoidHom ≤
              (T : Subgroup G) ⊓ centralizer ({n⁻¹ * (c'⁻¹ * b * c') * n} : Set G) := by
            rintro _ ⟨p, hp, rfl⟩
            change (c' * n)⁻¹ * p * (c' * n)⁻¹⁻¹ ∈ _
            rw [inv_inv]
            have hpQ : c'⁻¹ * p * c' ∈ Q := by
              apply hPQ
              exact ⟨p, hp, by simp⟩
            have hpQ' : n⁻¹ * (c'⁻¹ * p * c') * n ∈ Q := by
              have := (mem_normalizer_iff.mp (inv_mem hn) _).mp hpQ
              rwa [inv_inv] at this
            have hpb := mem_centralizer_singleton_iff.mp (mem_inf.mp hp).2
            refine mem_inf.mpr ⟨?_, mem_centralizer_singleton_iff.mpr ?_⟩
            · rw [show (c' * n)⁻¹ * p * (c' * n) = n⁻¹ * (c'⁻¹ * p * c') * n by group]
              exact hQ.1 hpQ'
            · calc (c' * n)⁻¹ * p * (c' * n) * (n⁻¹ * (c'⁻¹ * b * c') * n)
                  = (c' * n)⁻¹ * (p * b) * (c' * n) := by group
                _ = (c' * n)⁻¹ * (b * p) * (c' * n) := by rw [hpb]
                _ = n⁻¹ * (c'⁻¹ * b * c') * n * ((c' * n)⁻¹ * p * (c' * n)) := by group
          have hcard : Nat.card ↥((T : Subgroup G) ⊓
                centralizer ({n⁻¹ * (c'⁻¹ * b * c') * n} : Set G)) ≤
              Nat.card ↥(P.map (MulAut.conj (c' * n)⁻¹).toMonoidHom) := by
            rw [card_map_of_injective (MulAut.conj (c' * n)⁻¹).injective]
            exact hmax _ ⟨hQ.1 hb₂Q, hb₂a, ⟨g * c' * n, by rw [hg]; group⟩⟩
          exact (eq_of_le_of_card_ge hsub hcard).symm
      · exact Or.inr hdone
  rcases key k hdec with ⟨hk1, -⟩ | hdone
  · exact absurd hkb hk1
  · exact hdone

end CFSG.ComponentClassification.GrSLit.GrS4
