module

public import Certificates.Certificate24848
public import Certificates.Certificate24849

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

theorem qd_xor_lt_64 {a b : ℕ} (ha : a < 64) (hb : b < 64) : a ^^^ b < 64 :=
  Nat.xor_lt_two_pow (n := 6) ha hb

theorem qdLin_eq {φ : ℕ → ℕ} (hhom : ∀ k < 64, ∀ j < 64, φ (k ^^^ j) = φ k ^^^ φ j)
    {y : List ℕ} (hy : ∀ i < 6, y.getD i 0 = φ (2 ^ i)) : ∀ k < 64, φ k = qdLin y k := by
  have h0 : φ 0 = 0 := by
    have := hhom 0 (by norm_num) 0 (by norm_num)
    simpa using this
  have key : ∀ (l : List ℕ), (∀ i ∈ l, i < 6) → ∀ acc < 64,
      φ (l.foldl (fun a i => a ^^^ 2 ^ i) acc) =
        l.foldl (fun a i => a ^^^ y.getD i 0) (φ acc) := by
    intro l
    induction l with
    | nil => intros; rfl
    | cons i l ih =>
      intro hl acc hacc
      simp only [List.foldl_cons]
      have hi : i < 6 := hl i List.mem_cons_self
      have h2 : 2 ^ i < 64 := by
        calc 2 ^ i < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) hi
          _ = 64 := by norm_num
      rw [ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) _ (qd_xor_lt_64 hacc h2),
        hhom acc hacc _ h2, hy i hi]
  intro k hk
  have hdec : ∀ k < 64, k = ((List.range 6).filter fun i => k.testBit i).foldl
      (fun a i => a ^^^ 2 ^ i) 0 := by decide
  have hmem : ∀ i ∈ (List.range 6).filter fun i => k.testBit i, i < 6 := fun i hi =>
    List.mem_range.1 (List.mem_filter.1 hi).1
  conv_lhs => rw [hdec k hk]
  rw [key _ hmem 0 (by norm_num), h0]
  rfl

theorem mem_qdPairs {a b : ℕ} (ha : a < 64) (hb : b < 64) (h1 : qdFxTab.getD a 99 = 0)
    (h2 : qdFxTab.getD b 99 = 0) (h3 : qdFxTab.getD (a ^^^ b) 99 = 0) : (a, b) ∈ qdPairs := by
  unfold qdPairs
  rw [List.mem_filter]
  refine ⟨List.mem_flatMap.2 ⟨a, List.mem_range.2 ha, List.mem_map.2 ⟨b, List.mem_range.2 hb, rfl⟩⟩,
    ?_⟩
  show (qdFxTab.getD a 99 == 0 && qdFxTab.getD b 99 == 0 && qdFxTab.getD (a ^^^ b) 99 == 0) = true
  rw [h1, h2, h3]
  rfl

variable {G : Type} [Group G] {L A : Subgroup G}

theorem omegaW_of_type
    (h : SextetType L A) :
    ∃ w ∈ egNL L A, w * w * w = 1 ∧
      (∀ n ∈ egNL L A,
        (∀ a ∈ A, (n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹ = w * a * w⁻¹) ∨
        (∀ a ∈ A, (n * w * n⁻¹) * a * (n * w * n⁻¹)⁻¹ = w⁻¹ * a * w)) ∧
      ∀ a ∈ A, w * a * w⁻¹ = a → a = 1 := by
  obtain ⟨hAL, e, he⟩ := h
  obtain ⟨hQlist, hQmem, hQhom, hQinj, hQfx⟩ := Certificates.certificate24849
  obtain ⟨hωN, hω3, hωfree, hψ, henum⟩ := Certificates.certificate24848
  refine ⟨qdIota e qdOmega, qdIota_mem_egNL e hAL he hωN.norm, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, hω3, map_one]
  · intro n hn
    obtain ⟨g, hg, rfl⟩ := qdExists_norm_of_mem_egNL e he hn
    have hQ' : ∀ k < 64, ∀ j < 64, qdQ k = qdQ j → k = j := fun k hk j hj h =>
      hQinj k (List.mem_range.2 hk) j (List.mem_range.2 hj) h
    have hex : ∀ k, ∃ j, k < 64 → j < 64 ∧ g * qdQ k * g⁻¹ = qdQ j := by
      intro k
      by_cases hk : k < 64
      · obtain ⟨j, hj, hjq⟩ := hQlist _ ((hg _).1 (hQmem k (List.mem_range.2 hk)))
        exact ⟨j, fun _ => ⟨List.mem_range.1 hj, hjq.symm⟩⟩
      · exact ⟨0, fun h => absurd h hk⟩
    choose φ hφ using hex
    have hφhom : ∀ k < 64, ∀ j < 64, φ (k ^^^ j) = φ k ^^^ φ j := by
      intro k hk j hj
      obtain ⟨hk1, hk2⟩ := hφ k hk
      obtain ⟨hj1, hj2⟩ := hφ j hj
      obtain ⟨hkj1, hkj2⟩ := hφ (k ^^^ j) (qd_xor_lt_64 hk hj)
      refine hQ' _ hkj1 _ (qd_xor_lt_64 hk1 hj1) ?_
      calc qdQ (φ (k ^^^ j)) = g * qdQ (k ^^^ j) * g⁻¹ := hkj2.symm
        _ = g * (qdQ k * qdQ j) * g⁻¹ := by
          rw [hQhom k (List.mem_range.2 hk) j (List.mem_range.2 hj)]
        _ = (g * qdQ k * g⁻¹) * (g * qdQ j * g⁻¹) := by group
        _ = qdQ (φ k) * qdQ (φ j) := by rw [hk2, hj2]
        _ = qdQ (φ k ^^^ φ j) := hQhom _ (List.mem_range.2 hk1) _ (List.mem_range.2 hj1)
    have hφfx : ∀ k < 64, qdFxTab.getD (φ k) 99 = qdFxTab.getD k 99 := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := hφ k hk
      have e1 := hQfx (φ k) (List.mem_range.2 hk1)
      have e2 := hQfx k (List.mem_range.2 hk)
      rw [← e1, ← e2, ← hk2, qdFix_conj]
    have hfx : ∀ k < 64, qdFxTab.getD k 99 = 0 → qdFxTab.getD (φ k) 99 = 0 := fun k hk h0 =>
      (hφfx k hk).trans h0
    have hpair : ∀ a b : ℕ, a < 64 → b < 64 → a ^^^ b < 64 → qdFxTab.getD a 99 = 0 →
        qdFxTab.getD b 99 = 0 → qdFxTab.getD (a ^^^ b) 99 = 0 → (φ a, φ b) ∈ qdPairs := by
      intro a b ha hb hab h1 h2 h3
      refine mem_qdPairs (hφ a ha).1 (hφ b hb).1 (hfx a ha h1) (hfx b hb h2) ?_
      rw [← hφhom a ha b hb]
      exact hfx _ hab h3
    set y : List ℕ := [φ 1, φ 2, φ 4, φ 8, φ 16, φ 32] with hy
    have hy' : ∀ i < 6, y.getD i 0 = φ (2 ^ i) := by
      intro i hi
      interval_cases i <;> simp [hy]
    have hlin := qdLin_eq hφhom hy'
    have hE : QdEnumBody y := henum _ (hpair 1 2 (by norm_num) (by norm_num) (by norm_num)
      (by decide) (by decide) (by decide)) _ (hpair 4 8 (by norm_num) (by norm_num) (by norm_num)
      (by decide) (by decide) (by decide)) _ (hpair 16 32 (by norm_num) (by norm_num)
      (by norm_num) (by decide) (by decide) (by decide))
    have hant : ∀ k ∈ List.range 64, qdFxTab.getD (qdLin y k) 99 = qdFxTab.getD k 99 := by
      intro k hk
      have hk' := List.mem_range.1 hk
      rw [← hlin k hk']
      exact hφfx k hk'
    have hsrep : ∀ s ∈ m24E1l, ∃ j < 64, s = qdQ (φ j) := by
      intro s hs
      have ht : g⁻¹ * s * g ∈ m24E1l := by
        apply (hg _).2
        have : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
        rw [this]
        exact hs
      obtain ⟨j, hj, hjq⟩ := hQlist _ ht
      have hj' := List.mem_range.1 hj
      refine ⟨j, hj', ?_⟩
      rw [← (hφ j hj').2, hjq]
      group
    have hmain : ∀ j < 64, (g * qdOmega * g⁻¹) * qdQ (φ j) * (g * qdOmega * g⁻¹)⁻¹ =
        qdQ (φ (qdPsiTab.getD j 0)) := by
      intro j hj
      obtain ⟨hψj, -, hψ1, -⟩ := hψ j (List.mem_range.2 hj)
      rw [← (hφ j hj).2, ← (hφ _ hψj).2, ← hψ1]
      group
    rcases hE hant with h1 | h1
    · left
      intro a ha
      obtain ⟨s, hs, rfl⟩ := (qdMem_A_iff e hAL he a).1 ha
      obtain ⟨j, hj, rfl⟩ := hsrep s hs
      simp only [qdIota_conj]
      congr 1
      rw [hmain j hj]
      obtain ⟨hψj, -, -, -⟩ := hψ j (List.mem_range.2 hj)
      obtain ⟨-, -, hψ1, -⟩ := hψ (φ j) (List.mem_range.2 (hφ j hj).1)
      rw [hψ1]
      congr 1
      rw [hlin _ hψj, h1 j (List.mem_range.2 hj), ← hlin j hj]
    · right
      intro a ha
      obtain ⟨s, hs, rfl⟩ := (qdMem_A_iff e hAL he a).1 ha
      obtain ⟨j, hj, rfl⟩ := hsrep s hs
      have hrhs : (qdIota e qdOmega)⁻¹ * qdIota e (qdQ (φ j)) * qdIota e qdOmega =
          qdIota e (qdOmega⁻¹ * qdQ (φ j) * qdOmega) := by
        simp [map_mul, map_inv]
      rw [hrhs]
      simp only [qdIota_conj]
      congr 1
      rw [hmain j hj]
      obtain ⟨hψj, -, -, -⟩ := hψ j (List.mem_range.2 hj)
      obtain ⟨-, -, -, hψ2⟩ := hψ (φ j) (List.mem_range.2 (hφ j hj).1)
      have : qdOmega⁻¹ * qdQ (φ j) * qdOmega = qdQ (qdPsiInvTab.getD (φ j) 0) := hψ2
      rw [this]
      congr 1
      rw [hlin _ hψj, h1 j (List.mem_range.2 hj), ← hlin j hj]
  · intro a ha hfix
    obtain ⟨s, hs, rfl⟩ := (qdMem_A_iff e hAL he a).1 ha
    rw [qdIota_conj] at hfix
    rw [hωfree s hs (qdIota_injective e hfix), map_one]

end CFSG.EvenSporadicStandard.M24Std
