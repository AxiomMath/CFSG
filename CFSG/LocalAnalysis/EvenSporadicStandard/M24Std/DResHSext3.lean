module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.QuadDataOmega
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.TransData
public import Certificates.Certificate25761

public section

namespace CFSG.EvenSporadicStandard.M24Std.DResH

open Subgroup CFSG.Blueprint CFSG.Sporadic.Schreier CFSG.QuasithinUnique.Setup.X1

@[expose] def Sext3A6 {G : Type} [Group G] (L A : Subgroup G) : Prop :=
  ∃ w a b : G, w ∈ egNL L A ∧ a ∈ egNL L A ∧ b ∈ egNL L A ∧ w * w * w = 1 ∧ a * a * a = 1 ∧
    b * b * b = 1 ∧ (∀ x ∈ A, w * x * w⁻¹ = x → x = 1) ∧
    (∀ n ∈ egNL L A, ∃ x ∈ A, n * w * n⁻¹ = w * x ∨ n * w * n⁻¹ = w⁻¹ * x) ∧
    ∃ x ∈ A, a * b * a⁻¹ * b⁻¹ = w * x ∨ a * b * a⁻¹ * b⁻¹ = w⁻¹ * x

variable {G : Type} [Group G] {L A : Subgroup G}

theorem omegaW_pinned
    (e : L ≃* S24) (hAL : A ≤ L) (he : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l) :
    qdIota e qdOmega ∈ egNL L A ∧
      qdIota e qdOmega * qdIota e qdOmega * qdIota e qdOmega = 1 ∧
      (∀ n ∈ egNL L A,
        (∀ a ∈ A, (n * qdIota e qdOmega * n⁻¹) * a * (n * qdIota e qdOmega * n⁻¹)⁻¹ =
          qdIota e qdOmega * a * (qdIota e qdOmega)⁻¹) ∨
        (∀ a ∈ A, (n * qdIota e qdOmega * n⁻¹) * a * (n * qdIota e qdOmega * n⁻¹)⁻¹ =
          (qdIota e qdOmega)⁻¹ * a * qdIota e qdOmega)) ∧
      ∀ a ∈ A, qdIota e qdOmega * a * (qdIota e qdOmega)⁻¹ = a → a = 1 := by
  obtain ⟨hQlist, hQmem, hQhom, hQinj, hQfx⟩ := Certificates.certificate24849
  obtain ⟨hωN, hω3, hωfree, hψ, henum⟩ := Certificates.certificate24848
  refine ⟨qdIota_mem_egNL e hAL he hωN.norm, ?_, ?_, ?_⟩
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

theorem omegaStrong_pinned
    (e : L ≃* S24) (hAL : A ≤ L)
    (he : ∀ x : L, (x : G) ∈ A ↔ e x ∈ m24E1l) :
    ∀ n ∈ egNL L A, ∃ a ∈ A, n * qdIota e qdOmega * n⁻¹ = qdIota e qdOmega * a ∨
      n * qdIota e qdOmega * n⁻¹ = (qdIota e qdOmega)⁻¹ * a := by
  have hF := sextetFacts_of_type (L := L) (A := A) ⟨hAL, e, he⟩
  obtain ⟨hw, -, hconj, -⟩ := omegaW_pinned e hAL he
  intro n hn
  have hnL : n ∈ L := (mem_inf.1 hn).2
  have hwL : qdIota e qdOmega ∈ L := (mem_inf.1 hw).2
  have huL : n * qdIota e qdOmega * n⁻¹ ∈ L :=
    L.mul_mem (L.mul_mem hnL hwL) (L.inv_mem hnL)
  set w : G := qdIota e qdOmega with hwdef
  set u : G := n * w * n⁻¹ with hu
  rcases hconj n hn with h1 | h1
  · have hc : w⁻¹ * u ∈ A := by
      refine hF.cent _ (L.mul_mem (L.inv_mem hwL) huL) fun a ha => ?_
      calc w⁻¹ * u * a = w⁻¹ * (u * a * u⁻¹) * u := by group
        _ = w⁻¹ * (w * a * w⁻¹) * u := by rw [h1 a ha]
        _ = a * (w⁻¹ * u) := by group
    exact ⟨_, hc, Or.inl (by group)⟩
  · have hc : w * u ∈ A := by
      refine hF.cent _ (L.mul_mem hwL huL) fun a ha => ?_
      calc w * u * a = w * (u * a * u⁻¹) * u := by group
        _ = w * (w⁻¹ * a * w) * u := by rw [h1 a ha]
        _ = a * (w * u) := by group
    exact ⟨_, hc, Or.inr (by group)⟩

theorem sext3a6_of_type
    {G : Type} [Group G] {L A : Subgroup G} (h : SextetType L A) : Sext3A6 L A := by
  obtain ⟨hAL, e, he⟩ := h
  obtain ⟨hwN, hw3, -, hfix⟩ := omegaW_pinned e hAL he
  obtain ⟨hna, hnb, ha3, hb3, x, hx, hxc⟩ := Certificates.certificate25761
  refine ⟨qdIota e qdOmega, qdIota e sext3A, qdIota e sext3B, hwN,
    qdIota_mem_egNL e hAL he hna.norm, qdIota_mem_egNL e hAL he hnb.norm, hw3, ?_, ?_, hfix,
    omegaStrong_pinned e hAL he, qdIota e x, (qdIota_mem_A e he x).2 hx, Or.inl ?_⟩
  · rw [← map_mul, ← map_mul, ha3, map_one]
  · rw [← map_mul, ← map_mul, hb3, map_one]
  · have h1 := congrArg (qdIota e) hxc
    simpa only [map_mul, map_inv] using h1

end CFSG.EvenSporadicStandard.M24Std.DResH
