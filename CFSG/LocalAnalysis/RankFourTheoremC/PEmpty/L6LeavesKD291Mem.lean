module

public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankFourTheoremC

theorem exists_B_of_mem {p : ℕ} [hpp : Fact p.Prime]
    {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    {S₀ P G : Type} [Group S₀] [Group P] [Group G] (hS₀ : Group.IsPerfect S₀)
    (π : S₀ →* P) (c : G → (S₀ →* S₀)) (Φ : G →* MulAut P) (Z : Subgroup G)
    (hcentral : ∀ w ∈ Z, ∀ B : G, w * B = B * w)
    (hker : ∀ B : G, Φ B = 1 → B ∈ Z)
    (e : ↥L ⧸ center ↥L ≃* P) (φ : S₀ →* ↥L) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hc : ∀ B s, π (c B s) = Φ B (π s)) (hcZ : ∀ w ∈ Z, ∀ B : G, c (w * B) = c B)
    (htorus : ∀ B : G, B ^ p = 1 → ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* S₀,
      Function.Injective (π.comp f) ∧ ∀ a, c B (f a) = f a)
    (hmem : ∃ B : G, Φ B = l212in_descend e (odC L x)) :
    ∃ B : G, Φ B = l212in_descend e (odC L x) ∧ B ^ p ∈ Z ∧ ∀ w ∈ Z, w ^ p ≠ B ^ p := by
  haveI := hS₀
  have hp : p.Prime := hpp.out
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨B, hB⟩ := hmem
  have hlift : ∀ s, odC L x (φ s) = φ (c B s) := by
    intro s
    refine l212in_alpha_phi e π φ hφπ (odC L x) (c B) (fun t => ?_) s
    rw [hc, hB]
  have hBZ : B ^ p ∈ Z := by
    refine hker _ ?_
    rw [map_pow, hB]
    change ((l212in_descend e).comp (odC L)) x ^ p = 1
    rw [← map_pow, hxp, map_one]
  have hnp : ∀ w ∈ Z, w ^ p ≠ B ^ p := by
    intro w hw hwp
    have hw' : w⁻¹ ∈ Z := Z.inv_mem hw
    have hBp : (w⁻¹ * B) ^ p = 1 := by
      have hc1 : Commute w⁻¹ B := hcentral w⁻¹ hw' B
      rw [hc1.mul_pow, inv_pow, hwp, inv_mul_cancel]
    obtain ⟨f, hfi, hfix⟩ := htorus (w⁻¹ * B) hBp
    rw [hcZ w⁻¹ hw' B] at hfix
    have hinj : Function.Injective (φ.comp f) := by
      intro a b hab
      apply hfi
      change π (f a) = π (f b)
      rw [← hφπ, ← hφπ]
      exact congrArg (fun l : ↥L => e (QuotientGroup.mk l)) hab
    have h3 := od_three_le_pRank_of_torus (L := L) (x := x) (φ.comp f) hinj (fun a => by
      change odC L x (φ (f a)) = φ (f a)
      rw [hlift, hfix])
    omega
  exact ⟨B, hB, hBZ, hnp⟩

theorem n_eq_p_of_mem {p n : ℕ} [hpp : Fact p.Prime] (hp5 : 5 ≤ p) (hpn : p ∣ n) (hn0 : 0 < n)
    {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    {S₀ P G : Type} [Group S₀] [Group P] [Group G] (hS₀ : Group.IsPerfect S₀)
    (π : S₀ →* P) (c : G → (S₀ →* S₀)) (Φ : G →* MulAut P) (Z : Subgroup G)
    (hcentral : ∀ w ∈ Z, ∀ B : G, w * B = B * w)
    (hker : ∀ B : G, Φ B = 1 → B ∈ Z)
    (e : ↥L ⧸ center ↥L ≃* P) (φ : S₀ →* ↥L) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hc : ∀ B s, π (c B s) = Φ B (π s)) (hcZ : ∀ w ∈ Z, ∀ B : G, c (w * B) = c B)
    (htorus : ∀ B : G, B ^ p = 1 → ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* S₀,
      Function.Injective (π.comp f) ∧ ∀ a, c B (f a) = f a)
    (hmono : p + 3 ≤ n → ∀ B : G, B ^ p ∈ Z → (∀ w ∈ Z, w ^ p ≠ B ^ p) →
      ∃ T : Subgroup S₀, IsElemAbelian p T ∧ p ^ (p + 1) ≤ Nat.card (T.map π) ∧
        ∀ t ∈ T, c B t ∈ T)
    (hmem : ∃ B : G, Φ B = l212in_descend e (odC L x)) : n = p := by
  haveI := hS₀
  have hp : p.Prime := hpp.out
  obtain ⟨B, hB, hBZ, hnp⟩ := exists_B_of_mem L hx hx2 hS₀ π c Φ Z hcentral hker e φ hφπ hc hcZ
    htorus hmem
  have hlift : ∀ s, odC L x (φ s) = φ (c B s) := by
    intro s
    refine l212in_alpha_phi e π φ hφπ (odC L x) (c B) (fun t => ?_) s
    rw [hc, hB]
  by_contra hne
  obtain ⟨k, hk⟩ := hpn
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at hk
      omega
    · simp at hk
      exact absurd hk hne
    · omega
  have hn3 : p + 3 ≤ n := by nlinarith
  obtain ⟨T, hT, hTc, hTn⟩ := hmono hn3 B hBZ hnp
  have hπε : π = (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))).comp φ :=
    MonoidHom.ext fun s => (hφπ s).symm
  have hmap : T.map π = (T.map φ).map (e.toMonoidHom.comp (QuotientGroup.mk' (center ↥L))) := by
    rw [hπε, Subgroup.map_map]
  have hcardE : p ^ (p + 1) ≤ Nat.card (T.map φ) := by
    rw [hmap] at hTc
    exact hTc.trans (Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective _ _))
  have h3 := od_three_le_pRank_of_normalizes (L := L) hp5 hx (E := T.map φ)
    (IsElemAbelian.map hT φ) hcardE (by
      rintro _ ⟨t, ht, rfl⟩
      rw [hlift]
      exact ⟨c B t, hTn t ht, rfl⟩)
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD291
