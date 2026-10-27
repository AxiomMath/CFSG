module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniComm
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODCore

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni

open CFSG.Open Subgroup

theorem n_eq_p_of_cover {p n : ℕ} [hpp : Fact p.Prime] (hp5 : 5 ≤ p) (hpn : p ∣ n) (hn0 : 0 < n)
    {Y : Type} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup p (Y ⧸ N) → N = ⊤)
    {x : Y} (hx : orderOf x = p) (hx2 : CFSG.Open.pRank p (centralizer ({x} : Set Y)) ≤ 2)
    {S₀ P G : Type} [Group S₀] [Group P] [Group G] (hS₀ : Group.IsPerfect S₀)
    (π : S₀ →* P) (c : G → (S₀ →* S₀)) (Φ : G →* MulAut P) (Z : Subgroup G)
    (hcentral : ∀ w ∈ Z, ∀ B : G, w * B = B * w)
    (hcomm : ∀ α β : MulAut P, α * β * α⁻¹ * β⁻¹ ∈ Φ.range)
    (hker : ∀ B : G, Φ B = 1 → B ∈ Z)
    (e : ↥L ⧸ center ↥L ≃* P) (φ : S₀ →* ↥L) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hc : ∀ B s, π (c B s) = Φ B (π s)) (hcZ : ∀ w ∈ Z, ∀ B : G, c (w * B) = c B)
    (htorus : ∀ B : G, B ^ p = 1 → ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* S₀,
      Function.Injective (π.comp f) ∧ ∀ a, c B (f a) = f a)
    (hmono : p + 3 ≤ n → ∀ B : G, B ^ p ∈ Z → (∀ w ∈ Z, w ^ p ≠ B ^ p) →
      ∃ T : Subgroup S₀, IsElemAbelian p T ∧ p ^ (p + 1) ≤ Nat.card (T.map π) ∧
        ∀ t ∈ T, c B t ∈ T) : n = p := by
  haveI := hS₀
  have hp : p.Prime := hpp.out
  set ψ : Y →* MulAut P := (l212in_descend e).comp (odC L) with hψ
  haveI : Φ.range.Normal :=
    ⟨fun a ha g => by
      have h := hcomm g a
      have h2 : g * a * g⁻¹ = (g * a * g⁻¹ * a⁻¹) * a := by group
      rw [h2]
      exact mul_mem h ha⟩
  have hxp : x ^ p = 1 := hx ▸ pow_orderOf_eq_one x
  obtain ⟨B, hB⟩ : ψ x ∈ Φ.range := map_mem_of_pow_eq_one Φ.range hcomm hperf ψ hxp
  have hlift : ∀ s, odC L x (φ s) = φ (c B s) := by
    intro s
    refine l212in_alpha_phi e π φ hφπ (odC L x) (c B) (fun t => ?_) s
    rw [hc, hB]
    rfl
  have hBZ : B ^ p ∈ Z := by
    refine hker _ ?_
    rw [map_pow, hB, ← map_pow, hxp, map_one]
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

theorem final_of_cover {p : ℕ} [hpp : Fact p.Prime] {L S₀ P : Type} [Group L] [Group S₀]
    [Group P] (π : S₀ →* P) (e : L ⧸ center L ≃* P) (φ : S₀ →* L)
    (hφ : Function.Surjective φ) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hcard : Nat.card π.ker = p) : Nonempty (S₀ ≃* L) ∨ Nonempty (L ≃* P) := by
  have hp : p.Prime := hpp.out
  have hle : φ.ker ≤ π.ker := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs ⊢
    rw [← hφπ, hs]
    simp
  have hdvd : Nat.card φ.ker ∣ p := hcard ▸ Subgroup.card_dvd_of_le hle
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · left
    have hker : φ.ker = ⊥ := Subgroup.card_eq_one.1 h1
    exact ⟨MulEquiv.ofBijective φ ⟨(MonoidHom.ker_eq_bot_iff φ).1 hker, hφ⟩⟩
  · right
    haveI : Finite π.ker := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
    have heq : φ.ker = π.ker :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, h1])
    set ε : L →* P := e.toMonoidHom.comp (QuotientGroup.mk' (center L)) with hε
    have hεinj : Function.Injective ε := by
      rw [injective_iff_map_eq_one]
      intro l hl
      obtain ⟨s, rfl⟩ := hφ l
      have hs : s ∈ π.ker := by
        rw [MonoidHom.mem_ker, ← hφπ]
        exact hl
      rw [← heq, MonoidHom.mem_ker] at hs
      exact hs
    have hεsurj : Function.Surjective ε := by
      intro y
      obtain ⟨a, rfl⟩ := e.surjective y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective a
      exact ⟨l, rfl⟩
    exact ⟨MulEquiv.ofBijective ε ⟨hεinj, hεsurj⟩⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni
