module

public import CFSG.ClassicalInvolution.Asc77.AscT7DClique

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7D

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

@[expose] noncomputable def imgQ (ρ : Thompson.Rep Ω W) : ↥(muGroup Ω W) := ⟨ρ.img, rep_img_mem ρ⟩

omit [Finite G] in
theorem imgQ_mem (ρ : Thompson.Rep Ω W) : imgQ ρ ∈ Thompson.muDelta Ω W := rep_mem_muDelta ρ

theorem exists_swap_equiv [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting p f Ω K K' z)
    (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) :
    ∃ e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4), ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap := by
  obtain ⟨⟨d₀, hd₀⟩, hcl⟩ := c23_1_clique_proved (p := p) (f := f) G Ω K K' z hs W hW
  have hst : AscStand p f Ω K := hs.stand
  have hP : PartIHyp p f Ω := ⟨hst.odd, hst.five, hst.hyp, hst.aEmpty⟩
  have hTT : Star3T.IsTT (Thompson.muDelta Ω W) :=
    Thompson.isTT_muDelta hst.odd hst.five hst.hyp hW (thompsonCube G Ω hP W hW)
  have hS : Star3T.IsStar (Thompson.muDelta Ω W) :=
    Thompson.isStar_muDelta hst.odd hst.five hst.hyp hW (thompsonStar G Ω hP W hW)
  by_cases hconn : ∀ d ∈ Thompson.muDelta Ω W, ∀ a ∈ Thompson.muDelta Ω W,
      Star3T.Conn (Thompson.muDelta Ω W) d a
  · exfalso
    set Δ := Thompson.muDelta Ω W with hΔ
    obtain ⟨d', hne, hcent⟩ : ∃ d', d₀ ≠ d' ∧ Star3T.cent Δ d₀ = {d₀, d'} := by
      obtain ⟨x, y, hxy, hxy'⟩ := Set.ncard_eq_two.mp (hcl d₀ hd₀)
      have hdx : d₀ ∈ ({x, y} : Set _) := hxy' ▸ Star3T.self_mem_cent hd₀
      rcases hdx with rfl | hdy
      · exact ⟨y, hxy, hxy'⟩
      · rw [Set.mem_singleton_iff] at hdy
        subst hdy
        exact ⟨x, fun e => hxy e.symm, by rw [hxy', Set.pair_comm]⟩
    have hd'c : d' ∈ Star3T.cent Δ d₀ := by rw [hcent]; exact Or.inr rfl
    have hd'Δ : d' ∈ Δ := hd'c.1
    have hcomm : d₀ * d' = d' * d₀ := hd'c.2.symm
    have hcent' : Star3T.cent Δ d' = {d₀, d'} := by
      have hsub : ({d₀, d'} : Set _) ⊆ Star3T.cent Δ d' := by
        intro x hx
        rcases hx with rfl | rfl
        · exact ⟨hd₀, hcomm⟩
        · exact Star3T.self_mem_cent hd'Δ
      exact (Set.eq_of_subset_of_ncard_le hsub
        (by rw [hcl d' hd'Δ, Set.ncard_pair hne]) (Set.toFinite _)).symm
    have hall : ∀ a, Relation.ReflTransGen (Star3T.Adj Δ) d₀ a → a = d₀ ∨ a = d' := by
      intro a hb
      induction hb with
      | refl => exact Or.inl rfl
      | @tail b c _ hbc ih =>
        obtain ⟨-, hc, hbc⟩ := hbc
        rcases ih with rfl | rfl
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent] at this
          exact this
        · have : c ∈ Star3T.cent Δ b := ⟨hc, hbc.symm⟩
          rw [hcent'] at this
          exact this
    have hΔeq : Δ = {d₀, d'} := by
      ext a
      constructor
      · exact fun ha => hall a (hconn d₀ hd₀ a ha)
      · rintro (rfl | rfl)
        · exact hd₀
        · exact hd'Δ
    have hgen : Subgroup.closure ({d₀, d'} : Set ↥(muGroup Ω W)) = ⊤ := by
      rw [← hΔeq]
      exact hTT.closure_eq_top
    obtain ⟨e₁⟩ := T7B.nonempty_mulEquiv_klein (hTT.mul_self d₀ hd₀) (hTT.mul_self d' hd'Δ)
      (hTT.ne_one d₀ hd₀) (hTT.ne_one d' hd'Δ) hne hcomm hgen
    obtain ⟨e₂⟩ := hS4
    have h1 := Nat.card_congr e₁.toEquiv
    have h2 := Nat.card_congr e₂.toEquiv
    rw [h2] at h1
    have h3 : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      rfl
    have h4 : Nat.card (Multiplicative (ZMod 2 × ZMod 2)) = 4 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    omega
  · push Not at hconn
    obtain ⟨d, hd, a, ha, hnc⟩ := hconn
    exact Star3T.exists_mulEquiv_perm_four hTT hS hd ha hnc (hcl d hd)

@[expose] def conjRep (hΩ : HypOmegaMod p f Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) : Thompson.Rep Ω W where
  K := conjSub n ρ.K
  R := conjSub n ρ.R
  r := n * ρ.r * n⁻¹
  hK := hΩ.conjInvariant n ρ.K ρ.hK
  hR := Thompson.conjSub_mem_D hΩ ρ.hR hn
  hRK := ρ.hRK.conj n
  hr := conj_mem_conjSub ρ.hr
  hrW := fun h => ρ.hrW ((Thompson.mem_normalizer_iff_of_mem hn _).mp h)

omit [Finite G] in
theorem conjRep_img (hΩ : HypOmegaMod p f Ω) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W) :
    (conjRep hΩ hn ρ).img = Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ := by
  show Thompson.piG W (n * ρ.r * n⁻¹) = Thompson.piG W n * Thompson.piG W ρ.r *
    (Thompson.piG W n)⁻¹
  rw [Thompson.piG_mul (Subgroup.mul_mem _ hn ρ.r_mem_normalizer) (Subgroup.inv_mem _ hn),
    Thompson.piG_mul hn ρ.r_mem_normalizer, Thompson.piG_inv hn]

theorem conj_stable (c : Thompson.Ctx p f Ω W) {n : G} (hn : n ∈ Subgroup.normalizer (W : Set G))
    (ρ : Thompson.Rep Ω W)
    (h : Thompson.piG W n * ρ.img * (Thompson.piG W n)⁻¹ = ρ.img) :
    conjSub n ρ.K = ρ.K ∧
      ∀ w ∈ W, (n * ρ.r * n⁻¹) * w * (n * ρ.r * n⁻¹)⁻¹ = ρ.r * w * ρ.r⁻¹ := by
  have himg : (conjRep c.hΩ hn ρ).img = ρ.img := by rw [conjRep_img, h]
  refine ⟨c.K_eq_of_img_eq (conjRep c.hΩ hn ρ) ρ himg, fun w hw => ?_⟩
  exact Thompson.conj_eq_of_piG_eq c.hp c.hq c.hΩ c.hW ρ.r_mem_normalizer
    (conjRep c.hΩ hn ρ).r_mem_normalizer himg.symm hw

omit [Finite G] in
theorem exists_normalizer_of_mem_muGroup (y : ↥(muGroup Ω W)) :
    ∃ m ∈ Subgroup.normalizer (W : Set G), (y : NQuot (W ⊔ OCW W)) = Thompson.piG W m := by
  obtain ⟨m, hm, hy⟩ := Thompson.mem_muGroup_iff.mp y.2
  exact ⟨m, Thompson.MGrp_sup_le_normalizer Ω W hm, hy⟩

end T7D

end CFSG.ClassicalInvolution.Asc77
