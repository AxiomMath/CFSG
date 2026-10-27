module

public import CFSG.ClassicalInvolution.Q3.TL4ExitTwoU3C

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Check

variable {G : Type} [Group G] [Finite G] {M : Type} [Group M] [DecidableEq M] {ψ : G →* M}

theorem false_of_mixed (hψi : Function.Injective ψ) {P A : Subgroup M}
    (hLs : ∀ m, m ∈ A ↔ ∃ y, ψ y = m) {t : G} (hF : ExitFacts P A (ψ t)) {N : Subgroup G}
    [N.Normal] (hLN : ∀ y, ψ y ∈ P ↔ y ∈ N) {Δ : Set (Subgroup G)}
    (hΔ : PhilipHall.Frame.Thm4Twin.TwinT4Hyp 3 G Δ)
    {K K' : Subgroup G} (hK : K ∈ Δ) (hK' : K' ∈ Δ) (hKt : IsUniqueInvolution K t)
    (hK't : IsUniqueInvolution K' t) {a b a' b' : G} (hp : QPair K t a b)
    (hp' : QPair K' t a' b') (hKq : ∀ r ∈ K, r ∈ q8List t a b)
    (eK' : ↥K' ≃* QuaternionGroup 2) (hin : ψ a ∈ P ∧ ψ b ∈ P)
    (hout : ¬(ψ a' ∈ P ∧ ψ b' ∈ P)) : False := by
  classical
  have hL : ∀ y, ψ y ∈ A := fun y => (hLs _).2 ⟨y, rfl⟩
  have hpin := pair_of_qpair hL hp
  have hpout := pair_of_qpair hL hp'
  obtain ⟨hU, ro₁, ro₂, ri₁, ri₂, g₀, hro, hro2, hri, hri₁, hri₂, hg₀, ⟨c, hc, hcc, hct⟩, d, hd, x,
    hx, hdx⟩ := hF
  have hro' := hU _ _ _ _ hro hpout (iff_of_false hro2 hout)
  have hri' := hU _ _ _ _ hri hpin (iff_of_true ⟨hri₁, hri₂⟩ hin)
  have hin' := hU _ _ _ _ hpin hri (iff_of_true hin ⟨hri₁, hri₂⟩)
  have hmap : ∀ u v w : G, q8B (ψ u) (ψ v) (ψ w) = (q8List u v w).map ψ := fun u v w =>
    q8B_eq (ι := ψ) u v w
  obtain ⟨c₀, hc₀, rfl⟩ := List.mem_map.1 (hmap t a' b' ▸ hro' c hc)
  obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.1 (hmap t a' b' ▸ hro' d hd)
  obtain ⟨x₀, hx₀, rfl⟩ := List.mem_map.1 (hmap t a b ▸ hri' x hx)
  obtain ⟨g, rfl⟩ := (hLs g₀).1 hg₀
  have hc₀K' : c₀ ∈ K' := mem_of_mem_q8List hp'.ha hp'.hb hp'.haa hc₀
  have hd₀K' : d₀ ∈ K' := mem_of_mem_q8List hp'.ha hp'.hb hp'.haa hd₀
  have hx₀K : x₀ ∈ K := mem_of_mem_q8List hp.ha hp.hb hp.haa hx₀
  have hc₀2 : c₀ * c₀ = t := hψi (by rw [map_mul, hcc])
  rw [hLN, hLN] at hin
  have hKN : K ≤ N := fun r hr => mem_of_mem_q8List hin.1 hin.2 hp.haa (hKq r hr)
  set J := conjSub g K' with hJdef
  have hJΔ : J ∈ Δ := hΔ.hyp.conjInvariant g K' hK'
  have hJs : IsUniqueInvolution J (g * t * g⁻¹) := hK't.conj g
  have hJN : ¬ J ≤ N := by
    intro hle
    have hmem : ∀ y ∈ K', y ∈ N := fun y hy => by
      have h1 := (inferInstance : N.Normal).conj_mem _ (hle (conj_mem_conjSub hy)) g⁻¹
      simpa [mul_assoc] using h1
    apply hout
    rw [hLN, hLN]
    exact ⟨hmem _ hp'.ha, hmem _ hp'.hb⟩
  have hKJ : K ≠ J := fun h0 => hJN (h0 ▸ hKN)
  have hK'8 : Nat.card ↥K' = 8 := by
    rw [Nat.card_congr eK'.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hJ8 : Nat.card ↥J = 8 := by
    rw [hJdef, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hK'8]
  have hJ2 : IsPGroup 2 ↥J := IsPGroup.of_card (n := 3) (by rw [hJ8]; norm_num)
  set c₁ := g * c₀ * g⁻¹ with hc₁
  have hc₁J : c₁ ∈ J := conj_mem_conjSub hc₀K'
  have hc₁t : c₁ * t = t * c₁ := hψi (by rw [hc₁]; simp only [map_mul, map_inv]; exact hct)
  have hc₁2 : c₁ * c₁ = g * t * g⁻¹ := by rw [hc₁, ← hc₀2]; group
  have hc₁4 : orderOf c₁ = 4 := orderOf_eq_four hc₁2 hJs.sq hJs.ne_one
  have hc₁p : IsPGroup 2 ↥(Subgroup.zpowers c₁) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hc₁4]; norm_num)
  have hnc : ¬ ∀ w ∈ J, c₁ * w = w * c₁ := by
    intro hall
    have hq : ∀ q : QuaternionGroup 2, q * q ≠ 1 → ∃ r, q * r ≠ r * q := by decide
    obtain ⟨r, hr⟩ := hq (eK' ⟨c₀, hc₀K'⟩) (by
      rw [← map_mul, Ne, MulEquiv.map_eq_one_iff]
      intro h0
      exact hKt.ne_one (by simpa [← hc₀2] using congrArg Subtype.val h0))
    set w₀ := eK'.symm r with hw₀
    have h1 := hall (g * (w₀ : G) * g⁻¹) (conj_mem_conjSub w₀.2)
    have h2 : c₀ * (w₀ : G) = (w₀ : G) * c₀ := by
      have h3 : g * (c₀ * w₀) * g⁻¹ = g * (w₀ * c₀) * g⁻¹ := by rw [hc₁] at h1; simpa [mul_assoc]
        using h1
      simpa using h3
    apply hr
    have h4 : (⟨c₀, hc₀K'⟩ : ↥K') * w₀ = w₀ * ⟨c₀, hc₀K'⟩ := Subtype.ext h2
    have := congrArg eK' h4
    rwa [map_mul, map_mul, hw₀, MulEquiv.apply_symm_apply] at this
  have hJR : J ∈ RSet Δ :=
    mem_RSet_of_isSylow2In hJΔ ⟨le_rfl, hJ2, fun V' hV' _ hle => le_antisymm hV' hle⟩
  have hrel : (Subgroup.zpowers c₁).relIndex J = 2 := by
    have hle : Subgroup.zpowers c₁ ≤ J := Subgroup.zpowers_le.mpr hc₁J
    have h1 := Subgroup.card_mul_index ((Subgroup.zpowers c₁).subgroupOf J)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, Nat.card_zpowers, hc₁4,
      hJ8] at h1
    rw [Subgroup.relIndex]
    omega
  have hc₁N : c₁ ∈ Subgroup.normalizer (K : Set G) :=
    hΔ.hyp.omega5 K hK J hJΔ hKJ t hKt c₁ hc₁J hnc hc₁p hc₁t
  have hstar : J ∈ omegaStarNbr Δ K :=
    ⟨hJΔ, Ne.symm hKJ, Subgroup.zpowers c₁,
      ⟨J, hJR, Subgroup.zpowers_le.mpr hc₁J, inferInstance, hrel⟩,
      Subgroup.zpowers_le.mpr hc₁J, Subgroup.zpowers_le.mpr hc₁N⟩
  have hnot : J ∉ omegaNbr Δ K := by
    rintro ⟨-, -, R, hR, hRJ, hRN⟩
    have h8 := Sec6Gen.eight_le_of_mem_RSet hΔ.hyp hR
    have hRJ' : R = J := Subgroup.eq_of_le_of_card_ge hRJ (by rw [hJ8]; exact h8)
    have hd₁ : g * d₀ * g⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      hRN (hRJ' ▸ conj_mem_conjSub hd₀K')
    have hy : g * d₀ * g⁻¹ * x₀ * (g * d₀ * g⁻¹)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp hd₁ x₀).mp hx₀K
    apply hdx
    have h2 := hin' _ (hmap t a b ▸ List.mem_map_of_mem (hKq _ hy))
    simpa only [map_mul, map_inv] using h2
  obtain ⟨g', -, hg'⟩ := hΔ.aEmpty K hK J hstar hnot t (g * t * g⁻¹) hKt hJs
  apply hJN
  rw [← hg']
  rintro _ ⟨k, hk, rfl⟩
  exact (inferInstance : N.Normal).conj_mem k (hKN hk) g'

end CFSG.ClassicalInvolution.Q3.TL4.ExitTwo.U3
