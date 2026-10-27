module

public import CFSG.CGT.Foote82.T66.MC2Nat
public import CFSG.CGT.Foote82.T66.MC2Twist
public import CFSG.CGT.Foote82.T66.MC2Heart
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3EGroup
import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.AutFactsA6

public section

namespace CFSG.CGT.Foote82

namespace MC2

open CFSG.Open CFSG.Quasithin.G11 CFSG.QuasithinUnique CFSG.RankThree.PartTwo Equiv

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem gx_eq_c3 : ((CFSG.QuasithinUnique.Setup.X3E.gx : alternatingGroup (Fin 6)) :
    Perm (Fin 6)) = c3 0 2 1 := by
  decide

@[expose] def c345 : alternatingGroup (Fin 6) :=
  ⟨c[3, 4, 5], by rw [Perm.mem_alternatingGroup]; decide⟩

theorem c345_eq_c3 : ((c345 : alternatingGroup (Fin 6)) : Perm (Fin 6)) = c3 3 5 4 := by
  decide

@[expose] def g345 : alternatingGroup (Fin 6) :=
  ⟨swap 0 3 * swap 1 4 * swap 2 5 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem g345_conj : g345 * CFSG.QuasithinUnique.Setup.X3E.gx * g345⁻¹ = c345 := by
  apply Subtype.ext
  decide

theorem card_tildeV_of_witness {L : Subgroup (GLV V)} {n : ℕ}
    {β : ↥(commSpace L ⊤) →+ altHeart n} (hβ : Function.Surjective β)
    (hker : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup) :
    Nat.card (TildeV L) = Nat.card (altHeart n) := by
  set C := (fixedSpace L).comap (commSpace L ⊤).subtype with hC
  have h1 := Submodule.card_eq_card_quotient_mul_card C
  have h2 := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup β.ker
  have h3 : Nat.card (↥(commSpace L ⊤) ⧸ β.ker) = Nat.card (altHeart n) :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective β hβ).toEquiv
  have h4 : Nat.card ↥β.ker = Nat.card ↥C := by rw [hker]; rfl
  rw [h3, h4] at h2
  have hpos : 0 < Nat.card ↥C := Nat.card_pos
  rw [h2, mul_comm] at h1
  exact (Nat.eq_of_mul_eq_mul_left hpos h1).symm

theorem fpf_of_conj_d0 {L : Subgroup (GLV V)} {α : ↥L →* alternatingGroup (Fin 6)}
    {β : ↥(commSpace L ⊤) →+ altHeart 6}
    (hker : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (hR : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      ∀ x : evenWeight 6, β w = (x : altHeart 6) →
        β w' = (evenWeightPerm (α ℓ : Perm (Fin 6)) x : altHeart 6))
    (ℓ : ↥L) {k : Perm (Fin 6)} (hk : k * (α ℓ : Perm (Fin 6)) * k⁻¹ = d0) :
    ∀ q, rhoT L ℓ q = q → q = 0 := by
  intro q hq
  obtain ⟨⟨w, hw⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hℓw : (ℓ : GLV V) w ∈ commSpace L ⊤ := invariant_commSpace_self L ℓ ℓ.2 w hw
  rw [rhoT_mk] at hq
  have hC : (ℓ : GLV V) w - w ∈ fixedSpace L := (mk_eq_mk_iff L hℓw hw).1 hq
  have hmem : ∀ (u : ↥(commSpace L ⊤)), u ∈ β.ker ↔ (u : V) ∈ fixedSpace L := fun u => by
    rw [hker]
    rfl
  have hββ : β ⟨(ℓ : GLV V) w, hℓw⟩ = β ⟨w, hw⟩ := by
    rw [← sub_eq_zero, ← map_sub]
    exact (hmem _).2 hC
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (β ⟨w, hw⟩)
  have h1 := hR ℓ ⟨w, hw⟩ ⟨(ℓ : GLV V) w, hℓw⟩ rfl x hx.symm
  rw [hββ, ← hx] at h1
  have h0 := heart6_fpf hk x h1.symm
  rw [hx] at h0
  have : (w : V) ∈ fixedSpace L := (hmem ⟨w, hw⟩).1 h0
  exact (Submodule.Quotient.mk_eq_zero _).2 this

theorem footeLemma24Twist {G L : Subgroup (GLV V)} {ψ : ↥G ≃* alternatingGroup (Fin 10)}
    {F : Set (Fin 10)} (hd : AltData G L ψ F) (hirr : IsIrr G ⊤) {τ : Fin 6 ↪ Fin 10}
    {nat : ↥L ≃* alternatingGroup (Fin 6)} (hτF : Set.range τ = F)
    (hnat : ∀ (ℓ : ↥L) (i : Fin 6), hd.jL ℓ (τ i) = τ ((nat ℓ : Perm (Fin 6)) i))
    {α : ↥L →* alternatingGroup (Fin 6)} (hαb : Function.Bijective α)
    {β : ↥(commSpace L ⊤) →+ altHeart 6} (hβ : Function.Surjective β)
    (hker : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (hR : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      ∀ x : evenWeight 6, β w = (x : altHeart 6) →
        β w' = (evenWeightPerm (α ℓ : Perm (Fin 6)) x : altHeart 6))
    (htw : ¬ ∃ π : Perm (Fin 6), ∀ ℓ, (α ℓ : Perm (Fin 6)) = π * (nat ℓ : Perm (Fin 6)) * π⁻¹) :
    False := by
  let θ : MulAut (alternatingGroup (Fin 6)) := nat.symm.trans (MulEquiv.ofBijective α hαb)
  have hθ : ∀ ℓ, θ (nat ℓ) = α ℓ := fun ℓ => by
    change MulEquiv.ofBijective α hαb (nat.symm (nat ℓ)) = α ℓ
    rw [MulEquiv.symm_apply_apply]
    rfl
  rcases CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.mulAut_alt6_cases θ with
    ⟨π, hπ⟩ | ⟨k, hk⟩
  · exact htw ⟨π, fun ℓ => by rw [← hθ ℓ, hπ, MulAut.conjNormal_apply]⟩
  set gx := CFSG.QuasithinUnique.Setup.X3E.gx
  set ℓ₀ : ↥L := nat.symm gx with hℓ₀
  set ℓ₁ : ↥L := nat.symm c345 with hℓ₁
  have hα₀ : α ℓ₀ = θ gx := by rw [← hθ ℓ₀, hℓ₀, MulEquiv.apply_symm_apply]
  have hα₁ : α ℓ₁ = θ g345 * θ gx * (θ g345)⁻¹ := by
    rw [← hθ ℓ₁, hℓ₁, MulEquiv.apply_symm_apply, ← g345_conj, map_mul, map_mul, map_inv]
  have hk' : (k : Perm (Fin 6)) * (θ gx : Perm (Fin 6)) * (k : Perm (Fin 6))⁻¹ = d0 := by
    have h := hk
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    exact h
  have hf₀ := fpf_of_conj_d0 hker hR ℓ₀ (k := k) (by rw [hα₀]; exact hk')
  have hf₁ := fpf_of_conj_d0 hker hR ℓ₁ (k := (k : Perm (Fin 6)) * (θ g345 : Perm (Fin 6))⁻¹)
    (by
      rw [hα₁]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev, inv_inv]
      rw [← hk']
      group)
  have hj₀ : hd.jL ℓ₀ = c3 (τ 0) (τ 2) (τ 1) :=
    hd.jL_eq_c3 hτF hnat (by decide) (by decide) (by decide)
      (by rw [hℓ₀, MulEquiv.apply_symm_apply]; exact gx_eq_c3)
  have hj₁ : hd.jL ℓ₁ = c3 (τ 3) (τ 5) (τ 4) :=
    hd.jL_eq_c3 hτF hnat (by decide) (by decide) (by decide)
      (by rw [hℓ₁, MulEquiv.apply_symm_apply]; exact c345_eq_c3)
  have hnodup : [τ 0, τ 2, τ 1, τ 3, τ 5, τ 4].Nodup := by
    have : ([0, 2, 1, 3, 5, 4] : List (Fin 6)).Nodup := by decide
    simpa using this.map τ.injective
  have hdim : Module.finrank (ZMod 2) (TildeV L) ≤ 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hc := card_tildeV_of_witness hβ hker
    rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_even (by norm_num)
      (by decide)] at hc
    have h2 := FiniteField.pow_finrank_eq_natCard 2 (TildeV L)
    rw [hc] at h2
    have : Module.finrank (ZMod 2) (TildeV L) = 4 :=
      Nat.pow_right_injective (le_refl 2) (h2.trans (by norm_num))
    omega
  exact twist_false (by norm_num) hd hirr hdim hnodup hj₀ hj₁ hf₀ hf₁

theorem case_alt (h24 : FooteLemma24) {G L : Subgroup (GLV V)} {s : GLV V} (h : StdForm G L s)
    (hq : G = layerIn G) {m : ℕ} {ψ : ↥G ≃* alternatingGroup (Fin m)} {F : Set (Fin m)}
    (hd : AltData G L ψ F) {n : ℕ} (hn : 6 ≤ n) (hA : IsAltNaturalModule L n) : False := by
  obtain ⟨α, hα, β, hβ, hker, hR⟩ := hA
  have := hd.isSimpleGroup
  have : Nontrivial (alternatingGroup (Fin n)) := nontrivial_alt (by omega)
  have hinj := injective_of_isSimpleGroup α hα
  have hcard := hd.card_eq_of_surjective α hα
  rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_alternatingGroup_fin (by omega)] at hcard
  have hFn : F.ncard = n := factorial_div_two_inj (by have := hd.five_le; omega) (by omega) hcard
  have hm : m = n + 4 := by have := hd.card_add; omega
  subst hm
  obtain ⟨τ, nat, hτF, hnat⟩ := hd.exists_nat hFn
  let αe : ↥L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective α ⟨hinj, hα⟩
  have natural : ∀ π : Perm (Fin n),
      (∀ ℓ, (α ℓ : Perm (Fin n)) = π * (nat ℓ : Perm (Fin n)) * π⁻¹) → False := by
    intro π hαπ
    have hNat := isNaturalHeartFor_of_conj hd.le ψ τ nat hnat hαπ hβ hker hR
    have hrange : Set.range (π.symm.toEmbedding.trans τ) = F := by
      rw [← hτF]
      ext x
      simp only [Set.mem_range, Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
      exact ⟨fun ⟨i, hi⟩ => ⟨π.symm i, hi⟩, fun ⟨i, hi⟩ => ⟨π i, by simpa using hi⟩⟩
    have hH := h24 V G L n ψ _ hn hd.le (by rw [hrange]; exact hd.img_eq)
      h.extremal.setup.irr hNat
    apply h.extremal.not_concl
    refine Or.inr (Or.inl ⟨n, 2, hn, by norm_num, ⟨αe⟩, ?_⟩)
    rw [← hq]
    exact hH
  rcases (show n = 6 ∨ 7 ≤ n by omega) with rfl | h7
  · by_cases hnatural : ∃ π : Perm (Fin 6),
        ∀ ℓ, (α ℓ : Perm (Fin 6)) = π * (nat ℓ : Perm (Fin 6)) * π⁻¹
    · obtain ⟨π, hπ⟩ := hnatural
      exact natural π hπ
    · exact footeLemma24Twist hd h.extremal.setup.irr hτF hnat ⟨hinj, hα⟩ hβ hker hR hnatural
  ·
    let θ : MulAut (alternatingGroup (Fin n)) := nat.symm.trans αe
    have hθ : ∀ ℓ, θ (nat ℓ) = α ℓ := fun ℓ => by
      change αe (nat.symm (nat ℓ)) = α ℓ
      rw [MulEquiv.symm_apply_apply]
      rfl
    obtain ⟨π, hπ⟩ :=
      CFSG.AlternatingAutomorphism.exists_perm_conj_of_degree_eq_five_or_seven_le (Or.inr h7) θ
    exact natural π fun ℓ => by rw [← hθ ℓ, hπ]

end MC2

end CFSG.CGT.Foote82
