module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Inner
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Quasithin CFSG.Blueprint CFSG.QuasithinUnique.Setup.Family
  CFSG.ComponentClassification.OuterAutomorphisms

section Invol

variable {W : Type} [CommGroup W]

theorem le_of_autInner_invol [Finite W] (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S)
    (hAut : ∀ φ : S ≃* S, (∀ x, φ (φ x) = x) → ∃ s : S, ∀ x, φ x = s * x * s⁻¹) : E ≤ L := by
  intro b hbE
  have hbN : b ∈ Subgroup.normalizer (L : Set (MulAut W)) := hE hbE
  have hb2 : b * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  let ψ : CQ L ≃* CQ L :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) (conjAut L hbN)
      (Subgroup.map_center_eq (conjAut L hbN))
  have hψψ : ∀ q : CQ L, ψ (ψ q) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    show (QuotientGroup.mk (conjAut L hbN (conjAut L hbN x)) : CQ L) = QuotientGroup.mk x
    congr 1
    apply Subtype.ext
    show b * (b * (x : MulAut W) * b⁻¹) * b⁻¹ = (x : MulAut W)
    have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb2
    rw [hbi]
    calc b * (b * (x : MulAut W) * b) * b = (b * b) * (x : MulAut W) * (b * b) := by group
      _ = (x : MulAut W) := by rw [hb2]; group
  have hφinv : ∀ y : S, (e.symm.trans (ψ.trans e)) ((e.symm.trans (ψ.trans e)) y) = y := by
    intro y
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [hψψ]
    simp
  obtain ⟨s, hs⟩ := hAut (e.symm.trans (ψ.trans e)) hφinv
  obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (s := Subgroup.center ↥L) (e.symm s)
  have hψ : ∀ q : CQ L, ψ q = QuotientGroup.mk l * q * (QuotientGroup.mk l)⁻¹ := by
    intro q
    have h1 := hs (e q)
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
    have h2 : e (ψ q) = e (QuotientGroup.mk l * q * (QuotientGroup.mk l)⁻¹) := by
      rw [map_mul, map_mul, map_inv, hl, h1]
      simp
    exact e.injective h2
  set c : MulAut W := (l : MulAut W)⁻¹ * b with hc
  have hlN : (l : MulAut W) ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    Subgroup.le_normalizer l.2
  have hcN : c ∈ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normalizer (L : Set (MulAut W))).mul_mem
      ((Subgroup.normalizer (L : Set (MulAut W))).inv_mem hlN) hbN
  have hθ : ∀ x : ↥L, conjAut L hcN x = l⁻¹ * conjAut L hbN x * l := by
    intro x
    apply Subtype.ext
    show c * (x : MulAut W) * c⁻¹ = ((l : MulAut W)⁻¹) * (b * x * b⁻¹) * (l : MulAut W)
    rw [hc]
    group
  have hcentral : ∀ x : ↥L, x⁻¹ * conjAut L hcN x ∈ Subgroup.center ↥L := by
    intro x
    rw [← QuotientGroup.eq, hθ]
    have h3 : (QuotientGroup.mk (conjAut L hbN x) : CQ L) = ψ (QuotientGroup.mk x) := rfl
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h3, hψ]
    group
  let f : ↥L →* ↥(Subgroup.center ↥L) :=
    MonoidHom.mk' (fun x => ⟨x⁻¹ * conjAut L hcN x, hcentral x⟩) (by
      intro x y
      apply Subtype.ext
      have hz := Subgroup.mem_center_iff.1 (hcentral x) y⁻¹
      show (x * y)⁻¹ * conjAut L hcN (x * y) = (x⁻¹ * conjAut L hcN x) * (y⁻¹ * conjAut L hcN y)
      calc (x * y)⁻¹ * conjAut L hcN (x * y) = y⁻¹ * (x⁻¹ * conjAut L hcN x) * conjAut L hcN y := by
            rw [map_mul]; group
        _ = (x⁻¹ * conjAut L hcN x) * y⁻¹ * conjAut L hcN y := by rw [hz]
        _ = (x⁻¹ * conjAut L hcN x) * (y⁻¹ * conjAut L hcN y) := by group)
  have hfker : (⊤ : Subgroup ↥L) ≤ f.ker := by
    rw [← hperf.commutator_eq_top, commutator_def]
    refine Subgroup.commutator_le.2 fun g₁ _ g₂ _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f g₁).2 (f g₂)).symm)
  have hcomm : ∀ x ∈ L, x * c = c * x := by
    intro x hx
    have h1 := f.mem_ker.1 (hfker (Subgroup.mem_top ⟨x, hx⟩))
    have h2 := congrArg (fun z : ↥(Subgroup.center ↥L) => ((z : ↥L) : MulAut W)) h1
    simp only [Subgroup.coe_one] at h2
    have h3 : (x : MulAut W)⁻¹ * (c * x * c⁻¹) = 1 := h2
    have h5 : c * x * c⁻¹ = x := (inv_mul_eq_one.1 h3).symm
    calc x * c = (c * x * c⁻¹) * c := by rw [h5]
      _ = c * x := by group
  have hcC : c ∈ Subgroup.centralizer (L : Set (MulAut W)) := Subgroup.mem_centralizer_iff.2 hcomm
  have hcH : c ∈ L ⊔ E := Subgroup.mul_mem_sup (L.inv_mem l.2) hbE
  have hcL : c ∈ L := centralizer_inf_le hW hirr hE hEel ⟨hcH, hcC⟩
  have hbc : b = (l : MulAut W) * c := by rw [hc]; group
  rw [hbc]
  exact L.mul_mem l.2 hcL

end Invol

theorem autInner_of_outer_odd {G : Type*} [Group G] (hodd : Odd (Nat.card (Outer G)))
    (φ : G ≃* G) (hφ : ∀ x, φ (φ x) = x) : ∃ s : G, ∀ x, φ x = s * x * s⁻¹ := by
  let q : Outer G := QuotientGroup.mk φ
  have h2 : q ^ 2 = 1 := by
    rw [sq, ← QuotientGroup.mk_mul]
    have : φ * φ = 1 := by
      ext x
      exact hφ x
    rw [this, QuotientGroup.mk_one]
  have hdvd : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  have hdvd' : orderOf q ∣ Nat.card (Outer G) := orderOf_dvd_natCard q
  have h1 : orderOf q = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · rw [h] at hdvd'
      exact absurd hodd (by rw [Nat.not_odd_iff_even]; exact even_iff_two_dvd.2 hdvd')
  have hq1 : q = 1 := orderOf_eq_one_iff.1 h1
  have hmem : φ ∈ inner G := (QuotientGroup.eq_one_iff φ).1 hq1
  obtain ⟨s, hs⟩ := hmem
  exact ⟨s, fun x => by rw [← hs]; rfl⟩

section Generic

variable {W : Type} [CommGroup W] [Finite W]

theorem weight_lt_of_outer_odd_cover (hW : ∀ w : W, w * w = 1) {L E : Subgroup (MulAut W)}
    (hperf : Group.IsPerfect ↥L) (hirr : IsIrrOn L)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E)
    {S : Type} [Group S] (e : CQ L ≃* S) {r ρ : ℕ} (hrρ : r < ρ)
    (hOut : Odd (Nat.card (Outer S)))
    (hCover : ∀ (E : Type) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* S),
      Function.Surjective π → π.ker ≤ Subgroup.center E → Odd (Nat.card π.ker) → π.ker = ⊥)
    (hRank : ∀ B : Subgroup S, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B ≤ 2 ^ r)
    (hMoved : ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
      ∀ σ : S →* MulAut W, Function.Injective σ → ∀ t : S, t ≠ 1 → t * t = 1 →
        2 ^ ρ ≤ (fixV (Subgroup.zpowers (σ t))).index) :
    Nat.card E * Nat.card (fixV E) < Nat.card W := by
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    by_contra hev
    rw [Nat.not_odd_iff_even] at hev
    have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := even_iff_two_dvd.1 hev
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hcommZ : ∀ l ∈ L, l * ((x : ↥L) : MulAut W) = ((x : ↥L) : MulAut W) * l := by
      intro l hl
      have := Subgroup.mem_center_iff.1 x.2 ⟨l, hl⟩
      exact congrArg Subtype.val this
    have hxW : orderOf ((x : ↥L) : MulAut W) = 2 := by
      rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx]
    have hodd2 := odd_orderOf_of_commutes hW hirr hcommZ
    rw [hxW] at hodd2
    exact absurd hodd2 (by decide)
  have hker : (redHom L e).ker = Subgroup.center ↥L := by
    ext x
    exact redHom_eq_one_iff L e x
  have hker1 : (redHom L e).ker = ⊥ :=
    hCover ↥L (redHom L e) (redHom_surjective L e) (by rw [hker]) (by rw [hker]; exact hZodd)
  have hinj : Function.Injective (redHom L e) := (MonoidHom.ker_eq_bot_iff _).1 hker1
  let eqv : ↥L ≃* S := MulEquiv.ofBijective (redHom L e) ⟨hinj, redHom_surjective L e⟩
  let σ : S →* MulAut W := L.subtype.comp eqv.symm.toMonoidHom
  have hσinj : Function.Injective σ := by
    intro x y hxy
    exact eqv.symm.injective (Subtype.ext hxy)
  have hσ : ∀ l : ↥L, σ (redHom L e l) = (l : MulAut W) := by
    intro l
    show ((eqv.symm (redHom L e l) : ↥L) : MulAut W) = l
    have : eqv.symm (redHom L e l) = l := eqv.symm_apply_apply l
    rw [this]
  have hEL : E ≤ L :=
    le_of_autInner_invol hW hperf hirr hE hEel e (autInner_of_outer_odd hOut)
  have hcard : Nat.card E ≤ 2 ^ r := card_le_two_pow_of_le hW hirr hEL hEel e hRank
  obtain ⟨b, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hEne
  have hbE : (b : MulAut W) ∈ E := b.2
  have hbL : (b : MulAut W) ∈ L := hEL hbE
  have hb2 : (b : MulAut W) * b = 1 := by
    have := hEel.2 b hbE
    rwa [sq] at this
  let l : ↥L := ⟨b, hbL⟩
  have hl1 : l ≠ 1 := by
    intro h
    apply hb1
    have := congrArg Subtype.val h
    exact Subtype.ext this
  have hl2 : l * l = 1 := Subtype.ext hb2
  have hrank := hMoved W hW σ hσinj (redHom L e l) (fun h => hl1 (hinj (by rw [h, map_one])))
    (by rw [← map_mul, hl2, map_one])
  rw [hσ] at hrank
  have hle : fixV E ≤ fixV (Subgroup.zpowers (l : MulAut W)) := by
    apply fixV_anti
    rw [Subgroup.zpowers_le]
    exact hbE
  have h18 : 2 ^ ρ ≤ (fixV E).index := hrank.trans (Subgroup.index_antitone hle)
  have hlt : Nat.card E < (fixV E).index := by
    have : (2 : ℕ) ^ r < 2 ^ ρ := Nat.pow_lt_pow_right (by norm_num) hrρ
    omega
  exact weight_lt_of_lt_index E hlt

end Generic

@[expose] def J4OuterOddProp : Prop :=
  Odd (Nat.card (Outer (NativeSporadic.Carrier .J4)))

@[expose] def J4TwoRankProp : Prop :=
  ∀ B : Subgroup (NativeSporadic.Carrier .J4), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 17

@[expose] def J4MovedRankProp : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w * w = 1) →
    ∀ σ : NativeSporadic.Carrier .J4 →* MulAut W, Function.Injective σ →
      ∀ t : NativeSporadic.Carrier .J4, t ≠ 1 → t * t = 1 →
        2 ^ 18 ≤ (fixV (Subgroup.zpowers (σ t))).index

theorem j4_cover
    (E : Type) [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* NativeSporadic.Carrier .J4) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ :=
  CFSG.SectionRank.J4_perfect_odd_cover_trivial CFSG.SectionRank.j4OrderHyp π hπ hC hodd

theorem j4ExclusionProp_of
    (ha : J4OuterOddProp) (hb : J4TwoRankProp) (hc : J4MovedRankProp) :
    J4ExclusionProp := by
  intro W _ _ hW L E hperf hirr hE hEne hEel hoff ⟨e⟩
  have h := weight_lt_of_outer_odd_cover hW hperf hirr hE hEne hEel e (r := 17) (ρ := 18)
    (by norm_num) ha (fun E _ _ _ π hπ hC hodd => j4_cover E π hπ hC hodd) hb hc
  omega

theorem sporadicExclusion_J4_of
    (ha : J4OuterOddProp) (hb : J4TwoRankProp)
    (hc : J4MovedRankProp) : SporadicExclusion .J4 :=
  sporadicExclusion_of_J4 (j4ExclusionProp_of ha hb hc)

end CFSG.QuasithinUnique.Setup.X1
