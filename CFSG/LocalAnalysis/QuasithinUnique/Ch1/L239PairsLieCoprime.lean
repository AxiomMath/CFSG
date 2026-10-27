module

public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.Lie

open scoped commutatorElement IsMulCommutative

section Coprime

variable {G : Type*} [Group G]

theorem commutator_self_le (A : Subgroup G) : ⁅A, A⁆ ≤ A :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    simpa [commutatorElement_def, mul_assoc] using
      A.mul_mem (A.mul_mem (A.mul_mem ha hb) (A.inv_mem ha)) (A.inv_mem hb)

theorem normalizer_le_normalizer_centralizer (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (R : Set G) : Set G) :=
  CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup R

theorem le_normalizer_commutator_of_le_normalizer (H P Q : Subgroup G)
    (hHP : H ≤ Subgroup.normalizer (P : Set G)) (hHQ : H ≤ Subgroup.normalizer (Q : Set G)) :
    H ≤ Subgroup.normalizer ((⁅P, Q⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator]
  rw [(Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHP hh)),
    (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHQ hh))]

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ Subgroup.normalizer (H : Set G))
    (hK : g ∈ Subgroup.normalizer (K : Set G)) : g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hH hK ⊢
  rw [Subgroup.map_sup, hH, hK]

theorem fitting_commutator_inf_centralizer [Finite G] {B K : Subgroup G}
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hBK : B ≤ Subgroup.normalizer (K : Set G))
    (hcop : Nat.Coprime (Nat.card B) (Nat.card K)) :
    ⁅B, K⁆ ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
  classical
  let _ : Fintype B := Fintype.ofFinite B
  have _ : IsMulCommutative K := ⟨⟨fun x y => Subtype.ext (hK x x.2 y y.2)⟩⟩
  have hconj : ∀ b ∈ B, ∀ k ∈ K, b * k * b⁻¹ ∈ K := fun b hb k hk =>
    (Subgroup.mem_normalizer_iff.mp (hBK hb) k).mp hk
  let f : B → K → K := fun b k => ⟨(b : G) * k * (b : G)⁻¹, hconj b b.2 k k.2⟩
  have hfmul : ∀ b k₁ k₂, f b (k₁ * k₂) = f b k₁ * f b k₂ := fun b k₁ k₂ =>
    Subtype.ext (by simp only [f, Subgroup.coe_mul]; group)
  let σ : K →* K := MonoidHom.mk' (fun k => ∏ b : B, f b k) fun k₁ k₂ => by
    show ∏ b, f b (k₁ * k₂) = (∏ b, f b k₁) * ∏ b, f b k₂
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => hfmul b k₁ k₂
  have hσ : ∀ k, σ k = ∏ b : B, f b k := fun k => rfl
  have hker : ⁅B, K⁆ ≤ σ.ker.map K.subtype := by
    rw [Subgroup.commutator_le]
    intro b hb k hk
    refine ⟨⟨b * k * b⁻¹, hconj b hb k hk⟩ * ⟨k, hk⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, hσ, hσ]
      exact Fintype.prod_equiv (Equiv.mulRight (⟨b, hb⟩ : B)) _ _ fun c =>
        Subtype.ext (by simp only [f, Equiv.coe_mulRight, Subgroup.coe_mul, mul_inv_rev]; group)
    · simp [commutatorElement_def]
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxc, hxB⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k, hk, rfl⟩ := hker hxc
  have hfix : ∀ b : B, f b k = k := fun b => Subtype.ext (by
    have hb : (b : G) * k = k * b := Subgroup.mem_centralizer_iff.mp hxB b b.2
    show (b : G) * k * (b : G)⁻¹ = k
    rw [hb, mul_inv_cancel_right])
  have h1 : k ^ Fintype.card B = 1 := by
    rw [← MonoidHom.mem_ker.mp hk, hσ]
    simp only [hfix, Finset.prod_const, Finset.card_univ]
  have h2 : k ^ Nat.card K = 1 := pow_card_eq_one'
  have h3 := (pow_gcd_eq_one (a := k)).mpr ⟨h1, h2⟩
  rw [← Nat.card_eq_fintype_card, Nat.Coprime.gcd_eq_one hcop, pow_one] at h3
  rw [h3, Subgroup.mem_bot]
  rfl

theorem le_of_le_sup_commutator_of_isPGroup {p : ℕ} [Fact p.Prime] {Y N Z : Subgroup G} [Finite Y]
    (hY : IsPGroup p Y) (hNY : N ≤ Y) (hZY : Z ≤ Y)
    (hZn : Y ≤ Subgroup.normalizer (Z : Set G))
    (h : N ≤ Z ⊔ ⁅N, Y⁆) : N ≤ Z := by
  have hZnormal : (Z.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hZY).2 hZn
  set Z' : Subgroup ↥Y := Z.subgroupOf Y with hZ'
  set N' : Subgroup ↥Y := N.subgroupOf Y with hN'
  have hnil : Group.IsNilpotent ↥Y := hY.isNilpotent
  have hnilq : Group.IsNilpotent (↥Y ⧸ Z') := Group.nilpotent_quotient_of_nilpotent Z'
  have hmap : (Z' ⊔ ⁅N', ⊤⁆).map Y.subtype = Z ⊔ ⁅N, Y⁆ := by
    rw [Subgroup.map_sup, Subgroup.map_commutator, hZ', hN',
      Subgroup.map_subgroupOf_eq_of_le hZY, Subgroup.map_subgroupOf_eq_of_le hNY,
      Subgroup.map_top, Subgroup.range_subtype]
  have h' : N' ≤ Z' ⊔ ⁅N', ⊤⁆ := by
    intro x hx
    have hx1 : (x : G) ∈ Z ⊔ ⁅N, Y⁆ := h hx
    rw [← hmap] at hx1
    obtain ⟨y, hy, hyx⟩ := hx1
    have : y = x := Subtype.ext hyx
    rwa [this] at hy
  let φ : ↥Y →* ↥Y ⧸ Z' := QuotientGroup.mk' Z'
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Z'
  have hZφ : Z'.map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact le_of_eq (QuotientGroup.ker_mk' Z').symm
  have hq : N'.map φ ≤ ⁅N'.map φ, ⊤⁆ := by
    have h1 := Subgroup.map_mono (f := φ) h'
    rw [Subgroup.map_sup, Subgroup.map_commutator, hZφ, Subgroup.map_top_of_surjective φ hφs,
      bot_sup_eq] at h1
    exact h1
  have hk : ∀ k, N'.map φ ≤ (⊤ : Subgroup (↥Y ⧸ Z')).lowerCentralSeries k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [Subgroup.lowerCentralSeries_succ]
      exact hq.trans (Subgroup.commutator_mono ih le_rfl)
  have hbot : N'.map φ = ⊥ := by
    refine le_bot_iff.1 ?_
    have := hk (Group.nilpotencyClass (↥Y ⧸ Z'))
    rwa [Subgroup.lowerCentralSeries_nilpotencyClass] at this
  have hker : N' ≤ Z' := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hbot
  intro n hn
  have := hker (show (⟨n, hNY hn⟩ : ↥Y) ∈ N' from hn)
  exact this

theorem eq_of_sup_commutator_eq {p : ℕ} [Fact p.Prime] {Q H : Subgroup G} [Finite Q]
    (hQ : IsPGroup p Q) (hHQ : H ≤ Q) (h : H ⊔ ⁅Q, Q⁆ = Q) : H = Q := by
  have : Fact (IsPGroup p Q) := ⟨hQ⟩
  have hcomm : (_root_.commutator ↥Q).map Q.subtype = ⁅Q, Q⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  have hsup : H.subgroupOf Q ⊔ _root_.commutator ↥Q = ⊤ := by
    apply Subgroup.map_injective Q.subtype_injective
    rw [Subgroup.map_sup, hcomm, Subgroup.map_subgroupOf_eq_of_le hHQ, h, Subgroup.map_top,
      Subgroup.range_subtype]
  have hle : H.subgroupOf Q ⊔ _root_.commutator ↥Q ≤ H.subgroupOf Q ⊔ frattini ↥Q :=
    sup_le_sup_left (CFSG.commutator_le_frattini_of_isPGroup (p := p)) _
  have hsup' : H.subgroupOf Q ⊔ frattini ↥Q = ⊤ := top_le_iff.1 (hsup ▸ hle)
  have htop : H.subgroupOf Q = ⊤ := CFSG.lemma_1_7_a (p := p) _ hsup'
  refine le_antisymm hHQ fun x hx => ?_
  have : (⟨x, hx⟩ : ↥Q) ∈ H.subgroupOf Q := htop ▸ Subgroup.mem_top _
  exact this

theorem coprime_three_card [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q) :
    Nat.Coprime 3 (Nat.card Q) := by
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hQ
  rw [hn]
  exact Nat.Coprime.pow_right n (by norm_num)

theorem isPGroup_three_zpowers {t : G} (ht : orderOf t = 3) :
    IsPGroup 3 (Subgroup.zpowers t) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])

theorem zpowers_le_centralizer_of_commutator_le [Finite G] {Q : Subgroup G} (hQ : IsPGroup 2 Q)
    {t : G} (ht : orderOf t = 3) (htQ : t ∈ Subgroup.normalizer (Q : Set G))
    (h : ⁅Q, Subgroup.zpowers t⁆ ≤ ⁅Q, Q⁆) :
    Subgroup.zpowers t ≤ Subgroup.centralizer (Q : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Subgroup.zpowers t ≤ Subgroup.normalizer (Q : Set G) := by
    rw [Subgroup.zpowers_le]; exact htQ
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization 3
    Nat.prime_three (Subgroup.zpowers t) Q (isPGroup_three_zpowers ht) hA (coprime_three_card hQ)
  have hsup : (Q ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ⊔ ⁅Q, Q⁆ = Q := by
    refine le_antisymm (sup_le inf_le_left (commutator_self_le Q)) ?_
    calc Q = ⁅Q, Subgroup.zpowers t⁆ ⊔ (Q ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) :=
            hfac.symm
        _ ≤ ⁅Q, Q⁆ ⊔ (Q ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) :=
            sup_le_sup_right h _
        _ = (Q ⊓ Subgroup.centralizer (Subgroup.zpowers t : Set G)) ⊔ ⁅Q, Q⁆ := sup_comm _ _
  have hQfin : Finite Q := Finite.of_injective _ Q.subtype_injective
  have heq := eq_of_sup_commutator_eq (p := 2) hQ inf_le_left hsup
  have hQc : Q ≤ Subgroup.centralizer (Subgroup.zpowers t : Set G) := by
    rw [← heq]; exact inf_le_right
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have := Subgroup.mem_centralizer_iff.1 (hQc hq) a ha
  exact this.symm

end Coprime

end CFSG.QuasithinUnique.Vol2Native.L239.Lie
