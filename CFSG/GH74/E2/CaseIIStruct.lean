module

public import CFSG.GH74.E2.CaseIStruct
import CFSG.GH74.E2.QuasiRank

public section

namespace CFSG.GH74.E2

open Subgroup

section Helpers2

variable {C : Type} [Group C] [Finite C]

omit [Finite C] in
theorem exists_elemAb_range_conj {Q K : Subgroup C} (hL : LocalK C Q K) {p : ℕ} (hp : Odd p)
    {B : Subgroup C} (hB : ElemAb p B) :
    ∃ R : Subgroup (MulAut ↥K), ElemAb p R ∧
      Nat.card R = Nat.card ↥(B ⊓ centralizer (Q : Set C)) ∧
      ∀ r ∈ R, ∃ b ∈ B ⊓ centralizer (Q : Set C), ∀ k : ↥K, ((r k : ↥K) : C) = b * k * b⁻¹ := by
  set BQ : Subgroup C := B ⊓ centralizer (Q : Set C) with hBQdef
  have hnormK : BQ ≤ normalizer (K : Set C) := by
    have := hL.K_normal
    exact Subgroup.le_normalizer_of_normal
  let φ : BQ →* MulAut ↥K := conjAction BQ K hnormK
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hcK : ∀ k ∈ K, (b : C) * k = k * b := by
      intro k hk
      have h2 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : K) : C)) hb
      have h3 : ((φ b ⟨k, hk⟩ : K) : C) = (b : C) * k * (b : C)⁻¹ := rfl
      simp only [h3] at h2
      change (b : C) * k * (b : C)⁻¹ = k at h2
      calc (b : C) * k = ((b : C) * k * (b : C)⁻¹) * b := by group
        _ = k * b := by rw [h2]
    have hcQ : ∀ q ∈ Q, (b : C) * q = q * b := fun q hq =>
      (mem_centralizer_iff.1 b.2.2 q hq).symm
    have hbQ : (b : C) ∈ Q := hL.self_centralizing b hcQ hcK
    apply Subtype.ext
    exact eq_one_of_pgroup_of_pow hL.Q_pgroup hbQ hp (hB.2 b b.2.1)
  have hRel : ElemAb p φ.range := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hB.1 a a.2.1 b b.2.1)
    · rintro _ ⟨a, rfl⟩
      rw [← map_pow]
      have : a ^ p = 1 := Subtype.ext (hB.2 a a.2.1)
      rw [this, map_one]
  refine ⟨φ.range, hRel, (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm, ?_⟩
  rintro _ ⟨b, rfl⟩
  exact ⟨b, b.2, fun k => rfl⟩

theorem rank_add_le_of_centralizing {K P : Subgroup C} (hgen : Gen4 C) (hP : IsPGroup 2 P)
    (hPK : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) {U : Subgroup ↥K} (hU : IsPGroup 2 U) :
    Group.rank P + Group.rank U ≤ 4 + Group.rank ↥(P ⊓ U.map K.subtype) ∧
      Nat.card ↥(P ⊓ U.map K.subtype) ≤ Nat.card (center ↥K) := by
  let T' : Subgroup C := U.map K.subtype
  have hT'2 : IsPGroup 2 T' := hU.map K.subtype
  have hrankT' : Group.rank T' = Group.rank U :=
    (Group.rank_congr (U.equivMapOfInjective K.subtype K.subtype_injective)).symm
  have hcomm : ∀ q ∈ P, ∀ t ∈ T', q * t = t * q := by
    rintro q hq _ ⟨t, -, rfl⟩
    exact hPK q hq t t.2
  refine ⟨?_, ?_⟩
  · have := gen4_rank_add_le hgen P T' hP hT'2 hcomm
    rw [hrankT'] at this
    exact this
  · let f : ↥(P ⊓ T') → center ↥K := fun x =>
      ⟨⟨x.1, by
        obtain ⟨y, -, hy⟩ := x.2.2
        rw [← hy]; exact y.2⟩, by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        exact (hPK x.1 x.2.1 k k.2).symm⟩
    refine Nat.card_le_card_of_injective f ?_
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z => ((z : ↥K) : C)) (Subtype.ext_iff.1 hxy)

theorem false_of_center_bot {K P : Subgroup C} (hgen : Gen4 C) (hP : IsPGroup 2 P)
    (hPK : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) (hP2 : 2 ≤ Group.rank P) (hcen : center ↥K = ⊥)
    {U : Subgroup ↥K} (hU : IsPGroup 2 U) (hU3 : 3 ≤ Group.rank U) : False := by
  obtain ⟨h1, h2⟩ := rank_add_le_of_centralizing hgen hP hPK hU
  have h3 : Nat.card ↥(P ⊓ U.map K.subtype) ≤ 1 := by
    calc Nat.card ↥(P ⊓ U.map K.subtype) ≤ Nat.card (center ↥K) := h2
      _ = 1 := by rw [hcen, Subgroup.card_bot]
  have hsub : Subsingleton ↥(P ⊓ U.map K.subtype) := by
    have := Nat.card_pos (α := ↥(P ⊓ U.map K.subtype))
    exact (Nat.card_eq_one_iff_unique.1 (by omega)).1
  rw [Group.rank_eq_zero_iff.2 hsub] at h1
  omega

theorem false_of_center_card {K P : Subgroup C} (hgen : Gen4 C) (hP : IsPGroup 2 P)
    (hPK : ∀ p ∈ P, ∀ k ∈ K, p * k = k * p) (hP2 : 2 ≤ Group.rank P)
    (hcen : Nat.card (center ↥K) ≤ 2) {U : Subgroup ↥K} (hU : IsPGroup 2 U)
    (hU4 : 4 ≤ Group.rank U) : False := by
  obtain ⟨h1, h2⟩ := rank_add_le_of_centralizing hgen hP hPK hU
  have h3 := rank_le_one_of_card_le_two (h2.trans hcen)
  omega

omit [Finite C] in
theorem isPGroup_zpowers_of_sq {x : C} (hx : x ^ 2 = 1) : IsPGroup 2 ↥(zpowers x) := by
  have h1 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

theorem two_le_rank_of_two_involutions {W : Subgroup C} {t t' : C} (ht : t ∈ W) (ht' : t' ∈ W)
    (hne : t ≠ t') (ht1 : t ≠ 1) (ht'1 : t' ≠ 1) (ht2 : t ^ 2 = 1) (ht'2 : t' ^ 2 = 1) :
    2 ≤ Group.rank W := by
  by_contra hrk
  have hcyc : IsCyclic W := isCyclic_of_rank_le_one (by omega)
  classical
  have : Fintype W := Fintype.ofFinite W
  have hcard := IsCyclic.card_pow_eq_one_le (α := W) (n := 2) (by norm_num)
  have hsub : ({1, ⟨t, ht⟩, ⟨t', ht'⟩} : Finset W) ⊆
      Finset.univ.filter (fun a : W => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases ha with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext ht2
    · exact Subtype.ext ht'2
  have h1t : (1 : W) ≠ ⟨t, ht⟩ := fun h => ht1 (congrArg Subtype.val h).symm
  have h1t' : (1 : W) ≠ ⟨t', ht'⟩ := fun h => ht'1 (congrArg Subtype.val h).symm
  have htt' : (⟨t, ht⟩ : W) ≠ ⟨t', ht'⟩ := fun h => hne (congrArg Subtype.val h)
  have h3 : ({1, ⟨t, ht⟩, ⟨t', ht'⟩} : Finset W).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair htt']
    simp [h1t, h1t']
  have := Finset.card_le_card hsub
  omega

end Helpers2

theorem caseII_structure {C : Type} [Group C] [Finite C] (hgen : Gen4 C) {Q K : Subgroup C}
    (hL : LocalK C Q K) (hK : K0Shape ↥K) (hD : K0Data) (hD3 : K0Data3) {B : Subgroup C}
    (hB : ElemAb 3 B) (hBcard : Nat.card B = 9) {t t' : C} (htQ : t ∈ Q) (ht1 : t ≠ 1)
    (ht2 : t ^ 2 = 1) (ht'1 : t' ≠ 1) (htt' : t' ≠ t) (ht'2 : t' ^ 2 = 1) (hcomm : t * t' = t' * t)
    (hBt : ∀ b ∈ B, b * t = t * b) (hBt' : ∀ b ∈ B, b * t' = t' * b) :
    (B ≤ centralizer (Q : Set C) ∧ (ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) ∧ B ≤ K ∧
      ∀ k ∈ K, t' * k = k * t') ∨
    (Nat.card ↥(B ⊓ centralizer (Q : Set C)) = 3 ∧ Group.rank Q = 2 ∧
      (∀ P : Subgroup C, P ≤ Q → Group.rank P ≤ 2) ∧
      (ShapeA5 ↥K ∨ ShapeL27 ↥K ∨ ShapeA6 ↥K ∨ ShapeL217 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K) ∧
      ∃ c : C, (∀ k ∈ K, c * k = k * c) ∧ orderOf c = 3 ∧
        ∃ φ : MulAut ↥Q, (∀ x : ↥Q, ((φ x : ↥Q) : C) = c * x * c⁻¹) ∧ orderOf φ = 3 ∧
          (∀ x : ↥Q, φ x * x⁻¹ ∈ frattini ↥Q → x ∈ frattini ↥Q) ∧
          ∃ x : ↥Q, x ≠ 1 ∧ φ x = x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn := hL.Q_normal
  have hKn := hL.K_normal
  have hrankP : ∀ P : Subgroup C, P ≤ Q → Group.rank P ≤ 2 := fun P hP =>
    rank_le_two_of_le_Q hgen hL (hD.center_card _ hK) (fun hc => hD.sylow_rank_simple _ hK hc)
      (fun hc => hD.sylow_rank_cover _ hK hc) hP
  have hrankQ : Group.rank Q ≤ 2 := hrankP Q le_rfl
  have hQK : ∀ p ∈ Q, ∀ k ∈ K, p * k = k * p := hL.commute
  have hZ2 : Nat.card (center ↥K) ≤ 2 := hD.center_card _ hK
  obtain ⟨r, hcard, hF1⟩ := exists_centralizer_index_pow hL.Q_pgroup
    (fun b _ x hx => hL.Q_normal.conj_mem x hx b) (p := 3) Nat.prime_three (by norm_num) hB
  rw [orderOf_two_zmod_three] at hF1
  have hr1 : r ≤ 1 := by omega
  obtain ⟨R, hRel, hRcard, hRconj⟩ := exists_elemAb_range_conj hL (p := 3) (by decide) hB
  set BQ : Subgroup C := B ⊓ centralizer (Q : Set C) with hBQdef
  rw [hBcard] at hcard
  have hcases : Nat.card BQ = 9 ∨ (Nat.card BQ = 3 ∧ r = 1) := by
    interval_cases r
    · left
      norm_num at hcard
      omega
    · right
      norm_num at hcard
      exact ⟨by omega, rfl⟩
  have hnormK : ∀ x : C, x ∈ normalizer (K : Set C) := fun x =>
    (Subgroup.le_normalizer_of_normal : (⊤ : Subgroup C) ≤ normalizer (K : Set C))
      (Subgroup.mem_top x)
  rcases hcases with hn9 | ⟨hn3, hr⟩
  ·
    left
    have hBQeq : BQ = B := Subgroup.eq_of_le_of_card_ge (inf_le_left : BQ ≤ B)
      (by rw [hn9, hBcard])
    have hBc : B ≤ centralizer (Q : Set C) := fun b hb => by
      have : b ∈ BQ := hBQeq ▸ hb
      exact this.2
    have hle1 : ¬ (ShapeA5 ↥K ∨ ShapeL27 ↥K ∨ ShapeL217 ↥K ∨ ShapeSz8 ↥K ∨ Shape2Sz8 ↥K) :=
      fun h => by
        have := hD3.autRank3_le_one ↥K h R hRel
        omega
    have hshape6 : ShapeA6 ↥K ∨ ShapeL28 ↥K ∨ ShapeL33 ↥K ∨ ShapeU33 ↥K ∨ ShapeM11 ↥K ∨
        Shape2M12 ↥K := by
      rcases hK with h | h | h | h | h | h | h | h | h | h | h
      · exact absurd (Or.inl h) hle1
      · exact absurd (Or.inr (Or.inl h)) hle1
      · exact Or.inl h
      · exact absurd (Or.inr (Or.inr (Or.inl h))) hle1
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact absurd (Or.inr (Or.inr (Or.inr (Or.inl h)))) hle1
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exact absurd (Or.inr (Or.inr (Or.inr (Or.inr h)))) hle1
    let ψ : MulAut ↥K := K.normalizerMonoidHom ⟨t', hnormK t'⟩
    have hψ2 : ψ ^ 2 = 1 := by
      have h1 : (⟨t', hnormK t'⟩ : normalizer (K : Set C)) ^ 2 = 1 :=
        Subtype.ext (by simpa using ht'2)
      calc ψ ^ 2 = K.normalizerMonoidHom ((⟨t', hnormK t'⟩ : normalizer (K : Set C)) ^ 2) :=
            (map_pow _ _ _).symm
        _ = 1 := by rw [h1, map_one]
    have hψcomm : ∀ r ∈ R, ψ * r = r * ψ := by
      intro r hr
      obtain ⟨b, hb, hrb⟩ := hRconj r hr
      apply MulEquiv.ext
      intro k
      apply Subtype.ext
      have h1 : ((ψ * r) k : ↥K) = ψ (r k) := rfl
      have h2 : ((r * ψ) k : ↥K) = r (ψ k) := rfl
      rw [h1, h2]
      have h3 : ((ψ (r k) : ↥K) : C) = t' * (b * k * b⁻¹) * t'⁻¹ := by
        have : ((ψ (r k) : ↥K) : C) = t' * ((r k : ↥K) : C) * t'⁻¹ := rfl
        rw [this, hrb k]
      have h4 : ((r (ψ k) : ↥K) : C) = b * (t' * k * t'⁻¹) * b⁻¹ := by
        rw [hrb (ψ k)]
        rfl
      rw [h3, h4]
      have hbt' : b * t' = t' * b := hBt' b hb.1
      calc t' * (b * (k : C) * b⁻¹) * t'⁻¹ = (t' * b) * k * (t' * b)⁻¹ := by group
        _ = (b * t') * k * (b * t')⁻¹ := by rw [hbt']
        _ = b * (t' * k * t'⁻¹) * b⁻¹ := by group
    have hψ1 : ψ = 1 :=
      hD3.autCentralizer ↥K hshape6 R hRel (hRcard.trans hn9) ψ hψ2 hψcomm
    have ht'K : ∀ k ∈ K, t' * k = k * t' := by
      intro k hk
      have h1 := congrArg (fun f : MulAut ↥K => ((f ⟨k, hk⟩ : ↥K) : C)) hψ1
      have h2 : t' * k * t'⁻¹ = k := h1
      calc t' * k = (t' * k * t'⁻¹) * t' := by group
        _ = k * t' := by rw [h2]
    have hz : IsPGroup 2 ↥(zpowers t) := isPGroup_zpowers_of_sq ht2
    have hz' : IsPGroup 2 ↥(zpowers t') := isPGroup_zpowers_of_sq ht'2
    have hcz : ∀ q ∈ zpowers t, ∀ s ∈ zpowers t', q * s = s * q := by
      intro q hq s hs
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hq
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hs
      exact (Commute.zpow_zpow (show Commute t t' from hcomm) m n).eq
    have hW2 : IsPGroup 2 ↥(zpowers t ⊔ zpowers t') := isPGroup_sup_of_commute _ _ hz hz' hcz
    have htW : t ∈ zpowers t ⊔ zpowers t' := mem_sup_left (mem_zpowers t)
    have ht'W : t' ∈ zpowers t ⊔ zpowers t' := mem_sup_right (mem_zpowers t')
    have hWrank : 2 ≤ Group.rank ↥(zpowers t ⊔ zpowers t') :=
      two_le_rank_of_two_involutions htW ht'W htt'.symm ht1 ht'1 ht2 ht'2
    have hWK : ∀ w ∈ zpowers t ⊔ zpowers t', ∀ k ∈ K, w * k = k * w := by
      intro w hw k hk
      have hle : zpowers t ⊔ zpowers t' ≤ centralizer ({k} : Set C) := by
        refine sup_le (zpowers_le.2 ?_) (zpowers_le.2 ?_)
        · rw [mem_centralizer_singleton_iff]
          exact hQK t htQ k hk
        · rw [mem_centralizer_singleton_iff]
          exact ht'K k hk
      exact mem_centralizer_singleton_iff.1 (hle hw)
    have hshape3 : ShapeA6 ↥K ∨ ShapeL33 ↥K ∨ ShapeM11 ↥K := by
      rcases hshape6 with h | h | h | h | h | h
      · exact Or.inl h
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge3 ↥K (Or.inl h)
        exact false_of_center_bot hgen hW2 hWK hWrank (hD3.center_bot ↥K (by tauto)) hU hUr
      · exact Or.inr (Or.inl h)
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge3 ↥K (Or.inr (Or.inl h))
        exact false_of_center_bot hgen hW2 hWK hWrank (hD3.center_bot ↥K (by tauto)) hU hUr
      · exact Or.inr (Or.inr h)
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge4 ↥K h
        exact false_of_center_card hgen hW2 hWK hWrank hZ2 hU hUr
    have hinner : ∀ φ : MulAut ↥K, φ ^ 3 = 1 → ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹ :=
      fun φ hφ => hD3.inner3 ↥K hshape3 φ hφ
    have hBK : B ≤ K := fun b hb =>
      mem_K_of_pow_three hL hinner (hB.2 b hb)
        (fun q hq => (mem_centralizer_iff.1 (hBc hb) q hq).symm)
    exact ⟨hBc, hshape3, hBK, ht'K⟩
  ·
    right
    have hrankQ2 : Group.rank Q = 2 := by omega
    have hshape6 : ShapeA5 ↥K ∨ ShapeL27 ↥K ∨ ShapeA6 ↥K ∨ ShapeL217 ↥K ∨ ShapeL33 ↥K ∨
        ShapeM11 ↥K := by
      rcases hK with h | h | h | h | h | h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge3 ↥K (Or.inl h)
        exact false_of_center_bot hgen hL.Q_pgroup hQK (by omega)
          (hD3.center_bot ↥K (by tauto)) hU hUr
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge3 ↥K (Or.inr (Or.inl h))
        exact false_of_center_bot hgen hL.Q_pgroup hQK (by omega)
          (hD3.center_bot ↥K (by tauto)) hU hUr
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge3_sz ↥K (Or.inl h)
        exact false_of_center_bot hgen hL.Q_pgroup hQK (by omega)
          (hD3.center_bot ↥K (by tauto)) hU hUr
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge4 ↥K h
        exact false_of_center_card hgen hL.Q_pgroup hQK (by omega) hZ2 hU hUr
      · exfalso
        obtain ⟨U, hU, hUr⟩ := hD3.rank_ge4_sz ↥K h
        exact false_of_center_card hgen hL.Q_pgroup hQK (by omega) hZ2 hU hUr
    have hinner : ∀ φ : MulAut ↥K, φ ^ 3 = 1 → ∃ k : ↥K, ∀ x : ↥K, φ x = k * x * k⁻¹ := by
      rcases hshape6 with h | h | h | h | h | h
      · exact fun φ hφ => hD3.inner3_small ↥K (Or.inl h) φ hφ
      · exact fun φ hφ => hD3.inner3_small ↥K (Or.inr (Or.inl h)) φ hφ
      · exact fun φ hφ => hD3.inner3 ↥K (Or.inl h) φ hφ
      · exact fun φ hφ => hD3.inner3_small ↥K (Or.inr (Or.inr h)) φ hφ
      · exact fun φ hφ => hD3.inner3 ↥K (Or.inr (Or.inl h)) φ hφ
      · exact fun φ hφ => hD3.inner3 ↥K (Or.inr (Or.inr h)) φ hφ
    have hcen : center ↥K = ⊥ := by
      refine hD3.center_bot ↥K ?_
      rcases hshape6 with h | h | h | h | h | h <;> tauto
    obtain ⟨c₀, hc₀B, hc₀BQ⟩ : ∃ c₀ ∈ B, c₀ ∉ BQ := by
      by_contra hcon
      push Not at hcon
      have hle : B ≤ BQ := hcon
      have := Subgroup.card_le_of_le hle
      omega
    obtain ⟨k, hkK, hk⟩ := exists_inner_conj hinner (hB.2 c₀ hc₀B)
    have hcK : ∀ x ∈ K, (k⁻¹ * c₀) * x = x * (k⁻¹ * c₀) := by
      intro x hx
      have h1 := hk x hx
      calc k⁻¹ * c₀ * x = k⁻¹ * (c₀ * x * c₀⁻¹) * c₀ := by group
        _ = k⁻¹ * (k * x * k⁻¹) * c₀ := by rw [h1]
        _ = x * (k⁻¹ * c₀) := by group
    have hcQ : ∀ q ∈ Q, (k⁻¹ * c₀) * q * (k⁻¹ * c₀)⁻¹ = c₀ * q * c₀⁻¹ := by
      intro q hq
      have hq' : c₀ * q * c₀⁻¹ ∈ Q := hL.Q_normal.conj_mem q hq c₀
      have h1 := hQK _ hq' k hkK
      calc (k⁻¹ * c₀) * q * (k⁻¹ * c₀)⁻¹ = k⁻¹ * (c₀ * q * c₀⁻¹) * k := by group
        _ = k⁻¹ * (k * (c₀ * q * c₀⁻¹)) := by rw [← h1]; group
        _ = c₀ * q * c₀⁻¹ := by group
    have hcQ' : ¬ ∀ q ∈ Q, (k⁻¹ * c₀) * q = q * (k⁻¹ * c₀) := by
      intro h
      apply hc₀BQ
      refine ⟨hc₀B, mem_centralizer_iff.2 (fun q hq => ?_)⟩
      have h1 := hcQ q hq
      have h2 : (k⁻¹ * c₀) * q * (k⁻¹ * c₀)⁻¹ = q := by
        rw [h q hq]
        group
      rw [h2] at h1
      calc q * c₀ = (c₀ * q * c₀⁻¹) * c₀ := by rw [← h1]
        _ = c₀ * q := by group
    have hcne : k⁻¹ * c₀ ≠ 1 := fun h => hcQ' (fun q hq => by rw [h]; simp)
    have hkc : Commute k (k⁻¹ * c₀) := (hcK k hkK).symm
    have hc3' : (k⁻¹ * c₀) ^ 3 = 1 := by
      have h1 : (k * (k⁻¹ * c₀)) ^ 3 = k ^ 3 * (k⁻¹ * c₀) ^ 3 := hkc.mul_pow 3
      have h2 : k * (k⁻¹ * c₀) = c₀ := by group
      rw [h2, hB.2 c₀ hc₀B] at h1
      have h3 : (k⁻¹ * c₀) ^ 3 = (k ^ 3)⁻¹ := eq_inv_of_mul_eq_one_right h1.symm
      have hmemK : (k⁻¹ * c₀) ^ 3 ∈ K := by
        rw [h3]
        exact K.inv_mem (K.pow_mem hkK 3)
      have hz : (⟨(k⁻¹ * c₀) ^ 3, hmemK⟩ : ↥K) ∈ center ↥K := by
        rw [Subgroup.mem_center_iff]
        intro x
        apply Subtype.ext
        have h4 : Commute (k⁻¹ * c₀) (x : C) := hcK x x.2
        exact (h4.pow_left 3).eq.symm
      rw [hcen] at hz
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hz)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hc3 : orderOf (k⁻¹ * c₀) = 3 := orderOf_eq_prime hc3' hcne
    have htc : (k⁻¹ * c₀) * t = t * (k⁻¹ * c₀) := by
      have h1 := hcQ t htQ
      have h2 : c₀ * t * c₀⁻¹ = t := by
        rw [hBt c₀ hc₀B]
        group
      rw [h2] at h1
      exact mul_inv_eq_iff_eq_mul.1 h1
    obtain ⟨φ, hφapp, hφord, hφirr, x, hx1, hφx⟩ :=
      exists_irreducible_aut hL.Q_pgroup hQn hrankQ2 hc3 hcQ' htQ ht1 htc
    exact ⟨hn3, hrankQ2, hrankP, hshape6, k⁻¹ * c₀, hcK, hc3, φ, hφapp, hφord, hφirr, x, hx1, hφx⟩

end CFSG.GH74.E2
