module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.Rank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KSubgroupL1

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

theorem L1_not_isConj (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) {x : G} (hx : x ∈ L1sub h D hgood) : ¬ IsConj z x :=
  not_isConj_of_elemAb h hR (fun a ha b hb => L1sub_comm h D hgood ha hb)
    (fun a ha => L1sub_sq h D hgood ha)
    (by rw [card_L1sub h hZ D hgood X htrans]; norm_num) hx

theorem mem_E_of_involution_not_mem_L1 (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F) {k : G} (hk : k ∈ Ksub z F) (hk2 : k * k = 1)
    (hk1 : k ∉ L1sub h D hgood) : k ∈ F ⊔ zpowers z := by
  rcases mem_L1sub_or h hZ D hgood X hk with h1 | h1
  · exact absurd h1 hk1
  · have hℓ2 : (k * z) * (k * z) = 1 := L1sub_sq h D hgood h1
    have e : z * k * z = k := by
      have : k * (z * k * z) = 1 := by
        calc k * (z * k * z) = (k * z) * (k * z) := by simp only [mul_assoc]
          _ = 1 := hℓ2
      rw [eq_inv_of_mul_eq_one_right this, inv_eq_of_mul_eq_one_right hk2]
    have hzk : z * (k * z) = k * z * z := by
      calc z * (k * z) = z * k * z := by simp only [mul_assoc]
        _ = k := e
        _ = k * z * z := by rw [mul_assoc, h.z_mul_self, mul_one]
    have hF : k * z ∈ F := L1sub_centralizer_z h D hgood h1 hzk
    have hm : (k * z) * z ∈ F ⊔ zpowers z :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hF)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    rwa [mul_assoc, h.z_mul_self, mul_one] at hm

theorem Ksub_maximal (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) {S : Subgroup G} (hS : IsPGroup 2 S) (hKS : Ksub z F ≤ S)
    (hSC : S ≤ centralizer (F : Set G)) : S = Ksub z F := by
  refine le_antisymm ?_ hKS
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent S := hS.isNilpotent
  let K' : Subgroup S := (Ksub z F).subgroupOf S
  have hlt : K' < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hne
    intro s hs
    have : (⟨s, hs⟩ : S) ∈ K' := by rw [htop]; exact Subgroup.mem_top _
    exact this
  obtain ⟨-, n, hn, hnK'⟩ :=
    IsConcreteLE.lt_iff_le_and_exists.1 (Group.normalizerCondition_of_isNilpotent K' hlt)
  have hzK : z ∈ Ksub z F := E_le_K h D (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hzS : z ∈ S := hKS hzK
  have hconj : (n : G) * z * (n : G)⁻¹ ∈ Ksub z F := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨z, hzS⟩).1 (Subgroup.mem_subgroupOf.2 hzK)
    simpa using Subgroup.mem_subgroupOf.1 h1
  have hinv : ((n : G) * z * (n : G)⁻¹) * ((n : G) * z * (n : G)⁻¹) = 1 := by
    calc _ = (n : G) * (z * z) * (n : G)⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have hE : (n : G) * z * (n : G)⁻¹ ∈ F ⊔ zpowers z := by
    by_cases hL1 : (n : G) * z * (n : G)⁻¹ ∈ L1sub h D hgood
    · exact absurd (isConj_iff.2 ⟨(n : G), rfl⟩ : IsConj z ((n : G) * z * (n : G)⁻¹))
        (L1_not_isConj h hZ D hgood X htrans hR hL1)
    · exact mem_E_of_involution_not_mem_L1 h hZ D hgood X hconj hinv hL1
  have hnC : ∀ f ∈ F, f * (n : G) = (n : G) * f := fun f hf =>
    mem_centralizer_iff.1 (hSC n.2) f hf
  have hnK : (n : G) ∈ Ksub z F := by
    refine mem_Ksub.2 ⟨?_, hnC⟩
    apply forall_mem_iff_of_forall_mem
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hna : (n : G) * a * (n : G)⁻¹ = a := by
      rw [← hnC a ha]
      group
    have h1 : (n : G) * (a * z ^ k) * (n : G)⁻¹ = a * ((n : G) * z * (n : G)⁻¹) ^ k := by
      rw [conj_zpow]
      calc (n : G) * (a * z ^ k) * (n : G)⁻¹
          = ((n : G) * a * (n : G)⁻¹) * ((n : G) * z ^ k * (n : G)⁻¹) := by group
        _ = a * ((n : G) * z ^ k * (n : G)⁻¹) := by rw [hna]
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.zpow_mem _ hE k)
  exact hnK' (Subgroup.mem_subgroupOf.2 hnK)

theorem Ksub_sylow (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) :
    IsPGroup 2 (Ksub z F) ∧ ¬ 2 ∣ (Ksub z F).relIndex (centralizer (F : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKP : IsPGroup 2 (Ksub z F) :=
    IsPGroup.of_card (n := 9) (by rw [card_Ksub h hZ D htrans]; norm_num)
  have hKC : Ksub z F ≤ centralizer (F : Set G) := fun k hk =>
    mem_centralizer_iff.2 fun f hf => (mem_Ksub.1 hk).2 f hf
  refine ⟨hKP, ?_⟩
  have hK'P : IsPGroup 2 ((Ksub z F).subgroupOf (centralizer (F : Set G))) := hKP.comap_subtype
  obtain ⟨P, hP⟩ := hK'P.exists_le_sylow
  have hPG : IsPGroup 2 ((P : Subgroup (centralizer (F : Set G))).map
      (centralizer (F : Set G)).subtype) := P.isPGroup'.map _
  have hKP' : Ksub z F ≤ (P : Subgroup (centralizer (F : Set G))).map
      (centralizer (F : Set G)).subtype := fun k hk =>
    ⟨⟨k, hKC hk⟩, hP (Subgroup.mem_subgroupOf.2 hk), rfl⟩
  have hPC : (P : Subgroup (centralizer (F : Set G))).map (centralizer (F : Set G)).subtype ≤
      centralizer (F : Set G) := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have heq := Ksub_maximal h hZ D hgood X htrans hR hPG hKP' hPC
  have hK'eq : (Ksub z F).subgroupOf (centralizer (F : Set G)) =
      (P : Subgroup (centralizer (F : Set G))) := by
    refine le_antisymm hP fun x hx => ?_
    have hxm : (x : G) ∈ (P : Subgroup (centralizer (F : Set G))).map
        (centralizer (F : Set G)).subtype := ⟨x, hx, rfl⟩
    rw [heq] at hxm
    exact Subgroup.mem_subgroupOf.2 hxm
  unfold Subgroup.relIndex
  rw [hK'eq]
  exact P.not_dvd_index

theorem eq_L1_of_abelian (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {A : Subgroup G} (hAK : A ≤ Ksub z F) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcard : 256 ≤ Nat.card A) : A = L1sub h D hgood := by
  have hL1 : Nat.card (L1sub h D hgood) = 256 := card_L1sub h hZ D hgood X htrans
  by_cases hA : A ≤ L1sub h D hgood
  · exact Subgroup.eq_of_le_of_card_ge hA (by rw [hL1]; exact hcard)
  · exfalso
    obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    have hmul : ∀ x ∈ A, x ∉ L1sub h D hgood → x * a⁻¹ ∈ L1sub h D hgood := by
      intro x hx hxL
      have h1 : x * z ∈ L1sub h D hgood :=
        (mem_L1sub_or h hZ D hgood X (hAK hx)).resolve_left hxL
      have h2 : a * z ∈ L1sub h D hgood :=
        (mem_L1sub_or h hZ D hgood X (hAK haA)).resolve_left haL
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      rwa [show x * z * (a * z)⁻¹ = x * a⁻¹ by group] at this
    have hinF : ∀ x ∈ A ⊓ L1sub h D hgood, x ∈ F := by
      intro x hx
      have h2 : a * z ∈ L1sub h D hgood :=
        (mem_L1sub_or h hZ D hgood X (hAK haA)).resolve_left haL
      have hxa : x * a = a * x := hc x hx.1 a haA
      have hxl : x * (a * z) = (a * z) * x := L1sub_comm h D hgood hx.2 h2
      have hxz : z * x = x * z := by
        have e1 : a * (x * z) = a * (z * x) := by
          calc a * (x * z) = x * a * z := by rw [← mul_assoc, ← hxa, mul_assoc]
            _ = x * (a * z) := by simp only [mul_assoc]
            _ = a * z * x := hxl
            _ = a * (z * x) := by simp only [mul_assoc]
        exact (mul_left_cancel e1).symm
      exact L1sub_centralizer_z h D hgood hx.2 hxz
    have h16 : Nat.card ↥(A ⊓ L1sub h D hgood) ≤ 16 := by
      rw [← D.F_card]
      exact Subgroup.card_le_of_le fun x hx => hinF x hx
    let f : ↥(A ⊓ L1sub h D hgood) × Bool → A := fun p =>
      ⟨(p.1 : G) * (if p.2 then a else 1), Subgroup.mul_mem _ p.1.2.1
        (by split_ifs
            · exact haA
            · exact Subgroup.one_mem _)⟩
    have hsurj : Function.Surjective f := by
      intro x
      by_cases hxL : (x : G) ∈ L1sub h D hgood
      · exact ⟨(⟨x, x.2, hxL⟩, false), Subtype.ext (by simp [f])⟩
      · refine ⟨(⟨(x : G) * a⁻¹, Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ haA),
          hmul x x.2 hxL⟩, true), Subtype.ext ?_⟩
        simp [f]
    have h2 := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
    omega

theorem L1_normalized_of_normalizes_K (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {n : G} (hn : ∀ x, x ∈ Ksub z F ↔ n * x * n⁻¹ ∈ Ksub z F) :
    ∀ x, x ∈ L1sub h D hgood ↔ n * x * n⁻¹ ∈ L1sub h D hgood := by
  apply forall_mem_iff_of_forall_mem
  let B : Subgroup G := (L1sub h D hgood).map (MulAut.conj n).toMonoidHom
  have hBK : B ≤ Ksub z F := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hn x).1 (L1sub_le_K h D hgood hx)
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (MulAut.conj n) a * (MulAut.conj n) b = (MulAut.conj n) b * (MulAut.conj n) a
    rw [← map_mul, ← map_mul, L1sub_comm h D hgood ha hb]
  have hBcard : 256 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective,
      card_L1sub h hZ D hgood X htrans]
  have hBeq : B = L1sub h D hgood := eq_L1_of_abelian h hZ D hgood X htrans hBK hBc hBcard
  intro x hx
  have : n * x * n⁻¹ ∈ B := ⟨x, hx, rfl⟩
  rwa [hBeq] at this

theorem eq_mul_of_isConj_of_mem_Ksub (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) {k : G} (hk : k ∈ Ksub z F) (hconj : IsConj z k) :
    ∃ f ∈ F, k = z * f := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hk2 : k * k = 1 := by
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have hkL : k ∉ L1sub h D hgood := fun hkL =>
    L1_not_isConj h hZ D hgood X htrans hR hkL hconj
  have hkE := mem_E_of_involution_not_mem_L1 h hZ D hgood X hk hk2 hkL
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_centralizer_of_le h D.F_le) hkE
  rcases mem_zpowers_involution h.z_mul_self hb with rfl | rfl
  · exact absurd (by rw [hab, mul_one]; exact F_le_L1sub h D hgood ha) hkL
  · refine ⟨a, ha, ?_⟩
    rw [hab]
    exact (h.z_comm a (D.F_le ha)).symm

end CFSG.EvenSporadicStandard.M23Std
