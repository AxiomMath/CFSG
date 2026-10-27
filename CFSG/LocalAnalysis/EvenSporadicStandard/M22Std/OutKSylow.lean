module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutL1
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.OutRank
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.RankTwoE

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup CFSG.EvenSporadicStandard.M23Std

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z : G} {F : Subgroup G}

namespace OutOne

theorem L1_not_isConj (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) {x : G} (hx : x ∈ L1sub h hgood) : ¬ IsConj z x :=
  not_isConj_of_elemAb hcr (fun a ha b hb => L1sub_comm h hgood ha hb)
    (fun a ha => L1sub_sq h hgood ha)
    (by rw [card_L1sub h hsq hgood X htrans]; norm_num) hx

theorem mem_E_of_involution_not_mem_L1 (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F) {k : G} (hk : k ∈ Ksub z F) (hk2 : k * k = 1)
    (hk1 : k ∉ L1sub h hgood) : k ∈ F ⊔ zpowers z := by
  rcases mem_L1sub_or h hsq hgood X hk with h1 | h1
  · exact absurd h1 hk1
  · have hℓ2 : (k * z) * (k * z) = 1 := L1sub_sq h hgood h1
    have e : z * k * z = k := by
      have : k * (z * k * z) = 1 := by
        calc k * (z * k * z) = (k * z) * (k * z) := by simp only [mul_assoc]
          _ = 1 := hℓ2
      rw [eq_inv_of_mul_eq_one_right this, inv_eq_of_mul_eq_one_right hk2]
    have hzk : z * (k * z) = k * z * z := by
      calc z * (k * z) = z * k * z := by simp only [mul_assoc]
        _ = k := e
        _ = k * z * z := by rw [mul_assoc, h.z_mul_self, mul_one]
    have hF : k * z ∈ F := L1sub_centralizer_z h hgood h1 hzk
    have hm : (k * z) * z ∈ F ⊔ zpowers z :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_left hF)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
    rwa [mul_assoc, h.z_mul_self, mul_one] at hm

theorem Ksub_maximal (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) {S : Subgroup G} (hS : IsPGroup 2 S) (hKS : Ksub z F ≤ S)
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
  have hzK : z ∈ Ksub z F := E_le_K h (Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hzS : z ∈ S := hKS hzK
  have hconj : (n : G) * z * (n : G)⁻¹ ∈ Ksub z F := by
    have h1 := (Subgroup.mem_normalizer_iff.1 hn ⟨z, hzS⟩).1 (Subgroup.mem_subgroupOf.2 hzK)
    simpa using Subgroup.mem_subgroupOf.1 h1
  have hinv : ((n : G) * z * (n : G)⁻¹) * ((n : G) * z * (n : G)⁻¹) = 1 := by
    calc _ = (n : G) * (z * z) * (n : G)⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have hE : (n : G) * z * (n : G)⁻¹ ∈ F ⊔ zpowers z := by
    by_cases hL1 : (n : G) * z * (n : G)⁻¹ ∈ L1sub h hgood
    · exact absurd (isConj_iff.2 ⟨(n : G), rfl⟩ : IsConj z ((n : G) * z * (n : G)⁻¹))
        (L1_not_isConj h hsq hgood X htrans hcr hL1)
    · exact mem_E_of_involution_not_mem_L1 h hsq hgood X hconj hinv hL1
  have hnC : ∀ f ∈ F, f * (n : G) = (n : G) * f := fun f hf =>
    mem_centralizer_iff.1 (hSC n.2) f hf
  have hnK : (n : G) ∈ Ksub z F := by
    refine mem_Ksub.2 ⟨?_, hnC⟩
    apply forall_mem_iff_of_forall_mem
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ :=
      exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_cent h h.F_le) hx
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

theorem Ksub_sylow (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) :
    IsPGroup 2 (Ksub z F) ∧ ¬ 2 ∣ (Ksub z F).relIndex (centralizer (F : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKP : IsPGroup 2 (Ksub z F) :=
    IsPGroup.of_card (n := 9) (by rw [card_Ksub h htrans]; norm_num)
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
  have heq := Ksub_maximal h hsq hgood X htrans hcr hPG hKP' hPC
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

theorem eq_L1_of_abelian (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {A : Subgroup G} (hAK : A ≤ Ksub z F) (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hcard : 256 ≤ Nat.card A) : A = L1sub h hgood := by
  have hL1 : Nat.card (L1sub h hgood) = 256 := card_L1sub h hsq hgood X htrans
  by_cases hA : A ≤ L1sub h hgood
  · exact Subgroup.eq_of_le_of_card_ge hA (by rw [hL1]; exact hcard)
  · exfalso
    obtain ⟨a, haA, haL⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    have hmul : ∀ x ∈ A, x ∉ L1sub h hgood → x * a⁻¹ ∈ L1sub h hgood := by
      intro x hx hxL
      have h1 : x * z ∈ L1sub h hgood :=
        (mem_L1sub_or h hsq hgood X (hAK hx)).resolve_left hxL
      have h2 : a * z ∈ L1sub h hgood :=
        (mem_L1sub_or h hsq hgood X (hAK haA)).resolve_left haL
      have := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
      rwa [show x * z * (a * z)⁻¹ = x * a⁻¹ by group] at this
    have hinF : ∀ x ∈ A ⊓ L1sub h hgood, x ∈ F := by
      intro x hx
      have h2 : a * z ∈ L1sub h hgood :=
        (mem_L1sub_or h hsq hgood X (hAK haA)).resolve_left haL
      have hxa : x * a = a * x := hc x hx.1 a haA
      have hxl : x * (a * z) = (a * z) * x := L1sub_comm h hgood hx.2 h2
      have hxz : z * x = x * z := by
        have e1 : a * (x * z) = a * (z * x) := by
          calc a * (x * z) = x * a * z := by rw [← mul_assoc, ← hxa, mul_assoc]
            _ = x * (a * z) := by simp only [mul_assoc]
            _ = a * z * x := hxl
            _ = a * (z * x) := by simp only [mul_assoc]
        exact (mul_left_cancel e1).symm
      exact L1sub_centralizer_z h hgood hx.2 hxz
    have h16 : Nat.card ↥(A ⊓ L1sub h hgood) ≤ 16 := by
      rw [← h.F_card]
      exact Subgroup.card_le_of_le fun x hx => hinF x hx
    let f : ↥(A ⊓ L1sub h hgood) × Bool → A := fun p =>
      ⟨(p.1 : G) * (if p.2 then a else 1), Subgroup.mul_mem _ p.1.2.1
        (by split_ifs
            · exact haA
            · exact Subgroup.one_mem _)⟩
    have hsurj : Function.Surjective f := by
      intro x
      by_cases hxL : (x : G) ∈ L1sub h hgood
      · exact ⟨(⟨x, x.2, hxL⟩, false), Subtype.ext (by simp [f])⟩
      · refine ⟨(⟨(x : G) * a⁻¹, Subgroup.mul_mem _ x.2 (Subgroup.inv_mem _ haA),
          hmul x x.2 hxL⟩, true), Subtype.ext ?_⟩
        simp [f]
    have h2 := Nat.card_le_card_of_surjective f hsurj
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool] at h2
    omega

theorem L1_normalized_of_normalizes_K (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    {n : G} (hn : ∀ x, x ∈ Ksub z F ↔ n * x * n⁻¹ ∈ Ksub z F) :
    ∀ x, x ∈ L1sub h hgood ↔ n * x * n⁻¹ ∈ L1sub h hgood := by
  apply forall_mem_iff_of_forall_mem
  let B : Subgroup G := (L1sub h hgood).map (MulAut.conj n).toMonoidHom
  have hBK : B ≤ Ksub z F := by
    rintro _ ⟨x, hx, rfl⟩
    exact (hn x).1 (L1sub_le_K h hgood hx)
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (MulAut.conj n) a * (MulAut.conj n) b = (MulAut.conj n) b * (MulAut.conj n) a
    rw [← map_mul, ← map_mul, L1sub_comm h hgood ha hb]
  have hBcard : 256 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj n).injective,
      card_L1sub h hsq hgood X htrans]
  have hBeq : B = L1sub h hgood := eq_L1_of_abelian h hsq hgood X htrans hBK hBc hBcard
  intro x hx
  have : n * x * n⁻¹ ∈ B := ⟨x, hx, rfl⟩
  rwa [hBeq] at this

theorem eq_mul_of_isConj_of_mem_Ksub (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) {k : G} (hk : k ∈ Ksub z F) (hconj : IsConj z k) :
    ∃ f ∈ F, k = z * f := by
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hk2 : k * k = 1 := by
    rw [← hc]
    calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
      _ = 1 := by rw [h.z_mul_self]; group
  have hkL : k ∉ L1sub h hgood := fun hkL =>
    L1_not_isConj h hsq hgood X htrans hcr hkL hconj
  have hkE := mem_E_of_involution_not_mem_L1 h hsq hgood X hk hk2 hkL
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_mul_of_mem_sup_of_le_centralizer (zpowers_le_cent h h.F_le) hkE
  rcases mem_zpowers_involution h.z_mul_self hb with rfl | rfl
  · exact absurd (by rw [hab, mul_one]; exact F_le_L1sub h hgood ha) hkL
  · refine ⟨a, ha, ?_⟩
    rw [hab]
    exact (h.z_comm a (h.F_le ha)).symm

theorem exists_conj_mem_Ksub (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) {A : Subgroup G} (hA : IsPGroup 2 A) (hAC : A ≤ centralizer (F : Set G)) :
    ∃ c : G, c ∈ centralizer (F : Set G) ∧ ∀ x ∈ A, c * x * c⁻¹ ∈ Ksub z F := by
  obtain ⟨hKP, hKodd⟩ := Ksub_sylow h hsq hgood X htrans hcr
  have hKp : IsPGroup 2 ((Ksub z F).subgroupOf (centralizer (F : Set G))) := hKP.comap_subtype
  have hA' : IsPGroup 2 (A.subgroupOf (centralizer (F : Set G))) := hA.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hKp hKodd hA'
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have := hg ⟨x, hAC hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  simpa using Subgroup.mem_subgroupOf.1 this

theorem L1_maximal (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) {P : Subgroup G} (hP : IsPGroup 2 P) (hLP : L1sub h hgood ≤ P)
    (hPC : P ≤ centralizer (L1sub h hgood : Set G)) : P = L1sub h hgood := by
  refine le_antisymm ?_ hLP
  intro n hn
  by_contra hnL
  have hFL : F ≤ L1sub h hgood := F_le_L1sub h hgood
  have hCF : centralizer (L1sub h hgood : Set G) ≤ centralizer (F : Set G) :=
    Subgroup.centralizer_le hFL
  have hnC : ∀ x ∈ L1sub h hgood, x * n = n * x := fun x hx =>
    mem_centralizer_iff.1 (hPC hn) x hx
  let A : Subgroup G := L1sub h hgood ⊔ zpowers n
  have hAP : A ≤ P := sup_le hLP (by rw [Subgroup.zpowers_le]; exact hn)
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_Ksub h hsq hgood X htrans hcr (hP.to_le hAP)
    (hAP.trans (hPC.trans hCF))
  let B : Subgroup G := (L1sub h hgood).map (MulAut.conj c).toMonoidHom
  have hBK : B ≤ Ksub z F := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x (Subgroup.mem_sup_left hx)
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (MulAut.conj c) a * (MulAut.conj c) b = (MulAut.conj c) b * (MulAut.conj c) a
    rw [← map_mul, ← map_mul, L1sub_comm h hgood ha hb]
  have hBcard : 256 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
      card_L1sub h hsq hgood X htrans]
  have hBeq : B = L1sub h hgood := eq_L1_of_abelian h hsq hgood X htrans hBK hBc hBcard
  have hκK : c * n * c⁻¹ ∈ Ksub z F := hc n (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hκL : c * n * c⁻¹ ∉ L1sub h hgood := by
    intro hκ
    apply hnL
    have : c * n * c⁻¹ ∈ B := hBeq ▸ hκ
    obtain ⟨y, hy, hyn⟩ := this
    have hyn' : c * y * c⁻¹ = c * n * c⁻¹ := hyn
    have : y = n := mul_left_cancel (mul_right_cancel hyn')
    exact this ▸ hy
  have hκC : ∀ x ∈ L1sub h hgood, x * (c * n * c⁻¹) = (c * n * c⁻¹) * x := by
    intro x hx
    have hx' : x ∈ B := hBeq ▸ hx
    obtain ⟨y, hy, rfl⟩ := hx'
    show (MulAut.conj c) y * (c * n * c⁻¹) = (c * n * c⁻¹) * (MulAut.conj c) y
    have := hnC y hy
    calc (MulAut.conj c) y * (c * n * c⁻¹) = c * (y * n) * c⁻¹ := by
          rw [MulAut.conj_apply]
          group
      _ = c * (n * y) * c⁻¹ := by rw [this]
      _ = (c * n * c⁻¹) * (MulAut.conj c) y := by
          rw [MulAut.conj_apply]
          group
  have hℓ : (c * n * c⁻¹) * z ∈ L1sub h hgood :=
    (mem_L1sub_or h hsq hgood X hκK).resolve_left hκL
  have hzF : ∀ x ∈ L1sub h hgood, x ∈ F := by
    intro x hx
    have h1 := hκC x hx
    have h2 : x * ((c * n * c⁻¹) * z) = ((c * n * c⁻¹) * z) * x := L1sub_comm h hgood hx hℓ
    have hxz : z * x = x * z := by
      have e : (c * n * c⁻¹) * (x * z) = (c * n * c⁻¹) * (z * x) := by
        calc (c * n * c⁻¹) * (x * z) = x * ((c * n * c⁻¹) * z) := by
              rw [← mul_assoc, ← h1, mul_assoc]
          _ = ((c * n * c⁻¹) * z) * x := h2
          _ = (c * n * c⁻¹) * (z * x) := by simp only [mul_assoc]
      exact (mul_left_cancel e).symm
    exact L1sub_centralizer_z h hgood hx hxz
  have h16 : Nat.card (L1sub h hgood) ≤ 16 := by
    rw [← h.F_card]
    exact Subgroup.card_le_of_le hzF
  rw [card_L1sub h hsq hgood X htrans] at h16
  omega

theorem L1_sylow (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) :
    IsPGroup 2 (L1sub h hgood) ∧
      ¬ 2 ∣ (L1sub h hgood).relIndex (centralizer (L1sub h hgood : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1P : IsPGroup 2 (L1sub h hgood) :=
    IsPGroup.of_card (n := 8) (by rw [card_L1sub h hsq hgood X htrans]; norm_num)
  have hL1C : L1sub h hgood ≤ centralizer (L1sub h hgood : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => L1sub_comm h hgood hy hx
  refine ⟨hL1P, ?_⟩
  set C := centralizer (L1sub h hgood : Set G) with hC
  have hL1'P : IsPGroup 2 ((L1sub h hgood).subgroupOf C) := hL1P.comap_subtype
  obtain ⟨P, hP⟩ := hL1'P.exists_le_sylow
  have hPG : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map _
  have hLP : L1sub h hgood ≤ (P : Subgroup C).map C.subtype := fun k hk =>
    ⟨⟨k, hL1C hk⟩, hP (Subgroup.mem_subgroupOf.2 hk), rfl⟩
  have hPC : (P : Subgroup C).map C.subtype ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have heq := L1_maximal h hsq hgood X htrans hcr hPG hLP hPC
  have hK'eq : (L1sub h hgood).subgroupOf C = (P : Subgroup C) := by
    refine le_antisymm hP fun x hx => ?_
    have hxm : (x : G) ∈ (P : Subgroup C).map C.subtype := ⟨x, hx, rfl⟩
    rw [heq] at hxm
    exact Subgroup.mem_subgroupOf.2 hxm
  unfold Subgroup.relIndex
  rw [hK'eq]
  exact P.not_dvd_index

theorem exists_normal_two_complement (h : OutOne L z F)
    (hsq : ∀ g : G, g * g ≠ z) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hcr : CentRank z) :
    ∃ N : Subgroup G, N ≤ centralizer (L1sub h hgood : Set G) ∧
      (∀ c ∈ centralizer (L1sub h hgood : Set G), ∀ x ∈ N, c * x * c⁻¹ ∈ N) ∧
      ¬ 2 ∣ Nat.card N ∧ Disjoint N (L1sub h hgood) ∧
      N ⊔ L1sub h hgood = centralizer (L1sub h hgood : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hL1P, hodd⟩ := L1_sylow h hsq hgood X htrans hcr
  set L1 := L1sub h hgood with hL1
  set C := centralizer (L1 : Set G) with hC
  have hL1C : L1 ≤ C := fun x hx =>
    mem_centralizer_iff.2 fun y hy => L1sub_comm h hgood hy hx
  let P : Sylow 2 C := (hL1P.comap_subtype (K := C)).toSylow hodd
  have hPmem : ∀ x : C, x ∈ (P : Subgroup C) ↔ (x : G) ∈ L1 := fun x => Iff.rfl
  have hP : normalizer (P : Set C) ≤ centralizer (P : Set C) := by
    intro g _
    rw [mem_centralizer_iff]
    intro x hx
    exact Subtype.ext (mem_centralizer_iff.1 g.2 (x : G) ((hPmem x).1 hx))
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  let Nk : Subgroup C := (MonoidHom.transferSylow P hP).ker
  refine ⟨Nk.map C.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨k, -, rfl⟩
    exact k.2
  · rintro c hc _ ⟨k, hk, rfl⟩
    refine ⟨⟨c, hc⟩ * k * ⟨c, hc⟩⁻¹, ?_, rfl⟩
    exact (MonoidHom.normal_ker _).conj_mem k hk ⟨c, hc⟩
  · rw [Subgroup.card_map_of_injective C.subtype_injective]
    exact MonoidHom.not_dvd_card_ker_transferSylow P hP
  · rw [Subgroup.disjoint_def]
    rintro x ⟨k, hk, rfl⟩ hx
    have hkP : k ∈ (P : Subgroup C) := (hPmem k).2 hx
    have hdis := MonoidHom.ker_transferSylow_disjoint P hP (P : Subgroup C) P.isPGroup'
    have := Subgroup.disjoint_def.1 hdis hk hkP
    rw [this]
    rfl
  · refine le_antisymm (sup_le (by rintro _ ⟨k, -, rfl⟩; exact k.2) hL1C) fun c hc => ?_
    obtain ⟨⟨k, p⟩, hkp⟩ := hcompl.2 ⟨c, hc⟩
    have hc' : c = (k : C) * (p : C) := congrArg Subtype.val hkp.symm
    rw [hc']
    refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨k, k.2, rfl⟩)
      (Subgroup.mem_sup_right ((hPmem (p : C)).1 p.2))

end OutOne

end CFSG.EvenSporadicStandard.M22Std
