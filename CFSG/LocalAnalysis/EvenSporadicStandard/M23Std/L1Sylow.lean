module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.KSylow
public import CFSG.LocalAnalysis.EvenSporadicStandard.M23Std.RankTwoE

public section

namespace CFSG.EvenSporadicStandard.M23Std

open Subgroup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {F : Subgroup G}

theorem exists_conj_mem_Ksub (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) {A : Subgroup G} (hA : IsPGroup 2 A) (hAC : A ≤ centralizer (F : Set G)) :
    ∃ c : G, c ∈ centralizer (F : Set G) ∧ ∀ x ∈ A, c * x * c⁻¹ ∈ Ksub z F := by
  obtain ⟨hKP, hKodd⟩ := Ksub_sylow h hZ D hgood X htrans hR
  have hKp : IsPGroup 2 ((Ksub z F).subgroupOf (centralizer (F : Set G))) := hKP.comap_subtype
  have hA' : IsPGroup 2 (A.subgroupOf (centralizer (F : Set G))) := hA.comap_subtype
  obtain ⟨g, hg⟩ := exists_conj_mem_of_isPGroup hKp hKodd hA'
  refine ⟨(g : G), g.2, fun x hx => ?_⟩
  have := hg ⟨x, hAC hx⟩ (Subgroup.mem_subgroupOf.2 hx)
  simpa using Subgroup.mem_subgroupOf.1 this

theorem L1_maximal (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) {P : Subgroup G} (hP : IsPGroup 2 P) (hLP : L1sub h D hgood ≤ P)
    (hPC : P ≤ centralizer (L1sub h D hgood : Set G)) : P = L1sub h D hgood := by
  refine le_antisymm ?_ hLP
  intro n hn
  by_contra hnL
  have hFL : F ≤ L1sub h D hgood := F_le_L1sub h D hgood
  have hCF : centralizer (L1sub h D hgood : Set G) ≤ centralizer (F : Set G) :=
    Subgroup.centralizer_le hFL
  have hnC : ∀ x ∈ L1sub h D hgood, x * n = n * x := fun x hx =>
    mem_centralizer_iff.1 (hPC hn) x hx
  let A : Subgroup G := L1sub h D hgood ⊔ zpowers n
  have hAP : A ≤ P := sup_le hLP (by rw [Subgroup.zpowers_le]; exact hn)
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_Ksub h hZ D hgood X htrans hR (hP.to_le hAP)
    (hAP.trans (hPC.trans hCF))
  let B : Subgroup G := (L1sub h D hgood).map (MulAut.conj c).toMonoidHom
  have hBK : B ≤ Ksub z F := by
    rintro _ ⟨x, hx, rfl⟩
    exact hc x (Subgroup.mem_sup_left hx)
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    show (MulAut.conj c) a * (MulAut.conj c) b = (MulAut.conj c) b * (MulAut.conj c) a
    rw [← map_mul, ← map_mul, L1sub_comm h D hgood ha hb]
  have hBcard : 256 ≤ Nat.card B := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c).injective,
      card_L1sub h hZ D hgood X htrans]
  have hBeq : B = L1sub h D hgood := eq_L1_of_abelian h hZ D hgood X htrans hBK hBc hBcard
  have hκK : c * n * c⁻¹ ∈ Ksub z F := hc n (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
  have hκL : c * n * c⁻¹ ∉ L1sub h D hgood := by
    intro hκ
    apply hnL
    have : c * n * c⁻¹ ∈ B := hBeq ▸ hκ
    obtain ⟨y, hy, hyn⟩ := this
    have hyn' : c * y * c⁻¹ = c * n * c⁻¹ := hyn
    have : y = n := mul_left_cancel (mul_right_cancel hyn')
    exact this ▸ hy
  have hκC : ∀ x ∈ L1sub h D hgood, x * (c * n * c⁻¹) = (c * n * c⁻¹) * x := by
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
  have hℓ : (c * n * c⁻¹) * z ∈ L1sub h D hgood :=
    (mem_L1sub_or h hZ D hgood X hκK).resolve_left hκL
  have hzF : ∀ x ∈ L1sub h D hgood, x ∈ F := by
    intro x hx
    have h1 := hκC x hx
    have h2 : x * ((c * n * c⁻¹) * z) = ((c * n * c⁻¹) * z) * x := L1sub_comm h D hgood hx hℓ
    have hxz : z * x = x * z := by
      have e : (c * n * c⁻¹) * (x * z) = (c * n * c⁻¹) * (z * x) := by
        calc (c * n * c⁻¹) * (x * z) = x * ((c * n * c⁻¹) * z) := by
              rw [← mul_assoc, ← h1, mul_assoc]
          _ = ((c * n * c⁻¹) * z) * x := h2
          _ = (c * n * c⁻¹) * (z * x) := by simp only [mul_assoc]
      exact (mul_left_cancel e).symm
    exact L1sub_centralizer_z h D hgood hx hxz
  have h16 : Nat.card (L1sub h D hgood) ≤ 16 := by
    rw [← D.F_card]
    exact Subgroup.card_le_of_le hzF
  rw [card_L1sub h hZ D hgood X htrans] at h16
  omega

theorem L1_sylow (h : OneClassData L z t)
    (hZ : ∀ u ∈ L, u * u = 1 → u ≠ 1 → IsConj z (u * z)) (D : NData L F) (hgood : GoodK z F)
    (X : FixedData L F)
    (htrans : ∀ f ∈ F, ∃ c : G, (∀ x, x ∈ F ⊔ zpowers z ↔ c * x * c⁻¹ ∈ F ⊔ zpowers z) ∧
      c * z * c⁻¹ = z * f)
    (hR : RankFour L) :
    IsPGroup 2 (L1sub h D hgood) ∧
      ¬ 2 ∣ (L1sub h D hgood).relIndex (centralizer (L1sub h D hgood : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1P : IsPGroup 2 (L1sub h D hgood) :=
    IsPGroup.of_card (n := 8) (by rw [card_L1sub h hZ D hgood X htrans]; norm_num)
  have hL1C : L1sub h D hgood ≤ centralizer (L1sub h D hgood : Set G) := fun x hx =>
    mem_centralizer_iff.2 fun y hy => L1sub_comm h D hgood hy hx
  refine ⟨hL1P, ?_⟩
  set C := centralizer (L1sub h D hgood : Set G) with hC
  have hL1'P : IsPGroup 2 ((L1sub h D hgood).subgroupOf C) := hL1P.comap_subtype
  obtain ⟨P, hP⟩ := hL1'P.exists_le_sylow
  have hPG : IsPGroup 2 ((P : Subgroup C).map C.subtype) := P.isPGroup'.map _
  have hLP : L1sub h D hgood ≤ (P : Subgroup C).map C.subtype := fun k hk =>
    ⟨⟨k, hL1C hk⟩, hP (Subgroup.mem_subgroupOf.2 hk), rfl⟩
  have hPC : (P : Subgroup C).map C.subtype ≤ C := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have heq := L1_maximal h hZ D hgood X htrans hR hPG hLP hPC
  have hK'eq : (L1sub h D hgood).subgroupOf C = (P : Subgroup C) := by
    refine le_antisymm hP fun x hx => ?_
    have hxm : (x : G) ∈ (P : Subgroup C).map C.subtype := ⟨x, hx, rfl⟩
    rw [heq] at hxm
    exact Subgroup.mem_subgroupOf.2 hxm
  unfold Subgroup.relIndex
  rw [hK'eq]
  exact P.not_dvd_index

end CFSG.EvenSporadicStandard.M23Std
