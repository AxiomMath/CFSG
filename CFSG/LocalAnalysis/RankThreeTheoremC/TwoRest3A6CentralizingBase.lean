module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
import CFSG.LocalAnalysis.RankThreeTheoremC.D1BlockPushUp

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conj_mem_sup_of {H K : Subgroup G} {b : G}
    (hH : ∀ x ∈ H, b * x * b⁻¹ ∈ H ⊔ K) (hK : ∀ x ∈ K, b * x * b⁻¹ ∈ H ⊔ K) :
    ∀ x ∈ H ⊔ K, b * x * b⁻¹ ∈ H ⊔ K := by
  intro x hx
  have h : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj b).toMonoidHom :=
    sup_le (fun y hy => Subgroup.mem_comap.mpr (by simpa using hH y hy))
      (fun y hy => Subgroup.mem_comap.mpr (by simpa using hK y hy))
  simpa using Subgroup.mem_comap.mp (h hx)

theorem le_normalizer_sup {B H K : Subgroup G} (hBH : B ≤ Subgroup.normalizer (H : Set G))
    (hBK : ∀ b ∈ B, ∀ x ∈ K, b * x * b⁻¹ ∈ H ⊔ K) :
    B ≤ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  intro b hb
  apply Subgroup.mem_normalizer_fintype
  exact conj_mem_sup_of
    (fun x hx => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hBH hb) x).mp hx))
    (hBK b hb)

theorem le_of_isMaxInvariantTwo {B R O : Subgroup G}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo B R) (hO : IsPGroup 2 O)
    (hRO : R ≤ Subgroup.normalizer (O : Set G)) (hBO : B ≤ Subgroup.normalizer (O : Set G)) :
    O ≤ R := by
  obtain ⟨hR2, hBR, hmax⟩ := hR
  have h2 : IsPGroup 2 (R ⊔ O : Subgroup G) := hR2.to_sup_of_normal_right' hO hRO
  have hB : B ≤ Subgroup.normalizer ((R ⊔ O : Subgroup G) : Set G) :=
    le_normalizer_sup hBR fun b hb x hx =>
      Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hBO hb) x).mp hx)
  have heq := hmax _ h2 hB le_sup_left
  exact fun x hx => heq ▸ Subgroup.mem_sup_right hx

theorem not_two_dvd_index_inf_of_isMaxInvariantTwo {B R O L : Subgroup G}
    (hR : CFSG.LocalAnalysis.RankThreeUC.S15.IsMaxInvariantTwo B R) (hOR : O ≤ R)
    (hRL : R ≤ Subgroup.normalizer (L : Set G))
    (hBL : ∀ b ∈ B, ∀ l ∈ L, b * l * b⁻¹ * l⁻¹ ∈ O) :
    ¬ 2 ∣ ((L ⊓ R).subgroupOf L).index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hR2, hBR, hmax⟩ := hR
  set D := L ⊔ R with hD
  have hRD : R ≤ D := le_sup_right
  obtain ⟨T₀, hT₀⟩ :=
    (hR2.comap_of_injective D.subtype D.subtype_injective).exists_le_sylow
  set T : Subgroup G := (T₀ : Subgroup D).map D.subtype with hT
  have hTD : T ≤ D := Subgroup.map_subtype_le _
  have hRT : R ≤ T := fun x hx => ⟨⟨x, hRD hx⟩, hT₀ hx, rfl⟩
  have hT2 : IsPGroup 2 T := T₀.isPGroup'.map D.subtype
  have hDN : D ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hRL
  have hLT : L ⊔ T = D :=
    le_antisymm (sup_le le_sup_left hTD) (sup_le le_sup_left (hRT.trans le_sup_right))
  have hidx : ¬ 2 ∣ ((L ⊓ T).subgroupOf L).index := by
    rw [← index_sup_eq_index_inf (hTD.trans hDN), hLT]
    have e : T.subgroupOf D = (T₀ : Subgroup D) :=
      Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
    rw [e]
    exact T₀.not_dvd_index
  have hT'2 : IsPGroup 2 (R ⊔ (L ⊓ T) : Subgroup G) := hT2.to_le (sup_le hRT inf_le_right)
  have hBT' : B ≤ Subgroup.normalizer ((R ⊔ (L ⊓ T) : Subgroup G) : Set G) := by
    refine le_normalizer_sup hBR fun b hb x hx => ?_
    have h1 : b * x * b⁻¹ * x⁻¹ ∈ R ⊔ (L ⊓ T) := Subgroup.mem_sup_left (hOR (hBL b hb x hx.1))
    have h2 : x ∈ R ⊔ (L ⊓ T) := Subgroup.mem_sup_right hx
    simpa using (R ⊔ (L ⊓ T)).mul_mem h1 h2
  have heq := hmax _ hT'2 hBT' le_sup_left
  have hle : (L ⊓ T).subgroupOf L ≤ (L ⊓ R).subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨(Subgroup.mem_subgroupOf.mp hx).1,
      heq ▸ Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)⟩
  exact fun h2 => hidx (h2.trans (Subgroup.index_dvd_of_le hle))

theorem exists_isMaxInvariantTwoIn_ge {B S₀ Y : Subgroup G} (hS₀Y : S₀ ≤ Y)
    (hS₀ : IsPGroup 2 S₀) (hBS₀ : B ≤ Subgroup.normalizer (S₀ : Set G)) :
    ∃ R : Subgroup G, S₀ ≤ R ∧ Hyp111.IsMaxInvariantTwoIn B R Y := by
  classical
  set s : Set (Subgroup G) := {S | S ≤ Y ∧ IsPGroup 2 S ∧
    B ≤ Subgroup.normalizer (S : Set G) ∧ S₀ ≤ S} with hs
  obtain ⟨R, ⟨hRY, hR2, hBR, hS₀R⟩, hmax⟩ :=
    Set.exists_max_image s (fun S : Subgroup G => Nat.card S) (Set.toFinite s)
      ⟨S₀, hS₀Y, hS₀, hBS₀, le_rfl⟩
  refine ⟨R, hS₀R, hRY, hR2, hBR, fun S hSY hS2 hBS hRS => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hRS (hmax S ⟨hSY, hS2, hBS, hS₀R.trans hRS⟩)).symm

end CFSG.LocalAnalysis.RankThreeTheoremC.TwoRest3A6
