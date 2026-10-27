module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6Six
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelAbs

public section

namespace CFSG.QuasithinUnique.Borel252.A6

open CFSG.Open

abbrev M6 : Type := ↥A6s

def U6 : Subgroup M6 := D0.subgroupOf A6s

def Ra : Subgroup M6 := VA.subgroupOf A6s

def Rb : Subgroup M6 := VB.subgroupOf A6s

def Ka : Subgroup M6 := Sa.subgroupOf A6s

def Kb : Subgroup M6 := Sb.subgroupOf A6s

theorem card_sub {H : Subgroup P6} (h : H ≤ A6s) : Nat.card (H.subgroupOf A6s) = Nat.card H :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem sylow_U6 : IsSylowTwoOf U6 ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h8 : Nat.card U6 = 2 ^ 3 := by
    rw [U6, card_sub D0_le_A6, card_D0]
    norm_num
  refine ⟨le_top, IsPGroup.of_card h8, ?_⟩
  rw [show (U6.subgroupOf ⊤).index = U6.index from Subgroup.relIndex_top_right U6]
  have h := Subgroup.card_mul_index U6
  rw [h8, card_A6] at h
  omega

theorem Ra_le_U6 : Ra ≤ U6 := fun _ hx => VA_le_D0 hx

theorem Rb_le_U6 : Rb ≤ U6 := fun _ hx => VB_le_D0 hx

theorem sup_Ra_Rb : Ra ⊔ Rb = U6 := by
  apply Subgroup.map_injective A6s.subtype_injective
  rw [Subgroup.map_sup, Ra, Rb, U6, Subgroup.map_subgroupOf_eq_of_le VA_le_A6,
    Subgroup.map_subgroupOf_eq_of_le VB_le_A6, Subgroup.map_subgroupOf_eq_of_le D0_le_A6,
    sup_VA_VB]

theorem center_trivial_M6 : ∀ m : M6, (∀ y : M6, m * y = y * m) → m = 1 := fun m hm =>
  Subtype.ext (center_A6 m.2 fun y hy => congrArg Subtype.val (hm ⟨y, hy⟩))

theorem cent_Ra (g : M6) (hg : ∀ r ∈ Ra, g * r = r * g) : g ∈ Ra :=
  cent_VA g.2 fun v hv => congrArg Subtype.val (hg ⟨v, VA_le_A6 hv⟩ hv)

theorem cent_Rb (g : M6) (hg : ∀ r ∈ Rb, g * r = r * g) : g ∈ Rb :=
  cent_VB g.2 fun v hv => congrArg Subtype.val (hg ⟨v, VB_le_A6 hv⟩ hv)

theorem normalizer_U6 : Subgroup.normalizer (U6 : Set M6) = U6 := by
  rw [U6, ← Subgroup.subgroupOf_normalizer_eq D0_le_A6]
  ext x
  exact norm_D0 x x.2

theorem normalizer_Ra : Subgroup.normalizer (Ra : Set M6) = Ka := by
  rw [Ra, ← Subgroup.subgroupOf_normalizer_eq VA_le_A6]
  ext x
  exact norm_VA x x.2

theorem normalizer_Rb : Subgroup.normalizer (Rb : Set M6) = Kb := by
  rw [Rb, ← Subgroup.subgroupOf_normalizer_eq VB_le_A6]
  ext x
  exact norm_VB x x.2

theorem U6_lt_Ka : U6 < Ka := by
  refine lt_of_le_of_ne (fun x hx => D0_le_Sa hx) fun h => ?_
  obtain ⟨hsa, hnd, -, -, -, -, hev, -, -⟩ := witness_ok
  have hmem : (⟨perm6 [[2, 3], [4, 5]], Equiv.Perm.mem_alternatingGroup.2 hev⟩ : M6) ∈ Ka :=
    (mem_Sa _).2 hsa
  rw [← h] at hmem
  exact hnd ((mem_D0 _).1 hmem)

theorem U6_lt_Kb : U6 < Kb := by
  refine lt_of_le_of_ne (fun x hx => D0_le_Sb hx) fun h => ?_
  obtain ⟨-, -, hsb, hnd, -, -, -, hev, -⟩ := witness_ok
  have hmem : (⟨perm6 [[1, 4], [3, 5]], Equiv.Perm.mem_alternatingGroup.2 hev⟩ : M6) ∈ Kb :=
    (mem_Sb _).2 hsb
  rw [← h] at hmem
  exact hnd ((mem_D0 _).1 hmem)

theorem Ka_lt_top : Ka < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => ?_
  obtain ⟨-, -, -, -, hw, -, -, -, hev⟩ := witness_ok
  have hmem : (⟨perm6 [[0, 4, 3]], Equiv.Perm.mem_alternatingGroup.2 hev⟩ : M6) ∈ Ka := by
    rw [h]
    exact Subgroup.mem_top _
  exact hw ((mem_Sa _).1 hmem)

theorem Kb_lt_top : Kb < ⊤ := by
  refine lt_top_iff_ne_top.2 fun h => ?_
  obtain ⟨-, -, -, -, -, hw, -, -, hev⟩ := witness_ok
  have hmem : (⟨perm6 [[0, 4, 3]], Equiv.Perm.mem_alternatingGroup.2 hev⟩ : M6) ∈ Kb := by
    rw [h]
    exact Subgroup.mem_top _
  exact hw ((mem_Sb _).1 hmem)

theorem only_A6 (X : Subgroup M6) (h1 : Subgroup.normalizer (U6 : Set M6) < X) (h2 : X < ⊤) :
    X = Ka ∨ X = Kb := by
  rw [normalizer_U6] at h1
  have hcoe : ∀ x : M6, x ∈ X ↔ (x : P6) ∈ X.map A6s.subtype := fun x =>
    ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, hyx⟩ => by
      have : y = x := Subtype.ext hyx
      rwa [this] at hy⟩
  have hDY : D0 ≤ X.map A6s.subtype := fun d hd =>
    ⟨⟨d, D0_le_A6 hd⟩, h1.le (show (⟨d, D0_le_A6 hd⟩ : M6) ∈ U6 from hd), rfl⟩
  have hYA : X.map A6s.subtype ≤ A6s := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  rcases six_overgroups _ hDY hYA with hY | hY | hY | hY
  · exfalso
    have hXU : X ≤ U6 := fun x hx => by
      have := (hcoe x).1 hx
      rw [hY] at this
      exact this
    exact lt_irrefl _ (lt_of_lt_of_le h1 hXU)
  · left
    ext x
    rw [hcoe x, hY]
    exact Iff.rfl
  · right
    ext x
    rw [hcoe x, hY]
    exact Iff.rfl
  · exfalso
    apply h2.ne
    ext x
    refine ⟨fun _ => Subgroup.mem_top _, fun _ => ?_⟩
    rw [hcoe x, hY]
    exact x.2

theorem borelData_A6 : BorelData M6 U6 Ra Rb where
  center_trivial := center_trivial_M6
  sylow := sylow_U6
  le₁ := Ra_le_U6
  le₂ := Rb_le_U6
  sup := sup_Ra_Rb
  cent₁ := cent_Ra
  cent₂ := cent_Rb
  lt₁ := by
    rw [normalizer_U6, normalizer_Ra]
    exact U6_lt_Ka
  lt₂ := by
    rw [normalizer_U6, normalizer_Rb]
    exact U6_lt_Kb
  lt_top₁ := by
    rw [normalizer_Ra]
    exact Ka_lt_top
  lt_top₂ := by
    rw [normalizer_Rb]
    exact Kb_lt_top
  core₁ := by
    refine pCoreOf_normalizer_eq sylow_U6 Ra_le_U6 ?_ ?_
    · rw [normalizer_Ra]
      exact U6_lt_Ka.le
    · intro c hc h
      exact core_VA hc fun g hg => h ⟨g, Sa_le_A6 hg⟩ (by rw [normalizer_Ra]; exact hg)
  core₂ := by
    refine pCoreOf_normalizer_eq sylow_U6 Rb_le_U6 ?_ ?_
    · rw [normalizer_Rb]
      exact U6_lt_Kb.le
    · intro c hc h
      exact core_VB hc fun g hg => h ⟨g, Sb_le_A6 hg⟩ (by rw [normalizer_Rb]; exact hg)
  only := fun X h1 h2 => by
    rw [normalizer_Ra, normalizer_Rb]
    exact only_A6 X h1 h2

end CFSG.QuasithinUnique.Borel252.A6
