module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFBasic
public import CFSG.RankThree.FFModules.BinaryTransport

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

namespace L34FF

section Rep

variable {E : Type*} [CommGroup E] [Module (ZMod 2) (Additive E)]

variable (E) in
noncomputable abbrev autFTwoRep : Representation (ZMod 2) (MulAut E) (Additive E) :=
  CFSG.RankThree.FFModules.autRep E

theorem autFTwoRep_injective : Function.Injective (autFTwoRep E) :=
  CFSG.RankThree.FFModules.autRep_injective

theorem card_fixSub_autFTwoRep (S : Subgroup (MulAut E)) (B : Subgroup S) :
    Nat.card (CFSG.RankThree.FFModules.fixSub ((autFTwoRep E).comp S.subtype) B) =
      Nat.card (fixV (B.map S.subtype)) :=
  CFSG.RankThree.FFModules.card_fixSub_autRep S B

end Rep

noncomputable abbrev moduleOfSq {E : Type*} [CommGroup E]
    (h : ∀ e : E, e ^ 2 = 1) : Module (ZMod 2) (Additive E) :=
  CFSG.RankThree.FFModules.moduleOfSq h

section Conj

variable {G : Type*} [Group G]

@[expose] noncomputable def conjOnto (W X : Subgroup G)
    (hX : X ≤ Subgroup.normalizer (W : Set G)) : X →* autOn X W :=
  ((conjAct W).comp (Subgroup.inclusion hX)).codRestrict (autOn X W) fun x =>
    ⟨Subgroup.inclusion hX x, x.2, rfl⟩

variable {W X : Subgroup G} (hX : X ≤ Subgroup.normalizer (W : Set G))

theorem conjOnto_apply_coe (x : X) (w : W) :
    (((conjOnto W X hX x : autOn X W) : MulAut W) w : G) = x * w * (x : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe W _ w

theorem conjOnto_surjective : Function.Surjective (conjOnto W X hX) := by
  rintro ⟨φ, y, hy, rfl⟩
  exact ⟨⟨y, hy⟩, rfl⟩

theorem conjOnto_eq_one_iff (x : X) :
    conjOnto W X hX x = 1 ↔ (x : G) ∈ Subgroup.centralizer (W : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h w hw
    have h1 := congrArg (fun φ : autOn X W => (((φ : MulAut W) ⟨w, hw⟩ : W) : G)) h
    simp only [conjOnto_apply_coe] at h1
    have h2 : (x : G) * w * (x : G)⁻¹ = w := h1
    calc w * (x : G) = ((x : G) * w * (x : G)⁻¹) * x := by rw [h2]
      _ = x * w := by group
  · intro h
    apply Subtype.ext
    ext w
    rw [conjOnto_apply_coe]
    change (x : G) * w * (x : G)⁻¹ = w
    rw [← h w w.2, mul_inv_cancel_right]

theorem map_subtype_map_conjOnto {B : Subgroup G} (hBX : B ≤ X) :
    ((B.subgroupOf X).map (conjOnto W X hX)).map (autOn X W).subtype = autOn B W := by
  ext φ
  constructor
  · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨Subgroup.inclusion hX b, hb, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨conjOnto W X hX ⟨y, hBX hy⟩, ⟨⟨y, hBX hy⟩, hy, rfl⟩, rfl⟩

theorem card_map_conjOnto {B : Subgroup G} (hBX : B ≤ X) :
    Nat.card ((B.subgroupOf X).map (conjOnto W X hX)) =
      (B ⊓ Subgroup.centralizer (W : Set G)).relIndex B := by
  rw [← card_autOn_eq_relIndex (hBX.trans hX), ← map_subtype_map_conjOnto hX hBX,
    Subgroup.card_map_of_injective (autOn X W).subtype_injective]

theorem card_fixSub_map_conjOnto (hW : IsElemAbelian 2 W) {B : Subgroup G} (hBX : B ≤ X) :
    let _ : CommGroup W := commGroupOfElemAbelian hW
    let _ : Module (ZMod 2) (Additive W) := moduleOfSq fun w => Subtype.ext (hW.2 w w.2)
    Nat.card (CFSG.RankThree.FFModules.fixSub ((autFTwoRep W).comp (autOn X W).subtype)
      ((B.subgroupOf X).map (conjOnto W X hX))) =
      Nat.card (W ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) := by
  intro _ _
  rw [card_fixSub_autFTwoRep, map_subtype_map_conjOnto hX hBX]
  exact card_fixV_autOn_eq hW (hBX.trans hX)

theorem autFTwoRep_comp_injective (hW : IsElemAbelian 2 W) :
    let _ : CommGroup W := commGroupOfElemAbelian hW
    let _ : Module (ZMod 2) (Additive W) := moduleOfSq fun w => Subtype.ext (hW.2 w w.2)
    Function.Injective ((autFTwoRep W).comp (autOn X W).subtype) := by
  intro _ _ a b h
  exact Subtype.ext (autFTwoRep_injective h)

omit [Group G] in
theorem isKGroup_autOn {G : Type} [Group G] [Finite G] {W X : Subgroup G}
    (hX : X ≤ Subgroup.normalizer (W : Set G)) (hK : CFSG.Open.IsKProper G) (hXtop : X ≠ ⊤) :
    CFSG.IsKGroup (autOn X W) :=
  L34FF.isKGroup_of_catalogSimpleSections_finite
    ((catalogSimpleSections_of_isKProper hK X hXtop).of_surjective _ (conjOnto_surjective hX))

theorem isElementaryAbelian_map_conjOnto {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    CFSG.IsElementaryAbelian 2 ((A.subgroupOf X).map (conjOnto W X hX)) := by
  have hcomm : ∀ a b : (A.subgroupOf X).map (conjOnto W X hX), a * b = b * a := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩ ⟨_, ⟨y, hy, rfl⟩⟩
    apply Subtype.ext
    change conjOnto W X hX x * conjOnto W X hX y = conjOnto W X hX y * conjOnto W X hX x
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have := congrArg Subtype.val (hA.1.is_comm.comm (⟨(x : G), hx⟩ : A) ⟨(y : G), hy⟩)
    simpa using this
  have hsq : ∀ a : (A.subgroupOf X).map (conjOnto W X hX), a ^ 2 = 1 := by
    rintro ⟨_, ⟨x, hx, rfl⟩⟩
    apply Subtype.ext
    change (conjOnto W X hX x) ^ 2 = 1
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hA.2 x hx)
    rw [this, map_one]
  exact { is_comm := ⟨hcomm⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

omit [Group G] in
theorem isElemAbelian_two_sup_of_le_centralizer {G : Type*} [Group G] {A B : Subgroup G}
    (hA : IsElemAbelian 2 A) (hB : IsElemAbelian 2 B)
    (hAB : B ≤ Subgroup.centralizer (A : Set G)) : IsElemAbelian 2 (A ⊔ B) := by
  have hBN : B ≤ Subgroup.normalizer (A : Set G) := hAB.trans (Subgroup.centralizer_le_normalizer _)
  have hmem : ∀ x ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left A B hBN] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    exact ⟨a, ha, b, hb, rfl⟩
  have hcA : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨a', ha'⟩)
  have hcB : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  have hcAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hAB hb) a ha
  refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨a, ha, b, hb, hx⟩ := hmem x x.2
    obtain ⟨a', ha', b', hb', hy⟩ := hmem y y.2
    change (x : G) * y = y * x
    rw [hx, hy]
    calc a * b * (a' * b') = a * a' * (b * b') := by
          rw [mul_assoc, ← mul_assoc b, ← hcAB a' ha' b hb]; group
      _ = a' * a * (b' * b) := by rw [hcA a ha a' ha', hcB b hb b' hb']
      _ = a' * b' * (a * b) := by
          rw [mul_assoc, ← mul_assoc a, hcAB a ha b' hb']; group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    rw [sq, show a * b * (a * b) = a * a * (b * b) by
      rw [mul_assoc, ← mul_assoc b, ← hcAB a ha b hb]; group, ← sq, ← sq, hA.2 a ha, hB.2 b hb,
      one_mul]

end Conj

end L34FF

end CFSG.AGLEmbedding
