module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixSubT
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixLocal

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.SignalizerFunctor.Helpers
open CFSG.Open

variable {X : Type} [Group X] [Finite X]

namespace Conf46

variable {G T S Q H : Subgroup X} {g : X}

theorem le_normalizer_omegaOne_Z (c : Conf46 G T S Q H g) :
    T ≤ Subgroup.normalizer (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hzW : z ∈ T ⊔ rightConjugate T g := (omegaOne_le _ hz).1
  exact (congrArg Subtype.val
    (c.isMulCommutative_W.is_comm.comm ⟨t, Subgroup.mem_sup_left ht⟩ ⟨z, hzW⟩)).symm

theorem conj_eq_of_le_centralizer (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False) {x : X}
    (hC : rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) x ≤
      Subgroup.centralizer (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X)) :
    rightConjugate (omegaOne ((T ⊔ rightConjugate T g) ⊓ G)) x =
      omegaOne ((T ⊔ rightConjugate T g) ⊓ G) := by
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  have hZab : IsMulCommutative Z₁ :=
    isMulCommutative_of_le ((omegaOne_le _).trans inf_le_left) c.isMulCommutative_W
  have hZS : Z₁ ≤ S ⊓ G :=
    le_inf ((omegaOne_le _).trans (inf_le_left.trans c.W_le_S))
      ((omegaOne_le _).trans inf_le_right)
  have hx : x ∈ G ⊔ T := htop ▸ Subgroup.mem_top x
  obtain ⟨t, ht, h, hh, rfl⟩ := c.frame.mem_sup_iff.mp hx
  have hZt : rightConjugate Z₁ t = Z₁ :=
    (rightConjugate_eq_self_iff Z₁ t).mpr (c.le_normalizer_omegaOne_Z ht)
  rw [← rightConjugate_mul, hZt] at hC ⊢
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [rightConjugate_card])
  intro y hy
  have ha : h * y * h⁻¹ ∈ Z₁ := (mem_rightConjugate_iff Z₁ h y).mp hy
  have hyeq : y = h⁻¹ * (h * y * h⁻¹) * h := by group
  have hmem := mem_of_weaklyClosed c.isSylowOf_inf hZS hZab
    (c.weaklyClosed_omegaOne htop IH hnn) ha hh (by rw [← hyeq]; exact hC hy)
  rwa [← hyeq] at hmem

theorem normal_of_simple (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    {L B : Subgroup X} (hLn : L.Normal) (hBL : B ≤ L)
    (hLB : L ≤ Subgroup.normalizer (B : Set X)) (hBs : IsSimpleGroup B)
    (hZB : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ B) : B.Normal := by
  set Z₁ := omegaOne ((T ⊔ rightConjugate T g) ⊓ G) with hZ₁def
  rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff]
  intro x _
  rw [← rightConjugate_eq_self_iff]
  set B' := rightConjugate B x with hB'def
  have hLx : rightConjugate L x = L := (rightConjugate_eq_self_iff L x).mpr
    (by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x)
  have hB'L : B' ≤ L := by
    have h1 := rightConjugate_le_rightConjugate hBL x
    rwa [hLx] at h1
  have hLB' : L ≤ Subgroup.normalizer (B' : Set X) := by
    intro y hy
    rw [hB'def, ← rightConjugate_normalizer]
    have h1 := rightConjugate_le_rightConjugate hLB x
    rw [hLx] at h1
    exact h1 hy
  have hn : ((B ⊓ B').subgroupOf B).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hLB (hBL hy), hLB' (hBL hy)⟩
  rcases hn.eq_bot_or_eq_top with hbot | htop'
  · exfalso
    have hinf : B ⊓ B' = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at hbot
      have h1 := disjoint_iff.mp hbot
      rwa [inf_eq_left.mpr (inf_le_left : B ⊓ B' ≤ B)] at h1
    have hcomm : ⁅B', B⁆ = ⊥ := by
      rw [eq_bot_iff, ← hinf]
      exact le_inf ((Subgroup.le_normalizer_iff_commutator_le_right).mp (hB'L.trans hLB))
        ((Subgroup.le_normalizer_iff_commutator_le_left).mp (hBL.trans hLB'))
    have hC : rightConjugate Z₁ x ≤ Subgroup.centralizer (Z₁ : Set X) :=
      (rightConjugate_le_rightConjugate hZB x).trans
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
          (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hZB)))
    have hZx := c.conj_eq_of_le_centralizer htop IH hnn hC
    have hZ : Z₁ ≤ B ⊓ B' := le_inf hZB (hZx.symm.le.trans (rightConjugate_le_rightConjugate hZB x))
    rw [hinf, le_bot_iff] at hZ
    exact c.omegaOne_Z_ne_bot hZ
  · have hle : B ≤ B' := by
      intro y hy
      have : (⟨y, hy⟩ : B) ∈ (B ⊓ B').subgroupOf B := htop' ▸ Subgroup.mem_top _
      exact this.2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hB'def, rightConjugate_card])).symm

omit [Finite X] in
theorem le_of_rightConjugate_le {A K : Subgroup X} {y : X}
    (hy : y ∈ Subgroup.normalizer (K : Set X)) (h : rightConjugate A y ≤ K) : A ≤ K := by
  have h1 := rightConjugate_le_rightConjugate h y⁻¹
  rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one,
    (rightConjugate_eq_self_iff K y⁻¹).mpr (Subgroup.inv_mem _ hy)] at h1

theorem sub_normal (c : Conf46 G T S Q H g) (htop : G ⊔ T = ⊤) (hO : CFSG.oddCore G = ⊥)
    (IH : IH46 (Nat.card (G ⊔ T : Subgroup X)))
    (hnn : ∀ D : Subgroup X, omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ D → D ≤ S ⊓ G →
      G ≤ Subgroup.normalizer (D : Set X) → False)
    {L : Subgroup X} (hLn : L.Normal) (hLG : L ≤ G)
    (hcard : Nat.card (L ⊔ T : Subgroup X) < Nat.card (G ⊔ T : Subgroup X)) :
    ⁅L, T⁆ = ⊥ ∨
    ∃ y ∈ L ⊔ T, ∃ S₁ : Subgroup X, Bender46 L T S₁ ∧
      relativeWeakClosure L T S₁ = rightConjugate (T ⊔ rightConjugate T g) y ∧
      (T ⊔ rightConjugate T g) ⊓ G ≤ ⁅T, L⁆ ∧ (⁅T, L⁆).Normal ∧
      Subgroup.normalClosure (omegaOne ((T ⊔ rightConjugate T g) ⊓ G) : Set X) ≤ ⁅T, L⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLN : ∀ x : X, x ∈ Subgroup.normalizer (L : Set X) := fun x => by
    rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top x
  have hTN : T ≤ Subgroup.normalizer (L : Set X) := fun t _ => hLN t
  have hSL : IsSylowOf 2 (S ⊓ L) L := c.sylowFrame.sylow.inf_of_le_normalizer
    (hLG.trans le_sup_left) (fun x _ => hLN x)
  have hinfLT : L ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← c.frame.inf_eq_bot, inf_comm]
    exact inf_le_inf_left T hLG
  have hS₀ := isSylowOf_sup_of_isSylowOf hSL c.frame.isPGroup hTN
    (fun t ht => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer (c.le_S ht), hLN t⟩) hinfLT
  have hS₀S : S ⊓ L ⊔ T ≤ S := sup_le inf_le_left c.le_S
  have hOL : CFSG.oddCore L = ⊥ := oddCore_eq_bot_of_le hLG (fun x _ => hLN x) hO
  have hZ1Z : omegaOne ((T ⊔ rightConjugate T g) ⊓ G) ≤ (T ⊔ rightConjugate T g) ⊓ G :=
    omegaOne_le _
  rcases c.sub_T IH hLG hTN hS₀ hS₀S hcard hOL with hc | ⟨y, hyL, hN, hZL⟩ |
      ⟨y, hyL, S₁, hB, hW₁, hZB⟩
  · exact Or.inl hc
  ·
    exfalso
    set D := pCoreOf 2 L with hDdef
    have hGy : rightConjugate G y = G := (rightConjugate_eq_self_iff G y).mpr
      ((sup_le Subgroup.le_normalizer c.frame.le_normalizer) (sup_le_sup_right hLG T hyL))
    have hZ2 : IsPGroup 2 (rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) y) :=
      isPGroup_rightConjugate (c.isPGroup_S.to_le (inf_le_left.trans c.W_le_S)) y
    have hLZ : L ≤ Subgroup.normalizer
        (rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) y : Set X) := by
      rw [rightConjugate_inf, hGy]
      exact fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hN hx, (sup_le Subgroup.le_normalizer c.frame.le_normalizer) (Subgroup.mem_sup_left
          (hLG hx))⟩
    have hZyD : rightConjugate ((T ⊔ rightConjugate T g) ⊓ G) y ≤ D :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hZL hLZ hZ2
    have hDN : ∀ x : X, x ∈ Subgroup.normalizer (D : Set X) := fun x =>
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hLN x)
    have hZD := le_of_rightConjugate_le (hDN y) hZyD
    have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
    have hDL : D ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
    have hDS : D ≤ S := le_of_isSylowOf_of_le_normalizer c.sylowFrame.sylow hD2
      ((hDL.trans hLG).trans le_sup_left) (fun x _ => hDN x)
    exact hnn D (hZ1Z.trans hZD) (le_inf hDS (hDL.trans hLG)) (fun x _ => hDN x)
  ·
    right
    have hBN : L ⊔ T ≤ Subgroup.normalizer ((⁅T, L⁆ : Subgroup X) : Set X) :=
      sup_le (Subgroup.normalizer_commutator_ge_right T L)
        (Subgroup.normalizer_commutator_ge_left T L)
    have hZB' := le_of_rightConjugate_le (hBN hyL) hZB
    obtain ⟨m, -, -, -, -, -, hBen, -⟩ := id hB
    have hBs : IsSimpleGroup (⁅T, L⁆ : Subgroup X) := hBen.isSimpleGroup
    have hBn : (⁅T, L⁆).Normal := c.normal_of_simple htop IH hnn hLn
      (commutator_le_of_le_normalizer hTN) (le_sup_left.trans hBN) hBs (hZ1Z.trans hZB')
    refine ⟨y, hyL, S₁, hB, hW₁, hZB', hBn, ?_⟩
    exact Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr (hZ1Z.trans hZB'))

end Conf46

end CFSG.ComponentClassification.AschbacherTheorem3
