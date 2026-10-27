module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5StatementsS331
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5113Type

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise

@[expose] def Stmt5_1_13_type_nq_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ → conjClosure Kh₁ T = Kh₁ →
    ((IsSL2 5 (↥(o2Img X (oTwoUpper H)) ⧸ CFSG.oddCore ↥(o2Img X (oTwoUpper H))) ∧
        o2Img X Kh₁ = o2Img X (oTwoUpper H) ⊔ oddCoreSub (o2Img X Kh₁)) ∨
      (IsSL2 5 (↥(o2Img X (oTwoUpper H)) ⧸ CFSG.oddCore ↥(o2Img X (oTwoUpper H))) ∧
        ∃ p : ℕ, p.Prime ∧ p ^ 2 % 5 = 1 ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
          IsSL2 p (↥(o2Img X Kh₁) ⧸ CFSG.oddCore ↥(o2Img X Kh₁)))) →
    False

@[expose] def Stmt5_1_13_type_hat7_F4 : Prop :=
  ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L V H B D K₁ X Kh₁ : Subgroup G) (n : ℕ),
    Main513 G T M L V H B D K₁ X Kh₁ n → Case5_512 T H X Kh₁ → conjClosure Kh₁ T = Kh₁ →
    (∀ d ∈ o2Img X (D ⊓ X),
      d ^ 3 ∈ Subgroup.centralizer ((o2Img X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X))) →
    ¬ IsHat (O2Q Kh₁) (alternatingGroup (Fin 7))

namespace Main513

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D K₁ X Kh₁ : Subgroup G} {n : ℕ}

theorem star513_F4 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h510 : Stmt5_1_10_F4) (m : Main513 G T M L V H B D K₁ X Kh₁ n) (heq : K₁ = oTwoUpper H)
    (hcl : conjClosure Kh₁ T = Kh₁) (hL24 : LieModel (O2Q (oTwoUpper H)) .PSL 2 2 2) :
    Star513 (modO2Image X Kh₁) (modO2Image X (oTwoUpper H)) (modO2Image X T) (modO2Image X B)
        (modO2Image X (D ⊓ X)) ∧
      ¬ modO2Image X (D ⊓ X) ≤
        Subgroup.normalizer ((modO2Image X (oTwoUpper H) : Subgroup (O2Q X)) : Set (O2Q X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := m.hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf m.hyp.hStar.1.1
  have hHX : H ≤ X := m.inH.1
  have hXO : pCoreOf 2 X ≠ ⊥ := m.inH.2
  have hTX : T ≤ X := hTH.1.trans hHX
  have hTXs : IsSylowTwoOf T X := h.isSylowTwoOf hTX
  have hKH : oTwoUpper H ≤ H := oTwoUpper_le H
  have hKX : oTwoUpper H ≤ X := hKH.trans hHX
  have hKhc : Kh₁ ∈ cComp X := m.hat.1
  have hKKh : oTwoUpper H ≤ Kh₁ := heq ▸ m.hat.2.1
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := by
    rw [m.closure]
    exact le_normalizer_conjClosure K₁ T
  have hKperf : ⁅oTwoUpper H, oTwoUpper H⁆ = oTwoUpper H := by
    rw [m.closure]
    exact A3.conjClosure_perfect m.comp.2.1
  have hOT : pCoreOf 2 X ≤ T := F7.isSylowTwoOf_pCoreOf_le hTXs
  have hXN : X ≤ Subgroup.normalizer (Kh₁ : Set G) := by
    have := Vol2Native.normal_conjClosure_of_pCoreOf_ne_bot hloc h37 h38 hXO hTXs hKhc
    rwa [hcl] at this
  have hQN : ∀ y : O2Q X,
      y ∈ Subgroup.normalizer ((modO2Image X Kh₁ : Subgroup (O2Q X)) : Set (O2Q X)) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X) y
    exact o2Map_mem_normalizer (hXN x.2)
  have hSsyl : IsSylowTwoOf (modO2Image X T) ⊤ :=
    isSylowTwoOf_top_map_of_surjective (isSylowTwoOf_top_subgroupOf hTXs) _
      (QuotientGroup.mk'_surjective _)
  have hTKb : modO2Image X T ≤ Subgroup.normalizer
      ((modO2Image X (oTwoUpper H) : Subgroup (O2Q X)) : Set (O2Q X)) :=
    Vol2.Ch11.SecS.modO2Image_le_normalizer hTK
  obtain ⟨-, -, hBorel, hHall, -⟩ := h510 G T M L H B D n m.hyp m.nota
  have hBK : B ≤ oTwoUpper H := hHall.1.trans inf_le_right
  have hBX : B ≤ X := hBK.trans hKX
  have hHall' := hHall
  rw [m.hyp.borel_eq hBorel] at hHall'
  have hBb : Lin2.IsHallTwoPrimeOf (modO2Image X B)
      (modO2Image X (oTwoUpper H) ⊓ Subgroup.normalizer
        ((modO2Image X T ⊓ modO2Image X (oTwoUpper H) : Subgroup (O2Q X)) : Set (O2Q X))) := by
    have h1 := isHallTwoPrimeOf_modO2Image (X := X) (inf_le_left.trans hKX) hHall'
    rwa [modO2Image_inf_normalizer hKX inf_le_right (fun x hx => ⟨hOT hx.2, hx.1⟩),
      ← modO2Image_inf_of_pCoreOf_le hOT] at h1
  have hTMH : IsSylowTwoOf T (M ⊓ H) :=
    A4.isSylowTwoOf_mono hTH (le_inf h.T_le hTH.1) inf_le_right
  obtain ⟨hpB₁, hpB₂⟩ := exists_mul_eq_of_hall_sylow m.nota.1 hTMH
  have hD := m.nota.2.1
  have hDcyc : IsCyclic ↥D := (h.isCyclic_card_of_isHall l2TorusFact hD).1
  have hDXcyc : IsCyclic ↥(D ⊓ X) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe (inf_le_left : D ⊓ X ≤ D)).toMonoidHom
      (MulEquiv.surjective _)
  have hBDX : B ≤ Subgroup.normalizer ((D ⊓ X : Subgroup G) : Set G) := fun b hb =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨m.nota.2.2 hb, Subgroup.le_normalizer (hBX hb)⟩
  refine ⟨⟨Subgroup.map_mono fun x hx => hKKh hx, ?_, ?_, hSsyl.2.1, fun y _ => hQN y, hTKb,
    A4.isSylowTwoOf_inf_normal hSsyl le_top fun y _ => hQN y,
    A4.isSylowTwoOf_inf_normal (QuasithinUnique.isSylowTwoOf_of_le hSsyl le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTKb), hBb,
    modO2Image_mul_comm hBX hTX hpB₁ hpB₂,
    isCyclic_of_surjective (barMap inf_le_right) (barMap_surjective inf_le_right),
    Odd.of_dvd_nat hD.2.1 ((Subgroup.card_dvd_of_surjective
      (barMap_surjective inf_le_right)).trans (Subgroup.card_dvd_of_le inf_le_left)),
    fun y _ => hQN y, Vol2.Ch11.SecS.modO2Image_le_normalizer hBDX,
    modO2Image_mul_comm inf_le_right hTX
      (fun d hd c hc => h.exists_mul_eq_of_hall hD hTX hd hc)
      (fun d hd c hc => h.exists_mul_eq_of_hall' hD hTX hd hc)⟩, ?_⟩
  ·
    have : Group.IsPerfect ↥(oTwoUpper H) := Subgroup.isPerfect_iff.mpr hKperf
    have : Group.IsPerfect ↥(modO2Image X (oTwoUpper H)) :=
      Group.IsPerfect.ofSurjective (barMap_surjective hKX)
    exact Subgroup.isPerfect_iff.mp this
  ·
    obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv hKX
    exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e hL24
  ·
    intro hle
    apply m.not_le
    intro d hd
    have hdb : QuotientGroup.mk' (CFSG.pCore 2 ↥X) ⟨d, hd.2⟩ ∈ modO2Image X (D ⊓ X) :=
      ⟨⟨d, hd.2⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩
    exact mem_normalizer_of_modO2Image hKX hKperf (hOT.trans hTK) hd.2 (hle hdb)

end Main513

end CFSG.Quasithin.H13
