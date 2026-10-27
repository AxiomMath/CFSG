module

public import CFSG.ClassicalInvolution.Q3.TL3EndB3
public import CFSG.Goldschmidt75.CorollaryA2

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}
  {T : Sylow 2 G}

theorem TightSylowStd.comm_of_mem_cStar (h : TightSylowStd R S t T) {u : G}
    (huT : u ∈ (T : Subgroup G)) (huC : u ∈ centralizerModOdd ⊤ (tightCore R)) {s : G}
    (hs : s ∈ (S : Subgroup R).map R.subtype) : s * u = u * s := by
  set S₀ : Subgroup G := (S : Subgroup R).map R.subtype with hS₀
  have hsyl : IsSylow2In S₀ (tightCore R) := h.datum.sylow_core
  have hc : ⁅u, s⁆ ∈ oddCoreOf (tightCore R) := huC.2.2.2 s (hsyl.1 hs)
  have hcS : ⁅u, s⁆ ∈ S₀ := by
    rw [commutatorElement_def]
    exact S₀.mul_mem (h.normalizes_S₀ huT hs) (S₀.inv_mem hs)
  have h1 : ⁅u, s⁆ = 1 := by
    have hodd : Odd (Nat.card ↥(oddCoreOf (tightCore R))) := oddCoreOf_odd_natCard _
    have h2 : IsPGroup 2 ↥(Subgroup.zpowers ⁅u, s⁆) :=
      hsyl.2.1.to_le (Subgroup.zpowers_le.mpr hcS)
    exact eq_one_of_isPGroup_of_mem_odd hodd hc h2
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact h1.symm

theorem TightSylowStd.exists_commutator_eq (h : TightSylowStd R S t T) :
    ∃ x ∈ (S : Subgroup R).map R.subtype, ∃ y ∈ (S : Subgroup R).map R.subtype, ⁅x, y⁆ = t := by
  obtain ⟨e⟩ := h.q8
  set f : QuaternionGroup 2 →* G :=
    R.subtype.comp ((S : Subgroup R).subtype.comp e.symm.toMonoidHom) with hf
  have hfinj : Function.Injective f :=
    R.subtype_injective.comp ((S : Subgroup R).subtype_injective.comp e.symm.injective)
  have hmem : ∀ q : QuaternionGroup 2, f q ∈ (S : Subgroup R).map R.subtype := fun q =>
    Subgroup.mem_map.mpr ⟨_, (e.symm q).2, rfl⟩
  refine ⟨f (QuaternionGroup.a 1), hmem _, f (QuaternionGroup.xa 0), hmem _, ?_⟩
  have hc : ⁅QuaternionGroup.a (1 : ZMod (2 * 2)), QuaternionGroup.xa (0 : ZMod (2 * 2))⁆ =
      QuaternionGroup.a 2 := by decide
  have hw : f (QuaternionGroup.a 2) ∈ tightCore R := h.datum.sylow_core.1 (hmem _)
  have hsq : f (QuaternionGroup.a 2) * f (QuaternionGroup.a 2) = 1 := by
    rw [← map_mul, show QuaternionGroup.a (2 : ZMod (2 * 2)) * QuaternionGroup.a 2 = 1 by decide,
      map_one]
  have hne : f (QuaternionGroup.a 2) ≠ 1 := fun h1 =>
    absurd (hfinj (h1.trans (map_one f).symm)) (by decide)
  rw [← map_commutatorElement, hc]
  rcases h.isUniqueInvolution.unique _ hw hsq with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem TightSylowStd.mem_commutator_centralizer (h : TightSylowStd R S t T) {B : Subgroup G}
    (hBT : B ≤ (T : Subgroup G)) (hBK : B ≤ centralizerModOdd ⊤ (tightCore R)) :
    t ∈ ⁅Subgroup.centralizer (B : Set G), Subgroup.centralizer (B : Set G)⁆ := by
  have hS₀ : ∀ s ∈ (S : Subgroup R).map R.subtype, s ∈ Subgroup.centralizer (B : Set G) :=
    fun s hs => Subgroup.mem_centralizer_iff.mpr fun b hb =>
      (h.comm_of_mem_cStar (hBT hb) (hBK hb) hs).symm
  obtain ⟨x, hx, y, hy, hxy⟩ := h.exists_commutator_eq
  rw [← hxy]
  exact Subgroup.commutator_mem_commutator (hS₀ x hx) (hS₀ y hy)

theorem genFittingFStar_le_commutator [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) :
    genFittingFStar G ≤ ⁅genFittingFStar G, genFittingFStar G⁆ := by
  have hFn : (genFittingFStar G).Normal := genFittingFStar_normal G
  obtain ⟨a, b, hab⟩ := hnab
  refine genFittingFStar_le_of_normal ⟨a, b, hab⟩ (by infer_instance)
    (Subgroup.commutator_mem_commutator a.2 b.2) fun h1 => hab ?_
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  exact Subtype.ext h1

section Gold


theorem mem_of_stronglyClosed_abelian_fstar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hO : classicalInvolutionOddCore G = ⊥)
    (T : Sylow 2 G) {A : Subgroup G} (hAT : A ≤ (T : Subgroup G)) (hAab : IsMulCommutative A)
    (hcl : fusionStronglyClosed (A : Set G) (T : Subgroup G))
    (hFA : genFittingFStar G ≤ Subgroup.normalClosure (A : Set G)) {x : G}
    (hxT : x ∈ (T : Subgroup G)) (hxF : x ∈ genFittingFStar G) (hx2 : x * x = 1) : x ∈ A := by
  obtain ⟨-, hb, -⟩ := CFSG.Milestones.cl_lit_goldschmidt_strongly_closed_abelian G T A hAT hAab hcl
  set M : Subgroup G := Subgroup.normalClosure (A : Set G) with hM
  set F : Subgroup G := genFittingFStar G with hFdef
  have hMn : M.Normal := Subgroup.normalClosure_normal
  have hFn : F.Normal := genFittingFStar_normal G
  have hO' : goldschmidtOddCore G = ⊥ := hO
  have hodd : goldschmidtOddCore ↥M = ⊥ :=
    CFSG.Goldschmidt.G310.goldschmidtOddCore_eq_bot_of_isSubnormal hO' hMn.isSubnormal
  set π := QuotientGroup.mk' (goldschmidtOddCore ↥M) with hπ
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact hodd
  set K : Subgroup (↥M ⧸ goldschmidtOddCore ↥M) := (F.subgroupOf M).map π with hK
  have hKn : K.Normal := (Subgroup.normal_subgroupOf).map π (QuotientGroup.mk'_surjective _)
  let e : ↥K ≃* ↥F :=
    (Subgroup.equivMapOfInjective (F.subgroupOf M) π hπinj).symm.trans
      (Subgroup.subgroupOfEquivOfLe hFA)
  have hKs : IsSimpleGroup ↥K := e.isSimpleGroup
  have hKnab : ∃ a b : ↥K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨e.symm a, e.symm b, fun h' => hab (e.symm.injective ?_)⟩
    rw [map_mul, map_mul, h']
  obtain ⟨hquasi, -⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hKnab
  have hcomp : IsComponentOf K ⊤ :=
    ⟨le_top, IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤),
      Group.isPerfect_def.mp hquasi.1, hquasi.2.1⟩
  have hKE : K ≤ goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) := le_sSup hcomp
  set xm : ↥M := ⟨x, hFA hxF⟩ with hxm
  have hxK : π xm ∈ K := Subgroup.mem_map.mpr ⟨xm, Subgroup.mem_subgroupOf.mpr hxF, rfl⟩
  have hxsub : xm ∈ (T : Subgroup G).subgroupOf M := Subgroup.mem_subgroupOf.mpr hxT
  have hy2 : π xm ^ 2 = 1 := by
    have : xm ^ 2 = 1 := Subtype.ext (by simpa [sq] using hx2)
    rw [← map_pow, this, map_one]
  have hyc : π xm ∈ Subgroup.closure {u | u ∈ ((T : Subgroup G).subgroupOf M).map π ⊓
      goldschmidtLayer (↥M ⧸ goldschmidtOddCore ↥M) ∧ u ^ 2 = 1} :=
    Subgroup.subset_closure ⟨⟨Subgroup.mem_map.mpr ⟨xm, hxsub, rfl⟩, hKE hxK⟩, hy2⟩
  have hyA : π xm ∈ (A.subgroupOf M).map π := by
    rw [hb]
    exact Subgroup.mem_sup_right hyc
  obtain ⟨a, haA, hae⟩ := Subgroup.mem_map.1 hyA
  have hax : a = xm := hπinj hae
  have haA' : (a : G) ∈ A := Subgroup.mem_subgroupOf.1 haA
  rw [hax] at haA'
  exact haA'

theorem TightSylowStd.mem_of_stronglyClosed_cStar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hF : TightFStarOK G t)
    (h : TightSylowStd R S t T) {B : Subgroup G} (hBT : B ≤ (T : Subgroup G)) (hB : B ≠ ⊥)
    (hsc : fusionStronglyClosed (B : Set G) (T : Subgroup G))
    (hBK : B ≤ centralizerModOdd ⊤ (tightCore R)) : t ∈ B := by
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hC
  set S₂ : Subgroup G := ⁅C, C⁆ ⊓ (T : Subgroup G) with hS₂
  have htT : t ∈ (T : Subgroup G) := h.hST h.datum.mem
  have htS₂ : t ∈ S₂ := ⟨h.mem_commutator_centralizer hBT hBK, htT⟩
  have hS₂sc : fusionStronglyClosed (S₂ : Set G) (T : Subgroup G) :=
    CFSG.Goldschmidt75.theoremB_c T hBT hsc
  have hS₂C : S₂ ≤ C := inf_le_left.trans (Subgroup.commutator_le.mpr fun g₁ h₁ g₂ h₂ => by
    rw [commutatorElement_def]
    exact C.mul_mem (C.mul_mem (C.mul_mem h₁ h₂) (C.inv_mem h₁)) (C.inv_mem h₂))
  have hcomm : ⁅B, S₂⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hS₂C)
  have hA2 := CFSG.Goldschmidt75.corollaryA2 T T hBT inf_le_right hsc hS₂sc hcomm
  have hO : goldschmidtOddCore G = ⊥ := hF.oddCore
  rw [hO, sup_bot_eq] at hA2
  have ht1 : t ≠ 1 := h.isUniqueInvolution.ne_one
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB
  have hFB : genFittingFStar G ≤ Subgroup.normalClosure (B : Set G) :=
    genFittingFStar_le_of_normal hnab Subgroup.normalClosure_normal
      (Subgroup.subset_normalClosure hbB) (fun h1 => hb1 (Subtype.ext h1))
  have hFS₂ : genFittingFStar G ≤ Subgroup.normalClosure (S₂ : Set G) :=
    genFittingFStar_le_of_normal hnab Subgroup.normalClosure_normal
      (Subgroup.subset_normalClosure htS₂) ht1
  have hFA : genFittingFStar G ≤ Subgroup.normalClosure ((B ⊓ S₂ : Subgroup G) : Set G) :=
    (genFittingFStar_le_commutator hnab).trans ((Subgroup.commutator_mono hFB hFS₂).trans hA2)
  have hAab : IsMulCommutative ↥(B ⊓ S₂) :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp (hS₂C y.2.2) x x.2.1)⟩⟩
  have hAcl : fusionStronglyClosed ((B ⊓ S₂ : Subgroup G) : Set G) (T : Subgroup G) :=
    fun a ha g hg => ⟨hsc a ha.1 g hg, hS₂sc a ha.2 g hg⟩
  exact (mem_of_stronglyClosed_abelian_fstar hnab hF.oddCore T (inf_le_left.trans hBT) hAab hAcl
    hFA htT (h.datum.mem_genFittingFStar hF.oddCore) (t_mul_t h.datum)).1

theorem TightSylowStd.false_of_stronglyClosed_cStar [IsSimpleGroup (genFittingFStar G)]
    (hnab : ∃ a b : genFittingFStar G, a * b ≠ b * a) (hF : TightFStarOK G t)
    (h : TightSylowStd R S t T) {B : Subgroup G} (hBT : B ≤ (T : Subgroup G)) (hB : B ≠ ⊥)
    (hsc : fusionStronglyClosed (B : Set G) (T : Subgroup G))
    (hBK : B ≤ centralizerModOdd ⊤ (tightCore R))
    (hg : ∃ g ∈ Subgroup.centralizer (B : Set G),
      g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹)) : False := by
  have htB := h.mem_of_stronglyClosed_cStar hnab hF hBT hB hsc hBK
  obtain ⟨g, hgB, hgt, hgc⟩ := hg
  obtain ⟨k, -, hkT, hkt⟩ := h.exists_conj_mem_sylow hBT hsc hgB hgt hgc
  have hkB : k * t * k⁻¹ ∈ B := by
    have h1 : (k⁻¹)⁻¹ * t * k⁻¹ ∈ (T : Subgroup G) := by rwa [inv_inv]
    have := hsc t htB k⁻¹ h1
    rwa [inv_inv] at this
  exact h.false_of_conj_mem_cStar hkT hkt (hBK hkB)

theorem tightEndGameS_holds {IH : ℕ → Prop} : TightEndGameS IH := by
  intro G _ _ _ _ hnab R S t T hF hstd B hBT hB hsc hBK _ hg
  exact hstd.false_of_stronglyClosed_cStar hnab hF hBT hB hsc hBK hg

theorem tightEndGameOdd_holds {IH : ℕ → Prop} : TightEndGameOdd IH := by
  intro G _ _ _ hIH hnab R S t T hF hstd B hBT hB hsc hBK htB _ hg _
  exact tightEndGameS_holds G hIH hnab R S t T hF hstd B hBT hB hsc hBK htB hg

theorem tightC19_11bS_of_F1 {IH : ℕ → Prop} (hF1 : TightF1S IH) : TightC19_11bS IH :=
  tightC19_11bS_of_F1_endgame hF1 tightEndGameS_holds

end Gold

end CFSG.ClassicalInvolution.Q3
