module

public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5Classify
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifySylow
public import CFSG.GH74.QTGen4.DSGen4.OpenLeaves

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Background.Harris.F112S3Big
open Certificates.A5GL42 (Mat4 Vec4 commSet fixSet klein normSet NatFacts OrthFacts IsMulSet
  Offender)
open scoped commutatorElement Matrix

attribute [-instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

section Aux

variable {G : Type} [Group G] [Finite G] {P L E K T X Y : Subgroup G} {H : Finset Mat4}

noncomputable def actSet (M : A5Model P L E K H) (X : Subgroup G) : Finset Mat4 :=
  open Classical in
  Finset.univ.filter fun m => ∃ x : ↥P, (x : G) ∈ X ∧ glMat (M.F.M x) = m

theorem mem_actSet {M : A5Model P L E K H} {X : Subgroup G} {m : Mat4} :
    m ∈ actSet M X ↔ ∃ x : ↥P, (x : G) ∈ X ∧ glMat (M.F.M x) = m := by
  classical
  simp [actSet]

theorem relIndex_core_eq_card_actSet (M : A5Model P L E K H) (h : A5Pre P L E K)
    (hXP : X ≤ P) (hfaith : ∀ x ∈ X, (∀ e ∈ E, ⁅x, e⁆ ∈ K) → x ∈ pCoreOf 2 P) :
    (X ⊓ pCoreOf 2 P).relIndex X = (actSet M X).card := by
  classical
  let f : ↥X →* GL (Fin 4) (ZMod 2) := M.F.M.comp (Subgroup.inclusion hXP)
  have hker : f.ker = (X ⊓ pCoreOf 2 P).subgroupOf X := by
    ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hx1
      refine ⟨x.2, hfaith x x.2 (fun e he => ?_)⟩
      exact ElemFrame.comm_mem_of_M_eq_one M.F h.norm_E (Subgroup.inclusion hXP x) hx1 he
    · rintro ⟨-, hxQ⟩
      exact M.core _ hxQ
  rw [Subgroup.relIndex, ← hker, Subgroup.index_ker]
  let g : ↥f.range → ↥(actSet M X) := fun u =>
    ⟨glMat u.1, mem_actSet.mpr (by
      obtain ⟨⟨x, hx⟩, hxu⟩ := u.2
      exact ⟨Subgroup.inclusion hXP ⟨x, hx⟩, hx, by rw [← hxu]; rfl⟩)⟩
  have hg : Function.Bijective g := by
    constructor
    · intro u w huw
      exact Subtype.ext (Units.ext (congrArg Subtype.val huw))
    · rintro ⟨m, hm⟩
      obtain ⟨x, hxX, rfl⟩ := mem_actSet.mp hm
      exact ⟨⟨M.F.M x, ⟨⟨x, hxX⟩, rfl⟩⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective g hg), Nat.card_eq_fintype_card, Fintype.card_coe]

theorem m4_aux (h : A5Pre P L E K) (hT : IsSylowTwoOf T L) (M : A5Model P L E K H)
    (sd : SylowData M T) (hX : X ≤ T ⊔ pCoreOf 2 P) (hq : ⁅⁅E, X⁆, X⁆ ≤ K) (hnt : ¬ ⁅E, X⁆ ≤ K)
    (hfaith : ∀ x ∈ X, (∀ e ∈ E, ⁅x, e⁆ ∈ K) → x ∈ pCoreOf 2 P) (hKY : K ≤ Y) (hYE : Y ≤ E)
    (hYc : ∀ y ∈ Y, ∀ x ∈ X, ⁅y, x⁆ ∈ K)
    (hcard : Y.relIndex E ≤ (X ⊓ pCoreOf 2 P).relIndex X) :
    actSet M X ⊆ klein sd.x sd.y ∧ IsMulSet (actSet M X) ∧ Offender (actSet M X) ∧
      (img M.F Y).card * Y.relIndex E = 16 ∧ (img M.F Y).card ≤ (fixSet (actSet M X)).card ∧
      Y.relIndex E ≤ (actSet M X).card := by
  have hTP : T ≤ P := hT.1.trans h.le
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  have hXP : X ≤ P := hX.trans (sup_le hTP hQP)
  have hrel : Y.relIndex E ≤ (actSet M X).card := by
    rw [← relIndex_core_eq_card_actSet M h hXP hfaith]; exact hcard
  have hsub : actSet M X ⊆ klein sd.x sd.y := by
    intro a ha
    obtain ⟨x, hxX, rfl⟩ := mem_actSet.mp ha
    obtain ⟨hxP, t, htT, hMt, -⟩ := M.exists_act_eq_of_mem_sup h hT (hX hxX)
    have : M.F.M x = M.F.M t := hMt
    rw [this]
    exact sd.toA t htT
  have hmul : IsMulSet (actSet M X) := by
    refine ⟨mem_actSet.mpr ⟨1, X.one_mem, by simp [glMat]⟩, fun a ha b hb => ?_⟩
    obtain ⟨x, hx, rfl⟩ := mem_actSet.mp ha
    obtain ⟨y, hy, rfl⟩ := mem_actSet.mp hb
    exact mem_actSet.mpr ⟨x * y, X.mul_mem hx hy, by simp [glMat, Units.val_mul]⟩
  have hquad : ∀ a₁ ∈ actSet M X, ∀ a₂ ∈ actSet M X, ∀ v : Vec4,
      (v - a₁ *ᵥ v) - a₂ *ᵥ (v - a₁ *ᵥ v) = 0 := by
    intro a₁ ha₁ a₂ ha₂ v
    obtain ⟨x₁, hx₁, rfl⟩ := mem_actSet.mp ha₁
    obtain ⟨x₂, hx₂, rfl⟩ := mem_actSet.mp ha₂
    obtain ⟨e, he⟩ := M.F.surj (Multiplicative.ofAdd v)
    have hv : v = Multiplicative.toAdd (M.F.φ e) := by rw [he]; rfl
    have hcE : ⁅(e : G), (x₁ : G)⁆ ∈ E := ElemFrame.comm_right_mem h.norm_E x₁.2 e.2
    have hφ := M.F.phi_comm h.norm_E x₁ e ⟨_, hcE⟩ rfl
    have hd : ⁅⁅(e : G), (x₁ : G)⁆, (x₂ : G)⁆ ∈ K :=
      hq (Subgroup.commutator_mem_commutator
        (Subgroup.commutator_mem_commutator e.2 hx₁) hx₂)
    have hfix := (comm_mem_K_iff (F := M.F) h.norm_E x₂.2 hcE).mp hd
    rw [hφ] at hfix
    rw [hv]
    exact sub_eq_zero.mpr hfix.symm
  have hnontriv : ∃ a ∈ actSet M X, a ≠ 1 := by
    by_contra hcon
    apply hnt
    rw [Subgroup.commutator_le]
    intro e he x hx
    have hxP' : x ∈ P := hXP hx
    have h1 : glMat (M.F.M ⟨x, hxP'⟩) = 1 := by
      by_contra hne
      exact hcon ⟨_, mem_actSet.mpr ⟨⟨x, hxP'⟩, hx, rfl⟩, hne⟩
    rw [comm_mem_K_iff h.norm_E hxP' he, h1, Matrix.one_mulVec]
  have hsubY : img M.F Y ⊆ fixSet (actSet M X) := by
    intro v hv
    obtain ⟨e, heY, rfl⟩ := mem_img.mp hv
    unfold fixSet
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, fun a ha => ?_⟩
    obtain ⟨x, hxX, rfl⟩ := mem_actSet.mp ha
    exact (comm_mem_K_iff h.norm_E x.2 e.2).mp (hYc e heY x hxX)
  have hprod : (img M.F Y).card * Y.relIndex E = 16 := by
    have h1 := Subgroup.relIndex_mul_relIndex K Y E hKY hYE
    rw [relIndex_eq_card_img M.F hKY hYE, h.card] at h1
    exact h1
  have himg : (img M.F Y).card ≤ (fixSet (actSet M X)).card := Finset.card_le_card hsubY
  refine ⟨hsub, hmul, ⟨hnontriv, hquad, ?_⟩, hprod, himg, hrel⟩
  rw [← hprod]
  exact Nat.mul_le_mul himg hrel

end Aux

theorem leafM4 : LeafM4 := by
  intro G _ _ P L E K T X Y hc hT hX hq hnt hfaith hKY hYE hYc hcard
  have h := hc.toPre
  have hF := a5Facts
  have hTP : T ≤ P := hT.1.trans h.le
  have hQP : pCoreOf 2 P ≤ P := CFSG.LieType.BorelTits.pCoreOf_le 2 P
  rcases h.exists_model hF with ⟨hnat, ⟨M⟩⟩ | ⟨hnat, ⟨M⟩⟩
  · obtain ⟨sd⟩ := M.exists_sylowData hF.groupN h hT
    have hmem : klein sd.x sd.y ∈ Certificates.A5GL42.kleinGroups Certificates.A5GL42.HN :=
      sd.mem_kleinGroups
    have hA := hF.kleinN _ hmem
    obtain ⟨hsub, hmul, hoff, hprod, himg, hrel⟩ :=
      m4_aux h hT M sd hX hq hnt hfaith hKY hYE hYc hcard
    obtain ⟨⟨h0, hadd, hc4, hfix, hne1⟩, ⟨-, hoffA⟩⟩ := hA
    have hEq : actSet M X = klein sd.x sd.y :=
      hoffA _ (Finset.mem_powerset.mpr hsub) hmul hoff
    refine ⟨hnat, ?_, ?_⟩
    · apply le_antisymm
      · exact sup_le hX le_sup_right
      · refine sup_le (fun t htT => ?_) le_sup_right
        have htP : t ∈ P := hTP htT
        have hmt : glMat (M.F.M ⟨t, htP⟩) ∈ actSet M X := by
          rw [hEq]; exact sd.toA ⟨t, htP⟩ htT
        obtain ⟨x, hxX, hxt⟩ := mem_actSet.mp hmt
        have hxs : (x : G) ∈ T ⊔ pCoreOf 2 P := hX hxX
        have hs : t * (x : G)⁻¹ ∈ T ⊔ pCoreOf 2 P :=
          (T ⊔ pCoreOf 2 P).mul_mem ((le_sup_left : T ≤ T ⊔ pCoreOf 2 P) htT)
            ((T ⊔ pCoreOf 2 P).inv_mem hxs)
        have hsP : t * (x : G)⁻¹ ∈ P := P.mul_mem htP (P.inv_mem x.2)
        have hM1 : M.F.M ⟨t * (x : G)⁻¹, hsP⟩ = 1 := by
          have : (⟨t * (x : G)⁻¹, hsP⟩ : ↥P) = ⟨t, htP⟩ * x⁻¹ := Subtype.ext (by simp)
          rw [this, map_mul, map_inv]
          have : M.F.M ⟨t, htP⟩ = M.F.M x := Units.ext hxt.symm
          rw [this, mul_inv_cancel]
        have hQ := M.mem_core_of_act_eq_one h hT hs hsP hM1
        have : t = (t * (x : G)⁻¹) * (x : G) := by simp
        rw [this]
        exact (X ⊔ pCoreOf 2 P).mul_mem ((le_sup_right : pCoreOf 2 P ≤ X ⊔ pCoreOf 2 P) hQ)
          ((le_sup_left : X ≤ X ⊔ pCoreOf 2 P) hxX)
    · have hfixc : (fixSet (actSet M X)).card = 4 := by
        rw [hEq, ← hfix]; exact hc4
      have hAc : (actSet M X).card = 4 := by rw [hEq]; exact klein_card sd.isKlein
      have h1 : (img M.F Y).card ≤ 4 := by rw [← hfixc]; exact himg
      have h2 : Y.relIndex E ≤ 4 := by rw [← hAc]; exact hrel
      nlinarith
  · obtain ⟨sd⟩ := M.exists_sylowData hF.groupO h hT
    have hmem : klein sd.x sd.y ∈ Certificates.A5GL42.kleinGroups Certificates.A5GL42.HO :=
      sd.mem_kleinGroups
    have hA := hF.kleinO _ hmem
    obtain ⟨hsub, hmul, hoff, -, -, -⟩ := m4_aux h hT M sd hX hq hnt hfaith hKY hYE hYc hcard
    obtain ⟨-, ⟨-, -, hnoff⟩⟩ := hA
    exact absurd hoff (hnoff _ (Finset.mem_powerset.mpr hsub) hmul)

end CFSG.GH74.QTGen4.DSGen4
