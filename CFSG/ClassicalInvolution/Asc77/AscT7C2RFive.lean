module

public import CFSG.ClassicalInvolution.Asc77.AscT7C2RFix
public import CFSG.ClassicalInvolution.Asc77.AscT7C2RGen

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected

namespace T7C2

section Gen

variable {S Q : Type*} [Group S] [Group Q]

theorem GenLE.of_map_injective {φ : S →* Q} (hφ : Function.Injective φ) {H : Subgroup S} {n : ℕ}
    (h : GenLE (H.map φ) n) : GenLE H n := by
  classical
  obtain ⟨t, ht, htc⟩ := h
  obtain ⟨L, hL, hLH, hLt⟩ := exists_lift_finset φ H t (fun y hy => by
    rw [← htc]
    exact Subgroup.subset_closure hy)
  refine ⟨L, hL.trans ht, ?_⟩
  have hle : Subgroup.closure (L : Set S) ≤ H :=
    (Subgroup.closure_le H).mpr fun x hx => hLH x hx
  apply le_antisymm hle
  intro x hx
  have hmem : φ x ∈ (Subgroup.closure (L : Set S)).map φ := by
    rw [MonoidHom.map_closure, ← Finset.coe_image, hLt, htc]
    exact ⟨x, hx, rfl⟩
  obtain ⟨y, hy, hyx⟩ := hmem
  rwa [← hφ hyx]

theorem genLE_two_of_closure_pair {G : Type*} [Group G] {W : Subgroup G} {a b : G} (ha : a ∈ W)
    (hb : b ∈ W) (hab : a * b = b * a) (hgen : Subgroup.closure ({a, b} : Set G) = W)
    {B : Subgroup G} (hB : B ≤ W) : GenLE B 2 := by
  have hgen' : Subgroup.closure ({(⟨a, ha⟩ : ↥W), ⟨b, hb⟩} : Set ↥W) = ⊤ := by
    apply Subgroup.map_injective W.subtype_injective
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hgen
  have h2 := genLE_two_of_abelian (a := (⟨a, ha⟩ : ↥W)) (b := ⟨b, hb⟩) (Subtype.ext hab) hgen'
    (B.subgroupOf W)
  exact GenLE.of_subgroupOf hB h2

end Gen

section Main

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}

theorem genLE_four_of_le_MGrp [IsSimpleGroup G] {K K' W : Subgroup G} {S : Sylow 2 G}
    {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8)
    (hSM : (S : Subgroup G) ≤ MGrp Ω W) {H : Subgroup G} (hH : H ≤ (S : Subgroup G)) :
    GenLE H 4 := by
  have hst : AscStand p f Ω K := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hW : W ∈ WSet Ω := hd.hW
  have hWab := Thompson.commutes_of_mem_WSet hp hq hΩ hW
  obtain ⟨a, b, ha, hb, hgen⟩ := exists_two_gen_W hs hd h8
  obtain ⟨e⟩ := hd.hS4
  have hSN : (S : Subgroup G) ≤ Subgroup.normalizer (W : Set G) :=
    hSM.trans (Thompson.MGrp_le_normalizer Ω W)
  let ι : ↥(S : Subgroup G) →* ↥(Subgroup.normalizer (W : Set G)) := Subgroup.inclusion hSN
  have hψ : ∀ x : ↥(S : Subgroup G), (Thompson.piN W).comp ι x ∈ muGroup Ω W := by
    intro x
    have h1 : (Thompson.piN W).comp ι x = Thompson.piG W (x : G) :=
      (Thompson.piG_of_mem (hSN x.2)).symm
    rw [h1]
    exact Thompson.piG_mem_muGroup (Subgroup.mem_sup_left (hSM x.2))
  let ψ : ↥(S : Subgroup G) →* ↥(muGroup Ω W) :=
    ((Thompson.piN W).comp ι).codRestrict (muGroup Ω W) hψ
  let φ : ↥(S : Subgroup G) →* Equiv.Perm (Fin 4) := e.toMonoidHom.comp ψ
  have hker : φ.ker ≤ W.subgroupOf (S : Subgroup G) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : ψ x = 1 := e.injective (hx.trans (map_one e).symm)
    have h2 : Thompson.piN W (ι x) = 1 := congrArg Subtype.val h1
    have h3 : ((ι x : ↥(Subgroup.normalizer (W : Set G))) : G) ∈ W ⊔ OCW W :=
      (Thompson.piN_eq_one_iff W (ι x)).mp h2
    rw [Subgroup.mem_subgroupOf]
    exact Thompson.inf_sup_OCW_le (Thompson.isPGroup_of_mem_WSet hW) S.isPGroup' ⟨x.2, h3⟩
  have hA : ∀ B : Subgroup ↥(S : Subgroup G), B ≤ W.subgroupOf (S : Subgroup G) →
      GenLE B 2 := by
    intro B hB
    apply GenLE.of_map_injective (Subgroup.subtype_injective (S : Subgroup G))
    refine genLE_two_of_closure_pair ha hb (hWab a ha b hb) hgen ?_
    rintro y ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.mp (hB hx)
  have h4 := genLE_four_of_ker S.isPGroup' φ (W.subgroupOf (S : Subgroup G)) hA hker
    (H.subgroupOf (S : Subgroup G))
  exact GenLE.of_subgroupOf hH h4

theorem twoSubgroupsFourGenerated_of_le_MGrp [IsSimpleGroup G] {K K' W : Subgroup G}
    {S : Sylow 2 G} {R R' : Subgroup G} {z u : G} (hs : Hyp23Setting p f Ω K K' z)
    (hd : Hyp24Data Ω K K' W S R R' z u) (h8 : Nat.card ↥R = 8)
    (hSM : (S : Subgroup G) ≤ MGrp Ω W) : TwoSubgroupsFourGenerated G := by
  intro P hP
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := exists_conjSub_eq_of_sylow Q S
  have hle : conjSub g P ≤ (S : Subgroup G) := hg ▸ conjSub_mono hPQ
  have h4 := GenLE.conj (genLE_four_of_le_MGrp hs hd h8 hSM hle) g⁻¹
  have hP' : (conjSub g P).map (MulAut.conj g⁻¹).toMonoidHom = P := conjSub_inv_conjSub g P
  rw [hP'] at h4
  exact h4

end Main

end T7C2

variable (p f : ℕ) [Fact p.Prime]

theorem T7C2.c24_5_proved : C24_5 p f := by
  intro G _ _ _ Ω K K' W S R R' z u hyp h8
  by_cases hSM : (S : Subgroup G) ≤ MGrp Ω W
  · exact Or.inr (Or.inr (T7C2.twoSubgroupsFourGenerated_of_le_MGrp hyp.std.setting hyp.data h8
      hSM))
  · exact Or.inl hSM

@[expose] def C24_9_core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → Nat.card ↥R = 8 → ¬ (S : Subgroup G) ≤ MGrp Ω W → False

variable {p f}

theorem T7C2.c24_9_of_core (h : C24_9_core p f) : C24_9 p f := by
  intro G _ _ _ Ω K K' W S R R' z u hyp
  have hst : AscStand p f Ω K := hyp.std.1.stand
  have hR8 : 8 ≤ Nat.card ↥R := hst.hyp.eight_le_of_mem_RSet hst.odd hyp.hR.1
  by_contra hlt
  have h8 : Nat.card ↥R = 8 := by omega
  rcases T7C2.c24_5_proved p f G Ω K K' W S R R' z u hyp h8 with hnot | hconc
  · exact h G Ω K K' W S R R' z u hyp h8 hnot
  · exact hyp.std.1.cex hconc


variable (p f)

@[expose] def C24_8_big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (Ω : Set (Subgroup G))
    (K K' W : Subgroup G) (S : Sylow 2 G) (R R' : Subgroup G) (z u : G),
    Hyp24 p f Ω K K' W S R R' z u → 8 < Nat.card ↥R → ∀ g : G, g⁻¹ * z * g = u → ∀ d x : G,
      d ∈ (Subgroup.centralizer (R : Set G) ⊓
        Subgroup.normalizer ((conjSub g⁻¹ K : Subgroup G) : Set G) ⊓ (S : Subgroup G)) ⊓
        Subgroup.centralizer (R' : Set G) → orderOf d = 4 → x ∈ R' ⊓ W → orderOf x = 4 →
        (if piSign p f then SectionLieType p f Ω (rLayer Ω (d * x)) .PSL 3
          else SectionLieType p f Ω (rLayer Ω (d * x)) .PSU 3) ∧
        rLayer Ω (d * x) ⊔ K' = ⊤

variable {p f}

theorem T7C2.c24_8_of_big (h9 : C24_9 p f) (h : C24_8_big p f) : C24_8 p f := by
  intro G _ _ _ Ω K K' W S R R' z u hyp g hg d x hd od hx ox
  exact h G Ω K K' W S R R' z u hyp (h9 G Ω K K' W S R R' z u hyp) g hg d x hd od hx ox

end CFSG.ClassicalInvolution.Asc77
