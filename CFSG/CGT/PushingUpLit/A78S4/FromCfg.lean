module

public import CFSG.CGT.PushingUpLit.A78S4.Cyclic
public import CFSG.CGT.PushingUpLit.A78.NonSylowData
public import CFSG.CGT.PushingUpLit.A78S4.Coords
public import CFSG.CGT.PushingUpLit.A78S4.Cross
public import CFSG.CGT.PushingUpLit.A78S4.Field
public import CFSG.CGT.PushingUpLit.A78S4.SideRec

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.ABGLocalTools

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e) (hZ : Z ≠ ⊥)

include P hZ

theorem sp4Cross (hsyl₁ : IsSylowOf 2 T (Subgroup.normalizer (V : Set G)))
    (hsyl₂ : IsSylowOf 2 T (Subgroup.normalizer (W : Set G))) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hTS : T ≤ S) (hsw : ∃ s ∈ S, s ∉ T)
    (base : Sp4Base G V W (V ⊔ W) T S (Subgroup.normalizer (V : Set G))
      (Subgroup.normalizer (W : Set G)) e)
    (hcent₁ : ∀ z ∈ Z, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G))
    (hcent₂ : ∀ z ∈ Z₂, z ≠ 1 →
      Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (W : Set G))
    (hti₁ : ∀ g : G, Z ⊓ cj g Z ≠ ⊥ → cj g Z = Z)
    (hti₂ : ∀ g : G, Z₂ ⊓ cj g Z₂ ≠ ⊥ → cj g Z₂ = Z₂) :
    Sp4Cross G L₁ L₂ V W Z Z₂ (V ⊔ W) T S e := by
  obtain ⟨D₁⟩ := P.side₁.nat
  obtain ⟨D₂⟩ := P.side₂.nat
  have hZ₂ := P.Z₂_ne_bot hZ
  have hswZ : ∀ s ∈ S, s ∉ T → cj s Z = Z₂ ∧ cj s Z₂ = Z := fun s hs hsT =>
    P.swap_Z hZ (base.swap s hs hsT).1 (base.swap s hs hsT).2
  obtain ⟨s₀, hs₀, hs₀T⟩ := hsw
  have hnot := P.u_not_conj hZ hsyl₁ hS hTS ⟨s₀, hs₀, hs₀T⟩ hsyl₂ hcent₁ hcent₂
  have hnot₂ : ∀ u z : G, UType W V Z₂ Z u → (z ∈ Z₂ ∨ z ∈ Z) → z ≠ 1 → ∀ g : G,
      g⁻¹ * u * g ≠ z := fun u z hu hz hz1 g =>
    hnot u z (P.symm.utype_symm hZ₂ hu) hz.symm hz1 g
  exact
    { Z_le := P.side₁.Z_le_N.trans inf_le_right
      Z₂_le := P.Z₂_le_N.trans inf_le_left
      inf_Z := P.inf_Z
      sup_Z := P.sup_Z hZ
      T_normZ := fun t ht => ⟨cj_eq_of_mem_normalizer_set (P.side₁.T_le_Z ht),
        cj_eq_of_mem_normalizer_set (P.side₂.T_le_Z ht)⟩
      swap_Z := hswZ
      conj_in_V := fun A hA hAV =>
        P.conj_in_V hZ (hswZ s₀ hs₀ hs₀T) hti₁ hti₂ hnot A hA hAV
      conj_in_V₂ := fun A hA hAW => by
        have hA' : ∃ g : G, A = cj g Z₂ ∨ A = cj g Z := by
          obtain ⟨g, hg⟩ := hA
          exact ⟨g, hg.symm⟩
        have h1 := P.symm.conj_in_V hZ₂ ⟨(hswZ s₀ hs₀ hs₀T).2, (hswZ s₀ hs₀ hs₀T).1⟩ hti₂ hti₁
          hnot₂ A hA' hAW
        rw [inf_comm W V] at h1
        rcases h1 with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      cent_L := fun v hv hvZ => P.side₁.cent_L D₁ hv hvZ
      cent_L₂ := fun v hv hvZ₂ => by
        have h1 := P.side₂.cent_L D₂ (by rwa [inf_comm]) hvZ₂
        rwa [sup_comm] at h1
      inv_class := fun x hx hxx hx1 => P.inv_class hZ hx hxx hx1
      u_conj := fun u u' hu hu' => P.u_conj hZ hu hu'
      u_not_conj := hnot }

theorem sp4Field {S : Subgroup G}
    (base : Sp4Base G V W (V ⊔ W) T S (Subgroup.normalizer (V : Set G))
      (Subgroup.normalizer (W : Set G)) e)
    (cross : Sp4Cross G L₁ L₂ V W Z Z₂ (V ⊔ W) T S e) :
    Sp4Field G L₁ L₂ V W Z Z₂ (V ⊔ W) T S e := by
  have hZ₂ := P.Z₂_ne_bot hZ
  have hC := P.sp4Coords hZ
  have hTZ : ∀ t ∈ T, cj t Z = Z := fun t ht => (cross.T_normZ t ht).1
  have hsZ : ∀ s ∈ S, s ∉ T → cj s Z = Z₂ := fun s hs hsT => (cross.swap_Z s hs hsT).1
  have hinv : T ≠ V ⊔ W → ∃ f ∈ T, f ∉ V ⊔ W ∧ f * f = 1 := fun hTJ =>
    P.exists_involution hZ hTJ
  exact
    { S_cyclic := sp4_S_cyclic base hC hTZ hsZ
      exists_inv := hinv
      even_e := fun hTJ => by
        obtain ⟨f, hf, hfJ, hff⟩ := hinv hTJ
        exact P.even_e hf hfJ hff
      inv_conj := fun f hf hfJ hff x hx hxJ hxx => P.inv_conj hZ hf hfJ hff hx hxJ hxx
      no_inv := sp4_no_inv base hC hTZ hsZ hinv
      cent_L := fun f hf hfJ hff => P.centL hZ hf hfJ hff
      cent_L₂ := fun f hf hfJ hff => P.symm.centL hZ₂ hf (by rwa [sup_comm]) hff
      card_ZJf := fun f hf hfJ hff => P.card_CN hZ hf hfJ hff }

end S4Pair

theorem sp4FromCfg : A78Sp4.Sp4FromCfg := by
  intro G _ _ L₁ L₂ T e cfg hns hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have P := cfg.s4Pair hZ
  have hZ₂ := P.Z₂_ne_bot hZ
  obtain ⟨S, hS, hTS⟩ := exists_isSylowOf_ge P.side₁.pT (le_top : T ≤ ⊤)
  have hsw : ∃ s ∈ S, s ∉ T := by
    by_contra hcon
    push Not at hcon
    apply hns
    rw [le_antisymm hTS hcon]
    exact hS
  have base := P.sp4Base hZ cfg.hyg.sylow₁ cfg.hyg.sylow₂ hS hTS hsw
  have side₁ := cfg.sp4Side hZ
  have side₂ := cfg.symm.sp4Side hZ₂
  rw [sup_comm (oTwoIn (L₂ ⊔ T)) (oTwoIn (L₁ ⊔ T))] at side₂
  have cross := P.sp4Cross hZ cfg.hyg.sylow₁ cfg.hyg.sylow₂ hS hTS hsw base side₁.cent_z
    side₂.cent_z side₁.ti side₂.ti
  exact ⟨S, _, _,
    { simple := cfg.simple
      charTwo := cfg.charTwo
      base := base
      side₁ := side₁
      side₂ := side₂
      cross := cross
      field := P.sp4Field hZ base cross
      coords := P.sp4Coords hZ }⟩

end CFSG.CGT.PushingUpLit.A78S4

namespace CFSG.CGT.PushingUpLit.A78

theorem threeSNonSylow : Aschbacher78ThreeSNonSylow :=
  threeSNonSylow_of_sp4 A78S4.sp4FromCfg

end CFSG.CGT.PushingUpLit.A78
