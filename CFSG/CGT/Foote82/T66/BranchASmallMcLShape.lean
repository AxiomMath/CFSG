module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.OmegaFacts
import CFSG.CGT.Foote82.T66.Overgroup
public import CFSG.CGT.Foote82.T66.BranchASmallDim
public import CFSG.CGT.Foote82.T66.BranchASmallGL

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11 CFSG.ComponentClassification.OutcomeLocal
open CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Cooperstein.StructureLie
open CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open scoped Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem isComponentOf_map_inj {Γ Δ : Type*} [Group Γ] [Group Δ] (f : Γ →* Δ)
    (hf : Function.Injective f) {H K : Subgroup Γ} (h : IsComponentOf H K) :
    IsComponentOf (H.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map f,
    Open.IsQuasisimple.of_mulEquiv (H.equivMapOfInjective f hf).symm h.2.2⟩

theorem ne_bot_of_isQuasisimple {Γ : Type*} [Group Γ] {K : Subgroup Γ}
    (h : Open.IsQuasisimple ↥K) : K ≠ ⊥ := by
  intro hK
  have : Nontrivial (↥K ⧸ Subgroup.center ↥K) := h.2.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥K ⧸ Subgroup.center ↥K)
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  apply hab
  have ha : a = 1 := Subtype.ext (by simpa [hK] using a.2)
  have hb : b = 1 := Subtype.ext (by simpa [hK] using b.2)
  rw [ha, hb]

theorem eq_top_of_isComponentOf_simple {Y : Type*} [Group Y] [IsSimpleGroup Y]
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) : K = ⊤ := by
  rcases Open.IsSubnormal.eq_bot_or_top hK.2.1 with h | h
  · exact absurd h (ne_bot_of_isQuasisimple hK.2.2)
  · exact h

theorem eq_alt_of_isComponentOf_perm {N : ℕ} {K : Subgroup (Equiv.Perm (Fin N))}
    (hK : IsComponentOf K ⊤) : 5 ≤ N ∧ K = alternatingGroup (Fin N) := by
  classical
  have h := eq_altOn_of_isComponentOf (R := ⊥) (X := ⊤) (K := K) IsPGroup.of_bot le_top
    (by rw [Subgroup.coe_bot, Subgroup.centralizer_eq_top_iff_subset.2 (by simp)]) hK
  have hset : {i : Fin N | ∀ r ∈ (⊥ : Subgroup (Equiv.Perm (Fin N))), r i = i} = Set.univ := by
    ext i
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true, Subgroup.mem_bot]
    rintro r rfl
    rfl
  obtain ⟨h5, hK'⟩ := h
  refine ⟨?_, ?_⟩
  · have hc : Nat.card {i : Fin N // ∀ r ∈ (⊥ : Subgroup (Equiv.Perm (Fin N))), r i = i} = N := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      simp
    omega
  · rw [hK', hset, altOn]
    ext σ
    simp [mem_fixingSubgroup_iff]

theorem isComponentOf_transfer {Γ Y : Type*} [Group Γ] [Group Y] {K C : Subgroup Γ}
    (hK : IsComponentOf K C) (Φ : ↥C ≃* Y) :
    IsComponentOf ((K.subgroupOf C).map Φ.toMonoidHom) ⊤ ∧
      Nat.card ↥((K.subgroupOf C).map Φ.toMonoidHom) = Nat.card K := by
  have h1 := (CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hK.1).1 hK
  have h2 := isComponentOf_map_inj Φ.toMonoidHom Φ.injective h1
  rw [Subgroup.map_top_of_surjective _ Φ.surjective] at h2
  refine ⟨h2, ?_⟩
  rw [Nat.card_congr ((K.subgroupOf C).equivMapOfInjective _ Φ.injective).toEquiv.symm,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv]

theorem injective_of_witness {L : Subgroup (GLV V)} {X M : Type} [Group X] [AddGroup M]
    {R : X → M → M → Prop} (hR : ∀ a b, R 1 a b → b = a) (hfaith : FaithfulTildeV L)
    {α : ↥L →* X} {β : ↥(commSpace L ⊤) →+ M}
    (hker : β.ker = ((fixedSpace L).comap (commSpace L ⊤).subtype).toAddSubgroup)
    (hrel : ∀ (ℓ : ↥L) (w w' : ↥(commSpace L ⊤)), (w' : V) = (ℓ : GLV V) (w : V) →
      R (α ℓ) (β w) (β w')) : Function.Injective α := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro ℓ hℓ
  rw [MonoidHom.mem_ker] at hℓ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine hfaith ℓ ℓ.2 fun w hw => ?_
  have hlw : (ℓ : GLV V) w ∈ commSpace L ⊤ :=
    apply_mem_commSpace_of_normalizer (Subgroup.le_normalizer ℓ.2) hw
  have h1 := hrel ℓ ⟨w, hw⟩ ⟨_, hlw⟩ rfl
  rw [hℓ] at h1
  have h2 := hR _ _ h1
  have h3 : (⟨_, hlw⟩ : ↥(commSpace L ⊤)) - ⟨w, hw⟩ ∈ β.ker := by
    rw [AddMonoidHom.mem_ker, map_sub, h2, sub_self]
  rw [hker] at h3
  exact h3

theorem mulEquiv_of_alt6 {L : Subgroup (GLV V)} (h : IsAltNaturalModule L 6)
    (hfaith : FaithfulTildeV L) : Nonempty (↥L ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨α, hα, β, -, hker, hrel⟩ := h
  have hinj := injective_of_witness (X := ↥(alternatingGroup (Fin 6))) (M := altHeart 6)
    (R := fun (σ : ↥(alternatingGroup (Fin 6))) a b => ∀ x : evenWeight 6, a = (x : altHeart 6) →
      b = (evenWeightPerm (σ : Equiv.Perm (Fin 6)) x : altHeart 6)) (fun a b hab => by
      obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective a
      have := hab x rfl
      rw [this]
      congr 1) hfaith hker hrel
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hα⟩⟩

theorem mulEquiv_of_omegaMinus {L : Subgroup (GLV V)} {m : ℕ} (h : IsOmegaMinusModule L m)
    (hfaith : FaithfulTildeV L) : Nonempty (↥L ≃* ↥(omegaMinusTwo m)) := by
  obtain ⟨α, hα, β, -, hker, hrel⟩ := h
  have hinj := injective_of_witness (R := fun (g : ↥(omegaMinusTwo m)) a b =>
      b = ((g : GL (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) :
        Matrix (Fin m ⊕ Fin m ⊕ Fin 2) (Fin m ⊕ Fin m ⊕ Fin 2) (ZMod 2)) *ᵥ a)
    (fun a b hab => by
      rw [hab]
      simp) hfaith hker hrel
  exact ⟨MulEquiv.ofBijective α ⟨hinj, hα⟩⟩

theorem card_alt_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  have := two_mul_nat_card_alternatingGroup (α := Fin 6)
  rw [Nat.card_perm, Nat.card_fin] at this
  have h : Nat.factorial 6 = 720 := rfl
  omega

theorem two_mul_card_alt (N : ℕ) (hN : 2 ≤ N) :
    2 * Nat.card (alternatingGroup (Fin N)) = Nat.factorial N := by
  have : Nontrivial (Fin N) := Fin.nontrivial_iff_two_le.2 hN
  rw [two_mul_nat_card_alternatingGroup, Nat.card_perm, Nat.card_fin]

theorem card_omegaMinusTwo_two : Nat.card ↥(omegaMinusTwo 2) = 25920 := by
  have h := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_omegaMinusTwo (k := 2) le_rfl
  rw [show (2 * 3 : ℕ) = 6 from rfl] at h
  simp [Finset.prod_Icc_succ_top] at h
  omega

theorem card_omegaMinusTwo_three : Nat.card ↥(omegaMinusTwo 3) = 197406720 := by
  have h := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_omegaMinusTwo (k := 3) (by norm_num)
  simp [Finset.prod_Icc_succ_top] at h
  omega

theorem factorial_ne_51840 (N : ℕ) : Nat.factorial N ≠ 51840 := by
  intro h
  by_cases hN : N ≤ 8
  · have := Nat.factorial_le hN
    have h8 : Nat.factorial 8 = 40320 := rfl
    omega
  · have := Nat.factorial_le (show 9 ≤ N by omega)
    have h9 : Nat.factorial 9 = 362880 := rfl
    omega

theorem factorial_ne_394813440 (N : ℕ) : Nat.factorial N ≠ 394813440 := by
  intro h
  by_cases hN : N ≤ 11
  · have := Nat.factorial_le hN
    have h11 : Nat.factorial 11 = 39916800 := rfl
    omega
  · have := Nat.factorial_le (show 12 ≤ N by omega)
    have h12 : Nat.factorial 12 = 479001600 := rfl
    omega

theorem card_statedSp_cases {r : ℕ} (hr : 3 ≤ r) :
    Nat.card ↥(CFSG.Open.StatedSp r (ZMod 2)) = 1451520 ∨
      2 ^ 16 ∣ Nat.card ↥(CFSG.Open.StatedSp r (ZMod 2)) := by
  rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.OmegaFacts.card_statedSp_zmod_two]
  by_cases h3 : r = 3
  · left
    subst h3
    decide
  · right
    have h4 : 4 ≤ r := by omega
    have h16 : 16 ≤ r ^ 2 := by
      calc 16 = 4 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left h4 2
    exact Dvd.dvd.mul_right (pow_dvd_pow 2 h16) _

theorem mapGL_centralizer_singleton (t : GLV V) :
    mapGL (Subgroup.centralizer ({t} : Set (GLV V))) =
      Subgroup.centralizer ({toGL t} : Set (LinearMap.GeneralLinearGroup (ZMod 2) V)) := by
  ext x
  rw [mem_mapGL, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg toGL h
    simpa using this
  · intro h
    have := congrArg toGL.symm h
    simpa using this

variable {G L : Subgroup (GLV V)} {z : GLV V}

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem isComponentOf_mapGL :
    IsComponentOf (mapGL L) (mapGL (layerIn G) ⊓
      Subgroup.centralizer ({toGL z} : Set (LinearMap.GeneralLinearGroup (ZMod 2) V))) := by
  have h := isComponentOf_map_inj (toGL : GLV V ≃* _).toMonoidHom toGL.injective hc.component
  rw [Subgroup.map_inf_eq _ _ _ toGL.injective,
    show Subgroup.map (toGL : GLV V ≃* _).toMonoidHom
      (Subgroup.centralizer ({z} : Set (GLV V))) = mapGL (Subgroup.centralizer ({z} : Set (GLV V)))
      from rfl, mapGL_centralizer_singleton] at h
  exact isComponentOf_of_le_of_le h (le_inf (mapGL_mono hc.L_le_layerIn) (h.1.trans inf_le_right))
    (inf_le_inf_right _ (mapGL_mono (Subgroup.map_subtype_le _)))

theorem relIndex_eq_two
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) = 1)
    (hzE : z ∉ layerIn G) : (mapGL (layerIn G)).relIndex (mapGL G) = 2 := by
  have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
  set ρ : ↥G →* LinearMap.GeneralLinearGroup (ZMod 2) V :=
    (toGL : GLV V ≃* _).toMonoidHom.comp G.subtype with hρ
  have hρinj : Function.Injective ρ := toGL.injective.comp G.subtype_injective
  have hrange : ρ.range = mapGL G := by
    rw [hρ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hmap : (CFSG.layer ↥G).map ρ = mapGL (layerIn G) := by
    rw [hρ, ← Subgroup.map_map]
  set s : ↥G := ⟨z, hc.z_mem⟩
  have hs : ρ s = toGL z := rfl
  have htr : IsF2Transvection (ρ s) := isF2Transvection_toGL hc.z_mul_z hc.z_ne_one hdim
  have hM : ⊤ ≤ CFSG.layer ↥G ⊔ Subgroup.zpowers s ⊔ ρ.ker := by
    rw [(MonoidHom.ker_eq_bot_iff ρ).2 hρinj, sup_bot_eq]
    have h1 : (CFSG.layer ↥G ⊔ Subgroup.zpowers s).map G.subtype = G := by
      rw [Subgroup.map_sup, MonoidHom.map_zpowers]
      exact hc.conf.std.eq_layerIn_sup.symm
    intro x _
    have hx : (x : GLV V) ∈ (CFSG.layer ↥G ⊔ Subgroup.zpowers s).map G.subtype := h1.symm ▸ x.2
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy
  have hnot : ρ s ∉ (CFSG.layer ↥G).map ρ := by
    rw [hmap, hs]
    intro h
    exact hzE (by simpa using mem_mapGL.1 h)
  have := relIndex_map_eq_two ρ (CFSG.layer ↥G) s htr hM hnot
  rwa [hmap, hrange] at this

end Hyp

end CFSG.CGT.Foote82.BAS
