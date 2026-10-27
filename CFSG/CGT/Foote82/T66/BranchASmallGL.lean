module

public import CFSG.HardMathSupport.Cooperstein.StructureLie.ShapeAbstract
public import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCTypes
public import CFSG.CGT.Foote82.SetupLayer
public import CFSG.CGT.Foote82.T66.BranchASmallBasic

public section

namespace CFSG.CGT.Foote82.BAS

open CFSG.Open CFSG.Quasithin.G11 CFSG.ComponentClassification.OutcomeLocal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

noncomputable abbrev toGL : GLV V ≃* LinearMap.GeneralLinearGroup (ZMod 2) V :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V).symm

theorem toGL_apply (g : GLV V) (v : V) :
    ((toGL g : LinearMap.GeneralLinearGroup (ZMod 2) V) : V →ₗ[ZMod 2] V) v = g v := rfl

theorem toGL_symm_apply (g : LinearMap.GeneralLinearGroup (ZMod 2) V) (v : V) :
    (toGL.symm g) v = (g : V →ₗ[ZMod 2] V) v := rfl

noncomputable abbrev mapGL (H : Subgroup (GLV V)) :
    Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) V) :=
  H.map (toGL : GLV V ≃* _).toMonoidHom

theorem mem_mapGL {H : Subgroup (GLV V)} {x : LinearMap.GeneralLinearGroup (ZMod 2) V} :
    x ∈ mapGL H ↔ toGL.symm x ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨toGL.symm x, hx, by simp⟩

theorem toGL_mem_mapGL {H : Subgroup (GLV V)} {g : GLV V} (hg : g ∈ H) : toGL g ∈ mapGL H :=
  ⟨g, hg, rfl⟩

theorem mapGL_mono {H K : Subgroup (GLV V)} (h : H ≤ K) : mapGL H ≤ mapGL K :=
  Subgroup.map_mono h

theorem mapGL_commutator (H K : Subgroup (GLV V)) : mapGL ⁅H, K⁆ = ⁅mapGL H, mapGL K⁆ :=
  Subgroup.map_commutator _ _ _

theorem mapGL_injective : Function.Injective (mapGL : Subgroup (GLV V) → _) :=
  Subgroup.map_injective (toGL : GLV V ≃* _).injective

theorem commSpace_zpowers_eq_range {t : GLV V} (ht : t * t = 1) :
    commSpace (Subgroup.zpowers t) ⊤ = LinearMap.range ((t : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  apply le_antisymm
  · refine commSpace_le_iff.2 fun k hk u _ => ?_
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    rw [zpow_eq_zpow_emod n h2]
    rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
    · exact ⟨0, by simp⟩
    · exact ⟨u, by simp⟩
  · rintro _ ⟨v, rfl⟩
    simpa using sub_mem_commSpace (Subgroup.mem_zpowers t) (Submodule.mem_top (x := v))

theorem commutatorSpace_toGL {t : GLV V} (ht : t * t = 1) :
    commutatorSpace (toGL t) = commSpace (Subgroup.zpowers t) ⊤ := by
  rw [commSpace_zpowers_eq_range ht]
  unfold commutatorSpace
  congr 1
  ext v
  simp only [LinearMap.add_apply, LinearMap.id_apply, LinearMap.sub_apply]
  rw [toGL_apply, sub_eq_add_neg, zmod2_neg, add_comm]
  rfl

theorem isF2Transvection_toGL {t : GLV V} (ht : t * t = 1) (ht1 : t ≠ 1)
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers t) ⊤) = 1) :
    IsF2Transvection (toGL t) := by
  refine ⟨fun h => ht1 ?_, by rw [commutatorSpace_toGL ht]; exact hdim⟩
  have := congrArg toGL.symm h
  simpa using this

theorem finrank_comap_fixedSpace (L : Subgroup (GLV V)) :
    Module.finrank (ZMod 2) ↥((fixedSpace L).comap (commSpace L ⊤).subtype) =
      Module.finrank (ZMod 2) ↥(tildeVBot L) := by
  rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype, inf_comm]

theorem finrank_tildeV_add (L : Subgroup (GLV V)) :
    Module.finrank (ZMod 2) (TildeV L) + Module.finrank (ZMod 2) ↥(tildeVBot L) =
      Module.finrank (ZMod 2) ↥(commSpace L ⊤) := by
  rw [← finrank_comap_fixedSpace]
  exact Submodule.finrank_quotient_add_finrank _

theorem card_tildeV_of_witness {L : Subgroup (GLV V)} {X M : Type} [Group X] [AddGroup M]
    {R : X → M → M → Prop} (h : TildeVWitness L X M R) :
    Nat.card (TildeV L) = Nat.card M := by
  obtain ⟨-, -, β, hβ, hker, -⟩ := h
  have e := (QuotientAddGroup.quotientAddEquivOfEq hker).symm.trans
    (QuotientAddGroup.quotientKerEquivOfSurjective β hβ)
  exact Nat.card_congr e.toEquiv

theorem two_pow_finrank_tildeV {L : Subgroup (GLV V)} {X M : Type} [Group X] [AddGroup M]
    {R : X → M → M → Prop} (h : TildeVWitness L X M R) :
    2 ^ Module.finrank (ZMod 2) (TildeV L) = Nat.card M := by
  rw [← card_tildeV_of_witness h, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]

theorem finrank_tildeV_alt6 {L : Subgroup (GLV V)} (h : IsAltNaturalModule L 6) :
    Module.finrank (ZMod 2) (TildeV L) = 4 := by
  have h1 := two_pow_finrank_tildeV h
  rw [CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.card_altHeart_even (by norm_num)
    (by decide)] at h1
  exact Nat.pow_right_injective (le_refl 2) h1

theorem finrank_tildeV_omegaMinus {L : Subgroup (GLV V)} {m : ℕ} (h : IsOmegaMinusModule L m) :
    Module.finrank (ZMod 2) (TildeV L) = 2 * m + 2 := by
  have h1 := two_pow_finrank_tildeV h
  rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_fin] at h1
  have : m + (m + 2) = 2 * m + 2 := by ring
  rw [this] at h1
  exact Nat.pow_right_injective (le_refl 2) h1

theorem commSpace_le_fixedSpace_of_mul_self {t : GLV V} (ht : t * t = 1) :
    commSpace (Subgroup.zpowers t) ⊤ ≤ fixedSpace (Subgroup.zpowers t) := by
  rw [commSpace_zpowers_eq_range ht]
  rintro _ ⟨v, rfl⟩ k hk
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
  have h2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
  rw [zpow_eq_zpow_emod n h2]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> rw [h]
  · simp
  · have htt : ∀ w, t (t w) = w := fun w => by
      have := congrArg (fun f : GLV V => f w) ht
      simpa using this
    simp only [zpow_one, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe, map_sub,
      htt]
    rw [← zmod2_neg (t v - v), neg_sub]

theorem fixedSpace_zpowers_eq_ker (t : GLV V) :
    fixedSpace (Subgroup.zpowers t) = LinearMap.ker ((t : V →ₗ[ZMod 2] V) - LinearMap.id) := by
  ext v
  simp only [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, LinearEquiv.coe_coe,
    sub_eq_zero]
  constructor
  · intro h
    exact h t (Subgroup.mem_zpowers t)
  · intro h k hk
    have : k ∈ MulAction.stabilizer (GLV V) v :=
      Subgroup.zpowers_le.2 (MulAction.mem_stabilizer_iff.2 h) hk
    exact MulAction.mem_stabilizer_iff.1 this

theorem finrank_fixedSpace_add_commSpace {t : GLV V} (ht : t * t = 1) :
    Module.finrank (ZMod 2) ↥(fixedSpace (Subgroup.zpowers t)) +
      Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers t) ⊤) = Module.finrank (ZMod 2) V := by
  rw [fixedSpace_zpowers_eq_ker, commSpace_zpowers_eq_range ht, add_comm]
  exact LinearMap.finrank_range_add_finrank_ker _

variable {G L : Subgroup (GLV V)} {z : GLV V}

namespace Hyp

variable (hc : Hyp G L z)
include hc

theorem commSpace_z_ne_bot : commSpace (Subgroup.zpowers z) ⊤ ≠ ⊥ := by
  intro h
  apply hc.z_ne_one
  apply LinearEquiv.ext
  intro v
  have : z v - v ∈ commSpace (Subgroup.zpowers z) ⊤ :=
    sub_mem_commSpace (Subgroup.mem_zpowers z) Submodule.mem_top
  rw [h, Submodule.mem_bot, sub_eq_zero] at this
  exact this

theorem genByTransvections_mapGL
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) = 1) :
    ∃ S : Set (LinearMap.GeneralLinearGroup (ZMod 2) V),
      (∀ t ∈ S, IsF2Transvection t) ∧ mapGL G = Subgroup.closure S := by
  refine ⟨(toGL : GLV V ≃* _) '' {x | ∃ g ∈ G, x = g * z * g⁻¹}, ?_, ?_⟩
  · rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    have h1 : toGL (g * z * g⁻¹) = toGL g * toGL z * (toGL g)⁻¹ := by simp
    rw [h1]
    exact CFSG.HardMathSupport.Cooperstein.StructureLie.isF2Transvection_conj
      (isF2Transvection_toGL hc.z_mul_z hc.z_ne_one hdim) _
  · conv_lhs => rw [hc.conf.gen]
    exact MonoidHom.map_closure _ _

theorem irreducible_mapGL : ∀ W : Submodule (ZMod 2) V,
    (∀ g ∈ mapGL G, ∀ w ∈ W, (g : V →ₗ[ZMod 2] V) w ∈ W) → W = ⊥ ∨ W = ⊤ := by
  intro W hW
  have hinv : Invariant G W := fun g hg w hw => hW (toGL g) (toGL_mem_mapGL hg) w hw
  rcases hc.irr.2.2 W hinv bot_le le_top with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem L_le_layerIn : L ≤ layerIn G := hc.setup.toSetup6.le_layerIn

theorem layerIn_perfect : ⁅layerIn G, layerIn G⁆ = layerIn G := by
  rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect]

theorem layerIn_ne_bot : layerIn G ≠ ⊥ := fun h =>
  hc.L_ne_bot (le_bot_iff.1 (h ▸ hc.L_le_layerIn))

theorem eq_layerIn_of_mem (hz : z ∈ layerIn G) : G = layerIn G := by
  have h := hc.conf.std.eq_layerIn_sup
  refine le_antisymm ?_ (Subgroup.map_subtype_le _)
  calc G = layerIn G ⊔ Subgroup.zpowers z := h
    _ ≤ layerIn G := sup_le le_rfl (Subgroup.zpowers_le.2 hz)

theorem finrank_tildeV_add_two_le
    (hdim : Module.finrank (ZMod 2) ↥(commSpace (Subgroup.zpowers z) ⊤) = 1) :
    Module.finrank (ZMod 2) (TildeV L) + 2 ≤ Module.finrank (ZMod 2) V := by
  have hUF : commSpace L ⊤ ≤ fixedSpace (Subgroup.zpowers z) :=
    (hc.setup.toSetup6.lemma61 (Subgroup.mem_zpowers z)).2
  have hAF := commSpace_le_fixedSpace_of_mul_self hc.z_mul_z
  have hn := finrank_fixedSpace_add_commSpace hc.z_mul_z
  have hq := finrank_tildeV_add L
  by_cases hAU : commSpace (Subgroup.zpowers z) ⊤ ≤ commSpace L ⊤
  ·
    have hAC : commSpace (Subgroup.zpowers z) ⊤ ≤ tildeVBot L :=
      le_inf (fun w hw l hl => hc.fix_commSpace_z l hl w hw) hAU
    have h1 := Submodule.finrank_mono hAC
    have h2 := Submodule.finrank_mono hUF
    omega
  ·
    have hlt : commSpace L ⊤ < commSpace L ⊤ ⊔ commSpace (Subgroup.zpowers z) ⊤ :=
      lt_of_le_of_ne le_sup_left fun h => hAU (h ▸ le_sup_right)
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    have h2 := Submodule.finrank_mono (sup_le hUF hAF)
    omega

end Hyp

end CFSG.CGT.Foote82.BAS
