module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourLocal
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.SecModel
public import CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542.MS24
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.Alt7FourBud
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.AltSevenA1Orbit
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesExtraComponents
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorus

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData

open Module CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF CFSG.RankThree.FFModules
  CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542

variable {G : Type*} [Group G] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] noncomputable def restRep (ρ : Representation (ZMod 2) G W) (U : Submodule (ZMod 2) W)
    (S : Subgroup G) (h : ∀ s ∈ S, ∀ u ∈ U, ρ s u ∈ U) : Representation (ZMod 2) ↥S ↥U where
  toFun s := (ρ s).restrict (fun u hu => h s s.2 u hu)
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

theorem restRep_apply_coe (ρ : Representation (ZMod 2) G W) (U : Submodule (ZMod 2) W)
    (S : Subgroup G) (h : ∀ s ∈ S, ∀ u ∈ U, ρ s u ∈ U) (s : S) (u : U) :
    ((restRep ρ U S h s u : U) : W) = ρ s u := rfl

theorem mem_map_equiv_iff {G' : Type*} [Group G'] (e : G ≃* G') (R : Subgroup G) (x : G) :
    e x ∈ R.map e.toMonoidHom ↔ x ∈ R := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : y = x := e.injective hyx
    rwa [← this]
  · intro hx; exact ⟨x, hx, rfl⟩

theorem normalizer_map_equiv {G' : Type*} [Group G'] (e : G ≃* G') (R : Subgroup G) (g : G) :
    e g ∈ Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup G') : Set G') ↔
      g ∈ Subgroup.normalizer (R : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    rw [← mem_map_equiv_iff e R x, ← mem_map_equiv_iff e R (g * x * g⁻¹), map_mul, map_mul,
      map_inv]
    exact h (e x)
  · intro h x'
    obtain ⟨x, rfl⟩ := e.surjective x'
    rw [mem_map_equiv_iff, ← map_inv, ← map_mul, ← map_mul, mem_map_equiv_iff]
    exact h x

theorem card_normalizer_map_ge {G' : Type*} [Group G'] [Finite G'] (e : G ≃* G')
    (R : Subgroup G) :
    Nat.card (Subgroup.normalizer (R : Set G)) ≤
      Nat.card (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup G') : Set G')) := by
  have hmap : (Subgroup.normalizer (R : Set G)).map e.toMonoidHom ≤
      Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup G') : Set G') := by
    rintro _ ⟨g, hg, rfl⟩
    exact (normalizer_map_equiv e R g).2 hg
  calc Nat.card (Subgroup.normalizer (R : Set G))
      = Nat.card ((Subgroup.normalizer (R : Set G)).map e.toMonoidHom) :=
        (Subgroup.card_map_of_injective e.injective).symm
    _ ≤ _ := Subgroup.card_le_of_le hmap

theorem Alt7Hyp.of_mulEquiv {G' : Type*} [Group G'] [Finite G'] (e : G ≃* G') (h : Alt7Hyp G') :
    Alt7Hyp G where
  card_le R hc hs := by
    have h1 := h.card_le (R.map e.toMonoidHom)
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hc a ha b hb])
      (by
        rintro _ ⟨a, ha, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hs a ha, map_one])
    rwa [Subgroup.card_map_of_injective e.injective] at h1
  conj a b ha1 ha2 hb1 hb2 := by
    have hca := h.conj (e a) (e b) (by simpa using ha1) (by rw [← map_pow, ha2, map_one])
      (by simpa using hb1) (by rw [← map_pow, hb2, map_one])
    obtain ⟨c, hc⟩ := isConj_iff.1 hca
    refine isConj_iff.2 ⟨e.symm c, ?_⟩
    apply e.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact hc
  order5 := by
    obtain ⟨a, b, ha1, ha2, hb1, hb2, hab⟩ := h.order5
    refine ⟨e.symm a, e.symm b, ?_, ?_, ?_, ?_, ?_⟩
    · intro h'; apply ha1; simpa using congrArg e h'
    · apply e.injective; rw [map_pow, MulEquiv.apply_symm_apply, ha2, map_one]
    · intro h'; apply hb1; simpa using congrArg e h'
    · apply e.injective; rw [map_pow, MulEquiv.apply_symm_apply, hb2, map_one]
    · rw [← map_mul, MulEquiv.orderOf_eq]; exact hab
  card_inv := by
    rw [← h.card_inv]
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun t => ?_)
    simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe]
    constructor
    · rintro ⟨h2, h1⟩
      exact ⟨by rw [← map_pow, h2, map_one], by simpa using h1⟩
    · rintro ⟨h2, h1⟩
      refine ⟨?_, ?_⟩
      · apply e.injective; rw [map_pow, h2, map_one]
      · intro h'; apply h1; rw [h', map_one]
  card_G := by rw [Nat.card_congr e.toEquiv]; exact h.card_G
  klein R hR hc hs h72 := by
    have hcard : Nat.card (R.map e.toMonoidHom) = 4 := by
      rw [Subgroup.card_map_of_injective e.injective]; exact hR
    have hN : 72 ≤ Nat.card (Subgroup.normalizer ((R.map e.toMonoidHom : Subgroup G') : Set G')) :=
      h72.trans (card_normalizer_map_ge e R)
    obtain ⟨E, hE, hE9⟩ := h.klein (R.map e.toMonoidHom) hcard
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_mul, hc a ha b hb])
      (by
        rintro _ ⟨a, ha, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_pow, hs a ha, map_one]) hN
    refine ⟨E.comap e.toMonoidHom, fun g hg => ?_, ?_⟩
    · exact (normalizer_map_equiv e R g).1 (hE hg)
    · rw [← hE9]
      have := Subgroup.comap_equiv_eq_map_symm e E
      rw [show E.comap e.toMonoidHom = E.map e.symm.toMonoidHom from this]
      exact Subgroup.card_map_of_injective e.symm.injective
  klein_unique {D R R'} hD hR hR' h4 h4' h2 h2' h72 h72' := by
    have hmap := fun (S : Subgroup G) (hS : S ≤ D) => Subgroup.map_mono (f := e.toMonoidHom) hS
    have := h.klein_unique (D := D.map e.toMonoidHom) (R := R.map e.toMonoidHom)
      (R' := R'.map e.toMonoidHom) (hD.map e.toMonoidHom) (hmap R hR) (hmap R' hR')
      (by rw [Subgroup.card_map_of_injective e.injective]; exact h4)
      (by rw [Subgroup.card_map_of_injective e.injective]; exact h4')
      (by
        rintro _ ⟨a, ha, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_pow, h2 a ha, map_one])
      (by
        rintro _ ⟨a, ha, rfl⟩
        simp only [MulEquiv.coe_toMonoidHom, ← map_pow, h2' a ha, map_one])
      (h72.trans (card_normalizer_map_ge e R)) (h72'.trans (card_normalizer_map_ge e R'))
    exact Subgroup.map_injective e.injective this

section Basic

variable [Finite G] [Finite W] (ρ : Representation (ZMod 2) G W)
  {L : Subgroup G} (eL : ↥L ≃* alternatingGroup (Fin 7)) {U : Submodule (ZMod 2) W}
  (hUc : U = commOn ρ L ⊤) (hUUL : commOn ρ L U = U) (hU0 : U ≠ ⊥)

include hUc in
theorem inv_normalizer {γ : G} (hγ : γ ∈ Subgroup.normalizer (L : Set G)) {u : W} (hu : u ∈ U) :
    ρ γ u ∈ U := by
  subst hUc
  exact CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.isInvariant_commOn_top (ρ := ρ)
    (le_refl _) γ hγ u hu

include hUc eL hUUL hU0 in
theorem faithful_on {l₁ l₂ : G} (hl₁ : l₁ ∈ L) (hl₂ : l₂ ∈ L)
    (h : ∀ u ∈ U, ρ l₁ u = ρ l₂ u) : l₁ = l₂ := by
  have hLU : ∀ s ∈ L, ∀ u ∈ U, ρ s u ∈ U := fun s hs u hu =>
    inv_normalizer ρ hUc (Subgroup.le_normalizer hs) hu
  have hsimple : IsSimpleGroup ↥L := by
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by simp)
    exact eL.isSimpleGroup
  set σ := restRep ρ U L hLU with hσ
  have hker : ∀ x : ↥L, x ∈ σ.ker ↔ ∀ u ∈ U, ρ x u = u := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx u hu
      have := congrArg (fun f : Module.End (ZMod 2) ↥U => ((f ⟨u, hu⟩ : ↥U) : W)) hx
      simpa [hσ, restRep_apply_coe] using this
    · intro hx
      ext ⟨u, hu⟩
      simp [hσ, restRep_apply_coe, hx u hu]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σ.ker with hb | ht
  · have hm : (⟨l₁, hl₁⟩ : ↥L)⁻¹ * ⟨l₂, hl₂⟩ ∈ σ.ker := by
      rw [hker]
      intro u hu
      show ρ (l₁⁻¹ * l₂) u = u
      rw [map_mul, Module.End.mul_apply, ← h u hu, ← Module.End.mul_apply, ← map_mul]
      simp
    rw [hb, Subgroup.mem_bot, inv_mul_eq_one] at hm
    exact congrArg Subtype.val hm
  · exfalso
    apply hU0
    have hall : ∀ x : ↥L, ∀ u ∈ U, ρ x u = u := fun x u hu => (hker x).1 (by rw [ht]; trivial) u hu
    rw [← hUUL, eq_bot_iff, commOn, Submodule.span_le]
    rintro _ ⟨a, ha, u, hu, rfl⟩
    simp [hall ⟨a, ha⟩ u hu]

include hUc eL hUUL hU0 in
theorem exists_theta (hSA : ∀ γ ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ u ∈ U, ρ γ u = ρ l u)
    (S : Subgroup G) (hS : S ≤ Subgroup.normalizer (L : Set G)) :
    ∃ θ : ↥S →* ↥L, ∀ (s : S), ∀ u ∈ U, ρ (θ s : G) u = ρ (s : G) u := by
  classical
  choose c hcL hc using fun s : ↥S => hSA (s : G) (hS s.2)
  have hfa := fun {l₁ l₂ : G} (h1 : l₁ ∈ L) (h2 : l₂ ∈ L) (h : ∀ u ∈ U, ρ l₁ u = ρ l₂ u) =>
    faithful_on ρ eL hUc hUUL hU0 h1 h2 h
  refine ⟨{ toFun := fun s => ⟨c s, hcL s⟩
            map_one' := ?_
            map_mul' := ?_ }, fun s u hu => (hc s u hu).symm⟩
  · apply Subtype.ext
    apply hfa (hcL 1) L.one_mem
    intro u hu
    rw [← hc 1 u hu]
    simp
  · intro a b
    apply Subtype.ext
    apply hfa (hcL (a * b)) (L.mul_mem (hcL a) (hcL b))
    intro u hu
    have hbu : ρ (b : G) u ∈ U := inv_normalizer ρ hUc (hS b.2) hu
    rw [← hc (a * b) u hu]
    simp only [Subgroup.coe_mul, map_mul, Module.End.mul_apply]
    rw [← hc b u hu]
    exact hc a _ hbu

include eL in
theorem center_trivial_of_alt7 {z : ↥L} (hz : ∀ l : ↥L, z * l = l * z) : z = 1 := by
  have h4 : 4 ≤ Nat.card (Fin 7) := by rw [Nat.card_fin]; norm_num
  have hc : eL z ∈ Subgroup.center (alternatingGroup (Fin 7)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg eL (hz (eL.symm y))
    simpa using this.symm
  rw [alternatingGroup.center_eq_bot h4, Subgroup.mem_bot] at hc
  exact eL.injective (by simpa using hc)

include hUc eL hUUL hU0 in
theorem theta_eq_one_iff (S : Subgroup G) (hS : S ≤ Subgroup.normalizer (L : Set G))
    (θ : ↥S →* ↥L) (hθ : ∀ (s : S), ∀ u ∈ U, ρ (θ s : G) u = ρ (s : G) u) (s : S) :
    θ s = 1 ↔ (s : G) ∈ Subgroup.centralizer (L : Set G) := by
  have hfa := fun {l₁ l₂ : G} (h1 : l₁ ∈ L) (h2 : l₂ ∈ L) (h : ∀ u ∈ U, ρ l₁ u = ρ l₂ u) =>
    faithful_on ρ eL hUc hUUL hU0 h1 h2 h
  have hsU : ∀ u ∈ U, ρ (s : G) u ∈ U := fun u hu => inv_normalizer ρ hUc (hS s.2) hu
  constructor
  · intro h1
    have hfix : ∀ u ∈ U, ρ (s : G) u = u := by
      intro u hu
      rw [← hθ s u hu, h1]; simp
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hs' : (s : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ (hS s.2)
    have hfix' : ∀ u ∈ U, ρ (s : G)⁻¹ u = u := by
      intro u hu
      have := hfix (ρ (s : G)⁻¹ u) (inv_normalizer ρ hUc hs' hu)
      rw [← Module.End.mul_apply, ← map_mul] at this
      simpa using this.symm
    have hsl : (s : G) * l * (s : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (hS s.2) l).1 hl
    have := hfa hsl hl (by
      intro u hu
      rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix' u hu]
      have hlu : ρ l u ∈ U := inv_normalizer ρ hUc (Subgroup.le_normalizer hl) hu
      exact hfix _ hlu)
    calc l * (s : G) = ((s : G) * l * (s : G)⁻¹) * (s : G) := by rw [this]
      _ = (s : G) * l := by group
  · intro hc
    rw [Subgroup.mem_centralizer_iff] at hc
    apply center_trivial_of_alt7 eL
    intro l'
    apply Subtype.ext
    apply hfa (L.mul_mem (θ s).2 l'.2) (L.mul_mem l'.2 (θ s).2)
    intro u hu
    have hl'u : ρ (l' : G) u ∈ U := inv_normalizer ρ hUc (Subgroup.le_normalizer l'.2) hu
    show ρ ((θ s : G) * (l' : G)) u = ρ ((l' : G) * (θ s : G)) u
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hθ s _ hl'u, hθ s u hu,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hc _ l'.2]

include hUc in
@[expose] noncomputable def repL : Representation (ZMod 2) ↥L ↥U :=
  restRep ρ U L (fun _ hs _ hu => inv_normalizer ρ hUc (Subgroup.le_normalizer hs) hu)

include hUc in
theorem repL_apply_coe (l : L) (u : U) : ((repL ρ hUc l u : U) : W) = ρ (l : G) u := rfl

include hUc eL hUUL hU0 in
theorem repL_injective : Function.Injective (repL ρ hUc) := by
  intro l₁ l₂ h
  apply Subtype.ext
  apply faithful_on ρ eL hUc hUUL hU0 l₁.2 l₂.2
  intro u hu
  have := congrArg (fun f : Module.End (ZMod 2) ↥U => ((f ⟨u, hu⟩ : ↥U) : W)) h
  simpa [repL_apply_coe] using this

include hUc eL hUUL hU0 in
theorem offender_in_L (HA : Alt7Hyp (alternatingGroup (Fin 7)))
    (hU16 : Nat.card U = 16)
    (hSA : ∀ γ ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ u ∈ U, ρ γ u = ρ l u)
    {B : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) (hLB : ⁅L, B⁆ = L)
    (hBc : ∀ a ∈ B, ∀ c ∈ B, a * c = c * a) (hB2 : ∀ b ∈ B, b ^ 2 = 1)
    (hbud : 2 ^ secCod ρ B ⊥ U * Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card B) :
    ∃ θ : ↥B →* ↥L, (∀ (b : B), ∀ u ∈ U, ρ (θ b : G) u = ρ (b : G) u) ∧ θ.range ≠ ⊥ ∧
      Nat.card θ.range = 4 ∧ Nat.card (fixSub (repL ρ hUc) θ.range) = 4 ∧
      (∀ g : ↥L, g ∈ Subgroup.normalizer (θ.range : Set ↥L) ↔
        ∀ v, v ∈ fixSub (repL ρ hUc) θ.range ↔ repL ρ hUc g v ∈ fixSub (repL ρ hUc) θ.range) ∧
      Nat.card (Subgroup.normalizer (θ.range : Set ↥L)) = 72 ∧
      ∃ E : Subgroup ↥L, E ≤ Subgroup.normalizer (θ.range : Set ↥L) ∧ Nat.card E = 9 := by
  classical
  obtain ⟨θ, hθ⟩ := exists_theta ρ eL hUc hUUL hU0 hSA B hBN
  have hker := theta_eq_one_iff ρ eL hUc hUUL hU0 B hBN θ hθ
  have hdim : finrank (ZMod 2) ↥U = 4 := by
    have h := natCard_submodule_zmod2 U
    rw [hU16] at h
    have h' : 2 ^ finrank (ZMod 2) ↥U = 2 ^ 4 := by rw [← h]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h'
  have H : Alt7Hyp ↥L := Alt7Hyp.of_mulEquiv eL HA
  have hRab : ∀ a ∈ θ.range, ∀ b ∈ θ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hBc _ x.2 _ y.2)
  have hR2 : ∀ a ∈ θ.range, a ^ 2 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (hB2 _ x.2)
    rw [this, map_one]
  have hR1 : θ.range ≠ ⊥ := by
    intro hbot
    have hall : ∀ b : B, θ b = 1 := fun b => by
      have : θ b ∈ θ.range := ⟨b, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    have hcent : B ≤ Subgroup.centralizer (L : Set G) := fun b hb =>
      (hker ⟨b, hb⟩).1 (hall ⟨b, hb⟩)
    have h1 : ⁅B, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hcent
    rw [Subgroup.commutator_comm, hLB] at h1
    have : Nontrivial ↥L := eL.toEquiv.nontrivial
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥L)
    apply hx
    have hxb : (x : G) ∈ (⊥ : Subgroup G) := by rw [← h1]; exact x.2
    exact Subtype.ext (Subgroup.mem_bot.1 hxb)
  have hρL : Function.Injective (repL ρ hUc) := repL_injective ρ eL hUc hUUL hU0
  have hfixcard : Nat.card (fixSub (repL ρ hUc) θ.range) = Nat.card (fixOn ρ B U) := by
    refine Nat.card_congr ⟨fun u => ⟨u.1.1, u.1.2, fun a ha => ?_⟩,
      fun w => ⟨⟨w.1, w.2.1⟩, fun r hr => ?_⟩, fun u => rfl, fun w => rfl⟩
    · have h1 := u.2 (θ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
      have h2 := congrArg Subtype.val h1
      rw [repL_apply_coe] at h2
      rw [← hθ ⟨a, ha⟩ _ u.1.2]
      exact h2
    · obtain ⟨b, rfl⟩ := hr
      apply Subtype.ext
      rw [repL_apply_coe]
      show ρ (θ b : G) w.1 = w.1
      rw [hθ b _ w.2.1]
      exact w.2.2 _ b.2
  have hrel : relFix ρ B ⊥ U = fixOn ρ B U := by
    ext w
    constructor
    · rintro ⟨hw, hb⟩
      exact ⟨hw, fun a ha => sub_eq_zero.1 (Submodule.mem_bot _ |>.1 (hb a ha))⟩
    · rintro ⟨hw, hb⟩
      exact ⟨hw, fun a ha => by rw [hb a ha, sub_self]; exact Submodule.zero_mem _⟩
  have hfin_le : finrank (ZMod 2) ↥(fixOn ρ B U) ≤ finrank (ZMod 2) ↥U :=
    Submodule.finrank_mono (inf_le_left)
  have hpow : 2 ^ secCod ρ B ⊥ U * Nat.card (fixOn ρ B U) = 16 := by
    rw [natCard_submodule_zmod2 (fixOn ρ B U), secCod, hrel, hdim, ← pow_add]
    have : 4 - finrank (ZMod 2) ↥(fixOn ρ B U) + finrank (ZMod 2) ↥(fixOn ρ B U) = 4 := by
      rw [hdim] at hfin_le; omega
    rw [this]; norm_num
  have hcard : Nat.card θ.ker * Nat.card θ.range = Nat.card B := by
    have := Subgroup.card_mul_index θ.ker
    rwa [Subgroup.index_ker] at this
  have hkercard : Nat.card θ.ker = Nat.card ↥(B ⊓ Subgroup.centralizer (L : Set G)) := by
    refine Nat.card_congr ⟨fun b => ⟨b.1.1, b.1.2, (hker b.1).1 b.2⟩,
      fun b => ⟨⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩, ?_⟩, fun b => rfl, fun b => rfl⟩
    exact (hker ⟨b.1, (Subgroup.mem_inf.1 b.2).1⟩).2 (Subgroup.mem_inf.1 b.2).2
  have hKpos : 0 < Nat.card θ.ker := Nat.card_pos
  have hle : 2 ^ secCod ρ B ⊥ U ≤ Nat.card θ.range := by
    have h1 : 2 ^ secCod ρ B ⊥ U * Nat.card θ.ker ≤ Nat.card θ.ker * Nat.card θ.range := by
      rw [hcard, hkercard]; exact hbud
    have h2 : 2 ^ secCod ρ B ⊥ U * Nat.card θ.ker ≤ Nat.card θ.range * Nat.card θ.ker := by
      rw [mul_comm (Nat.card θ.range)]; exact h1
    exact Nat.le_of_mul_le_mul_right h2 hKpos
  have hoff : Nat.card ↥U ≤ Nat.card θ.range * Nat.card (fixSub (repL ρ hUc) θ.range) := by
    rw [hfixcard, hU16, ← hpow]
    exact Nat.mul_le_mul_right _ hle
  have hdimU : finrank (ZMod 2) ↥U = 4 := hdim
  obtain ⟨h4, hl4, hnorm, h72, hE⟩ := alt7_four_offender (repL ρ hUc) hρL hdimU H hR1 hRab hR2 hoff
  exact ⟨θ, hθ, hR1, h4, hl4, hnorm, h72, hE⟩

include hUc eL hUUL hU0 in
theorem mem_of_theta_sylow
    (hSA : ∀ γ ∈ Subgroup.normalizer (L : Set G), ∃ l ∈ L, ∀ u ∈ U, ρ γ u = ρ l u)
    {T₁ : Subgroup G} (hT₁ : CFSG.QuasithinUnique.IsSylowTwoOf T₁ (Subgroup.normalizer (L : Set G)))
    {t l : G} (ht : t ∈ T₁) (hl : l ∈ L) (hlt : ∀ u ∈ U, ρ l u = ρ t u) : l ∈ T₁ := by
  classical
  set Γ := Subgroup.normalizer (L : Set G) with hΓ
  obtain ⟨θ, hθ⟩ := exists_theta ρ eL hUc hUUL hU0 hSA Γ le_rfl
  have htΓ : t ∈ Γ := hT₁.1 ht
  set D₂ : Subgroup G := ((T₁.subgroupOf Γ).map θ).map L.subtype with hD₂
  have hD₂L : D₂ ≤ L := by
    rintro _ ⟨_, _, rfl⟩
    exact (Subtype.property _)
  have hT2 : IsPGroup 2 (T₁.subgroupOf Γ) :=
    hT₁.2.1.comap_of_injective Γ.subtype Subtype.coe_injective
  have hD₂p : IsPGroup 2 D₂ := (hT2.map θ).map L.subtype
  have hLnormal : (L.subgroupOf Γ).Normal := Subgroup.normal_in_normalizer
  have hSylL : CFSG.QuasithinUnique.IsSylowTwoOf (T₁ ⊓ L) L :=
    CFSG.QuasithinUnique.RankOneRecog.isSylowTwoOf_inf_of_subnormal hT₁
      (Subgroup.le_normalizer) hLnormal.isSubnormal
  have hfa := fun {l₁ l₂ : G} (h1 : l₁ ∈ L) (h2 : l₂ ∈ L) (h : ∀ u ∈ U, ρ l₁ u = ρ l₂ u) =>
    faithful_on ρ eL hUc hUUL hU0 h1 h2 h
  have hle : T₁ ⊓ L ≤ D₂ := by
    intro x hx
    have hxΓ : x ∈ Γ := Subgroup.le_normalizer hx.2
    have hθx : (θ ⟨x, hxΓ⟩ : G) = x :=
      hfa (θ ⟨x, hxΓ⟩).2 hx.2 (fun u hu => hθ ⟨x, hxΓ⟩ u hu)
    exact ⟨θ ⟨x, hxΓ⟩, ⟨⟨x, hxΓ⟩, Subgroup.mem_subgroupOf.2 hx.1, rfl⟩, hθx⟩
  have hD₂eq : D₂ = T₁ ⊓ L := hSylL.eq_of_le hle hD₂L hD₂p
  have htΓ' : (θ ⟨t, htΓ⟩ : G) = l :=
    hfa (θ ⟨t, htΓ⟩).2 hl (fun u hu => by rw [hθ ⟨t, htΓ⟩ u hu]; exact (hlt u hu).symm)
  have : l ∈ D₂ := ⟨θ ⟨t, htΓ⟩, ⟨⟨t, htΓ⟩, Subgroup.mem_subgroupOf.2 ht, rfl⟩, htΓ'⟩
  rw [hD₂eq] at this
  exact this.1

include hUc eL hUUL hU0 in
theorem fixing_le_of_two_group (H : Alt7Hyp ↥L) (hU16 : Nat.card U = 16)
    (hfix0 : fixOn ρ L U = ⊥)
    {D R : Subgroup ↥L} (hD : IsPGroup 2 D) (hRD : R ≤ D) (hR4 : Nat.card R = 4)
    (hℓ4 : Nat.card (fixSub (repL ρ hUc) R) = 4)
    {l : ↥L} (hlD : l ∈ D) (hl : ∀ v ∈ fixSub (repL ρ hUc) R, repL ρ hUc l v = v) : l ∈ R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hDP⟩ := hD.exists_le_sylow
  set ℓ := fixSub (repL ρ hUc) R with hℓ
  let pst : Subgroup ↥L :=
    { carrier := {x | ∀ v ∈ ℓ, repL ρ hUc x v = v}
      mul_mem' := by
        intro a b ha hb v hv
        rw [map_mul, Module.End.mul_apply, hb v hv, ha v hv]
      one_mem' := fun v _ => by simp
      inv_mem' := by
        intro a ha v hv
        calc repL ρ hUc a⁻¹ v = repL ρ hUc a⁻¹ (repL ρ hUc a v) := by rw [ha v hv]
          _ = v := by rw [← Module.End.mul_apply, ← map_mul]; simp }
  have hRpst : R ≤ pst := fun r hr v hv => hv r hr
  set C : Subgroup ↥L := (P : Subgroup ↥L) ⊓ pst with hC
  have hRC : R ≤ C := le_inf (hRD.trans hDP) hRpst
  have hP8 : Nat.card (P : Subgroup ↥L) = 8 := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hidx := Subgroup.card_mul_index (P : Subgroup ↥L)
    have hodd : ¬ 2 ∣ (P : Subgroup ↥L).index := P.not_dvd_index
    rw [H.card_G, hn] at hidx
    have hn3 : n ≤ 3 := by
      by_contra hc
      push Not at hc
      have h16 : 2 ^ 4 ∣ 2 ^ n := pow_dvd_pow 2 hc
      have : 2 ^ 4 ∣ 2520 := h16.trans ⟨_, hidx.symm⟩
      omega
    interval_cases n <;> omega
  have hC8 : Nat.card C ∣ 8 := hP8 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hC4 : 4 ≤ Nat.card C := hR4 ▸ Subgroup.card_le_of_le hRC
  have hCne : Nat.card C = 4 := by
    by_contra hne
    have h8 : Nat.card C = 8 := by
      have : Nat.card C ≤ 8 := Nat.le_of_dvd (by norm_num) hC8
      have : Nat.card C = 5 ∨ Nat.card C = 6 ∨ Nat.card C = 7 ∨ Nat.card C = 8 := by omega
      rcases this with h | h | h | h <;> first | exact h | (exfalso; rw [h] at hC8; omega)
    have hPC : (P : Subgroup ↥L) = C :=
      (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, hP8])).symm
    have hPfix : ∀ p ∈ (P : Subgroup ↥L), ∀ v ∈ ℓ, repL ρ hUc p v = v := fun p hp v hv => by
      have : p ∈ C := by rw [← hPC]; exact hp
      exact this.2 v hv
    letI : MulAction (alternatingGroup (Fin 7)) ↥U :=
      MulAction.compHom ↥U ((repL ρ hUc).comp eL.symm.toMonoidHom)
    have hsmul : ∀ (g : alternatingGroup (Fin 7)) (u : ↥U), g • u = repL ρ hUc (eL.symm g) u :=
      fun g u => rfl
    have hhfin : Fintype ↥ℓ := Fintype.ofFinite _
    have h3 : 1 < (Finset.univ.erase (0 : ↥ℓ)).card := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hℓ4]
      norm_num
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.1 h3
    have ha0 : a ≠ 0 := Finset.ne_of_mem_erase ha
    have hb0 : b ≠ 0 := Finset.ne_of_mem_erase hb
    have hS2 : IsPGroup 2 ((P : Subgroup ↥L).map eL.toMonoidHom) := P.isPGroup'.map _
    have hSodd : ¬ 2 ∣ ((P : Subgroup ↥L).map eL.toMonoidHom).index := by
      rw [Subgroup.index_map_of_bijective eL.bijective]; exact P.not_dvd_index
    refine hab (Subtype.ext (CFSG.AGLEmbeddingD2.GN.eq_of_fixed_of_card_sixteen
      (X := ↥U) (by rw [← hU16]) 0 (fun g => by rw [hsmul]; exact map_zero _) ?_ hS2 hSodd
      (u₁ := a.1) (u₂ := b.1) ?_ ?_ ?_ ?_))
    · intro x hx
      by_contra hx0
      have hxfix : x.1 ∈ fixOn ρ L U := by
        refine ⟨x.2, fun l hl => ?_⟩
        have := hx (eL ⟨l, hl⟩)
        rw [hsmul, MulEquiv.symm_apply_apply] at this
        have h2 := congrArg Subtype.val this
        rwa [repL_apply_coe] at h2
      rw [hfix0, Submodule.mem_bot] at hxfix
      exact hx0 (Subtype.ext hxfix)
    · intro h; apply ha0; exact Subtype.ext h
    · intro h; apply hb0; exact Subtype.ext h
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := hs
      rw [hsmul]
      simpa using hPfix p hp a.1 a.2
    · intro s hs
      obtain ⟨p, hp, rfl⟩ := hs
      rw [hsmul]
      simpa using hPfix p hp b.1 b.2
  have hCR : R = C := Subgroup.eq_of_le_of_card_ge hRC (by rw [hR4, hCne])
  have : l ∈ C := ⟨hDP hlD, hl⟩
  rw [← hCR] at this
  exact this

include hUc eL hUUL hU0 in
theorem centralizes_of_trivial {c : G} (hc : c ∈ Subgroup.normalizer (L : Set G))
    (hfix : ∀ u ∈ U, ρ c u = u) : c ∈ Subgroup.centralizer (L : Set G) := by
  have hfa := fun {l₁ l₂ : G} (h1 : l₁ ∈ L) (h2 : l₂ ∈ L) (h : ∀ u ∈ U, ρ l₁ u = ρ l₂ u) =>
    faithful_on ρ eL hUc hUUL hU0 h1 h2 h
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hs' : c⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hc
  have hfix' : ∀ u ∈ U, ρ c⁻¹ u = u := by
    intro u hu
    have := hfix (ρ c⁻¹ u) (inv_normalizer ρ hUc hs' hu)
    rw [← Module.End.mul_apply, ← map_mul] at this
    simpa using this.symm
  have hsl : c * l * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hc l).1 hl
  have := hfa hsl hl (by
    intro u hu
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hfix' u hu]
    have hlu : ρ l u ∈ U := inv_normalizer ρ hUc (Subgroup.le_normalizer hl) hu
    exact hfix _ hlu)
  calc l * c = (c * l * c⁻¹) * c := by rw [this]
    _ = c * l := by group

end Basic

end CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
