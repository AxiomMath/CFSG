module

public import CFSG.CGT.Foote82.SetupLayer
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbPerfect
import CFSG.Quasithin.EmptyFaithful.SzN31Basic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.CGT.Foote82

open CFSG.Open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

private instance instFiniteGLVProp35 : Finite (GLV V) :=
  Finite.of_injective (fun f : GLV V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

private theorem commSpace_commSpace_of_perfect' {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    {X : Submodule (ZMod 2) V} (hX : Invariant L X) :
    commSpace L (commSpace L X) = commSpace L X := by
  have hconj : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L := fun k' hk' k hk =>
    L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')
  refine le_antisymm (commSpace_le_of_invariant (invariant_commSpace hconj hX)) ?_
  set M : Submodule (ZMod 2) V := commSpace L (commSpace L X) with hM
  let K : Subgroup (GLV V) :=
    { carrier := {k | k ∈ L ∧ ∀ v ∈ X, k v - v ∈ M}
      mul_mem' := fun {a b} ha hb => by
        refine ⟨L.mul_mem ha.1 hb.1, fun v hv => ?_⟩
        have h := M.add_mem (ha.2 (b v) (hX b hb.1 v hv)) (hb.2 v hv)
        rwa [sub_add_sub_cancel] at h
      one_mem' := ⟨L.one_mem, fun v _ => by simp⟩
      inv_mem' := fun {a} ha => by
        refine ⟨L.inv_mem ha.1, fun v hv => ?_⟩
        have h := M.neg_mem (ha.2 (a⁻¹ v) (hX a⁻¹ (L.inv_mem ha.1) v hv))
        simpa using h }
  have hcomm : ⁅L, L⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨L.mul_mem (L.mul_mem (L.mul_mem hg hh) (L.inv_mem hg)) (L.inv_mem hh),
      fun v hv => ?_⟩
    have key : ∀ u ∈ X, (g * h * g⁻¹ * h⁻¹) (h (g u)) - h (g u) ∈ M := by
      intro u hu
      have e1 : (g * h * g⁻¹ * h⁻¹) (h (g u)) = g (h u) := by simp
      have e2 : g (h u) - h (g u) = (g (h u - u) - (h u - u)) - (h (g u - u) - (g u - u)) := by
        simp only [map_sub]
        abel
      rw [e1, e2]
      exact M.sub_mem (sub_mem_commSpace hg (sub_mem_commSpace hh hu))
        (sub_mem_commSpace hh (sub_mem_commSpace hg hu))
    have hu : g⁻¹ (h⁻¹ v) ∈ X := hX g⁻¹ (L.inv_mem hg) _ (hX h⁻¹ (L.inv_mem hh) v hv)
    have e : h (g (g⁻¹ (h⁻¹ v))) = v := by simp
    have := key _ hu
    rw [e] at this
    exact this
  rw [hperf] at hcomm
  exact commSpace_le_iff.2 fun l hl v hv => (hcomm hl).2 v hv

private theorem trivial_of_commSpace_le_fixedSpace' {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    {X : Submodule (ZMod 2) V} (hX : Invariant L X) (h : commSpace L X ≤ fixedSpace L) :
    ∀ l ∈ L, ∀ x ∈ X, l x = x := by
  have h0 : commSpace L (commSpace L X) = ⊥ :=
    commSpace_eq_bot_iff.2 fun l hl w hw => h hw l hl
  rw [commSpace_commSpace_of_perfect' hperf hX] at h0
  exact commSpace_eq_bot_iff.1 h0

theorem trivial_or_commSpace_le {L : Subgroup (GLV V)} (hperf : ⁅L, L⁆ = L)
    (hirr : HasIrrTildeV L) {U : Submodule (ZMod 2) V} (hU : Invariant L U) :
    (∀ l ∈ L, ∀ u ∈ U, l u = u) ∨ commSpace L ⊤ ≤ U := by
  have hconj : ∀ k' ∈ L, ∀ k ∈ L, k' * k * k'⁻¹ ∈ L := fun k' hk' k hk =>
    L.mul_mem (L.mul_mem hk' hk) (L.inv_mem hk')
  obtain ⟨-, hmin⟩ : IrrSec L (fixedSpace L ⊓ commSpace L ⊤) (commSpace L ⊤) := hirr
  have hAinv : Invariant L (commSpace L ⊤) := invariant_commSpace hconj (invariant_top L)
  have hCinv : Invariant L (fixedSpace L ⊓ commSpace L ⊤) := fun l hl u hu => by
    rw [hu.1 l hl]
    exact hu
  have hJinv : Invariant L (U ⊓ commSpace L ⊤ ⊔ fixedSpace L ⊓ commSpace L ⊤) :=
    (hU.inf hAinv).sup hCinv
  rcases hmin _ hJinv le_sup_right (sup_le inf_le_right inf_le_right) with hJ | hJ
  ·
    left
    refine trivial_of_commSpace_le_fixedSpace' hperf hU fun w hw => ?_
    have hwJ : w ∈ U ⊓ commSpace L ⊤ ⊔ fixedSpace L ⊓ commSpace L ⊤ :=
      Submodule.mem_sup_left ⟨commSpace_le_of_invariant hU hw, commSpace_mono le_rfl le_top hw⟩
    rw [hJ] at hwJ
    exact hwJ.1
  ·
    right
    rw [← commSpace_commSpace_top_of_perfect hperf]
    refine commSpace_le_iff.2 fun l hl a ha => ?_
    have haJ : a ∈ U ⊓ commSpace L ⊤ ⊔ fixedSpace L ⊓ commSpace L ⊤ := by
      rw [hJ]
      exact ha
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 haJ
    have e : l (u + c) - (u + c) = l u - u := by
      rw [map_add, hc.1 l hl]
      abel
    rw [e]
    exact U.sub_mem (hU l hl u hu.1) hu.1

private theorem conj_mem_layerIn {G : Subgroup (GLV V)} {g : GLV V} (hg : g ∈ G) {e : GLV V}
    (he : e ∈ layerIn G) : g * e * g⁻¹ ∈ layerIn G := by
  have : (CFSG.layer ↥G).Characteristic := CFSG.LocalCores.layer_characteristic
  obtain ⟨e₀, he₀, rfl⟩ := he
  exact ⟨⟨g, hg⟩ * e₀ * ⟨g, hg⟩⁻¹, Subgroup.Normal.conj_mem inferInstance e₀ he₀ ⟨g, hg⟩,
    by simp⟩

private theorem layerIn_perfect (G : Subgroup (GLV V)) : ⁅layerIn G, layerIn G⁆ = layerIn G := by
  rw [← Subgroup.map_commutator, CFSG.LocalCores.layer_perfect]

private theorem Setup6.perfect {G S L : Subgroup (GLV V)} (h : Setup6 G S L) : ⁅L, L⁆ = L :=
  Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 h.component.2.2.1)

private theorem Setup6.commSpace_ne_bot {G S L : Subgroup (GLV V)} (h : Setup6 G S L) :
    commSpace L ⊤ ≠ ⊥ :=
  ne_bot_of_gt h.irrTilde.1

private theorem commSpace_closure_le {s : Set (GLV V)} {U : Submodule (ZMod 2) V}
    (h : ∀ x ∈ s, ∀ v, x v - v ∈ U) : commSpace (Subgroup.closure s) ⊤ ≤ U := by
  let K : Subgroup (GLV V) :=
    { carrier := {k | ∀ v, k v - v ∈ U}
      mul_mem' := fun {a b} ha hb v => by
        have h := U.add_mem (ha (b v)) (hb v)
        rwa [sub_add_sub_cancel] at h
      one_mem' := fun v => by simp
      inv_mem' := fun {a} ha v => by
        have h := U.neg_mem (ha (a⁻¹ v))
        simpa using h }
  have hle : Subgroup.closure s ≤ K := (Subgroup.closure_le K).2 h
  exact commSpace_le_iff.2 fun k hk v _ => hle hk v

private theorem fixes_of_mem_closure {s : Set (GLV V)} {U : Submodule (ZMod 2) V}
    (h : ∀ x ∈ s, ∀ u ∈ U, x u = u) : ∀ g ∈ Subgroup.closure s, ∀ u ∈ U, g u = u := by
  have hle : Subgroup.closure s ≤ centralizerOn ⊤ U :=
    (Subgroup.closure_le _).2 fun x hx => ⟨Subgroup.mem_top x, h x hx⟩
  exact fun g hg u hu => (hle hg).2 u hu

theorem Setup6Irr.eq_bot_of_isPGroup {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L)
    {P : Subgroup (GLV V)} (hPG : P ≤ G) (hP : IsPGroup 2 P)
    (hN : G ≤ Subgroup.normalizer (P : Set (GLV V))) : P = ⊥ :=
  CFSG.Quasithin.SzN31.eq_bot_of_isPGroup_normal h.irr
    (fun γ hγ n hn => (Subgroup.mem_normalizer_iff.1 (hN hγ) n).1 hn) hP

theorem Setup6Irr.normalClosure_layerIn {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L) :
    normalClosure (layerIn G) L = layerIn G := by
  have hLE : L ≤ layerIn G := h.toSetup6.le_layerIn
  have hLC : L ≤ Subgroup.centralizer (S : Set (GLV V)) := h.component.1.trans inf_le_right
  have hEN : layerIn G ≤ Subgroup.normalizer (normalClosure (layerIn G) L : Set (GLV V)) :=
    Subgroup.le_normalizer_iff.2 fun e he x hx => normalClosure_conj he hx
  have hSN : S ≤ Subgroup.normalizer (normalClosure (layerIn G) L : Set (GLV V)) := by
    refine Subgroup.le_normalizer_closure_iff.2 ?_
    rintro s hs _ ⟨γ, hγ, l, hl, rfl⟩
    apply Subgroup.subset_closure
    have hsl : s * l * s⁻¹ = l := by
      rw [Subgroup.mem_centralizer_iff.1 (hLC hl) s hs, mul_inv_cancel_right]
    refine ⟨s * γ * s⁻¹, conj_mem_layerIn (h.S_le hs) hγ, l, hl, ?_⟩
    calc s * (γ * l * γ⁻¹) * s⁻¹ = s * γ * s⁻¹ * (s * l * s⁻¹) * (s * γ * s⁻¹)⁻¹ := by group
      _ = s * γ * s⁻¹ * l * (s * γ * s⁻¹)⁻¹ := by rw [hsl]
  have hGN : G ≤ Subgroup.normalizer (normalClosure (layerIn G) L : Set (GLV V)) :=
    h.eq_layerIn_sup.le.trans (sup_le hEN hSN)
  have hNC : normalClosure G L ≤ normalClosure (layerIn G) L := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨g, hg, l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hGN hg) l).1 (le_normalClosure _ _ hl)
  have hGle : G ≤ normalClosure (layerIn G) L ⊔ S := h.gen.le.trans (sup_le_sup_right hNC S)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_antisymm (normalClosure_le hLE)
    (CFSG.AGLEmbeddingD2.Tits.GN516.Perf.le_of_perfect_of_le_sup (layerIn_perfect G)
      ((Subgroup.map_subtype_le _).trans hGle) hSN h.isPGroup)

private theorem Setup6Irr.isIrr_layerIn {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L) :
    IsIrr (layerIn G) ⊤ := by
  have hLE : L ≤ layerIn G := h.toSetup6.le_layerIn
  have hnE : ∀ g ∈ G, ∀ e ∈ layerIn G, g * e * g⁻¹ ∈ layerIn G := fun g hg e he =>
    conj_mem_layerIn hg he
  have hLne := h.toSetup6.commSpace_ne_bot
  have hEcl := h.normalClosure_layerIn
  have hfix : fixedSpace (layerIn G) = ⊥ := by
    rcases h.irr.eq_bot_or_eq (invariant_fixedSpace hnE) le_top with h0 | h0
    · exact h0
    · exfalso
      apply hLne
      rw [fixedSpace_eq_top_iff] at h0
      rw [commSpace_eq_bot_iff]
      intro l hl u _
      rw [h0 l (hLE hl)]
      rfl
  have hcomm : commSpace (layerIn G) ⊤ = ⊤ := by
    rcases h.irr.eq_bot_or_eq (invariant_commSpace hnE (invariant_top G)) le_top with h0 | h0
    · exfalso
      apply hLne
      rw [commSpace_eq_bot_iff] at h0 ⊢
      exact fun l hl u hu => h0 l (hLE hl) u hu
    · exact h0
  refine ⟨invariant_top _, h.irr.2.1, fun U hU _ _ => ?_⟩
  rcases trivial_or_commSpace_le h.toSetup6.perfect h.irrTilde (hU.mono hLE) with htriv | hle
  ·
    left
    have hEU : ∀ e ∈ normalClosure (layerIn G) L, ∀ u ∈ U, e u = u := by
      refine fixes_of_mem_closure ?_
      rintro _ ⟨γ, hγ, l, hl, rfl⟩ u hu
      have h1 : γ⁻¹ u ∈ U := hU γ⁻¹ ((layerIn G).inv_mem hγ) u hu
      have e : (γ * l * γ⁻¹) u = γ (l (γ⁻¹ u)) := rfl
      rw [e, htriv l hl _ h1]
      simp
    rw [hEcl] at hEU
    rw [eq_bot_iff, ← hfix]
    intro u hu e he
    exact hEU e he u hu
  ·
    right
    rw [eq_top_iff, ← hcomm, ← hEcl]
    refine commSpace_closure_le ?_
    rintro _ ⟨γ, hγ, l, hl, rfl⟩ v
    have h1 : l (γ⁻¹ v) - γ⁻¹ v ∈ U := hle (sub_mem_commSpace hl Submodule.mem_top)
    have e : (γ * l * γ⁻¹) v - v = γ (l (γ⁻¹ v) - γ⁻¹ v) := by simp [map_sub]
    rw [e]
    exact hU γ hγ _ h1

theorem Setup6Irr.isIrr_of_layerIn_le {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L)
    {X : Subgroup (GLV V)} (hX : layerIn G ≤ X) : IsIrr X ⊤ := by
  have hE := h.isIrr_layerIn
  exact ⟨invariant_top X, hE.2.1, fun J hJ h0 h1 => hE.2.2 J (hJ.mono hX) h0 h1⟩

theorem Setup6Irr.odd_card_centralizer_layerIn {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L) :
    Odd (Nat.card ↥(G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hodd)
  have hy2 : orderOf (y : GLV V) = 2 := by rw [Subgroup.orderOf_coe, hy]
  have hyC : (y : GLV V) ∈ Subgroup.centralizer (layerIn G : Set (GLV V)) := y.2.2
  have hLE : L ≤ layerIn G := h.toSetup6.le_layerIn
  have hinv : Invariant (layerIn G) (commSpace (Subgroup.zpowers (y : GLV V)) ⊤) := by
    refine invariant_commSpace (fun e he k hk => ?_) (invariant_top _)
    have hc : Commute e (y : GLV V) := Subgroup.mem_centralizer_iff.1 hyC e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [(hc.zpow_right n).eq, mul_inv_cancel_right]
    exact hk
  have hP : IsPGroup 2 (Subgroup.zpowers (y : GLV V)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy2, pow_one])
  have h61 := lemma61 h.toSetup6.perfect h.irrTilde
    (fun l hl => Subgroup.mem_centralizer_iff.1 hyC l (hLE hl)) hP
  rcases h.isIrr_layerIn.eq_bot_or_eq hinv le_top with h0 | h0
  ·
    rw [commSpace_eq_bot_iff] at h0
    have hy1 : (y : GLV V) = 1 :=
      LinearEquiv.ext fun v => h0 _ (Subgroup.mem_zpowers _) v Submodule.mem_top
    rw [hy1, orderOf_one] at hy2
    exact absurd hy2 (by norm_num)
  ·
    apply h.toSetup6.commSpace_ne_bot
    rw [commSpace_eq_bot_iff]
    intro l hl u _
    refine h61.1 l hl u ?_
    rw [h0]
    exact Submodule.mem_top

theorem Setup6Irr.odd_card_center {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L) :
    Odd (Nat.card ↥(G ⊓ Subgroup.centralizer (G : Set (GLV V)))) := by
  have hle : G ⊓ Subgroup.centralizer (G : Set (GLV V)) ≤
      G ⊓ Subgroup.centralizer (layerIn G : Set (GLV V)) :=
    inf_le_inf_left G (Subgroup.centralizer_le (Subgroup.map_subtype_le _))
  exact h.odd_card_centralizer_layerIn.of_dvd_nat (Subgroup.card_dvd_of_le hle)

private theorem Setup6Irr.eq_bot_of_le_sup {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L)
    (hG : G ≤ L ⊔ S) : S = ⊥ := by
  refine h.eq_bot_of_isPGroup h.S_le h.isPGroup (hG.trans (sup_le ?_ Subgroup.le_normalizer))
  exact (h.component.1.trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _)

theorem Setup6Irr.eq_iff_eq_bot {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L) :
    L = G ↔ S = ⊥ := by
  constructor
  · intro hLG
    refine h.eq_bot_of_le_sup ?_
    rw [← hLG]
    exact le_sup_left
  · intro hS
    have hLG : L ≤ G := h.component.1.trans inf_le_left
    have hcent : G ⊓ Subgroup.centralizer (S : Set (GLV V)) = G := by
      refine inf_eq_left.2 fun g _ => Subgroup.mem_centralizer_iff.2 fun x hx => ?_
      rw [hS, Subgroup.coe_bot, Set.mem_singleton_iff] at hx
      rw [hx, one_mul, mul_one]
    have hcomp : CFSG.Open.IsComponentOf L G := hcent ▸ h.component
    have hcomp' : CFSG.IsComponent (L.subgroupOf G) :=
      (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf hLG).1
        (CFSG.Assembly.isComponentOf_iff_open.2 hcomp)
    have hnorm := CFSG.LocalCores.layer_le_normalizer hcomp'
    have hGE : G = layerIn G := by
      have := h.eq_layerIn_sup
      rwa [hS, sup_bot_eq] at this
    have hconj : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L := by
      intro g hg l hl
      obtain ⟨g₀, hg₀, rfl⟩ := hGE.le hg
      exact Subgroup.mem_subgroupOf.1
        ((Subgroup.mem_normalizer_iff.1 (hnorm hg₀) ⟨l, hLG hl⟩).1 (Subgroup.mem_subgroupOf.2 hl))
    refine le_antisymm hLG ?_
    calc G = normalClosure G L ⊔ S := h.gen
      _ = normalClosure G L := by rw [hS, sup_bot_eq]
      _ ≤ L := (Subgroup.closure_le L).2 (by
          rintro _ ⟨g, hg, l, hl, rfl⟩
          exact hconj g hg l hl)

theorem Setup6Irr.layerIn_ne_of_ne_bot {G S L : Subgroup (GLV V)} (h : Setup6Irr G S L)
    (hS : S ≠ ⊥) : layerIn G ≠ L := by
  intro hEL
  apply hS
  refine h.eq_bot_of_le_sup ?_
  have := h.eq_layerIn_sup
  rw [hEL] at this
  exact this.le

end CFSG.CGT.Foote82
