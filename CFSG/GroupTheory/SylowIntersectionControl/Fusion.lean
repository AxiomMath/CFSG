module

public import CFSG.GroupTheory.SylowIntersectionControl.Defs
public import CFSG.GroupTheory.FusionFamilyControl
import CFSG.GroupTheory.SylowIntersectionControl.Basic
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G] {p : ℕ}

private lemma map_conj_eq_self_of_mem {K : Subgroup G} {g : G} (hg : g ∈ K) :
    K.map (MulAut.conj g).toMonoidHom = K :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hg)

private lemma map_conj_map_conj {R : Subgroup G} {a b : G} :
    (R.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      R.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private lemma map_conj_one (S : Subgroup G) :
    S.map (MulAut.conj (1 : G)).toMonoidHom = S := by
  simp [MulAut.one_def]

private lemma mem_map_conj_inv_iff {S : Subgroup G} {a g : G} :
    a ∈ S.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * a * g⁻¹ ∈ S := by
  have h : (MulAut.conj g⁻¹) (g * a * g⁻¹) = a := by
    simp
    group
  conv_lhs => rw [← h]
  exact Subgroup.mem_map_iff_mem (f := (MulAut.conj g⁻¹).toMonoidHom)
    (MulAut.conj g⁻¹).injective

private lemma isSylowOf_map_conj_of_mem [Finite G] [Fact p.Prime] {K S : Subgroup G}
    (hS : IsSylowOf p S K) {g : G} (hg : g ∈ K) :
    IsSylowOf p (S.map (MulAut.conj g).toMonoidHom) K := by
  have h := isSylowOf_map_conj hS g
  rwa [map_conj_eq_self_of_mem (K := K) hg] at h

private lemma sylowMembers_map_conj [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {K : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K) {g : G} (hg : g ∈ K) {R X : Subgroup G}
    (hX : X ∈ sylowMembers p 𝓕 R) :
    X.map (MulAut.conj g).toMonoidHom ∈
      sylowMembers p 𝓕 (R.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hX𝓕, hXsys⟩ := hX
  refine ⟨h𝓕.2 X hX𝓕 g hg, ?_⟩
  have h := isSylowOf_map_conj hXsys g
  rwa [Subgroup.map_inf_eq R X (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective] at h

private lemma fusionChainStep_mem_conj [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {K S : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K) {A : Set G}
    {u v : G} (hstep : FusionChainStep p 𝓕 S A u v) (huK : u ∈ K) :
    v ∈ K ∧ ∀ a ∈ A, v * a * v⁻¹ ∈ S := by
  obtain ⟨Y, hY, z, hz, hv, hcond⟩ := hstep
  subst v
  exact ⟨K.mul_mem (h𝓕.1 Y hY.1 hz) huK, fun a ha => (hcond a ha).1⟩

private lemma sylowConjLink_of_fusionChainStep [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K S T : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K)
    (hS : IsSylowOf p S K) {u v : G}
    (hstep : FusionChainStep p 𝓕 S ((S ⊓ T : Subgroup G) : Set G) u v)
    (huK : u ∈ K) (hinv : ∀ a ∈ (S ⊓ T : Subgroup G), u * a * u⁻¹ ∈ S) :
    SylowConjLink p 𝓕 K (S ⊓ T)
      (S.map (MulAut.conj u⁻¹).toMonoidHom)
      (S.map (MulAut.conj v⁻¹).toMonoidHom) := by
  obtain ⟨Y, hY, z, hz, hv, hcond⟩ := hstep
  have hzK : z ∈ K := h𝓕.1 Y hY.1 hz
  have hvK : v ∈ K := by rw [hv]; exact K.mul_mem hzK huK
  set X : Subgroup G := Y.map (MulAut.conj v⁻¹).toMonoidHom with hXdef
  have hXeq : X = Y.map (MulAut.conj u⁻¹).toMonoidHom := by
    rw [hXdef, hv, show (z * u)⁻¹ = u⁻¹ * z⁻¹ by group, ← map_conj_map_conj]
    rw [map_conj_eq_self_of_mem (Y.inv_mem hz)]
  have hSylU : IsSylowOf p (S.map (MulAut.conj u⁻¹).toMonoidHom) K :=
    isSylowOf_map_conj_of_mem hS (K.inv_mem huK)
  have hSylV : IsSylowOf p (S.map (MulAut.conj v⁻¹).toMonoidHom) K :=
    isSylowOf_map_conj_of_mem hS (K.inv_mem hvK)
  have hXmemU : X ∈ sylowMembers p 𝓕 (S.map (MulAut.conj u⁻¹).toMonoidHom) := by
    rw [hXeq]
    exact sylowMembers_map_conj h𝓕 (K.inv_mem huK) hY
  have hXmemV : X ∈ sylowMembers p 𝓕 (S.map (MulAut.conj v⁻¹).toMonoidHom) := by
    rw [hXdef]
    exact sylowMembers_map_conj h𝓕 (K.inv_mem hvK) hY
  have hDle : (S ⊓ T) ≤
      (S.map (MulAut.conj u⁻¹).toMonoidHom) ⊓
        (S.map (MulAut.conj v⁻¹).toMonoidHom) ⊓ X := by
    intro a ha
    have hva : v * a * v⁻¹ ∈ S ⊓ Y := hcond a ha
    have huaY : u * a * u⁻¹ ∈ Y := by
      have h : u * a * u⁻¹ = z⁻¹ * (v * a * v⁻¹) * z := by rw [hv]; group
      rw [h]
      exact Y.mul_mem (Y.mul_mem (Y.inv_mem hz) hva.2) hz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · exact mem_map_conj_inv_iff.mpr (hinv a ha)
    · exact mem_map_conj_inv_iff.mpr hva.1
    · rw [hXeq]
      exact mem_map_conj_inv_iff.mpr huaY
  set x : G := v⁻¹ * z⁻¹ * v with hxdef
  have hxX : x ∈ X := by
    rw [hXeq, hxdef]
    refine Subgroup.mem_map.mpr ⟨z⁻¹, Y.inv_mem hz, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hv]
    group
  have hright : S.map (MulAut.conj v⁻¹).toMonoidHom =
      (S.map (MulAut.conj u⁻¹).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
    rw [map_conj_map_conj]
    rw [show x * u⁻¹ = v⁻¹ by rw [hxdef, hv]; group]
  exact ⟨hSylU, hSylV, X, hXmemU, hXmemV, hDle, x, hxX, hright⟩

private lemma fusionChain_reflTransGen_sylowConjLink [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K S T : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K)
    (hS : IsSylowOf p S K) {w : G}
    (hchain : Relation.ReflTransGen
      (FusionChainStep p 𝓕 S ((S ⊓ T : Subgroup G) : Set G)) 1 w) :
    w ∈ K ∧ (∀ a ∈ (S ⊓ T : Subgroup G), w * a * w⁻¹ ∈ S) ∧
      Relation.ReflTransGen (SylowConjLink p 𝓕 K (S ⊓ T)) S
        (S.map (MulAut.conj w⁻¹).toMonoidHom) := by
  refine Relation.ReflTransGen.rec
    (motive := fun w _ => w ∈ K ∧
      (∀ a ∈ (S ⊓ T : Subgroup G), w * a * w⁻¹ ∈ S) ∧
        Relation.ReflTransGen (SylowConjLink p 𝓕 K (S ⊓ T)) S
          (S.map (MulAut.conj w⁻¹).toMonoidHom)) ?_ ?_ hchain
  · refine ⟨K.one_mem, ?_, ?_⟩
    · intro a ha
      simpa using ha.1
    · have h1 : S.map (MulAut.conj (1 : G)⁻¹).toMonoidHom = S := by
        rw [show (1 : G)⁻¹ = 1 by simp, map_conj_one]
      rw [h1]
  · intro b c hprev hstep ih
    obtain ⟨hbK, hinv, hlink⟩ := ih
    have hstep' := fusionChainStep_mem_conj h𝓕 hstep hbK
    have hlink' := sylowConjLink_of_fusionChainStep h𝓕 hS hstep hbK hinv
    exact ⟨hstep'.1, hstep'.2, Relation.ReflTransGen.tail hlink hlink'⟩

theorem exists_fusionChain_of_reflTransGen [Finite G] [Fact p.Prime] {𝓕 : Set (Subgroup G)}
    {K D S T : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K)
    (h : Relation.ReflTransGen (SylowConjLink p 𝓕 K D) S T) :
    ∃ g ∈ K, Relation.ReflTransGen (FusionChainStep p 𝓕 S (D : Set G)) 1 g ∧
      S = T.map (MulAut.conj g).toMonoidHom := by
  have hmain : ∃ g ∈ K,
      Relation.ReflTransGen (FusionChainStep p 𝓕 S (D : Set G)) 1 g ∧
        T.map (MulAut.conj g).toMonoidHom = S := by
    refine Relation.ReflTransGen.rec
      (motive := fun R _ => ∃ g ∈ K,
        Relation.ReflTransGen (FusionChainStep p 𝓕 S (D : Set G)) 1 g ∧
          R.map (MulAut.conj g).toMonoidHom = S) ?_ ?_ h
    · refine ⟨1, K.one_mem, Relation.ReflTransGen.refl, ?_⟩
      exact map_conj_one S
    · intro R R' hprev hlink ih
      obtain ⟨g, hgK, hgchain, hgmap⟩ := ih
      obtain ⟨hR, hR', X, hXmem, hXmem', hD, x, hxX, hXeq⟩ := hlink
      have hxK : x ∈ K := h𝓕.1 X hXmem.1 hxX
      set Y : Subgroup G := X.map (MulAut.conj g).toMonoidHom with hYdef
      have hYmem : Y ∈ sylowMembers p 𝓕 S := by
        have h := sylowMembers_map_conj h𝓕 hgK hXmem
        rw [← hYdef, hgmap] at h
        exact h
      have hzY : g * x⁻¹ * g⁻¹ ∈ Y := by
        rw [hYdef]
        exact Subgroup.mem_map.mpr ⟨x⁻¹, X.inv_mem hxX, by simp [MulAut.conj_apply]⟩
      have hstep : FusionChainStep p 𝓕 S (D : Set G) g (g * x⁻¹) := by
        refine ⟨Y, hYmem, g * x⁻¹ * g⁻¹, hzY, by group, ?_⟩
        intro a ha
        rw [hXeq] at hD
        obtain ⟨r, hrR, hrx⟩ := Subgroup.mem_map.mp (hD ha).1.2
        have hrX : r ∈ X := by
          have h : r = x⁻¹ * a * x := by rw [← hrx]; simp [MulAut.conj_apply]; group
          rw [h]
          exact X.mul_mem (X.mul_mem (X.inv_mem hxX) (hD ha).2) hxX
        have hgrS : g * r * g⁻¹ ∈ S := by
          rw [← hgmap]
          exact Subgroup.mem_map.mpr ⟨r, hrR, by simp [MulAut.conj_apply]⟩
        have hgrY : g * r * g⁻¹ ∈ Y := by
          rw [hYdef]
          exact Subgroup.mem_map.mpr ⟨r, hrX, by simp [MulAut.conj_apply]⟩
        have hkey : g * x⁻¹ * a * (g * x⁻¹)⁻¹ = g * r * g⁻¹ := by
          rw [← hrx]
          simp [MulAut.conj_apply]
          group
        rw [hkey]
        exact ⟨hgrS, hgrY⟩
      refine ⟨g * x⁻¹, K.mul_mem hgK (K.inv_mem hxK),
        Relation.ReflTransGen.tail hgchain hstep, ?_⟩
      rw [hXeq, map_conj_map_conj]
      rw [show (g * x⁻¹) * x = g by group, hgmap]
  obtain ⟨g, hgK, hgchain, hmap⟩ := hmain
  exact ⟨g, hgK, hgchain, hmap.symm⟩

private lemma stronglyControlsFusion_of_controlsSylowIntersections [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K)
    (hctrl : ControlsSylowIntersections p 𝓕 K) : StronglyControlsFusion p 𝓕 K := by
  intro S hS A hA hne k hk hkA
  set T : Subgroup G := S.map (MulAut.conj k⁻¹).toMonoidHom with hTdef
  have hT : IsSylowOf p T K := isSylowOf_map_conj_of_mem hS (K.inv_mem hk)
  have hAT : A ⊆ (S ⊓ T : Subgroup G) := by
    intro a ha
    exact ⟨hA ha, mem_map_conj_inv_iff.mpr (hkA a ha)⟩
  have hneBot : S ⊓ T ≠ ⊥ := by
    obtain ⟨a, haA, ha1⟩ := hne
    intro hbot
    have : a ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hAT haA
    exact ha1 (Subgroup.mem_bot.mp this)
  by_cases hST : S = T
  · have hkmap : S.map (MulAut.conj k⁻¹).toMonoidHom = S :=
      hTdef.symm.trans hST.symm
    have hkNS : k ∈ normalizer (S : Set G) := by
      have hkinv : k⁻¹ ∈ normalizer (S : Set G) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hkmap
      simpa using (normalizer (S : Set G)).inv_mem hkinv
    refine ⟨1, Relation.ReflTransGen.refl, ?_⟩
    exact ⟨by simpa using hk, by simpa using hkNS⟩
  · have hconj : ConjVia p 𝓕 K S T := hctrl S T hS hT hST hneBot
    obtain ⟨g, hgK, hgchain, hgmap⟩ := exists_fusionChain_of_reflTransGen h𝓕 hconj
    have hchainA : Relation.ReflTransGen (FusionChainStep p 𝓕 S A) 1 g :=
      (Relation.ReflTransGen.mono (p := FusionChainStep p 𝓕 S A) (fun _ _ hstep => by
        obtain ⟨Y, hY, z, hz, hv, hcond⟩ := hstep
        exact ⟨Y, hY, z, hz, hv, fun a ha => hcond a (hAT ha)⟩)) 1 g hgchain
    have hgk : g * k⁻¹ ∈ normalizer (S : Set G) := by
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      calc S.map (MulAut.conj (g * k⁻¹)).toMonoidHom
          = (S.map (MulAut.conj k⁻¹).toMonoidHom).map
              (MulAut.conj g).toMonoidHom := by
            rw [map_conj_map_conj]
        _ = T.map (MulAut.conj g).toMonoidHom := by rw [hTdef]
        _ = S := hgmap.symm
    have hkg : k * g⁻¹ ∈ normalizer (S : Set G) := by
      have := (normalizer (S : Set G)).inv_mem hgk
      simpa [mul_inv_rev] using this
    exact ⟨g, hchainA, ⟨K.mul_mem hk (K.inv_mem hgK), hkg⟩⟩

private lemma controlsSylowIntersections_of_stronglyControlsFusion [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K)
    (hstrong : StronglyControlsFusion p 𝓕 K) : ControlsSylowIntersections p 𝓕 K := by
  intro S T hS hT hST hneBot
  obtain ⟨k, hkK, hkconj⟩ := IsSylowOf.exists_mem_conj hT hS
  have hkST : S = T.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      exact ⟨k⁻¹ * x * k, (hkconj x).mp hx, by simp [MulAut.conj_apply]; group⟩
    · rintro ⟨y, hy, rfl⟩
      change k * y * k⁻¹ ∈ S
      exact (hkconj (k * y * k⁻¹)).mpr (by
        rw [show k⁻¹ * (k * y * k⁻¹) * k = y by group]
        exact hy)
  have hTmap : T = S.map (MulAut.conj k⁻¹).toMonoidHom := by
    have h := congrArg (fun R : Subgroup G =>
      R.map (MulAut.conj k⁻¹).toMonoidHom) hkST
    rw [map_conj_map_conj] at h
    rw [show k⁻¹ * k = 1 by group] at h
    rw [map_conj_one T] at h
    exact h.symm
  let A : Set G := (S ⊓ T : Subgroup G)
  have hAS : A ⊆ S := fun _ ha => ha.1
  have hne : ∃ a ∈ A, a ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one (S ⊓ T) with hbot | h
    · exact absurd hbot hneBot
    · exact h
  have hkA : ∀ a ∈ A, k * a * k⁻¹ ∈ S := by
    intro a ha
    have haT : a ∈ T := ha.2
    rw [hTmap] at haT
    exact mem_map_conj_inv_iff.mp haT
  obtain ⟨w, hchain, hwn⟩ := hstrong S hS A hAS hne k hkK hkA
  obtain ⟨hwK, hinv, hlink⟩ :=
    fusionChain_reflTransGen_sylowConjLink h𝓕 hS hchain
  have hwT : S.map (MulAut.conj w⁻¹).toMonoidHom = T := by
    have hw_eq : w⁻¹ = k⁻¹ * (k * w⁻¹) := by group
    have hmapn : S.map (MulAut.conj (k * w⁻¹)).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hwn.2
    calc S.map (MulAut.conj w⁻¹).toMonoidHom
        = S.map (MulAut.conj (k⁻¹ * (k * w⁻¹))).toMonoidHom :=
            congrArg (fun y => S.map (MulAut.conj y).toMonoidHom) hw_eq
      _ = (S.map (MulAut.conj (k * w⁻¹)).toMonoidHom).map
            (MulAut.conj k⁻¹).toMonoidHom := by
          rw [map_conj_map_conj]
      _ = S.map (MulAut.conj k⁻¹).toMonoidHom := by rw [hmapn]
      _ = T := by rw [hTmap]
  rwa [hwT] at hlink

theorem controlsSylowIntersections_iff_stronglyControlsFusion [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {K : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 K) :
    ControlsSylowIntersections p 𝓕 K ↔ StronglyControlsFusion p 𝓕 K :=
  ⟨stronglyControlsFusion_of_controlsSylowIntersections h𝓕,
    controlsSylowIntersections_of_stronglyControlsFusion h𝓕⟩

private lemma eqvGen_of_fusionChain_singleton {𝓕 : Set (Subgroup G)} {S : Subgroup G}
    {x : G} (hx : x ∈ S) {w : G}
    (hchain : Relation.ReflTransGen (FusionChainStep p 𝓕 S ({x} : Set G)) 1 w) :
    w * x * w⁻¹ ∈ S ∧
      Relation.EqvGen (FusionStep (insert (normalizer (S : Set G))
        (sylowMembers p 𝓕 S)) S) x (w * x * w⁻¹) := by
  let F : Set (Subgroup G) := insert (normalizer (S : Set G)) (sylowMembers p 𝓕 S)
  refine Relation.ReflTransGen.rec
    (motive := fun w _ => w * x * w⁻¹ ∈ S ∧
      Relation.EqvGen (FusionStep F S) x (w * x * w⁻¹)) ?_ ?_ hchain
  · refine ⟨by simpa using hx, ?_⟩
    simpa using Relation.EqvGen.refl (r := FusionStep F S) (x := x)
  · intro b c hprev hstep ih
    obtain ⟨hbS, hbeq⟩ := ih
    obtain ⟨Y, hY, z, hz, hc, hcond⟩ := hstep
    subst c
    have hcS : (z * b) * x * (z * b)⁻¹ ∈ S := (hcond x (by simp)).1
    have hstep' : FusionStep F S (b * x * b⁻¹) ((z * b) * x * (z * b)⁻¹) := by
      refine ⟨hbS, hcS, Y, ?_, z, hz, ?_⟩
      · exact Set.mem_insert_of_mem _ hY
      · group
    exact ⟨hcS, Relation.EqvGen.trans x (b * x * b⁻¹) ((z * b) * x * (z * b)⁻¹)
      hbeq (Relation.EqvGen.rel _ _ hstep')⟩

theorem StronglyControlsFusion.familyControlsFusion {𝓕 : Set (Subgroup G)} {S : Subgroup G}
    (h : StronglyControlsFusion p 𝓕 ⊤) (hS : IsSylowOf p S ⊤) :
    FamilyControlsFusion (insert (normalizer (S : Set G)) (sylowMembers p 𝓕 S)) S := by
  intro x y hxS hyS hxy
  by_cases hx1 : x = 1
  · subst x
    have hy1 : y = 1 := by
      obtain ⟨c, hc⟩ := isConj_iff.mp hxy
      rw [← hc]
      group
    subst y
    exact Relation.EqvGen.refl (x := (1 : G))
  · obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    have hA : ({x} : Set G) ⊆ S := by
      intro a ha
      rwa [Set.mem_singleton_iff.mp ha]
    have hne : ∃ a ∈ ({x} : Set G), a ≠ 1 := ⟨x, rfl, hx1⟩
    have hkA : ∀ a ∈ ({x} : Set G), c * a * c⁻¹ ∈ S := by
      intro a ha
      rw [Set.mem_singleton_iff.mp ha, hc]
      exact hyS
    obtain ⟨w, hchain, hwn⟩ := h S hS {x} hA hne c (Subgroup.mem_top c) hkA
    obtain ⟨hwS, hweq⟩ := eqvGen_of_fusionChain_singleton hxS hchain
    have hlast : FusionStep (insert (normalizer (S : Set G))
        (sylowMembers p 𝓕 S)) S (w * x * w⁻¹) y := by
      refine ⟨hwS, hyS, normalizer (S : Set G), Set.mem_insert_iff.mpr (Or.inl rfl),
        c * w⁻¹, hwn.2, ?_⟩
      rw [← hc]
      group
    exact Relation.EqvGen.trans x (w * x * w⁻¹) y hweq
      (Relation.EqvGen.rel _ _ hlast)

theorem ControlsSylowIntersections.familyControlsFusion [Finite G] [Fact p.Prime]
    {𝓕 : Set (Subgroup G)} {S : Subgroup G} (h𝓕 : IsNormalSetIn 𝓕 ⊤)
    (h : ControlsSylowIntersections p 𝓕 ⊤) (hS : IsSylowOf p S ⊤) :
    FamilyControlsFusion (insert (normalizer (S : Set G)) (sylowMembers p 𝓕 S)) S :=
  ((controlsSylowIntersections_iff_stronglyControlsFusion h𝓕).1 h).familyControlsFusion hS

end CFSG.GroupTheory
