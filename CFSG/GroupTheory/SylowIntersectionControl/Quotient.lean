module

public import CFSG.GroupTheory.SylowIntersectionControl.Isolated

import CFSG.GroupTheory.SylowIntersectionControl.Fusion
import CFSG.GroupTheory.SylowIntersectionControl.Generation
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.ClassicalInvolution.LBalance.Glauberman.SylowTools
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

omit [Finite G] in
private lemma map_conj_map_conj_quo {S : Subgroup G} {a b : G} :
    (S.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      S.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  group

private lemma isSylowOf_map_quo {G' : Type*} [Group G'] {φ : G →* G'} {S K : Subgroup G}
    (h : IsSylowOf p S K) :
    IsSylowOf p (S.map φ) (K.map φ) := by
  obtain ⟨Q, rfl⟩ := h
  refine ⟨Q.mapSurjective (f := φ.subgroupMap K) (φ.subgroupMap_surjective K), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, Subgroup.map_map]
  congr 1

private lemma isSylowOf_map_top_quo {G' : Type*} [Group G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {S : Subgroup G} (hS : IsSylowOf p S ⊤) :
    IsSylowOf p (S.map φ) ⊤ := by
  have h := isSylowOf_map_quo (φ := φ) hS
  rwa [Subgroup.map_top_of_surjective φ hφ] at h

private lemma isSylowOf_of_le_of_not_dvd_relIndex_quo {Q X K : Subgroup G}
    (hQ : IsSylowOf p Q X) (hXK : X ≤ K) (hX : ¬ p ∣ X.relIndex K) :
    IsSylowOf p Q K := by
  rw [isSylowOf_iff] at hQ ⊢
  obtain ⟨hQX, hQp, hQidx⟩ := hQ
  refine ⟨hQX.trans hXK, hQp, ?_⟩
  intro hdvd
  rw [← Subgroup.relIndex_mul_relIndex (H := Q) (K := X) (L := K) hQX hXK] at hdvd
  exact (Nat.Prime.dvd_mul Fact.out).mp hdvd |>.elim hQidx hX

omit [Finite G] in
private lemma sup_inf_eq_inf_sup_quo {S O C : Subgroup G} [O.Normal] (hOC : O ≤ C) :
    (S ⊔ O) ⊓ C = (S ⊓ C) ⊔ O := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxS, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxS' : x ∈ (S : Set G) * (O : Set G) := by
      rw [← Subgroup.mul_normal S O]
      exact hxS
    obtain ⟨s, hsS, o, hoO, rfl⟩ := hxS'
    have hoC : o ∈ C := hOC hoO
    change s * o ∈ (↑((S ⊓ C) ⊔ O) : Set G)
    rw [Subgroup.mul_normal (S ⊓ C) O]
    exact ⟨s, ⟨hsS, (C.mul_mem_cancel_right hoC).mp hxC⟩, o, hoO, rfl⟩
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hOC)

private lemma isSylowOf_inf_comap_quo {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {S : Subgroup G} (hS : IsSylowOf p S ⊤) {X : Subgroup G'}
    (hX : IsSylowOf p (S.map φ ⊓ X) X) :
    IsSylowOf p (S ⊓ X.comap φ) (X.comap φ) := by
  rw [isSylowOf_iff] at hX ⊢
  obtain ⟨-, -, hBidx⟩ := hX
  refine ⟨inf_le_right, hS.isPGroup.to_inf_left, ?_⟩
  set C : Subgroup G := X.comap φ with hCdef
  set B : Subgroup G' := S.map φ ⊓ X with hBdef
  set D : Subgroup G := S ⊓ C with hDdef
  set E : Subgroup G := (S ⊔ φ.ker) ⊓ C with hEdef
  have hOC : φ.ker ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact X.one_mem
  have hcomap : B.comap φ = E := by
    rw [hBdef, Subgroup.comap_inf, Subgroup.comap_map_eq, hEdef]
  have hmapC : C.map φ = X := Subgroup.map_comap_eq_self_of_surjective hφ X
  have hErel : E.relIndex C = B.relIndex X := by
    have h := Subgroup.relIndex_comap (f := φ) (H := B) C
    rw [hcomap, hmapC] at h
    exact h
  have hEeq : E = D ⊔ φ.ker := by
    rw [hEdef, hDdef]
    exact sup_inf_eq_inf_sup_quo hOC
  have hDX : D ≤ E := by
    rw [hDdef, hEdef]
    exact le_inf (inf_le_left.trans le_sup_left) inf_le_right
  have hEC : E ≤ C := by rw [hEdef]; exact inf_le_right
  have hDC : D.relIndex C = D.relIndex E * E.relIndex C :=
    (Subgroup.relIndex_mul_relIndex (H := D) (K := E) (L := C) hDX hEC).symm
  have hprime1 : ¬ p ∣ D.relIndex E := by
    have h1 : D.relIndex E = D.relIndex φ.ker := by
      rw [hEeq, sup_comm]
      exact relIndex_sup_eq_relIndex_of_normal φ.ker D
    have h2 : D.relIndex φ.ker = (S ⊓ φ.ker).relIndex φ.ker := by
      rw [← Subgroup.inf_relIndex_right (H := D) (K := φ.ker)]
      congr 1
      rw [hDdef, inf_assoc, inf_comm C φ.ker, inf_eq_left.mpr hOC]
    have hSO : IsSylowOf p (S ⊓ φ.ker) φ.ker :=
      hS.inf_of_le_normalizer le_top (by rw [normalizer_eq_top (H := φ.ker)])
    rw [h1, h2]
    exact (isSylowOf_iff.mp hSO).2.2
  have hprime2 : ¬ p ∣ E.relIndex C := by rw [hErel]; exact hBidx
  rw [hDC]
  exact Nat.Prime.not_dvd_mul Fact.out hprime1 hprime2

private lemma exists_conj_mem_of_le_sup_quo {O : Subgroup G} [O.Normal] {S P : Subgroup G}
    (hS : IsSylowOf p S ⊤) (hP : IsPGroup p P) (hPS : P ≤ S ⊔ O) :
    ∃ o ∈ O, ∀ x ∈ P, o * x * o⁻¹ ∈ S := by
  have hSyl : IsSylowOf p S (S ⊔ O) := hS.of_le le_sup_left le_top
  obtain ⟨Q, hPQ, hQ⟩ := CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge hP hPS
  obtain ⟨k, hk, hkconj⟩ := IsSylowOf.exists_mem_conj hQ hSyl
  have hkmap : ∀ q ∈ Q, k * q * k⁻¹ ∈ S := fun q hq =>
    (hkconj (k * q * k⁻¹)).mpr (by rw [show k⁻¹ * (k * q * k⁻¹) * k = q by group]; exact hq)
  have hkSO : k ∈ (S : Set G) * (O : Set G) := by
    rw [← Subgroup.mul_normal S O]
    exact hk
  obtain ⟨s, hs, o, ho, hkso⟩ := hkSO
  refine ⟨o, ho, ?_⟩
  intro x hx
  have hkx : k * x * k⁻¹ ∈ S := hkmap x (hPQ hx)
  rw [← hkso] at hkx
  have : o * x * o⁻¹ = s⁻¹ * ((s * o) * x * (s * o)⁻¹) * s := by group
  rw [this]
  exact S.mul_mem (S.mul_mem (S.inv_mem hs) hkx) hs

omit [Finite G] in
private lemma map_conj_comap_quo {G' : Type*} [Group G'] {φ : G →* G'}
    (X : Subgroup G') (g : G) :
    (X.comap φ).map (MulAut.conj g).toMonoidHom =
      (X.map (MulAut.conj (φ g)).toMonoidHom).comap φ := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, hx, by simp [map_mul]⟩
  · rintro ⟨z, hz, hzy⟩
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have h : φ (g⁻¹ * y * g) = z := by
      rw [map_mul, map_mul, map_inv, ← hzy]
      group
    rw [h]
    exact hz

omit [Finite G] in
private lemma isNormalSetIn_comap_quo {G' : Type*} [Group G'] {φ : G →* G'}
    {𝓜 : Set (Subgroup G')} (hn : IsNormalSetIn 𝓜 ⊤) :
    IsNormalSetIn ((fun X => X.comap φ) '' 𝓜) ⊤ := by
  constructor
  · rintro - ⟨X, -, rfl⟩
    exact le_top
  · rintro - ⟨X, hX, rfl⟩ g -
    rw [map_conj_comap_quo]
    exact ⟨X.map (MulAut.conj (φ g)).toMonoidHom, hn.2 X hX _ trivial, rfl⟩

private lemma exists_mul_normalizer_quo {G' : Type*} [Group G'] {φ : G →* G'}
    {S : Subgroup G} (hS : IsSylowOf p S ⊤) {k : G}
    (hk : φ k ∈ normalizer ((S.map φ : Subgroup G') : Set G')) :
    ∃ o ∈ φ.ker, ∃ n ∈ normalizer (S : Set G), k = o * n := by
  have hhom : φ.comp (MulAut.conj k).toMonoidHom =
      (MulAut.conj (φ k)).toMonoidHom.comp φ := by
    ext s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    simp [map_mul]
  have hcomp : (S.map (MulAut.conj k).toMonoidHom).map φ =
      (S.map φ).map (MulAut.conj (φ k)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map, hhom]
  have hmaple : (S.map (MulAut.conj k).toMonoidHom).map φ ≤ S.map φ := by
    rw [hcomp]
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hk).le
  have hle : S.map (MulAut.conj k).toMonoidHom ≤ S ⊔ φ.ker := by
    have h := (Subgroup.map_le_iff_le_comap (f := φ) (H := S.map φ)).mp hmaple
    rwa [Subgroup.comap_map_eq] at h
  obtain ⟨o, ho, hoQ⟩ := exists_conj_mem_of_le_sup_quo (O := φ.ker) hS
    (hS.isPGroup.map (MulAut.conj k).toMonoidHom) hle
  have hok : S.map (MulAut.conj (o * k)).toMonoidHom ≤ S := by
    rw [← map_conj_map_conj_quo (S := S) (a := k) (b := o)]
    rintro x ⟨y, hy, rfl⟩
    exact hoQ y hy
  have heq : S.map (MulAut.conj (o * k)).toMonoidHom = S :=
    Subgroup.eq_of_le_of_card_ge hok
      (le_of_eq (Subgroup.card_map_of_injective (MulAut.conj (o * k)).injective).symm)
  refine ⟨o⁻¹, (φ.ker).inv_mem ho, o * k,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq, by group⟩

private lemma exists_le_mem_comap_quo {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {S : Subgroup G} (hS : IsSylowOf p S ⊤)
    {𝓜 : Set (Subgroup G')} (hn : IsNormalSetIn 𝓜 ⊤) (hne : 𝓜.Nonempty)
    (hind : ∀ X ∈ 𝓜, ¬ p ∣ X.index) :
    ∃ Y ∈ (fun X => X.comap φ) '' 𝓜, S ≤ Y := by
  obtain ⟨X, hX⟩ := hne
  obtain ⟨Q, hQ⟩ := exists_isSylowOf p X
  have hQtop : IsSylowOf p Q ⊤ :=
    isSylowOf_of_le_of_not_dvd_relIndex_quo (G := G') hQ le_top (by
      rw [Subgroup.relIndex_top_right]
      exact hind X hX)
  have hStop : IsSylowOf p (S.map φ) ⊤ := isSylowOf_map_top_quo hφ hS
  obtain ⟨k, _, hkconj⟩ := IsSylowOf.exists_mem_conj hQtop hStop
  refine ⟨(X.map (MulAut.conj k).toMonoidHom).comap φ,
    ⟨X.map (MulAut.conj k).toMonoidHom, hn.2 X hX k trivial, rfl⟩, ?_⟩
  intro s hs
  have hxQ : k⁻¹ * φ s * k ∈ Q :=
    (hkconj (φ s)).mp (Subgroup.mem_map.mpr ⟨s, hs, rfl⟩)
  exact Subgroup.mem_map.mpr
    ⟨k⁻¹ * φ s * k, hQ.le hxQ, by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

omit [Finite G] [Fact (Nat.Prime p)] in
private lemma reflTransGen_fusionChainStep_of_mem_iSup_quo {S : Subgroup G}
    {𝓜 : Set (Subgroup G)} {A : Set G} (hA : A ⊆ {1}) {w : G}
    (hw : w ∈ ⨆ X ∈ sylowMembers p 𝓜 S, X) :
    Relation.ReflTransGen (FusionChainStep p 𝓜 S A) 1 w := by
  classical
  let R : G → G → Prop := fun a b => ∃ Y ∈ sylowMembers p 𝓜 S, ∃ z ∈ Y, b = z * a
  have hRmul : ∀ a b, R a b → ∀ c, R (a * c) (b * c) := by
    rintro a b ⟨Y, hY, z, hz, rfl⟩ c
    exact ⟨Y, hY, z, hz, by group⟩
  have hlift : ∀ x, Relation.ReflTransGen R 1 x → ∀ y, Relation.ReflTransGen R y (x * y) := by
    intro x hx
    refine Relation.ReflTransGen.rec (motive := fun x _ =>
      ∀ y, Relation.ReflTransGen R y (x * y)) ?_ ?_ hx
    · intro y; simpa using Relation.ReflTransGen.refl (r := R) (a := y)
    · intro b c _ hbc ih y
      exact (ih y).tail (hRmul b c hbc y)
  have hmul : ∀ x y, Relation.ReflTransGen R 1 x → Relation.ReflTransGen R 1 y →
      Relation.ReflTransGen R 1 (x * y) := fun x y hx hy => hy.trans (hlift x hx y)
  have hC : ∀ x ∈ (⨆ X ∈ sylowMembers p 𝓜 S, X), Relation.ReflTransGen R 1 x := by
    intro x hx
    refine Subgroup.iSup_induction (C := fun z => Relation.ReflTransGen R 1 z)
      (fun X => ⨆ (_ : X ∈ sylowMembers p 𝓜 S), X) hx ?_ ?_ ?_
    · intro X z hz
      refine Subgroup.iSup_induction (C := fun z => Relation.ReflTransGen R 1 z)
        (fun (_ : X ∈ sylowMembers p 𝓜 S) => X) hz ?_ ?_ ?_
      · intro hX y hy
        exact Relation.ReflTransGen.single ⟨X, hX, y, hy, by simp⟩
      · exact Relation.ReflTransGen.refl
      · intro a b ha hb; exact hmul a b ha hb
    · exact Relation.ReflTransGen.refl
    · intro a b ha hb; exact hmul a b ha hb
  refine Relation.ReflTransGen.mono (fun a b hr => ?_) 1 w (hC w hw)
  obtain ⟨Y, hY, z, hz, rfl⟩ := hr
  exact ⟨Y, hY, z, hz, rfl, fun x hx => by
    rw [Set.mem_singleton_iff.mp (hA hx)]
    simp⟩

omit [Finite G] in
private lemma map_subtype_map_conj_quo {K : Subgroup G} {A : Subgroup K} {x : K} :
    (A.map (MulAut.conj x).toMonoidHom).map K.subtype =
      (A.map K.subtype).map (MulAut.conj (K.subtype x)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

omit [Finite G] in
private lemma map_subtype_top_quo (K : Subgroup G) : (⊤ : Subgroup K).map K.subtype = K := by
  rw [← Subgroup.top_subgroupOf (H := K), Subgroup.subgroupOf_map_subtype, top_inf_eq]

private lemma sylowConjLink_map_subtype_quo {K : Subgroup G} {𝓕 : Set (Subgroup K)}
    {A B D : Subgroup K} (h : SylowConjLink p 𝓕 ⊤ D A B) :
    SylowConjLink p ((fun X => X.map K.subtype) '' 𝓕) K (D.map K.subtype)
      (A.map K.subtype) (B.map K.subtype) := by
  obtain ⟨hA, hB, X, hXA, hXB, hD, x, hxX, hAB⟩ := h
  have hAmap : IsSylowOf p (A.map K.subtype) K := by
    have h := (isSylowOf_map_subtype_iff K (A := A) (B := ⊤)).mpr hA
    rwa [map_subtype_top_quo K] at h
  have hBmap : IsSylowOf p (B.map K.subtype) K := by
    have h := (isSylowOf_map_subtype_iff K (A := B) (B := ⊤)).mpr hB
    rwa [map_subtype_top_quo K] at h
  have hXmapA : X.map K.subtype ∈
      sylowMembers p ((fun X => X.map K.subtype) '' 𝓕) (A.map K.subtype) := by
    refine ⟨⟨X, hXA.1, rfl⟩, ?_⟩
    have h := (isSylowOf_map_subtype_iff K (A := A ⊓ X) (B := X)).mpr hXA.2
    rwa [Subgroup.map_inf A X K.subtype K.subtype_injective] at h
  have hXmapB : X.map K.subtype ∈
      sylowMembers p ((fun X => X.map K.subtype) '' 𝓕) (B.map K.subtype) := by
    refine ⟨⟨X, hXB.1, rfl⟩, ?_⟩
    have h := (isSylowOf_map_subtype_iff K (A := B ⊓ X) (B := X)).mpr hXB.2
    rwa [Subgroup.map_inf B X K.subtype K.subtype_injective] at h
  refine ⟨hAmap, hBmap, X.map K.subtype, hXmapA, hXmapB, ?_, K.subtype x, ?_, ?_⟩
  · calc D.map K.subtype ≤ (A ⊓ B ⊓ X).map K.subtype := Subgroup.map_mono hD
      _ = A.map K.subtype ⊓ B.map K.subtype ⊓ X.map K.subtype := by
        rw [Subgroup.map_inf (A ⊓ B) X K.subtype K.subtype_injective,
          Subgroup.map_inf A B K.subtype K.subtype_injective]
  · exact Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩
  · rw [hAB, map_subtype_map_conj_quo]

private lemma exists_conj_closure_quo {G' : Type*} [Group G'] {φ : G →* G'} {S : Subgroup G}
    (hS : IsSylowOf p S ⊤) {A : Set G} {h z0 : G} {b c zb : G'} {Y : Subgroup G'}
    (hz0 : φ z0 = zb) (hc : c = zb * b) (hh : φ h = b)
    (hhS : ∀ a ∈ A, h * a * h⁻¹ ∈ S)
    (hcond : ∀ ā ∈ φ '' A, c * ā * c⁻¹ ∈ S.map φ ⊓ Y) :
    ∃ o ∈ φ.ker, ∀ a ∈ A, o * (z0 * (h * a * h⁻¹) * z0⁻¹) * o⁻¹ ∈ S := by
  let P : Subgroup G := Subgroup.closure ((fun a => z0 * (h * a * h⁻¹) * z0⁻¹) '' A)
  have hPz : P ≤ S.map (MulAut.conj z0).toMonoidHom := by
    refine (Subgroup.closure_le (K := S.map (MulAut.conj z0).toMonoidHom)).mpr ?_
    rintro x ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨h * a * h⁻¹, hhS a ha, by simp [MulAut.conj_apply]⟩
  have hPcomap : P ≤ (S.map φ).comap φ := by
    refine (Subgroup.closure_le (K := (S.map φ).comap φ)).mpr ?_
    rintro x ⟨a, ha, rfl⟩
    change φ (z0 * (h * a * h⁻¹) * z0⁻¹) ∈ S.map φ
    have hza : φ (z0 * (h * a * h⁻¹) * z0⁻¹) = c * φ a * c⁻¹ := by
      simp only [map_mul, map_inv, hz0, hh]
      rw [hc]
      group
    rw [hza]
    exact (hcond (φ a) ⟨a, ha, rfl⟩).1
  have hPp : IsPGroup p P := (hS.isPGroup.map (MulAut.conj z0).toMonoidHom).to_le hPz
  have hPS : P ≤ S ⊔ φ.ker := by
    rw [← Subgroup.comap_map_eq (f := φ) (H := S)]
    exact hPcomap
  obtain ⟨o, ho, hoP⟩ := exists_conj_mem_of_le_sup_quo (O := φ.ker) hS hPp hPS
  exact ⟨o, ho, fun a ha => hoP _ (Subgroup.subset_closure ⟨a, ha, rfl⟩)⟩

private lemma fusionChainStep_lift_quo {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {S : Subgroup G}
    (hS : IsSylowOf p S ⊤) {𝓜 : Set (Subgroup G')}
    {A : Set G} {h : G} {b c : G'} (hh : φ h = b)
    (hhS : ∀ a ∈ A, h * a * h⁻¹ ∈ S)
    (hstep : FusionChainStep p 𝓜 (S.map φ) (φ '' A) b c) :
    ∃ h' : G, φ h' = c ∧ (∀ a ∈ A, h' * a * h'⁻¹ ∈ S) ∧
      FusionChainStep p ((fun X => X.comap φ) '' 𝓜) S A h h' := by
  obtain ⟨Y, hY, zb, hzb, hc, hcond⟩ := hstep
  obtain ⟨z0, hz0⟩ := hφ zb
  obtain ⟨o, ho, hoP⟩ := exists_conj_closure_quo hS hz0 hc hh hhS hcond
  have hzo : φ o = 1 := MonoidHom.mem_ker.mp ho
  have hgoal : ∀ a ∈ A, (o * z0 * h) * a * (o * z0 * h)⁻¹ ∈ S := by
    intro a ha
    have h1 : o * (z0 * (h * a * h⁻¹) * z0⁻¹) * o⁻¹ ∈ S := hoP a ha
    have h2 : (o * z0 * h) * a * (o * z0 * h)⁻¹ =
        o * (z0 * (h * a * h⁻¹) * z0⁻¹) * o⁻¹ := by group
    rwa [h2]
  refine ⟨o * z0 * h, ?_, hgoal, ?_⟩
  · simp only [map_mul, hzo, hz0, hh, one_mul]
    exact hc.symm
  · refine ⟨Y.comap φ,
      ⟨⟨Y, hY.1, rfl⟩, isSylowOf_inf_comap_quo hφ hS hY.2⟩, o * z0, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_comap, map_mul, hzo, hz0, one_mul]; exact hzb
    · group
    · intro a ha
      have h1 : o * (z0 * (h * a * h⁻¹) * z0⁻¹) * o⁻¹ ∈ S := hoP a ha
      have h2 : (o * z0 * h) * a * (o * z0 * h)⁻¹ =
          o * (z0 * (h * a * h⁻¹) * z0⁻¹) * o⁻¹ := by group
      have h3 : φ (o * (z0 * (h * a * h⁻¹) * z0⁻¹) * o⁻¹) = c * φ a * c⁻¹ := by
        simp only [map_mul, map_inv, hzo, hz0, hh]
        rw [hc]
        group
      rw [Subgroup.mem_inf]
      refine ⟨h2 ▸ h1, ?_⟩
      rw [Subgroup.mem_comap, h2, h3]
      exact (hcond (φ a) ⟨a, ha, rfl⟩).2

private lemma exists_lift_fusionChain_quo {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {S : Subgroup G}
    (hS : IsSylowOf p S ⊤) {𝓜 : Set (Subgroup G')}
    {A : Set G} (hA : A ⊆ S) {hb : G'}
    (hchain : Relation.ReflTransGen
      (FusionChainStep p 𝓜 (S.map φ) (φ '' A)) 1 hb) :
    ∃ h : G, φ h = hb ∧
      Relation.ReflTransGen (FusionChainStep p
        ((fun X => X.comap φ) '' 𝓜) S A) 1 h ∧
      ∀ a ∈ A, h * a * h⁻¹ ∈ S := by
  refine Relation.ReflTransGen.rec (motive := fun b _ => ∃ h : G,
    φ h = b ∧
      Relation.ReflTransGen (FusionChainStep p
        ((fun X => X.comap φ) '' 𝓜) S A) 1 h ∧
      ∀ a ∈ A, h * a * h⁻¹ ∈ S) ?_ ?_ hchain
  · refine ⟨1, by simp, Relation.ReflTransGen.refl, ?_⟩
    intro a ha
    simpa using hA ha
  · rintro b c _ hstep ⟨h, hhb, hchainh, hhS⟩
    obtain ⟨h', hh', hh'S, hstep'⟩ := fusionChainStep_lift_quo hφ hS hhb hhS hstep
    exact ⟨h', hh', hchainh.tail hstep', hh'S⟩

private lemma stronglyControlsFusion_finish_quo {G' : Type*} [Group G'] [Finite G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {S : Subgroup G} (hS : IsSylowOf p S ⊤)
    {𝓜 : Set (Subgroup G')} (hn : IsNormalSetIn 𝓜 ⊤) (hne : 𝓜.Nonempty)
    (hind : ∀ X ∈ 𝓜, ¬ p ∣ X.index) {A : Set G} (hA : A ⊆ S) {k : G}
    (hkA : ∀ a ∈ A, k * a * k⁻¹ ∈ S) {hb : G'}
    (hchain : Relation.ReflTransGen (FusionChainStep p 𝓜 (S.map φ) (φ '' A)) 1 hb)
    (hnorm : φ k * hb⁻¹ ∈ normalizer ((S.map φ : Subgroup G') : Set G')) :
    ∃ h : G, Relation.ReflTransGen
        (FusionChainStep p ((fun X => X.comap φ) '' 𝓜) S A) 1 h ∧
      k * h⁻¹ ∈ ⊤ ⊓ normalizer (S : Set G) := by
  obtain ⟨h, hh, hchainG, -⟩ := exists_lift_fusionChain_quo hφ hS hA hchain
  have hnorm' : φ (k * h⁻¹) ∈ normalizer ((S.map φ : Subgroup G') : Set G') := by
    rw [map_mul, map_inv, hh]
    exact hnorm
  obtain ⟨o, ho, n, hnN, hkn⟩ := exists_mul_normalizer_quo hS hnorm'
  obtain ⟨Y, hY, hSY⟩ := exists_le_mem_comap_quo hφ hS hn hne hind
  obtain ⟨X, hX, rfl⟩ := hY
  have hOY : φ.ker ≤ X.comap φ := by
    intro x hx
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact X.one_mem
  have hYmem : X.comap φ ∈ sylowMembers p ((fun X => X.comap φ) '' 𝓜) S := by
    refine ⟨⟨X, hX, rfl⟩, ?_⟩
    rw [inf_eq_left.mpr hSY]
    exact hS.of_le hSY le_top
  have hzY : n⁻¹ * o * n ∈ X.comap φ :=
    hOY (by simpa using (inferInstance : φ.ker.Normal).conj_mem o ho n⁻¹)
  have hkh : k = o * n * h := by rw [← hkn]; group
  refine ⟨n⁻¹ * k, ?_, ?_⟩
  · refine hchainG.tail ⟨X.comap φ, hYmem, n⁻¹ * o * n, hzY, ?_, ?_⟩
    · show n⁻¹ * k = (n⁻¹ * o * n) * h
      rw [hkh]; group
    · intro a ha
      have hka : k * a * k⁻¹ ∈ S := hkA a ha
      have h1 : (n⁻¹ * k) * a * (n⁻¹ * k)⁻¹ ∈ S := by
        have h2 : (n⁻¹ * k) * a * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * a * k⁻¹) * n := by group
        rw [h2]
        exact (Subgroup.mem_normalizer_iff''.mp hnN (k * a * k⁻¹)).mp hka
      exact ⟨h1, hSY h1⟩
  · have h2 : k * (n⁻¹ * k)⁻¹ = n := by group
    rw [h2]
    exact ⟨trivial, hnN⟩

theorem ControlsSylowIntersections.comap_of_surjective {G' : Type*} [Group G'] {φ : G →* G'}
    (hφ : Function.Surjective φ) {𝓜 : Set (Subgroup G')} (hn : IsNormalSetIn 𝓜 ⊤)
    (hne : 𝓜.Nonempty) (hind : ∀ X ∈ 𝓜, ¬ p ∣ X.index) (h : ControlsSylowIntersections p 𝓜 ⊤)
    (hiso : ¬ IsPIsolatedOver p ⊤ (⊥ : Subgroup G')) :
    ControlsSylowIntersections p ((fun X => X.comap φ) '' 𝓜) ⊤ := by
  have : Finite G' := Finite.of_surjective φ hφ
  have h𝓜' : IsNormalSetIn ((fun X => X.comap φ) '' 𝓜) ⊤ := isNormalSetIn_comap_quo hn
  refine (controlsSylowIntersections_iff_stronglyControlsFusion h𝓜').mpr ?_
  intro S hS A hA hneA k _ hkA
  have hStop : IsSylowOf p (S.map φ) ⊤ := isSylowOf_map_top_quo hφ hS
  have hĀ : φ '' A ⊆ S.map φ := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨a, hA ha, rfl⟩
  have hkĀ : ∀ ā ∈ φ '' A, φ k * ā * (φ k)⁻¹ ∈ S.map φ := by
    rintro _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨k * a * k⁻¹, hkA a ha, by simp [map_mul]⟩
  by_cases hcase : ∃ a ∈ A, φ a ≠ 1
  · obtain ⟨a0, ha0, ha0ne⟩ := hcase
    obtain ⟨hb, hchain, hnorm⟩ :=
      ((controlsSylowIntersections_iff_stronglyControlsFusion hn).mp h)
        (S.map φ) hStop (φ '' A) hĀ ⟨φ a0, ⟨a0, ha0, rfl⟩, ha0ne⟩ (φ k) trivial hkĀ
    exact stronglyControlsFusion_finish_quo hφ hS hn hne hind hA hkA hchain hnorm.2
  · push Not at hcase
    have hĀ1 : φ '' A ⊆ ({1} : Set G') := by
      rintro _ ⟨a, ha, rfl⟩
      simp [hcase a ha]
    obtain ⟨w, hw, m, hm, hwm⟩ := Set.mem_mul.mp
      (show (φ k)⁻¹ ∈
          ((⨆ X ∈ sylowMembers p 𝓜 (S.map φ), X : Subgroup G') : Set G') *
          ((⊤ ⊓ normalizer ((S.map φ : Subgroup G') : Set G') : Subgroup G') : Set G') from by
        rw [ControlsSylowIntersections.mul_normalizer_eq hn h hiso hStop]
        trivial)
    have hchain : Relation.ReflTransGen
        (FusionChainStep p 𝓜 (S.map φ) (φ '' A)) 1 w⁻¹ :=
      reflTransGen_fusionChainStep_of_mem_iSup_quo (G := G') (S := S.map φ) (𝓜 := 𝓜)
        (A := φ '' A) hĀ1 (Subgroup.inv_mem _ hw)
    have hnorm : φ k * (w⁻¹)⁻¹ ∈ normalizer ((S.map φ : Subgroup G') : Set G') := by
      have h2 : φ k = m⁻¹ * w⁻¹ := by
        rw [← inv_inv (φ k), ← hwm, mul_inv_rev]
      have h : φ k * (w⁻¹)⁻¹ = m⁻¹ := by rw [inv_inv, h2]; group
      rw [h]
      exact (normalizer _).inv_mem hm.2
    exact stronglyControlsFusion_finish_quo hφ hS hn hne hind hA hkA hchain hnorm

theorem ControlsSylowIntersections.map_subtype {K : Subgroup G} {𝓕 : Set (Subgroup K)}
    (h : ControlsSylowIntersections p 𝓕 ⊤) :
    ControlsSylowIntersections p ((fun X => X.map K.subtype) '' 𝓕) K := by
  intro S T hS hT hST hne
  set S₀ : Subgroup K := S.subgroupOf K with hS₀
  set T₀ : Subgroup K := T.subgroupOf K with hT₀
  have hS₀map : S₀.map K.subtype = S := by
    rw [hS₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hS.le]
  have hT₀map : T₀.map K.subtype = T := by
    rw [hT₀, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hT.le]
  have hS₀syl : IsSylowOf p S₀ ⊤ :=
    (isSylowOf_map_subtype_iff K (A := S₀) (B := ⊤)).mp (by rwa [hS₀map, map_subtype_top_quo K])
  have hT₀syl : IsSylowOf p T₀ ⊤ :=
    (isSylowOf_map_subtype_iff K (A := T₀) (B := ⊤)).mp (by rwa [hT₀map, map_subtype_top_quo K])
  have hST₀ : S₀ ≠ T₀ := fun hEq => hST (by rw [← hS₀map, ← hT₀map, hEq])
  have hD : (S₀ ⊓ T₀).map K.subtype = S ⊓ T := by
    rw [Subgroup.map_inf S₀ T₀ K.subtype K.subtype_injective, hS₀map, hT₀map]
  have hne₀ : S₀ ⊓ T₀ ≠ ⊥ := by
    intro hbot
    exact hne (by rw [← hD, hbot, Subgroup.map_bot])
  have hchain := h S₀ T₀ hS₀syl hT₀syl hST₀ hne₀
  rw [show S = S₀.map K.subtype from hS₀map.symm,
      show T = T₀.map K.subtype from hT₀map.symm]
  change Relation.ReflTransGen (SylowConjLink p ((fun X => X.map K.subtype) '' 𝓕) K
    (S₀.map K.subtype ⊓ T₀.map K.subtype)) (S₀.map K.subtype) (T₀.map K.subtype)
  rw [← Subgroup.map_inf S₀ T₀ K.subtype K.subtype_injective]
  refine Relation.ReflTransGen.rec (motive := fun R _ =>
    Relation.ReflTransGen (SylowConjLink p ((fun X => X.map K.subtype) '' 𝓕) K
      ((S₀ ⊓ T₀).map K.subtype)) (S₀.map K.subtype) (R.map K.subtype)) ?_ ?_ hchain
  · exact Relation.ReflTransGen.refl
  · intro b c _ hlink ih
    exact ih.tail (sylowConjLink_map_subtype_quo hlink)

end CFSG.GroupTheory
