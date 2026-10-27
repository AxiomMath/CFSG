module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Index
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem sec10A2_conj_sup_le {X Y Z : Subgroup G} {c : G} (hX : ∀ x ∈ X, c * x * c⁻¹ ∈ Z)
    (hY : ∀ y ∈ Y, c * y * c⁻¹ ∈ Z) : ∀ x ∈ X ⊔ Y, c * x * c⁻¹ ∈ Z := by
  intro x hx
  have hle : (X ⊔ Y).map (MulAut.conj c).toMonoidHom ≤ Z := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hX a ha
    · rintro _ ⟨a, ha, rfl⟩
      simpa [MulAut.conj_apply] using hY a ha
  simpa [MulAut.conj_apply] using hle (Subgroup.mem_map_of_mem _ hx)

theorem sec10A2_mem_sup_zpowers {S : Subgroup G} {g : G} (hg : g ∈ normalizer (S : Set G))
    (hg2 : g * g ∈ S) : ∀ y ∈ S ⊔ zpowers g, y ∈ S ∨ g⁻¹ * y ∈ S := by
  have hg' : ∀ s, s ∈ S ↔ g * s * g⁻¹ ∈ S := Subgroup.mem_normalizer_iff.mp hg
  have hconj : ∀ s ∈ S, g⁻¹ * s * g ∈ S := by
    intro s hs
    rw [hg' (g⁻¹ * s * g)]
    have e : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    rw [e]
    exact hs
  have hg2i : g⁻¹ * g⁻¹ ∈ S := by
    have h := S.inv_mem hg2
    rwa [mul_inv_rev] at h
  let U : Subgroup G :=
    { carrier := {y | y ∈ S ∨ g⁻¹ * y ∈ S}
      mul_mem' := by
        rintro a b (ha | ha) (hb | hb)
        · exact Or.inl (S.mul_mem ha hb)
        · right
          have e : g⁻¹ * (a * b) = (g⁻¹ * a * g) * (g⁻¹ * b) := by group
          rw [e]
          exact S.mul_mem (hconj a ha) hb
        · right
          have e : g⁻¹ * (a * b) = (g⁻¹ * a) * b := by group
          rw [e]
          exact S.mul_mem ha hb
        · left
          have e : a * b = (g * g) * (g⁻¹ * (g⁻¹ * a) * g) * (g⁻¹ * b) := by group
          rw [e]
          exact S.mul_mem (S.mul_mem hg2 (hconj _ ha)) hb
      one_mem' := Or.inl S.one_mem
      inv_mem' := by
        rintro a (ha | ha)
        · exact Or.inl (S.inv_mem ha)
        · right
          have e : g⁻¹ * a⁻¹ = (g⁻¹ * (g⁻¹ * a)⁻¹ * g) * (g⁻¹ * g⁻¹) := by group
          rw [e]
          exact S.mul_mem (hconj _ (S.inv_mem ha)) hg2i }
  have hle : S ⊔ zpowers g ≤ U := by
    refine sup_le (fun s hs => Or.inl hs) ?_
    rw [Subgroup.zpowers_le]
    exact Or.inr (by simp)
  intro y hy
  exact hle hy

theorem sec10A2_mem_normalizer_of_map_le [Finite G] {X : Subgroup G} {c : G}
    (hc : ∀ a ∈ X, c * a * c⁻¹ ∈ X) : c ∈ normalizer (X : Set G) := by
  have hle : X.map (MulAut.conj c).toMonoidHom ≤ X := by
    rintro _ ⟨a, ha, rfl⟩
    simpa [MulAut.conj_apply] using hc a ha
  have hcard : Nat.card ↥X ≤ Nat.card ↥(X.map (MulAut.conj c).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj c).injective).ge
  have heq : X.map (MulAut.conj c).toMonoidHom = X := Subgroup.eq_of_le_of_card_ge hle hcard
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hc x hx, fun hx => ?_⟩
  have hx' : c * x * c⁻¹ ∈ X.map (MulAut.conj c).toMonoidHom := by
    rw [heq]
    exact hx
  obtain ⟨a, ha, hax⟩ := hx'
  have hax' : c * a * c⁻¹ = c * x * c⁻¹ := by simpa [MulAut.conj_apply] using hax
  have : a = x := mul_left_cancel (mul_right_cancel hax')
  rwa [← this]

theorem sec10A2_elem_comm {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian 2 E) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a := by
  exact congrArg Subtype.val (hE.1.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)

theorem sec10A2_idx2_mul {S P : Subgroup G} (h2 : P.relIndex S = 2) {a b : G} (ha : a ∈ S)
    (hb : b ∈ S) (haP : a ∉ P) (hbP : b ∉ P) : a⁻¹ * b ∈ P := by
  have h2' : (P.subgroupOf S).index = 2 := h2
  have hiff := (Subgroup.mul_mem_iff_of_index_two h2' (a := (⟨a, ha⟩ : ↥S)⁻¹)
    (b := (⟨b, hb⟩ : ↥S)))
  have hnota : (⟨a, ha⟩ : ↥S)⁻¹ ∉ P.subgroupOf S := by
    intro h
    exact haP (by simpa using P.inv_mem (Subgroup.mem_subgroupOf.mp h))
  have hnotb : (⟨b, hb⟩ : ↥S) ∉ P.subgroupOf S := fun h => hbP (Subgroup.mem_subgroupOf.mp h)
  have hmem : (⟨a, ha⟩ : ↥S)⁻¹ * ⟨b, hb⟩ ∈ P.subgroupOf S :=
    hiff.mpr ⟨fun h => absurd h hnota, fun h => absurd h hnotb⟩
  exact Subgroup.mem_subgroupOf.mp hmem

theorem sec10A2_relIndex_dvd_two {S P X : Subgroup G} (hXS : X ≤ S) (h2 : P.relIndex S = 2) :
    P.relIndex X ∣ 2 := by
  rw [Subgroup.relIndex_dvd_two_iff]
  by_cases hXP : X ≤ P
  · exact ⟨1, X.one_mem, fun b hb => Or.inr (hXP hb)⟩
  · obtain ⟨x0, hx0, hx0P⟩ := SetLike.not_le_iff_exists.mp hXP
    refine ⟨x0, hx0, fun b hb => ?_⟩
    by_cases hbP : b ∈ P
    · exact Or.inr hbP
    · left
      have hbi : b⁻¹ ∉ P := fun h => hbP (by simpa using P.inv_mem h)
      have := sec10A2_idx2_mul h2 (S.inv_mem (hXS hb)) (hXS hx0) hbi hx0P
      simpa using this

structure IsDirectSplit (N K K0 : Subgroup G) : Prop where
  left_le : N ≤ K0
  right_le : K ≤ K0
  comm : ∀ n ∈ N, ∀ k ∈ K, n * k = k * n
  disj : ∀ x, x ∈ N → x ∈ K → x = 1
  dec : ∀ x ∈ K0, ∃ n ∈ N, ∃ k ∈ K, x = n * k

theorem IsDirectSplit.unique {N K K0 : Subgroup G} (D : IsDirectSplit N K K0) {n n' k k' : G}
    (hn : n ∈ N) (hn' : n' ∈ N) (hk : k ∈ K) (hk' : k' ∈ K) (h : n * k = n' * k') :
    n = n' ∧ k = k' := by
  have h1 : n'⁻¹ * n = k' * k⁻¹ := by
    calc n'⁻¹ * n = n'⁻¹ * (n * k) * k⁻¹ := by group
      _ = n'⁻¹ * (n' * k') * k⁻¹ := by rw [h]
      _ = k' * k⁻¹ := by group
  have h2 : n'⁻¹ * n = 1 :=
    D.disj _ (N.mul_mem (N.inv_mem hn') hn) (h1 ▸ K.mul_mem hk' (K.inv_mem hk))
  have h3 : n' = n := inv_mul_eq_one.mp h2
  subst h3
  exact ⟨rfl, mul_left_cancel h⟩

theorem IsDirectSplit.exists_act {N K K0 T : Subgroup G} (D : IsDirectSplit N K K0)
    (hK0 : ∀ y ∈ T, ∀ x ∈ K0, y * x * y⁻¹ ∈ K0) (hN : ∀ y ∈ T, ∀ x ∈ N, y * x * y⁻¹ ∈ N) :
    ∃ f : ↥T →* MulAut ↥K, ∀ (y : ↥T) (k : ↥K),
      ∃ n ∈ N, (y : G) * (k : G) * (y : G)⁻¹ = n * ((f y k : ↥K) : G) := by
  classical
  have hex : ∀ y : G, y ∈ T → ∀ k : G, k ∈ K → ∃ n ∈ N, ∃ k' ∈ K, y * k * y⁻¹ = n * k' :=
    fun y hy k hk => D.dec _ (hK0 y hy k (D.right_le hk))
  choose! nn hnn kk hkk hspec using hex
  have huniq : ∀ y ∈ T, ∀ k ∈ K, ∀ n ∈ N, ∀ k' ∈ K, y * k * y⁻¹ = n * k' → kk y k = k' := by
    intro y hy k hk n hn k' hk' h
    exact (D.unique (hnn y hy k hk) hn (hkk y hy k hk) hk'
      ((hspec y hy k hk).symm.trans h)).2
  have hmul : ∀ y ∈ T, ∀ k ∈ K, ∀ k' ∈ K, kk y (k * k') = kk y k * kk y k' := by
    intro y hy k hk k' hk'
    have e1 := hspec y hy k hk
    have e2 := hspec y hy k' hk'
    have hc := D.comm (nn y k') (hnn y hy k' hk') (kk y k) (hkk y hy k hk)
    refine huniq y hy (k * k') (K.mul_mem hk hk') (nn y k * nn y k')
      (N.mul_mem (hnn y hy k hk) (hnn y hy k' hk')) (kk y k * kk y k')
      (K.mul_mem (hkk y hy k hk) (hkk y hy k' hk')) ?_
    calc y * (k * k') * y⁻¹ = (y * k * y⁻¹) * (y * k' * y⁻¹) := by group
      _ = (nn y k * kk y k) * (nn y k' * kk y k') := by rw [e1, e2]
      _ = nn y k * (kk y k * nn y k') * kk y k' := by group
      _ = nn y k * (nn y k' * kk y k) * kk y k' := by rw [← hc]
      _ = (nn y k * nn y k') * (kk y k * kk y k') := by group
  have hinvl : ∀ y ∈ T, ∀ k ∈ K, kk y⁻¹ (kk y k) = k := by
    intro y hy k hk
    have hyi : y⁻¹ ∈ T := T.inv_mem hy
    refine huniq y⁻¹ hyi (kk y k) (hkk y hy k hk) (y⁻¹ * (nn y k)⁻¹ * y) ?_ k hk ?_
    · have h := hN y⁻¹ hyi (nn y k)⁻¹ (N.inv_mem (hnn y hy k hk))
      simpa using h
    · have e1 := hspec y hy k hk
      have e2 : kk y k = (nn y k)⁻¹ * (y * k * y⁻¹) := by rw [e1]; group
      calc y⁻¹ * kk y k * y⁻¹⁻¹ = y⁻¹ * ((nn y k)⁻¹ * (y * k * y⁻¹)) * y := by rw [e2]; group
        _ = (y⁻¹ * (nn y k)⁻¹ * y) * k := by group
  have hinvr : ∀ y ∈ T, ∀ k ∈ K, kk y (kk y⁻¹ k) = k := by
    intro y hy k hk
    have h := hinvl y⁻¹ (T.inv_mem hy) k hk
    rwa [inv_inv] at h
  have hone : ∀ k ∈ K, kk 1 k = k := by
    intro k hk
    exact huniq 1 T.one_mem k hk 1 N.one_mem k hk (by group)
  have hcomp : ∀ y ∈ T, ∀ y' ∈ T, ∀ k ∈ K, kk (y * y') k = kk y (kk y' k) := by
    intro y hy y' hy' k hk
    have hk1 : kk y' k ∈ K := hkk y' hy' k hk
    refine huniq (y * y') (T.mul_mem hy hy') k hk
      (y * nn y' k * y⁻¹ * nn y (kk y' k))
      (N.mul_mem (hN y hy _ (hnn y' hy' k hk)) (hnn y hy _ hk1)) (kk y (kk y' k))
      (hkk y hy _ hk1) ?_
    have e1 := hspec y' hy' k hk
    have e2 := hspec y hy _ hk1
    calc y * y' * k * (y * y')⁻¹ = y * (y' * k * y'⁻¹) * y⁻¹ := by group
      _ = y * (nn y' k * kk y' k) * y⁻¹ := by rw [e1]
      _ = (y * nn y' k * y⁻¹) * (y * kk y' k * y⁻¹) := by group
      _ = (y * nn y' k * y⁻¹) * (nn y (kk y' k) * kk y (kk y' k)) := by rw [e2]
      _ = (y * nn y' k * y⁻¹ * nn y (kk y' k)) * kk y (kk y' k) := by group
  let A : ↥T → MulAut ↥K := fun y =>
    { toFun := fun k => ⟨kk y k, hkk y y.2 k k.2⟩
      invFun := fun k => ⟨kk (y : G)⁻¹ k, hkk (y : G)⁻¹ (T.inv_mem y.2) k k.2⟩
      left_inv := fun k => Subtype.ext (hinvl y y.2 k k.2)
      right_inv := fun k => Subtype.ext (hinvr y y.2 k k.2)
      map_mul' := fun k k' => Subtype.ext (hmul y y.2 k k.2 k' k'.2) }
  refine ⟨{ toFun := A
            map_one' := ?_
            map_mul' := ?_ }, fun y k => ⟨nn y k, hnn y y.2 k k.2, hspec y y.2 k k.2⟩⟩
  · refine MulEquiv.ext fun k => Subtype.ext ?_
    exact hone k k.2
  · intro y y'
    refine MulEquiv.ext fun k => Subtype.ext ?_
    exact hcomp y y.2 y' y'.2 k k.2

theorem IsDirectSplit.act_eq_of_spec {N K K0 T : Subgroup G} (D : IsDirectSplit N K K0)
    (f : ↥T →* MulAut ↥K)
    (hf : ∀ (y : ↥T) (k : ↥K),
      ∃ n ∈ N, (y : G) * (k : G) * (y : G)⁻¹ = n * ((f y k : ↥K) : G))
    {y : ↥T} {k k' : ↥K} {n : G} (hn : n ∈ N)
    (h : (y : G) * (k : G) * (y : G)⁻¹ = n * (k' : G)) : f y k = k' := by
  obtain ⟨n0, hn0, h0⟩ := hf y k
  exact Subtype.ext (D.unique hn0 hn (f y k).2 k'.2 (h0.symm.trans h)).2

theorem IsDirectSplit.act_eq_one_iff {N K K0 T : Subgroup G} (D : IsDirectSplit N K K0)
    (f : ↥T →* MulAut ↥K)
    (hf : ∀ (y : ↥T) (k : ↥K),
      ∃ n ∈ N, (y : G) * (k : G) * (y : G)⁻¹ = n * ((f y k : ↥K) : G)) (y : ↥T) :
    f y = 1 ↔ ∀ k ∈ K, (y : G) * k * (y : G)⁻¹ * k⁻¹ ∈ N := by
  constructor
  · intro h k hk
    obtain ⟨n, hn, hy⟩ := hf y ⟨k, hk⟩
    have hk1 : ((f y ⟨k, hk⟩ : ↥K) : G) = k := by rw [h]; rfl
    rw [hk1] at hy
    have e : (y : G) * k * (y : G)⁻¹ * k⁻¹ = n := by rw [hy]; group
    rw [e]
    exact hn
  · intro h
    refine MulEquiv.ext fun k => ?_
    have hk := h k k.2
    exact D.act_eq_of_spec f hf (y := y) (k := k) (k' := k) hk (by group)

theorem IsDirectSplit.act_conj {N K K0 T : Subgroup G} (D : IsDirectSplit N K K0)
    (f : ↥T →* MulAut ↥K)
    (hf : ∀ (y : ↥T) (k : ↥K),
      ∃ n ∈ N, (y : G) * (k : G) * (y : G)⁻¹ = n * ((f y k : ↥K) : G)) (y : ↥T)
    (hyK : (y : G) ∈ K) (k : ↥K) : ((f y k : ↥K) : G) = (y : G) * k * (y : G)⁻¹ := by
  have hmem : (y : G) * (k : G) * (y : G)⁻¹ ∈ K := K.mul_mem (K.mul_mem hyK k.2) (K.inv_mem hyK)
  have h := D.act_eq_of_spec f hf (y := y) (k := k) (k' := ⟨_, hmem⟩) N.one_mem (by simp)
  rw [h]

end CFSG.OddStandard.SmallF3.Omega
