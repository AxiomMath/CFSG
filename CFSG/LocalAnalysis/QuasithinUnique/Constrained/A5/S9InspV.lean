module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S9InspA

public section

namespace CFSG.QuasithinUnique.A5.Insp

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.Id2519 CFSG.GH74.Uniqueness.SU.SU1

section Inner

variable {G : Type} [Group G]

@[expose] def innerActing (K N : Subgroup G) (hN : N ≤ Subgroup.normalizer (K : Set G)) :
    Subgroup G where
  carrier := {g | g ∈ N ∧ ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹}
  mul_mem' := by
    rintro a b ⟨haN, k₁, hk₁, h₁⟩ ⟨hbN, k₂, hk₂, h₂⟩
    refine ⟨N.mul_mem haN hbN, k₁ * k₂, K.mul_mem hk₁ hk₂, fun x hx => ?_⟩
    have hy : k₂ * x * k₂⁻¹ ∈ K := K.mul_mem (K.mul_mem hk₂ hx) (K.inv_mem hk₂)
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * (k₂ * x * k₂⁻¹) * a⁻¹ := by rw [h₂ x hx]
      _ = k₁ * (k₂ * x * k₂⁻¹) * k₁⁻¹ := h₁ _ hy
      _ = (k₁ * k₂) * x * (k₁ * k₂)⁻¹ := by group
  one_mem' := ⟨N.one_mem, 1, K.one_mem, fun x _ => by group⟩
  inv_mem' := by
    rintro a ⟨haN, k, hk, h⟩
    refine ⟨N.inv_mem haN, k⁻¹, K.inv_mem hk, fun x hx => ?_⟩
    have hy : a⁻¹ * x * a ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem (hN haN))
        x).mp hx
      simpa using this
    have h1 := h _ hy
    have h2 : x = k * (a⁻¹ * x * a) * k⁻¹ := by
      calc x = a * (a⁻¹ * x * a) * a⁻¹ := by group
        _ = k * (a⁻¹ * x * a) * k⁻¹ := h1
    calc a⁻¹ * x * a⁻¹⁻¹ = k⁻¹ * (k * (a⁻¹ * x * a) * k⁻¹) * k := by group
      _ = k⁻¹ * x * k := by rw [← h2]
      _ = k⁻¹ * x * k⁻¹⁻¹ := by group

theorem mem_innerActing {K N : Subgroup G} {hN : N ≤ Subgroup.normalizer (K : Set G)} {g : G} :
    g ∈ innerActing K N hN ↔ g ∈ N ∧ ∃ k ∈ K, ∀ x ∈ K, g * x * g⁻¹ = k * x * k⁻¹ := Iff.rfl

theorem innerActing_conj {K N : Subgroup G} (hN : N ≤ Subgroup.normalizer (K : Set G)) {a y : G}
    (ha : a ∈ N) (hy : y ∈ innerActing K N hN) : a * y * a⁻¹ ∈ innerActing K N hN := by
  obtain ⟨hyN, k, hk, h⟩ := mem_innerActing.mp hy
  refine mem_innerActing.mpr ⟨N.mul_mem (N.mul_mem ha hyN) (N.inv_mem ha), a * k * a⁻¹, ?_,
    fun x hx => ?_⟩
  · exact (Subgroup.mem_normalizer_iff.mp (hN ha) k).mp hk
  · have hx' : a⁻¹ * x * a ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem (hN ha))
        x).mp hx
      simpa using this
    have h1 := h _ hx'
    calc a * y * a⁻¹ * x * (a * y * a⁻¹)⁻¹ = a * (y * (a⁻¹ * x * a) * y⁻¹) * a⁻¹ := by group
      _ = a * (k * (a⁻¹ * x * a) * k⁻¹) * a⁻¹ := by rw [h1]
      _ = (a * k * a⁻¹) * x * (a * k * a⁻¹)⁻¹ := by group

end Inner

section StageV

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {z u : G} {A V K : Subgroup G}

theorem uz_mem_K (D : U9Data T M H S L z u A V)
    (hK : IsComponentIn K (centralizerElem u)) (hcomm : ⁅K, Subgroup.zpowers z⁆ = K)
    (hN2 : (centralizerElem u ⊓ Subgroup.normalizer (K : Set G)).relIndex (centralizerElem u) ≤ 2)
    (hZK : ∀ k ∈ K, (∀ k' ∈ K, k * k' = k' * k) → k = 1)
    (hout : ∀ g : MulAut ↥K, g ^ 3 = 1 → g ∈ innAut ↥K)
    (hmax : ∀ E : Subgroup G, E ≤ T → IsElemAbelian 2 E → Nat.card ↥E ≤ 16) :
    u * z ∈ K := by
  classical
  by_contra huz
  set Gu : Subgroup G := centralizerElem u with hGu
  set N : Subgroup G := Gu ⊓ Subgroup.normalizer (K : Set G) with hNdef
  have hNG : N ≤ Gu := inf_le_left
  have hKN : N ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hKG : K ≤ Gu := hK.1
  have hAN : A ≤ N := A_le_of_relIndex D hNG hN2
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := hAN.trans hKN
  have hCK : A ⊓ Subgroup.centralizer (K : Set G) = ⊥ := A_inf_centralizer_eq_bot D hK hcomm hAK
  have hAG : ∀ a ∈ A, a ∈ Gu := fun a ha => (D.A_le_Hu ha).2
  have hu : ∀ g ∈ Gu, g * u = u * g := fun g hg => Subgroup.mem_centralizer_singleton_iff.mp hg
  have hVK : ∀ x ∈ V, x ∈ K → x = 1 := by
    intro x hxV hxK
    by_contra hx1
    exact huz (D.hA.le_of_mem hAK hxK hxV hx1 D.uz_mem)
  obtain ⟨c, hcA, hc3, hcNV, hcfp, hAc⟩ := D.hA.exists_c
  have hc3' : c ^ 3 = 1 := by rw [← hc3]; exact pow_orderOf_eq_one c
  have hcN : c ∈ N := hAN hcA
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := hKN hcN
  have hcG : c ∈ Gu := hNG hcN
  obtain ⟨k₀, hk₀K, hk₀⟩ : ∃ k₀ ∈ K, ∀ x ∈ K, c * x * c⁻¹ = k₀ * x * k₀⁻¹ := by
    have hg3 : (k32ActHom K N hKN ⟨c, hcN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : ↥N) ^ 3 = 1 := Subtype.ext (by simpa using hc3')
      rw [this, map_one]
    obtain ⟨k₀, hk₀⟩ := hout _ hg3
    refine ⟨(k₀ : G), k₀.2, fun x hx => ?_⟩
    have := congrArg (fun f : MulAut ↥K => ((f ⟨x, hx⟩ : ↥K) : G)) hk₀
    simpa [k32ActHom_apply, MulAut.conj_apply] using this.symm
  have hcY : c ∈ innerActing K N hKN := mem_innerActing.mpr ⟨hcN, k₀, hk₀K, hk₀⟩
  have hAY : A ≤ Subgroup.normalizer ((innerActing K N hKN : Subgroup G) : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · exact fun hy => innerActing_conj hKN (hAN ha) hy
    · intro hy
      have h1 := innerActing_conj hKN (hAN (A.inv_mem ha)) hy
      have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
      rwa [e] at h1
  have hv₁V : u * z ∈ V := D.uz_mem
  have hv₁1 : u * z ≠ 1 := D.uz_ne_one
  have hVY : V ≤ innerActing K N hKN := by
    have hwY : (u * z) * c * (u * z)⁻¹ * c⁻¹ ∈ innerActing K N hKN := by
      have h1 := innerActing_conj hKN (hAN (D.V_le_A hv₁V)) hcY
      exact (innerActing K N hKN).mul_mem h1 ((innerActing K N hKN).inv_mem hcY)
    have hwV : (u * z) * c * (u * z)⁻¹ * c⁻¹ ∈ V := by
      have h1 : c * (u * z)⁻¹ * c⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp hcNV _).mp (V.inv_mem hv₁V)
      have e : (u * z) * c * (u * z)⁻¹ * c⁻¹ = (u * z) * (c * (u * z)⁻¹ * c⁻¹) := by group
      rw [e]
      exact V.mul_mem hv₁V h1
    have hw1 : (u * z) * c * (u * z)⁻¹ * c⁻¹ ≠ 1 := by
      intro h
      apply hcfp (u * z) hv₁V hv₁1
      have h2 : (u * z) * c = c * (u * z) := by
        calc (u * z) * c = ((u * z) * c * (u * z)⁻¹ * c⁻¹) * (c * (u * z)) := by group
          _ = c * (u * z) := by rw [h, one_mul]
      calc c * (u * z) * c⁻¹ = (u * z) * c * c⁻¹ := by rw [← h2]
        _ = u * z := by group
    exact D.hA.le_of_mem hAY hwY hwV hw1
  obtain ⟨-, k₁, hk₁K, hk₁⟩ := mem_innerActing.mp (hVY hv₁V)
  have hb₁ : ∀ x ∈ K, (k₁⁻¹ * (u * z)) * x = x * (k₁⁻¹ * (u * z)) := by
    intro x hx
    have h1 := hk₁ x hx
    calc (k₁⁻¹ * (u * z)) * x = k₁⁻¹ * ((u * z) * x * (u * z)⁻¹) * (u * z) := by group
      _ = k₁⁻¹ * (k₁ * x * k₁⁻¹) * (u * z) := by rw [h1]
      _ = x * (k₁⁻¹ * (u * z)) := by group
  set b₁ : G := k₁⁻¹ * (u * z) with hb₁def
  have hv₁eq : u * z = k₁ * b₁ := by rw [hb₁def]; group
  set k₂ : G := c * k₁ * c⁻¹ with hk₂def
  set b₂ : G := c * b₁ * c⁻¹ with hb₂def
  set v₂ : G := c * (u * z) * c⁻¹ with hv₂def
  have hk₂K : k₂ ∈ K := (Subgroup.mem_normalizer_iff.mp hcK k₁).mp hk₁K
  have hb₂ : ∀ x ∈ K, b₂ * x = x * b₂ := by
    intro x hx
    have hx' : c⁻¹ * x * c ∈ K := by
      have hcK' : c⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
        (Subgroup.normalizer (K : Set G)).inv_mem hcK
      have := (Subgroup.mem_normalizer_iff.mp hcK' x).mp hx
      simpa using this
    have h1 := hb₁ _ hx'
    calc b₂ * x = c * (b₁ * (c⁻¹ * x * c)) * c⁻¹ := by rw [hb₂def]; group
      _ = c * ((c⁻¹ * x * c) * b₁) * c⁻¹ := by rw [h1]
      _ = x * b₂ := by rw [hb₂def]; group
  have hv₂eq : v₂ = k₂ * b₂ := by
    rw [hv₂def, hk₂def, hb₂def, hv₁eq]
    group
  have hv₂V : v₂ ∈ V := (Subgroup.mem_normalizer_iff.mp hcNV _).mp hv₁V
  have hv₂1 : v₂ ≠ 1 := by
    intro h
    apply hv₁1
    have : c * (u * z) * c⁻¹ = 1 := h
    calc u * z = c⁻¹ * (c * (u * z) * c⁻¹) * c := by group
      _ = 1 := by rw [this]; group
  have hv₁₂ : u * z ≠ v₂ := fun h => hcfp (u * z) hv₁V hv₁1 h.symm
  have hv₁sq : (u * z) * (u * z) = 1 := uz_sq D
  have hV4 : Nat.card ↥V = 4 := D.hA.card_U
  have hVc := klein_cases hV4 hv₁V hv₂V hv₁sq hv₁1 hv₂1 hv₁₂
  have hVcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := D.hA.comm_U
  have hk₁1 : k₁ ≠ 1 := by
    intro h
    have hb : u * z = b₁ := by rw [hv₁eq, h, one_mul]
    have hmem : u * z ∈ A ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨D.V_le_A hv₁V, Subgroup.mem_centralizer_iff.mpr fun x hx => by
        rw [hb]; exact (hb₁ x hx).symm⟩
    rw [hCK] at hmem
    exact hv₁1 (Subgroup.mem_bot.mp hmem)
  have hk₁comm : ∀ x ∈ K, b₁ * x = x * b₁ := hb₁
  have hk₁sq : k₁ * k₁ = 1 := by
    have h1 : (k₁ * b₁) * (k₁ * b₁) = 1 := by rw [← hv₁eq]; exact hv₁sq
    have hkb : b₁ * k₁ = k₁ * b₁ := hb₁ k₁ hk₁K
    have h2 : (k₁ * k₁) * (b₁ * b₁) = 1 := by
      calc (k₁ * k₁) * (b₁ * b₁) = k₁ * (k₁ * b₁) * b₁ := by group
        _ = k₁ * (b₁ * k₁) * b₁ := by rw [hkb]
        _ = (k₁ * b₁) * (k₁ * b₁) := by group
        _ = 1 := h1
    have hkk : k₁ * k₁ = (b₁ * b₁)⁻¹ := eq_inv_of_mul_eq_one_left h2
    refine hZK _ (K.mul_mem hk₁K hk₁K) fun k' hk' => ?_
    have hc : Commute b₁ k' := hb₁ k' hk'
    rw [hkk]
    exact (hc.mul_left hc).inv_left.eq
  have hk₂1 : k₂ ≠ 1 := by
    intro h
    apply hk₁1
    have : c * k₁ * c⁻¹ = 1 := h
    calc k₁ = c⁻¹ * (c * k₁ * c⁻¹) * c := by group
      _ = 1 := by rw [this]; group
  have hk₂sq : k₂ * k₂ = 1 := by
    calc k₂ * k₂ = c * (k₁ * k₁) * c⁻¹ := by rw [hk₂def]; group
      _ = 1 := by rw [hk₁sq]; group
  have hv12 : (u * z) * v₂ = v₂ * (u * z) := hVcomm _ hv₁V _ hv₂V
  have hbk₂ : b₁ * k₂ = k₂ * b₁ := hb₁ k₂ hk₂K
  have hbk₁ : b₂ * k₁ = k₁ * b₂ := hb₂ k₁ hk₁K
  have hk₁₂comm : k₁ * k₂ = k₂ * k₁ := by
    have h2a : (k₁ * b₁) * (k₂ * b₂) = k₁ * k₂ * (b₁ * b₂) := by
      calc (k₁ * b₁) * (k₂ * b₂) = k₁ * (b₁ * k₂) * b₂ := by group
        _ = k₁ * (k₂ * b₁) * b₂ := by rw [hbk₂]
        _ = k₁ * k₂ * (b₁ * b₂) := by group
    have h2b : (k₂ * b₂) * (k₁ * b₁) = k₂ * k₁ * (b₂ * b₁) := by
      calc (k₂ * b₂) * (k₁ * b₁) = k₂ * (b₂ * k₁) * b₁ := by group
        _ = k₂ * (k₁ * b₂) * b₁ := by rw [hbk₁]
        _ = k₂ * k₁ * (b₂ * b₁) := by group
    have h2 : k₁ * k₂ * (b₁ * b₂) = k₂ * k₁ * (b₂ * b₁) := by
      rw [← h2a, ← h2b, ← hv₁eq, ← hv₂eq]
      exact hv12
    have hp : (k₂ * k₁)⁻¹ * (k₁ * k₂) = (b₂ * b₁) * (b₁ * b₂)⁻¹ := by
      have h3 : k₁ * k₂ = k₂ * k₁ * (b₂ * b₁) * (b₁ * b₂)⁻¹ := by
        calc k₁ * k₂ = (k₁ * k₂ * (b₁ * b₂)) * (b₁ * b₂)⁻¹ := by group
          _ = (k₂ * k₁ * (b₂ * b₁)) * (b₁ * b₂)⁻¹ := by rw [h2]
      calc (k₂ * k₁)⁻¹ * (k₁ * k₂) = (k₂ * k₁)⁻¹ * (k₂ * k₁ * (b₂ * b₁) * (b₁ * b₂)⁻¹) := by
            rw [← h3]
        _ = (b₂ * b₁) * (b₁ * b₂)⁻¹ := by group
    have hpK : (k₂ * k₁)⁻¹ * (k₁ * k₂) ∈ K :=
      K.mul_mem (K.inv_mem (K.mul_mem hk₂K hk₁K)) (K.mul_mem hk₁K hk₂K)
    have hp1 : (k₂ * k₁)⁻¹ * (k₁ * k₂) = 1 := by
      refine hZK _ hpK fun x hx => ?_
      rw [hp]
      have c1 : Commute b₁ x := hb₁ x hx
      have c2 : Commute b₂ x := hb₂ x hx
      exact ((c2.mul_left c1).mul_left (c1.mul_left c2).inv_left).eq
    calc k₁ * k₂ = (k₂ * k₁) * ((k₂ * k₁)⁻¹ * (k₁ * k₂)) := by group
      _ = k₂ * k₁ := by rw [hp1, mul_one]
  have hk₁₂ne : k₁ ≠ k₂ := by
    intro h
    have hb12 : (u * z) * v₂ = b₁ * b₂ := by
      rw [hv₂eq, hv₁eq, ← h]
      calc (k₁ * b₁) * (k₁ * b₂) = k₁ * (b₁ * k₁) * b₂ := by group
        _ = k₁ * (k₁ * b₁) * b₂ := by rw [hb₁ k₁ hk₁K]
        _ = (k₁ * k₁) * (b₁ * b₂) := by group
        _ = b₁ * b₂ := by rw [hk₁sq, one_mul]
    have hmemA : b₁ * b₂ ∈ A := by
      rw [← hb12]
      exact A.mul_mem (D.V_le_A hv₁V) (D.V_le_A hv₂V)
    have hmemC : b₁ * b₂ ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have c1 : Commute b₁ x := hb₁ x hx
      have c2 : Commute b₂ x := hb₂ x hx
      exact (c1.mul_left c2).eq.symm
    have hmem : b₁ * b₂ ∈ A ⊓ Subgroup.centralizer (K : Set G) := ⟨hmemA, hmemC⟩
    rw [hCK] at hmem
    have h1 : (u * z) * v₂ = 1 := hb12.trans (Subgroup.mem_bot.mp hmem)
    have h2 : v₂ = (u * z)⁻¹ := eq_inv_of_mul_eq_one_right h1
    exact hv₁₂ (by rw [h2, inv_eq_of_mul_eq_one_right hv₁sq])
  have hcommV : ∀ g : G, g * (u * z) = (u * z) * g → g * v₂ = v₂ * g →
      ∀ v ∈ V, g * v = v * g := by
    intro g h1 h2 v hv
    rcases hVc v hv with rfl | rfl | rfl | rfl
    · simp
    · exact h1
    · exact h2
    · exact (Commute.mul_right (show Commute g (u * z) from h1) (show Commute g v₂ from h2)).eq
  have hk₁v₁ : k₁ * (u * z) = (u * z) * k₁ := by
    rw [hv₁eq]
    calc k₁ * (k₁ * b₁) = k₁ * (b₁ * k₁) := by rw [hb₁ k₁ hk₁K]
      _ = (k₁ * b₁) * k₁ := by group
  have hk₁v₂ : k₁ * v₂ = v₂ * k₁ := by
    rw [hv₂eq]
    calc k₁ * (k₂ * b₂) = (k₁ * k₂) * b₂ := by group
      _ = (k₂ * k₁) * b₂ := by rw [hk₁₂comm]
      _ = k₂ * (k₁ * b₂) := by group
      _ = k₂ * (b₂ * k₁) := by rw [hbk₁]
      _ = (k₂ * b₂) * k₁ := by group
  have hk₂v₁ : k₂ * (u * z) = (u * z) * k₂ := by
    rw [hv₁eq]
    calc k₂ * (k₁ * b₁) = (k₂ * k₁) * b₁ := by group
      _ = (k₁ * k₂) * b₁ := by rw [hk₁₂comm]
      _ = k₁ * (k₂ * b₁) := by group
      _ = k₁ * (b₁ * k₂) := by rw [hbk₂]
      _ = (k₁ * b₁) * k₂ := by group
  have hk₂v₂ : k₂ * v₂ = v₂ * k₂ := by
    rw [hv₂eq]
    calc k₂ * (k₂ * b₂) = k₂ * (b₂ * k₂) := by rw [hb₂ k₂ hk₂K]
      _ = (k₂ * b₂) * k₂ := by group
  have hkV₁ := hcommV k₁ hk₁v₁ hk₁v₂
  have hkV₂ := hcommV k₂ hk₂v₁ hk₂v₂
  have hk₁u : k₁ * u = u * k₁ := hu k₁ (hKG hk₁K)
  have hk₂u : k₂ * u = u * k₂ := hu k₂ (hKG hk₂K)
  have hVea : IsElemAbelian 2 V := isElemAbelian_iff.mpr ⟨hVcomm, D.hA.sq_U⟩
  have hVu : ∀ w ∈ V, w * u = u * w := fun w hw => hu w (hAG w (D.V_le_A hw))
  have hP := adjoin_involution hVea D.u_sq' hVu D.u_not_mem_V
  set P : Subgroup G := V ⊔ Subgroup.zpowers u with hPdef
  have hVz : ∀ a ∈ V, ∀ b ∈ Subgroup.zpowers u, a * b = b * a := by
    rintro a ha _ ⟨n, rfl⟩
    exact (Commute.zpow_right (show Commute a u from hVu a ha) n).eq
  have hcu : c * u = u * c := hu c hcG
  have hcu' : u * c⁻¹ = c⁻¹ * u := (Commute.inv_right (show Commute u c from hcu.symm)).eq
  have hPK : ∀ x ∈ P, x ∈ K → x = 1 := by
    intro x hxP hxK
    obtain ⟨w, hwV, g, hgz, hx⟩ := mem_sup_of_commute hVz hxP
    rcases (mem_zpowers_two D.u_sq' g).mp hgz with hg1 | hgu
    · rw [hg1, mul_one] at hx
      rw [← hx] at hxK ⊢
      exact hVK w hwV hxK
    · exfalso
      rw [hgu] at hx
      rw [← hx] at hxK
      have hw'V : c * w * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcNV w).mp hwV
      have hx'K : c * (w * u) * c⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hcK _).mp hxK
      have hcomp : c * (w * u) * c⁻¹ = (c * w * c⁻¹) * u := by
        calc c * (w * u) * c⁻¹ = c * w * (u * c⁻¹) := by group
          _ = c * w * (c⁻¹ * u) := by rw [hcu']
          _ = (c * w * c⁻¹) * u := by group
      have hrat : (c * w * c⁻¹) * w⁻¹ ∈ K := by
        have := K.mul_mem hx'K (K.inv_mem hxK)
        rwa [hcomp, show (c * w * c⁻¹) * u * (w * u)⁻¹ = (c * w * c⁻¹) * w⁻¹ by group] at this
      have hrat1 : (c * w * c⁻¹) * w⁻¹ = 1 :=
        hVK _ (V.mul_mem hw'V (V.inv_mem hwV)) hrat
      have hcw : c * w * c⁻¹ = w := by
        calc c * w * c⁻¹ = ((c * w * c⁻¹) * w⁻¹) * w := by group
          _ = w := by rw [hrat1, one_mul]
      have hw1 : w = 1 := by
        by_contra hw1
        exact hcfp w hwV hw1 hcw
      subst hw1
      rw [one_mul] at hxK
      exact D.u_ne_one (hZK u hxK fun k' hk' => (hu k' (hKG hk')).symm)
  have hPcomm : ∀ g : G, (∀ v ∈ V, g * v = v * g) → g * u = u * g →
      ∀ p ∈ P, g * p = p * g := by
    intro g hgV hgu p hp
    obtain ⟨w, hwV, y, hy, rfl⟩ := mem_sup_of_commute hVz hp
    have hy' : g * y = y * g := by
      rcases (mem_zpowers_two D.u_sq' y).mp hy with hy1 | hyu
      · rw [hy1]
        simp
      · rw [hyu]
        exact hgu
    calc g * (w * y) = (g * w) * y := by group
      _ = (w * g) * y := by rw [hgV w hwV]
      _ = w * (g * y) := by group
      _ = w * (y * g) := by rw [hy']
      _ = (w * y) * g := by group
  have hk₁P : ∀ p ∈ P, p * k₁ = k₁ * p := fun p hp => (hPcomm k₁ hkV₁ hk₁u p hp).symm
  have hk₁P' : k₁ ∉ P := fun hk => hk₁1 (hPK k₁ hk hk₁K)
  obtain ⟨hQ₁e, hQ₁c⟩ := adjoin_involution hP.1 hk₁sq hk₁P hk₁P'
  set Q₁ : Subgroup G := P ⊔ Subgroup.zpowers k₁ with hQ₁def
  have hPk : ∀ p ∈ P, ∀ y ∈ Subgroup.zpowers k₁, p * y = y * p := by
    rintro p hp _ ⟨n, rfl⟩
    exact (Commute.zpow_right (show Commute p k₁ from hk₁P p hp) n).eq
  have hk₂Q : ∀ q ∈ Q₁, q * k₂ = k₂ * q := by
    intro q hq
    obtain ⟨p, hp, y, hy, rfl⟩ := mem_sup_of_commute hPk hq
    have h1 : p * k₂ = k₂ * p := (hPcomm k₂ hkV₂ hk₂u p hp).symm
    have h2 : y * k₂ = k₂ * y := by
      rcases (mem_zpowers_two hk₁sq y).mp hy with hy1 | hyk
      · rw [hy1]
        simp
      · rw [hyk]
        exact hk₁₂comm
    calc p * y * k₂ = p * (y * k₂) := by group
      _ = p * (k₂ * y) := by rw [h2]
      _ = (p * k₂) * y := by group
      _ = (k₂ * p) * y := by rw [h1]
      _ = k₂ * (p * y) := by group
  have hk₂Q' : k₂ ∉ Q₁ := by
    intro hk
    obtain ⟨p, hp, y, hy, hpy⟩ := mem_sup_of_commute hPk hk
    have hyK : y ∈ K := by
      rcases (mem_zpowers_two hk₁sq y).mp hy with hy1 | hyk
      · rw [hy1]
        exact K.one_mem
      · rw [hyk]
        exact hk₁K
    have hpK : p ∈ K := by
      have : p = k₂ * y⁻¹ := by rw [← hpy]; group
      rw [this]
      exact K.mul_mem hk₂K (K.inv_mem hyK)
    have hp1 : p = 1 := hPK p hp hpK
    rw [hp1, one_mul] at hpy
    rcases (mem_zpowers_two hk₁sq y).mp hy with h | h
    · exact hk₂1 (hpy.symm.trans h)
    · exact hk₁₂ne (h.symm.trans hpy)
  obtain ⟨hQ₂e, hQ₂c⟩ := adjoin_involution hQ₁e hk₂sq hk₂Q hk₂Q'
  set Q₂ : Subgroup G := Q₁ ⊔ Subgroup.zpowers k₂ with hQ₂def
  have hQ₂T : Q₂ ≤ T := by
    have hD0 : Q₂ ≤ Gu ⊓ Subgroup.centralizer ({u * z} : Set G) := by
      refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
      · intro v hv
        exact ⟨hAG v (D.V_le_A hv), Subgroup.mem_centralizer_singleton_iff.mpr
          (hVcomm v hv _ hv₁V)⟩
      · refine Subgroup.zpowers_le.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, ?_⟩
        refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
        calc u * (u * z) = u * (z * u) := by rw [D.uz_comm]
          _ = (u * z) * u := by group
      · refine Subgroup.zpowers_le.mpr ⟨hKG hk₁K, Subgroup.mem_centralizer_singleton_iff.mpr hk₁v₁⟩
      · refine Subgroup.zpowers_le.mpr ⟨hKG hk₂K, Subgroup.mem_centralizer_singleton_iff.mpr hk₂v₁⟩
    intro q hq
    exact (mem_Tu_of_commute_uz D (hD0 hq).1
      (Subgroup.mem_centralizer_singleton_iff.mp (hD0 hq).2)).1
  have hcard : Nat.card ↥Q₂ = 32 := by
    have h1 := hQ₂c
    have h2 := hQ₁c
    have h3 := hP.2
    omega
  have := hmax Q₂ hQ₂T hQ₂e
  omega

end StageV

end CFSG.QuasithinUnique.A5.Insp
