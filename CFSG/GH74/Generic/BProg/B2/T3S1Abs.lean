module

public import CFSG.GH74.Generic.Front.Transport
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.GH74.Generic.BProg.B2.T3S1

open CFSG CFSG.GH74 CFSG.GH74.Generic Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner perfect_action_inner)

@[expose] def IsE8 {K : Type*} [Group K] (E : Subgroup K) : Prop :=
  CFSG.IsElementaryAbelian 2 ↥E ∧ Nat.card ↥E = 8

@[expose] def GoodFixedQ8 {K : Type*} [Group K] (T : Prop) (α : MulAut K) : Prop :=
  ∃ H : Subgroup K, (∀ h ∈ H, α h = h) ∧ GoodSub T H ∧
    ∃ a ∈ H, ∃ b ∈ H, a * a ∈ center K ∧ a * a ≠ 1 ∧ b * b = a * a ∧ a * b = a * a * (b * a)

structure S1Facts (K : Type) [Group K] : Prop where
  center : ∃ z : K, z ≠ 1 ∧ (∀ g : K, g ∈ Subgroup.center K ↔ g = 1 ∨ g = z) ∧
    ∀ E : Subgroup K, IsE8 E → z ∈ E
  conj : ∀ E E' : Subgroup K, IsE8 E → IsE8 E' → ∃ k : K, E' = E.map (MulAut.conj k).toMonoidHom
  invol : ∀ t : K, t * t = 1 → ∃ E : Subgroup K, IsE8 E ∧ t ∈ E
  dich : ∀ α : MulAut K, α * α = 1 →
    (∃ E : Subgroup K, IsE8 E ∧ ∀ e ∈ E, α e = e) ∨ GoodFixedQ8 (ThreeModel K) α

section Transport

variable {K K' : Type} [Group K] [Group K']

theorem isE8_map (e : K ≃* K') {E : Subgroup K} (hE : IsE8 E) : IsE8 (E.map e.toMonoidHom) := by
  have := hE.1
  refine ⟨IsElementaryAbelian.map e.toMonoidHom, ?_⟩
  rw [Subgroup.card_map_of_injective e.injective]
  exact hE.2

theorem map_symm_map (e : K ≃* K') (E : Subgroup K') :
    (E.map e.symm.toMonoidHom).map e.toMonoidHom = E := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id E
  ext g
  simp

theorem threeModel_of_mulEquiv (e : K ≃* K') (h : ThreeModel K) : ThreeModel K' := by
  obtain ⟨F, hF, hFin, h3, h⟩ := h
  refine ⟨F, hF, hFin, h3, ?_⟩
  rcases h with ⟨⟨e'⟩⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨e.symm.trans e'⟩
  · exact Or.inr ⟨e.symm.trans e'⟩

theorem goodSub_map_equiv (e : K ≃* K') {T T' : Prop} (hT : T → T') {H : Subgroup K}
    (hH : GoodSub T H) : GoodSub T' (H.map e.toMonoidHom) :=
  GoodSub.mono hT (goodSub_map e.toMonoidHom hH)

theorem GoodFixedQ8.of_mulEquiv (e : K ≃* K') {T T' : Prop} (hT : T → T') {α : MulAut K}
    (hα : GoodFixedQ8 T α) : GoodFixedQ8 T' (MulAut.congr e α) := by
  obtain ⟨H, hfix, hgood, a, ha, b, hb, hac, ha1, hbb, hab⟩ := hα
  refine ⟨H.map e.toMonoidHom, ?_, goodSub_map_equiv e hT hgood, e a, ⟨a, ha, rfl⟩, e b,
    ⟨b, hb, rfl⟩, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨h, hh, rfl⟩
    change e (α (e.symm (e h))) = e h
    rw [MulEquiv.symm_apply_apply, hfix h hh]
  · rw [← map_mul, Subgroup.mem_center_iff]
    intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hac g')]
  · rw [← map_mul]
    intro h
    exact ha1 (e.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, hbb]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hab]

theorem S1Facts.of_mulEquiv (e : K ≃* K') (h : S1Facts K) : S1Facts K' := by
  obtain ⟨⟨z, hz1, hzc, hzE⟩, hconj, hinv, hdich⟩ := h
  refine ⟨⟨e z, fun h => hz1 (e.injective (by rw [h, map_one])), ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g
    obtain ⟨g', rfl⟩ := e.surjective g
    have hc : e g' ∈ Subgroup.center K' ↔ g' ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
      constructor
      · intro hg a
        apply e.injective
        rw [map_mul, map_mul]
        exact hg (e a)
      · intro hg a
        obtain ⟨a', rfl⟩ := e.surjective a
        rw [← map_mul, ← map_mul, hg a']
    rw [hc, hzc g']
    constructor
    · rintro (rfl | rfl)
      · left; exact map_one e
      · right; rfl
    · rintro (h | h)
      · left; exact e.injective (by rw [h, map_one])
      · right; exact e.injective h
  · intro E hE
    have hE' : IsE8 (E.map e.symm.toMonoidHom) := isE8_map e.symm hE
    have hz := hzE _ hE'
    rw [← map_symm_map e E]
    exact ⟨z, hz, rfl⟩
  · intro E E' hE hE'
    obtain ⟨k, hk⟩ := hconj _ _ (isE8_map e.symm hE) (isE8_map e.symm hE')
    refine ⟨e k, ?_⟩
    have h1 : E' = ((E.map e.symm.toMonoidHom).map (MulAut.conj k).toMonoidHom).map e.toMonoidHom := by
      rw [← hk, map_symm_map]
    rw [h1, Subgroup.map_map, Subgroup.map_map]
    congr 1
    refine MonoidHom.ext fun a => ?_
    simp [MulAut.conj_apply, map_mul, map_inv]
  · intro t ht
    have ht' : e.symm t * e.symm t = 1 := by rw [← map_mul, ht, map_one]
    obtain ⟨E, hE, htE⟩ := hinv _ ht'
    refine ⟨E.map e.toMonoidHom, isE8_map e hE, ⟨_, htE, ?_⟩⟩
    simp
  · intro α hα
    set β : MulAut K := MulAut.congr e.symm α with hβ
    have hβ2 : β * β = 1 := by
      rw [hβ, ← map_mul, hα, map_one]
    have hαβ : MulAut.congr e β = α := by
      rw [hβ]
      ext g
      simp
    rcases hdich β hβ2 with ⟨E, hE, hfix⟩ | hQ
    · left
      refine ⟨E.map e.toMonoidHom, isE8_map e hE, ?_⟩
      rintro _ ⟨a, ha, rfl⟩
      rw [← hαβ]
      change e (β (e.symm (e a))) = e a
      rw [MulEquiv.symm_apply_apply, hfix a ha]
    · right
      rw [← hαβ]
      exact GoodFixedQ8.of_mulEquiv e (threeModel_of_mulEquiv e) hQ

end Transport

theorem mem_of_quaternion {X : Type*} [Group X] {L C : Subgroup X}
    (hLC : ∀ l ∈ L, ∀ c ∈ C, l * c = c * l) {z : X} (hzL : z ∈ L) (hz1 : z ≠ 1)
    (hLCz : ∀ g ∈ L, g ∈ C → g = 1 ∨ g = z) (hCinv : ∀ c ∈ C, c * c = 1 → c = 1 ∨ c = z)
    {i j t : X} (hi : ∃ l ∈ L, ∃ c ∈ C, i = l * c) (hj : ∃ l ∈ L, ∃ c ∈ C, j = l * c)
    (hii : i * i = t) (hjj : j * j = t) (htt : t * t = 1) (hij : i * j = t * (j * i)) : t ∈ L := by
  obtain ⟨l₁, hl₁, c₁, hc₁, rfl⟩ := hi
  obtain ⟨l₂, hl₂, c₂, hc₂, rfl⟩ := hj
  have hsq : ∀ {l c : X}, l ∈ L → c ∈ C → l * c * (l * c) = (l * l) * (c * c) := by
    intro l c hl hc
    calc l * c * (l * c) = l * (c * l) * c := by group
      _ = l * (l * c) * c := by rw [hLC l hl c hc]
      _ = (l * l) * (c * c) := by group
  have hsq1 : t = (l₁ * l₁) * (c₁ * c₁) := by rw [← hii, hsq hl₁ hc₁]
  have hsq2 : t = (l₂ * l₂) * (c₂ * c₂) := by rw [← hjj, hsq hl₂ hc₂]
  by_contra htL
  set u := c₁ * c₁ with hu
  have huC : u ∈ C := C.mul_mem hc₁ hc₁
  have hL11 : l₁ * l₁ ∈ L := L.mul_mem hl₁ hl₁
  have hL22 : l₂ * l₂ ∈ L := L.mul_mem hl₂ hl₂
  have huL : u ∉ L := fun h => htL (hsq1 ▸ L.mul_mem hL11 h)
  have huu : u * u = z := by
    have hcomm : (l₁ * l₁) * u = u * (l₁ * l₁) := hLC _ hL11 u huC
    have h1 : (l₁ * l₁) * u * ((l₁ * l₁) * u) = 1 := by rw [← hsq1]; exact htt
    have h2 : (l₁ * l₁) * (l₁ * l₁) * (u * u) = 1 := by
      calc (l₁ * l₁) * (l₁ * l₁) * (u * u) = (l₁ * l₁) * ((l₁ * l₁) * u) * u := by group
        _ = (l₁ * l₁) * (u * (l₁ * l₁)) * u := by rw [hcomm]
        _ = (l₁ * l₁) * u * ((l₁ * l₁) * u) := by group
        _ = 1 := h1
    have h3 : u * u = ((l₁ * l₁) * (l₁ * l₁))⁻¹ := eq_inv_of_mul_eq_one_right h2
    have hmemL : u * u ∈ L := h3 ▸ L.inv_mem (L.mul_mem hL11 hL11)
    rcases hLCz _ hmemL (C.mul_mem huC huC) with h | h
    · exfalso
      rcases hCinv u huC h with h' | h'
      · exact huL (h' ▸ L.one_mem)
      · exact huL (h' ▸ hzL)
    · exact h
  have hzC : z ∈ C := huu ▸ C.mul_mem huC huC
  have hzz : z * z = 1 := by
    rcases hLCz _ (L.mul_mem hzL hzL) (C.mul_mem hzC hzC) with h | h
    · exact h
    · exfalso
      apply hz1
      calc z = z * z * z⁻¹ := by group
        _ = z * z⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel z
  have hzc : ∀ c ∈ C, z * c = c * z := fun c hc => hLC z hzL c hc
  have hc2 : c₂ * c₂ = u ∨ c₂ * c₂ = z * u := by
    have h1 : (l₂ * l₂) * (c₂ * c₂) = (l₁ * l₁) * u := by rw [← hsq1, ← hsq2]
    have h2 : c₂ * c₂ * u⁻¹ = (l₂ * l₂)⁻¹ * (l₁ * l₁) := by
      have hcomm : (l₁ * l₁) * u = u * (l₁ * l₁) := hLC _ hL11 u huC
      calc c₂ * c₂ * u⁻¹ = (l₂ * l₂)⁻¹ * ((l₂ * l₂) * (c₂ * c₂)) * u⁻¹ := by group
        _ = (l₂ * l₂)⁻¹ * ((l₁ * l₁) * u) * u⁻¹ := by rw [h1]
        _ = (l₂ * l₂)⁻¹ * (l₁ * l₁) := by group
    have hmL : c₂ * c₂ * u⁻¹ ∈ L := h2 ▸ L.mul_mem (L.inv_mem hL22) hL11
    have hmC : c₂ * c₂ * u⁻¹ ∈ C := C.mul_mem (C.mul_mem hc₂ hc₂) (C.inv_mem huC)
    rcases hLCz _ hmL hmC with h | h
    · left
      exact mul_inv_eq_one.1 h
    · right
      calc c₂ * c₂ = c₂ * c₂ * u⁻¹ * u := by group
        _ = z * u := by rw [h]
  obtain ⟨w, hw, hwC⟩ : ∃ w : X, (w = 1 ∨ w = z) ∧ c₂ * c₁ * c₂⁻¹ = c₁⁻¹ * w := by
    have hji : (l₂ * c₂) * (l₁ * c₁) * (l₂ * c₂)⁻¹ = (l₁ * c₁)⁻¹ := by
      have e1 : l₁ * c₁ * (l₂ * c₂) = (l₁ * c₁) * (l₁ * c₁) * ((l₂ * c₂) * (l₁ * c₁)) := by
        rw [hii]; exact hij
      have e2 : l₂ * c₂ = (l₁ * c₁) * ((l₂ * c₂) * (l₁ * c₁)) := by
        have := congrArg (fun g => (l₁ * c₁)⁻¹ * g) e1
        simpa [mul_assoc] using this
      calc (l₂ * c₂) * (l₁ * c₁) * (l₂ * c₂)⁻¹
          = (l₂ * c₂) * (l₁ * c₁) * ((l₁ * c₁) * ((l₂ * c₂) * (l₁ * c₁)))⁻¹ := by rw [← e2]
        _ = (l₁ * c₁)⁻¹ := by group
    have hsplit : (l₂ * c₂) * (l₁ * c₁) * (l₂ * c₂)⁻¹ =
        (l₂ * l₁ * l₂⁻¹) * (c₂ * c₁ * c₂⁻¹) := by
      have h1 : c₂ * l₁ = l₁ * c₂ := (hLC l₁ hl₁ c₂ hc₂).symm
      have h2 : c₁ * l₂⁻¹ = l₂⁻¹ * c₁ := (hLC _ (L.inv_mem hl₂) c₁ hc₁).symm
      have h3 : c₂⁻¹ * l₂⁻¹ = l₂⁻¹ * c₂⁻¹ := (hLC _ (L.inv_mem hl₂) _ (C.inv_mem hc₂)).symm
      calc (l₂ * c₂) * (l₁ * c₁) * (l₂ * c₂)⁻¹ = l₂ * (c₂ * l₁) * c₁ * (c₂⁻¹ * l₂⁻¹) := by group
        _ = l₂ * (l₁ * c₂) * c₁ * (l₂⁻¹ * c₂⁻¹) := by rw [h1, h3]
        _ = l₂ * l₁ * c₂ * (c₁ * l₂⁻¹) * c₂⁻¹ := by group
        _ = l₂ * l₁ * c₂ * (l₂⁻¹ * c₁) * c₂⁻¹ := by rw [h2]
        _ = l₂ * l₁ * (c₂ * l₂⁻¹) * c₁ * c₂⁻¹ := by group
        _ = l₂ * l₁ * (l₂⁻¹ * c₂) * c₁ * c₂⁻¹ := by
            rw [(hLC _ (L.inv_mem hl₂) c₂ hc₂).symm]
        _ = (l₂ * l₁ * l₂⁻¹) * (c₂ * c₁ * c₂⁻¹) := by group
    have hinv : (l₁ * c₁)⁻¹ = l₁⁻¹ * c₁⁻¹ := by
      rw [mul_inv_rev]
      exact (hLC _ (L.inv_mem hl₁) _ (C.inv_mem hc₁)).symm
    rw [hsplit, hinv] at hji
    set w : X := c₁ * (c₂ * c₁ * c₂⁻¹) with hwdef
    have hwC : w ∈ C := C.mul_mem hc₁ (C.mul_mem (C.mul_mem hc₂ hc₁) (C.inv_mem hc₂))
    have hwL : w ∈ L := by
      have e : w = (l₂ * l₁ * l₂⁻¹)⁻¹ * l₁⁻¹ := by
        have hc1L : c₁ * (l₂ * l₁ * l₂⁻¹)⁻¹ = (l₂ * l₁ * l₂⁻¹)⁻¹ * c₁ :=
          (hLC _ (L.inv_mem (L.mul_mem (L.mul_mem hl₂ hl₁) (L.inv_mem hl₂))) c₁ hc₁).symm
        have hc1L' : c₁ * l₁⁻¹ = l₁⁻¹ * c₁ := (hLC _ (L.inv_mem hl₁) c₁ hc₁).symm
        calc w = c₁ * ((l₂ * l₁ * l₂⁻¹)⁻¹ * ((l₂ * l₁ * l₂⁻¹) * (c₂ * c₁ * c₂⁻¹))) := by
              rw [hwdef]; group
          _ = c₁ * ((l₂ * l₁ * l₂⁻¹)⁻¹ * (l₁⁻¹ * c₁⁻¹)) := by rw [hji]
          _ = (c₁ * (l₂ * l₁ * l₂⁻¹)⁻¹) * l₁⁻¹ * c₁⁻¹ := by group
          _ = (l₂ * l₁ * l₂⁻¹)⁻¹ * (c₁ * l₁⁻¹) * c₁⁻¹ := by rw [hc1L]; group
          _ = (l₂ * l₁ * l₂⁻¹)⁻¹ * (l₁⁻¹ * c₁) * c₁⁻¹ := by rw [hc1L']
          _ = (l₂ * l₁ * l₂⁻¹)⁻¹ * l₁⁻¹ := by group
      rw [e]
      exact L.mul_mem (L.inv_mem (L.mul_mem (L.mul_mem hl₂ hl₁) (L.inv_mem hl₂))) (L.inv_mem hl₁)
    refine ⟨w, hLCz w hwL hwC, ?_⟩
    rw [hwdef]
    group
  have hwc : w * c₁⁻¹ = c₁⁻¹ * w := by
    rcases hw with rfl | rfl
    · group
    · exact hzc _ (C.inv_mem hc₁)
  have hww : w * w = 1 := by rcases hw with rfl | rfl <;> simp [hzz]
  have hcu : c₂ * u * c₂⁻¹ = u⁻¹ := by
    calc c₂ * u * c₂⁻¹ = (c₂ * c₁ * c₂⁻¹) * (c₂ * c₁ * c₂⁻¹) := by rw [hu]; group
      _ = c₁⁻¹ * w * (c₁⁻¹ * w) := by rw [hwC]
      _ = c₁⁻¹ * (w * c₁⁻¹) * w := by group
      _ = c₁⁻¹ * (c₁⁻¹ * w) * w := by rw [hwc]
      _ = c₁⁻¹ * c₁⁻¹ * (w * w) := by group
      _ = u⁻¹ := by rw [hww, hu]; group
  have huinv : u⁻¹ = u := by
    rcases hc2 with h | h
    · calc u⁻¹ = c₂ * u * c₂⁻¹ := hcu.symm
        _ = c₂ * (c₂ * c₂) * c₂⁻¹ := by rw [h]
        _ = c₂ * c₂ := by group
        _ = u := h
    · have hz2 : c₂ * z = z * c₂ := (hzc c₂ hc₂).symm
      have : z * u⁻¹ = z * u := by
        calc z * u⁻¹ = z * (c₂ * u * c₂⁻¹) := by rw [hcu]
          _ = (z * c₂) * u * c₂⁻¹ := by group
          _ = (c₂ * z) * u * c₂⁻¹ := by rw [hz2]
          _ = c₂ * (z * u) * c₂⁻¹ := by group
          _ = c₂ * (c₂ * c₂) * c₂⁻¹ := by rw [h]
          _ = c₂ * c₂ := by group
          _ = z * u := h
      exact mul_left_cancel this
  apply hz1
  rw [← huu]
  calc u * u = u * u⁻¹ := by rw [huinv]
    _ = 1 := mul_inv_cancel u

theorem mem_sup_of_conjNormal_inner {X : Type*} [Group X] {K : Subgroup X} [K.Normal] {g : X} {k : ↥K}
    (h : (MulAut.conjNormal g : MulAut ↥K) = MulAut.conj k) :
    g ∈ K ⊔ Subgroup.centralizer (K : Set X) := by
  have hc : (k : X)⁻¹ * g ∈ Subgroup.centralizer (K : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 := congrArg (fun σ : MulAut ↥K => ((σ ⟨n, hn⟩ : ↥K) : X)) h
    simp only [MulAut.conjNormal_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      at h1
    have h2 : (k : X)⁻¹ * g * n = n * ((k : X)⁻¹ * g) := by
      calc (k : X)⁻¹ * g * n = (k : X)⁻¹ * (g * n * g⁻¹) * g := by group
        _ = (k : X)⁻¹ * ((k : X) * n * (k : X)⁻¹) * g := by rw [h1]
        _ = n * ((k : X)⁻¹ * g) := by group
    exact h2.symm
  have : (k : X) * ((k : X)⁻¹ * g) ∈ K ⊔ Subgroup.centralizer (K : Set X) :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hc)
  simpa using this

theorem goodSub_le_sup_centralizer {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    {T : Prop} (hsolv : Group.IsSolvable (Outer ↥K))
    (hodd : T → ∀ o : Outer ↥K, Odd (orderOf o) → o = 1) :
    ∀ P : Subgroup X, GoodSub T P → P ≤ K ⊔ Subgroup.centralizer (K : Set X) := by
  intro P hP
  let act : ↥P →* MulAut ↥K := (MulAut.conjNormal : X →* MulAut ↥K).comp P.subtype
  rcases hP with hperf | ⟨hgen, hT⟩
  · have : Group.IsPerfect ↥P := Subgroup.isPerfect_iff.2 hperf
    intro p hp
    obtain ⟨k, hk⟩ := perfect_action_inner act ⟨p, hp⟩
    exact mem_sup_of_conjNormal_inner hk
  · rw [← hgen]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨hgP, hgodd⟩
    have hmem : (QuotientGroup.mk' (inner ↥K)) (act ⟨g, hgP⟩) = 1 := by
      apply hodd hT
      have h1 := orderOf_map_dvd (QuotientGroup.mk' (inner ↥K)) (act ⟨g, hgP⟩)
      have h2 := orderOf_map_dvd act (⟨g, hgP⟩ : ↥P)
      rw [Subgroup.orderOf_mk] at h2
      exact Odd.of_dvd_nat hgodd (h1.trans h2)
    obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff _).1 hmem
    exact mem_sup_of_conjNormal_inner (by simpa [act] using hk.symm)

theorem exists_lift_two {G H : Type*} [Group G] [Finite G] [Group H] [Finite H] (ρ : G →* H)
    (hker : ¬ 2 ∣ Nat.card ρ.ker) (E : Subgroup H) (hE : E ≤ ρ.range) (hE2 : IsPGroup 2 ↥E)
    {x : G} {n : ℕ} (hx : x ^ (2 ^ n) = 1) (hxE : ρ x ∈ E) :
    ∃ S : Subgroup G, x ∈ S ∧ S.map ρ = E ∧ ∀ s ∈ S, ρ s = 1 → s = 1 := by
  classical
  have hp : Nat.Prime 2 := Nat.prime_two
  have : Fact (Nat.Prime 2) := ⟨hp⟩
  obtain ⟨k, hEcard⟩ := hE2.exists_card_eq
  set P' : Subgroup G := E.comap ρ with hP'
  let f : P' →* E := (ρ.comp P'.subtype).codRestrict E fun x => x.2
  have hfsurj : Function.Surjective f := fun e => by
    obtain ⟨g, hg⟩ := hE e.2
    exact ⟨⟨g, show ρ g ∈ E by rw [hg]; exact e.2⟩, Subtype.ext hg⟩
  have hfx : ∀ x : P', (f x : H) = ρ x := fun x => rfl
  have hkerf : Nat.card f.ker = Nat.card ρ.ker := by
    refine Nat.card_congr ⟨fun x => ⟨x.1.1, ?_⟩, fun x => ⟨⟨x.1, ?_⟩, ?_⟩, ?_, ?_⟩
    · have := x.2
      rw [MonoidHom.mem_ker] at this ⊢
      have h2 := congrArg Subtype.val this
      rwa [hfx] at h2
    · show ρ x.1 ∈ E
      rw [MonoidHom.mem_ker.mp x.2]; exact E.one_mem
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [hfx]
      exact MonoidHom.mem_ker.mp x.2
    · intro x; rfl
    · intro x; rfl
  have hPc : Nat.card P' = Nat.card ρ.ker * 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, hEcard,
      hkerf] at h1
    rw [h1, mul_comm]
  set x' : P' := ⟨x, hxE⟩ with hx'
  have hx'2 : x' ^ (2 ^ n) = 1 := Subtype.ext (by simpa [hx'] using hx)
  obtain ⟨S, hxS⟩ := (isPGroup_zpowers_of_pow_two_pow_eq_one hx'2).exists_le_sylow
  have hScard : Nat.card S = 2 ^ k := by
    rw [Sylow.card_eq_multiplicity, hPc, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero k hp.ne_zero), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker, Nat.Prime.factorization_pow hp]
    simp
  have key : ∀ x ∈ S.map P'.subtype, ρ x = 1 → x = 1 := by
    intro x hx hρx
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    have h1 : orderOf (x' : G) ∣ 2 ^ k := by
      rw [← hScard]
      have := Subgroup.orderOf_dvd_natCard (S : Subgroup P') hx'
      simpa [Subgroup.orderOf_coe] using this
    have h2 : orderOf (x' : G) ∣ Nat.card ρ.ker := by
      have hmem : (x' : G) ∈ ρ.ker := hρx
      have := Subgroup.orderOf_dvd_natCard ρ.ker hmem
      simpa [Subgroup.orderOf_coe] using this
    have hcop : Nat.Coprime (2 ^ k) (Nat.card ρ.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hker)
    exact orderOf_eq_one_iff.mp
      (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  have hSinj : ∀ x ∈ S.map P'.subtype, ∀ y ∈ S.map P'.subtype, ρ x = ρ y → x = y := by
    intro x hx y hy hxy
    have : x * y⁻¹ = 1 := key _ (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy))
      (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
    exact mul_inv_eq_one.mp this
  set E₀ : Subgroup G := S.map P'.subtype with hE₀
  have hE₀card : Nat.card E₀ = 2 ^ k := by
    rw [hE₀, Subgroup.card_map_of_injective P'.subtype_injective, hScard]
  have hmapE : E₀.map ρ = E := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
      exact g'.2
    · have : Nat.card (E₀.map ρ) = Nat.card E₀ := by
        refine Nat.card_congr (Equiv.ofBijective
          (fun x : E₀ => ⟨ρ x, Subgroup.mem_map_of_mem _ x.2⟩) ⟨?_, ?_⟩).symm
        · intro x y hxy
          exact Subtype.ext (hSinj _ x.2 _ y.2 (congrArg Subtype.val hxy))
        · rintro ⟨_, g, hg, rfl⟩
          exact ⟨⟨g, hg⟩, rfl⟩
      rw [this, hE₀card, hEcard]
  refine ⟨E₀, ⟨x', hxS (Subgroup.mem_zpowers x'), rfl⟩, hmapE, key⟩

end CFSG.GH74.Generic.BProg.B2.T3S1
