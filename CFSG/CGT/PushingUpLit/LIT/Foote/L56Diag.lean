module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Top

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.CGT.PushingUpLit
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G]

theorem le_normalizer_of_forall {H K : Subgroup G} (h : ∀ k ∈ K, ∀ a ∈ H, k * a * k⁻¹ ∈ H) :
    K ≤ Subgroup.normalizer (H : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => h k hk a ha, fun ha => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) _ ha
  have e : k⁻¹ * (k * a * k⁻¹) * k⁻¹⁻¹ = a := by group
  rwa [e] at this

@[expose] def diagHom (B : Subgroup G) (u : G)
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, b' * (u⁻¹ * b * u) = (u⁻¹ * b * u) * b') : ↥B →* G :=
  MonoidHom.mk' (fun b => (b : G) * (u⁻¹ * (b : G) * u)) (fun b b' => by
    have h := hcomm b b.2 b' b'.2
    show (b : G) * b' * (u⁻¹ * ((b : G) * b') * u) =
      ((b : G) * (u⁻¹ * b * u)) * ((b' : G) * (u⁻¹ * b' * u))
    calc (b : G) * b' * (u⁻¹ * ((b : G) * b') * u)
        = b * (b' * (u⁻¹ * b * u)) * (u⁻¹ * b' * u) := by group
      _ = b * ((u⁻¹ * b * u) * b') * (u⁻¹ * b' * u) := by rw [h]
      _ = ((b : G) * (u⁻¹ * b * u)) * ((b' : G) * (u⁻¹ * b' * u)) := by group)

theorem diagHom_apply {B : Subgroup G} {u : G}
    {hcomm : ∀ b ∈ B, ∀ b' ∈ B, b' * (u⁻¹ * b * u) = (u⁻¹ * b * u) * b'} (b : ↥B) :
    diagHom B u hcomm b = (b : G) * (u⁻¹ * (b : G) * u) := rfl

theorem diagHom_comm {B : Subgroup G} {u : G}
    {hcomm : ∀ b ∈ B, ∀ b' ∈ B, b' * (u⁻¹ * b * u) = (u⁻¹ * b * u) * b'} (hu : u * u = 1)
    (b : ↥B) : u * diagHom B u hcomm b = diagHom B u hcomm b * u := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h := hcomm b b.2 b b.2
  rw [diagHom_apply, hui]
  rw [hui] at h
  calc u * ((b : G) * (u * b * u)) = (u * b * u) * b * u := by group
    _ = b * (u * b * u) * u := by rw [← h]

theorem conj_diagHom_eq {B : Subgroup G} {u c : G}
    {hcomm : ∀ b ∈ B, ∀ b' ∈ B, b' * (u⁻¹ * b * u) = (u⁻¹ * b * u) * b'}
    (hcu : c * u = u * c) (b : ↥B) :
    c * diagHom B u hcomm b * c⁻¹ = (c * b * c⁻¹) * (u⁻¹ * (c * b * c⁻¹) * u) := by
  have hcu1 : c * u⁻¹ = u⁻¹ * c := by
    calc c * u⁻¹ = u⁻¹ * (u * c) * u⁻¹ := by group
      _ = u⁻¹ * (c * u) * u⁻¹ := by rw [hcu]
      _ = u⁻¹ * c := by group
  have hcu2 : u * c⁻¹ = c⁻¹ * u := by
    calc u * c⁻¹ = c⁻¹ * (c * u) * c⁻¹ := by group
      _ = c⁻¹ * (u * c) * c⁻¹ := by rw [hcu]
      _ = c⁻¹ * u := by group
  rw [diagHom_apply]
  calc c * ((b : G) * (u⁻¹ * b * u)) * c⁻¹ = (c * b * c⁻¹) * ((c * u⁻¹) * b * (u * c⁻¹)) := by
        group
    _ = (c * b * c⁻¹) * ((u⁻¹ * c) * b * (c⁻¹ * u)) := by rw [hcu1, hcu2]
    _ = (c * b * c⁻¹) * (u⁻¹ * (c * b * c⁻¹) * u) := by group

theorem conj_mem_range_diagHom {B : Subgroup G} {u c : G}
    {hcomm : ∀ b ∈ B, ∀ b' ∈ B, b' * (u⁻¹ * b * u) = (u⁻¹ * b * u) * b'} (hu : u * u = 1)
    (hBB' : ∀ b ∈ B, ∀ b' ∈ rightConjugate B u, b * b' = b' * b) (hcu : c * u = u * c)
    (hc : (∀ b ∈ B, c * b * c⁻¹ ∈ B) ∨ (∀ b ∈ B, c * b * c⁻¹ ∈ rightConjugate B u)) :
    ∀ k ∈ (diagHom B u hcomm).range, c * k * c⁻¹ ∈ (diagHom B u hcomm).range := by
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  rintro _ ⟨b, rfl⟩
  rw [conj_diagHom_eq hcu b]
  rcases hc with hc | hc
  · exact ⟨⟨c * b * c⁻¹, hc b b.2⟩, by rw [diagHom_apply]⟩
  · have hb1 : c * (b : G) * c⁻¹ ∈ rightConjugate B u := hc b b.2
    have hmem : u⁻¹ * (c * b * c⁻¹) * u ∈ B := by
      have := (mem_rightConjugate_iff B u _).1 hb1
      rw [hui] at this ⊢
      exact this
    refine ⟨⟨u⁻¹ * (c * b * c⁻¹) * u, hmem⟩, ?_⟩
    rw [diagHom_apply]
    show (u⁻¹ * (c * b * c⁻¹) * u) * (u⁻¹ * (u⁻¹ * (c * b * c⁻¹) * u) * u) =
      (c * b * c⁻¹) * (u⁻¹ * (c * b * c⁻¹) * u)
    have hcomm' := hBB' _ hmem _ hb1
    have e : u⁻¹ * (u⁻¹ * (c * b * c⁻¹) * u) * u = c * b * c⁻¹ := by
      rw [hui]
      calc u * (u * (c * b * c⁻¹) * u) * u = (u * u) * (c * b * c⁻¹) * (u * u) := by group
        _ = c * b * c⁻¹ := by rw [hu]; group
    rw [e, hcomm']

theorem centralizes_of_centralizes_fixed {X K : Subgroup G} {z : G}
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hXs : ∀ x ∈ X, x * x = 1)
    (hz2 : z * z = 1) (hzX : ∀ x ∈ X, z * x * z⁻¹ ∈ X)
    (hKX : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ ∈ X) (hKz : ∀ k ∈ K, k * z = z * k)
    (hKp : ⁅K, K⁆ = K)
    (hKC : ∀ k ∈ K, ∀ x ∈ X, z * x = x * z → k * x = x * k) :
    ∀ k ∈ K, ∀ x ∈ X, k * x = x * k := by
  have hz1 : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hxi : ∀ x ∈ X, x⁻¹ = x := fun x hx => inv_eq_of_mul_eq_one_right (hXs x hx)
  have hdz : ∀ x ∈ X, z * (x * (z * x * z⁻¹)) = (x * (z * x * z⁻¹)) * z := by
    intro x hx
    have hw := hzX x hx
    have e1 : z * (x * (z * x * z⁻¹)) = (z * x * z⁻¹) * x * z := by
      rw [hz1]
      group
    rw [e1, hXc _ hw x hx]
  have hfix : ∀ k ∈ K, ∀ x ∈ X, z * (k * x * k⁻¹ * x⁻¹) = (k * x * k⁻¹ * x⁻¹) * z := by
    intro k hk x hx
    have ha := hKX k hk x hx
    have hw := hzX x hx
    have hw' := hzX _ ha
    have hkd : k * (x * (z * x * z⁻¹)) = (x * (z * x * z⁻¹)) * k := hKC k hk _
      (X.mul_mem hx hw) (hdz x hx)
    have hkz := hKz k hk
    have h1 : (k * x * k⁻¹) * (z * (k * x * k⁻¹) * z⁻¹) = x * (z * x * z⁻¹) := by
      have e : (k * x * k⁻¹) * (z * (k * x * k⁻¹) * z⁻¹) =
          k * (x * (z * x * z⁻¹)) * k⁻¹ := by
        calc (k * x * k⁻¹) * (z * (k * x * k⁻¹) * z⁻¹)
            = k * x * (k⁻¹ * z * k) * x * (k⁻¹ * z⁻¹ * k) * k⁻¹ := by group
          _ = k * x * z * x * z⁻¹ * k⁻¹ := by
            have e1 : k⁻¹ * z * k = z := by
              calc k⁻¹ * z * k = k⁻¹ * (z * k) := by group
                _ = k⁻¹ * (k * z) := by rw [← hkz]
                _ = z := by group
            have e2 : k⁻¹ * z⁻¹ * k = z⁻¹ := by
              rw [hz1]
              exact e1
            rw [e1, e2]
          _ = k * (x * (z * x * z⁻¹)) * k⁻¹ := by group
      rw [e, hkd]
      group
    have hy : z * (k * x * k⁻¹ * x⁻¹) * z⁻¹ = k * x * k⁻¹ * x⁻¹ := by
      set a := k * x * k⁻¹ with ha_def
      set w := z * x * z⁻¹ with hw_def
      set w' := z * a * z⁻¹ with hw'_def
      have hai := hxi a ha
      have hxii := hxi x hx
      have hww : w * w = 1 := hXs w hw
      have h2 : a * w' = x * w := h1
      have hza : z * (a * x⁻¹) * z⁻¹ = w' * w⁻¹ := by
        rw [hw'_def, hw_def]
        group
      rw [hza]
      have h3 : w' = a⁻¹ * (x * w) := by
        rw [← h2]
        group
      rw [h3]
      have hwi := hxi w hw
      rw [hwi, hai, hxii]
      calc a * (x * w) * w = a * x * (w * w) := by group
        _ = a * x := by rw [hww, mul_one]
    calc z * (k * x * k⁻¹ * x⁻¹) = (z * (k * x * k⁻¹ * x⁻¹) * z⁻¹) * z := by group
      _ = (k * x * k⁻¹ * x⁻¹) * z := by rw [hy]
  have hC : ∀ k ∈ K, ∀ x ∈ X, k * x * k⁻¹ * x⁻¹ ∈ X ∧
      ∀ k' ∈ K, k' * (k * x * k⁻¹ * x⁻¹) = (k * x * k⁻¹ * x⁻¹) * k' := by
    intro k hk x hx
    have hmem : k * x * k⁻¹ * x⁻¹ ∈ X := X.mul_mem (hKX k hk x hx) (X.inv_mem hx)
    exact ⟨hmem, fun k' hk' => hKC k' hk' _ hmem (hfix k hk x hx)⟩
  have hcommact : ∀ k ∈ K, ∀ k' ∈ K, ∀ x ∈ X,
      k * (k' * x * k'⁻¹) * k⁻¹ = k' * (k * x * k⁻¹) * k'⁻¹ := by
    intro k hk k' hk' x hx
    obtain ⟨hc1, hc1k⟩ := hC k hk x hx
    obtain ⟨hc2, hc2k⟩ := hC k' hk' x hx
    obtain ⟨c₁, hc1_def⟩ : ∃ c₁ : G, c₁ = k * x * k⁻¹ * x⁻¹ := ⟨_, rfl⟩
    obtain ⟨c₂, hc2_def⟩ : ∃ c₂ : G, c₂ = k' * x * k'⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hc1_def] at hc1 hc1k
    rw [← hc2_def] at hc2 hc2k
    have e1 : k * x * k⁻¹ = c₁ * x := by rw [hc1_def]; group
    have e2 : k' * x * k'⁻¹ = c₂ * x := by rw [hc2_def]; group
    have h1 : k * (c₂ * x) * k⁻¹ = c₂ * (c₁ * x) := by
      have : k * c₂ = c₂ * k := hc2k k hk
      calc k * (c₂ * x) * k⁻¹ = (k * c₂) * x * k⁻¹ := by group
        _ = (c₂ * k) * x * k⁻¹ := by rw [this]
        _ = c₂ * (k * x * k⁻¹) := by group
        _ = c₂ * (c₁ * x) := by rw [e1]
    have h2 : k' * (c₁ * x) * k'⁻¹ = c₁ * (c₂ * x) := by
      have : k' * c₁ = c₁ * k' := hc1k k' hk'
      calc k' * (c₁ * x) * k'⁻¹ = (k' * c₁) * x * k'⁻¹ := by group
        _ = (c₁ * k') * x * k'⁻¹ := by rw [this]
        _ = c₁ * (k' * x * k'⁻¹) := by group
        _ = c₁ * (c₂ * x) := by rw [e2]
    rw [e2, e1, h1, h2, ← mul_assoc, ← mul_assoc, hXc c₂ hc2 c₁ hc1]
  have hcomm : ⁅K, K⁆ ≤ Subgroup.centralizer (X : Set G) := by
    refine Subgroup.commutator_le.2 fun k hk k' hk' => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h := hcommact k⁻¹ (K.inv_mem hk) k'⁻¹ (K.inv_mem hk') x hx
    have h2 : ⁅k, k'⁆ * x * ⁅k, k'⁆⁻¹ = x := by
      calc ⁅k, k'⁆ * x * ⁅k, k'⁆⁻¹
          = (k * k') * (k⁻¹ * (k'⁻¹ * x * k'⁻¹⁻¹) * k⁻¹⁻¹) * (k * k')⁻¹ := by
            simp only [commutatorElement_def]
            group
        _ = (k * k') * (k'⁻¹ * (k⁻¹ * x * k⁻¹⁻¹) * k'⁻¹⁻¹) * (k * k')⁻¹ := by rw [h]
        _ = x := by group
    have h3 : ⁅k, k'⁆ * x = x * ⁅k, k'⁆ := by
      calc ⁅k, k'⁆ * x = (⁅k, k'⁆ * x * ⁅k, k'⁆⁻¹) * ⁅k, k'⁆ := by group
        _ = x * ⁅k, k'⁆ := by rw [h2]
    exact h3.symm
  rw [hKp] at hcomm
  intro k hk x hx
  exact (Subgroup.mem_centralizer_iff.1 (hcomm hk) x hx).symm

variable [Finite G]

theorem diag_dichotomy {B : Subgroup G} (hB : QBlock B) (δ : ↥B →* G) {C : Subgroup G}
    (hKC : ∀ k ∈ δ.range, k ∈ Subgroup.normalizer (C : Set G))
    (hCK : ∀ c ∈ C, c ∈ Subgroup.normalizer ((δ.range : Subgroup G) : Set G)) :
    (∀ k ∈ δ.range, ∀ c ∈ C, k * c = c * k) ∨ (∀ b : ↥B, (b : G) ∈ blockU B → δ b ∈ C) := by
  have : Group.IsPerfect ↥B := Subgroup.isPerfect_iff.2 hB.perfect
  have : Group.IsPerfect ↥δ.range := Group.IsPerfect.range δ
  have hKperf : ⁅δ.range, δ.range⁆ = δ.range := Subgroup.commutator_eq_self
  obtain ⟨A, hAdef⟩ : ∃ A : Subgroup G, A = ⁅C, δ.range⁆ := ⟨_, rfl⟩
  have hAC : A ≤ C := by
    rw [hAdef]
    refine Subgroup.commutator_le.2 fun c hc k hk => ?_
    have h1 : k * c⁻¹ * k⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.1 (hKC k hk) c⁻¹).1 (C.inv_mem hc)
    have e : ⁅c, k⁆ = c * (k * c⁻¹ * k⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact C.mul_mem hc h1
  have hAK : A ≤ δ.range := by
    rw [hAdef]
    refine Subgroup.commutator_le.2 fun c hc k hk => ?_
    have h1 : c * k * c⁻¹ ∈ δ.range := (Subgroup.mem_normalizer_iff.1 (hCK c hc) k).1 hk
    rw [commutatorElement_def]
    exact δ.range.mul_mem h1 (δ.range.inv_mem hk)
  have hKA : δ.range ≤ Subgroup.normalizer (A : Set G) := by
    rw [hAdef]
    exact Subgroup.normalizer_commutator_ge_right C δ.range
  obtain ⟨NA, hNAdef⟩ : ∃ NA : Subgroup G, NA = (A.comap δ).map B.subtype := ⟨_, rfl⟩
  have hNAmem : ∀ x, x ∈ NA ↔ ∃ b : ↥B, δ b ∈ A ∧ (b : G) = x := by
    intro x
    rw [hNAdef]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b, hb, rfl⟩
  have hNAB : NA ≤ B := by
    rw [hNAdef]
    exact Subgroup.map_subtype_le _
  have hBNA : B ≤ Subgroup.normalizer (NA : Set G) := by
    refine le_normalizer_of_forall fun b hb a ha => ?_
    obtain ⟨α, hαA, rfl⟩ := (hNAmem a).1 ha
    have hδ : δ ⟨b, hb⟩ ∈ δ.range := ⟨⟨b, hb⟩, rfl⟩
    have h1 := (Subgroup.mem_normalizer_iff.1 (hKA hδ) (δ α)).1 hαA
    refine (hNAmem _).2 ⟨⟨b, hb⟩ * α * ⟨b, hb⟩⁻¹, ?_, rfl⟩
    rw [map_mul, map_mul, map_inv]
    exact h1
  by_cases hz : NA ≤ Subgroup.centralizer (B : Set G)
  · left
    have hAK0 : ⁅A, δ.range⁆ = ⊥ := by
      refine le_bot_iff.1 (Subgroup.commutator_le.2 fun a ha k hk => ?_)
      obtain ⟨β, rfl⟩ := hAK ha
      obtain ⟨β', rfl⟩ := hk
      have hβ : (β : G) ∈ NA := (hNAmem _).2 ⟨β, ha, rfl⟩
      have hc : ∀ b' ∈ B, b' * (β : G) = (β : G) * b' :=
        fun b' hb' => Subgroup.mem_centralizer_iff.1 (hz hβ) b' hb'
      have hββ : β' * β = β * β' := Subtype.ext (hc β' β'.2)
      have : δ β * δ β' = δ β' * δ β := by
        rw [← map_mul, ← map_mul, hββ.symm]
      rw [Subgroup.mem_bot]
      exact commutatorElement_eq_one_iff_mul_comm.2 this
    have h2 : ⁅⁅C, δ.range⁆, δ.range⁆ = ⊥ := by
      rw [← hAdef]
      exact hAK0
    have h1 : ⁅⁅δ.range, C⁆, δ.range⁆ = ⊥ := by
      rw [Subgroup.commutator_comm δ.range C, ← hAdef]
      exact hAK0
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := δ.range) (H₂ := δ.range)
      (H₃ := C) h1 h2
    rw [hKperf] at h3
    intro k hk c hc
    have : ⁅k, c⁆ ∈ (⊥ : Subgroup G) := by
      rw [← h3]
      exact Subgroup.commutator_mem_commutator hk hc
    rw [Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · right
    have hU := hB.blockU_le_of_normal hNAB hBNA hz
    intro b hb
    obtain ⟨b', hb'A, hb'eq⟩ := (hNAmem _).1 (hU hb)
    have hbb : b' = b := Subtype.ext hb'eq
    rw [hbb] at hb'A
    exact hAC hb'A

end CFSG.CGT.PushingUpLit.LIT.Foote
