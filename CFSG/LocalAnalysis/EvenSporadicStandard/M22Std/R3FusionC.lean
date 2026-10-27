module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3FusionB
public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.R3FusionA

public section

namespace CFSG.EvenSporadicStandard.M22Std

open Subgroup

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem elemAb_sup_zpowers {A : Subgroup G} {w : G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hAs : ∀ a ∈ A, a * a = 1) (hw2 : w * w = 1) (hwA : ∀ a ∈ A, w * a = a * w) :
    (∀ a ∈ A ⊔ zpowers w, ∀ b ∈ A ⊔ zpowers w, a * b = b * a) ∧
      ∀ a ∈ A ⊔ zpowers w, a * a = 1 := by
  have hN := normalizes_of_centralizes hwA
  have key : ∀ a ∈ A ⊔ zpowers w, a ∈ A ∨ ∃ u ∈ A, a = w * u := fun a ha =>
    mem_sup_zpowers_invol hw2 hN ha
  constructor
  · intro a ha b hb
    rcases key a ha with hu | ⟨u, hu, rfl⟩ <;> rcases key b hb with hv | ⟨v, hv, rfl⟩
    · exact hAc a hu b hv
    · calc a * (w * v) = (a * w) * v := by group
        _ = (w * a) * v := by rw [← hwA a hu]
        _ = w * (a * v) := by group
        _ = w * (v * a) := by rw [hAc a hu v hv]
        _ = w * v * a := by group
    · calc w * u * b = w * (u * b) := by group
        _ = w * (b * u) := by rw [hAc u hu b hv]
        _ = (w * b) * u := by group
        _ = (b * w) * u := by rw [hwA b hv]
        _ = b * (w * u) := by group
    · calc w * u * (w * v) = w * (u * w) * v := by group
        _ = w * (w * u) * v := by rw [← hwA u hu]
        _ = (w * w) * u * v := by group
        _ = u * v := by rw [hw2, one_mul]
        _ = v * u := hAc u hu v hv
        _ = (w * w) * v * u := by rw [hw2, one_mul]
        _ = w * (w * v) * u := by group
        _ = w * (v * w) * u := by rw [hwA v hv]
        _ = w * v * (w * u) := by group
  · intro a ha
    rcases key a ha with hu | ⟨u, hu, rfl⟩
    · exact hAs a hu
    · calc w * u * (w * u) = w * (u * w) * u := by group
        _ = w * (w * u) * u := by rw [← hwA u hu]
        _ = (w * w) * (u * u) := by group
        _ = 1 := by rw [hw2, hAs u hu, one_mul]

theorem exists_conj_sylow {T R : Subgroup G} {z y : G}
    (hCG : Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({z} : Set G)))
    (hyc : IsConj z y) (hTz : T ≤ centralizer ({z} : Set G)) (hTp : IsPGroup 2 ↥T)
    (hTs : ¬ 2 ∣ T.relIndex (centralizer ({z} : Set G)))
    (hRy : R ≤ centralizer ({y} : Set G)) (hRp : IsPGroup 2 ↥R)
    (hRs : ¬ 2 ∣ R.relIndex (centralizer ({y} : Set G))) :
    ∃ g : G, g * z * g⁻¹ = y ∧ ∀ x, x ∈ R ↔ g⁻¹ * x * g ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c0, hc0⟩ := isConj_iff.1 hyc
  set T0 : Subgroup G := T.map (MulAut.conj c0).toMonoidHom with hT0
  have hmem : ∀ x, x ∈ T0 ↔ c0⁻¹ * x * c0 ∈ T := mem_map_conj c0
  have hT0y : T0 ≤ centralizer ({y} : Set G) := by
    intro x hx
    rw [mem_centralizer_singleton_iff]
    have h1 := mem_centralizer_singleton_iff.1 (hTz ((hmem x).1 hx))
    rw [← hc0]
    calc x * (c0 * z * c0⁻¹) = c0 * ((c0⁻¹ * x * c0) * z) * c0⁻¹ := by group
      _ = c0 * (z * (c0⁻¹ * x * c0)) * c0⁻¹ := by rw [h1]
      _ = c0 * z * c0⁻¹ * x := by group
  have hT0card : Nat.card T0 = Nat.card T :=
    Subgroup.card_map_of_injective (MulAut.conj c0).injective
  have hT0p : IsPGroup 2 ↥T0 := by
    obtain ⟨n, hn⟩ := hTp.exists_card_eq
    exact IsPGroup.of_card (n := n) (by rw [hT0card, hn])
  have hT0s : ¬ 2 ∣ T0.relIndex (centralizer ({y} : Set G)) := by
    have h1 := Subgroup.relIndex_mul_card T (centralizer ({z} : Set G))
    have h2 := Subgroup.relIndex_mul_card T0 (centralizer ({y} : Set G))
    rw [inf_of_le_left hTz] at h1
    rw [inf_of_le_left hT0y, hT0card, hCG] at h2
    have : T0.relIndex (centralizer ({y} : Set G)) = T.relIndex (centralizer ({z} : Set G)) :=
      Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := T)) (h2.trans h1.symm)
    rw [this]
    exact hTs
  obtain ⟨d, hd, hdx⟩ := exists_conj_sylow_two ⟨hT0y, hT0p, hT0s⟩ ⟨hRy, hRp, hRs⟩
  refine ⟨d * c0, ?_, fun x => ?_⟩
  · have hdy : d * y = y * d := mem_centralizer_singleton_iff.1 hd
    calc d * c0 * z * (d * c0)⁻¹ = d * (c0 * z * c0⁻¹) * d⁻¹ := by group
      _ = d * y * d⁻¹ := by rw [hc0]
      _ = y := by rw [hdy]; group
  · rw [hdx x, hmem]
    have : (d * c0)⁻¹ * x * (d * c0) = c0⁻¹ * (d⁻¹ * x * d) * c0 := by group
    rw [this]

theorem exists_normalizer_conj_of_fusion {L1 F T E Q : Subgroup G} {z y : G}
    (hL1c : ∀ a ∈ L1, ∀ b ∈ L1, a * b = b * a) (hL1s : ∀ a ∈ L1, a * a = 1)
    (hL1card : Nat.card L1 = 256) (hz2 : z * z = 1) (hzN : ∀ a, a ∈ L1 ↔ z * a * z⁻¹ ∈ L1)
    (hzL : z ∉ L1) (hFL : F ≤ L1) (hFcard : Nat.card F = 16) (hzF : ∀ x ∈ F, z * x = x * z)
    (hFz : ∀ x ∈ L1, z * x = x * z → x ∈ F) (hKp : IsPGroup 2 ↥(L1 ⊔ zpowers z))
    (hKs : ¬ 2 ∣ (L1 ⊔ zpowers z).relIndex (centralizer (F : Set G)))
    (hnc : ∀ x ∈ L1, ¬ IsConj z x) (htr : ∀ f ∈ F, IsConj z (z * f))
    (hy2 : y * y = 1) (hyz : y * z = z * y) (hyN : ∀ a, a ∈ L1 ↔ y * a * y⁻¹ ∈ L1)
    (hyc : IsConj z y) (hCG : Nat.card (centralizer ({z} : Set G)) = 1774080)
    (hU16 : 16 ≤ Nat.card ↥(centralizer ({y} : Set G) ⊓ L1))
    (hW : Nat.card ↥(centralizer ({y} : Set G) ⊓ F) = 4)
    (hTz : T ≤ centralizer ({z} : Set G)) (hTp : IsPGroup 2 ↥T)
    (hTs : ¬ 2 ∣ T.relIndex (centralizer ({z} : Set G)))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEs : ∀ a ∈ E, a * a = 1)
    (hEcard : Nat.card E = 64) (hzE : z ∈ E) (hyE : y ∈ E)
    (hT1 : ∀ W' : Subgroup G, W' ≤ T → (∀ a ∈ W', ∀ b ∈ W', a * b = b * a) →
      (∀ a ∈ W', a * a = 1) → Nat.card W' = 64 → W' = E)
    (hT2 : ∀ V : Subgroup G, V ≤ T → (∀ t ∈ T, ∀ v ∈ V, t * v * t⁻¹ ∈ V) →
      (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) → (∀ a ∈ V, a * a = 1) → Nat.card V = 32 →
      z ∈ V → Nat.card ↥(V ⊓ E) ≤ 8 → V = F ⊔ zpowers z)
    (hQN : Q ≤ normalizer (L1 : Set G)) (hQy : Q ≤ centralizer ({y} : Set G))
    (hQz : Q ≤ centralizer ({z} : Set G)) (hEQ : E ≤ Q) (hQp : IsPGroup 2 ↥Q)
    (hQcard : 128 ≤ Nat.card Q) :
    ∃ k ∈ normalizer (L1 : Set G), ∃ l ∈ L1, k * z * k⁻¹ = y * l := by
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
  have hzN' : ∀ a, a ∈ L1 ↔ z * a * z ∈ L1 := by simpa [hzi] using hzN
  have hyL : y ∉ L1 := fun h => hnc y h hyc
  have hU16' : Nat.card ↥(centralizer ({y} : Set G) ⊓ L1) = 16 :=
    le_antisymm (card_centralizer_le_sixteen hL1c hL1s hz2 hzN' hyz hFz hW) hU16
  obtain ⟨c0, hc0⟩ := isConj_iff.1 hyc
  have hCGy : Nat.card (centralizer ({y} : Set G)) = 1774080 := by
    rw [card_centralizer_eq_of_conj hc0, hCG]
  obtain ⟨hRcard, hRp, hRs, hRN⟩ := exists_sylow_R hFz hU16' hW hQN hQy hQz hQp hQcard hCGy
  set U : Subgroup G := centralizer ({y} : Set G) ⊓ L1 with hUdef
  set R : Subgroup G := U ⊔ Q with hRdef
  have hRC : R ≤ centralizer ({y} : Set G) := sup_le inf_le_left hQy
  obtain ⟨g, hgz, hgR⟩ :=
    exists_conj_sylow (card_centralizer_eq_of_conj hc0) hyc hTz hTp hTs hRC hRp hRs
  have hUy : ∀ u ∈ U, y * u = u * y := fun u hu =>
    (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hu).1).symm
  have hUL : U ≤ L1 := inf_le_right
  have hUc : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := fun a ha b hb => hL1c a (hUL ha) b (hUL hb)
  have hUs : ∀ a ∈ U, a * a = 1 := fun a ha => hL1s a (hUL ha)
  have hER : E ≤ R := hEQ.trans le_sup_right
  have hUR : U ≤ R := le_sup_left
  have hgE : ∀ x ∈ E, g * x * g⁻¹ ∈ E := by
    set E' : Subgroup G := E.map (MulAut.conj g⁻¹).toMonoidHom with hE'
    have hmemE' : ∀ x, x ∈ E' ↔ g * x * g⁻¹ ∈ E := fun x => by
      rw [hE', mem_map_conj]
      simp
    have hE'T : E' ≤ T := fun x hx => by
      have := (hgR (g * x * g⁻¹)).1 (hER ((hmemE' x).1 hx))
      rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
    have hE'c : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
      intro a ha b hb
      have := hEc _ ((hmemE' a).1 ha) _ ((hmemE' b).1 hb)
      calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [this]
        _ = b * a := by group
    have hE's : ∀ a ∈ E', a * a = 1 := by
      intro a ha
      have := hEs _ ((hmemE' a).1 ha)
      calc a * a = g⁻¹ * ((g * a * g⁻¹) * (g * a * g⁻¹)) * g := by group
        _ = 1 := by rw [this]; group
    have hE'card : Nat.card E' = 64 := by
      rw [hE', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEcard]
    have hE'E : E' = E := hT1 E' hE'T hE'c hE's hE'card
    intro x hx
    exact (hmemE' x).1 (hE'E ▸ hx)
  set V : Subgroup G := U ⊔ zpowers y with hVdef
  obtain ⟨hVc, hVs⟩ := elemAb_sup_zpowers hUc hUs hy2 hUy
  have hUN := normalizes_of_centralizes hUy
  have hyU : y ∉ U := fun h => hyL (hUL h)
  have hVcard : Nat.card V = 32 := by
    rw [hVdef, card_sup_zpowers_invol hy2 hUN hyU, hU16']
  have hVR : V ≤ R := sup_le hUR (Subgroup.zpowers_le.2 (hER hyE))
  have hVn : ∀ r ∈ R, ∀ v ∈ V, r * v * r⁻¹ ∈ V := by
    intro r hr v hv
    have hry : r * y = y * r := mem_centralizer_singleton_iff.1 (hRC hr)
    have hrU := Subgroup.mem_normalizer_iff.1 (hRN hr)
    rcases mem_sup_zpowers_invol hy2 hUN hv with hu | ⟨u, hu, rfl⟩
    · exact Subgroup.mem_sup_left ((hrU v).1 hu)
    · have : r * (y * u) * r⁻¹ = y * (r * u * r⁻¹) := by
        calc r * (y * u) * r⁻¹ = (r * y) * u * r⁻¹ := by group
          _ = (y * r) * u * r⁻¹ := by rw [hry]
          _ = y * (r * u * r⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
        (Subgroup.mem_sup_left ((hrU u).1 hu))
  set V' : Subgroup G := V.map (MulAut.conj g⁻¹).toMonoidHom with hV'
  have hmemV' : ∀ x, x ∈ V' ↔ g * x * g⁻¹ ∈ V := fun x => by
    rw [hV', mem_map_conj]
    simp
  have hV'T : V' ≤ T := fun x hx => by
    have := (hgR (g * x * g⁻¹)).1 (hVR ((hmemV' x).1 hx))
    rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this
  have hV'n : ∀ t ∈ T, ∀ v ∈ V', t * v * t⁻¹ ∈ V' := by
    intro t ht v hv
    have hgt : g * t * g⁻¹ ∈ R := (hgR _).2 (by rwa [show g⁻¹ * (g * t * g⁻¹) * g = t by group])
    have := hVn _ hgt _ ((hmemV' v).1 hv)
    rw [hmemV']
    rwa [show g * t * g⁻¹ * (g * v * g⁻¹) * (g * t * g⁻¹)⁻¹ = g * (t * v * t⁻¹) * g⁻¹ by
      group] at this
  have hV'c : ∀ a ∈ V', ∀ b ∈ V', a * b = b * a := by
    intro a ha b hb
    have := hVc _ ((hmemV' a).1 ha) _ ((hmemV' b).1 hb)
    calc a * b = g⁻¹ * ((g * a * g⁻¹) * (g * b * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * b * g⁻¹) * (g * a * g⁻¹)) * g := by rw [this]
      _ = b * a := by group
  have hV's : ∀ a ∈ V', a * a = 1 := by
    intro a ha
    have := hVs _ ((hmemV' a).1 ha)
    calc a * a = g⁻¹ * ((g * a * g⁻¹) * (g * a * g⁻¹)) * g := by group
      _ = 1 := by rw [this]; group
  have hV'card : Nat.card V' = 32 := by
    rw [hV', Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hVcard]
  have hzV' : z ∈ V' := by
    rw [hmemV', hgz]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hVE : Nat.card ↥(V ⊓ E) ≤ 8 := by
    set W : Subgroup G := centralizer ({y} : Set G) ⊓ F with hWdef
    have hWy : ∀ a ∈ W, y * a = a * y := fun a ha =>
      (mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ha).1).symm
    have hyW : y ∉ W := fun h => hyL (hFL (Subgroup.mem_inf.1 h).2)
    have hWcard : Nat.card ↥(W ⊔ zpowers y) = 8 := by
      rw [card_sup_zpowers_invol hy2 (normalizes_of_centralizes hWy) hyW, hW]
    have huW : ∀ u ∈ U, z * u = u * z → u ∈ W := fun u hu hz =>
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hu).1, hFz u (hUL hu) hz⟩
    have hle : V ⊓ E ≤ W ⊔ zpowers y := by
      intro x hx
      obtain ⟨hxV, hxE⟩ := Subgroup.mem_inf.1 hx
      have hxz : x * z = z * x := hEc x hxE z hzE
      rcases mem_sup_zpowers_invol hy2 hUN hxV with hu | ⟨u, hu, rfl⟩
      · exact Subgroup.mem_sup_left (huW x hu hxz.symm)
      · have huz : u * z = z * u := by
          have h1 : y * u * z = z * (y * u) := hxz
          have h2 : y * (u * z) = y * (z * u) := by
            calc y * (u * z) = y * u * z := by group
              _ = z * (y * u) := h1
              _ = (z * y) * u := by group
              _ = (y * z) * u := by rw [hyz]
              _ = y * (z * u) := by group
          exact mul_left_cancel h2
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
          (Subgroup.mem_sup_left (huW u hu huz.symm))
    calc Nat.card ↥(V ⊓ E) ≤ Nat.card ↥(W ⊔ zpowers y) := Subgroup.card_le_of_le hle
      _ = 8 := hWcard
  have hV'E : Nat.card ↥(V' ⊓ E) ≤ 8 := by
    have hle : (V' ⊓ E).map (MulAut.conj g).toMonoidHom ≤ V ⊓ E := by
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨hxV, hxE⟩ := Subgroup.mem_inf.1 hx
      exact Subgroup.mem_inf.2 ⟨(hmemV' x).1 hxV, hgE x hxE⟩
    have := Subgroup.card_le_of_le hle
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at this
    omega
  have hVeq : V' = F ⊔ zpowers z :=
    hT2 V' hV'T hV'n hV'c hV's hV'card hzV' hV'E
  have hzNF := normalizes_of_centralizes hzF
  have hUle : U ≤ F.map (MulAut.conj g).toMonoidHom := by
    intro u hu
    rw [mem_map_conj]
    have hu' : g⁻¹ * u * g ∈ F ⊔ zpowers z := by
      rw [← hVeq, hmemV']
      rw [show g * (g⁻¹ * u * g) * g⁻¹ = u by group]
      exact Subgroup.mem_sup_left hu
    rcases mem_sup_zpowers_invol hz2 hzNF hu' with h | ⟨f, hf, hfu⟩
    · exact h
    · exfalso
      have hconj : IsConj (z * f) u := by
        refine isConj_iff.2 ⟨g, ?_⟩
        rw [← hfu]
        group
      exact hnc u (hUL hu) ((htr f hf).trans hconj)
  have hUeq : centralizer ({y} : Set G) ⊓ L1 = F.map (MulAut.conj g).toMonoidHom :=
    Subgroup.eq_of_le_of_card_ge hUle (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hFcard, hU16'])
  exact exists_normalizer_conj_mem_coset hL1c hL1card hz2 hy2 hzN hyN hzL hyL hFL hzF hKp hKs
    hUeq hU16'

end CFSG.EvenSporadicStandard.M22Std
