module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Sylow

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G] {L K : Subgroup G} {t u : G}

omit [Finite G] in
theorem center_eq_bot_of_simple_nonabelian {X : Type} [Group X] [IsSimpleGroup X]
    (hnonab : ∃ a b : X, a * b ≠ b * a) : center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center X) with h' | h'
  · exact h'
  · obtain ⟨a, b, hab⟩ := hnonab
    exact absurd (mem_center_iff.1 (h' ▸ mem_top b) a) hab

omit [Finite G] in
theorem mem_or_mul_mem_of_centralizer_eq (htC : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hM : centralizer ({t} : Set G) = L ⊔ zpowers t) :
    ∀ b ∈ centralizer ({t} : Set G), b ∈ L ∨ b * t ∈ L := by
  intro b hb
  rw [hM] at hb
  obtain ⟨l, hl, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (zpowers_le.2 htC) hb
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hc
  rcases zpow_eq_one_or_self_of_orderOf_eq_two ht2 k with h1 | h1
  · rw [h1, mul_one]
    exact Or.inl hl
  · rw [h1, mul_assoc, mul_self_eq_one_of_orderOf_eq_two ht2, mul_one]
    exact Or.inr hl

omit [Finite G] in
theorem not_mem_of_center_eq_bot (htC : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hZ : center L = ⊥) : t ∉ L := by
  intro htL
  have hmem : t ∈ (center L).map L.subtype := by
    rw [map_center_eq_inf_centralizer]
    exact ⟨htL, htC⟩
  rw [hZ, Subgroup.map_bot, mem_bot] at hmem
  exact ne_one_of_orderOf_eq_two ht2 hmem

omit [Finite G] in
theorem commutator_centralizer_le (htC : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hM : centralizer ({t} : Set G) = L ⊔ zpowers t) (htL : t ∉ L) :
    ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ ≤ L := by
  have htM : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have hLM : L.relIndex (centralizer ({t} : Set G)) = 2 :=
    relIndex_eq_two htM htL (mem_or_mul_mem_of_centralizer_eq htC ht2 hM)
  have hN : (L.subgroupOf (centralizer ({t} : Set G))).index = 2 := hLM
  have h3 := commutator_le_of_index_eq_two hN
  intro x hx
  rw [← map_subtype_commutator] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact mem_subgroupOf.1 (h3 hy)

omit [Finite G] in
theorem not_isConj_of_perf (htC : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2)
    (hM : centralizer ({t} : Set G) = L ⊔ zpowers t) (htL : t ∉ L)
    (hperf : ∀ w ∈ L, orderOf w = 2 →
      w ∈ ⁅L ⊓ centralizer ({w} : Set G), L ⊓ centralizer ({w} : Set G)⁆)
    {a : G} (haL : a ∈ L) (ha2 : orderOf a = 2) : ¬ IsConj t a := by
  intro hconj
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  have hcomm := hperf a haL ha2
  have ht : t = c⁻¹ * a * c := by rw [← hc]; group
  set f : G →* G := (MulAut.conj c⁻¹).toMonoidHom with hf'
  have hfa : f a = t := by
    show c⁻¹ * a * c⁻¹⁻¹ = t
    rw [ht]
    group
  have hmap : (L ⊓ centralizer ({a} : Set G)).map f ≤ centralizer ({t} : Set G) := by
    rintro _ ⟨y, ⟨-, hy⟩, rfl⟩
    refine mem_centralizer_singleton_iff.2 ?_
    have hy' : y * a = a * y := mem_centralizer_singleton_iff.1 hy
    show c⁻¹ * y * c⁻¹⁻¹ * t = t * (c⁻¹ * y * c⁻¹⁻¹)
    have e1 : c⁻¹ * y * c⁻¹⁻¹ * t = c⁻¹ * (y * a) * c := by rw [ht]; group
    have e2 : t * (c⁻¹ * y * c⁻¹⁻¹) = c⁻¹ * (a * y) * c := by rw [ht]; group
    rw [e1, e2, hy']
  have h1 : t ∈ ⁅centralizer ({t} : Set G), centralizer ({t} : Set G)⁆ := by
    have h2 := Subgroup.mem_map_of_mem f hcomm
    rw [hfa, map_commutator] at h2
    exact commutator_mono hmap hmap h2
  exact htL (commutator_centralizer_le htC ht2 hM htL h1)

theorem solomon_closing_3_12_2 (hStd : StdHyp G L)
    (hS : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2)
    (h : SolomonHyp G L K t u) (hf : Sol78Fusion u t)
    (hinn : centralizer ({t} : Set G) ≤ L ⊔ centralizer (L : Set G))
    (hperf : ∀ w ∈ L, orderOf w = 2 →
      w ∈ ⁅L ⊓ centralizer ({w} : Set G), L ⊓ centralizer ({w} : Set G)⁆) : False := by
  have := h.simple
  have := h.simpleL
  have ht2 := h.t_order
  obtain ⟨P, htP, huP, hPM⟩ := exists_sylow_le_centralizer ht2 h.u_order h.u_comm_t
    (fun t' ht' => eq_of_mem_fusedSet h hf ht')
  have hM : centralizer ({t} : Set G) = L ⊔ zpowers t :=
    hStd.centralizer_eq_sup_zpowers hS h.t_mem ht2 hinn
  have hZ : center L = ⊥ := center_eq_bot_of_simple_nonabelian h.nonabelianL
  have htL : t ∉ L := not_mem_of_center_eq_bot h.t_mem ht2 hZ
  have hsplit := mem_or_mul_mem_of_centralizer_eq h.t_mem ht2 hM
  have hLP : L.relIndex P = 2 := relIndex_eq_two htP htL (fun b hb => hsplit b (hPM hb))
  have hU : (↑P ⊓ L : Subgroup G).relIndex P = 2 := by
    rw [inf_relIndex_left]
    exact hLP
  obtain ⟨g, hg⟩ := exists_conj_mem_complement h.nonabelian (S := (P : Subgroup G))
    (U := (P : Subgroup G) ⊓ L) P.isPGroup' (Sylow.not_dvd_index P) inf_le_left hU htP
    (fun htU => htL htU.2) ht2
  have haL : g⁻¹ * t * g ∈ L := hg.2
  have ha2 : orderOf (g⁻¹ * t * g) = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective t
    simpa [MulAut.conj_apply] using this.trans ht2
  exact not_isConj_of_perf h.t_mem ht2 hM htL hperf haL ha2 (isConj_iff.2 ⟨g⁻¹, by simp⟩)

end CFSG.EvenSporadicStandard.Solomon78
