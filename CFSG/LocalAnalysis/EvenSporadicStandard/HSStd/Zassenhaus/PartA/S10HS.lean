module

public import CFSG.Sporadic.SmallOddCore.HSAut
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier

section General

variable {M : Type*} [Group M]

theorem card_inf_centralizer_conj {Z : Subgroup M} {u : M} (hu : u ∈ normalizer (Z : Set M))
    (a : M) :
    Nat.card ↥(Z ⊓ centralizer ({u * a * u⁻¹} : Set M)) =
      Nat.card ↥(Z ⊓ centralizer ({a} : Set M)) := by
  symm
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAut.conj u).toEquiv fun x => ?_)
  have key : ∀ x y : M, u * x * u⁻¹ * (u * y * u⁻¹) = u * (x * y) * u⁻¹ := fun x y => by group
  have hcomm : x * a = a * x ↔ u * x * u⁻¹ * (u * a * u⁻¹) = u * a * u⁻¹ * (u * x * u⁻¹) := by
    rw [key, key]
    constructor
    · intro h
      rw [h]
    · intro h
      have := congrArg (fun z => u⁻¹ * z * u) h
      simpa [mul_assoc] using this
  rw [mem_inf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff, hcomm,
    mem_normalizer_iff.1 hu x]
  rfl

end General

theorem hsR_invol_cent_order
    {τ : Equiv.Perm (Fin 3850)} (hτR : τ ∈ hsR)
    (hτ : orderOf τ = 2) :
    (∃ g ∈ hsP, hsU * τ * hsU⁻¹ = g * τ * g⁻¹) ∧
      Nat.card ↥(hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))) ∈
        ({7680, 2880, 40320, 1920} : Set ℕ) := by
  obtain ⟨-, -, -, hrows, hcover, -, hlist, -⟩ := hs_involution_centralizers
  obtain ⟨hU2, -, hUP, hmap, -, hRmem, -⟩ := hs_normalizing_model
  have hUn : ∀ p ∈ hsP, hsU * p * hsU⁻¹ ∈ hsP := fun p hp => by
    rw [← hmap]
    exact ⟨p, hp, rfl⟩
  have hUU : hsU * hsU = 1 := by rw [← sq, hU2]
  have hUnorm : hsU ∈ normalizer (hsP : Set (Equiv.Perm (Fin 3850))) := by
    rw [mem_normalizer_iff]
    intro h
    refine ⟨fun hh => hUn h hh, fun hh => ?_⟩
    have hUi : hsU⁻¹ = hsU := inv_eq_of_mul_eq_one_right hUU
    have e : hsU * (hsU * h * hsU⁻¹) * hsU⁻¹ = h := by
      rw [hUi]
      calc hsU * (hsU * h * hsU) * hsU = (hsU * hsU) * h * (hsU * hsU) := by group
        _ = h := by rw [hUU]; group
    have := hUn _ hh
    rwa [e] at this
  have hUR : hsU ∈ hsR := (hRmem hsU).2 (Or.inr (by rw [hUU]; exact hsP.one_mem))
  have hτ'R : hsU * τ * hsU⁻¹ ∈ hsR := hsR.mul_mem (hsR.mul_mem hUR hτR) (hsR.inv_mem hUR)
  have hτ'2 : orderOf (hsU * τ * hsU⁻¹) = 2 :=
    (orderOf_injective (MulAut.conj hsU).toMonoidHom (MulAut.conj hsU).injective τ).symm ▸ hτ
  obtain ⟨r, hr, g, hg, hgr⟩ := hcover τ hτR hτ
  obtain ⟨r', hr', g', hg', hgr'⟩ := hcover _ hτ'R hτ'2
  obtain ⟨-, -, hrout, -, hrcard, -⟩ := hrows r hr
  obtain ⟨-, -, hrout', -, hrcard', -⟩ := hrows r' hr'
  have hgnorm : ∀ {h : Equiv.Perm (Fin 3850)}, h ∈ hsP →
      h ∈ normalizer (hsP : Set (Equiv.Perm (Fin 3850))) := fun {h} hh =>
    (mem_normalizer_iff.2 fun x => ⟨fun hx => hsP.mul_mem (hsP.mul_mem hh hx) (hsP.inv_mem hh),
      fun hx => by
        have := hsP.mul_mem (hsP.mul_mem (hsP.inv_mem hh) hx) hh
        simpa [mul_assoc] using this⟩)
  have hmemconj : ∀ {h x : Equiv.Perm (Fin 3850)}, h ∈ hsP → (h * x * h⁻¹ ∈ hsP ↔ x ∈ hsP) :=
    fun {h x} hh => (mem_normalizer_iff.1 (hgnorm hh) x).symm
  have hc1 : Nat.card ↥(hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))) = r.centOrder := by
    rw [← hrcard, hgr, card_inf_centralizer_conj (hgnorm hg)]
  have hc2 : Nat.card ↥(hsP ⊓ centralizer ({hsU * τ * hsU⁻¹} : Set (Equiv.Perm (Fin 3850)))) =
      r'.centOrder := by
    rw [← hrcard', hgr', card_inf_centralizer_conj (hgnorm hg')]
  have hc12 := card_inf_centralizer_conj hUnorm τ
  have hcen : r.centOrder = r'.centOrder := by rw [← hc1, ← hc2, hc12]
  have hout : r.outer = r'.outer := by
    have h1 : τ ∈ hsP ↔ hsU * τ * hsU⁻¹ ∈ hsP := mem_normalizer_iff.1 hUnorm τ
    have h2 := hmemconj (x := tp 3850 r.rep) hg
    have h3 := hmemconj (x := tp 3850 r'.rep) hg'
    rw [← hgr] at h2
    rw [← hgr'] at h3
    have h4 : r.outer = true ↔ r'.outer = true := by
      rw [hrout, hrout', not_iff_not]
      exact h2.symm.trans (h1.trans h3)
    exact Bool.eq_iff_iff.2 h4
  have hnodup : (hsRows.map fun r => (r.outer, r.centOrder)).Nodup := by decide
  have hrr : r = r' := List.inj_on_of_nodup_map hnodup hr hr' (by rw [hcen, hout])
  subst hrr
  refine ⟨⟨g' * g⁻¹, hsP.mul_mem hg' (hsP.inv_mem hg), ?_⟩, ?_⟩
  · rw [hgr', hgr]
    group
  · have hmem : (r.outer, r.classSize, r.centOrder) ∈ hsRows.map fun r => (r.outer, r.classSize, r.centOrder) :=
      List.mem_map_of_mem hr
    rw [hlist] at hmem
    rw [hc1]
    simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at hmem
    rcases hmem with h | h | h | h <;> simp [h.2.2]


theorem card_hsR_inf_centralizer
    {τ : Equiv.Perm (Fin 3850)} (hτR : τ ∈ hsR)
    (hτ : orderOf τ = 2) :
    Nat.card ↥(hsR ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))) =
      2 * Nat.card ↥(hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))) := by
  obtain ⟨⟨g, hg, hgτ⟩, -⟩ := hsR_invol_cent_order hτR hτ
  obtain ⟨hU2, -, hUP, hmap, -, hRmem, -⟩ := hs_normalizing_model
  have hUU : hsU * hsU = 1 := by rw [← sq, hU2]
  have hUi : hsU⁻¹ = hsU := inv_eq_of_mul_eq_one_right hUU
  have hUR : hsU ∈ hsR := (hRmem hsU).2 (Or.inr (by rw [hUU]; exact hsP.one_mem))
  set H : Subgroup (Equiv.Perm (Fin 3850)) := hsR ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))
    with hH
  have hPR : hsP ≤ hsR := le_sup_left
  have hKH : hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) ≤ H :=
    inf_le_inf_right _ hPR
  set a : Equiv.Perm (Fin 3850) := g⁻¹ * hsU with ha
  have haR : a ∈ hsR := hsR.mul_mem (hPR (hsP.inv_mem hg)) hUR
  have haP : a ∉ hsP := fun h => hUP (by
    have := hsP.mul_mem hg h
    simpa [ha, ← mul_assoc] using this)
  have haC : a ∈ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) := by
    rw [mem_centralizer_singleton_iff]
    have h1 : hsU * τ * hsU⁻¹ = g * τ * g⁻¹ := hgτ
    have h2 : hsU * τ = g * τ * g⁻¹ * hsU := by
      rw [← h1]; group
    calc g⁻¹ * hsU * τ = g⁻¹ * (g * τ * g⁻¹ * hsU) := by rw [mul_assoc, h2]
      _ = τ * (g⁻¹ * hsU) := by group
  have hPR' : ∀ b ∈ hsR, b ∉ hsP → b * hsU ∈ hsP := fun b hb hbP =>
    ((hRmem b).1 hb).resolve_left hbP
  have hidx : ((hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))).subgroupOf H).index = 2 := by
    rw [index_eq_two_iff]
    refine ⟨⟨a, mem_inf.2 ⟨haR, haC⟩⟩, fun b => ?_⟩
    have hbR : (b : Equiv.Perm (Fin 3850)) ∈ hsR := (mem_inf.1 b.2).1
    have hbC := (mem_inf.1 b.2).2
    have hbaC : (b : Equiv.Perm (Fin 3850)) * a ∈ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) :=
      mul_mem hbC haC
    simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf, hbC, and_true, hbaC]
    by_cases hbP : (b : Equiv.Perm (Fin 3850)) ∈ hsP
    · have : ¬ (b : Equiv.Perm (Fin 3850)) * a ∈ hsP := fun h => haP (by
        have := hsP.mul_mem (hsP.inv_mem hbP) h
        simpa using this)
      exact Or.inr ⟨hbP, this⟩
    · refine Or.inl ⟨?_, hbP⟩
      have hba : (b : Equiv.Perm (Fin 3850)) * g⁻¹ ∉ hsP := fun h => hbP (by
        have := hsP.mul_mem h hg
        simpa using this)
      have := hPR' _ (hsR.mul_mem hbR (hPR (hsP.inv_mem hg))) hba
      simpa [ha, mul_assoc] using this
  have hcard := Subgroup.card_mul_index ((hsP ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))).subgroupOf H)
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv] at hcard
  rw [← hcard, mul_comm]

theorem card_hsR_inf_centralizer_ne
    {τ : Equiv.Perm (Fin 3850)} (hτR : τ ∈ hsR)
    (hτ : orderOf τ = 2) :
    Nat.card ↥(hsR ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))) ≠ 2880 := by
  rw [card_hsR_inf_centralizer hτR hτ]
  have := (hsR_invol_cent_order hτR hτ).2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at this
  omega


theorem eq_top_of_card_centralizer_hs
    {X : Type*} [Group X] [Finite X] (S : Subgroup X) [S.Normal]
    (hS : Nonempty (S ≃* CFSG.Blueprint.NativeSporadic.HS))
    (hC : centralizer (S : Set X) = ⊥) {t : X} (ht : orderOf t = 2)
    (hcard : Nat.card ↥(centralizer ({t} : Set X)) = 2880) : S = ⊤ := by
  obtain ⟨ψ⟩ := hS
  set θ : S ≃* hsP := ψ.trans hsPermEquiv with hθ
  have h := hs_autModel
  have hinj := h.embed_injective S θ hC
  obtain ⟨-, -, -, -, -, -, -, -, hRcard, -⟩ := hs_normalizing_model
  have hPcard : Nat.card hsP = 44352000 := card_hsP
  have hSP : Nat.card S = 44352000 := by rw [Nat.card_congr θ.toEquiv, hPcard]
  by_contra hne
  have hXS : 2 * Nat.card S ≤ Nat.card X := by
    have h1 := S.card_mul_index
    have h2 : S.index ≠ 1 := fun h1' => hne (Subgroup.index_eq_one.1 h1')
    have h3 : S.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : 2 ≤ S.index := by omega
    calc 2 * Nat.card S ≤ S.index * Nat.card S := Nat.mul_le_mul_right _ this
      _ = Nat.card X := by rw [mul_comm]; exact h1
  have hrange : (h.embed S θ).range ≤ hsR := by
    rintro _ ⟨x, rfl⟩
    exact h.embed_mem S θ x
  have hX : Nat.card X = Nat.card (h.embed S θ).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hrangeEq : (h.embed S θ).range = hsR :=
    Subgroup.eq_of_le_of_card_ge hrange (by
      rw [← hX, hRcard]; omega)
  set τ := h.embed S θ t with hτdef
  have hτR : τ ∈ hsR := h.embed_mem S θ t
  have hτ2 : orderOf τ = 2 := by rw [hτdef, orderOf_injective _ hinj, ht]
  have hmap : (centralizer ({t} : Set X)).map (h.embed S θ) =
      hsR ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850))) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine mem_inf.2 ⟨h.embed_mem S θ x, ?_⟩
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff] at hx
      rw [mem_centralizer_singleton_iff]
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      have hyR := (mem_inf.1 hy).1
      have hyC := (mem_inf.1 hy).2
      rw [← hrangeEq] at hyR
      obtain ⟨x, rfl⟩ := hyR
      refine ⟨x, ?_, rfl⟩
      rw [mem_centralizer_singleton_iff] at hyC
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact hyC
  have hcard' : Nat.card ↥(hsR ⊓ centralizer ({τ} : Set (Equiv.Perm (Fin 3850)))) = 2880 := by
    rw [← hmap, Subgroup.card_map_of_injective hinj]
    exact hcard
  exact card_hsR_inf_centralizer_ne hτR hτ2 hcard'

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
