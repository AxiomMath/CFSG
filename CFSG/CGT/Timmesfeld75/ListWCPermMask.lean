module

public import CFSG.CGT.Timmesfeld75.ListWCPermMain

public section

namespace CFSG.CGT.Timmesfeld75.WCCheck

open CFSG.Open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem mem_allMasks : ∀ l : List Bool, l ∈ allMasks l.length
  | [] => List.mem_singleton_self _
  | b :: l => by
    simp only [List.length_cons, allMasks, List.mem_flatMap]
    exact ⟨l, mem_allMasks l, by cases b <;> simp⟩

theorem filter_zip_map {α : Type*} (f : α → Bool) :
    ∀ L : List α, ((L.zip (L.map f)).filter fun p => p.2).map Prod.fst = L.filter f
  | [] => rfl
  | a :: L => by
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons]
    cases f a <;> simp [filter_zip_map f L]

theorem selCls_map (D : Data) (f : List (ℕ × List ℤ) → Bool) :
    selCls D (D.cls.map f) = D.cls.filter f :=
  filter_zip_map f D.cls

theorem card_eq_length_of_mem_iff {G : Type*} [Group G] {T : Subgroup G} {l : List G}
    (hl : l.Nodup) (h : ∀ x, x ∈ T ↔ x ∈ l) : Nat.card T = l.length := by
  rw [← Nat.card_fin l.length]
  symm
  refine Nat.card_eq_of_bijective (fun i : Fin l.length => (⟨l.get i, (h _).2 (List.get_mem ..)⟩ :
    T)) ⟨fun i j hij => (hl.get_inj_iff).1 (congrArg Subtype.val hij), ?_⟩
  rintro ⟨x, hx⟩
  obtain ⟨i, hi⟩ := List.get_of_mem ((h x).1 hx)
  exact ⟨i, Subtype.ext hi⟩

variable {D : Data} {M : Subgroup (Equiv.Perm (Fin D.n))} {genG : ℤ → M}

section

variable (hn : D.n < 2 ^ 32) (hgen : ∀ l, Rep D.n (D.gens l) (genG l))
  (hinv : ∀ l, genG (-l) = (genG l)⁻¹) (hF : Facts D)
include hn hgen hinv hF

theorem exists_conj_of_mem_cls {c : List (ℕ × List ℤ)} (hc : c ∈ D.cls) :
    ∃ i₀, (∃ w₀, (i₀, w₀) ∈ c) ∧ ∀ q ∈ c, ∃ g : M, g * zG D genG = zG D genG * g ∧
      g * eltG (pcG D genG) i₀ * g⁻¹ = eltG (pcG D genG) q.1 := by
  have h := hF.classes c hc
  match c, hc, h with
  | [], _, h => exact absurd h Bool.false_ne_true
  | (i₀, w₀) :: rest, _, h =>
    refine ⟨i₀, ⟨w₀, List.mem_cons_self ..⟩, fun q hq => ?_⟩
    simp only [List.all_eq_true, Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h q hq
    have hrw := rep_wT hn hgen q.2
    have hrwi := rep_wT hn hgen (invWord q.2)
    rw [wG_invWord hinv] at hrwi
    refine ⟨wG D genG q.2, eq_of_rep ((compT_eq_of_commT h1) ▸
      Rep.compT hrw (rep_el hn hgen D.zIdx)) (Rep.compT (rep_el hn hgen D.zIdx) hrw), ?_⟩
    exact eq_of_beq (Rep.compT (Rep.compT hrw (rep_el hn hgen i₀)) hrwi) (rep_el hn hgen q.1) h2

theorem mem_of_mem_cls {T : Subgroup M} (hT : IsWC T) (hz : zG D genG ∈ T)
    {c : List (ℕ × List ℤ)} (hc : c ∈ D.cls) {p : ℕ × List ℤ} (hp : p ∈ c)
    (hpT : eltG (pcG D genG) p.1 ∈ T) {q : ℕ × List ℤ} (hq : q ∈ c) :
    eltG (pcG D genG) q.1 ∈ T := by
  obtain ⟨i₀, -, hcl⟩ := exists_conj_of_mem_cls hn hgen hinv hF hc
  obtain ⟨gp, hgpz, hgp⟩ := hcl p hp
  obtain ⟨gq, hgqz, hgq⟩ := hcl q hq
  have hNp := mem_normalizer_of_comm_z hn hgen hF hT hz hgpz
  have hNq := mem_normalizer_of_comm_z hn hgen hF hT hz hgqz
  have h0 : eltG (pcG D genG) i₀ ∈ T := by
    have := conj_mem (Subgroup.inv_mem _ hNp) hpT
    rwa [← hgp, inv_inv, show gp⁻¹ * (gp * eltG (pcG D genG) i₀ * gp⁻¹) * gp =
      eltG (pcG D genG) i₀ by group] at this
  rw [← hgq]
  exact conj_mem hNq h0

theorem conj_of_mem_cls_head {i₀ : ℕ} {w₀ : List ℤ} {rest : List (ℕ × List ℤ)}
    (hc : (i₀, w₀) :: rest ∈ D.cls) : ∀ q ∈ (i₀, w₀) :: rest, ∃ g : M,
      g * zG D genG = zG D genG * g ∧ g * eltG (pcG D genG) i₀ * g⁻¹ = eltG (pcG D genG) q.1 := by
  have h := hF.classes _ hc
  simp only [List.all_eq_true, Bool.and_eq_true] at h
  intro q hq
  obtain ⟨h1, h2⟩ := h q hq
  have hrw := rep_wT hn hgen q.2
  have hrwi := rep_wT hn hgen (invWord q.2)
  rw [wG_invWord hinv] at hrwi
  refine ⟨wG D genG q.2, eq_of_rep ((compT_eq_of_commT h1) ▸
    Rep.compT hrw (rep_el hn hgen D.zIdx)) (Rep.compT (rep_el hn hgen D.zIdx) hrw), ?_⟩
  exact eq_of_beq (Rep.compT (Rep.compT hrw (rep_el hn hgen i₀)) hrwi) (rep_el hn hgen q.1) h2

omit hn hgen hinv in
theorem ne_nil_of_mem_cls {c : List (ℕ × List ℤ)} (hc : c ∈ D.cls) : c ≠ [] := by
  rintro rfl
  exact absurd (hF.classes _ hc) Bool.false_ne_true

end

end CFSG.CGT.Timmesfeld75.WCCheck
