module

public import Certificates.Data.Kernel.NPL587K
public import CFSG.Quasithin.Vol2.Ch12Sec6P31WNPLSoundB
public import Mathlib.GroupTheory.Perm.Centralizer

public section

namespace CFSG.Quasithin.H13.NPLKSound

open CFSG.Quasithin.H13.NPL CFSG.Quasithin.H13.NPLK CFSG.Quasithin.H13.NPLSound

@[expose] def S0K : Subgroup (Equiv.Perm (Fin 8)) :=
  Subgroup.closure {g : Equiv.Perm (Fin 8) | g ∈ S0gens ()}

theorem gen_mem {g : Equiv.Perm (Fin 8)} (hg : g ∈ S0gens ()) : g ∈ S0K :=
  Subgroup.subset_closure hg

theorem mem_gens {a : ℕ} (ha : a ∈ S0codes ()) : ∃ π ∈ S0K, encP π = a := by
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp (ha : a ∈ (S0gens ()).map encP)
  exact ⟨g, gen_mem hg, rfl⟩

theorem memB_iff (S : List ℕ) (c : ℕ) : memB S c = true ↔ c ∈ S := by
  simp [memB]

theorem incB_spec : ∀ (a : ℕ) (l : List ℕ), incB a l = true →
    (∀ x ∈ l, a < x) ∧ l.Pairwise (· < ·)
  | _, [], _ => ⟨by simp, List.Pairwise.nil⟩
  | a, b :: t, h => by
    simp only [incB, Bool.and_eq_true, Nat.blt_eq] at h
    obtain ⟨hab, ht⟩ := h
    obtain ⟨h1, h2⟩ := incB_spec b t ht
    refine ⟨fun x hx => ?_, List.pairwise_cons.mpr ⟨h1, h2⟩⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hab
    · exact lt_trans hab (h1 x hx)

theorem wordL_mem (H : Subgroup (Equiv.Perm (Fin 8))) (w : List ℕ)
    (hw : ∀ a ∈ w, ∃ π ∈ H, encP π = a) : ∃ π ∈ H, encP π = wordL w := by
  unfold wordL
  suffices h : ∀ π0 : Equiv.Perm (Fin 8), π0 ∈ H → ∃ π ∈ H, encP π = w.foldl mulC (encP π0) by
    rw [idC_eq]
    exact h 1 H.one_mem
  induction w with
  | nil => exact fun π0 h0 => ⟨π0, h0, rfl⟩
  | cons a t ih =>
    intro π0 h0
    obtain ⟨π, hπ, rfl⟩ := hw a List.mem_cons_self
    rw [List.foldl_cons, mulC_encP]
    exact ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)) _ (H.mul_mem h0 hπ)

structure S0Facts (s0 : List ℕ) : Prop where
  code : ∀ c ∈ s0, ∃ π ∈ S0K, encP π = c
  mem : ∀ π ∈ S0K, encP π ∈ s0
  card : Nat.card S0K = 64
  pow4 : ∀ c ∈ s0, powC c 4 = idC ()

theorem s0Facts_of {gens s0 : List ℕ} {s0w : List (ℕ × List ℕ)}
    (h : s0OK gens s0 s0w = true) : S0Facts s0 := by
  simp only [s0OK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, memB_iff] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, hw⟩, hlen⟩, hinc⟩, hwords⟩, hcl⟩, hid⟩, hinv⟩, hpow⟩ := h
  subst hg
  have hcode : ∀ c ∈ s0, ∃ π ∈ S0K, encP π = c := by
    intro c hc
    rw [← hw] at hc
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hl, hwe⟩ := hwords e he
    rw [← hwe]
    exact wordL_mem S0K e.2 fun a ha => mem_gens (hl a ha)
  have hmul_self : ∀ g ∈ S0gens (), g * g = 1 := by
    intro g hg
    apply encP_injective
    rw [← mulC_encP, hinv _ (List.mem_map_of_mem hg), idC_eq]
  have hmem : ∀ π ∈ S0K, encP π ∈ s0 := by
    have key : ∀ x ∈ S0K, (∀ c ∈ s0, mulC c (encP x) ∈ s0) ∧
        (∀ c ∈ s0, mulC c (encP x⁻¹) ∈ s0) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        have hx' : x ∈ S0gens () := hx
        have hxx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hmul_self x hx')
        have hc : encP x ∈ S0codes () := List.mem_map_of_mem hx'
        rw [hxx]
        exact ⟨fun c h => hcl c h _ hc, fun c h => hcl c h _ hc⟩
      | one =>
        have h1 : ∀ c ∈ s0, mulC c (encP 1) = c := by
          intro c hc
          obtain ⟨a, -, rfl⟩ := hcode c hc
          rw [mulC_encP, mul_one]
        exact ⟨fun c hc => by rw [h1 c hc]; exact hc,
          fun c hc => by rw [inv_one, h1 c hc]; exact hc⟩
      | mul x y _ _ ihx ihy =>
        refine ⟨fun c hc => ?_, fun c hc => ?_⟩
        · obtain ⟨a, -, rfl⟩ := hcode _ hc
          rw [← mulC_encP x y, show mulC (encP a) (mulC (encP x) (encP y)) =
            mulC (mulC (encP a) (encP x)) (encP y) by rw [mulC_encP, mulC_encP, mulC_encP,
              mulC_encP, mul_assoc]]
          exact ihy.1 _ (ihx.1 _ hc)
        · obtain ⟨a, -, rfl⟩ := hcode _ hc
          rw [mul_inv_rev, ← mulC_encP, show mulC (encP a) (mulC (encP y⁻¹) (encP x⁻¹)) =
            mulC (mulC (encP a) (encP y⁻¹)) (encP x⁻¹) by rw [mulC_encP, mulC_encP, mulC_encP,
              mulC_encP, mul_assoc]]
          exact ihx.2 _ (ihy.2 _ hc)
      | inv x _ ihx =>
        rw [inv_inv]
        exact ⟨ihx.2, ihx.1⟩
    intro π hπ
    have h1 := (key π hπ).1 (idC ()) hid
    rwa [idC_eq, mulC_encP, one_mul] at h1
  refine ⟨hcode, hmem, ?_, hpow⟩
  have hnd : s0.Nodup := (incB_spec 0 s0 hinc).2.imp (fun h => ne_of_lt h)
  have hbij : Function.Bijective
      (fun h : S0K => (⟨encP h.1, List.mem_toFinset.mpr (hmem h.1 h.2)⟩ : ↥s0.toFinset)) := by
    constructor
    · intro a b hab
      exact Subtype.ext (encP_injective (congrArg Subtype.val hab))
    · rintro ⟨c, hc⟩
      obtain ⟨a, ha, rfl⟩ := hcode c (List.mem_toFinset.mp hc)
      exact ⟨⟨a, ha⟩, rfl⟩
  calc Nat.card S0K = Nat.card ↥s0.toFinset := Nat.card_eq_of_bijective _ hbij
    _ = s0.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = 64 := by rw [List.toFinset_card_of_nodup hnd, hlen]

theorem pairsOK_spec (S : List ℕ) : ∀ E : List (ℕ × ℕ × List ℕ × List ℕ), pairsOK S E = true →
    E.Pairwise (fun a b => mulC a.1 b.2.1 ∉ S)
  | [], _ => List.Pairwise.nil
  | a :: t, h => by
    simp only [pairsOK, Bool.and_eq_true, List.all_eq_true] at h
    refine List.pairwise_cons.mpr ⟨fun b hb hm => ?_, pairsOK_spec S t h.2⟩
    have h1 := h.1 b hb
    rw [(memB_iff S _).mpr hm] at h1
    simp at h1

theorem lett_mem {L : Subgroup (Equiv.Perm (Fin 8))} (hL : S0K ≤ L) {ρ : Equiv.Perm (Fin 8)}
    (hρ : ρ ∈ L) (o : ℕ) (w : List ℕ) (hw : lettOK (S0codes ()) w = true) :
    ∃ π ∈ L, encP π = wordR (encP ρ) o w := by
  unfold wordR
  apply wordL_mem
  intro b hb
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  have h := List.all_eq_true.mp hw a ha
  simp only [Bool.or_eq_true, beq_iff_eq, memB_iff] at h
  unfold lettC
  by_cases h0 : a = 0
  · simp only [h0, beq_self_eq_true, if_true]
    exact ⟨ρ, hρ, rfl⟩
  by_cases h1 : a = 1
  · simp only [h1, beq_self_eq_true, if_true, Nat.one_ne_zero, beq_iff_eq, if_false]
    exact ⟨ρ ^ (o - 1), L.pow_mem hρ _, (powC_encP ρ (o - 1)).symm⟩
  have hg : a ∈ S0codes () := by
    rcases h with (h | h) | h
    · exact absurd h h0
    · exact absurd h h1
    · exact h
  have h0' : (a == 0) = false := by simpa using h0
  have h1' : (a == 1) = false := by simpa using h1
  rw [h0', h1']
  obtain ⟨π, hπ, he⟩ := mem_gens hg
  exact ⟨π, hL hπ, he⟩

theorem rep_sound {s0 : List ℕ} (hS : S0Facts s0)
    {e : ℕ × ℕ × List ℕ × List (ℕ × ℕ × List ℕ × List ℕ)}
    (he : repOK (S0codes ()) s0 e = true) :
    ∃ ρ : Equiv.Perm (Fin 8), encP ρ = e.1 ∧ (e.2.1 = 5 ∨ e.2.1 = 7) ∧ ρ ^ e.2.1 = 1 ∧
      ∀ L : Subgroup (Equiv.Perm (Fin 8)), S0K ≤ L → ρ ∈ L → 512 ≤ Nat.card L := by
  simp only [repOK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, List.all_eq_true] at he
  obtain ⟨⟨⟨⟨⟨⟨ho, hpow⟩, hrw⟩, hword⟩, hlen⟩, hx⟩, hpair⟩ := he
  obtain ⟨ρ, -, hρ⟩ := wordL_mem ⊤ e.2.2.1 fun a ha => by
    obtain ⟨g, -, rfl⟩ := List.mem_map.mp ((memB_iff _ _).mp (hrw a ha) :
      a ∈ (tgens ()).map encP)
    exact ⟨g, Subgroup.mem_top g, rfl⟩
  rw [hword] at hρ
  refine ⟨ρ, hρ, ho, ?_, ?_⟩
  · apply encP_injective
    rw [← powC_encP, hρ, hpow, idC_eq]
  intro L hL hρL
  have hxs : ∀ x ∈ e.2.2.2, ∃ ξ ∈ L, encP ξ = x.1 ∧ encP ξ⁻¹ = x.2.1 := by
    intro x hxm
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hx x hxm
    obtain ⟨ξ, hξ, e1⟩ := lett_mem hL hρL e.2.1 _ h1
    obtain ⟨ξ', -, e2⟩ := lett_mem hL hρL e.2.1 _ h2
    rw [← hρ] at h3 h4
    rw [h3] at e1
    rw [h4] at e2
    have hinv : ξ' * ξ = 1 := by
      apply encP_injective
      rw [← mulC_encP, e1, e2, h5, idC_eq]
    exact ⟨ξ, hξ, e1, by rw [← eq_inv_of_mul_eq_one_left hinv, e2]⟩
  have hP := pairsOK_spec s0 _ hpair
  have hx' : ∀ i : Fin 8, ∃ ξ ∈ L, encP ξ = (e.2.2.2[i.1]'(by omega)).1 ∧
      encP ξ⁻¹ = (e.2.2.2[i.1]'(by omega)).2.1 := fun i => hxs _ (List.getElem_mem _)
  choose ξ hξL hξ1 hξ2 using hx'
  have hS0L : ∀ h ∈ S0K, h ∈ L := fun h hh => hL hh
  let f : S0K × Fin 8 → L := fun p => ⟨p.1.1 * ξ p.2, L.mul_mem (hS0L _ p.1.2) (hξL p.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨h, i⟩ ⟨h', j⟩ hij
    have heq : h.1 * ξ i = h'.1 * ξ j := congrArg Subtype.val hij
    have hij' : i = j := by
      by_contra hne
      have hm : ξ i * (ξ j)⁻¹ ∈ S0K := by
        have : ξ i * (ξ j)⁻¹ = h.1⁻¹ * h'.1 := by
          rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, heq, mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact S0K.mul_mem (S0K.inv_mem h.2) h'.2
      have hm' : ξ j * (ξ i)⁻¹ ∈ S0K := by
        have : ξ j * (ξ i)⁻¹ = (ξ i * (ξ j)⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
        rw [this]
        exact S0K.inv_mem hm
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
      · apply List.pairwise_iff_getElem.mp hP i.1 j.1 (by omega) (by omega) hlt
        rw [← hξ1 i, ← hξ2 j, mulC_encP]
        exact hS.mem _ hm
      · apply List.pairwise_iff_getElem.mp hP j.1 i.1 (by omega) (by omega) hlt
        rw [← hξ1 j, ← hξ2 i, mulC_encP]
        exact hS.mem _ hm'
    subst hij'
    exact Prod.ext (Subtype.ext (mul_right_cancel heq)) rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, hS.card, Nat.card_eq_fintype_card (α := Fin 8), Fintype.card_fin] at this

theorem rec_sound {gens s0 : List ℕ} {s0w : List (ℕ × List ℕ)}
    {reps : List (ℕ × ℕ × List ℕ × List (ℕ × ℕ × List ℕ × List ℕ))} {repc qc : List ℕ}
    {ql : List (ℕ × ℕ × ℕ × ℕ)} (hs0 : s0OK gens s0 s0w = true)
    (hreps : reps.all (repOK gens s0) = true) (hrepc : (repc == reps.map Prod.fst) = true)
    (hql : ql.all (qOK repc) = true) (hqc : (qc == ql.map Prod.fst) = true) {q h : ℕ}
    (hq : q ∈ qc) (hh : h ∈ s0) :
    ∃ σ : Equiv.Perm (Fin 8), encP σ = tauC q h ∧ σ ≠ 1 ∧ (σ ^ 5 = 1 ∨ σ ^ 7 = 1) ∧
      448 < Nat.card (Subgroup.closure (insert σ (S0K : Set (Equiv.Perm (Fin 8))))) := by
  have hS := s0Facts_of hs0
  have hg : gens = S0codes () := by
    simp only [s0OK, Bool.and_eq_true, beq_iff_eq] at hs0
    exact hs0.1.1.1.1.1.1.1.1
  subst hg
  rw [beq_iff_eq] at hrepc hqc
  subst hrepc hqc
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hq
  have hqe := List.all_eq_true.mp hql e he
  simp only [qOK, Bool.and_eq_true, beq_iff_eq, memB_iff] at hqe
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hqe
  obtain ⟨R, hR, hRr⟩ := List.mem_map.mp h1
  obtain ⟨ρ, hρ, ho, hρo, hL⟩ := rep_sound hS (List.all_eq_true.mp hreps R hR)
  rw [hRr] at hρ
  set ψ := ρ ^ e.2.2.1 with hψdef
  have hψ : encP ψ = e.1 := by rw [hψdef, ← powC_encP, hρ, h2]
  have hψk : ψ ^ e.2.2.2 = ρ := by
    apply encP_injective
    rw [← powC_encP, hψ, h3, hρ]
  have hψ1 : ψ ≠ 1 := by
    intro h1
    rw [h1, ← idC_eq] at hψ
    rw [hψ] at h4
    simp at h4
  obtain ⟨η, hηS, hη⟩ := hS.code h hh
  have hη4 : η ^ 4 = 1 := by
    apply encP_injective
    rw [← powC_encP, hη, hS.pow4 h hh, idC_eq]
  have hη3 : η ^ 3 = η⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← pow_succ]; exact hη4)
  refine ⟨η * ψ * η⁻¹, ?_, ?_, ?_, ?_⟩
  · rw [tauC, ← hη, ← hψ, mulC_encP, powC_encP, mulC_encP, hη3]
  · intro hσ
    apply hψ1
    have : ψ = η⁻¹ * (η * ψ * η⁻¹) * η := by group
    rw [this, hσ]
    group
  · have hψo : ψ ^ R.2.1 = 1 := by
      rw [hψdef, ← pow_mul, mul_comm, pow_mul, hρo, one_pow]
    have hσo : (η * ψ * η⁻¹) ^ R.2.1 = 1 := by
      rw [conj_pow, hψo, mul_one, mul_inv_cancel]
    rcases ho with h5 | h7
    · left
      rwa [h5] at hσo
    · right
      rwa [h7] at hσo
  · set L := Subgroup.closure (insert (η * ψ * η⁻¹) (S0K : Set (Equiv.Perm (Fin 8))))
    have hS0L : S0K ≤ L := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
    have hσL : η * ψ * η⁻¹ ∈ L := Subgroup.subset_closure (Set.mem_insert _ _)
    have hψL : ψ ∈ L := by
      have : ψ = η⁻¹ * (η * ψ * η⁻¹) * η := by group
      rw [this]
      exact L.mul_mem (L.mul_mem (L.inv_mem (hS0L hηS)) hσL) (hS0L hηS)
    have hρL : ρ ∈ L := by
      rw [← hψk]
      exact L.pow_mem hψL _
    have := hL L hS0L hρL
    omega

theorem cycleType_iff (σ : Equiv.Perm (Fin 8)) (p : ℕ) (hp : p = 5 ∨ p = 7) :
    (σ ≠ 1 ∧ σ ^ p = 1) ↔ σ.cycleType = {p} := by
  have hpr : p.Prime := by rcases hp with rfl | rfl <;> decide
  have : Fact p.Prime := ⟨hpr⟩
  constructor
  · rintro ⟨h1, hp1⟩
    have hord : orderOf σ = p := orderOf_eq_prime hp1 h1
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (hord ▸ hpr)
    have hsum := Equiv.Perm.sum_cycleType_le σ
    rw [hn, Multiset.sum_replicate, hord, Fintype.card_fin, smul_eq_mul] at hsum
    have hn0 : n = 0 := by rcases hp with rfl | rfl <;> omega
    rw [hn, hn0, hord]
    rfl
  · intro hc
    have hord : orderOf σ = p := by
      rw [← Equiv.Perm.lcm_cycleType, hc, Multiset.lcm_singleton, normalize_eq]
    refine ⟨fun h1 => ?_, by rw [← hord]; exact pow_orderOf_eq_one σ⟩
    rw [h1, orderOf_one] at hord
    rcases hp with rfl | rfl <;> omega

theorem card_X : (Finset.univ.filter fun σ : Equiv.Perm (Fin 8) =>
    σ ≠ 1 ∧ (σ ^ 5 = 1 ∨ σ ^ 7 = 1)).card = 7104 := by
  have hX : (Finset.univ.filter fun σ : Equiv.Perm (Fin 8) => σ ≠ 1 ∧ (σ ^ 5 = 1 ∨ σ ^ 7 = 1)) =
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {5}) ∪
        (Finset.univ.filter fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {7}) := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
      ← cycleType_iff σ 5 (Or.inl rfl), ← cycleType_iff σ 7 (Or.inr rfl)]
    tauto
  have hdisj : Disjoint (Finset.univ.filter fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {5})
      (Finset.univ.filter fun σ : Equiv.Perm (Fin 8) => σ.cycleType = {7}) := by
    rw [Finset.disjoint_filter]
    intro σ _ h5 h7
    rw [h5] at h7
    simp at h7
  rw [hX, Finset.card_union_of_disjoint hdisj, Equiv.Perm.card_of_cycleType,
    Equiv.Perm.card_of_cycleType]
  simp [Nat.factorial]

theorem sound {gens s0 : List ℕ} {s0w : List (ℕ × List ℕ)}
    {reps : List (ℕ × ℕ × List ℕ × List (ℕ × ℕ × List ℕ × List ℕ))} {repc qc : List ℕ}
    {ql : List (ℕ × ℕ × ℕ × ℕ)} {recs : List (ℕ × ℕ)} {a : ℕ} (hs0 : s0OK gens s0 s0w = true)
    (hreps : reps.all (repOK gens s0) = true) (hrepc : (repc == reps.map Prod.fst) = true)
    (hql : ql.all (qOK repc) = true) (hqc : (qc == ql.map Prod.fst) = true)
    (hrec : ∀ p ∈ recs, p.1 ∈ qc ∧ p.2 ∈ s0)
    (hinc : incB a (recs.map fun p => tauC p.1 p.2) = true) (hlen : recs.length = 7104) :
    Nat.card S0K = 64 ∧ ∀ σ : Equiv.Perm (Fin 8), σ ≠ 1 → (σ ^ 5 = 1 ∨ σ ^ 7 = 1) →
      448 < Nat.card (Subgroup.closure (insert σ (S0K : Set (Equiv.Perm (Fin 8))))) := by
  refine ⟨(s0Facts_of hs0).card, fun σ h1 h57 => ?_⟩
  set T := recs.map fun p => tauC p.1 p.2 with hT
  have hnd : T.Nodup := (incB_spec a T hinc).2.imp (fun h => ne_of_lt h)
  set X := Finset.univ.filter fun σ : Equiv.Perm (Fin 8) => σ ≠ 1 ∧ (σ ^ 5 = 1 ∨ σ ^ 7 = 1)
  have hsub : T.toFinset ⊆ X.image encP := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ht)
    obtain ⟨τ, hτ, hτ1, hτ57, -⟩ := rec_sound hs0 hreps hrepc hql hqc (hrec p hp).1 (hrec p hp).2
    exact Finset.mem_image.mpr ⟨τ, by simp [X, hτ1, hτ57], hτ⟩
  have hcard : (X.image encP).card ≤ T.toFinset.card := by
    rw [Finset.card_image_of_injective _ encP_injective, card_X, List.toFinset_card_of_nodup hnd,
      hT, List.length_map, hlen]
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hσ : encP σ ∈ T.toFinset := by
    rw [heq]
    exact Finset.mem_image_of_mem _ (by simp [X, h1, h57])
  obtain ⟨p, hp, hpσ⟩ := List.mem_map.mp (List.mem_toFinset.mp hσ)
  obtain ⟨τ, hτ, -, -, hbig⟩ := rec_sound hs0 hreps hrepc hql hqc (hrec p hp).1 (hrec p hp).2
  rw [hpσ] at hτ
  rwa [← encP_injective hτ]

theorem covOK_cons {S qc : List ℕ} {lo hi : ℕ} {L : List (ℕ × ℕ)} (h : covOK S qc lo hi L = true)
    {R : List (ℕ × ℕ)} (hR : (∀ p ∈ R, p.1 ∈ qc ∧ p.2 ∈ S) ∧
      incB hi (R.map fun p => tauC p.1 p.2) = true) :
    (∀ p ∈ L ++ R, p.1 ∈ qc ∧ p.2 ∈ S) ∧ incB lo ((L ++ R).map fun p => tauC p.1 p.2) = true := by
  unfold covOK at h
  induction L generalizing lo with
  | nil =>
    simp only [covGo, beq_iff_eq] at h
    subst h
    simpa using hR
  | cons p t ih =>
    simp only [covGo, Bool.and_eq_true, memB_iff] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    obtain ⟨ih1, ih2⟩ := ih h4
    refine ⟨fun x hx => ?_, ?_⟩
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact ⟨h1, h2⟩
      · exact ih1 x hx
    · simp only [List.cons_append, List.map_cons, incB, Bool.and_eq_true]
      exact ⟨h3, ih2⟩

end CFSG.Quasithin.H13.NPLKSound

end
