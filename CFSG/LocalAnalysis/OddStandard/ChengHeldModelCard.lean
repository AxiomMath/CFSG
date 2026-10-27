module

public import CFSG.LocalAnalysis.OddStandard.ChengHeldSetupCenter
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelFrame
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelLoop
public import CFSG.LocalAnalysis.OddStandard.ChengHeldModelRegular

public section

namespace CFSG.OddStandard.ChengHeld

open Subgroup CFSG.OddStandard.ChengHeldData
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Sporadic.Recognition.PresentedWords CFSG.OddStandard.ChengHeld.Model

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {d : Datum A}

@[expose] def Chart4.fam {α : ℕ} (c : Chart4 d α) : Fin 7 → ↥d.S :=
  ![⟨c.t, c.t_mem.2⟩, ⟨c.pi, c.mem.1⟩, ⟨c.tau, c.mem.2.1⟩, ⟨c.mu, c.mem.2.2.1⟩,
    ⟨c.lam, c.mem.2.2.2.1⟩, ⟨c.ze, c.mem.2.2.2.2.1⟩, ⟨c.xi, c.mem.2.2.2.2.2⟩]

@[expose] def Chart2.fam (c : Chart2 d) : Fin 7 → ↥d.S :=
  ![⟨d.q, c.mem.2.2.2.2.2.2⟩, ⟨c.pi, c.mem.1⟩, ⟨c.tau, c.mem.2.1⟩, ⟨c.mu, c.mem.2.2.1⟩,
    ⟨c.lam, c.mem.2.2.2.1⟩, ⟨c.ze, c.mem.2.2.2.2.1⟩, ⟨c.xi, c.mem.2.2.2.2.2.1⟩]

@[expose] def Chart4.famG {α : ℕ} (c : Chart4 d α) : Fin 7 → G :=
  ![c.t, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi]

@[expose] def Chart2.famG (c : Chart2 d) : Fin 7 → G :=
  ![d.q, c.pi, c.tau, c.mu, c.lam, c.ze, c.xi]

theorem Chart4.subtype_fam {α : ℕ} (c : Chart4 d α) (j : Fin 7) :
    ((c.fam j : ↥d.S) : G) = c.famG j := by
  fin_cases j <;> rfl

theorem Chart2.subtype_fam (c : Chart2 d) (j : Fin 7) :
    ((c.fam j : ↥d.S) : G) = c.famG j := by
  fin_cases j <;> rfl

theorem range_seven {E : Type*} (a b c d e f g : E) :
    Set.range ![a, b, c, d, e, f, g] = ({a, b, c, d, e, f, g} : Set E) := by
  ext x
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, rfl⟩
    fin_cases j <;> simp
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩

theorem closure_fam_of {x : Fin 7 → ↥d.S}
    (hgen : Subgroup.closure (Set.range fun j => ((x j : ↥d.S) : G)) = d.S) :
    Subgroup.closure (Set.range x) = ⊤ := by
  refine Subgroup.map_injective d.S.subtype_injective ?_
  rw [MonoidHom.map_closure, Subgroup.map_top, Subgroup.range_subtype, ← Set.range_comp]
  exact hgen

theorem Chart4.closure_fam {α : ℕ} (c : Chart4 d α) : Subgroup.closure (Set.range c.fam) = ⊤ := by
  refine closure_fam_of ?_
  have : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
  rw [this, Chart4.famG, range_seven]
  exact c.gen

theorem Chart2.closure_fam (c : Chart2 d) : Subgroup.closure (Set.range c.fam) = ⊤ := by
  refine closure_fam_of ?_
  have : (fun j => ((c.fam j : ↥d.S) : G)) = c.famG := funext c.subtype_fam
  rw [this, Chart2.famG, range_seven]
  exact c.gen

theorem Chart4.wprod_fam {α : ℕ} (c : Chart4 d α) : ∀ w ∈ relWords4 α, wprod c.fam w = 1 := by
  intro w hw
  refine d.S.subtype_injective ?_
  have h1 := map_wprod d.S.subtype c.fam w
  have h2 : (fun i => d.S.subtype (c.fam i)) = c.famG := funext c.subtype_fam
  rw [h2] at h1
  rw [h1, map_one]
  exact wprod_relWords4 α c.famG c.frame w hw

theorem Chart2.wprod_fam (c : Chart2 d) : ∀ w ∈ relWords2, wprod c.fam w = 1 := by
  intro w hw
  refine d.S.subtype_injective ?_
  have h1 := map_wprod d.S.subtype c.fam w
  have h2 : (fun i => d.S.subtype (c.fam i)) = c.famG := funext c.subtype_fam
  rw [h2] at h1
  rw [h1, map_one]
  exact wprod_relWords2 c.famG c.frame w hw

theorem card_le_of_rels (hP : chPresOK = true) {α : ℕ} (hα : α ≤ 2) {H : Type} [Group H]
    [Finite H] (x : Fin 7 → H) (hrel : ∀ w ∈ regRelWords α, wprod x w = 1)
    (hgen : Subgroup.closure (Set.range x) = ⊤) : Nat.card H ≤ regN α := by
  obtain ⟨hfin, hpres⟩ := pres_card hP hα
  have hs : Function.Surjective (pgHom x hrel) := by
    rw [← MonoidHom.range_eq_top, range_pgHom', hgen]
  exact (Nat.card_le_card_of_surjective _ hs).trans hpres

theorem Datum.dvd_card_S (h : Hyp G A) (d : Datum A) {z : G} (hz : z ∈ A)
    (hzc : z ∈ centralizer (A : Set G)) {k : ℕ} (hk : orderOf z = 2 ^ k) :
    2 ^ (k + 6) ∣ Nat.card ↥d.S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardA : Nat.card ↥A = 20160 * Nat.card (center ↥A) := by
    rw [← h.card_quotient]
    exact card_eq_card_quotient_mul_card_subgroup (center ↥A)
  have hzcenter : (⟨z, hz⟩ : ↥A) ∈ center ↥A := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext (mem_centralizer_iff.1 hzc g g.2)
  have hdvd : 2 ^ k ∣ Nat.card (center ↥A) := by
    have h1 : orderOf (⟨⟨z, hz⟩, hzcenter⟩ : center ↥A) ∣ Nat.card (center ↥A) :=
      orderOf_dvd_natCard _
    have h2 : orderOf (⟨⟨z, hz⟩, hzcenter⟩ : center ↥A) = orderOf z := by
      rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe]
    rwa [h2, hk] at h1
  have hne : Nat.card (center ↥A) ≠ 0 := Nat.card_pos.ne'
  rw [d.S_sylow.card_eq, hcardA]
  have h6 : (20160 : ℕ).factorization 2 = 6 := by
    have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two]
    simp [Nat.factorization_eq_zero_of_not_dvd (show ¬ 2 ∣ 315 by norm_num)]
  rw [Nat.factorization_mul (by norm_num) hne, Finsupp.add_apply, h6]
  have h2 : k ≤ (Nat.card (center ↥A)).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1 hdvd
  exact pow_dvd_pow 2 (by omega)

theorem Chart4.orderOf_t {α : ℕ} (c : Chart4 d α) : orderOf c.t = 4 := by
  have h2 : c.t ^ 2 ^ 1 ≠ 1 := by
    intro h
    have hq : d.q = 1 := by rw [c.q_eq]; simpa using h
    have := d.q_ord
    rw [hq, orderOf_one] at this
    omega
  have h4 : c.t ^ 2 ^ (1 + 1) = 1 := by simpa using c.frame.t4
  simpa using orderOf_eq_prime_pow h2 h4

theorem Chart4.card_S {α : ℕ} (hα : α ≤ 1) (c : Chart4 d α) (h : Hyp G A)
    (hP : chPresOK = true) : Nat.card ↥d.S = 256 := by
  have hge : 2 ^ (2 + 6) ∣ Nat.card ↥d.S :=
    Datum.dvd_card_S h d (d.S_le_A c.t_mem.2) (d.Q_le_centralizer c.t_mem.1)
      (k := 2) (by rw [c.orderOf_t]; norm_num)
  have hrel : ∀ w ∈ regRelWords α, wprod c.fam w = 1 := by
    intro w hw
    have : regRelWords α = relWords4 α := by simp [regRelWords, show α ≠ 2 by omega]
    rw [this] at hw
    exact c.wprod_fam w hw
  have hle := card_le_of_rels hP (α := α) (by omega) c.fam hrel c.closure_fam
  have hN : regN α = 256 := by simp [regN, show α ≠ 2 by omega]
  rw [hN] at hle
  have hpos : 0 < Nat.card ↥d.S := Nat.card_pos
  have := Nat.le_of_dvd hpos hge
  exact le_antisymm hle (by simpa using this)

theorem Chart2.card_S (c : Chart2 d) (h : Hyp G A) (hP : chPresOK = true) :
    Nat.card ↥d.S = 128 := by
  have hge : 2 ^ (1 + 6) ∣ Nat.card ↥d.S :=
    Datum.dvd_card_S h d d.q_mem d.q_cent (k := 1) (by rw [d.q_ord]; norm_num)
  have hrel : ∀ w ∈ regRelWords 2, wprod c.fam w = 1 := by
    intro w hw
    have : regRelWords 2 = relWords2 := by simp [regRelWords]
    rw [this] at hw
    exact c.wprod_fam w hw
  have hle := card_le_of_rels hP (α := 2) (by omega) c.fam hrel c.closure_fam
  have hN : regN 2 = 128 := by simp [regN]
  rw [hN] at hle
  have hpos : 0 < Nat.card ↥d.S := Nat.card_pos
  have := Nat.le_of_dvd hpos hge
  exact le_antisymm hle (by simpa using this)

end CFSG.OddStandard.ChengHeld
