module

public import CFSG.LocalAnalysis.ComponentClassification.GSYard03Cat
import CFSG.LocalAnalysis.ComponentClassification.GSYard03L4U4
import CFSG.LocalAnalysis.ComponentClassification.GSYard02CoverAltBase

public section

namespace CFSG.ComponentClassification.Sol76.Sig.GSYard03

open CFSG Subgroup Equiv Equiv.Perm
open scoped commutatorElement

section PermLemmas

variable {α : Type*} [DecidableEq α]

private theorem perm_conj_one {p q s t : α} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) :
    (swap q s * swap s t) * (swap p q * swap s t) * (swap q s * swap s t)⁻¹ =
      swap p s * swap q t := by
  ext i
  simp only [mul_inv_rev, swap_inv, Perm.mul_apply, swap_apply_def]
  grind

private theorem perm_conj_two {p q s t : α} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) :
    (swap p q * swap s t) * (swap p s * swap q t) =
      (swap q s * swap s t) * (swap p s * swap q t) * (swap q s * swap s t)⁻¹ := by
  ext i
  simp only [mul_inv_rev, swap_inv, Perm.mul_apply, swap_apply_def]
  grind

private theorem perm_commutator {e f g h : α} (hef : e ≠ f) (heg : e ≠ g) (heh : e ≠ h)
    (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h) :
    ⁅swap e g * swap g f, swap g h * swap h f⁆ = swap e f * swap g h := by
  ext i
  simp only [commutatorElement_def, mul_inv_rev, swap_inv, Perm.mul_apply, swap_apply_def]
  grind

private theorem swap_swap_sq {a b c d : α} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) : (swap a b * swap c d) * (swap a b * swap c d) = 1 := by
  ext i
  simp only [Perm.mul_apply, swap_apply_def, Perm.one_apply]
  grind

private theorem sign_swap_mul_swap [Fintype α] {a b c d : α} (hab : a ≠ b) (hcd : c ≠ d) :
    sign (swap a b * swap c d) = 1 := by
  rw [map_mul, sign_swap hab, sign_swap hcd]
  decide

end PermLemmas

section Peel

variable {α : Type*} [Fintype α] [DecidableEq α]

private def fixc (τ : Perm α) : ℕ := (Finset.univ.filter fun i => τ i = i).card

private theorem fixc_le (τ : Perm α) : fixc τ ≤ Fintype.card α :=
  (Finset.card_filter_le _ _).trans (by simp)

private theorem fixc_one : fixc (1 : Perm α) = Fintype.card α := by
  simp [fixc]

private theorem exists_two_moved {τ : Perm α} (hτ : τ * τ = 1) (hs : sign τ = 1) (h1 : τ ≠ 1) :
    ∃ a c : α, τ a ≠ a ∧ τ c ≠ c ∧ c ≠ a ∧ c ≠ τ a := by
  have hinv : ∀ i, τ (τ i) = i := fun i => by
    simpa [Perm.mul_apply] using congrArg (fun f : Perm α => f i) hτ
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
    by_contra hcon
    push Not at hcon
    exact h1 (Equiv.ext hcon)
  by_contra hno
  push Not at hno
  have hτ_eq : τ = swap a (τ a) := by
    ext i
    by_cases hia : i = a
    · subst hia; simp
    · by_cases hi : τ i = i
      · have hne : i ≠ τ a := by
          intro h
          apply hia
          have h1 := hinv a
          rw [← h, hi] at h1
          exact h1
        rw [swap_apply_of_ne_of_ne hia hne, hi]
      · have h := hno a i ha hi hia
        rw [h, swap_apply_right, hinv a]
  have h2 := sign_swap (Ne.symm ha)
  rw [← hτ_eq, hs] at h2
  exact absurd h2 (by decide)

private theorem peel {τ : Perm α} (hτ : τ * τ = 1) (hs : sign τ = 1) (h1 : τ ≠ 1) :
    ∃ (a b c d : α) (τ' : Perm α), a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      τ a = b ∧ τ c = d ∧ τ = swap a b * swap c d * τ' ∧ τ' * τ' = 1 ∧ sign τ' = 1 ∧
      τ' a = a ∧ τ' b = b ∧ τ' c = c ∧ τ' d = d ∧ fixc τ' = fixc τ + 4 := by
  have hinv : ∀ i, τ (τ i) = i := fun i => by
    simpa [Perm.mul_apply] using congrArg (fun f : Perm α => f i) hτ
  obtain ⟨a, c, ha, hc, hca, hcb⟩ := exists_two_moved hτ hs h1
  obtain ⟨b, hb⟩ : ∃ b, τ a = b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, τ c = d := ⟨_, rfl⟩
  rw [hb] at ha hcb
  rw [hd] at hc
  have hba : τ b = a := by rw [← hb]; exact hinv a
  have hdc : τ d = c := by rw [← hd]; exact hinv c
  have hab : a ≠ b := fun h => ha h.symm
  have hcd : c ≠ d := fun h => hc h.symm
  have hac : a ≠ c := fun h => hca h.symm
  have hbc : b ≠ c := fun h => hcb h.symm
  have had : a ≠ d := by
    intro h
    apply hbc
    rw [← hb, h, hdc]
  have hbd : b ≠ d := by
    intro h
    apply hac
    apply τ.injective
    rw [hb, hd, h]
  have hDD : (swap a b * swap c d) * (swap a b * swap c d) = 1 := swap_swap_sq hac had hbc hbd
  have hcomm : τ * (swap a b * swap c d) = (swap a b * swap c d) * τ := by
    calc τ * (swap a b * swap c d) = (τ * swap a b) * swap c d := by rw [mul_assoc]
      _ = (swap (τ a) (τ b) * τ) * swap c d := by rw [mul_swap_eq_swap_mul τ a b]
      _ = swap (τ a) (τ b) * (τ * swap c d) := by rw [mul_assoc]
      _ = swap (τ a) (τ b) * (swap (τ c) (τ d) * τ) := by rw [mul_swap_eq_swap_mul τ c d]
      _ = swap b a * (swap d c * τ) := by rw [hb, hba, hd, hdc]
      _ = swap a b * swap c d * τ := by rw [swap_comm b a, swap_comm d c, mul_assoc]
  have hτ'a : (swap a b * swap c d * τ) a = a := by
    show swap a b (swap c d (τ a)) = a
    rw [hb, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
  have hτ'b : (swap a b * swap c d * τ) b = b := by
    show swap a b (swap c d (τ b)) = b
    rw [hba, swap_apply_of_ne_of_ne hac had, swap_apply_left]
  have hτ'c : (swap a b * swap c d * τ) c = c := by
    show swap a b (swap c d (τ c)) = c
    rw [hd, swap_apply_right, swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
  have hτ'd : (swap a b * swap c d * τ) d = d := by
    show swap a b (swap c d (τ d)) = d
    rw [hdc, swap_apply_left, swap_apply_of_ne_of_ne (Ne.symm had) (Ne.symm hbd)]
  have hmoved : ∀ i, τ i = i → i ≠ a ∧ i ≠ b ∧ i ≠ c ∧ i ≠ d := by
    intro i hi
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro h; rw [h] at hi; exact ha (hb.symm.trans hi)
    · intro h; rw [h] at hi; exact hab (hba.symm.trans hi)
    · intro h; rw [h] at hi; exact hc (hd.symm.trans hi)
    · intro h; rw [h] at hi; exact hcd (hdc.symm.trans hi)
  have hτ'2 : (swap a b * swap c d * τ) * (swap a b * swap c d * τ) = 1 := by
    calc (swap a b * swap c d * τ) * (swap a b * swap c d * τ)
        = (swap a b * swap c d) * (τ * (swap a b * swap c d)) * τ := by simp only [mul_assoc]
      _ = (swap a b * swap c d) * ((swap a b * swap c d) * τ) * τ := by rw [hcomm]
      _ = ((swap a b * swap c d) * (swap a b * swap c d)) * (τ * τ) := by simp only [mul_assoc]
      _ = 1 := by rw [hDD, hτ, one_mul]
  have hsign : sign (swap a b * swap c d * τ) = 1 := by
    rw [map_mul, sign_swap_mul_swap hab hcd, hs, one_mul]
  have hfixset : Finset.univ.filter (fun i => (swap a b * swap c d * τ) i = i) =
      (Finset.univ.filter fun i => τ i = i) ∪ {a, b, c, d} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro h
      by_cases hi : i = a ∨ i = b ∨ i = c ∨ i = d
      · exact Or.inr hi
      · left
        push Not at hi
        obtain ⟨hia, hib, hic, hid⟩ := hi
        have hDi : (swap a b * swap c d) i = i := by
          rw [Perm.mul_apply, swap_apply_of_ne_of_ne hic hid, swap_apply_of_ne_of_ne hia hib]
        have h2 : (swap a b * swap c d) (τ i) = (swap a b * swap c d) i := by
          rw [hDi]; exact h
        exact (swap a b * swap c d).injective h2
    · rintro (h | h | h | h | h)
      · obtain ⟨hia, hib, hic, hid⟩ := hmoved i h
        show (swap a b * swap c d) (τ i) = i
        rw [h, Perm.mul_apply, swap_apply_of_ne_of_ne hic hid, swap_apply_of_ne_of_ne hia hib]
      · rw [h]; exact hτ'a
      · rw [h]; exact hτ'b
      · rw [h]; exact hτ'c
      · rw [h]; exact hτ'd
  have hdisj : Disjoint (Finset.univ.filter fun i => τ i = i) ({a, b, c, d} : Finset α) := by
    rw [Finset.disjoint_left]
    intro i hi hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨hia, hib, hic, hid⟩ := hmoved i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h | h | h | h
    exacts [hia h, hib h, hic h, hid h]
  have hcard : ({a, b, c, d} : Finset α).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]), Finset.card_pair hcd]
  refine ⟨a, b, c, d, swap a b * swap c d * τ, hab, hac, had, hbc, hbd, hcd, hb, hd, ?_, hτ'2,
    hsign, hτ'a, hτ'b, hτ'c, hτ'd, ?_⟩
  · rw [← mul_assoc, hDD, one_mul]
  · unfold fixc
    rw [hfixset, Finset.card_union_of_disjoint hdisj, hcard]

private theorem two_cases {n : ℕ} (hn8 : 8 ≤ n) (hn11 : n ≤ 11) {τ : Perm (Fin n)}
    (hτ : τ * τ = 1) (hs : sign τ = 1) (h1 : τ ≠ 1) (hfix : fixc τ ≤ 3) :
    ∃ a b c d e f g h : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h ∧
      (swap a b * swap c d) e = e ∧ (swap a b * swap c d) f = f ∧
      (swap a b * swap c d) g = g ∧ (swap a b * swap c d) h = h ∧
      τ = swap a b * swap c d * (swap e f * swap g h) := by
  obtain ⟨a, b, c, d, τ', hab, hac, had, hbc, hbd, hcd, hτa, hτc, hτeq, hτ'2, hs', hτ'a, hτ'b,
    hτ'c, hτ'd, hfix'⟩ := peel hτ hs h1
  have h1' : τ' ≠ 1 := by
    intro h
    rw [h, fixc_one, Fintype.card_fin] at hfix'
    omega
  obtain ⟨e, f, g, h, τ2, hef, heg, heh, hfg, hfh, hgh, hτ'e, hτ'g, hτ'eq, hτ2sq, hs2, hτ2e,
    hτ2f, hτ2g, hτ2h, hfix2⟩ := peel hτ'2 hs' h1'
  have h1'' : τ2 = 1 := by
    by_contra hne
    obtain ⟨_, _, _, _, τ3, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hfix3⟩ :=
      peel hτ2sq hs2 hne
    have := fixc_le τ3
    rw [Fintype.card_fin] at this
    omega
  have hinv' : ∀ i, τ' (τ' i) = i := fun i => by
    simpa [Perm.mul_apply] using congrArg (fun f : Perm (Fin n) => f i) hτ'2
  have hD : ∀ i, τ' i ≠ i → (swap a b * swap c d) i = i := by
    intro i hi
    have hia : i ≠ a := fun h => hi (h ▸ hτ'a)
    have hib : i ≠ b := fun h => hi (h ▸ hτ'b)
    have hic : i ≠ c := fun h => hi (h ▸ hτ'c)
    have hid : i ≠ d := fun h => hi (h ▸ hτ'd)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hic hid, swap_apply_of_ne_of_ne hia hib]
  refine ⟨a, b, c, d, e, f, g, h, hab, hac, had, hbc, hbd, hcd, hef, heg, heh, hfg, hfh, hgh,
    hD e (by rw [hτ'e]; exact hef.symm), hD f ?_, hD g (by rw [hτ'g]; exact hgh.symm), hD h ?_, ?_⟩
  · have hfe : τ' f = e := by rw [← hτ'e, hinv']
    rw [hfe]; exact hef
  · have hhg : τ' h = g := by rw [← hτ'g, hinv']
    rw [hhg]; exact hgh
  · rw [hτeq, hτ'eq, h1'', mul_one]

private theorem exists_four_fixed {n : ℕ} {τ : Perm (Fin n)} (hf4 : 4 ≤ fixc τ) :
    ∃ e f g h : Fin n, e ≠ f ∧ e ≠ g ∧ e ≠ h ∧ f ≠ g ∧ f ≠ h ∧ g ≠ h ∧
      τ e = e ∧ τ f = f ∧ τ g = g ∧ τ h = h := by
  have hcard : Fintype.card (Fin 4) ≤ Fintype.card {i : Fin n // τ i = i} := by
    rw [Fintype.card_fin, Fintype.card_subtype]
    exact hf4
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  have hne : ∀ i j : Fin 4, i ≠ j → (emb i).1 ≠ (emb j).1 := fun i j hij hh =>
    hij (emb.injective (Subtype.ext hh))
  exact ⟨(emb 0).1, (emb 1).1, (emb 2).1, (emb 3).1, hne 0 1 (by decide), hne 0 2 (by decide),
    hne 0 3 (by decide), hne 1 2 (by decide), hne 1 3 (by decide), hne 2 3 (by decide),
    (emb 0).2, (emb 1).2, (emb 2).2, (emb 3).2⟩

end Peel

structure AltDblCover (G : Type) [Group G] (n : ℕ) where
  φ : G →* Perm (Fin n)
  z : G
  sign_eq_one : ∀ g, sign (φ g) = 1
  surj : ∀ σ : Perm (Fin n), sign σ = 1 → ∃ g, φ g = σ
  ker_iff : ∀ g, φ g = 1 ↔ g = 1 ∨ g = z
  z_ne_one : z ≠ 1
  z_mem_center : z ∈ center G
  center_le : ∀ g ∈ center G, g = 1 ∨ g = z
  comm : ∀ {p q s t : Fin n}, p ≠ q → p ≠ s → p ≠ t → q ≠ s → q ≠ t → s ≠ t →
    ∀ e₁ e₂ : G, φ e₁ = swap p q * swap s t → φ e₂ = swap p s * swap q t →
      e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = z

section CentralLemmas

variable {G : Type} [Group G]

private theorem conj_central {a g : G} (ha : a ∈ center G) : a * g * a⁻¹ = g := by
  rw [← Subgroup.mem_center_iff.mp ha g]; group

private theorem commutator_mul_central_left {a u w : G} (ha : a ∈ center G) :
    ⁅a * u, w⁆ = ⁅u, w⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc a * u * w * (a * u)⁻¹ * w⁻¹ = (a * (u * w * u⁻¹) * a⁻¹) * w⁻¹ := by group
    _ = u * w * u⁻¹ * w⁻¹ := by rw [conj_central ha]

private theorem commutator_mul_central_right {b u v : G} (hb : b ∈ center G) :
    ⁅u, b * v⁆ = ⁅u, v⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc u * (b * v) * u⁻¹ * (b * v)⁻¹ = (u * b) * v * u⁻¹ * v⁻¹ * b⁻¹ := by group
    _ = (b * u) * v * u⁻¹ * v⁻¹ * b⁻¹ := by rw [Subgroup.mem_center_iff.mp hb u]
    _ = b * (u * v * u⁻¹ * v⁻¹) * b⁻¹ := by group
    _ = u * v * u⁻¹ * v⁻¹ := conj_central hb

end CentralLemmas

namespace AltDblCover

variable {G : Type} [Group G] {n : ℕ} (C : AltDblCover G n)

private theorem φ_z : C.φ C.z = 1 := (C.ker_iff C.z).mpr (Or.inr rfl)

private theorem z_mul_z : C.z * C.z = 1 := by
  rcases (C.ker_iff (C.z * C.z)).mp (by rw [map_mul, C.φ_z, one_mul]) with h | h
  · exact h
  · exact absurd (by simpa using h) C.z_ne_one

private theorem ker_central {g : G} (hg : C.φ g = 1) : g ∈ center G := by
  rcases (C.ker_iff g).mp hg with rfl | rfl
  · exact one_mem _
  · exact C.z_mem_center

private theorem sq_mem {g : G} (hg : C.φ g * C.φ g = 1) : g * g = 1 ∨ g * g = C.z :=
  (C.ker_iff (g * g)).mp (by rw [map_mul]; exact hg)

private theorem sq_conj {e e' : G} (he : C.φ e * C.φ e = 1) {c : Perm (Fin n)}
    (hc : sign c = 1) (h : C.φ e' = c * C.φ e * c⁻¹) : e' * e' = e * e := by
  obtain ⟨g, hg⟩ := C.surj c hc
  have hee : e * e ∈ center G := by
    rcases C.sq_mem he with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact C.z_mem_center
  have hk : C.φ ((g * e * g⁻¹)⁻¹ * e') = 1 := by
    simp only [map_mul, map_inv, hg, h]
    group
  obtain ⟨m, hm⟩ : ∃ m, m = g * e * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = m⁻¹ * e' := ⟨_, rfl⟩
  rw [← hm] at hk
  rw [← hkdef] at hk
  have hkc : k ∈ center G := C.ker_central hk
  have hkk : k * k = 1 := by
    rcases (C.ker_iff k).mp hk with h1 | h1
    · rw [h1, mul_one]
    · rw [h1]; exact C.z_mul_z
  have he' : e' = m * k := by rw [hkdef]; group
  have hmm : m * m = e * e := by
    calc m * m = g * (e * e) * g⁻¹ := by rw [hm]; group
      _ = (e * e) * g * g⁻¹ := by rw [Subgroup.mem_center_iff.mp hee g]
      _ = e * e := by group
  calc e' * e' = (m * k) * (m * k) := by rw [← he']
    _ = m * (k * m) * k := by group
    _ = m * (m * k) * k := by rw [← Subgroup.mem_center_iff.mp hkc m]
    _ = (m * m) * (k * k) := by group
    _ = e * e := by rw [hkk, mul_one, hmm]

private theorem sq_eq_z {p q s t : Fin n} (hpq : p ≠ q) (hps : p ≠ s) (hpt : p ≠ t)
    (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) {e : G} (he : C.φ e = swap p q * swap s t) :
    e * e = C.z := by
  have hc : sign (swap q s * swap s t) = 1 := sign_swap_mul_swap hqs hst
  obtain ⟨g, hg⟩ := C.surj _ hc
  have hτ1 : (swap p q * swap s t) * (swap p q * swap s t) = 1 := swap_swap_sq hps hpt hqs hqt
  have hτ2 : (swap p s * swap q t) * (swap p s * swap q t) = 1 :=
    swap_swap_sq hpq hpt (Ne.symm hqs) hst
  have he2 : C.φ e * C.φ e = 1 := by rw [he]; exact hτ1
  have hee : e * e ∈ center G := by
    rcases C.sq_mem he2 with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact C.z_mem_center
  have hsq1 : (e * e) * (e * e) = 1 := by
    rcases C.sq_mem he2 with h1 | h1
    · rw [h1, mul_one]
    · rw [h1]; exact C.z_mul_z
  have hφ2 : C.φ (g * e * g⁻¹) = swap p s * swap q t := by
    rw [map_mul, map_mul, map_inv, hg, he]
    exact perm_conj_one hpq hps hpt hqs hqt hst
  have hcomm := C.comm hpq hps hpt hqs hqt hst e (g * e * g⁻¹) he hφ2
  have hφ3 : C.φ (e * (g * e * g⁻¹)) =
      (swap q s * swap s t) * C.φ (g * e * g⁻¹) * (swap q s * swap s t)⁻¹ := by
    rw [map_mul, he, hφ2]
    exact perm_conj_two hpq hps hpt hqs hqt hst
  have h3 : (e * (g * e * g⁻¹)) * (e * (g * e * g⁻¹)) = (g * e * g⁻¹) * (g * e * g⁻¹) :=
    C.sq_conj (by rw [hφ2]; exact hτ2) hc hφ3
  have h2 : (g * e * g⁻¹) * (g * e * g⁻¹) = e * e :=
    C.sq_conj he2 hc (by rw [hφ2, he]; exact (perm_conj_one hpq hps hpt hqs hqt hst).symm)
  obtain ⟨e₂, he₂⟩ : ∃ e₂, e₂ = g * e * g⁻¹ := ⟨_, rfl⟩
  rw [← he₂] at hcomm h3 h2
  have hz2 : e * e₂ = C.z * e₂ * e := by
    calc e * e₂ = (e * e₂ * e⁻¹ * e₂⁻¹) * e₂ * e := by group
      _ = C.z * e₂ * e := by rw [hcomm]
  have h4 : (e * e₂) * (e * e₂) = C.z := by
    calc (e * e₂) * (e * e₂) = (C.z * e₂ * e) * (e * e₂) := by rw [← hz2]
      _ = C.z * (e₂ * (e * e) * e₂) := by group
      _ = C.z * ((e * e) * e₂ * e₂) := by rw [Subgroup.mem_center_iff.mp hee e₂]
      _ = C.z * ((e * e) * (e₂ * e₂)) := by group
      _ = C.z * ((e * e) * (e * e)) := by rw [h2]
      _ = C.z := by rw [hsq1, mul_one]
  rw [h3, h2] at h4
  exact h4

private theorem commute_commutator {x u v : G} (hu : C.φ u * C.φ x = C.φ x * C.φ u)
    (hv : C.φ v * C.φ x = C.φ x * C.φ v) : x * (⁅u, v⁆ : G) = (⁅u, v⁆ : G) * x := by
  obtain ⟨a, ha⟩ : ∃ a, a = x * u * x⁻¹ * u⁻¹ := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = x * v * x⁻¹ * v⁻¹ := ⟨_, rfl⟩
  have hau : C.φ a = 1 := by
    rw [ha]
    simp only [map_mul, map_inv]
    rw [← hu]
    group
  have hbv : C.φ b = 1 := by
    rw [hb]
    simp only [map_mul, map_inv]
    rw [← hv]
    group
  have hac : a ∈ center G := C.ker_central hau
  have hbc : b ∈ center G := C.ker_central hbv
  have hxu : x * u * x⁻¹ = a * u := by rw [ha]; group
  have hxv : x * v * x⁻¹ = b * v := by rw [hb]; group
  have key : x * ⁅u, v⁆ * x⁻¹ = ⁅u, v⁆ := by
    calc x * ⁅u, v⁆ * x⁻¹ = ⁅x * u * x⁻¹, x * v * x⁻¹⁆ := by
          simp only [commutatorElement_def]; group
      _ = ⁅a * u, b * v⁆ := by rw [hxu, hxv]
      _ = ⁅u, v⁆ := by rw [commutator_mul_central_left hac, commutator_mul_central_right hbc]
  calc x * ⁅u, v⁆ = (x * ⁅u, v⁆ * x⁻¹) * x := by group
    _ = ⁅u, v⁆ * x := by rw [key]

private theorem comm_of_lift {x : G} {e f g h : Fin n} (hef : e ≠ f) (heg : e ≠ g)
    (heh : e ≠ h) (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h) (hxe : C.φ x e = e)
    (hxf : C.φ x f = f) (hxg : C.φ x g = g) (hxh : C.φ x h = h) {s : G}
    (hs : C.φ s = swap e f * swap g h) : x * s = s * x := by
  obtain ⟨u, hu⟩ := C.surj (swap e g * swap g f) (sign_swap_mul_swap heg hfg.symm)
  obtain ⟨v, hv⟩ := C.surj (swap g h * swap h f) (sign_swap_mul_swap hgh hfh.symm)
  have hcu : (swap e g * swap g f) * C.φ x = C.φ x * (swap e g * swap g f) := by
    have hdis : Disjoint (swap e g * swap g f) (C.φ x) := by
      intro i
      by_cases hi : i = e ∨ i = g ∨ i = f
      · right
        rcases hi with rfl | rfl | rfl
        exacts [hxe, hxg, hxf]
      · left
        push Not at hi
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi.2.1 hi.2.2,
          swap_apply_of_ne_of_ne hi.1 hi.2.1]
    exact hdis.commute.eq
  have hcv : (swap g h * swap h f) * C.φ x = C.φ x * (swap g h * swap h f) := by
    have hdis : Disjoint (swap g h * swap h f) (C.φ x) := by
      intro i
      by_cases hi : i = g ∨ i = h ∨ i = f
      · right
        rcases hi with rfl | rfl | rfl
        exacts [hxg, hxh, hxf]
      · left
        push Not at hi
        rw [Perm.mul_apply, swap_apply_of_ne_of_ne hi.2.1 hi.2.2,
          swap_apply_of_ne_of_ne hi.1 hi.2.1]
    exact hdis.commute.eq
  have hs0 : C.φ ⁅u, v⁆ = swap e f * swap g h := by
    rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, hu, hv]
    exact perm_commutator hef heg heh hfg hfh hgh
  have hcomm0 : x * (⁅u, v⁆ : G) = (⁅u, v⁆ : G) * x :=
    C.commute_commutator (by rw [hu]; exact hcu) (by rw [hv]; exact hcv)
  obtain ⟨k, hkdef⟩ : ∃ k, k = ⁅u, v⁆⁻¹ * s := ⟨_, rfl⟩
  have hk : C.φ k = 1 := by rw [hkdef, map_mul, map_inv, hs0, hs, inv_mul_cancel]
  have hkc : k ∈ center G := C.ker_central hk
  have hs_eq : s = ⁅u, v⁆ * k := by rw [hkdef]; group
  rw [hs_eq]
  calc x * (⁅u, v⁆ * k) = (x * ⁅u, v⁆) * k := by group
    _ = ⁅u, v⁆ * x * k := by rw [hcomm0]
    _ = ⁅u, v⁆ * (x * k) := by group
    _ = ⁅u, v⁆ * (k * x) := by rw [Subgroup.mem_center_iff.mp hkc x]
    _ = (⁅u, v⁆ * k) * x := by group

private theorem exists_kleinFour_of_fixed {x : G} (hx : x * x = C.z) {e f g h : Fin n}
    (hef : e ≠ f) (heg : e ≠ g) (heh : e ≠ h) (hfg : f ≠ g) (hfh : f ≠ h) (hgh : g ≠ h)
    (hxe : C.φ x e = e) (hxf : C.φ x f = f) (hxg : C.φ x g = g) (hxh : C.φ x h = h) :
    ∃ A : Subgroup G, IsKleinFour A ∧ A ≤ centralizer ({x} : Set G) := by
  obtain ⟨s, hs⟩ := C.surj (swap e f * swap g h) (sign_swap_mul_swap hef hgh)
  have hsx : x * s = s * x := C.comm_of_lift hef heg heh hfg hfh hgh hxe hxf hxg hxh hs
  have hss : s * s = C.z := C.sq_eq_z hef heg heh hfg hfh hgh hs
  have hy2 : (x * s) * (x * s) = 1 := by
    calc x * s * (x * s) = x * (s * x) * s := by group
      _ = x * (x * s) * s := by rw [← hsx]
      _ = (x * x) * (s * s) := by group
      _ = 1 := by rw [hx, hss]; exact C.z_mul_z
  have hφy : C.φ (x * s) = C.φ x * (swap e f * swap g h) := by rw [map_mul, hs]
  have hφy_ne : C.φ (x * s) ≠ 1 := by
    intro h2
    rw [hφy] at h2
    have h3 := congrArg (fun p : Perm (Fin n) => p e) h2
    simp only [Perm.mul_apply, Perm.one_apply] at h3
    rw [swap_apply_of_ne_of_ne heg heh, swap_apply_left, hxf] at h3
    exact hef.symm h3
  have hy_ne : x * s ≠ 1 := fun h1 => hφy_ne (by rw [h1, map_one])
  have hzy : C.z ≠ x * s := fun h1 => hφy_ne (by rw [← h1]; exact C.φ_z)
  have hzc : C.z * (x * s) = (x * s) * C.z :=
    (Subgroup.mem_center_iff.mp C.z_mem_center (x * s)).symm
  obtain ⟨hK, -⟩ := GSYard02.CoverAltGroup.isKleinFour_closure_pair C.z_mul_z hy2 hzc
    C.z_ne_one hy_ne hzy
  refine ⟨Subgroup.closure {C.z, x * s}, hK, ?_⟩
  rw [Subgroup.closure_le]
  intro w hw
  rcases hw with rfl | rfl
  · exact mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp C.z_mem_center x).symm
  · exact mem_centralizer_singleton_iff.mpr (by
      calc x * s * x = x * (s * x) := by group
        _ = x * (x * s) := by rw [← hsx])

include C in
private theorem exists_kleinFour (hn8 : 8 ≤ n) : ∃ A : Subgroup G, IsKleinFour A := by
  obtain ⟨i, hi⟩ : ∃ i : Fin 8 → Fin n, Function.Injective i :=
    ⟨Fin.castLE hn8, Fin.castLE_injective hn8⟩
  have hne : ∀ a b : Fin 8, a ≠ b → i a ≠ i b := fun a b h => hi.ne h
  obtain ⟨x, hx⟩ := C.surj (swap (i 0) (i 1) * swap (i 2) (i 3))
    (sign_swap_mul_swap (hne 0 1 (by decide)) (hne 2 3 (by decide)))
  have hxx : x * x = C.z := C.sq_eq_z (hne 0 1 (by decide)) (hne 0 2 (by decide))
    (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide)) (hne 2 3 (by decide)) hx
  have hfix : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → C.φ x (i j) = i j := by
    intro j h0 h1 h2 h3
    rw [hx, Perm.mul_apply, swap_apply_of_ne_of_ne (hne _ _ h2) (hne _ _ h3),
      swap_apply_of_ne_of_ne (hne _ _ h0) (hne _ _ h1)]
  obtain ⟨A, hA, -⟩ := C.exists_kleinFour_of_fixed hxx (hne 4 5 (by decide))
    (hne 4 6 (by decide)) (hne 4 7 (by decide)) (hne 5 6 (by decide)) (hne 5 7 (by decide))
    (hne 6 7 (by decide)) (hfix 4 (by decide) (by decide) (by decide) (by decide))
    (hfix 5 (by decide) (by decide) (by decide) (by decide))
    (hfix 6 (by decide) (by decide) (by decide) (by decide))
    (hfix 7 (by decide) (by decide) (by decide) (by decide))
  exact ⟨A, hA⟩

include C in
theorem centralSquareFour (hn8 : 8 ≤ n) (hn11 : n ≤ 11) : CentralSquareFour G := by
  intro x hx
  by_cases hxc : x ∈ center G
  · obtain ⟨A, hA⟩ := C.exists_kleinFour hn8
    refine ⟨A, hA, fun a _ => ?_⟩
    exact mem_centralizer_singleton_iff.mpr (Subgroup.mem_center_iff.mp hxc a)
  rcases C.center_le _ hx with h1 | h1
  · have hx1 : x ≠ 1 := fun h => hxc (h ▸ one_mem _)
    have hxz : C.z ≠ x := fun h => hxc (h ▸ C.z_mem_center)
    have hzc : C.z * x = x * C.z := (Subgroup.mem_center_iff.mp C.z_mem_center x).symm
    obtain ⟨hK, -⟩ := GSYard02.CoverAltGroup.isKleinFour_closure_pair C.z_mul_z h1 hzc
      C.z_ne_one hx1 hxz
    refine ⟨Subgroup.closure {C.z, x}, hK, ?_⟩
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with rfl | rfl
    · exact mem_centralizer_singleton_iff.mpr hzc
    · exact mem_centralizer_singleton_iff.mpr rfl
  · have hφx2 : C.φ x * C.φ x = 1 := by rw [← map_mul, h1]; exact C.φ_z
    have hφx1 : C.φ x ≠ 1 := fun h => hxc (C.ker_central h)
    by_cases hfix : 4 ≤ fixc (C.φ x)
    · obtain ⟨e, f, g, h, hef, heg, heh, hfg, hfh, hgh, hxe, hxf, hxg, hxh⟩ :=
        exists_four_fixed hfix
      exact C.exists_kleinFour_of_fixed h1 hef heg heh hfg hfh hgh hxe hxf hxg hxh
    · exfalso
      push Not at hfix
      obtain ⟨a, b, c, d, e, f, g, h, hab, hac, had, hbc, hbd, hcd, hef, heg, heh, hfg, hfh,
        hgh, hde, hdf, hdg, hdh, hφeq⟩ :=
        two_cases hn8 hn11 hφx2 (C.sign_eq_one x) hφx1 (by omega)
      obtain ⟨u, hu⟩ := C.surj (swap a b * swap c d) (sign_swap_mul_swap hab hcd)
      obtain ⟨v, hv⟩ := C.surj (swap e f * swap g h) (sign_swap_mul_swap hef hgh)
      have hu2 : u * u = C.z := C.sq_eq_z hab hac had hbc hbd hcd hu
      have hv2 : v * v = C.z := C.sq_eq_z hef heg heh hfg hfh hgh hv
      have huv : u * v = v * u :=
        C.comm_of_lift hef heg heh hfg hfh hgh (by rw [hu]; exact hde) (by rw [hu]; exact hdf)
          (by rw [hu]; exact hdg) (by rw [hu]; exact hdh) hv
      have hww : (u * v) * (u * v) = 1 := by
        calc u * v * (u * v) = u * (v * u) * v := by group
          _ = u * (u * v) * v := by rw [← huv]
          _ = (u * u) * (v * v) := by group
          _ = 1 := by rw [hu2, hv2]; exact C.z_mul_z
      obtain ⟨w, hw⟩ : ∃ w, w = u * v := ⟨_, rfl⟩
      rw [← hw] at hww
      have hk : C.φ (w⁻¹ * x) = 1 := by
        rw [map_mul, map_inv, hw, map_mul, hu, hv, hφeq, inv_mul_cancel]
      obtain ⟨k, hkdef⟩ : ∃ k, k = w⁻¹ * x := ⟨_, rfl⟩
      rw [← hkdef] at hk
      have hkc : k ∈ center G := C.ker_central hk
      have hkk : k * k = 1 := by
        rcases (C.ker_iff k).mp hk with h1' | h1'
        · rw [h1', mul_one]
        · rw [h1']; exact C.z_mul_z
      have hx_eq : x = w * k := by rw [hkdef]; group
      have hxx : x * x = 1 := by
        calc x * x = (w * k) * (w * k) := by rw [← hx_eq]
          _ = w * (k * w) * k := by group
          _ = w * (w * k) * k := by rw [← Subgroup.mem_center_iff.mp hkc w]
          _ = (w * w) * (k * k) := by group
          _ = 1 := by rw [hww, hkk, one_mul]
      rw [h1] at hxx
      exact C.z_ne_one hxx

end AltDblCover

section Instance

open CFSG.Alternating.Multipliers.Spin CFSG.ComponentClassification.Sol76.Sig.GSYard02

private theorem comm_E {m : ℕ} (hm : 6 ≤ m) {p q s t : Fin (m + 2)} (hpq : p ≠ q) (hps : p ≠ s)
    (hpt : p ≠ t) (hqs : q ≠ s) (hqt : q ≠ t) (hst : s ≠ t) (e₁ e₂ : E (m + 2))
    (h₁ : permH (n := m + 2) (e₁ : H (m + 2)) = swap p q * swap s t)
    (h₂ : permH (n := m + 2) (e₂ : H (m + 2)) = swap p s * swap q t) :
    e₁ * e₂ * e₁⁻¹ * e₂⁻¹ = negE (m := m) (by omega) := by
  obtain ⟨d₁, hd₁⟩ : ∃ d₁ : H (m + 2), (d₁ : monomial (m + 2)) = dd hpq hst :=
    ⟨⟨dd hpq hst, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩, rfl⟩
  obtain ⟨d₂, hd₂⟩ : ∃ d₂ : H (m + 2), (d₂ : monomial (m + 2)) = dd hps hqt :=
    ⟨⟨dd hps hqt, subset_closure ⟨_, _, _, _, _, _, rfl⟩⟩, rfl⟩
  have hp₁ : permH (n := m + 2) d₁ = swap p q * swap s t := by
    show perm (d₁ : monomial (m + 2)) = _
    rw [hd₁, perm_dd]
  have hp₂ : permH (n := m + 2) d₂ = swap p s * swap q t := by
    show perm (d₂ : monomial (m + 2)) = _
    rw [hd₂, perm_dd]
  have hk₁ : (e₁ : H (m + 2))⁻¹ * d₁ ∈ (permH (n := m + 2)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h₁, hp₁, inv_mul_cancel]
  have hk₂ : (e₂ : H (m + 2))⁻¹ * d₂ ∈ (permH (n := m + 2)).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h₂, hp₂, inv_mul_cancel]
  obtain ⟨k₁, hk₁def⟩ : ∃ k₁, k₁ = (e₁ : H (m + 2))⁻¹ * d₁ := ⟨_, rfl⟩
  obtain ⟨k₂, hk₂def⟩ : ∃ k₂, k₂ = (e₂ : H (m + 2))⁻¹ * d₂ := ⟨_, rfl⟩
  rw [← hk₁def] at hk₁
  rw [← hk₂def] at hk₂
  have hc₁ : k₁ ∈ center (H (m + 2)) := ker_permH_le_center hk₁
  have hc₂ : k₂ ∈ center (H (m + 2)) := ker_permH_le_center hk₂
  have hd₁' : d₁ = k₁ * (e₁ : H (m + 2)) := by
    rw [← Subgroup.mem_center_iff.mp hc₁ (e₁ : H (m + 2)), hk₁def]; group
  have hd₂' : d₂ = k₂ * (e₂ : H (m + 2)) := by
    rw [← Subgroup.mem_center_iff.mp hc₂ (e₂ : H (m + 2)), hk₂def]; group
  have key : ⁅d₁, d₂⁆ = ⁅(e₁ : H (m + 2)), (e₂ : H (m + 2))⁆ := by
    rw [hd₁', hd₂', commutator_mul_central_left hc₁, commutator_mul_central_right hc₂]
  have hval : ((⁅d₁, d₂⁆ : H (m + 2)) : monomial (m + 2)) = negOne := by
    have h := commutator_dd hpq hps hpt hqs hqt hst
    rw [← hd₁, ← hd₂] at h
    exact h
  rw [key] at hval
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_negE]
  exact hval

private noncomputable def dblCoverE {m : ℕ} (hm : 6 ≤ m) : AltDblCover (E (m + 2)) (m + 2) where
  φ := (permH (n := m + 2)).comp (E (m + 2)).subtype
  z := negE (m := m) (by omega)
  sign_eq_one g := by
    have hmem : permH (n := m + 2) (g : H (m + 2)) ∈ alternatingGroup (Fin (m + 2)) := by
      rw [← range_permH]; exact ⟨(g : H (m + 2)), rfl⟩
    exact Equiv.Perm.mem_alternatingGroup.mp hmem
  surj σ hσ := by
    obtain ⟨e, he⟩ := psi_surjective (m := m) (by omega)
      ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hσ⟩
    exact ⟨e, congrArg Subtype.val he⟩
  ker_iff g := by
    constructor
    · intro h
      exact ker_psi_eq hm g (Subtype.ext h)
    · rintro (rfl | rfl)
      · exact map_one _
      · exact congrArg Subtype.val (psi_negE (m := m) (by omega))
  z_ne_one := negE_ne_one _
  z_mem_center := by
    rw [center_E_eq hm]; exact MonoidHom.mem_ker.mpr (psi_negE _)
  center_le g hg := ker_psi_eq hm g (by
    rw [center_E_eq hm] at hg; exact MonoidHom.mem_ker.mp hg)
  comm := fun hpq hps hpt hqs hqt hst e₁ e₂ h₁ h₂ =>
    comm_E hm hpq hps hpt hqs hqt hst e₁ e₂ h₁ h₂

theorem f1LeafAlt_holds : CoverLeafAltFor F1Concl := by
  intro Q _ _ hQ n hn8 hn11 hQA
  obtain ⟨eQ⟩ := hQA
  obtain ⟨hquasi, hz, h2, -, -, -⟩ := hQ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have hm : 6 ≤ m := by omega
  have hzQ : Nat.card (center Q) = 2 := card_center_of_cover hquasi hz h2 (by omega) eQ
  have hGr : Nat.card (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) = 2 :=
    card_griess_alt (by omega)
  haveI : Finite (CFSG.Open.griessHopfMultiplier (alternatingGroup (Fin (m + 2)))) :=
    Nat.finite_of_card_ne_zero (by rw [hGr]; norm_num)
  haveI := finite_E hm
  obtain ⟨e⟩ := (RankThree.PerfectCover.hopf_central_cover_consequences
    (alternatingGroup (Fin (m + 2)))).2 (fun S => card_sylow_of_card_two hGr S) Q (E (m + 2))
    hquasi (isQuasisimple_E hm) hzQ (card_center_E hm) ⟨eQ⟩ (quotCenter_E hm)
  intro _ _
  exact CentralSquareFour.of_mulEquiv e.symm
    ((dblCoverE hm).centralSquareFour (by omega) (by omega))

end Instance

end CFSG.ComponentClassification.Sol76.Sig.GSYard03
