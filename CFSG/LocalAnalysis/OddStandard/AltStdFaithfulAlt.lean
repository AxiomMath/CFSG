module

public import CFSG.LocalAnalysis.OddStandard.AltNoHePerm
public import CFSG.LocalAnalysis.OddStandard.AltStdFaithfulRank
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.Open.StandardComponentRecognitionMilestoneDefs

public section

namespace CFSG.OddStandard.AltStdFaithful

open Subgroup Equiv Equiv.Perm

section Base

variable {G : Type*} [Group G] {α : Type*} (ε : G →* Perm α) (t : G)

@[expose] def baseGroup (ht : ∀ x, ε t (ε t x) = x) : Subgroup G where
  carrier := {g | ∀ x, ε g x = x ∨ ε g x = ε t x}
  one_mem' := fun x => Or.inl (by simp)
  mul_mem' := by
    intro a b ha hb x
    rcases hb x with h | h
    · simpa [h] using ha x
    · rcases ha (ε t x) with h' | h'
      · right
        simp [h, h']
      · left
        simp [h, h', ht]
  inv_mem' := by
    intro a ha x
    obtain ⟨y, hy⟩ : ∃ y, ε a⁻¹ x = y := ⟨_, rfl⟩
    have h1 : ε a y = x := by
      rw [← hy, ← Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    rw [hy]
    rcases ha y with h | h
    · left
      rw [h] at h1
      exact h1
    · right
      rw [h] at h1
      rw [← h1, ht]

variable {ε t} {ht : ∀ x, ε t (ε t x) = x}

theorem mem_baseGroup {g : G} : g ∈ baseGroup ε t ht ↔ ∀ x, ε g x = x ∨ ε g x = ε t x :=
  Iff.rfl

theorem t_mem_baseGroup : t ∈ baseGroup ε t ht := fun _ => Or.inr rfl

theorem perm_apply_comm {σ τ : Perm α} (hτ : ∀ x, τ (τ x) = x)
    (h : ∀ x, σ x = x ∨ σ x = τ x) (x : α) : σ (τ x) = τ (σ x) := by
  rcases h x with h1 | h1
  · rw [h1]
    rcases h (τ x) with h2 | h2
    · exact h2
    · have : τ x = x := σ.injective (by rw [h2, hτ, h1])
      rw [this]
      exact h1
  · rw [h1, hτ]
    rcases h (τ x) with h2 | h2
    · have : τ x = x := σ.injective (by rw [h2, h1])
      rw [h2, this]
    · rw [h2, hτ]

theorem baseGroup_apply_comm {a : G} (ha : a ∈ baseGroup ε t ht) (x : α) :
    ε a (ε t x) = ε t (ε a x) :=
  perm_apply_comm ht ha x

theorem baseGroup_apply_apply {a : G} (ha : a ∈ baseGroup ε t ht) (x : α) :
    ε a (ε a x) = x := by
  rcases ha x with h | h
  · rw [h, h]
  · rw [h, baseGroup_apply_comm ha, h, ht]

theorem baseGroup_le_centralizer (hε : Function.Injective ε) {a : G}
    (ha : a ∈ baseGroup ε t ht) : a ∈ centralizer ({t} : Set G) := by
  rw [mem_centralizer_singleton_iff]
  apply hε
  ext x
  simp [baseGroup_apply_comm ha]

theorem baseGroup_mul_comm (hε : Function.Injective ε) {a b : G} (ha : a ∈ baseGroup ε t ht)
    (hb : b ∈ baseGroup ε t ht) : a * b = b * a := by
  apply hε
  rw [map_mul, map_mul]
  have hg : ε t * ε t = 1 := by
    ext x
    simp [ht]
  refine AltNoHe.mul_comm_of_apply_eq_or_apply_eq hg ?_ ?_ ha hb
  · ext x
    simp [baseGroup_apply_comm ha]
  · ext x
    simp [baseGroup_apply_comm hb]

theorem baseGroup_conj {c : G} (hc : c ∈ centralizer ({t} : Set G)) {a : G}
    (ha : a ∈ baseGroup ε t ht) : c * a * c⁻¹ ∈ baseGroup ε t ht := by
  intro x
  have hct : ∀ y, ε c (ε t y) = ε t (ε c y) := fun y => by
    have := congrArg (fun g => ε g y) (mem_centralizer_singleton_iff.1 hc)
    simpa using this
  have hcy : ε c (ε c⁻¹ x) = x := by
    rw [← Perm.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl
  have hex : ε (c * a * c⁻¹) x = ε c (ε a (ε c⁻¹ x)) := by
    simp [map_mul]
  rw [hex]
  rcases ha (ε c⁻¹ x) with h | h
  · left
    rw [h, hcy]
  · right
    rw [h, hct, hcy]

theorem commute_of_mem_baseGroup (hε : Function.Injective ε) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLn : (L.subgroupOf (centralizer ({t} : Set G))).Normal) [hs : IsSimpleGroup L]
    (hnab : ∃ a b : L, a * b ≠ b * a) {g : G} (hg : g ∈ baseGroup ε t ht) {l : G} (hl : l ∈ L) :
    g * l = l * g := by
  let N : Subgroup L := (baseGroup ε t ht).subgroupOf L
  have hN : N.Normal := by
    refine ⟨fun n hn l' => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := baseGroup_conj (ht := ht) (hLt l'.2) hn
    simpa using this
  have hbot : N = ⊥ := by
    have := hN
    rcases hs.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : (a : G) ∈ baseGroup ε t ht := by
        have : a ∈ N := h ▸ Subgroup.mem_top a
        exact this
      have hb : (b : G) ∈ baseGroup ε t ht := by
        have : b ∈ N := h ▸ Subgroup.mem_top b
        exact this
      exact hab (Subtype.ext (baseGroup_mul_comm hε ha hb))
  have hgC : g ∈ centralizer ({t} : Set G) := baseGroup_le_centralizer hε hg
  have hlC : l ∈ centralizer ({t} : Set G) := hLt hl
  have hcL : g * l * g⁻¹ * l⁻¹ ∈ L := by
    have h1 : (⟨l, hlC⟩ : centralizer ({t} : Set G)) ∈ L.subgroupOf (centralizer ({t} : Set G)) :=
      hl
    have h2 := hLn.conj_mem _ h1 ⟨g, hgC⟩
    rw [Subgroup.mem_subgroupOf] at h2
    exact mul_mem (by simpa using h2) (inv_mem hl)
  have hcW : g * l * g⁻¹ * l⁻¹ ∈ baseGroup ε t ht := by
    have h3 := baseGroup_conj (ht := ht) hlC (inv_mem hg)
    have h4 := mul_mem hg h3
    simpa [mul_assoc] using h4
  have h5 : (⟨g * l * g⁻¹ * l⁻¹, hcL⟩ : L) ∈ N := hcW
  rw [hbot, Subgroup.mem_bot] at h5
  have h6 : g * l * g⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h5
  exact mul_inv_eq_iff_eq_mul.1 (mul_inv_eq_one.1 h6)

end Base

section Moved

variable {G : Type*} [Group G] {α : Type*} [Fintype α] [DecidableEq α] (ε : G →* Perm α) (t : G)

theorem fixes_moved_points {L : Subgroup G} (hLt : L ≤ centralizer ({t} : Set G))
    [hs : IsSimpleGroup L] [Finite L] (hbig : 24 < Nat.card L)
    (hcard : (Finset.univ.filter fun x => ε t x ≠ x).card = 4) {l : G} (hl : l ∈ L) {x : α}
    (hx : ε t x ≠ x) : ε l x = x := by
  classical
  set M : Finset α := Finset.univ.filter fun x => ε t x ≠ x with hM
  have hpres : ∀ l : L, ∀ x, ε l x ∈ M ↔ x ∈ M := by
    intro l x
    have hcomm : ∀ y, ε l (ε t y) = ε t (ε l y) := fun y => by
      have := congrArg (fun g => ε g y) (mem_centralizer_singleton_iff.1 (hLt l.2))
      simpa using this
    simp only [hM, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [← hcomm x]
    exact (Equiv.injective (ε l)).ne_iff
  let φ : L →* Perm {x // x ∈ M} :=
    { toFun := fun l => (ε l).subtypePerm (hpres l)
      map_one' := by
        ext x
        simp
      map_mul' := fun a b => by
        ext x
        simp
        rfl }
  have := MonoidHom.normal_ker φ
  rcases hs.eq_bot_or_eq_top_of_normal (MonoidHom.ker φ) with h | h
  · exfalso
    have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 h
    have h1 := Nat.card_le_card_of_injective φ hinj
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := {x // x ∈ M}), Fintype.card_coe,
      hcard] at h1
    have h24 : Nat.factorial 4 = 24 := by decide
    omega
  · have hφ : φ ⟨l, hl⟩ = 1 := by
      have : (⟨l, hl⟩ : L) ∈ MonoidHom.ker φ := h ▸ Subgroup.mem_top _
      exact this
    have hxM : x ∈ M := by simp [hM, hx]
    have := congrArg (fun p => ((p ⟨x, hxM⟩ : {y // y ∈ M}) : α)) hφ
    simpa [φ] using this

end Moved

section Points

variable {α : Type*} [DecidableEq α]

theorem exists_second_moved [Fintype α] {τ : Perm α} (hτ : ∀ x, τ (τ x) = x) (hτ1 : τ ≠ 1)
    (hsign : sign τ = 1) :
    ∃ a c : α, τ a ≠ a ∧ τ c ≠ c ∧ c ≠ a ∧ c ≠ τ a := by
  obtain ⟨a, ha⟩ : ∃ a, τ a ≠ a := by
    by_contra h
    push Not at h
    exact hτ1 (Equiv.ext h)
  by_cases hc : ∃ c, τ c ≠ c ∧ c ≠ a ∧ c ≠ τ a
  · obtain ⟨c, h1, h2, h3⟩ := hc
    exact ⟨a, c, ha, h1, h2, h3⟩
  · exfalso
    push Not at hc
    have hτswap : τ = swap a (τ a) := by
      ext x
      by_cases hx : τ x = x
      · have hxa : x ≠ a := fun h => ha (h ▸ hx)
        have hxb : x ≠ τ a := fun h => ha (by
          have : τ (τ a) = τ a := h ▸ hx
          rw [hτ] at this
          exact this.symm)
        rw [swap_apply_of_ne_of_ne hxa hxb, hx]
      · by_cases hxa : x = a
        · rw [hxa, swap_apply_left]
        · have := hc x hx hxa
          rw [this, hτ, swap_apply_right]
    have h1 : sign τ = -1 := by
      rw [hτswap]
      exact sign_swap ha.symm
    rw [h1] at hsign
    exact absurd hsign (by decide)

theorem swap_mul_swap_apply (p q r s : α) (hpr : p ≠ r) (hps : p ≠ s) (hqr : q ≠ r)
    (hqs : q ≠ s) :
    (swap p q * swap r s) p = q ∧ (swap p q * swap r s) q = p ∧ (swap p q * swap r s) r = s ∧
      (swap p q * swap r s) s = r := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hpr hps, swap_apply_left]
  · rw [Perm.mul_apply, swap_apply_of_ne_of_ne hqr hqs, swap_apply_right]
  · rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hps.symm hqs.symm]
  · rw [Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hpr.symm hqr.symm]

theorem swap_mul_swap_apply_of_ne (p q r s x : α) (hp : x ≠ p) (hq : x ≠ q) (hr : x ≠ r)
    (hs : x ≠ s) : (swap p q * swap r s) x = x := by
  rw [Perm.mul_apply, swap_apply_of_ne_of_ne hr hs, swap_apply_of_ne_of_ne hp hq]

omit [DecidableEq α] in
theorem perm_commute_of_fixes {P : α → Prop} {ρ σ : Perm α} (hρ : ∀ x, ¬ P x → ρ x = x)
    (hρP : ∀ x, P x → P (ρ x)) (hσ : ∀ x, P x → σ x = x) : ρ * σ = σ * ρ := by
  ext x
  by_cases hx : P x
  · rw [Perm.mul_apply, Perm.mul_apply, hσ x hx, hσ _ (hρP x hx)]
  · have hσx : ¬ P (σ x) := fun h => hx (by
      have : σ x = x := σ.injective (by rw [hσ _ h])
      rwa [this] at h)
    rw [Perm.mul_apply, Perm.mul_apply, hρ _ hσx, hρ _ hx]

end Points

section Second

variable {G : Type*} [Group G] {α : Type*} [Fintype α] [DecidableEq α]

theorem exists_second_involution (ε : G →* Perm α) (hε : Function.Injective ε)
    (hsurj : ∀ p : Perm α, sign p = 1 → ∃ g, ε g = p) {t : G} (ht2 : ε t * ε t = 1)
    (ht1 : t ≠ 1) (hsign : sign (ε t) = 1) {L : Subgroup G}
    (hLt : L ≤ centralizer ({t} : Set G))
    (hLn : (L.subgroupOf (centralizer ({t} : Set G))).Normal) [hs : IsSimpleGroup L] [Finite L]
    (hnab : ∃ a b : L, a * b ≠ b * a) (hbig : 24 < Nat.card L) :
    ∃ s : G, (∀ l ∈ L, s * l = l * s) ∧ orderOf s = 2 ∧ s ≠ t ∧ s * t = t * s := by
  classical
  have hτ : ∀ x, ε t (ε t x) = x := fun x => by
    have := congrArg (fun p => p x) ht2
    simpa using this
  have hτ1 : ε t ≠ 1 := fun h => ht1 (hε (by rw [h, map_one]))
  obtain ⟨a, c, ha, hc, hca, hcb⟩ := exists_second_moved hτ hτ1 hsign
  obtain ⟨b, hb⟩ : ∃ b, ε t a = b := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d, ε t c = d := ⟨_, rfl⟩
  rw [hb] at hcb
  have hba : ε t b = a := by rw [← hb]; exact hτ a
  have hdc : ε t d = c := by rw [← hd]; exact hτ c
  have hab : a ≠ b := fun h => ha (hb.trans h.symm)
  have hac : a ≠ c := hca.symm
  have hbc : b ≠ c := hcb.symm
  have hcd : c ≠ d := fun h => hc (hd.trans h.symm)
  have had : a ≠ d := fun h => hcb (by
    have := congrArg (ε t) h
    rw [hb, hdc] at this
    exact this.symm)
  have hbd : b ≠ d := fun h => hac (by
    have := congrArg (ε t) h
    rw [hba, hdc] at this
    exact this)
  by_cases hB : ∃ e, e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ ε t e ≠ e
  ·
    obtain ⟨e, hea, heb, hec, hed, he⟩ := hB
    obtain ⟨hσa, hσb, hσc, hσd⟩ := swap_mul_swap_apply a b c d hac had hbc hbd
    have hσ : ∀ x, (swap a b * swap c d) x = x ∨ (swap a b * swap c d) x = ε t x := by
      intro x
      by_cases hxa : x = a
      · right
        rw [hxa, hσa, hb]
      by_cases hxb : x = b
      · right
        rw [hxb, hσb, hba]
      by_cases hxc : x = c
      · right
        rw [hxc, hσc, hd]
      by_cases hxd : x = d
      · right
        rw [hxd, hσd, hdc]
      left
      exact swap_mul_swap_apply_of_ne a b c d x hxa hxb hxc hxd
    have hsg : sign (swap a b * swap c d) = 1 := by
      rw [Perm.sign_mul, sign_swap hab, sign_swap hcd]
      decide
    obtain ⟨g, hg⟩ := hsurj _ hsg
    have hgW : g ∈ baseGroup ε t hτ := by
      rw [mem_baseGroup]
      intro x
      rw [hg]
      exact hσ x
    have hgg : g * g = 1 := hε (by
      rw [map_mul, map_one]
      ext x
      exact baseGroup_apply_apply hgW x)
    have hg1 : g ≠ 1 := by
      intro h1
      rw [h1, map_one] at hg
      have := congrArg (fun p : Perm α => p a) hg
      simp only [Perm.coe_one, id_eq] at this
      rw [hσa] at this
      exact hab this
    refine ⟨g, fun l hl => commute_of_mem_baseGroup hε hLt hLn hnab hgW hl, ?_, ?_,
      baseGroup_mul_comm hε hgW t_mem_baseGroup⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hgg) hg1
    · intro h
      rw [h] at hg
      have := congrArg (fun p : Perm α => p e) hg
      rw [swap_mul_swap_apply_of_ne a b c d e hea heb hec hed] at this
      exact he this
  ·
    push Not at hB
    have hmoved : ∀ x, ε t x ≠ x → x = a ∨ x = b ∨ x = c ∨ x = d := by
      intro x hx
      by_contra hcon
      push Not at hcon
      exact hx (hB x hcon.1 hcon.2.1 hcon.2.2.1 hcon.2.2.2)
    have hbmoved : ε t b ≠ b := by
      rw [hba]
      exact hab
    have hdmoved : ε t d ≠ d := by
      rw [hdc]
      exact hcd
    have hcard : (Finset.univ.filter fun x => ε t x ≠ x).card = 4 := by
      have hset : (Finset.univ.filter fun x => ε t x ≠ x) = {a, b, c, d} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton]
        refine ⟨hmoved x, ?_⟩
        rintro (rfl | rfl | rfl | rfl)
        · exact ha
        · exact hbmoved
        · exact hc
        · exact hdmoved
      rw [hset, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_pair hcd]
      · simp [hbc, hbd]
      · simp [hab, hac, had]
    have hfix : ∀ l ∈ L, ∀ x, (x = a ∨ x = b ∨ x = c ∨ x = d) → ε l x = x := by
      intro l hl x hx
      refine fixes_moved_points ε t hLt hbig hcard hl ?_
      rcases hx with rfl | rfl | rfl | rfl
      · exact ha
      · exact hbmoved
      · exact hc
      · exact hdmoved
    obtain ⟨hρa, hρc, hρb, hρd⟩ := swap_mul_swap_apply a c b d hab had hbc.symm hcd
    have hρout : ∀ x, x ≠ a → x ≠ b → x ≠ c → x ≠ d → (swap a c * swap b d) x = x :=
      fun x hxa hxb hxc hxd => swap_mul_swap_apply_of_ne a c b d x hxa hxc hxb hxd
    have hρρ : ∀ x, (swap a c * swap b d) ((swap a c * swap b d) x) = x := by
      intro x
      by_cases hxa : x = a
      · rw [hxa, hρa, hρc]
      by_cases hxb : x = b
      · rw [hxb, hρb, hρd]
      by_cases hxc : x = c
      · rw [hxc, hρc, hρa]
      by_cases hxd : x = d
      · rw [hxd, hρd, hρb]
      rw [hρout x hxa hxb hxc hxd, hρout x hxa hxb hxc hxd]
    have hsg : sign (swap a c * swap b d) = 1 := by
      rw [Perm.sign_mul, sign_swap hac, sign_swap hbd]
      decide
    obtain ⟨g, hg⟩ := hsurj _ hsg
    have hgg : g * g = 1 := hε (by
      rw [map_mul, map_one, hg]
      ext x
      exact hρρ x)
    have hg1 : g ≠ 1 := by
      intro h1
      rw [h1, map_one] at hg
      have := congrArg (fun p : Perm α => p a) hg
      simp only [Perm.coe_one, id_eq] at this
      rw [hρa] at this
      exact hac this
    refine ⟨g, fun l hl => ?_, ?_, ?_, ?_⟩
    · apply hε
      rw [map_mul, map_mul, hg]
      refine perm_commute_of_fixes (P := fun x => x = a ∨ x = b ∨ x = c ∨ x = d) ?_ ?_
        (hfix l hl)
      · intro x hx
        simp only [not_or] at hx
        exact hρout x hx.1 hx.2.1 hx.2.2.1 hx.2.2.2
      · rintro x (rfl | rfl | rfl | rfl)
        · rw [hρa]
          exact Or.inr (Or.inr (Or.inl rfl))
        · rw [hρb]
          exact Or.inr (Or.inr (Or.inr rfl))
        · rw [hρc]
          exact Or.inl rfl
        · rw [hρd]
          exact Or.inr (Or.inl rfl)
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (by rw [sq]; exact hgg) hg1
    · intro h
      rw [h] at hg
      have := congrArg (fun p : Perm α => p a) hg
      rw [hρa, hb] at this
      exact hbc this
    · apply hε
      rw [map_mul, map_mul, hg]
      ext x
      show (swap a c * swap b d) (ε t x) = ε t ((swap a c * swap b d) x)
      by_cases hxa : x = a
      · rw [hxa, hb, hρa, hρb, hd]
      by_cases hxb : x = b
      · rw [hxb, hba, hρa, hρb, hdc]
      by_cases hxc : x = c
      · rw [hxc, hd, hρd, hρc, hb]
      by_cases hxd : x = d
      · rw [hxd, hdc, hρc, hρd, hba]
      simp [hρout x hxa hxb hxc hxd, hB x hxa hxb hxc hxd]

end Second

theorem card_alternatingGroup_fin_gt {n : ℕ} (hn : 8 ≤ n) :
    24 < Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at h2
  have h3 : Nat.factorial 8 ≤ Nat.factorial n := Nat.factorial_le hn
  have h4 : Nat.factorial 8 = 40320 := by decide
  omega

end CFSG.OddStandard.AltStdFaithful

namespace CFSG.OddStandard

open Subgroup Equiv Equiv.Perm CFSG.Open

theorem altStandard_in_alternating
    {G : Type} [Group G] [Finite G] {m : ℕ} (e : G ≃* alternatingGroup (Fin m))
    {L : Subgroup G} (hL : standardComponentIsStandard L) {n : ℕ} (hn : 8 ≤ n)
    (θ : L ≃* alternatingGroup (Fin n)) (S : Sylow 2 (centralizer (L : Set G))) :
    ¬ IsCyclic (S : Subgroup (centralizer (L : Set G))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
  have hLsimple : IsSimpleGroup L := θ.isSimpleGroup
  have hnab : ∃ a b : L, a * b ≠ b * a := by
    have hnabA : ∃ a b : alternatingGroup (Fin n), a * b ≠ b * a := by
      by_contra h
      push Not at h
      have hc : IsMulCommutative (alternatingGroup (Fin n)) := ⟨⟨fun a b => h a b⟩⟩
      have := alternatingGroup.isMulCommutative_iff_card_le_three.1 hc
      rw [Nat.card_eq_fintype_card, Fintype.card_fin] at this
      omega
    obtain ⟨a, b, hab⟩ := hnabA
    refine ⟨θ.symm a, θ.symm b, fun h => hab ?_⟩
    have := congrArg θ h
    simpa using this
  have hbig : 24 < Nat.card L := by
    rw [Nat.card_congr θ.toEquiv]
    exact AltStdFaithful.card_alternatingGroup_fin_gt hn
  let ε : G →* Perm (Fin m) := (alternatingGroup (Fin m)).subtype.comp e.toMonoidHom
  have hε : Function.Injective ε := Subtype.val_injective.comp e.injective
  have hsurj : ∀ p : Perm (Fin m), sign p = 1 → ∃ g, ε g = p := fun p hp =>
    ⟨e.symm ⟨p, Equiv.Perm.mem_alternatingGroup.2 hp⟩, by simp [ε]⟩
  obtain ⟨t, htC, ht2⟩ : ∃ t : G, t ∈ centralizer (L : Set G) ∧ orderOf t = 2 := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.1 hL.2.1)
    exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩
  obtain ⟨-, hLt, hLn, -, -⟩ :=
    LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality hL htC ht2
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht2
    omega
  have htsq : t * t = 1 := by
    rw [← sq, ← ht2]
    exact pow_orderOf_eq_one t
  have htτ : ε t * ε t = 1 := by rw [← map_mul, htsq, map_one]
  have hsign : sign (ε t) = 1 := Equiv.Perm.mem_alternatingGroup.1 (e t).2
  obtain ⟨s, hsL, hs2, hst, hsc⟩ :=
    AltStdFaithful.exists_second_involution ε hε hsurj htτ ht1 hsign hLt hLn hnab hbig
  have hsC : s ∈ centralizer (L : Set G) :=
    mem_centralizer_iff.2 fun l hl => (hsL l hl).symm
  refine AltStdFaithful.not_isCyclic_sylow_two S (x := ⟨t, htC⟩) (y := ⟨s, hsC⟩)
    ((Subgroup.orderOf_mk t htC).trans ht2) ((Subgroup.orderOf_mk s hsC).trans hs2) ?_ ?_
  · intro h
    exact hst (congrArg Subtype.val h).symm
  · exact Subtype.ext hsc.symm

end CFSG.OddStandard
