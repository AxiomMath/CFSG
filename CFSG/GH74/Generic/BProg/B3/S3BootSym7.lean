module

public import CFSG.GH74.Generic.BProg.B3.S3Theta52
public import CFSG.GH74.GLS.C3.Layer1.Th2P61A7

public section

namespace CFSG.GH74.Generic.BProg.B3

open Equiv Equiv.Perm Subgroup

namespace S3BootSym7

def QSub (π : Perm (Fin 7)) (hπ : π * π = 1) : Subgroup (Perm (Fin 7)) where
  carrier := {g | ∀ i, g i = i ∨ g i = π i}
  one_mem' := fun _ => Or.inl rfl
  mul_mem' := by
    intro g h hg hh i
    rcases hh i with h1 | h1
    · show g (h i) = i ∨ g (h i) = π i
      rw [h1]
      exact hg i
    · show g (h i) = i ∨ g (h i) = π i
      rw [h1]
      rcases hg (π i) with h2 | h2
      · exact Or.inr h2
      · left
        rw [h2]
        simpa using congrArg (fun f : Perm (Fin 7) => f i) hπ
  inv_mem' := by
    intro g hg i
    have hj : g (g⁻¹ i) = i := by simp
    rcases hg (g⁻¹ i) with h1 | h1
    · exact Or.inl (h1.symm.trans hj)
    · right
      have h2 : π (g⁻¹ i) = i := h1.symm.trans hj
      have h3 := congrArg π h2
      have h4 : π (π (g⁻¹ i)) = g⁻¹ i := by
        simpa using congrArg (fun f : Perm (Fin 7) => f (g⁻¹ i)) hπ
      rw [h4] at h3
      exact h3

theorem eq_of_support_eq {π : Perm (Fin 7)} {hπ : π * π = 1} {g h : Perm (Fin 7)}
    (hg : g ∈ QSub π hπ) (hh : h ∈ QSub π hπ) (hs : g.support = h.support) : g = h := by
  ext i
  by_cases hgi : g i = i
  · have h1 : i ∉ g.support := by simpa using hgi
    rw [hs] at h1
    have h2 : h i = i := by simpa using h1
    rw [hgi, h2]
  · have h1 : i ∈ g.support := by simpa using hgi
    rw [hs] at h1
    have hhi : h i ≠ i := by simpa using h1
    rw [(hg i).resolve_left hgi, (hh i).resolve_left hhi]

theorem not_isRootFour_of_le {π : Perm (Fin 7)} {hπ : π * π = 1} {R : Subgroup (Perm (Fin 7))}
    (hR : R ≤ QSub π hπ) : ¬ GLS.Th2.Obs.IsRootFour R := by
  rintro ⟨-, hcard, hsq, S, -, hS⟩
  have hall : ∀ r₁ ∈ R, ∀ r₂ ∈ R, r₁ ≠ 1 → r₂ ≠ 1 → r₁ = r₂ := fun r₁ h₁ r₂ h₂ n₁ n₂ =>
    eq_of_support_eq (hR h₁) (hR h₂) ((hS r₁ h₁ n₁).trans (hS r₂ h₂ n₂).symm)
  by_cases hex : ∃ r ∈ R, r ≠ 1
  · obtain ⟨r, hr, hr1⟩ := hex
    have hle : R ≤ Subgroup.zpowers r := by
      intro g hg
      by_cases hg1 : g = 1
      · rw [hg1]
        exact Subgroup.one_mem _
      · rw [hall g hg r hr hg1 hr1]
        exact Subgroup.mem_zpowers r
    have h1 : Nat.card ↥R ≤ Nat.card ↥(Subgroup.zpowers r) := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at h1
    have h2 : orderOf r ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hsq r hr)
    have h3 : orderOf r ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    omega
  · push Not at hex
    have hbot : R = ⊥ := (Subgroup.eq_bot_iff_forall R).2 hex
    rw [hbot, Subgroup.card_bot] at hcard
    omega

theorem exists_points {y : Perm (Fin 7)} (hy2 : y * y = 1) (hS : y.support.card = 4) :
    ∃ a b c d : Fin 7, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      y = swap a b * swap c d := by
  classical
  have hinv : ∀ i, y (y i) = i := fun i => by
    simpa using congrArg (fun f : Perm (Fin 7) => f i) hy2
  have hpos : 0 < y.support.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
  have hya : y a ≠ a := Equiv.Perm.mem_support.mp ha
  obtain ⟨b, hb⟩ : ∃ b, b = y a := ⟨_, rfl⟩
  have hba : b ≠ a := by rw [hb]; exact hya
  have hyb : y b = a := by rw [hb]; exact hinv a
  have hbs : b ∈ y.support := by
    rw [Equiv.Perm.mem_support, hyb]
    exact fun h => hba h.symm
  have hbe : b ∈ y.support.erase a := Finset.mem_erase.mpr ⟨hba, hbs⟩
  have hcard2 : ((y.support.erase a).erase b).card = 2 := by
    rw [Finset.card_erase_of_mem hbe, Finset.card_erase_of_mem ha, hS]
  obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < ((y.support.erase a).erase b).card)
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).1
  have hcs : c ∈ y.support := (Finset.mem_erase.mp (Finset.mem_erase.mp hc).2).2
  have hyc : y c ≠ c := Equiv.Perm.mem_support.mp hcs
  obtain ⟨d, hd⟩ : ∃ d, d = y c := ⟨_, rfl⟩
  have hdc : d ≠ c := by rw [hd]; exact hyc
  have hyd : y d = c := by rw [hd]; exact hinv c
  have hda : d ≠ a := by
    intro h
    apply hcb
    rw [← hyd, h, ← hb]
  have hdb : d ≠ b := by
    intro h
    apply hca
    rw [← hyd, h, hyb]
  have hab : a ≠ b := fun h => hba h.symm
  have hac : a ≠ c := fun h => hca h.symm
  have had : a ≠ d := fun h => hda h.symm
  have hbc : b ≠ c := fun h => hcb h.symm
  have hbd : b ≠ d := fun h => hdb h.symm
  have hcd : c ≠ d := fun h => hdc h.symm
  have hds : d ∈ y.support := by
    rw [Equiv.Perm.mem_support, hyd]
    exact fun h => hdc h.symm
  have hsub : ({a, b, c, d} : Finset (Fin 7)) ⊆ y.support := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ha
    · exact hbs
    · exact hcs
    · exact hds
  have hc4 : ({a, b, c, d} : Finset (Fin 7)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  have heq : ({a, b, c, d} : Finset (Fin 7)) = y.support :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hS, hc4])
  have hout : ∀ i, i ≠ a → i ≠ b → i ≠ c → i ≠ d → y i = i := by
    intro i h1 h2 h3 h4
    have : i ∉ y.support := by
      rw [← heq]
      simp [h1, h2, h3, h4]
    simpa using this
  refine ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, ?_⟩
  ext i
  by_cases h1 : i = a
  · subst h1
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left, ← hb]
  by_cases h2 : i = b
  · subst h2
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hbc hbd, Equiv.swap_apply_right, hyb]
  by_cases h3 : i = c
  · subst h3
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hda hdb, ← hd]
  by_cases h4 : i = d
  · subst h4
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hca hcb, hyd]
  rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h3 h4,
    Equiv.swap_apply_of_ne_of_ne h1 h2, hout i h1 h2 h3 h4]

theorem exists_two_outside (a b c d : Fin 7) :
    ∃ e f : Fin 7, e ≠ f ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d := by
  classical
  have h : 1 < (Finset.univ \ ({a, b, c, d} : Finset (Fin 7))).card := by
    have h1 : ({a, b, c, d} : Finset (Fin 7)).card ≤ 4 := by
      refine (Finset.card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
      simp
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp h
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton,
    not_or] at he hf
  exact ⟨e, f, hef, he.1, he.2.1, he.2.2.1, he.2.2.2, hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

theorem swap_disjoint {a b c d : Fin 7} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    (swap a b).Disjoint (swap c d) := by
  intro i
  by_cases h : i = a ∨ i = b
  · right
    rcases h with rfl | rfl
    · exact swap_apply_of_ne_of_ne hac had
    · exact swap_apply_of_ne_of_ne hbc hbd
  · left
    push Not at h
    exact swap_apply_of_ne_of_ne h.1 h.2

theorem sq_eq_one_of_commute {g h : Perm (Fin 7)} (hc : Commute g h) (hg : g * g = 1)
    (hh : h * h = 1) : (g * h) * (g * h) = 1 := by
  have := hc.mul_pow 2
  simpa [sq, hg, hh] using this

theorem eq_one_or_of_mem_zpowers {g h : Perm (Fin 7)} (hg : g * g = 1)
    (hh : h ∈ Subgroup.zpowers g) : h = 1 ∨ h = g := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  rcases Int.even_or_odd' k with ⟨n, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hg, one_zpow]
  · right
    rw [zpow_add_one, zpow_mul, zpow_two, hg, one_zpow, one_mul]

theorem assemble {a b c d e f : Fin 7} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hae : a ≠ e)
    (haf : a ≠ f) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hbf : b ≠ f) (hcd : c ≠ d)
    (hce : c ≠ e) (hcf : c ≠ f) (hde : d ≠ e) (hdf : d ≠ f) (hef : e ≠ f) :
    (swap a b * swap e f) * (swap a b * swap e f) = 1 ∧
      swap a b * swap e f ∈ alternatingGroup (Fin 7) ∧ swap a b * swap e f ≠ 1 ∧
      (swap a b * swap e f) * (swap a b * swap c d) =
        (swap a b * swap c d) * (swap a b * swap e f) ∧
      (swap a b * swap e f) * swap e f = swap e f * (swap a b * swap e f) ∧
      swap a b * swap e f ∉ Subgroup.zpowers (swap a b * swap c d) ⊔ Subgroup.zpowers (swap e f) ∧
      (∀ R : Subgroup (Perm (Fin 7)),
        R ≤ Subgroup.zpowers (swap a b * swap c d) ⊔ Subgroup.zpowers (swap e f) ⊔
          Subgroup.zpowers (swap a b * swap e f) → ¬ GLS.Th2.Obs.IsRootFour R) := by
  have c12 : Commute (swap a b) (swap c d) := (swap_disjoint hac had hbc hbd).commute
  have c13 : Commute (swap a b) (swap e f) := (swap_disjoint hae haf hbe hbf).commute
  have c23 : Commute (swap c d) (swap e f) := (swap_disjoint hce hcf hde hdf).commute
  have s1 : swap a b * swap a b = 1 := swap_mul_self a b
  have s2 : swap c d * swap c d = 1 := swap_mul_self c d
  have s3 : swap e f * swap e f = 1 := swap_mul_self e f
  have hyt : Commute (swap a b * swap c d) (swap e f) := c13.mul_left c23
  have hy2 : (swap a b * swap c d) * (swap a b * swap c d) = 1 := sq_eq_one_of_commute c12 s1 s2
  have hu2 : (swap a b * swap e f) * (swap a b * swap e f) = 1 := sq_eq_one_of_commute c13 s1 s3
  have hπ : ((swap a b * swap c d) * swap e f) * ((swap a b * swap c d) * swap e f) = 1 :=
    sq_eq_one_of_commute hyt hy2 s3
  have huy : Commute (swap a b * swap e f) (swap a b * swap c d) := by
    have h1 : Commute (swap a b * swap e f) (swap a b) :=
      (Commute.refl (swap a b)).mul_left c13.symm
    have h2 : Commute (swap a b * swap e f) (swap c d) := c12.mul_left c23.symm
    exact h1.mul_right h2
  have hut : Commute (swap a b * swap e f) (swap e f) := c13.mul_left (Commute.refl (swap e f))
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hea := hae.symm
  have hfa := haf.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have heb := hbe.symm
  have hfb := hbf.symm
  have hdc := hcd.symm
  have hec := hce.symm
  have hfc := hcf.symm
  have hed := hde.symm
  have hfd := hdf.symm
  have hfe := hef.symm
  have hall := And.intro hab (And.intro hac (And.intro had (And.intro hae (And.intro haf
    (And.intro hbc (And.intro hbd (And.intro hbe (And.intro hbf
    (And.intro hcd (And.intro hce (And.intro hcf (And.intro hde
    (And.intro hdf (And.intro hef (And.intro hba (And.intro hca
    (And.intro hda (And.intro hea (And.intro hfa (And.intro hcb
    (And.intro hdb (And.intro heb (And.intro hfb (And.intro hdc
    (And.intro hec (And.intro hfc (And.intro hed (And.intro hfd (hfe)))))))))))))))))))))))))))))
  have huc : (swap a b * swap e f) c = c := by
    rw [Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hce hcf, swap_apply_of_ne_of_ne hca hcb]
  have hua : (swap a b * swap e f) a = b := by
    rw [Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hae haf, swap_apply_left]
  have hta : swap e f a = a := swap_apply_of_ne_of_ne hae haf
  have htc : swap e f c = c := swap_apply_of_ne_of_ne hce hcf
  have hyc : (swap a b * swap c d) c = d := by
    rw [Equiv.Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hdb]
  refine ⟨hu2, ?_, ?_, huy.eq, hut.eq, ?_, ?_⟩
  · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
      Equiv.Perm.sign_swap hef]
    decide
  · intro h
    have := congrArg (fun g : Perm (Fin 7) => g a) h
    simp only [hua, Equiv.Perm.one_apply] at this
    exact hba this
  · intro hmem
    have hcomm : ∀ h ∈ Subgroup.zpowers (swap a b * swap c d), ∀ k ∈ Subgroup.zpowers (swap e f),
        h * k = k * h := by
      intro h hh k hk
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      exact (hyt.zpow_zpow m n).eq
    obtain ⟨h, hh, k, hk, hu⟩ := S3Theta52.exists_mul_of_mem_sup hcomm hmem
    rcases eq_one_or_of_mem_zpowers hy2 hh with rfl | rfl <;>
      rcases eq_one_or_of_mem_zpowers s3 hk with rfl | rfl
    · have := congrArg (fun g : Perm (Fin 7) => g a) hu
      simp only [hua, mul_one, Equiv.Perm.one_apply] at this
      exact hba this
    · have := congrArg (fun g : Perm (Fin 7) => g a) hu
      simp only [hua, one_mul, hta] at this
      exact hba this
    · have := congrArg (fun g : Perm (Fin 7) => g c) hu
      simp only [huc, mul_one, hyc] at this
      exact hdc this.symm
    · have := congrArg (fun g : Perm (Fin 7) => g c) hu
      simp only [huc, Equiv.Perm.mul_apply, htc, hyc] at this
      exact hdc this.symm
  · intro R hR
    refine not_isRootFour_of_le (π := (swap a b * swap c d) * swap e f) (hπ := hπ) ?_
    refine hR.trans (sup_le (sup_le ?_ ?_) ?_)
    · rw [Subgroup.zpowers_le]
      intro i
      by_cases hia : i = a
      · subst hia
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hib : i = b
      · subst hib
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hic : i = c
      · subst hic
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hid : i = d
      · subst hid
        right
        simp [Equiv.swap_apply_def, hall]
      left
      simp [Equiv.swap_apply_def, hia, hib, hic, hid]
    · rw [Subgroup.zpowers_le]
      intro i
      by_cases hie : i = e
      · subst hie
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hif : i = f
      · subst hif
        right
        simp [Equiv.swap_apply_def, hall]
      left
      simp [Equiv.swap_apply_def, hie, hif]
    · rw [Subgroup.zpowers_le]
      intro i
      by_cases hia : i = a
      · subst hia
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hib : i = b
      · subst hib
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hie : i = e
      · subst hie
        right
        simp [Equiv.swap_apply_def, hall]
      by_cases hif : i = f
      · subst hif
        right
        simp [Equiv.swap_apply_def, hall]
      left
      simp [Equiv.swap_apply_def, hia, hib, hie, hif]

theorem swap_ne_one' {e f : Fin 7} (hef : e ≠ f) : swap e f ≠ 1 := by
  intro h
  have := congrArg (fun g : Perm (Fin 7) => g e) h
  simp only [swap_apply_left, Equiv.Perm.one_apply] at this
  exact hef this.symm

theorem ne_of_swap_fix {e f i : Fin 7} (hef : e ≠ f) (h : swap e f i = i) : i ≠ e ∧ i ≠ f := by
  constructor
  · rintro rfl
    rw [swap_apply_left] at h
    exact hef h.symm
  · rintro rfl
    rw [swap_apply_right] at h
    exact hef h

end S3BootSym7

section SD17

open S3BootSym7

theorem lemma2911 {F F₀ F₁ : Subgroup (Equiv.Perm (Fin 7))} (hF₀ : GLS.Th2.Obs.IsRootFour F₀)
    (hF₁ : F₁ = ⊥ ∨ ∃ t : Equiv.Perm (Fin 7), t.IsSwap ∧ F₁ = Subgroup.zpowers t ∧
      ∀ i, (∃ f ∈ F₀, f i ≠ i) → t i = i) (hF : F = F₀ ⊔ F₁) {x : Equiv.Perm (Fin 7)}
    (hx : x ∈ F) :
    ∃ u : Equiv.Perm (Fin 7), u ∈ alternatingGroup (Fin 7) ∧ u * u = 1 ∧ u ≠ 1 ∧
      ∃ F' : Subgroup (Equiv.Perm (Fin 7)), F' ≤ F ∧ 2 * Nat.card ↥F' = Nat.card ↥F ∧ x ∈ F' ∧
        F₁ ≤ F' ∧ (∀ f ∈ F', f * u = u * f) ∧ u ∉ F' ∧
        ∀ R : Subgroup (Equiv.Perm (Fin 7)), R ≤ F' ⊔ Subgroup.zpowers u →
          ¬ GLS.Th2.Obs.IsRootFour R := by
  classical
  obtain ⟨-, hcard0, hsq0, S, hS4, hSupp⟩ := hF₀
  obtain ⟨y₀, hy₀F, hy₀1⟩ : ∃ g ∈ F₀, g ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : F₀ = ⊥ := (Subgroup.eq_bot_iff_forall F₀).2 h
    rw [hbot, Subgroup.card_bot] at hcard0
    omega
  have hcomm : ∀ f ∈ F₀, ∀ g ∈ F₁, f * g = g * f := by
    intro f hf g hg
    rcases hF₁ with rfl | ⟨t, -, rfl, hfix⟩
    · rw [Subgroup.mem_bot.mp hg]
      simp
    · have hd : f.Disjoint t := by
        intro i
        by_cases hi : f i = i
        · exact Or.inl hi
        · exact Or.inr (hfix i ⟨f, hf, hi⟩)
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (hd.commute.zpow_right n).eq
  obtain ⟨f₀, hf₀, f₁, hf₁, hxe⟩ := S3Theta52.exists_mul_of_mem_sup hcomm (hF ▸ hx)
  obtain ⟨y, hyF, hy1, hxy⟩ : ∃ y ∈ F₀, y ≠ 1 ∧ x ∈ Subgroup.zpowers y ⊔ F₁ := by
    by_cases h : f₀ = 1
    · refine ⟨y₀, hy₀F, hy₀1, ?_⟩
      rw [hxe, h, one_mul]
      exact Subgroup.mem_sup_right hf₁
    · refine ⟨f₀, hf₀, h, ?_⟩
      rw [hxe]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers f₀))
        (Subgroup.mem_sup_right hf₁)
  have hy2 : y * y = 1 := hsq0 y hyF
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd, hyeq⟩ :=
    exists_points hy2 (by rw [hSupp y hyF hy1]; exact hS4)
  have hba := hab.symm
  have hca := hac.symm
  have hda := had.symm
  have hcb := hbc.symm
  have hdb := hbd.symm
  have hdc := hcd.symm
  have hya : y a ≠ a := by
    rw [hyeq, Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hac had, swap_apply_left]
    exact hba
  have hyb : y b ≠ b := by
    rw [hyeq, Equiv.Perm.mul_apply, swap_apply_of_ne_of_ne hbc hbd, swap_apply_right]
    exact hab
  have hyc : y c ≠ c := by
    rw [hyeq, Equiv.Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hda hdb]
    exact hdc
  have hyd : y d ≠ d := by
    rw [hyeq, Equiv.Perm.mul_apply, swap_apply_right, swap_apply_of_ne_of_ne hca hcb]
    exact hcd
  obtain ⟨e, f, hef, hea, heb, hec, hed, hfa, hfb, hfc, hfd, hF₁le, hF₁card⟩ :
      ∃ e f : Fin 7, e ≠ f ∧ e ≠ a ∧ e ≠ b ∧ e ≠ c ∧ e ≠ d ∧ f ≠ a ∧ f ≠ b ∧ f ≠ c ∧ f ≠ d ∧
        F₁ ≤ Subgroup.zpowers (swap e f) ∧
        (Nat.card ↥F₁ = 1 ∧ F₁ = ⊥ ∨ Nat.card ↥F₁ = 2 ∧ F₁ = Subgroup.zpowers (swap e f)) := by
    rcases hF₁ with rfl | ⟨t, ht, rfl, hfix⟩
    · obtain ⟨e, f, hef, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_two_outside a b c d
      exact ⟨e, f, hef, h1, h2, h3, h4, h5, h6, h7, h8, bot_le, Or.inl ⟨Subgroup.card_bot, rfl⟩⟩
    · obtain ⟨e, f, hef, rfl⟩ := ht
      have h1 := ne_of_swap_fix hef (hfix a ⟨y, hyF, hya⟩)
      have h2 := ne_of_swap_fix hef (hfix b ⟨y, hyF, hyb⟩)
      have h3 := ne_of_swap_fix hef (hfix c ⟨y, hyF, hyc⟩)
      have h4 := ne_of_swap_fix hef (hfix d ⟨y, hyF, hyd⟩)
      refine ⟨e, f, hef, h1.1.symm, h2.1.symm, h3.1.symm, h4.1.symm, h1.2.symm, h2.2.symm,
        h3.2.symm, h4.2.symm, le_rfl, Or.inr ⟨?_, rfl⟩⟩
      rw [Nat.card_zpowers]
      exact orderOf_eq_prime (by rw [sq]; exact swap_mul_self e f) (swap_ne_one' hef)
  have hae := hea.symm
  have hbe := heb.symm
  have hce := hec.symm
  have hde := hed.symm
  have haf := hfa.symm
  have hbf := hfb.symm
  have hcf := hfc.symm
  have hdf := hfd.symm
  obtain ⟨hu2, huA, hu1, huy, hut, hunot, hnoroot⟩ :=
    assemble hab hac had hae haf hbc hbd hbe hbf hcd hce hcf hde hdf hef
  rw [← hyeq] at huy hunot hnoroot
  have hF₀F₁ : F₀ ⊓ F₁ = ⊥ := by
    rcases hF₁card with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact inf_bot_eq _
    · rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      obtain ⟨hg0, hg1⟩ := hg
      rcases eq_one_or_of_mem_zpowers (swap_mul_self e f) hg1 with h | h
      · exact h
      · exfalso
        have hne : g ≠ 1 := by
          rw [h]
          exact swap_ne_one' hef
        have hs := hSupp g hg0 hne
        have hS2 : S.card = 2 := by
          rw [← hs, h, Equiv.Perm.support_swap hef, Finset.card_pair hef]
        omega
  have hy2card : Nat.card ↥(Subgroup.zpowers y) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hy2) hy1
  have hyle : Subgroup.zpowers y ≤ F₀ := (Subgroup.zpowers_le).2 hyF
  have hzy : Subgroup.zpowers y ⊓ F₁ = ⊥ :=
    eq_bot_iff.2 (le_trans (inf_le_inf_right _ hyle) hF₀F₁.le)
  have hcommy : ∀ h ∈ Subgroup.zpowers y, ∀ k ∈ F₁, h * k = k * h := fun h hh k hk =>
    hcomm h (hyle hh) k hk
  have hcardF : Nat.card ↥F = 4 * Nat.card ↥F₁ := by
    rw [hF, S3Theta52.card_sup_of_commute hcomm hF₀F₁, hcard0]
  have hcardF' : Nat.card ↥(Subgroup.zpowers y ⊔ F₁) = 2 * Nat.card ↥F₁ := by
    rw [S3Theta52.card_sup_of_commute hcommy hzy, hy2card]
  refine ⟨swap a b * swap e f, huA, hu2, hu1, Subgroup.zpowers y ⊔ F₁, ?_, ?_, hxy, le_sup_right,
    ?_, ?_, ?_⟩
  · rw [hF]
    exact sup_le_sup_right hyle _
  · rw [hcardF', hcardF]
    ring
  · have hle : Subgroup.zpowers y ⊔ F₁ ≤ Subgroup.centralizer ({swap a b * swap e f} : Set _) := by
      refine sup_le ((Subgroup.zpowers_le).2 ?_) (hF₁le.trans ((Subgroup.zpowers_le).2 ?_))
      · exact Subgroup.mem_centralizer_singleton_iff.mpr huy.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hut.symm
    intro g hg
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
  · intro hmem
    exact hunot (sup_le_sup_left hF₁le _ hmem)
  · intro R hR
    exact hnoroot R (hR.trans (sup_le_sup_right (sup_le_sup_left hF₁le _) _))

end SD17

end CFSG.GH74.Generic.BProg.B3
