module

public import CFSG.GH74.Tits83.Defs
public import CFSG.GH74.BNPair.RootGroups
public import CFSG.LieType.Steinberg.Collection

public section

namespace CFSG.GH74.Tits83

open CFSG.GH74.BNPair

open scoped commutatorElement Pointwise

universe u

private theorem nodup_intList (i j : ℤ) : (intList i j).Nodup := by
  refine List.Nodup.map (fun a b h => ?_) List.nodup_range
  have : (a : ℤ) = b := by simpa using h
  exact_mod_cast this

private theorem prod_pad {X : Type u} [Group X] {l a b r : ℤ}
    (hl : l ≤ a) (ha : a ≤ b) (hb : b ≤ r) (f : ℤ → X) :
    ((intList l r).map (fun k => if a ≤ k ∧ k ≤ b then f k else 1)).prod =
      ((intList a b).map f).prod := by
  classical
  have happ : ∀ {x y z : ℤ}, x ≤ y + 1 → y ≤ z →
      intList x z = intList x y ++ intList (y + 1) z := by
    intro x y z h1 h2
    apply List.ext_getElem
    · simp only [intList, List.length_append, List.length_map, List.length_range]
      omega
    · intro t ht1 ht2
      simp only [intList, List.length_map, List.length_range] at ht1 ht2 ⊢
      by_cases ht : t < (y + 1 - x).toNat
      · rw [List.getElem_append_left (by simpa using ht)]
        simp
      · rw [List.getElem_append_right (by simp; omega)]
        simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
        omega
  have e1 : intList l r = intList l (a - 1) ++ (intList a b ++ intList (b + 1) r) := by
    have h1 := happ (x := l) (y := a - 1) (z := r) (by omega) (by omega)
    have h2 := happ (x := a) (y := b) (z := r) (by omega) hb
    rw [show a - 1 + 1 = a by ring, h2] at h1
    exact h1
  rw [e1, List.map_append, List.map_append, List.prod_append, List.prod_append]
  have hA : ((intList l (a - 1)).map
      (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : X))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := mem_intList_iff.1 hk
    have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
    simp [hk']
  have hC : ((intList (b + 1) r).map
      (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : X))).prod = 1 := by
    apply List.prod_eq_one
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
    have := mem_intList_iff.1 hk
    have hk' : ¬(a ≤ k ∧ k ≤ b) := by omega
    simp [hk']
  have hB : (intList a b).map (fun k => if a ≤ k ∧ k ≤ b then f k else (1 : X)) =
      (intList a b).map f := by
    apply List.map_congr_left
    intro k hk
    have := mem_intList_iff.1 hk
    simp [this]
  rw [hA, hC, hB, one_mul, mul_one]

namespace TitsSystem

variable {G : Type u} [Group G] {n : ℕ} (T : TitsSystem G n)

@[expose] def Moves (g : G) (π : ℤ → ℤ) : Prop :=
  ∀ j, (T.U j).map (MulAut.conj g).toMonoidHom = T.U (π j)

theorem Moves.mul {g h : G} {π ρ : ℤ → ℤ} (hg : T.Moves g π) (hh : T.Moves h ρ) :
    T.Moves (g * h) (π ∘ ρ) := by
  intro j
  rw [CFSG.LieType.Steinberg.map_conj_mul, hh j, hg (ρ j)]
  rfl

theorem Moves.conj_mem {g : G} {π : ℤ → ℤ} (hg : T.Moves g π) {j : ℤ} {x : G}
    (hx : x ∈ T.U j) : g * x * g⁻¹ ∈ T.U (π j) := by
  have h : g * x * g⁻¹ ∈ (T.U j).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [hg j] at h

theorem Moves.inv_shift {g : G} {c : ℤ} (hg : T.Moves g (· + c)) :
    T.Moves g⁻¹ (· - c) := by
  intro j
  have h := hg (j - c)
  have h' : (T.U (j - c)).map (MulAut.conj g).toMonoidHom = T.U j := by
    simpa [sub_add_cancel] using h
  simpa using CFSG.LieType.Steinberg.map_conj_inv_of_map_conj h'

theorem Moves.inv_refl {g : G} {c : ℤ} (hg : T.Moves g (c - ·)) :
    T.Moves g⁻¹ (c - ·) := by
  intro j
  have h := hg (c - j)
  have h' : (T.U (c - j)).map (MulAut.conj g).toMonoidHom = T.U j := by
    simpa using h
  simpa using CFSG.LieType.Steinberg.map_conj_inv_of_map_conj h'

theorem Moves.map_win_shift {g : G} {c : ℤ} (hg : T.Moves g (· + c)) (a b : ℤ) :
    (win T.U a b).map (MulAut.conj g).toMonoidHom = win T.U (a + c) (b + c) := by
  simp only [win, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (k + c) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by rw [hg]))
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (k - c) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by simpa [sub_add_cancel] using (hg (k - c)).symm))

theorem Moves.map_win_refl {g : G} {c : ℤ} (hg : T.Moves g (c - ·)) (a b : ℤ) :
    (win T.U a b).map (MulAut.conj g).toMonoidHom = win T.U (c - b) (c - a) := by
  simp only [win, Subgroup.map_iSup]
  apply le_antisymm
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (c - k) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by rw [hg]))
  · refine iSup₂_le fun k hk => ?_
    exact le_iSup₂_of_le (c - k) (by simp only [Set.mem_Icc] at hk ⊢; omega)
      (le_of_eq (by simpa [sub_sub_cancel] using (hg (c - k)).symm))

theorem mem_win_iff_prod {a b : ℤ} (hab : b < a + n) {g : G} :
    g ∈ win T.U a b ↔ ∃ f : ℤ → G,
      (∀ k ∈ intList a b, f k ∈ T.U k) ∧ g = ((intList a b).map f).prod := by
  constructor
  · intro hg
    have hwin : win T.U a b = ⨆ k ∈ intList a b, T.U k := by
      apply le_antisymm
      · refine iSup₂_le fun k hk => ?_
        exact le_iSup₂_of_le k (mem_intList_iff.2 hk) le_rfl
      · refine iSup₂_le fun k hk => ?_
        exact le_iSup₂_of_le k (by
          simpa [Set.mem_Icc] using mem_intList_iff.1 hk) le_rfl
    rw [hwin] at hg
    have hpw : (intList a b).Pairwise (· ≤ ·) := by
      unfold intList
      rw [List.pairwise_map]
      exact List.pairwise_lt_range.imp fun {u v} h => by
        have : (u : ℤ) < v := by exact_mod_cast h
        omega
    obtain ⟨f, hf, hprod⟩ := CFSG.LieType.Steinberg.exists_prod_eq_of_commutator_mem
      (A := T.U) (h := fun k => k) (L := intList a b) (nodup_intList a b)
      hpw (fun i hi j hj hij x hx y hy => by
        have hi' := mem_intList_iff.1 hi
        have hj' := mem_intList_iff.1 hj
        have hmem : ⁅x, y⁆ ∈ ⨆ k ∈ Set.Ioo (min i j) (max i j), T.U k := by
          rcases lt_or_gt_of_ne hij with hlt | hgt
          · have h := T.comm i j hlt (by omega) x hx y hy
            simpa [commutatorElement_def, min_eq_left hlt.le, max_eq_right hlt.le] using h
          · have h := T.comm j i hgt (by omega) y hy x hx
            have hinv := (⨆ k ∈ Set.Ioo j i, T.U k).inv_mem h
            have e : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := (commutatorElement_inv y x).symm
            rw [e]
            simpa [commutatorElement_def, mul_assoc, min_eq_right hgt.le,
              max_eq_left hgt.le] using hinv
        refine SetLike.le_def.mp (iSup₂_le fun k hk => ?_) hmem
        have hk' : min i j < k ∧ k < max i j := hk
        exact le_iSup₂_of_le k (mem_intList_iff.2 ⟨by omega, by omega⟩)
          (le_iSup_of_le (by omega) le_rfl)) g hg
    exact ⟨f, hf, hprod⟩
  · rintro ⟨f, hf, rfl⟩
    exact (win T.U a b).list_prod_mem fun x hx => by
      obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
      exact SetLike.le_def.mp (le_iSup₂_of_le k (by
        simpa [Set.mem_Icc] using mem_intList_iff.1 hk) le_rfl) (hf k hk)

theorem prod_unique {a b : ℤ} (hab : b < a + n) {f g : ℤ → G}
    (hf : ∀ k ∈ intList a b, f k ∈ T.U k)
    (hg : ∀ k ∈ intList a b, g k ∈ T.U k)
    (h : ((intList a b).map f).prod = ((intList a b).map g).prod) :
    ∀ k ∈ intList a b, f k = g k := by
  classical
  intro k hk
  by_cases hle : a ≤ b
  · let F : ℤ → G := fun k => if a ≤ k ∧ k ≤ b then f k else 1
    let G' : ℤ → G := fun k => if a ≤ k ∧ k ≤ b then g k else 1
    have hlist : intList ((a - 1) + 1) ((a - 1) + n) = intList a (a + n - 1) := by
      rw [show (a - 1) + 1 = a by ring, show (a - 1) + n = a + n - 1 by ring]
    have hF : ∀ k ∈ intList ((a - 1) + 1) ((a - 1) + n), F k ∈ T.U k := by
      intro k hk'
      rw [hlist] at hk'
      have hk'' := mem_intList_iff.1 hk'
      by_cases hb : a ≤ k ∧ k ≤ b
      · have := hf k (mem_intList_iff.2 ⟨hb.1, hb.2⟩)
        simpa [F, hb] using this
      · simpa [F, hb] using (T.U k).one_mem
    have hG : ∀ k ∈ intList ((a - 1) + 1) ((a - 1) + n), G' k ∈ T.U k := by
      intro k hk'
      rw [hlist] at hk'
      have hk'' := mem_intList_iff.1 hk'
      by_cases hb : a ≤ k ∧ k ≤ b
      · have := hg k (mem_intList_iff.2 ⟨hb.1, hb.2⟩)
        simpa [G', hb] using this
      · simpa [G', hb] using (T.U k).one_mem
    have hprodF : ((intList ((a - 1) + 1) ((a - 1) + n)).map F).prod =
        ((intList a b).map f).prod := by
      rw [hlist]
      exact prod_pad (l := a) (a := a) (b := b) (r := a + n - 1) (by omega) hle (by omega) f
    have hprodG : ((intList ((a - 1) + 1) ((a - 1) + n)).map G').prod =
        ((intList a b).map g).prod := by
      rw [hlist]
      exact prod_pad (l := a) (a := a) (b := b) (r := a + n - 1) (by omega) hle (by omega) g
    have huniq := T.unique (a - 1) F G' hF hG (by rw [hprodF, hprodG]; exact h)
    have hk'' := mem_intList_iff.1 hk
    have hmem : k ∈ intList ((a - 1) + 1) ((a - 1) + n) := by
      rw [hlist]
      exact mem_intList_iff.2 ⟨hk''.1, by omega⟩
    have := huniq k hmem
    have hk' := mem_intList_iff.1 hk
    simpa [F, G', hk'.1, hk'.2] using this
  · have hk' := mem_intList_iff.1 hk
    omega

theorem mem_win_iff_coord {i a b : ℤ} (ha : i + 1 ≤ a) (hb : b ≤ i + n) {f : ℤ → G}
    (hf : ∀ k ∈ intList (i + 1) (i + n), f k ∈ T.U k) :
    ((intList (i + 1) (i + n)).map f).prod ∈ win T.U a b ↔
      ∀ k ∈ intList (i + 1) (i + n), (k < a ∨ b < k) → f k = 1 := by
  classical
  by_cases hle : a ≤ b
  · constructor
    · intro hmem
      obtain ⟨h, hh, hprod⟩ := (mem_win_iff_prod (T := T) (a := a) (b := b)
        (by omega)).1 hmem
      let F : ℤ → G := fun k => if a ≤ k ∧ k ≤ b then h k else 1
      have hF : ∀ k ∈ intList (i + 1) (i + n), F k ∈ T.U k := by
        intro k hk
        by_cases hk' : a ≤ k ∧ k ≤ b
        · have := hh k (mem_intList_iff.2 ⟨hk'.1, hk'.2⟩)
          simpa [F, hk'] using this
        · simpa [F, hk'] using (T.U k).one_mem
      have hprodF : ((intList (i + 1) (i + n)).map F).prod =
          ((intList a b).map h).prod := by
        exact prod_pad (l := i + 1) (a := a) (b := b) (r := i + n) ha hle hb h
      have huniq := T.unique i f F hf hF (by rw [hprodF, ← hprod])
      intro k hk hkout
      have hmemk : k ∈ intList (i + 1) (i + n) := hk
      have := huniq k hmemk
      have hk' := mem_intList_iff.1 hk
      by_cases hkab : a ≤ k ∧ k ≤ b
      · omega
      · simpa [F, hkab] using this
    · intro hzero
      let F : ℤ → G := fun k => if a ≤ k ∧ k ≤ b then f k else 1
      have hF : ∀ k ∈ intList a b, F k ∈ T.U k := by
        intro k hk
        have hk' := mem_intList_iff.1 hk
        have hki : k ∈ intList (i + 1) (i + n) := mem_intList_iff.2 ⟨by omega, by omega⟩
        simpa [F, hk'.1, hk'.2] using hf k hki
      have hprodF : ((intList (i + 1) (i + n)).map F).prod =
          ((intList a b).map f).prod := by
        exact prod_pad (l := i + 1) (a := a) (b := b) (r := i + n) ha hle hb f
      have hFeq : ((intList (i + 1) (i + n)).map F).prod =
          ((intList (i + 1) (i + n)).map f).prod := by
        apply congrArg List.prod
        apply List.map_congr_left
        intro k hk
        by_cases hkab : a ≤ k ∧ k ≤ b
        · simp [F, hkab]
        · have hkout : k < a ∨ b < k := by omega
          simp [F, hkab, hzero k hk hkout]
      have hf_ab : ∀ k ∈ intList a b, f k ∈ T.U k := by
        intro k hk
        have hk' := mem_intList_iff.1 hk
        exact hf k (mem_intList_iff.2 ⟨by omega, by omega⟩)
      have hmem : ((intList a b).map f).prod ∈ win T.U a b :=
        (mem_win_iff_prod (T := T) (a := a) (b := b) (by omega)).2 ⟨f, hf_ab, rfl⟩
      rw [← hprodF, hFeq] at hmem
      exact hmem
  · constructor
    · intro hmem
      have hbot : win T.U a b = ⊥ := by
        simp [win, show ¬(a ≤ b) by omega]
      rw [hbot] at hmem
      have hprod : ((intList (i + 1) (i + n)).map f).prod = 1 := by
        simpa using hmem
      have huniq := T.unique i f (fun _ => 1) hf (fun k hk => (T.U k).one_mem) (by
        rw [hprod]; simp)
      intro k hk _
      exact huniq k hk
    · intro hzero
      have hzero_all : ∀ k ∈ intList (i + 1) (i + n), f k = 1 := by
        intro k hk
        exact hzero k hk (by omega)
      have hprod : ((intList (i + 1) (i + n)).map f).prod = 1 := by
        apply List.prod_eq_one
        intro x hx
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        exact hzero_all k hk
      rw [hprod]
      exact (win T.U a b).one_mem

theorem win_inf_win {a b c d : ℤ} (h : max b d < min a c + n) :
    win T.U a b ⊓ win T.U c d = win T.U (max a c) (min b d) := by
  classical
  by_cases hleab : a ≤ b
  swap
  · have hbot : win T.U a b = ⊥ := by
      simp [win, show ¬ a ≤ b by omega]
    rw [hbot, bot_inf_eq]
    have hempty : win T.U (max a c) (min b d) = ⊥ := by
      simp [win, show ¬ max a c ≤ min b d by omega]
    rw [hempty]
  by_cases hlecd : c ≤ d
  swap
  · have hbot : win T.U c d = ⊥ := by
      simp [win, show ¬ c ≤ d by omega]
    rw [hbot, inf_bot_eq]
    have hempty : win T.U (max a c) (min b d) = ⊥ := by
      simp [win, show ¬ max a c ≤ min b d by omega]
    rw [hempty]
  apply le_antisymm
  · intro x hx
    have hx1 : x ∈ win T.U a b := hx.1
    have hx2 : x ∈ win T.U c d := hx.2
    have hab : b < a + n := by omega
    have hcd : d < c + n := by omega
    obtain ⟨f, hf, hfx⟩ := (mem_win_iff_prod (T := T) (a := a) (b := b) hab).1 hx1
    obtain ⟨g, hg, hgx⟩ := (mem_win_iff_prod (T := T) (a := c) (b := d) hcd).1 hx2
    let m := min a c
    have hm : m = min a c := rfl
    rw [← hm] at h
    let F : ℤ → G := fun k => if a ≤ k ∧ k ≤ b then f k else 1
    let G' : ℤ → G := fun k => if c ≤ k ∧ k ≤ d then g k else 1
    have hlist : intList ((m - 1) + 1) ((m - 1) + n) = intList m (m + n - 1) := by
      rw [show (m - 1) + 1 = m by ring, show (m - 1) + n = m + n - 1 by ring]
    have hF : ∀ k ∈ intList ((m - 1) + 1) ((m - 1) + n), F k ∈ T.U k := by
      intro k hk
      rw [hlist] at hk
      by_cases hkab : a ≤ k ∧ k ≤ b
      · have hki : k ∈ intList a b := mem_intList_iff.2 ⟨hkab.1, hkab.2⟩
        simpa [F, hkab] using hf k hki
      · simpa [F, hkab] using (T.U k).one_mem
    have hG : ∀ k ∈ intList ((m - 1) + 1) ((m - 1) + n), G' k ∈ T.U k := by
      intro k hk
      rw [hlist] at hk
      by_cases hkcd : c ≤ k ∧ k ≤ d
      · have hki : k ∈ intList c d := mem_intList_iff.2 ⟨hkcd.1, hkcd.2⟩
        simpa [G', hkcd] using hg k hki
      · simpa [G', hkcd] using (T.U k).one_mem
    have hprodF : ((intList ((m - 1) + 1) ((m - 1) + n)).map F).prod =
        ((intList a b).map f).prod := by
      rw [hlist]
      have hmk : m ≤ a := by rw [hm]; exact min_le_left a c
      have hbm : b ≤ m + n - 1 := by
        have := le_max_left b d
        omega
      exact prod_pad (l := m) (a := a) (b := b) (r := m + n - 1) hmk (by omega)
        hbm f
    have hprodG : ((intList ((m - 1) + 1) ((m - 1) + n)).map G').prod =
        ((intList c d).map g).prod := by
      rw [hlist]
      have hmk : m ≤ c := by rw [hm]; exact min_le_right a c
      have hdm : d ≤ m + n - 1 := by
        have := le_max_right b d
        omega
      exact prod_pad (l := m) (a := c) (b := d) (r := m + n - 1) hmk (by omega)
        hdm g
    have hprod : ((intList ((m - 1) + 1) ((m - 1) + n)).map F).prod =
        ((intList ((m - 1) + 1) ((m - 1) + n)).map G').prod := by
      rw [hprodF, hprodG, ← hfx, ← hgx]
    have huniq := T.unique (m - 1) F G' hF hG hprod
    have hzero : ∀ k ∈ intList m (m + n - 1),
        (k < max a c ∨ min b d < k) → F k = 1 := by
      intro k hk hkout
      have hk' := mem_intList_iff.1 hk
      by_cases hkab : a ≤ k ∧ k ≤ b
      · have hkG : G' k = F k := by
          have hmem : k ∈ intList ((m - 1) + 1) ((m - 1) + n) := by
            rw [hlist]; exact hk
          exact (huniq k hmem).symm
        have hknot : ¬(c ≤ k ∧ k ≤ d) := by omega
        have hGone : G' k = 1 := by simp [G', hknot]
        rw [← hkG, hGone]
      · simpa [F, hkab]
    have hF' : ∀ k ∈ intList ((m - 1) + 1) ((m - 1) + n), F k ∈ T.U k := hF
    have hcoord := (mem_win_iff_coord (T := T) (i := m - 1) (a := max a c) (b := min b d)
      (by omega) (by omega) hF').2 (by
        intro k hk hkout
        rw [hlist] at hk
        exact hzero k hk hkout)
    have hFx : ((intList ((m - 1) + 1) ((m - 1) + n)).map F).prod = x := by
      rw [hprodF, ← hfx]
    rwa [hFx] at hcoord
  · intro x hx
    have h1 : win T.U (max a c) (min b d) ≤ win T.U a b := by
      refine iSup₂_le fun k hk => ?_
      have hk' : max a c ≤ k ∧ k ≤ min b d := hk
      exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
    have h2 : win T.U (max a c) (min b d) ≤ win T.U c d := by
      refine iSup₂_le fun k hk => ?_
      have hk' : max a c ≤ k ∧ k ≤ min b d := hk
      exact le_iSup₂_of_le k ⟨by omega, by omega⟩ le_rfl
    exact ⟨h1 hx, h2 hx⟩

theorem U_inf_U {k l : ℤ} (hkl : k ≠ l) (h : |k - l| < n) : T.U k ⊓ T.U l = ⊥ := by
  have hwin : win T.U k k = T.U k := by simp [win]
  have hwin' : win T.U l l = T.U l := by simp [win]
  rw [← hwin, ← hwin']
  rw [win_inf_win (T := T) (a := k) (b := k) (c := l) (d := l) (by
    rw [abs_lt] at h
    rcases le_total k l with hkl' | hkl'
    · rw [max_eq_right hkl', min_eq_left hkl']; omega
    · rw [max_eq_left hkl', min_eq_right hkl']; omega)]
  have hlt : min k l < max k l := by
    rcases lt_or_gt_of_ne hkl with hlt | hlt <;> omega
  simp [win, not_le.2 hlt]

theorem le_normalizer_win {a b : ℤ} (hab : b - a ≤ n - 2) :
    T.U (a - 1) ≤ Subgroup.normalizer (win T.U a b : Set G) ∧
      T.U (b + 1) ≤ Subgroup.normalizer (win T.U a b : Set G) := by
  constructor
  · refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun x hx => ?_
    simp only [win, Subgroup.map_iSup]
    refine iSup₂_le fun k hk => ?_
    have hk' : a ≤ k ∧ k ≤ b := hk
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun y hy => ?_
    have hcomm : ⁅x, y⁆ ∈ win T.U a b := by
      have h := T.comm (a - 1) k (by omega) (by omega) x hx y hy
      refine SetLike.le_def.mp ?_ h
      refine iSup₂_le fun t ht => ?_
      have ht' : a - 1 < t ∧ t < k := ht
      refine le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [hxy]
    exact (win T.U a b).mul_mem hcomm (SetLike.le_def.mp (le_iSup₂_of_le k ⟨hk'.1, hk'.2⟩
      le_rfl) hy)
  · refine CFSG.LieType.Steinberg.le_normalizer_of_map_conj_le fun x hx => ?_
    simp only [win, Subgroup.map_iSup]
    refine iSup₂_le fun k hk => ?_
    have hk' : a ≤ k ∧ k ≤ b := hk
    refine CFSG.LieType.Steinberg.map_conj_le_iff.2 fun y hy => ?_
    have hcomm : ⁅x, y⁆ ∈ win T.U a b := by
      have h := T.comm k (b + 1) (by omega) (by omega) y hy x hx
      have hinv := (⨆ t ∈ Set.Ioo k (b + 1), T.U t).inv_mem h
      have e : ⁅x, y⁆ = ⁅y, x⁆⁻¹ := (commutatorElement_inv y x).symm
      rw [e]
      refine SetLike.le_def.mp ?_ hinv
      refine iSup₂_le fun t ht => ?_
      have ht' : k < t ∧ t < b + 1 := ht
      refine le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
    have hxy : x * y * x⁻¹ = ⁅x, y⁆ * y := by
      simp only [commutatorElement_def]
      group
    rw [hxy]
    exact (win T.U a b).mul_mem hcomm (SetLike.le_def.mp (le_iSup₂_of_le k ⟨hk'.1, hk'.2⟩
      le_rfl) hy)

theorem commutator_mem_win {j a b : ℤ} (hja : j < a) (hab : a ≤ b) (hb : b < j + n)
    {x y : G} (hx : x ∈ T.U j) (hy : y ∈ win T.U a b) :
    ⁅x, y⁆ ∈ win T.U (j + 1) (b - 1) := by
  let M := win T.U (j + 1) (b - 1)
  have hwin : win T.U a b ≤ M ⊔ T.U b := by
    refine iSup₂_le fun k hk => ?_
    have hk' : a ≤ k ∧ k ≤ b := hk
    by_cases hkb : k = b
    · subst hkb
      exact le_sup_right
    · have hmem : k ∈ Set.Icc (j + 1) (b - 1) := ⟨by omega, by omega⟩
      have hle : T.U k ≤ M := by
        change T.U k ≤ win T.U (j + 1) (b - 1)
        exact le_iSup₂_of_le k hmem le_rfl
      exact hle.trans le_sup_left
  have hnormM : T.U j ≤ Subgroup.normalizer (M : Set G) := by
    have h := (le_normalizer_win (T := T) (a := j + 1) (b := b - 1) (by omega)).1
    simpa [M] using h
  have hbnorm : T.U b ≤ Subgroup.normalizer (M : Set G) := by
    have h := (le_normalizer_win (T := T) (a := j + 1) (b := b - 1) (by omega)).2
    simpa [M] using h
  have hsup : ((M ⊔ T.U b : Subgroup G) : Set G) = (M : Set G) * (T.U b : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left M (T.U b) hbnorm
  have hy' : y ∈ ((M ⊔ T.U b : Subgroup G) : Set G) := hwin hy
  rw [hsup, Set.mem_mul] at hy'
  obtain ⟨m, hm, u, hu, rfl⟩ := hy'
  have hxm : ⁅x, m⁆ ∈ M := by
    have hconj : x * m * x⁻¹ ∈ M :=
      (Subgroup.mem_normalizer_iff.mp (hnormM hx) m).1 hm
    have : x * m * x⁻¹ * m⁻¹ ∈ M := M.mul_mem hconj (M.inv_mem hm)
    simpa [commutatorElement_def] using this
  have hxu : ⁅x, u⁆ ∈ M := by
    have h := T.comm j b (by omega) hb x hx u hu
    refine SetLike.le_def.mp ?_ h
    refine iSup₂_le fun t ht => ?_
    have ht' : j < t ∧ t < b := ht
    refine le_iSup₂_of_le t ⟨by omega, by omega⟩ le_rfl
  have hconj : m * ⁅x, u⁆ * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm hxu) (M.inv_mem hm)
  have hformula : ⁅x, m * u⁆ = ⁅x, m⁆ * (m * ⁅x, u⁆ * m⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [hformula]
  exact M.mul_mem hxm hconj

end TitsSystem

end CFSG.GH74.Tits83
