module

public import Mathlib.Data.Set.BooleanAlgebra

public section

namespace CFSG.Geometry.ProjectiveSpaces

universe u

structure ProjectiveSpace (P : Type u) where
  lines : Set (Set P)
  existsUnique_line : ∀ p q : P, p ≠ q → ∃! ℓ, ℓ ∈ lines ∧ p ∈ ℓ ∧ q ∈ ℓ
  exists_three : ∀ ℓ ∈ lines, ∃ a b c : P, a ∈ ℓ ∧ b ∈ ℓ ∧ c ∈ ℓ ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c
  veblen : ∀ a b c d : P, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∀ ℓ₁ ∈ lines, ∀ ℓ₂ ∈ lines, ∀ ℓ₃ ∈ lines, ∀ ℓ₄ ∈ lines,
      a ∈ ℓ₁ → b ∈ ℓ₁ → c ∈ ℓ₂ → d ∈ ℓ₂ → a ∈ ℓ₃ → c ∈ ℓ₃ → b ∈ ℓ₄ → d ∈ ℓ₄ →
      (ℓ₁ ∩ ℓ₂).Nonempty → (ℓ₃ ∩ ℓ₄).Nonempty

namespace ProjectiveSpace

variable {P : Type u} (G : ProjectiveSpace P)

open Classical in
@[expose] noncomputable def line (p q : P) : Set P :=
  if h : p = q then {p} else (G.existsUnique_line p q h).exists.choose

theorem line_spec {p q : P} (h : p ≠ q) :
    G.line p q ∈ G.lines ∧ p ∈ G.line p q ∧ q ∈ G.line p q := by
  rw [line, dite_eq_right h]
  exact (G.existsUnique_line p q h).exists.choose_spec

theorem line_mem_lines {p q : P} (h : p ≠ q) : G.line p q ∈ G.lines := (G.line_spec h).1

theorem left_mem_line (p q : P) : p ∈ G.line p q := by
  by_cases h : p = q
  · rw [line, dite_eq_left h]
    exact Set.mem_singleton p
  · exact (G.line_spec h).2.1

theorem right_mem_line (p q : P) : q ∈ G.line p q := by
  by_cases h : p = q
  · rw [line, dite_eq_left h, h]
    exact Set.mem_singleton q
  · exact (G.line_spec h).2.2

theorem line_self (p : P) : G.line p p = {p} := by
  rw [line, dite_eq_left rfl]

theorem eq_line {ℓ : Set P} (hℓ : ℓ ∈ G.lines) {p q : P} (hpq : p ≠ q) (hp : p ∈ ℓ)
    (hq : q ∈ ℓ) : ℓ = G.line p q :=
  (G.existsUnique_line p q hpq).unique ⟨hℓ, hp, hq⟩ (G.line_spec hpq)

theorem line_comm (p q : P) : G.line p q = G.line q p := by
  by_cases h : p = q
  · rw [h]
  · exact G.eq_line (G.line_mem_lines h) (Ne.symm h) (G.right_mem_line p q)
      (G.left_mem_line p q)

theorem line_eq_line {p q r s : P} (hrs : r ≠ s) (hr : r ∈ G.line p q) (hs : s ∈ G.line p q) :
    G.line r s = G.line p q := by
  by_cases hpq : p = q
  · rw [hpq, line_self] at hr hs
    exact absurd (hr.trans hs.symm) hrs
  · exact (G.eq_line (G.line_mem_lines hpq) hrs hr hs).symm

theorem line_eq_of_mem {p q r : P} (hr : r ∈ G.line p q) (hrp : r ≠ p) :
    G.line p r = G.line p q :=
  G.line_eq_line (Ne.symm hrp) (G.left_mem_line p q) hr

theorem eq_of_mem_of_mem {ℓ m : Set P} (hℓ : ℓ ∈ G.lines) (hm : m ∈ G.lines) (hℓm : ℓ ≠ m)
    {x y : P} (hxℓ : x ∈ ℓ) (hxm : x ∈ m) (hyℓ : y ∈ ℓ) (hym : y ∈ m) : x = y := by
  by_contra hxy
  exact hℓm ((G.eq_line hℓ hxy hxℓ hyℓ).trans (G.eq_line hm hxy hxm hym).symm)

theorem exists_mem_line_ne {p q : P} (hpq : p ≠ q) :
    ∃ r ∈ G.line p q, r ≠ p ∧ r ≠ q := by
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := G.exists_three _ (G.line_mem_lines hpq)
  by_cases hap : a = p
  · by_cases hbq : b = q
    · exact ⟨c, hc, fun h => hac (hap.trans h.symm), fun h => hbc (hbq.trans h.symm)⟩
    · exact ⟨b, hb, fun h => hab (hap.trans h.symm), hbq⟩
  · by_cases haq : a = q
    · by_cases hbp : b = p
      · exact ⟨c, hc, fun h => hbc (hbp.trans h.symm), fun h => hac (haq.trans h.symm)⟩
      · exact ⟨b, hb, hbp, fun h => hab (haq.trans h.symm)⟩
    · exact ⟨a, ha, hap, haq⟩

theorem veblen_line {a b c d : P} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (h : (G.line a b ∩ G.line c d).Nonempty) :
    (G.line a c ∩ G.line b d).Nonempty :=
  G.veblen a b c d hab hac had hbc hbd hcd _ (G.line_mem_lines hab) _ (G.line_mem_lines hcd) _
    (G.line_mem_lines hac) _ (G.line_mem_lines hbd) (G.left_mem_line a b)
    (G.right_mem_line a b) (G.left_mem_line c d) (G.right_mem_line c d) (G.left_mem_line a c)
    (G.right_mem_line a c) (G.left_mem_line b d) (G.right_mem_line b d) h

@[expose] def Collinear (x y z : P) : Prop := x = y ∨ z ∈ G.line x y

theorem collinear_iff_of_ne {x y z : P} (hxy : x ≠ y) : G.Collinear x y z ↔ z ∈ G.line x y :=
  ⟨fun h => h.resolve_left hxy, Or.inr⟩

variable {G} in
theorem Collinear.swap12 {x y z : P} (h : G.Collinear x y z) : G.Collinear y x z := by
  rcases h with h | h
  · exact Or.inl h.symm
  · exact Or.inr (G.line_comm x y ▸ h)

variable {G} in
theorem Collinear.swap23 {x y z : P} (h : G.Collinear x y z) : G.Collinear x z y := by
  rcases h with rfl | h
  · exact Or.inr (G.left_mem_line x z)
  · by_cases hzx : z = x
    · exact Or.inl hzx.symm
    · exact Or.inr (G.line_eq_of_mem h hzx ▸ G.right_mem_line x y)

variable {G} in
theorem Collinear.rotate {x y z : P} (h : G.Collinear x y z) : G.Collinear y z x :=
  h.swap12.swap23

theorem collinear_right (x y : P) : G.Collinear x y y := Or.inr (G.right_mem_line x y)

theorem collinear_middle (x y : P) : G.Collinear x y x := Or.inr (G.left_mem_line x y)

theorem collinear_of_mem_line {p q x y z : P} (hx : x ∈ G.line p q) (hy : y ∈ G.line p q)
    (hz : z ∈ G.line p q) : G.Collinear x y z := by
  by_cases hxy : x = y
  · exact Or.inl hxy
  · exact Or.inr (G.line_eq_line hxy hx hy ▸ hz)

theorem ne_of_not_collinear {x y z : P} (h : ¬ G.Collinear x y z) :
    x ≠ y ∧ x ≠ z ∧ y ≠ z :=
  ⟨fun hxy => h (Or.inl hxy), fun hxz => h (hxz ▸ G.collinear_middle x y),
    fun hyz => h (hyz ▸ G.collinear_right x y)⟩

@[expose] def IsSubspace (S : Set P) : Prop := ∀ p ∈ S, ∀ q ∈ S, p ≠ q → G.line p q ⊆ S

variable {G} in
theorem IsSubspace.line_subset {S : Set P} (hS : G.IsSubspace S) {p q : P} (hp : p ∈ S)
    (hq : q ∈ S) : G.line p q ⊆ S := by
  by_cases hpq : p = q
  · rw [hpq, line_self]
    exact Set.singleton_subset_iff.2 hq
  · exact hS p hp q hq hpq

theorem isSubspace_line (p q : P) : G.IsSubspace (G.line p q) := fun _ hx _ hy hxy =>
  (G.line_eq_line hxy hx hy).le

theorem isSubspace_univ : G.IsSubspace (Set.univ : Set P) := fun _ _ _ _ _ => Set.subset_univ _

variable {G} in
theorem IsSubspace.inter {S T : Set P} (hS : G.IsSubspace S) (hT : G.IsSubspace T) :
    G.IsSubspace (S ∩ T) := fun p hp q hq hpq =>
  Set.subset_inter (hS p hp.1 q hq.1 hpq) (hT p hp.2 q hq.2 hpq)

@[expose] def join (S : Set P) (p : P) : Set P := ⋃ s ∈ S, G.line p s

theorem mem_join {S : Set P} {p x : P} : x ∈ G.join S p ↔ ∃ s ∈ S, x ∈ G.line p s := by
  simp only [join, Set.mem_iUnion, exists_prop]

theorem subset_join (S : Set P) (p : P) : S ⊆ G.join S p := fun s hs =>
  G.mem_join.2 ⟨s, hs, G.right_mem_line p s⟩

theorem mem_join_self {S : Set P} (hS : S.Nonempty) (p : P) : p ∈ G.join S p := by
  obtain ⟨s, hs⟩ := hS
  exact G.mem_join.2 ⟨s, hs, G.left_mem_line p s⟩

theorem join_subset {S T : Set P} (hT : G.IsSubspace T) (hST : S ⊆ T) {p : P} (hp : p ∈ T) :
    G.join S p ⊆ T := by
  intro x hx
  obtain ⟨s, hs, hx⟩ := G.mem_join.1 hx
  exact hT.line_subset hp (hST hs) hx

theorem isSubspace_join {S : Set P} (hS : G.IsSubspace S) {p : P} (hp : p ∉ S) :
    G.IsSubspace (G.join S p) := by
  intro x hx y hy hxy z hz
  rw [mem_join] at hx hy ⊢
  obtain ⟨s₁, hs₁, hx⟩ := hx
  obtain ⟨s₂, hs₂, hy⟩ := hy
  have hps₁ : p ≠ s₁ := fun h => hp (h ▸ hs₁)
  have hps₂ : p ≠ s₂ := fun h => hp (h ▸ hs₂)
  by_cases hzx : z = x
  · exact ⟨s₁, hs₁, hzx ▸ hx⟩
  by_cases hzp : z = p
  · exact ⟨s₁, hs₁, hzp ▸ G.left_mem_line p s₁⟩
  by_cases hzS : z ∈ S
  · exact ⟨z, hzS, G.right_mem_line p z⟩
  by_cases hxp : x = p
  · subst hxp
    refine ⟨s₂, hs₂, ?_⟩
    rw [← G.line_eq_of_mem hy (Ne.symm hxy)]
    exact hz
  by_cases hyp : y = p
  · subst hyp
    refine ⟨s₁, hs₁, ?_⟩
    rw [G.line_comm] at hz
    rw [← G.line_eq_of_mem hx hxp]
    exact hz
  by_cases hs : s₁ = s₂
  · subst hs
    refine ⟨s₁, hs₁, ?_⟩
    rw [← G.line_eq_line hxy hx hy]
    exact hz
  have hzs₂ : z ≠ s₂ := fun h => hzS (h ▸ hs₂)
  have hzs₁ : z ≠ s₁ := fun h => hzS (h ▸ hs₁)
  have hlx : G.line p x = G.line p s₁ := G.line_eq_of_mem hx hxp
  have hA : (G.line z s₂ ∩ G.line x p).Nonempty := by
    by_cases hxs₂ : x = s₂
    · exact ⟨s₂, G.right_mem_line z s₂, hxs₂ ▸ G.left_mem_line x p⟩
    refine G.veblen_line hzx hzs₂ hzp hxs₂ hxp (Ne.symm hps₂) ⟨y, ?_, ?_⟩
    · have h1 : G.line x z = G.line x y := G.line_eq_of_mem hz hzx
      rw [G.line_comm, h1]
      exact G.right_mem_line x y
    · rw [G.line_comm]
      exact hy
  have hB : (G.line p z ∩ G.line s₁ s₂).Nonempty := by
    refine G.veblen_line hps₁ (Ne.symm hzp) hps₂ (Ne.symm hzs₁) hs hzs₂ ?_
    obtain ⟨u, hu1, hu2⟩ := hA
    refine ⟨u, ?_, hu1⟩
    rw [← hlx, G.line_comm]
    exact hu2
  obtain ⟨w, hw1, hw2⟩ := hB
  have hwS : w ∈ S := hS.line_subset hs₁ hs₂ hw2
  have hwp : w ≠ p := fun h => hp (h ▸ hwS)
  refine ⟨w, hwS, ?_⟩
  rw [G.line_eq_of_mem hw1 hwp]
  exact G.right_mem_line p z

@[expose] def plane (x y z : P) : Set P := G.join (G.line x y) z

theorem isSubspace_plane {x y z : P} (h : ¬ G.Collinear x y z) :
    G.IsSubspace (G.plane x y z) :=
  G.isSubspace_join (G.isSubspace_line x y) fun hz =>
    h (Or.inr hz)

theorem left_mem_plane (x y z : P) : x ∈ G.plane x y z :=
  G.subset_join _ z (G.left_mem_line x y)

theorem middle_mem_plane (x y z : P) : y ∈ G.plane x y z :=
  G.subset_join _ z (G.right_mem_line x y)

theorem right_mem_plane (x y z : P) : z ∈ G.plane x y z :=
  G.mem_join_self ⟨x, G.left_mem_line x y⟩ z

theorem line_subset_plane (x y z : P) : G.line x y ⊆ G.plane x y z := G.subset_join _ z

theorem plane_subset {T : Set P} (hT : G.IsSubspace T) {x y z : P} (hx : x ∈ T) (hy : y ∈ T)
    (hz : z ∈ T) : G.plane x y z ⊆ T :=
  G.join_subset hT (hT.line_subset hx hy) hz

theorem inter_line_nonempty_of_mem_plane {x y z : P} (h : ¬ G.Collinear x y z) {u v : P}
    (hu : u ∈ G.plane x y z) (hv : v ∈ G.plane x y z) (huv : u ≠ v) :
    (G.line u v ∩ G.line x y).Nonempty := by
  obtain ⟨s₁, hs₁, hu⟩ := G.mem_join.1 hu
  obtain ⟨s₂, hs₂, hv⟩ := G.mem_join.1 hv
  have hz : z ∉ G.line x y := fun hz => h (Or.inr hz)
  have hzs₁ : z ≠ s₁ := fun e => hz (e ▸ hs₁)
  have hzs₂ : z ≠ s₂ := fun e => hz (e ▸ hs₂)
  by_cases hul : u ∈ G.line x y
  · exact ⟨u, G.left_mem_line u v, hul⟩
  by_cases hvl : v ∈ G.line x y
  · exact ⟨v, G.right_mem_line u v, hvl⟩
  by_cases huz : u = z
  · have hvz : v ≠ z := fun e => huv (huz.trans e.symm)
    refine ⟨s₂, ?_, hs₂⟩
    rw [huz, G.line_eq_of_mem hv hvz]
    exact G.right_mem_line z s₂
  by_cases hvz : v = z
  · have huz' : u ≠ z := huz
    refine ⟨s₁, ?_, hs₁⟩
    rw [hvz, G.line_comm, G.line_eq_of_mem hu huz']
    exact G.right_mem_line z s₁
  by_cases hs : s₁ = s₂
  · subst hs
    refine ⟨s₁, ?_, hs₁⟩
    rw [G.line_eq_line huv hu hv]
    exact G.right_mem_line z s₁
  have hus₁ : u ≠ s₁ := fun e => hul (e ▸ hs₁)
  have hus₂ : u ≠ s₂ := fun e => hul (e ▸ hs₂)
  have hvs₁ : v ≠ s₁ := fun e => hvl (e ▸ hs₁)
  have hvs₂ : v ≠ s₂ := fun e => hvl (e ▸ hs₂)
  have hz1 : z ∈ G.line u s₁ := by
    rw [G.line_eq_line hus₁ hu (G.right_mem_line z s₁)]
    exact G.left_mem_line z s₁
  have hz2 : z ∈ G.line v s₂ := by
    rw [G.line_eq_line hvs₂ hv (G.right_mem_line z s₂)]
    exact G.left_mem_line z s₂
  obtain ⟨w, hw1, hw2⟩ := G.veblen_line hus₁ huv hus₂ (Ne.symm hvs₁) hs hvs₂ ⟨z, hz1, hz2⟩
  exact ⟨w, hw1, G.line_eq_line hs hs₁ hs₂ ▸ hw2⟩

theorem inter_nonempty_of_mem_plane {x y z : P} (h : ¬ G.Collinear x y z) {u v u' v' : P}
    (hu : u ∈ G.plane x y z) (hv : v ∈ G.plane x y z) (hu' : u' ∈ G.plane x y z)
    (hv' : v' ∈ G.plane x y z) (huv : u ≠ v) (huv' : u' ≠ v') :
    (G.line u v ∩ G.line u' v').Nonempty := by
  have hxy : x ≠ y := (G.ne_of_not_collinear h).1
  have hπ := G.isSubspace_plane h
  obtain ⟨a, ha1, ha2⟩ := G.inter_line_nonempty_of_mem_plane h hu hv huv
  obtain ⟨a', ha1', ha2'⟩ := G.inter_line_nonempty_of_mem_plane h hu' hv' huv'
  by_cases haa : a = a'
  · exact ⟨a, ha1, haa ▸ ha1'⟩
  have hla : G.line u v ≠ G.line x y → ∀ t ∈ G.line u v, t ∈ G.line x y → t = a :=
    fun hne t ht1 ht2 => G.eq_of_mem_of_mem (G.line_mem_lines huv) (G.line_mem_lines hxy) hne
      ht1 ht2 ha1 ha2
  have hla' : G.line u' v' ≠ G.line x y → ∀ t ∈ G.line u' v', t ∈ G.line x y → t = a' :=
    fun hne t ht1 ht2 => G.eq_of_mem_of_mem (G.line_mem_lines huv') (G.line_mem_lines hxy) hne
      ht1 ht2 ha1' ha2'
  by_cases hm : G.line u v = G.line x y
  · exact ⟨a', hm ▸ ha2', ha1'⟩
  by_cases hm' : G.line u' v' = G.line x y
  · exact ⟨a, ha1, hm' ▸ ha2⟩
  obtain ⟨b, hb, hba⟩ : ∃ b ∈ G.line u v, b ≠ a := by
    by_cases hua : u = a
    · exact ⟨v, G.right_mem_line u v, fun e => huv (hua.trans e.symm)⟩
    · exact ⟨u, G.left_mem_line u v, hua⟩
  obtain ⟨b', hb', hba'⟩ : ∃ b' ∈ G.line u' v', b' ≠ a' := by
    by_cases hua : u' = a'
    · exact ⟨v', G.right_mem_line u' v', fun e => huv' (hua.trans e.symm)⟩
    · exact ⟨u', G.left_mem_line u' v', hua⟩
  have hbl : b ∉ G.line x y := fun hb2 => hba (hla hm b hb hb2)
  have hbl' : b' ∉ G.line x y := fun hb2 => hba' (hla' hm' b' hb' hb2)
  by_cases hbb : b = b'
  · exact ⟨b, hb, hbb ▸ hb'⟩
  have hbπ : b ∈ G.plane x y z := hπ.line_subset hu hv hb
  have hbπ' : b' ∈ G.plane x y z := hπ.line_subset hu' hv' hb'
  obtain ⟨t, ht1, ht2⟩ := G.inter_line_nonempty_of_mem_plane h hbπ hbπ' hbb
  have hab : a ≠ b' := fun e => hbl' (e ▸ ha2)
  have hba2 : b ≠ a' := fun e => hbl (e ▸ ha2')
  obtain ⟨w, hw1, hw2⟩ := G.veblen_line hbb hba hba2 (Ne.symm hab) hba' haa
    ⟨t, ht1, G.line_eq_line haa ha2 ha2' ▸ ht2⟩
  refine ⟨w, ?_, ?_⟩
  · rw [← G.line_eq_line (Ne.symm hba) ha1 hb, G.line_comm]
    exact hw1
  · rw [← G.line_eq_line (Ne.symm hba') ha1' hb', G.line_comm]
    exact hw2

theorem plane_eq_of_mem {x y z : P} (h : ¬ G.Collinear x y z) {a b c : P}
    (ha : a ∈ G.plane x y z) (hb : b ∈ G.plane x y z) (hc : c ∈ G.plane x y z)
    (habc : ¬ G.Collinear a b c) : G.plane a b c = G.plane x y z := by
  have hπ := G.isSubspace_plane h
  refine (G.plane_subset hπ ha hb hc).antisymm fun w hw => ?_
  have hab : a ≠ b := (G.ne_of_not_collinear habc).1
  have hc' : c ∉ G.line a b := fun e => habc (Or.inr e)
  by_cases hwc : w = c
  · rw [hwc]
    exact G.right_mem_plane a b c
  obtain ⟨s, hs1, hs2⟩ := G.inter_nonempty_of_mem_plane h hc hw ha hb (Ne.symm hwc) hab
  have hsc : s ≠ c := fun e => hc' (e ▸ hs2)
  refine G.mem_join.2 ⟨s, hs2, ?_⟩
  rw [G.line_eq_of_mem hs1 hsc]
  exact G.right_mem_line c w

theorem collinear_of_mem_plane_of_mem_plane {x y z x' y' z' : P} (h : ¬ G.Collinear x y z)
    (h' : ¬ G.Collinear x' y' z') (hne : G.plane x y z ≠ G.plane x' y' z') {a b c : P}
    (ha : a ∈ G.plane x y z) (hb : b ∈ G.plane x y z) (hc : c ∈ G.plane x y z)
    (ha' : a ∈ G.plane x' y' z') (hb' : b ∈ G.plane x' y' z') (hc' : c ∈ G.plane x' y' z') :
    G.Collinear a b c := by
  by_contra habc
  exact hne ((G.plane_eq_of_mem h ha hb hc habc).symm.trans (G.plane_eq_of_mem h' ha' hb' hc' habc))

end ProjectiveSpace

end CFSG.Geometry.ProjectiveSpaces
