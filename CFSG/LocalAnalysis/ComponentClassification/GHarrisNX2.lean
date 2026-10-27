module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisNX1
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSigCtl

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG CFSG.Open Subgroup SCert CFSG.ABGLocalTools

theorem mz2_sq : ∀ m : Multiplicative (ZMod 2), m * m = 1 := by decide

theorem mz2_pow_odd (m : Multiplicative (ZMod 2)) {n : ℕ} (hn : ¬ 2 ∣ n) : m ^ n = m := by
  obtain ⟨k, rfl⟩ := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hn)
  rw [pow_succ, pow_mul, sq, mz2_sq, one_pow, one_mul]

theorem transfer_inv_eq {K : Type*} [Group K] [Finite K] {X : Subgroup K}
    (ϕ : X →* Multiplicative (ZMod 2)) (hodd : ¬ 2 ∣ X.index) {w : K} (hw : w ∈ X)
    (hw2 : w * w = 1)
    (hconj : ∀ a : K, ∀ ha : a⁻¹ * w * a ∈ X, ϕ ⟨a⁻¹ * w * a, ha⟩ = ϕ ⟨w, hw⟩) :
    ϕ.transfer w = ϕ ⟨w, hw⟩ := by
  rw [CFSG.Quasithin.transfer_eq_pow_of_forall ϕ hw ?_]
  · exact mz2_pow_odd _ hodd
  intro k a ha
  rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
  · have h1 : w ^ (j + j) = 1 := by rw [← two_mul, pow_mul, sq, hw2, one_pow]
    have e1 : (⟨a⁻¹ * w ^ (j + j) * a, ha⟩ : X) = 1 :=
      Subtype.ext (show a⁻¹ * w ^ (j + j) * a = 1 by rw [h1, mul_one, inv_mul_cancel])
    have e2 : (⟨w ^ (j + j), X.pow_mem hw (j + j)⟩ : X) = 1 := Subtype.ext h1
    rw [e1, e2]
  · have h1 : w ^ (2 * j + 1) = w := by rw [pow_succ, pow_mul, sq, hw2, one_pow, one_mul]
    have e1 : (⟨a⁻¹ * w ^ (2 * j + 1) * a, ha⟩ : X) = ⟨a⁻¹ * w * a, by rwa [h1] at ha⟩ :=
      Subtype.ext (show a⁻¹ * w ^ (2 * j + 1) * a = a⁻¹ * w * a by rw [h1])
    have e2 : (⟨w ^ (2 * j + 1), X.pow_mem hw (2 * j + 1)⟩ : X) = ⟨w, hw⟩ := Subtype.ext h1
    rw [e1, e2]
    exact hconj a _

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

abbrev ZC (w : G) : Prop := ∃ g : G, g⁻¹ * D.z * g = w

abbrev XC (w : G) : Prop := ∃ g : G, g⁻¹ * D.x * g = w

theorem not_ZC_XC {w : G} (hz : D.ZC w) (hx : D.XC w) : False := by
  obtain ⟨g, hg⟩ := hz
  obtain ⟨h, hh⟩ := hx
  exact D.not_conj_x_z ⟨h * g⁻¹, by rw [show (h * g⁻¹)⁻¹ * D.x * (h * g⁻¹) =
    g * (h⁻¹ * D.x * h) * g⁻¹ by group, hh, ← hg]; group⟩

omit [Finite G]
  in
theorem conj_class {c w : G} (h : ∃ g : G, g⁻¹ * c * g = w) (a : G) :
    ∃ g : G, g⁻¹ * c * g = a⁻¹ * w * a := by
  obtain ⟨g, rfl⟩ := h
  exact ⟨g * a, by group⟩

omit [Finite G]
  in
theorem conj_of_conj_rep {c : G} {s r : SE} (hr : ∃ g : G, g⁻¹ * c * g = D.toG r)
    {k : SE} (hk : k⁻¹ * s * k = r) : ∃ g : G, g⁻¹ * c * g = D.toG s := by
  obtain ⟨g, hg⟩ := hr
  refine ⟨g * (D.toG k)⁻¹, ?_⟩
  rw [show (g * (D.toG k)⁻¹)⁻¹ * c * (g * (D.toG k)⁻¹) = D.toG k * (g⁻¹ * c * g) * (D.toG k)⁻¹
    by group, hg, ← hk, map_mul, map_mul, map_inv]
  group

omit [Finite G]
  in
theorem fusN_conj {i j : Fin 9} (h : D.FusN i j) :
    ∃ g : G, g⁻¹ * D.toG (SE.invRep j) * g = D.toG (SE.invRep i) := by
  obtain ⟨g, hg⟩ := h
  have hi : Fin.ofNat 9 i.val = i := Fin.ext (by simp)
  have hj : Fin.ofNat 9 j.val = j := Fin.ext (by simp)
  rw [hi, hj] at hg
  exact ⟨g⁻¹, by rw [← hg]; group⟩

omit [Finite G]
  in
theorem ZC_of_ZrepsA (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i)) {s : SE}
    (h : ∃ k : SE, k⁻¹ * s * k ∈ SE.ZrepsA) : D.ZC (D.toG s) := by
  obtain ⟨k, hk⟩ := h
  have hz : ∀ i : Fin 9, D.FusN i 0 → ∃ g : G, g⁻¹ * D.z * g = D.toG (SE.invRep i) :=
    fun i hi => by rw [← D.toG_invRep_zero]; exact D.fusN_conj (j := 0) hi
  simp only [SE.ZrepsA, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk | hk | hk | hk | hk
  · exact D.conj_of_conj_rep ⟨1, by rw [D.toG_invRep_zero]; group⟩ hk
  · exact D.conj_of_conj_rep (hz 1 (hP 1 (by decide))) hk
  · exact D.conj_of_conj_rep (hz 2 (hP 2 (by decide))) hk
  · exact D.conj_of_conj_rep (hz 3 (hP 3 (by decide))) hk
  · exact D.conj_of_conj_rep (hz 4 (hP 4 (by decide))) hk
  · exact D.conj_of_conj_rep (hz 7 (hP 7 (by decide))) hk

omit [Finite G]
  in
theorem XC_of_Xreps (h6 : D.FusN 6 5) (h8 : D.FusN 8 5) {s : SE}
    (h : ∃ k : SE, k⁻¹ * s * k ∈ SE.Xreps) : D.XC (D.toG s) := by
  obtain ⟨k, hk⟩ := h
  simp only [SE.Xreps, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk | hk
  · exact D.conj_of_conj_rep ⟨1, by rw [show SE.invRep 5 = SE.gen 6 by decide]; group⟩ hk
  · exact D.conj_of_conj_rep (D.fusN_conj (i := 6) (j := 5) h6) hk
  · exact D.conj_of_conj_rep (D.fusN_conj (i := 8) (j := 5) h8) hk


omit [Finite G]
  in
theorem mem_Xlist_of_toG {s : SE} (hs : D.toG s ∈ D.X) : s ∈ SE.Xlist := by
  have h := D.eS_mem_Xlist hs
  rwa [D.eS_toG] at h

omit [Finite G]
  in
theorem X_inv_type (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s : SE} (hs : D.toG s ∈ D.X) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    (s ∈ SE.LZX ∧ D.ZC (D.toG s) ∧ D.XC (D.toG s * D.x)) ∨ s = SE.gen 6 ∨
      (s ∈ SE.LXZ ∧ D.XC (D.toG s) ∧ D.ZC (D.toG s * D.x)) ∨
      (s ∈ SE.LXX ∧ D.XC (D.toG s) ∧ D.XC (D.toG s * D.x)) := by
  have h8 : D.FusN 8 5 := hP 8 (by decide)
  have hx : D.toG s * D.x = D.toG (s * SE.gen 6) := by rw [map_mul]
  rcases SE.inv_X_cases s (D.mem_Xlist_of_toG hs) hs2 hs1 with h | h | h | h
  · obtain ⟨h1, h2⟩ := SE.LZX_spec s h
    exact Or.inl ⟨h, D.ZC_of_ZrepsA hP h1, by rw [hx]; exact D.XC_of_Xreps h6 h8 h2⟩
  · exact Or.inr (Or.inl h)
  · obtain ⟨h1, h2⟩ := SE.LXZ_spec s h
    exact Or.inr (Or.inr (Or.inl ⟨h, D.XC_of_Xreps h6 h8 h1, by
      rw [hx]; exact D.ZC_of_ZrepsA hP h2⟩))
  · obtain ⟨h1, h2⟩ := SE.LXX_spec s h
    exact Or.inr (Or.inr (Or.inr ⟨h, D.XC_of_Xreps h6 h8 h1, by
      rw [hx]; exact D.XC_of_Xreps h6 h8 h2⟩))

theorem f_conj (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s s' : SE} (hs : D.toG s ∈ D.X) (hs' : D.toG s' ∈ D.X)
    (hs2 : s * s = 1) (hs1 : s ≠ 1) {a : G} (ha : a ∈ centralizer ({D.x} : Set G))
    (h : a⁻¹ * D.toG s * a = D.toG s') :
    SE.fB s' = SE.fB s ∧ (s ∉ SE.LXX → SE.fA s' = SE.fA s) := by
  have hax : a⁻¹ * D.x * a = D.x := by
    have := mem_centralizer_singleton_iff.mp ha
    calc a⁻¹ * D.x * a = a⁻¹ * (D.x * a) := by group
      _ = a⁻¹ * (a * D.x) := by rw [this]
      _ = D.x := by group
  have hs'2 : s' * s' = 1 := D.toG_injective (by
    rw [map_mul, ← h, show a⁻¹ * D.toG s * a * (a⁻¹ * D.toG s * a) = a⁻¹ * D.toG (s * s) * a by
      rw [map_mul]; group, hs2, map_one]
    group)
  have hs'1 : s' ≠ 1 := fun h1 => hs1 (D.toG_injective (by
    have : a⁻¹ * D.toG s * a = 1 := by rw [h, h1, map_one]
    rw [map_one]
    calc D.toG s = a * (a⁻¹ * D.toG s * a) * a⁻¹ := by group
      _ = 1 := by rw [this]; group))
  have hwx : a⁻¹ * (D.toG s * D.x) * a = D.toG s' * D.x := by
    rw [show a⁻¹ * (D.toG s * D.x) * a = a⁻¹ * D.toG s * a * (a⁻¹ * D.x * a) by group, h, hax]
  have hcl : ∀ {c w : G}, (∃ g : G, g⁻¹ * c * g = w) → ∃ g : G, g⁻¹ * c * g = a⁻¹ * w * a :=
    fun hc => conj_class hc a
  have hx6 : D.toG (SE.gen 6) = D.x := rfl
  have hX1 : s' = SE.gen 6 → s = SE.gen 6 := fun h2 => by
    subst h2
    apply D.toG_injective
    calc D.toG s = a * (a⁻¹ * D.toG s * a) * a⁻¹ := by group
      _ = a * D.x * a⁻¹ := by rw [h]
      _ = a * (a⁻¹ * D.x * a) * a⁻¹ := by rw [hax]
      _ = D.x := by group
  have hX1' : s = SE.gen 6 → s' = SE.gen 6 := fun h1 => by
    subst h1
    apply D.toG_injective
    rw [← h, hx6, hax]
  rcases D.X_inv_type hP h6 hs hs2 hs1 with ⟨h1, z1, x1⟩ | h1 | ⟨h1, x1, z1⟩ | ⟨h1, x1, x1'⟩ <;>
    rcases D.X_inv_type hP h6 hs' hs'2 hs'1 with ⟨h2, z2, x2⟩ | h2 | ⟨h2, x2, z2⟩ | ⟨h2, x2, x2'⟩
  · exact ⟨by rw [(SE.f_LZX s' h2).2, (SE.f_LZX s h1).2],
      fun _ => by rw [(SE.f_LZX s' h2).1, (SE.f_LZX s h1).1]⟩
  · rw [hX1 h2] at h1
    exact absurd h1 (by decide)
  · exact (D.not_ZC_XC (by rw [← h]; exact hcl z1) x2).elim
  · exact (D.not_ZC_XC (by rw [← h]; exact hcl z1) x2).elim
  · rw [hX1' h1] at h2
    exact absurd h2 (by decide)
  · subst h1 h2; exact ⟨rfl, fun _ => rfl⟩
  · rw [hX1' h1] at h2
    exact absurd h2 (by decide)
  · rw [hX1' h1] at h2
    exact absurd h2 (by decide)
  · exact (D.not_ZC_XC z2 (by rw [← h]; exact hcl x1)).elim
  · rw [hX1 h2] at h1
    exact absurd h1 (by decide)
  · exact ⟨by rw [(SE.f_LXZ s' h2).2, (SE.f_LXZ s h1).2],
      fun _ => by rw [(SE.f_LXZ s' h2).1, (SE.f_LXZ s h1).1]⟩
  · exact (D.not_ZC_XC (by rw [← hwx]; exact hcl z1) x2').elim
  · exact (D.not_ZC_XC z2 (by rw [← h]; exact hcl x1)).elim
  · rw [hX1 h2] at h1
    exact absurd h1 (by decide)
  · exact (D.not_ZC_XC z2 (by rw [← hwx]; exact hcl x1')).elim
  · exact ⟨by rw [SE.f_LXX s' h2, SE.f_LXX s h1], fun h' => absurd h1 h'⟩

omit [Finite G]
  in
theorem X_le_N : D.X ≤ centralizer ({D.x} : Set G) := inf_le_right

abbrev Xn : Subgroup ↥(centralizer ({D.x} : Set G)) :=
  D.X.subgroupOf (centralizer ({D.x} : Set G))

theorem not_two_dvd_index_Xn : ¬ 2 ∣ D.Xn.index := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isSylowOf_iff.mp D.isSylowOf_X).2.2

abbrev phiAn : D.Xn →* Multiplicative (ZMod 2) :=
  D.phiA.comp (subgroupOfEquivOfLe D.X_le_N).toMonoidHom

abbrev phiBn : D.Xn →* Multiplicative (ZMod 2) :=
  D.phiB.comp (subgroupOfEquivOfLe D.X_le_N).toMonoidHom

abbrev VA : ↥(centralizer ({D.x} : Set G)) →* Multiplicative (ZMod 2) := D.phiAn.transfer

abbrev VB : ↥(centralizer ({D.x} : Set G)) →* Multiplicative (ZMod 2) := D.phiBn.transfer

omit [Finite G]
  in
theorem exists_model_conj {s : SE} (hs : D.toG s ∈ D.X) (a : ↥(centralizer ({D.x} : Set G)))
    (ha : a⁻¹ * ⟨D.toG s, D.X_le_N hs⟩ * a ∈ D.Xn) :
    ∃ s' : SE, ∃ hs' : D.toG s' ∈ D.X,
      (⟨((a⁻¹ * ⟨D.toG s, D.X_le_N hs⟩ * a : ↥(centralizer ({D.x} : Set G))) : G),
        mem_subgroupOf.mp ha⟩ : ↥D.X) = ⟨D.toG s', hs'⟩ ∧
      (a : G)⁻¹ * D.toG s * a = D.toG s' := by
  have haX := mem_subgroupOf.mp ha
  obtain ⟨s', hs'⟩ := D.exists_toG (mem_inf.mp haX).1
  refine ⟨s', hs' ▸ haX, Subtype.ext hs'.symm, ?_⟩
  rw [hs']
  rfl

theorem VA_toG (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s : SE} (hs : D.toG s ∈ D.X) (hs2 : s * s = 1) (hs1 : s ≠ 1)
    (hXX : s ∉ SE.LXX) :
    D.VA ⟨D.toG s, D.X_le_N hs⟩ = Multiplicative.ofAdd (SE.fA s) := by
  have hw : (⟨D.toG s, D.X_le_N hs⟩ : ↥(centralizer ({D.x} : Set G))) ∈ D.Xn :=
    mem_subgroupOf.mpr hs
  refine (transfer_inv_eq D.phiAn D.not_two_dvd_index_Xn hw
    (Subtype.ext (show D.toG s * D.toG s = 1 by rw [← map_mul, hs2, map_one])) ?_).trans ?_
  · intro a ha
    obtain ⟨s', hs', e, he⟩ := D.exists_model_conj hs a ha
    have key := D.f_conj hP h6 hs hs' hs2 hs1 a.2 he
    change D.phiA ⟨((a⁻¹ * ⟨D.toG s, D.X_le_N hs⟩ * a : ↥(centralizer ({D.x} : Set G))) : G),
      mem_subgroupOf.mp ha⟩ = D.phiA ⟨D.toG s, hs⟩
    rw [e, D.phiA_toG, D.phiA_toG, key.2 hXX]
  · exact D.phiA_toG hs

theorem VB_toG (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i))
    (h6 : D.FusN 6 5) {s : SE} (hs : D.toG s ∈ D.X) (hs2 : s * s = 1) (hs1 : s ≠ 1) :
    D.VB ⟨D.toG s, D.X_le_N hs⟩ = Multiplicative.ofAdd (SE.fB s) := by
  have hw : (⟨D.toG s, D.X_le_N hs⟩ : ↥(centralizer ({D.x} : Set G))) ∈ D.Xn :=
    mem_subgroupOf.mpr hs
  refine (transfer_inv_eq D.phiBn D.not_two_dvd_index_Xn hw
    (Subtype.ext (show D.toG s * D.toG s = 1 by rw [← map_mul, hs2, map_one])) ?_).trans ?_
  · intro a ha
    obtain ⟨s', hs', e, he⟩ := D.exists_model_conj hs a ha
    have key := D.f_conj hP h6 hs hs' hs2 hs1 a.2 he
    change D.phiB ⟨((a⁻¹ * ⟨D.toG s, D.X_le_N hs⟩ * a : ↥(centralizer ({D.x} : Set G))) : G),
      mem_subgroupOf.mp ha⟩ = D.phiB ⟨D.toG s, hs⟩
    rw [e, D.phiB_toG, D.phiB_toG, key.1]
  · exact D.phiB_toG hs

end GHSylow

end CFSG.ComponentClassification.GHarris
