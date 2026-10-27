module

public import CFSG.GH74.QTGen4.Recog.G23.HK2
public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.B27ContradictionA
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open scoped commutatorElement
open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable
open CFSG.GH74.QTGen4.Recog.G23.P7.B27A

variable {G : Type} [Group G]

theorem conj_eq_of_comm_rel {a b : G} (h : a⁻¹ * (b⁻¹ * (a * b)) = 1) : b⁻¹ * a * b = a := by
  calc b⁻¹ * a * b = a * (a⁻¹ * (b⁻¹ * (a * b))) := by group
    _ = a := by rw [h, mul_one]

theorem commute_of_comm_rel {a b : G} (h : a⁻¹ * (b⁻¹ * (a * b)) = 1) : Commute a b := by
  show a * b = b * a
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [conj_eq_of_comm_rel h]

section Letters

variable {H H₁ H₂ : Subgroup G} {e : Fin 6 → G}

theorem hlet_sq_eq (hlet : HLetters H H₁ H₂ e) :
    e 0 * e 1 * (e 0 * e 1) = e 2 * e 3 * (e 2 * e 3) := by
  have h := hlet.rels [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false),
    (3, false), (2, false)] (by simp [g23WordsH])
  simp at h
  have h' : e 0 * e 1 * (e 0 * e 1) * ((e 3)⁻¹ * ((e 2)⁻¹ * ((e 3)⁻¹ * (e 2)⁻¹))) = 1 := by
    simpa only [mul_assoc] using h
  rw [eq_inv_of_mul_eq_one_left h']
  group

theorem hlet_comm (hlet : HLetters H H₁ H₂ e) :
    Commute (e 0) (e 2) ∧ Commute (e 0) (e 3) ∧ Commute (e 1) (e 2) ∧ Commute (e 1) (e 3) := by
  have h02 := hlet.rels [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
  have h03 := hlet.rels [(0, false), (3, false), (0, true), (3, true)] (by simp [g23WordsH])
  have h12 := hlet.rels [(1, false), (2, false), (1, true), (2, true)] (by simp [g23WordsH])
  have h13 := hlet.rels [(1, false), (3, false), (1, true), (3, true)] (by simp [g23WordsH])
  simp at h02 h03 h12 h13
  exact ⟨commute_of_comm_rel h02, commute_of_comm_rel h03, commute_of_comm_rel h12,
    commute_of_comm_rel h13⟩

theorem hlet_cube (hlet : HLetters H H₁ H₂ e) :
    e 0 ^ 3 = 1 ∧ e 1 ^ 3 = 1 ∧ e 2 ^ 3 = 1 ∧ e 3 ^ 3 = 1 := by
  have h0 := hlet.rels [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
  have h1 := hlet.rels [(1, true), (1, true), (1, true)] (by simp [g23WordsH])
  have h2 := hlet.rels [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
  have h3 := hlet.rels [(3, true), (3, true), (3, true)] (by simp [g23WordsH])
  simp at h0 h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pow_three]; exact h0
  · rw [pow_three]; exact h1
  · rw [pow_three]; exact h2
  · rw [pow_three]; exact h3

theorem hlet_inv4 (hlet : HLetters H H₁ H₂ e) :
    e 4 * e 4 = 1 ∧ e 4 * (e 0 * (e 4 * e 0)) = 1 ∧ e 4 * (e 1 * (e 4 * e 1)) = 1 ∧
      e 4 * (e 2 * (e 4 * e 2)) = 1 ∧ e 4 * (e 3 * (e 4 * e 3)) = 1 := by
  have h4 := hlet.rels [(4, true), (4, true)] (by simp [g23WordsH])
  have h40 := hlet.rels [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
  have h41 := hlet.rels [(4, true), (1, true), (4, true), (1, true)] (by simp [g23WordsH])
  have h42 := hlet.rels [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
  have h43 := hlet.rels [(4, true), (3, true), (4, true), (3, true)] (by simp [g23WordsH])
  simp at h4 h40 h41 h42 h43
  exact ⟨h4, h40, h41, h42, h43⟩

theorem hlet_mem (hlet : HLetters H H₁ H₂ e) :
    e 0 ∈ H₁ ∧ e 1 ∈ H₁ ∧ e 2 ∈ H₂ ∧ e 3 ∈ H₂ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hlet.gen₁]; exact Subgroup.subset_closure (by simp)
  · rw [← hlet.gen₁]; exact Subgroup.subset_closure (by simp)
  · rw [← hlet.gen₂]; exact Subgroup.subset_closure (by simp)
  · rw [← hlet.gen₂]; exact Subgroup.subset_closure (by simp)

theorem zOf_mem_inf (hlet : HLetters H H₁ H₂ e) : zOf e ∈ H₁ ⊓ H₂ := by
  obtain ⟨a0, a1, a2, a3⟩ := hlet_mem hlet
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · unfold zOf
    exact pow_mem (H₁.mul_mem a0 a1) 2
  · unfold zOf
    rw [pow_two, hlet_sq_eq hlet, ← pow_two]
    exact pow_mem (H₂.mul_mem a2 a3) 2

theorem zOf_ne_one (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) : zOf e ≠ 1 := by
  intro hz
  obtain ⟨a0, a1, -, -⟩ := hlet_mem hlet
  have hyy1 : (e 0 * e 1) * (e 0 * e 1) = 1 := by
    have : (e 0 * e 1) ^ 2 = 1 := hz
    rwa [pow_two] at this
  have hyH : e 0 * e 1 ∈ H₁ := H₁.mul_mem a0 a1
  obtain ⟨ψ⟩ := hone.iso_one
  let yy : H₁ := ⟨e 0 * e 1, hyH⟩
  have hψy : ψ yy * ψ yy = 1 := by
    rw [← map_mul, ← map_one ψ]
    congr 1
    apply Subtype.ext
    exact hyy1
  have hcase := sl23_involution (ψ yy) hψy
  have hneg : ∀ X : Mat2, (-1 : Mat2) * X = X * (-1) := by decide
  have hcent : ∀ B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3), ψ yy * B = B * ψ yy := by
    intro B
    apply Subtype.ext
    rcases hcase with h | h
    · simp [Matrix.SpecialLinearGroup.coe_mul, h]
    · rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h]
      exact hneg _
  have hcentH : ∀ x : H₁, x * yy = yy * x := by
    intro x
    apply ψ.injective
    rw [map_mul, map_mul]
    exact (hcent (ψ x)).symm
  have h0y : e 0 * (e 0 * e 1) = (e 0 * e 1) * e 0 := by
    have := congrArg Subtype.val (hcentH ⟨e 0, a0⟩)
    exact this
  have hcom01 : e 0 * e 1 = e 1 * e 0 := by
    calc e 0 * e 1 = (e 0)⁻¹ * (e 0 * (e 0 * e 1)) := by group
      _ = (e 0)⁻¹ * ((e 0 * e 1) * e 0) := by rw [h0y]
      _ = e 1 * e 0 := by group
  have hcomm : Set.Pairwise ({e 0, e 1} : Set G) Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hcom01
    · exact hcom01.symm
    · exact Commute.refl _
  have hH₁comm : IsMulCommutative H₁ := by
    rw [← hlet.gen₁]
    exact Subgroup.isMulCommutative_closure hcomm
  obtain ⟨A₀, B₀, hAB⟩ := sl23_exists_noncomm
  apply hAB
  have hxy := hH₁comm.is_comm.comm (ψ.symm A₀) (ψ.symm B₀)
  have := congrArg ψ hxy
  simpa using this

theorem inf_eq_or (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (y : G)
    (hy : y ∈ H₁ ⊓ H₂) : y = 1 ∨ y = zOf e := by
  obtain ⟨zu, -, -, huniq⟩ := G23One.exists_unique_inf hone
  have hz' : zOf e = zu := (huniq _ (zOf_mem_inf hlet)).resolve_left (zOf_ne_one hone hlet)
  rw [hz']
  exact huniq y hy

theorem centralizer_zOf (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    Subgroup.centralizer ({zOf e} : Set G) = H := by
  rw [hone.eq_centralizer]
  ext g
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro hg h hh
    rcases inf_eq_or hone hlet h hh with rfl | rfl
    · simp
    · exact hg _ rfl
  · intro hg h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hg _ (Subgroup.mem_inf.mpr ⟨(zOf_mem_inf hlet |> Subgroup.mem_inf.mp).1,
      (zOf_mem_inf hlet |> Subgroup.mem_inf.mp).2⟩)

theorem zOf_central (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    ∀ h ∈ H, h * zOf e = zOf e * h := by
  intro h hh
  rw [← centralizer_zOf hone hlet] at hh
  exact (Subgroup.mem_centralizer_iff.mp hh) _ rfl |>.symm

theorem orderOf_zOf (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    orderOf (zOf e) = 2 :=
  orderOf_eq_prime (by
    have := G23One.sq_inf hone (zOf_mem_inf hlet)
    exact this) (zOf_ne_one hone hlet)

theorem zOf_mem_H (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) : zOf e ∈ H :=
  hone.le_one (zOf_mem_inf hlet |> Subgroup.mem_inf.mp).1

theorem e4_mem_H (hlet : HLetters H H₁ H₂ e) : e 4 ∈ H := by
  rw [← hlet.gen]
  exact Subgroup.subset_closure ⟨4, rfl⟩

theorem e4_sq (hlet : HLetters H H₁ H₂ e) : e 4 * e 4 = 1 := (hlet_inv4 hlet).1

theorem e4_not_mem_K (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    e 4 ∉ H₁ ⊔ H₂ := by
  intro h4
  obtain ⟨a0, a1, a2, a3⟩ := hlet_mem hlet
  have hle : H ≤ H₁ ⊔ H₂ := by
    rw [← hlet.gen]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨i, rfl⟩
    fin_cases i
    · exact le_sup_left (a := H₁) (b := H₂) |> fun h => h a0
    · exact (le_sup_left : H₁ ≤ H₁ ⊔ H₂) a1
    · exact (le_sup_right : H₂ ≤ H₁ ⊔ H₂) a2
    · exact (le_sup_right : H₂ ≤ H₁ ⊔ H₂) a3
    · exact h4
  have hrel := hone.index
  rw [Subgroup.relIndex_eq_one.mpr hle] at hrel
  exact absurd hrel (by norm_num)

end Letters

open scoped Pointwise in
theorem card_sup_eq_mul [Finite G] {X L N : Subgroup G} (hNX : N ≤ X) (hLX : L ≤ X)
    (hconj : ∀ c ∈ X, ∀ n ∈ N, c * n * c⁻¹ ∈ N) (hdisj : N ⊓ L = ⊥) (hsup : N ⊔ L = X) :
    Nat.card ↥X = Nat.card ↥N * Nat.card ↥L := by
  have hNnorm : (N.subgroupOf X).Normal := by
    refine ⟨fun n hn c => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj c.1 c.2 n.1 hn
  have hdisj' : Disjoint (N.subgroupOf X) (L.subgroupOf X) := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxL
    have hx1 : (x : G) ∈ N ⊓ L :=
      ⟨Subgroup.mem_subgroupOf.mp hxN, Subgroup.mem_subgroupOf.mp hxL⟩
    rw [hdisj, Subgroup.mem_bot] at hx1
    exact Subtype.ext hx1
  have hLE : L ≤ Subgroup.normalizer (N : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj l (hLX hl) x hx
    · intro hx
      have h2 := hconj l⁻¹ (X.inv_mem (hLX hl)) _ hx
      have e : l⁻¹ * (l * x * l⁻¹) * l⁻¹⁻¹ = x := by group
      rw [e] at h2
      exact h2
  have hmul : (N.subgroupOf X : Set ↥X) * (L.subgroupOf X : Set ↥X) = Set.univ := by
    ext c
    simp only [Set.mem_mul, SetLike.mem_coe, Set.mem_univ, iff_true]
    have hc : (c : G) ∈ N ⊔ L := by rw [hsup]; exact c.2
    have hc' : (c : G) ∈ ((N ⊔ L : Subgroup G) : Set G) := hc
    rw [Subgroup.coe_mul_of_right_le_normalizer_left N L hLE] at hc'
    obtain ⟨n, hn, l, hl, hnl⟩ := Set.mem_mul.mp hc'
    refine ⟨⟨n, hNX hn⟩, Subgroup.mem_subgroupOf.mpr hn, ⟨l, hLX hl⟩,
      Subgroup.mem_subgroupOf.mpr hl, Subtype.ext ?_⟩
    exact hnl
  have hcomp := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hmul
  have h1 := hcomp.card_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNX).toEquiv] at h1
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLX).toEquiv] at h1
  exact h1.symm

theorem card_of_centComplement [Finite G] {C L N : Subgroup G}
    (h : IsCentComplement C L N) : Nat.card ↥C = Nat.card ↥N * Nat.card ↥L :=
  card_sup_eq_mul h.left_le h.right_le h.conj_mem h.disjoint h.sup_eq

section Helpers

theorem zpowers_order3_eq {g x : G} (hg : g ^ 3 = 1) (hx : x ∈ Subgroup.zpowers g) (h1 : x ≠ 1)
    (h2 : x ≠ g) : x = g⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact h1 (by simp)
  have hord : orderOf g = 3 := orderOf_eq_prime hg hg1
  rw [← zpow_mod_orderOf, hord] at h1 h2 ⊢
  have hk : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hk3 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases hm : k % 3
  · exact absurd (by simp) h1
  · exact absurd (by simp) h2
  · have : g ^ (2 : ℤ) = g⁻¹ := by
      rw [zpow_two, ← pow_two, eq_inv_iff_mul_eq_one, ← pow_succ, hg]
    exact this

end Helpers

section CentE0

variable {H H₁ H₂ M₁ : Subgroup G} {e : Fin 6 → G}

theorem not_commute_e0_e1 (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    ¬ Commute (e 0) (e 1) := by
  intro hc
  have hcomm : Set.Pairwise ({e 0, e 1} : Set G) Commute := by
    intro x hx y hy _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hc
    · exact hc.symm
    · exact Commute.refl _
  have hH₁comm : IsMulCommutative H₁ := by
    rw [← hlet.gen₁]
    exact Subgroup.isMulCommutative_closure hcomm
  obtain ⟨A₀, B₀, hAB⟩ := sl23_exists_noncomm
  obtain ⟨ψ⟩ := hone.iso_one
  apply hAB
  have hxy := hH₁comm.is_comm.comm (ψ.symm A₀) (ψ.symm B₀)
  have := congrArg ψ hxy
  simpa using this

theorem e0_ne_one (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) : e 0 ≠ 1 := by
  intro h
  exact not_commute_e0_e1 hone hlet (by rw [h]; exact Commute.one_left _)

theorem e0_mem_H (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) : e 0 ∈ H :=
  hone.le_one (hlet_mem hlet).1

theorem H₂_le_cent_e0 (hlet : HLetters H H₁ H₂ e) :
    H₂ ≤ Subgroup.centralizer ({e 0} : Set G) := by
  rw [← hlet.gen₂]
  refine (Subgroup.closure_le _).mpr ?_
  intro x hx
  obtain ⟨c02, c03, -, -⟩ := hlet_comm hlet
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  rcases hx with rfl | rfl
  · exact c02.eq
  · exact c03.eq

theorem zOf_mem_cent_e0 (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    zOf e ∈ Subgroup.centralizer ({e 0} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  exact zOf_central hone hlet _ (e0_mem_H hone hlet)

theorem e4_not_mem_cent_e0 (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hF : HFacts H H₁ H₂ e) : e 4 ∉ Subgroup.centralizer ({e 0} : Set G) := by
  intro h4
  have hH : e 4 ∈ Subgroup.centralizer ({e 0} : Set G) ⊓ H :=
    Subgroup.mem_inf.mpr ⟨h4, e4_mem_H hlet⟩
  rw [hF.cent₁] at hH
  apply e4_not_mem_K hone hlet
  have hle : Subgroup.zpowers (e 0) ⊔ H₂ ≤ H₁ ⊔ H₂ :=
    sup_le_sup_right (Subgroup.zpowers_le.mpr (hlet_mem hlet).1) _
  exact hle hH

theorem e4_conj_e0 (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) : e 4 * e 0 * (e 4)⁻¹ = (e 0)⁻¹ := by
  have hmem : e 4 ∈ Subgroup.normalizer (Subgroup.zpowers (e 0) : Set G) := by
    rw [hv.normalizer_eq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hconj : e 4 * e 0 * (e 4)⁻¹ ∈ Subgroup.zpowers (e 0) :=
    (Subgroup.mem_normalizer_iff.mp hmem) (e 0) |>.mp (Subgroup.mem_zpowers _)
  have hne1 : e 4 * e 0 * (e 4)⁻¹ ≠ 1 := by
    intro h
    apply e0_ne_one hone hlet
    have h' : e 4 * e 0 = e 4 := mul_inv_eq_one.mp h
    exact mul_left_cancel (a := e 4) (by rw [mul_one]; exact h')
  have hneq : e 4 * e 0 * (e 4)⁻¹ ≠ e 0 := by
    intro h
    apply e4_not_mem_cent_e0 hone hlet hF
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact (mul_inv_eq_iff_eq_mul.mp h).symm
  exact zpowers_order3_eq (hlet_cube hlet).1 hconj hne1 hneq

end CentE0

section Dsec

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ : Subgroup G} {e : Fin 6 → G}

theorem e0_mem_M₁ (hv : VertexCore e H (e 0) H₂ M₁) : e 0 ∈ M₁ := by
  have h : e 0 ∈ M₁ ⊓ H := by
    rw [hv.inf_H]; exact Subgroup.mem_zpowers _
  exact (Subgroup.mem_inf.mp h).1

theorem zOf_conj_M₁ (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (m : G) (hm : m ∈ M₁) :
    zOf e * m * (zOf e)⁻¹ ∈ M₁ :=
  hv.compl.conj_mem _ (zOf_mem_cent_e0 hone hlet) m hm

theorem M₁_inter_cent_z (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) :
    M₁ ⊓ Subgroup.centralizer ({zOf e} : Set G) = Subgroup.zpowers (e 0) := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxM, hxC⟩ := Subgroup.mem_inf.mp hx
    have hxH : x ∈ H := by
      rw [← centralizer_zOf hone hlet]; exact hxC
    have : x ∈ M₁ ⊓ H := Subgroup.mem_inf.mpr ⟨hxM, hxH⟩
    rw [hv.inf_H] at this
    exact this
  · intro hx
    have hxM : x ∈ M₁ := by
      have h : x ∈ M₁ ⊓ H := by rw [hv.inf_H]; exact hx
      exact (Subgroup.mem_inf.mp h).1
    refine Subgroup.mem_inf.mpr ⟨hxM, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have hxH : x ∈ H := by
      have h : x ∈ M₁ ⊓ H := by rw [hv.inf_H]; exact hx
      exact (Subgroup.mem_inf.mp h).2
    exact (zOf_central hone hlet x hxH).symm

end Dsec

section DDef

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ : Subgroup G} {e : Fin 6 → G}

def zcHom (z : G) (M : Subgroup G) (hz : ∀ m ∈ M, z * m * z⁻¹ ∈ M) : M →* M where
  toFun m := ⟨z * m * z⁻¹, hz m m.2⟩
  map_one' := by ext; simp
  map_mul' m n := by ext; simp only [Subgroup.coe_mul]; group

def phiZ (z : G) (M : Subgroup G) [IsMulCommutative M] (hz : ∀ m ∈ M, z * m * z⁻¹ ∈ M) :
    M →* M :=
  MonoidHom.id M * zcHom z M hz

theorem phiZ_apply (z : G) (M : Subgroup G) [IsMulCommutative M]
    (hz : ∀ m ∈ M, z * m * z⁻¹ ∈ M) (m : M) :
    ((phiZ z M hz) m : G) = (m : G) * (z * m * z⁻¹) := by
  simp [phiZ, zcHom]

def Dg (z : G) (M : Subgroup G) [IsMulCommutative M] (hz : ∀ m ∈ M, z * m * z⁻¹ ∈ M) :
    Subgroup G :=
  (phiZ z M hz).ker.map M.subtype

theorem mem_Dg (z : G) (M : Subgroup G) [IsMulCommutative M] (hz : ∀ m ∈ M, z * m * z⁻¹ ∈ M)
    (x : G) : x ∈ Dg z M hz ↔ x ∈ M ∧ z * x * z⁻¹ = x⁻¹ := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [MonoidHom.mem_ker] at hy
    refine ⟨y.2, ?_⟩
    have h := congrArg (fun w : M => (w : G)) hy
    simp only [Subgroup.coe_one] at h
    rw [phiZ_apply] at h
    have h3 : ((y : G))⁻¹ = z * (y : G) * z⁻¹ := mul_eq_one_iff_inv_eq.mp h
    exact h3.symm
  · rintro ⟨hxM, hx⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    simp only [Subgroup.coe_one]
    rw [phiZ_apply]
    simp only
    rw [hx, mul_inv_cancel]

end DDef

section DCard

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ : Subgroup G} {e : Fin 6 → G}

theorem comm_of_mem_M₁ [IsMulCommutative M₁] {a b : G} (ha : a ∈ M₁) (hb : b ∈ M₁) :
    a * b = b * a :=
  congrArg Subtype.val (mul_comm (⟨a, ha⟩ : M₁) ⟨b, hb⟩)

theorem zOf_comm_zpow_e0 (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) {x : G} (hx : x ∈ Subgroup.zpowers (e 0)) :
    zOf e * x * (zOf e)⁻¹ = x := by
  have hxC : x ∈ Subgroup.centralizer ({zOf e} : Set G) := by
    have : x ∈ M₁ ⊓ Subgroup.centralizer ({zOf e} : Set G) := by
      rw [M₁_inter_cent_z hone hlet hv]; exact hx
    exact (Subgroup.mem_inf.mp this).2
  rw [Subgroup.mem_centralizer_iff] at hxC
  have := hxC (zOf e) (Set.mem_singleton _)
  rw [this, mul_inv_cancel_right]

theorem zpow_three_eq_one_of_mem {g x : G} (hg : g ^ 3 = 1) (hx : x ∈ Subgroup.zpowers g) :
    x ^ 3 = 1 := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have hg' : g ^ ((3 : ℕ) : ℤ) = 1 := by rw [zpow_natCast]; exact hg
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, hg', one_zpow]

theorem zOf_sq (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    zOf e * zOf e = 1 := by
  have h := pow_orderOf_eq_one (zOf e)
  rw [orderOf_zOf hone hlet] at h
  rwa [pow_two] at h

end DCard

section DImage

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ : Subgroup G} {e : Fin 6 → G}

theorem Dg_inter_zpowers (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) [IsMulCommutative M₁]
    (hzM : ∀ m ∈ M₁, zOf e * m * (zOf e)⁻¹ ∈ M₁)
    (hcube : e 0 ^ 3 = 1) :
    Dg (zOf e) M₁ hzM ⊓ Subgroup.zpowers (e 0) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxD, hxP⟩ := Subgroup.mem_inf.mp hx
  rw [mem_Dg] at hxD
  have hxc := zOf_comm_zpow_e0 hone hlet hv hxP
  have h2 : x⁻¹ = x := hxD.2.symm.trans hxc
  have hx2 : x * x = 1 := mul_eq_one_iff_inv_eq.mpr h2
  have hx3 := zpow_three_eq_one_of_mem hcube hxP
  have h := pow_three x
  rw [hx3, hx2, mul_one] at h
  exact Subgroup.mem_bot.mpr h.symm

theorem map_range_phiZ (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) [IsMulCommutative M₁]
    (hzM : ∀ m ∈ M₁, zOf e * m * (zOf e)⁻¹ ∈ M₁)
    (hcube : e 0 ^ 3 = 1) :
    (phiZ (zOf e) M₁ hzM).range.map M₁.subtype = Subgroup.zpowers (e 0) := by
  have hz2 := zOf_sq hone hlet
  have he0M : e 0 ∈ M₁ := e0_mem_M₁ hv
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hy
    show ((phiZ (zOf e) M₁ hzM m : M₁) : G) ∈ Subgroup.zpowers (e 0)
    rw [phiZ_apply]
    have hu : zOf e * (zOf e * (m : G) * (zOf e)⁻¹) * (zOf e)⁻¹ = (m : G) := by
      calc zOf e * (zOf e * (m : G) * (zOf e)⁻¹) * (zOf e)⁻¹
          = (zOf e * zOf e) * (m : G) * (zOf e * zOf e)⁻¹ := by group
        _ = (m : G) := by rw [hz2]; group
    have hcent : zOf e * ((m : G) * (zOf e * (m : G) * (zOf e)⁻¹)) * (zOf e)⁻¹ =
        (zOf e * (m : G) * (zOf e)⁻¹) * (m : G) := by
      rw [show zOf e * ((m : G) * (zOf e * (m : G) * (zOf e)⁻¹)) * (zOf e)⁻¹ =
        (zOf e * (m : G) * (zOf e)⁻¹) * (zOf e * (zOf e * (m : G) * (zOf e)⁻¹) * (zOf e)⁻¹) by group,
        hu]
    have hxcomm : zOf e * ((m : G) * (zOf e * (m : G) * (zOf e)⁻¹)) * (zOf e)⁻¹ =
        (m : G) * (zOf e * (m : G) * (zOf e)⁻¹) := by
      rw [hcent]; exact comm_of_mem_M₁ (hzM _ m.2) m.2
    have hmem : (m : G) * (zOf e * (m : G) * (zOf e)⁻¹) ∈ M₁ :=
      M₁.mul_mem m.2 (hzM _ m.2)
    rw [← M₁_inter_cent_z hone hlet hv]
    refine Subgroup.mem_inf.mpr ⟨hmem, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact mul_inv_eq_iff_eq_mul.mp hxcomm
  · intro hx
    have hxM : x ∈ M₁ := (Subgroup.zpowers_le.mpr he0M) hx
    have hxc := zOf_comm_zpow_e0 hone hlet hv hx
    have hx3 := zpow_three_eq_one_of_mem hcube hx
    refine Subgroup.mem_map.mpr ⟨(phiZ (zOf e) M₁ hzM) ⟨x ^ 2, M₁.pow_mem hxM 2⟩,
      MonoidHom.mem_range.mpr ⟨⟨x ^ 2, M₁.pow_mem hxM 2⟩, rfl⟩, ?_⟩
    show ((phiZ (zOf e) M₁ hzM ⟨x ^ 2, M₁.pow_mem hxM 2⟩ : M₁) : G) = x
    rw [phiZ_apply]
    have hconj : zOf e * x ^ 2 * (zOf e)⁻¹ = x ^ 2 := by
      have hm := map_pow (MulAut.conj (zOf e)) x 2
      simp only [MulAut.conj_apply] at hm
      rw [hm, hxc]
    show x ^ 2 * (zOf e * x ^ 2 * (zOf e)⁻¹) = x
    rw [hconj, ← pow_add, show 2 + 2 = 1 + 3 from rfl, pow_add, hx3, mul_one, pow_one]

end DImage

section Basis

open scoped IsMulCommutative

variable {M₁ : Subgroup G}

theorem exp3_add (hA : IsElemAbelian 3 M₁) : ∀ x : Additive M₁, (3 : ℕ) • x = 0 := by
  intro x
  have hm : (Additive.toMul x) ^ 3 = 1 := by
    apply Subtype.ext
    simpa using hA.2 ((Additive.toMul x : M₁) : G) (Additive.toMul x).2
  show Additive.ofMul ((Additive.toMul x) ^ 3) = 0
  rw [hm]
  rfl

theorem smul_eq_pow_val [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)] (c : ZMod 3)
    (x : Additive M₁) :
    c • x = Additive.ofMul (Additive.toMul x ^ c.val) := by
  calc c • x = ((c.val : ℕ) : ZMod 3) • x := by rw [ZMod.natCast_zmod_val]
    _ = c.val • x := Nat.cast_smul_eq_nsmul (ZMod 3) c.val x
    _ = Additive.ofMul (Additive.toMul x ^ c.val) := rfl

theorem indep_group {σ d₁ d₂ : G} {D : Subgroup G} (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hD : D ⊓ Subgroup.zpowers σ = ⊥) (hd1D : d₁ ∈ D) (hd2D : d₂ ∈ D)
    (hd13 : d₁ ^ 3 = 1) (hd11 : d₁ ≠ 1) (hd23 : d₂ ^ 3 = 1) (hd2 : d₂ ∉ Subgroup.zpowers d₁)
    {n0 n1 n2 : ℕ} (h0 : n0 < 3) (h1 : n1 < 3) (h2 : n2 < 3)
    (hprod : σ ^ n0 * d₁ ^ n1 * d₂ ^ n2 = 1) : n0 = 0 ∧ n1 = 0 ∧ n2 = 0 := by
  have hord_σ : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hord_d : orderOf d₁ = 3 := orderOf_eq_prime hd13 hd11
  have hq : d₁ ^ n1 * d₂ ^ n2 ∈ D :=
    D.mul_mem (D.pow_mem hd1D _) (D.pow_mem hd2D _)
  have hp : σ ^ n0 = (d₁ ^ n1 * d₂ ^ n2)⁻¹ :=
    eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact hprod)
  have hpD : σ ^ n0 ∈ D ⊓ Subgroup.zpowers σ := by
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
    rw [hp]; exact D.inv_mem hq
  rw [hD, Subgroup.mem_bot] at hpD
  have hn0 : n0 = 0 := by
    have : orderOf σ ∣ n0 := orderOf_dvd_of_pow_eq_one hpD
    rw [hord_σ] at this
    interval_cases n0 <;> simp_all
  subst hn0
  simp only [pow_zero, one_mul] at hprod
  have hn2 : n2 = 0 := by
    by_contra hne
    apply hd2
    have hd2pow : d₂ ^ n2 ∈ Subgroup.zpowers d₁ := by
      have : d₂ ^ n2 = (d₁ ^ n1)⁻¹ := eq_inv_of_mul_eq_one_right hprod
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _)
    interval_cases n2
    · exact absurd rfl hne
    · simpa using hd2pow
    · have h4 : (d₂ ^ 2) ^ 2 = d₂ := by
        rw [← pow_mul, show 2 * 2 = 1 + 3 from rfl, pow_add, hd23, mul_one, pow_one]
      rw [← h4]
      exact Subgroup.pow_mem _ hd2pow 2
  subst hn2
  simp only [pow_zero, mul_one] at hprod
  have hn1 : n1 = 0 := by
    have : orderOf d₁ ∣ n1 := orderOf_dvd_of_pow_eq_one hprod
    rw [hord_d] at this
    interval_cases n1 <;> simp_all
  exact ⟨rfl, hn1, rfl⟩

theorem linInd_three [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)] {σ d₁ d₂ : G}
    {D : Subgroup G} (hσM : σ ∈ M₁) (hd1M : d₁ ∈ M₁) (hd2M : d₂ ∈ M₁)
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hD : D ⊓ Subgroup.zpowers σ = ⊥) (hd1D : d₁ ∈ D)
    (hd2D : d₂ ∈ D) (hd13 : d₁ ^ 3 = 1) (hd11 : d₁ ≠ 1) (hd23 : d₂ ^ 3 = 1)
    (hd2 : d₂ ∉ Subgroup.zpowers d₁) :
    LinearIndependent (ZMod 3)
      ![Additive.ofMul (⟨σ, hσM⟩ : M₁), Additive.ofMul (⟨d₁, hd1M⟩ : M₁),
        Additive.ofMul (⟨d₂, hd2M⟩ : M₁)] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_three] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Matrix.cons_val_fin_one, Matrix.head_fin_const] at hg
  rw [smul_eq_pow_val, smul_eq_pow_val, smul_eq_pow_val] at hg
  have hA : (⟨σ, hσM⟩ : M₁) ^ (g 0).val * (⟨d₁, hd1M⟩ : M₁) ^ (g 1).val *
      (⟨d₂, hd2M⟩ : M₁) ^ (g 2).val = 1 := hg
  have hG : σ ^ (g 0).val * d₁ ^ (g 1).val * d₂ ^ (g 2).val = 1 := by
    have := congrArg Subtype.val hA
    simpa using this
  obtain ⟨h0, h1, h2⟩ := indep_group hσ3 hσ1 hD hd1D hd2D hd13 hd11 hd23 hd2
    (ZMod.val_lt _) (ZMod.val_lt _) (ZMod.val_lt _) hG
  intro i
  fin_cases i
  · exact (ZMod.val_eq_zero _).mp h0
  · exact (ZMod.val_eq_zero _).mp h1
  · exact (ZMod.val_eq_zero _).mp h2

end Basis

section Wsec

theorem central_of_normal_card_three {X : Type*} [Group X] [Finite X] [Group.IsNilpotent X]
    (N : Subgroup X) [N.Normal] (hN : Nat.card N = 3) (x : X) (n : X) (hn : n ∈ N) :
    x * n * x⁻¹ = n := by
  have hne : N ≠ ⊥ := by
    intro h
    rw [h] at hN
    simp at hN
  have hne2 : N ⊓ Subgroup.center X ≠ ⊥ := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have hle : N ≤ N ⊓ Subgroup.center X := by
    apply le_of_eq
    symm
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    have hdvd : Nat.card ↥(N ⊓ Subgroup.center X) ∣ 3 := hN ▸ Subgroup.card_dvd_of_le inf_le_left
    have hpos : Nat.card ↥(N ⊓ Subgroup.center X) ≠ 1 := by
      intro h1
      exact hne2 (Subgroup.eq_bot_of_card_eq (N ⊓ Subgroup.center X) h1)
    have := (Nat.dvd_prime Nat.prime_three).mp hdvd
    rcases this with h1 | h1
    · exact absurd h1 hpos
    · rw [h1, hN]
  have hn' : n ∈ Subgroup.center X := (Subgroup.mem_inf.mp (hle hn)).2
  have hc := (Subgroup.mem_center_iff.mp hn') x
  rw [hc, mul_inv_cancel_right]

end Wsec

section WState

variable {H H₁ H₂ M₁ M₂ Pb Np Nm W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem W₁_gen [Finite G] (hst : B27State e M₁ Pb W₁ Mf t') :
    ∃ w ∈ W₁, w ≠ 1 ∧ w ^ 3 = 1 ∧ W₁ = Subgroup.zpowers w := by
  have hne : W₁ ≠ ⊥ := by
    intro h
    rw [h] at hst
    have := hst.card_W₁
    simp at this
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W₁, w ≠ 1 := by
    by_contra hcon
    push_neg at hcon
    exact hne (eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx))
  have hord : orderOf w = 3 := by
    have hdvd : orderOf w ∣ 3 := by
      have := orderOf_dvd_natCard (⟨w, hw⟩ : W₁)
      rw [Subgroup.orderOf_mk, hst.card_W₁] at this
      exact this
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h1
  refine ⟨w, hw, hw1, ?_, ?_⟩
  · rw [← hord]; exact pow_orderOf_eq_one w
  · refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hw) ?_).symm
    rw [Nat.card_zpowers, hord, hst.card_W₁]

theorem W₁_le_Mf (hst : B27State e M₁ Pb W₁ Mf t') : W₁ ≤ Mf :=
  fun x hx => hst.M₁_le (Subgroup.mem_inf.mp (hst.W₁_le hx)).1

theorem W₁_normal_Mf [Finite G] (hst : B27State e M₁ Pb W₁ Mf t') :
    (W₁.subgroupOf Mf).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hc : ⁅(g : G), (n : G)⁆ ∈ W₁ := by
    rw [← hst.derived]
    exact Subgroup.commutator_mem_commutator g.2 (W₁_le_Mf hst hn)
  show (g : G) * (n : G) * (g : G)⁻¹ ∈ W₁
  rw [show (g : G) * (n : G) * (g : G)⁻¹ = ⁅(g : G), (n : G)⁆ * (n : G) by
    rw [commutatorElement_def]; group]
  exact W₁.mul_mem hc hn

theorem W₁_central_Mf [Finite G] (hst : B27State e M₁ Pb W₁ Mf t') (x : G) (hx : x ∈ Mf)
    (n : G) (hn : n ∈ W₁) : x * n * x⁻¹ = n := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Group.IsNilpotent ↥Mf := IsPGroup.isNilpotent hst.three
  haveI := W₁_normal_Mf hst
  have hcard : Nat.card (W₁.subgroupOf Mf) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (W₁_le_Mf hst)).toEquiv, hst.card_W₁]
  have key := central_of_normal_card_three (W₁.subgroupOf Mf) hcard ⟨x, hx⟩ ⟨n, W₁_le_Mf hst hn⟩
    (Subgroup.mem_subgroupOf.mpr hn)
  have := congrArg Subtype.val key
  simpa using this

theorem Mf_le_cent_W₁ [Finite G] (hst : B27State e M₁ Pb W₁ Mf t') :
    Mf ≤ Subgroup.centralizer (W₁ : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hh' : h ∈ W₁ := hh
  have := W₁_central_Mf hst x hx h hh'
  exact (mul_inv_eq_iff_eq_mul.mp this).symm

end WState

section CardH2

variable {H H₁ H₂ : Subgroup G}

theorem card_H₂ (hone : G23One H H₁ H₂) : Nat.card H₂ = 24 := by
  obtain ⟨ψ⟩ := hone.iso_two
  rw [Nat.card_congr ψ.toEquiv, sl23_card]

end CardH2

section Faithful

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem psi_involution_eq (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (ψ : H₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)) (k : G) (hk : k ∈ H₂)
    (hk2 : k * k = 1) (hk1 : k ≠ 1) : (ψ ⟨k, hk⟩ : Mat2) = -1 := by
  have hsq : ψ ⟨k, hk⟩ * ψ ⟨k, hk⟩ = 1 := by
    rw [← map_mul, ← map_one ψ]
    congr 1
    exact Subtype.ext hk2
  rcases sl23_involution _ hsq with h | h
  · exfalso
    apply hk1
    have : (⟨k, hk⟩ : H₂) = 1 := ψ.injective (by rw [map_one]; exact Subtype.ext h)
    exact congrArg Subtype.val this
  · exact h

theorem invol_eq_zOf_H₂ (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (k : G)
    (hk : k ∈ H₂) (hk2 : k * k = 1) (hk1 : k ≠ 1) : k = zOf e := by
  obtain ⟨ψ⟩ := hone.iso_two
  have hzH₂ : zOf e ∈ H₂ := (Subgroup.mem_inf.mp (zOf_mem_inf hlet)).2
  have hz2 : zOf e * zOf e = 1 := zOf_sq hone hlet
  have hz1 := zOf_ne_one hone hlet
  have h1 := psi_involution_eq hone hlet ψ k hk hk2 hk1
  have h2 := psi_involution_eq hone hlet ψ (zOf e) hzH₂ hz2 hz1
  have : ψ ⟨k, hk⟩ = ψ ⟨zOf e, hzH₂⟩ := Subtype.ext (h1.trans h2.symm)
  exact congrArg Subtype.val (ψ.injective this)

theorem zOf_not_cent_M₁ [Finite G] (hst : B27State e M₁ Pb W₁ Mf t') (hone : G23One H H₁ H₂)
    (hlet : HLetters H H₁ H₂ e) : zOf e ∉ Subgroup.centralizer (M₁ : Set G) := by
  intro hz
  obtain ⟨w, hwW, hw1, hw3, -⟩ := W₁_gen hst
  have hwM : w ∈ M₁ := (Subgroup.mem_inf.mp (hst.W₁_le hwW)).1
  have hcomm : w * zOf e = zOf e * w := (Subgroup.mem_centralizer_iff.mp hz) w hwM
  have hconj : zOf e * w * (zOf e)⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr hcomm.symm
  have hinv := hst.W₁_inv w hwW
  rw [hconj] at hinv
  have hw2 : w * w = 1 := mul_eq_one_iff_inv_eq.mpr hinv.symm
  apply hw1
  have h := pow_three w
  rw [hw3, hw2, mul_one] at h
  exact h.symm

theorem conj_H₂_mem (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (h : G) (hh : h ∈ H₂) (m : G) (hm : m ∈ M₁) : h * m * h⁻¹ ∈ M₁ :=
  hv.compl.conj_mem h (H₂_le_cent_e0 hlet hh) m hm

theorem fix_H₂_eq_bot [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t') :
    Subgroup.centralizer (M₁ : Set G) ⊓ H₂ = ⊥ := by
  by_contra hne
  set K : Subgroup G := Subgroup.centralizer (M₁ : Set G) ⊓ H₂ with hKdef
  have hKC : ∀ x ∈ K, ∀ m ∈ M₁, x * m = m * x := fun x hx m hm =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).1) m hm |>.symm
  have hKH : ∀ x ∈ K, x ∈ H₂ := fun x hx => (Subgroup.mem_inf.mp hx).2
  have hnoinv : ∀ k ∈ K, k * k = 1 → k = 1 := by
    intro k hk hk2
    by_contra hk1
    have hkz := invol_eq_zOf_H₂ hone hlet k (hKH k hk) hk2 hk1
    apply zOf_not_cent_M₁ hst hone hlet
    rw [← hkz]
    exact (Subgroup.mem_inf.mp hk).1
  have hconjK : ∀ h ∈ H₂, ∀ x ∈ K, h * x * h⁻¹ ∈ K := by
    intro h hh x hx
    refine Subgroup.mem_inf.mpr ⟨?_, Subgroup.mem_inf.mp hx |>.2 |> fun h2 =>
      (H₂.mul_mem (H₂.mul_mem hh h2) (H₂.inv_mem hh))⟩
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hm' : h⁻¹ * m * h⁻¹⁻¹ ∈ M₁ := conj_H₂_mem hlet hv h⁻¹ (H₂.inv_mem hh) m hm
    have hxm := hKC x hx (h⁻¹ * m * h⁻¹⁻¹) hm'
    have hmm : h * (h⁻¹ * m * h⁻¹⁻¹) * h⁻¹ = m := by group
    calc m * (h * x * h⁻¹) = (h * (h⁻¹ * m * h⁻¹⁻¹) * h⁻¹) * (h * x * h⁻¹) := by rw [hmm]
      _ = h * ((h⁻¹ * m * h⁻¹⁻¹) * x) * h⁻¹ := by group
      _ = h * (x * (h⁻¹ * m * h⁻¹⁻¹)) * h⁻¹ := by rw [← hxm]
      _ = (h * x * h⁻¹) * (h * (h⁻¹ * m * h⁻¹⁻¹) * h⁻¹) := by group
      _ = (h * x * h⁻¹) * m := by rw [hmm]
  have hcardH₂ : Nat.card H₂ = 24 := card_H₂ hone
  have hdvdK : Nat.card K ∣ 24 := hcardH₂ ▸ Subgroup.card_dvd_of_le (inf_le_right : K ≤ H₂)
  have hodd : ¬ 2 ∣ Nat.card K := by
    intro h2
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hk2 : (k : G) * (k : G) = 1 := by
      have h1 : k ^ 2 = 1 := by rw [← hk]; exact pow_orderOf_eq_one k
      have h3 := congrArg Subtype.val h1
      simpa [pow_two] using h3
    have hk1 : (k : G) ≠ 1 := by
      intro h1
      have : orderOf k = 1 := by
        rw [orderOf_eq_one_iff]
        exact Subtype.ext h1
      rw [hk] at this
      norm_num at this
    exact hk1 (hnoinv _ k.2 hk2)
  obtain ⟨n, hn⟩ : ∃ n, Nat.card K = n := ⟨_, rfl⟩
  rw [hn] at hdvdK hodd
  have hn3 : n = 1 ∨ n = 3 := by
    have hle : n ≤ 24 := Nat.le_of_dvd (by norm_num) hdvdK
    interval_cases n
    all_goals first
      | (left; rfl)
      | (right; rfl)
      | (exfalso; omega)
  rcases hn3 with h1 | h3
  · exact hne (Subgroup.eq_bot_of_card_eq K (by rw [hn, h1]))
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx3⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hn, h3])
  have hyK : (x : G) ∈ K := x.2
  have hordy : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx3]
  have hy3 : (x : G) ^ 3 = 1 := by rw [← hordy]; exact pow_orderOf_eq_one _
  have hy1 : (x : G) ≠ 1 := by
    intro h
    have : orderOf (x : G) = 1 := by rw [h, orderOf_one]
    rw [hordy] at this
    norm_num at this
  have hKeq : Subgroup.zpowers (x : G) = K :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hyK) (by
      rw [Nat.card_zpowers, hordy, hn, h3])
  have hfix : ∀ g ∈ H₂, g ^ 3 = 1 → g * (x : G) * g⁻¹ = (x : G) := by
    intro g hg hg3
    have hmemK : g * (x : G) * g⁻¹ ∈ K := hconjK g hg _ hyK
    have hmem : g * (x : G) * g⁻¹ ∈ Subgroup.zpowers (x : G) := by
      rw [hKeq]; exact hmemK
    by_cases hc : g * (x : G) * g⁻¹ = (x : G)
    · exact hc
    · exfalso
      have hne1 : g * (x : G) * g⁻¹ ≠ 1 := by
        intro h
        apply hy1
        exact mul_left_cancel (a := g) (by rw [mul_one]; exact mul_inv_eq_one.mp h)
      have hinv := zpowers_order3_eq hy3 hmem hne1 hc
      have h3' : g * (x : G)⁻¹ * g⁻¹ = (x : G) := by
        calc g * (x : G)⁻¹ * g⁻¹ = (g * (x : G) * g⁻¹)⁻¹ := by group
          _ = (x : G) := by rw [hinv, inv_inv]
      have hA : g * (g * (g * (x : G) * g⁻¹) * g⁻¹) * g⁻¹ = (x : G)⁻¹ := by
        rw [hinv, h3', hinv]
      have hg3' : g * (g * g) = 1 := by rw [← pow_three]; exact hg3
      have key : g * (g * (g * (x : G) * g⁻¹) * g⁻¹) * g⁻¹ = (x : G) := by
        calc g * (g * (g * (x : G) * g⁻¹) * g⁻¹) * g⁻¹
            = (g * (g * g)) * (x : G) * (g * (g * g))⁻¹ := by group
          _ = (x : G) := by rw [hg3']; group
      have hxx : (x : G) * (x : G) = 1 := mul_eq_one_iff_inv_eq.mpr (hA.symm.trans key)
      apply hy1
      have h := pow_three (x : G)
      rw [hy3, hxx, mul_one] at h
      exact h.symm
  have hcentH : H₂ ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
    rw [← hlet.gen₂]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hgH : g ∈ H₂ := by
      rw [← hlet.gen₂]; exact Subgroup.subset_closure (by simpa using hg)
    have hg3 : g ^ 3 = 1 := by
      rcases hg with rfl | rfl
      · exact (hlet_cube hlet).2.2.1
      · exact (hlet_cube hlet).2.2.2
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    exact (mul_inv_eq_iff_eq_mul.mp (hfix g hgH hg3)).symm
  obtain ⟨ψ⟩ := hone.iso_two
  have hxH : (x : G) ∈ H₂ := hKH _ hyK
  have hcentψ : ∀ B : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3),
      ψ ⟨(x : G), hxH⟩ * B = B * ψ ⟨(x : G), hxH⟩ := by
    intro B
    obtain ⟨u, rfl⟩ : ∃ u : H₂, ψ u = B := ⟨ψ.symm B, ψ.apply_symm_apply B⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp (hcentH u.2) (x : G) rfl
  rcases sl23_central _ hcentψ with hc | hc
  · apply hy1
    have : ψ ⟨(x : G), hxH⟩ = 1 := Subtype.ext hc
    exact congrArg Subtype.val (ψ.injective (this.trans (map_one ψ).symm))
  · have hzH₂ : zOf e ∈ H₂ := (Subgroup.mem_inf.mp (zOf_mem_inf hlet)).2
    have hz2 : zOf e * zOf e = 1 := zOf_sq hone hlet
    have hz1 := zOf_ne_one hone hlet
    have hzψ := psi_involution_eq hone hlet ψ (zOf e) hzH₂ hz2 hz1
    have hpsi : ψ ⟨(x : G), hxH⟩ = ψ ⟨zOf e, hzH₂⟩ := Subtype.ext (hc.trans hzψ.symm)
    have hxz : (x : G) = zOf e := congrArg Subtype.val (ψ.injective hpsi)
    apply zOf_not_cent_M₁ hst hone hlet
    have hzK : zOf e ∈ K := hxz ▸ hyK
    exact (Subgroup.mem_inf.mp hzK).1

end Faithful

section GL3Rep

open scoped IsMulCommutative

variable {M : Subgroup G} [IsMulCommutative M]

@[expose] def conjM (x : G) (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M) : M →* M where
  toFun m := ⟨x * m * x⁻¹, hx m m.2⟩
  map_one' := by ext; simp
  map_mul' m n := by ext; simp only [Subgroup.coe_mul]; group

@[expose] noncomputable def conjLin [Module (ZMod 3) (Additive M)] (x : G) (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M) :
    Additive M →ₗ[ZMod 3] Additive M :=
  AddMonoidHom.toZModLinearMap 3 (MonoidHom.toAdditive (conjM x hx))

theorem conjLin_apply [Module (ZMod 3) (Additive M)] (x : G) (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (v : Additive M) : Additive.toMul (conjLin x hx v) = conjM x hx (Additive.toMul v) := rfl

theorem conjLin_mul [Module (ZMod 3) (Additive M)] (x y : G) (hx : ∀ m ∈ M, x * m * x⁻¹ ∈ M)
    (hy : ∀ m ∈ M, y * m * y⁻¹ ∈ M) (hxy : ∀ m ∈ M, x * y * m * (x * y)⁻¹ ∈ M) :
    conjLin (x * y) hxy = (conjLin x hx).comp (conjLin y hy) := by
  ext v : 1
  apply Additive.toMul.injective
  rw [conjLin_apply, LinearMap.comp_apply, conjLin_apply, conjLin_apply]
  apply Subtype.ext
  simp only [conjM, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mk]
  group

theorem conjLin_one [Module (ZMod 3) (Additive M)] (hx : ∀ m ∈ M, (1 : G) * m * (1 : G)⁻¹ ∈ M) :
    conjLin (1 : G) hx = LinearMap.id := by
  ext v : 1
  apply Additive.toMul.injective
  rw [conjLin_apply]
  apply Subtype.ext
  simp [conjM]

end GL3Rep

section GL3Hom

open scoped IsMulCommutative

variable {M : Subgroup G} [IsMulCommutative M]

theorem mem_NM_conj {x : G} (hx : x ∈ Subgroup.normalizer (M : Set G)) :
    ∀ m ∈ M, x * m * x⁻¹ ∈ M :=
  fun m hm => (Subgroup.mem_normalizer_iff.mp hx m).mp hm

@[expose] noncomputable def rhoMat [Module (ZMod 3) (Additive M)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M)) (x : Subgroup.normalizer (M : Set G)) :
    Matrix (Fin 3) (Fin 3) (ZMod 3) :=
  LinearMap.toMatrix b b (conjLin (x : G) (mem_NM_conj x.2))

theorem rhoMat_mul [Module (ZMod 3) (Additive M)] (b : Module.Basis (Fin 3) (ZMod 3) (Additive M))
    (x y : Subgroup.normalizer (M : Set G)) :
    rhoMat b (x * y) = rhoMat b x * rhoMat b y := by
  unfold rhoMat
  exact (congrArg (LinearMap.toMatrix b b) (conjLin_mul (M := M) (x : G) (y : G)
    (mem_NM_conj x.2) (mem_NM_conj y.2) (mem_NM_conj (x * y).2))).trans
    (LinearMap.toMatrix_comp b b b _ _)

theorem rhoMat_one [Module (ZMod 3) (Additive M)] (b : Module.Basis (Fin 3) (ZMod 3) (Additive M)) :
    rhoMat b 1 = 1 := by
  unfold rhoMat
  exact (congrArg (LinearMap.toMatrix b b) (conjLin_one (M := M) _)).trans
    (LinearMap.toMatrix_id b)

@[expose] noncomputable def rhoGL [Module (ZMod 3) (Additive M)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M)) :
    Subgroup.normalizer (M : Set G) →* GL (Fin 3) (ZMod 3) where
  toFun x := ⟨rhoMat b x, rhoMat b x⁻¹, by
      rw [← rhoMat_mul, mul_inv_cancel, rhoMat_one],
    by rw [← rhoMat_mul, inv_mul_cancel, rhoMat_one]⟩
  map_one' := Units.ext (rhoMat_one b)
  map_mul' x y := Units.ext (rhoMat_mul b x y)

theorem rhoGL_val [Module (ZMod 3) (Additive M)] (b : Module.Basis (Fin 3) (ZMod 3) (Additive M))
    (x : Subgroup.normalizer (M : Set G)) :
    ((rhoGL b x : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = rhoMat b x := rfl

theorem rhoMat_entry [Module (ZMod 3) (Additive M)] (b : Module.Basis (Fin 3) (ZMod 3) (Additive M))
    (x : Subgroup.normalizer (M : Set G)) (i j : Fin 3) :
    rhoMat b x i j = b.repr (conjLin (x : G) (mem_NM_conj x.2) (b j)) i :=
  LinearMap.toMatrix_apply b b _ i j

theorem rhoGL_eq_one_iff [Module (ZMod 3) (Additive M)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M)) (x : Subgroup.normalizer (M : Set G)) :
    rhoGL b x = 1 ↔ ∀ m ∈ M, (x : G) * m * (x : G)⁻¹ = m := by
  constructor
  · intro h m hm
    have hm1 : rhoMat b x = 1 := by
      have := congrArg (fun g : GL (Fin 3) (ZMod 3) => (g : Matrix (Fin 3) (Fin 3) (ZMod 3))) h
      exact this
    have hlin : conjLin (x : G) (mem_NM_conj x.2) = LinearMap.id := by
      apply (LinearMap.toMatrix b b).injective
      rw [LinearMap.toMatrix_id]
      exact hm1
    have hv := congrArg (fun f : Additive M →ₗ[ZMod 3] Additive M => f (Additive.ofMul ⟨m, hm⟩)) hlin
    have := congrArg Additive.toMul hv
    have h2 : (x : G) * m * (x : G)⁻¹ = m := congrArg Subtype.val this
    exact h2
  · intro h
    apply Units.ext
    show rhoMat b x = 1
    have hlin : conjLin (x : G) (mem_NM_conj x.2) = LinearMap.id := by
      apply LinearMap.ext
      intro v
      apply Additive.toMul.injective
      rw [conjLin_apply]
      apply Subtype.ext
      show (x : G) * ((Additive.toMul v : M) : G) * (x : G)⁻¹ = ((Additive.toMul v : M) : G)
      exact h _ (Additive.toMul v : M).2
    show LinearMap.toMatrix b b (conjLin (x : G) (mem_NM_conj x.2)) = 1
    rw [hlin, LinearMap.toMatrix_id]

end GL3Hom

section BasisM1

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem card_additive (M : Subgroup G) : Nat.card (Additive M) = Nat.card M :=
  Nat.card_congr Additive.ofMul

theorem card_Dg [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) [IsMulCommutative M₁]
    (hzM : ∀ m ∈ M₁, zOf e * m * (zOf e)⁻¹ ∈ M₁) (hcard : Nat.card M₁ = 27) :
    Nat.card (Dg (zOf e) M₁ hzM) = 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcube : e 0 ^ 3 = 1 := (hlet_cube hlet).1
  have he0 : e 0 ≠ 1 := e0_ne_one hone hlet
  have himg : Nat.card (phiZ (zOf e) M₁ hzM).range = 3 := by
    rw [← Subgroup.card_map_of_injective (f := M₁.subtype) Subtype.val_injective,
      map_range_phiZ hone hlet hv hzM hcube, Nat.card_zpowers, orderOf_eq_prime hcube he0]
  have hker := Subgroup.card_mul_index (phiZ (zOf e) M₁ hzM).ker
  rw [Subgroup.index_ker, himg, hcard] at hker
  unfold Dg
  rw [Subgroup.card_map_of_injective Subtype.val_injective]
  omega

theorem exists_d₂ [Finite G] (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) [IsMulCommutative M₁]
    (hzM : ∀ m ∈ M₁, zOf e * m * (zOf e)⁻¹ ∈ M₁) (hcard : Nat.card M₁ = 27)
    (w : G) (hw3 : w ^ 3 = 1) :
    ∃ d ∈ Dg (zOf e) M₁ hzM, d ∉ Subgroup.zpowers w := by
  by_contra hcon
  push_neg at hcon
  have hle : Dg (zOf e) M₁ hzM ≤ Subgroup.zpowers w := fun x hx => hcon x hx
  have h1 := Subgroup.card_le_of_le hle
  have hdD := card_Dg hone hlet hv hzM hcard
  have hord : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have hord3 : Nat.card (Subgroup.zpowers w) ≤ 3 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) hord
  omega

theorem gl3_basis [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t') (hcard : Nat.card M₁ = 27) (hexp : ∀ m ∈ M₁, m ^ 3 = 1) :
    ∃ (w : G) (hwM : w ∈ M₁) (d : G) (hdM : d ∈ M₁)
      (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁)),
      w ∈ W₁ ∧ w ≠ 1 ∧ d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) ∧
      b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁) ∧
      b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁) ∧ b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁) := by
  have hcube : e 0 ^ 3 = 1 := (hlet_cube hlet).1
  obtain ⟨w, hwW, hw1, hw3, -⟩ := W₁_gen hst
  have hwM : w ∈ M₁ := (Subgroup.mem_inf.mp (hst.W₁_le hwW)).1
  have hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) :=
    (mem_Dg _ _ _ w).mpr ⟨hwM, hst.W₁_inv w hwW⟩
  obtain ⟨d, hdD, hdw⟩ := exists_d₂ hone hlet hv (zOf_conj_M₁ hone hlet hv) hcard w hw3
  have hdM : d ∈ M₁ := ((mem_Dg _ _ _ d).mp hdD).1
  have hd3 : d ^ 3 = 1 := hexp d hdM
  have hli := linInd_three (σ := e 0) (d₁ := w) (d₂ := d) (hσM := e0_mem_M₁ hv) (hd1M := hwM)
    (hd2M := hdM) (hσ3 := hcube) (hσ1 := e0_ne_one hone hlet)
    (hD := Dg_inter_zpowers hone hlet hv (zOf_conj_M₁ hone hlet hv) hcube) (hd1D := hwD)
    (hd2D := hdD) (hd13 := hw3) (hd11 := hw1) (hd23 := hd3) (hd2 := hdw)
  have hcardA : Nat.card (Additive M₁) = 27 := (card_additive M₁).trans hcard
  refine ⟨w, hwM, d, hdM, basis_of_indep3 hcardA _ hli, hwW, hw1, hdD, ?_, ?_, ?_⟩
  · exact basis_of_indep3_apply hcardA _ hli 0
  · exact basis_of_indep3_apply hcardA _ hli 1
  · exact basis_of_indep3_apply hcardA _ hli 2

end BasisM1

section Coords

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem coord0_zero [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t') {w d : G} (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (x : Additive M₁) (hx : ((Additive.toMul x : M₁) : G) ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    b.repr x 0 = 0 := by
  have hcube : e 0 ^ 3 = 1 := (hlet_cube hlet).1
  have hsum := b.sum_repr x
  rw [Fin.sum_univ_three, hb0, hb1, hb2, smul_eq_pow_val, smul_eq_pow_val, smul_eq_pow_val] at hsum
  have h' : ((⟨e 0, e0_mem_M₁ hv⟩ : M₁) ^ (b.repr x 0).val * (⟨w, hwM⟩ : M₁) ^ (b.repr x 1).val *
      (⟨d, hdM⟩ : M₁) ^ (b.repr x 2).val : M₁) = Additive.toMul x := congrArg Additive.toMul hsum
  have hG : e 0 ^ (b.repr x 0).val * w ^ (b.repr x 1).val * d ^ (b.repr x 2).val =
      ((Additive.toMul x : M₁) : G) := by
    have := congrArg Subtype.val h'
    simpa using this
  have hσD : e 0 ^ (b.repr x 0).val ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) := by
    have hq : w ^ (b.repr x 1).val * d ^ (b.repr x 2).val ∈
        Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) :=
      Subgroup.mul_mem _ (Subgroup.pow_mem _ hwD _) (Subgroup.pow_mem _ hdD _)
    have : e 0 ^ (b.repr x 0).val = ((Additive.toMul x : M₁) : G) * (w ^ (b.repr x 1).val * d ^ (b.repr x 2).val)⁻¹ := by
      rw [← hG]; group
    rw [this]
    exact Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hq)
  have hmem : e 0 ^ (b.repr x 0).val ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) ⊓
      Subgroup.zpowers (e 0) := Subgroup.mem_inf.mpr ⟨hσD, Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _⟩
  rw [Dg_inter_zpowers hone hlet hv (zOf_conj_M₁ hone hlet hv) hcube, Subgroup.mem_bot] at hmem
  have hord : orderOf (e 0) = 3 := orderOf_eq_prime hcube (e0_ne_one hone hlet)
  have hdvd : orderOf (e 0) ∣ (b.repr x 0).val := orderOf_dvd_of_pow_eq_one hmem
  rw [hord] at hdvd
  have hlt := ZMod.val_lt (b.repr x 0)
  have h0 : (b.repr x 0).val = 0 := by
    interval_cases hv' : (b.repr x 0).val <;> omega
  exact (ZMod.val_eq_zero _).mp h0

end Coords

section Entries

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem H₂_le_normalizer_M₁ (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁) :
    H₂ ≤ Subgroup.normalizer (M₁ : Set G) := fun h hh => by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    exact conj_H₂_mem hlet hv h hh g hg
  · intro hg
    have := conj_H₂_mem hlet hv h⁻¹ (H₂.inv_mem hh) (h * g * h⁻¹) hg
    have e1 : h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g := by group
    rw [e1] at this
    exact this

theorem mem_of_rho_eq_one [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (x : Subgroup.normalizer (M₁ : Set G)) (hx : rhoGL b x = 1) : (x : G) ∈ M₁ := by
  have hc := (rhoGL_eq_one_iff b x).mp hx
  have hxk : ∀ k ∈ M₁, (x : G) * k = k * (x : G) := fun k hk =>
    mul_inv_eq_iff_eq_mul.mp (hc k hk)
  have hxσ : (x : G) ∈ Subgroup.centralizer ({e 0} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hxk (e 0) (e0_mem_M₁ hv)).symm
  have hsup : (x : G) ∈ M₁ ⊔ H₂ := by
    rw [hv.compl.sup_eq]; exact hxσ
  have hmul := Subgroup.coe_mul_of_right_le_normalizer_left M₁ H₂ (H₂_le_normalizer_M₁ hlet hv)
  have hx' : (x : G) ∈ ((M₁ ⊔ H₂ : Subgroup G) : Set G) := hsup
  rw [hmul] at hx'
  obtain ⟨m, hm, h, hh, hmh⟩ := Set.mem_mul.mp hx'
  have hh_eq : h = m⁻¹ * (x : G) := by rw [← hmh]; group
  have hhc : h ∈ Subgroup.centralizer (M₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    symm
    calc h * k = m⁻¹ * ((x : G) * k) := by rw [hh_eq]; group
      _ = m⁻¹ * (k * (x : G)) := by rw [hxk k hk]
      _ = (m⁻¹ * k) * (x : G) := by group
      _ = (k * m⁻¹) * (x : G) := by rw [comm_of_mem_M₁ (M₁.inv_mem hm) hk]
      _ = k * h := by rw [hh_eq]; group
  have hh1 : h = 1 := by
    have hmem : h ∈ Subgroup.centralizer (M₁ : Set G) ⊓ H₂ := Subgroup.mem_inf.mpr ⟨hhc, hh⟩
    rw [fix_H₂_eq_bot hone hlet hv hst, Subgroup.mem_bot] at hmem
    exact hmem
  rw [← hmh, hh1, mul_one]
  exact hm

end Entries

section RhoEntries

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem zpow_smul_eq [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)] (x : M₁) (k : ℤ) :
    Additive.ofMul (x ^ k) = (k : ZMod 3) • Additive.ofMul x := by
  rw [Int.cast_smul_eq_zsmul]
  rfl

theorem rhoMat_col0 [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hv : VertexCore e H (e 0) H₂ M₁)
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (n : Subgroup.normalizer (M₁ : Set G)) (k : ℤ) (hk : (n : G) * e 0 * (n : G)⁻¹ = e 0 ^ k)
    (i : Fin 3) : rhoMat b n i 0 = if i = 0 then (k : ZMod 3) else 0 := by
  rw [rhoMat_entry]
  have hconj : conjLin (n : G) (mem_NM_conj n.2) (b 0) = (k : ZMod 3) • b 0 := by
    rw [hb0]
    have h1 : conjLin (n : G) (mem_NM_conj n.2) (Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁)) =
        Additive.ofMul (⟨(n : G) * e 0 * (n : G)⁻¹, mem_NM_conj n.2 _ (e0_mem_M₁ hv)⟩ : M₁) := rfl
    rw [h1]
    have h2 : (⟨(n : G) * e 0 * (n : G)⁻¹, mem_NM_conj n.2 _ (e0_mem_M₁ hv)⟩ : M₁) =
        (⟨e 0, e0_mem_M₁ hv⟩ : M₁) ^ k := Subtype.ext (by simpa using hk)
    rw [h2, zpow_smul_eq]
  rw [hconj, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply]
  by_cases hi : i = 0
  · subst hi; simp
  · simp only [hi, if_false, Finsupp.single_apply, if_neg (Ne.symm hi), mul_zero]
    simp [Ne.symm hi]

end RhoEntries

section RhoEntries2

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem rhoMat_row0 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (n : Subgroup.normalizer (M₁ : Set G))
    (hD : ∀ x ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv), (n : G) * x * (n : G)⁻¹ ∈
      Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    rhoMat b n 0 1 = 0 ∧ rhoMat b n 0 2 = 0 := by
  constructor
  · rw [rhoMat_entry, hb1]
    apply coord0_zero hone hlet hv hst hwM hdM b hb0 hb1 hb2 hwD hdD
    show (n : G) * w * (n : G)⁻¹ ∈ _
    exact hD w hwD
  · rw [rhoMat_entry, hb2]
    apply coord0_zero hone hlet hv hst hwM hdM b hb0 hb1 hb2 hwD hdD
    show (n : G) * d * (n : G)⁻¹ ∈ _
    exact hD d hdD

end RhoEntries2

section ConjCent

theorem card_centralizer_conj [Finite G] (n x : G) :
    Nat.card (Subgroup.centralizer ({n * x * n⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  let f : G →* G := MulAut.conj n
  have hf : ∀ y : G, f y = n * y * n⁻¹ := fun y => rfl
  have hmap : Subgroup.centralizer ({n * x * n⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map f := by
    ext g
    constructor
    · intro hg
      rw [Subgroup.mem_centralizer_iff] at hg
      refine Subgroup.mem_map.mpr ⟨n⁻¹ * g * n, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        rw [hh]
        have h1 := hg (n * x * n⁻¹) (Set.mem_singleton _)
        calc x * (n⁻¹ * g * n) = n⁻¹ * ((n * x * n⁻¹) * g) * n := by group
          _ = n⁻¹ * (g * (n * x * n⁻¹)) * n := by rw [h1]
          _ = n⁻¹ * g * n * x := by group
      · rw [hf]; group
    · intro hg
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have hy' := hy x (Set.mem_singleton _)
      rw [hf]
      calc n * x * n⁻¹ * (n * y * n⁻¹) = n * (x * y) * n⁻¹ := by group
        _ = n * (y * x) * n⁻¹ := by rw [hy']
        _ = n * y * n⁻¹ * (n * x * n⁻¹) := by group
  rw [hmap, Subgroup.card_map_of_injective (f := f) (MulAut.conj n).injective]

end ConjCent

section Not13

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

theorem not_dvd13 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    [G23Leaf LeafGL3Facts]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t') (hC : Nat.card (Subgroup.centralizer ({e 0} : Set G)) = 648)
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (w : G) (hwM : w ∈ M₁) (hwW : w ∈ W₁) (hw1 : w ≠ 1)
    (hWeq : W₁ = Subgroup.zpowers w) (hw3 : w ^ 3 = 1)
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) :
    ¬ 13 ∣ Nat.card (rhoGL b).range := by
  intro h13
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 13 h13
  have hyY : (y : GL (Fin 3) (ZMod 3)) ∈ (rhoGL b).range := y.2
  have hy13 : orderOf (y : GL (Fin 3) (ZMod 3)) = 13 := by
    rw [Subgroup.orderOf_coe, hy]
  have hLGL := (G23Leaf.out (L := LeafGL3Facts)).1
  have hu : (fun i => b.repr (b 0) i : Fin 3 → ZMod 3) ≠ 0 := by
    intro h0
    have : b.repr (b 0) = 0 := Finsupp.ext fun i => congrFun h0 i
    rw [Module.Basis.repr_self] at this
    exact Finsupp.single_ne_zero.mpr one_ne_zero this
  have hv' : (fun i => b.repr (b 1) i : Fin 3 → ZMod 3) ≠ 0 := by
    intro h0
    have : b.repr (b 1) = 0 := Finsupp.ext fun i => congrFun h0 i
    rw [Module.Basis.repr_self] at this
    exact Finsupp.single_ne_zero.mpr one_ne_zero this
  obtain ⟨k, c, hc, hmul⟩ := hLGL _ hy13 _ _ hu hv'
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp (Subgroup.pow_mem _ hyY k)
  have hmv : (rhoMat b n).mulVec (fun i => b.repr (b 0) i) =
      c • (fun i => b.repr (b 1) i) := by
    have : rhoMat b n = (((y : GL (Fin 3) (ZMod 3)) ^ k : GL (Fin 3) (ZMod 3)) :
        Matrix (Fin 3) (Fin 3) (ZMod 3)) := by
      rw [← hn]; rfl
    rw [this]
    exact hmul
  have hcol : ∀ i, rhoMat b n i 0 = c * (if i = 1 then 1 else 0) := by
    intro i
    have := congrFun hmv i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Module.Basis.repr_self,
      Finsupp.single_apply] at this
    rw [this]
    by_cases hi : i = 1
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  have hconj : conjLin (n : G) (mem_NM_conj n.2) (b 0) = c • b 1 := by
    apply b.repr.injective
    ext i
    rw [← rhoMat_entry, hcol i, map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_apply, smul_eq_mul]
    by_cases hi : i = 1
    · subst hi; simp
    · simp [hi, Ne.symm hi]
  have hs : (n : G) * e 0 * (n : G)⁻¹ = w ^ c.val := by
    have h1 := congrArg Additive.toMul hconj
    rw [conjLin_apply, hb0, hb1, smul_eq_pow_val] at h1
    have h2 := congrArg Subtype.val h1
    exact h2
  have hwne : w ^ c.val ≠ 1 := by
    intro h
    have hdvd := orderOf_dvd_of_pow_eq_one h
    rw [orderOf_eq_prime hw3 hw1] at hdvd
    have hlt : c.val < 3 := ZMod.val_lt c
    have hpos : c.val ≠ 0 := fun h0 => hc ((ZMod.val_eq_zero c).mp h0)
    omega
  have hsW : (n : G) * e 0 * (n : G)⁻¹ ∈ W₁ := by
    rw [hs, hWeq]; exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) _
  have hMfC : Mf ≤ Subgroup.centralizer ({(n : G) * e 0 * (n : G)⁻¹} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have hx' := Subgroup.mem_centralizer_iff.mp (Mf_le_cent_W₁ hst hx)
    exact hx' _ hsW
  have hdvd := Subgroup.card_dvd_of_le hMfC
  rw [card_centralizer_conj, hC, hst.card_Mf] at hdvd
  norm_num at hdvd

end Not13

section Y0

theorem Y0Set_one : (1 : GL (Fin 3) (ZMod 3)) ∈ Y0Set := by
  change ((1 : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧ _
  simp

theorem Y0Set_mul {g h : GL (Fin 3) (ZMod 3)} (hg : g ∈ Y0Set) (hh : h ∈ Y0Set) :
    g * h ∈ Y0Set := by
  obtain ⟨g01, g02, g10, g20, g00⟩ := hg
  obtain ⟨h01, h02, h10, h20, h00⟩ := hh
  change ((g * h : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) 0 1 = 0 ∧ _
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_three, g01, g02, g10, g20, h01, h02,
    h10, h20, zero_mul, mul_zero, add_zero, zero_add]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · simp
  · simp
  · linear_combination (h 0 0) * g00 + (g 1 1 * g 2 2 - g 1 2 * g 2 1) * h00

theorem Y0Set_pow {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ Y0Set) (k : ℕ) : g ^ k ∈ Y0Set := by
  induction k with
  | zero => simpa using Y0Set_one
  | succ k ih => rw [pow_succ]; exact Y0Set_mul ih hg

theorem Y0Set_inv {g : GL (Fin 3) (ZMod 3)} (hg : g ∈ Y0Set) : g⁻¹ ∈ Y0Set := by
  have hpos : 0 < orderOf g := orderOf_pos g
  have h1 : g * g ^ (orderOf g - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  rw [inv_eq_of_mul_eq_one_right h1]
  exact Y0Set_pow hg _

@[expose] def Y0Subgroup : Subgroup (GL (Fin 3) (ZMod 3)) where
  carrier := Y0Set
  mul_mem' := fun {_ _} ha hb => Y0Set_mul ha hb
  one_mem' := Y0Set_one
  inv_mem' := fun {_} ha => Y0Set_inv ha

theorem lowBlock_det_ne (g : GL (Fin 3) (ZMod 3)) (hg : g ∈ Y0Set) :
    (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 1 * (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 2 -
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2 * (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1 ≠ 0 := by
  obtain ⟨g01, g02, g10, g20, g00⟩ := hg
  have hdet : (g : Matrix (Fin 3) (Fin 3) (ZMod 3)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp g.isUnit).ne_zero
  rw [Matrix.det_fin_three, g01, g02, g10, g20, g00] at hdet
  intro h
  apply hdet
  rw [h]
  ring

def blockMat (g : GL (Fin 3) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  Matrix.of ![![(g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 1, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2],
    ![(g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1, (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 2]]

theorem blockMat_det (g : GL (Fin 3) (ZMod 3)) :
    blockMat g 0 0 * blockMat g 1 1 - blockMat g 0 1 * blockMat g 1 0 =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 1 * (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 2 -
        (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 1 2 * (g : Matrix (Fin 3) (Fin 3) (ZMod 3)) 2 1 := by
  simp [blockMat]

theorem card_Y0Subgroup_le : Nat.card Y0Subgroup ≤ 48 := by
  let f : Y0Subgroup → {B : Matrix (Fin 2) (Fin 2) (ZMod 3) //
      B 0 0 * B 1 1 - B 0 1 * B 1 0 ≠ 0} := fun g =>
    ⟨blockMat (g : GL (Fin 3) (ZMod 3)), by
      rw [blockMat_det]
      exact lowBlock_det_ne (g : GL (Fin 3) (ZMod 3)) g.2⟩
  have hf : Function.Injective f := by
    intro g₁ g₂ h
    have hB := congrArg Subtype.val h
    have e11 : blockMat (g₁ : GL (Fin 3) (ZMod 3)) 0 0 = blockMat (g₂ : GL (Fin 3) (ZMod 3)) 0 0 :=
      congrFun (congrFun hB 0) 0
    have e12 : blockMat (g₁ : GL (Fin 3) (ZMod 3)) 0 1 = blockMat (g₂ : GL (Fin 3) (ZMod 3)) 0 1 :=
      congrFun (congrFun hB 0) 1
    have e21 : blockMat (g₁ : GL (Fin 3) (ZMod 3)) 1 0 = blockMat (g₂ : GL (Fin 3) (ZMod 3)) 1 0 :=
      congrFun (congrFun hB 1) 0
    have e22 : blockMat (g₁ : GL (Fin 3) (ZMod 3)) 1 1 = blockMat (g₂ : GL (Fin 3) (ZMod 3)) 1 1 :=
      congrFun (congrFun hB 1) 1
    simp only [blockMat, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_fin_one] at e11 e12 e21 e22
    have hg₁ : (g₁ : GL (Fin 3) (ZMod 3)) ∈ Y0Set := g₁.2
    have hg₂ : (g₂ : GL (Fin 3) (ZMod 3)) ∈ Y0Set := g₂.2
    obtain ⟨g₁01, g₁02, g₁10, g₁20, g₁00⟩ := hg₁
    obtain ⟨g₂01, g₂02, g₂10, g₂20, g₂00⟩ := hg₂
    apply Subtype.ext
    apply Units.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp_all [blockMat]
  calc Nat.card Y0Subgroup ≤ Nat.card {B : Matrix (Fin 2) (Fin 2) (ZMod 3) //
        B 0 0 * B 1 1 - B 0 1 * B 1 0 ≠ 0} := Nat.card_le_card_of_injective f hf
    _ = 48 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      decide

end Y0

section DetH

open scoped IsMulCommutative

variable {H H₁ H₂ M₁ Pb W₁ Mf : Subgroup G} {e : Fin 6 → G} {t' : G}

noncomputable def chiDet [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁)) :
    Subgroup.normalizer (M₁ : Set G) →* ZMod 3 where
  toFun x := (rhoMat b x).det
  map_one' := by simp [rhoMat_one]
  map_mul' x y := by simp [rhoMat_mul, Matrix.det_mul]

theorem zmod3_cube_eq_one {y : ZMod 3} (h : y ^ 3 = 1) : y = 1 := by
  revert h
  revert y
  decide

theorem det_rho_H₂ [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁)) (h : G) (hh : h ∈ H₂) :
    (rhoMat b ⟨h, H₂_le_normalizer_M₁ hlet hv hh⟩).det = 1 := by
  let K : Subgroup G := (chiDet b).ker.map (Subgroup.normalizer (M₁ : Set G)).subtype
  have hK : H₂ ≤ K := by
    rw [← hlet.gen₂]
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    have hgN : g ∈ Subgroup.normalizer (M₁ : Set G) := by
      rw [← hlet.gen₂] at *
      exact H₂_le_normalizer_M₁ hlet hv (Subgroup.subset_closure (by simpa using hg))
    refine Subgroup.mem_map.mpr ⟨⟨g, hgN⟩, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    show (rhoMat b ⟨g, hgN⟩).det = 1
    have hcube : g ^ 3 = 1 := by
      rcases hg with rfl | rfl
      · exact (hlet_cube hlet).2.2.1
      · exact (hlet_cube hlet).2.2.2
    have hx3 : (chiDet b ⟨g, hgN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨g, hgN⟩ : Subgroup.normalizer (M₁ : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using hcube)
      rw [this, map_one]
    exact zmod3_cube_eq_one hx3
  obtain ⟨x, hx, hxh⟩ := Subgroup.mem_map.mp (hK hh)
  have hxh' : x = ⟨h, H₂_le_normalizer_M₁ hlet hv hh⟩ := Subtype.ext hxh
  subst hxh'
  exact MonoidHom.mem_ker.mp hx

theorem zOf_mul_self (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    zOf e * zOf e = 1 := by
  have h := pow_orderOf_eq_one (zOf e)
  rw [orderOf_zOf hone hlet, pow_two] at h
  exact h

theorem zOf_inv_eq (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) :
    (zOf e)⁻¹ = zOf e :=
  inv_eq_of_mul_eq_one_right (zOf_mul_self hone hlet)

theorem mem_normalizer_of_conj {g : G} {M : Subgroup G} (h1 : ∀ m ∈ M, g * m * g⁻¹ ∈ M)
    (h2 : ∀ m ∈ M, g⁻¹ * m * g⁻¹⁻¹ ∈ M) : g ∈ Subgroup.normalizer (M : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact h1 x hx
  · intro hx
    have h := h2 _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h
    exact h

theorem zOf_mem_normalizer_M₁ (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) : zOf e ∈ Subgroup.normalizer (M₁ : Set G) := by
  have hinv := zOf_inv_eq hone hlet
  refine mem_normalizer_of_conj (zOf_conj_M₁ hone hlet hv) ?_
  intro m hm
  rw [hinv]
  exact zOf_conj_M₁ hone hlet hv m hm

theorem e4_mem_normalizer_M₁ (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁) :
    e 4 ∈ Subgroup.normalizer (M₁ : Set G) := by
  have hinv : (e 4)⁻¹ = e 4 := inv_eq_of_mul_eq_one_right (e4_sq hlet)
  refine mem_normalizer_of_conj hv.conj_t ?_
  intro m hm
  rw [hinv]
  exact hv.conj_t m hm

theorem conj_H_Dg (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) [IsMulCommutative M₁] {h : G} (hh : h ∈ H)
    (hn : h ∈ Subgroup.normalizer (M₁ : Set G)) (x : G)
    (hx : x ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    h * x * h⁻¹ ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) := by
  rw [mem_Dg] at hx ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hn x).mp hx.1, ?_⟩
  have hzh : zOf e * h = h * zOf e := (zOf_central hone hlet h hh).symm
  have e1 : zOf e * (h * x * h⁻¹) * (zOf e)⁻¹ = (zOf e * h) * x * (zOf e * h)⁻¹ := by group
  have e2 : h * zOf e * x * (h * zOf e)⁻¹ = h * (zOf e * x * (zOf e)⁻¹) * h⁻¹ := by group
  rw [e1, hzh, e2, hx.2]
  group

theorem rho_block [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hv : VertexCore e H (e 0) H₂ M₁)
    (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (n : Subgroup.normalizer (M₁ : Set G)) (hnH : (n : G) ∈ H) (k : ℤ)
    (hk : (n : G) * e 0 * (n : G)⁻¹ = e 0 ^ k) :
    rhoMat b n 0 1 = 0 ∧ rhoMat b n 0 2 = 0 ∧ rhoMat b n 1 0 = 0 ∧ rhoMat b n 2 0 = 0 ∧
      rhoMat b n 0 0 = (k : ZMod 3) := by
  have hD : ∀ x ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv), (n : G) * x * (n : G)⁻¹ ∈
      Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv) :=
    fun x hx => conj_H_Dg hone hlet hv hnH n.2 x hx
  obtain ⟨r1, r2⟩ := rhoMat_row0 hone hlet hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD n hD
  have c := rhoMat_col0 hv b hb0 n k hk
  refine ⟨r1, r2, ?_, ?_, ?_⟩
  · rw [c 1]; simp
  · rw [c 2]; simp
  · rw [c 0]; simp

theorem rho_H₂_mem_Y0 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    {h : G} (hh : h ∈ H₂) :
    rhoGL b ⟨h, H₂_le_normalizer_M₁ hlet hv hh⟩ ∈ Y0Set := by
  have hcent := Subgroup.mem_centralizer_iff.mp (H₂_le_cent_e0 hlet hh) (e 0) (Set.mem_singleton _)
  have hk : h * e 0 * h⁻¹ = e 0 ^ (1 : ℤ) := by
    rw [zpow_one, ← hcent, mul_inv_cancel_right]
  obtain ⟨r01, r02, r10, r20, r00⟩ := rho_block hone hlet hv hst b w d hwM hdM hb0 hb1 hb2
    hwD hdD ⟨h, H₂_le_normalizer_M₁ hlet hv hh⟩ (hone.le_two hh) 1 hk
  have hdet := det_rho_H₂ hone hlet hv b h hh
  rw [Matrix.det_fin_three, r01, r02, r10, r20, r00] at hdet
  unfold Y0Set
  simp only [Set.mem_setOf_eq, rhoGL_val]
  refine ⟨r01, r02, r10, r20, ?_⟩
  rw [r00]
  push_cast at hdet ⊢
  linear_combination -hdet

theorem zmod3_sl2_involution : ∀ a b c d : ZMod 3, a * d - b * c = 1 → a * a + b * c = 1 →
    a * b + b * d = 0 → c * a + d * c = 0 → c * b + d * d = 1 →
    (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) := by
  decide

theorem zmod3_trace_t : ∀ a d : ZMod 3, -1 + a + d = -1 + -a + -d → a + d = 0 := by decide

theorem zmod3_det_t : ∀ a b c d : ZMod 3, a * a + b * c = 1 → a + d = 0 →
    a * d - b * c = -1 := by decide

theorem rho_z_block [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 0 0 = 1 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 0 1 = 0 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 0 2 = 0 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 1 0 = 0 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 2 0 = 0 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 1 1 = -1 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 2 2 = -1 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 1 2 = 0 ∧
      rhoMat b ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩ 2 1 = 0 := by
  set nz : Subgroup.normalizer (M₁ : Set G) := ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩
    with hnz
  have hcent := Subgroup.mem_centralizer_iff.mp (zOf_mem_cent_e0 hone hlet) (e 0)
    (Set.mem_singleton _)
  have hk : zOf e * e 0 * (zOf e)⁻¹ = e 0 ^ (1 : ℤ) := by
    rw [zpow_one, ← hcent, mul_inv_cancel_right]
  have hzH : zOf e ∈ H := zOf_mem_H hone hlet
  obtain ⟨r01, r02, r10, r20, r00⟩ := rho_block hone hlet hv hst b w d hwM hdM hb0 hb1 hb2
    hwD hdD nz hzH 1 hk
  have hdet := det_rho_H₂ hone hlet hv b (zOf e) ((zOf_mem_inf hlet).2)
  set M := rhoMat b nz with hM
  have hMM : M * M = 1 := by
    rw [hM, ← rhoMat_mul, show nz * nz = 1 from Subtype.ext (zOf_mul_self hone hlet), rhoMat_one]
  have hdetM : M 1 1 * M 2 2 - M 1 2 * M 2 1 = 1 := by
    have h := hdet
    simp [Matrix.det_fin_three, r01, r02, r10, r20, r00] at h
    linear_combination h
  have e11 : M 1 1 * M 1 1 + M 1 2 * M 2 1 = 1 := by
    have h := congrFun (congrFun hMM 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, r01, r02, r10, r20, r00] at h
    linear_combination h
  have e12 : M 1 1 * M 1 2 + M 1 2 * M 2 2 = 0 := by
    have h := congrFun (congrFun hMM 1) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, r01, r02, r10, r20, r00] at h
    linear_combination h
  have e21 : M 2 1 * M 1 1 + M 2 2 * M 2 1 = 0 := by
    have h := congrFun (congrFun hMM 2) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, r01, r02, r10, r20, r00] at h
    linear_combination h
  have e22 : M 2 1 * M 1 2 + M 2 2 * M 2 2 = 1 := by
    have h := congrFun (congrFun hMM 2) 2
    simp [Matrix.mul_apply, Fin.sum_univ_three, r01, r02, r10, r20, r00] at h
    linear_combination h
  rcases zmod3_sl2_involution _ _ _ _ hdetM e11 e12 e21 e22 with ⟨a1, b1, c1, d1⟩ | ⟨a1, b1, c1, d1⟩
  ·
    exfalso
    have hone' : rhoGL b nz = 1 := by
      apply Units.ext
      rw [Units.val_one, rhoGL_val, ← hM]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [r01, r02, r10, r20, r00, a1, b1, c1, d1]
    have hzM : zOf e ∈ M₁ := mem_of_rho_eq_one hone hlet hv hst b nz hone'
    have hzp : zOf e ∈ Subgroup.zpowers (e 0) := by
      rw [← hv.inf_H]
      exact ⟨hzM, hzH⟩
    have hz1 : zOf e ∈ Subgroup.zpowers (e 0) ⊓ H₂ := ⟨hzp, (zOf_mem_inf hlet).2⟩
    rw [hF.disj₁, Subgroup.mem_bot] at hz1
    exact zOf_ne_one hone hlet hz1
  · have h00 : M 0 0 = 1 := by rw [r00]; simp
    exact ⟨h00, r01, r02, r10, r20, a1, d1, b1, c1⟩

theorem rho_t_mem_Y0 [Finite G] [IsMulCommutative M₁] [Module (ZMod 3) (Additive M₁)]
    (hone : G23One H H₁ H₂) (hlet : HLetters H H₁ H₂ e) (hF : HFacts H H₁ H₂ e)
    (hv : VertexCore e H (e 0) H₂ M₁) (hst : B27State e M₁ Pb W₁ Mf t')
    (b : Module.Basis (Fin 3) (ZMod 3) (Additive M₁))
    (w d : G) (hwM : w ∈ M₁) (hdM : d ∈ M₁)
    (hb0 : b 0 = Additive.ofMul (⟨e 0, e0_mem_M₁ hv⟩ : M₁))
    (hb1 : b 1 = Additive.ofMul (⟨w, hwM⟩ : M₁)) (hb2 : b 2 = Additive.ofMul (⟨d, hdM⟩ : M₁))
    (hwD : w ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv))
    (hdD : d ∈ Dg (zOf e) M₁ (zOf_conj_M₁ hone hlet hv)) :
    rhoGL b ⟨e 4, e4_mem_normalizer_M₁ hlet hv⟩ ∈ Y0Set := by
  obtain ⟨z00, z01, z02, z10, z20, z11, z22, z12, z21⟩ :=
    rho_z_block hone hlet hF hv hst b w d hwM hdM hb0 hb1 hb2 hwD hdD
  have hkt : (e 4 : G) * e 0 * (e 4)⁻¹ = e 0 ^ (-1 : ℤ) := by
    rw [zpow_neg_one]
    exact e4_conj_e0 hone hlet hF hv
  obtain ⟨t01, t02, t10, t20, t00⟩ := rho_block hone hlet hv hst b w d hwM hdM hb0 hb1 hb2
    hwD hdD ⟨e 4, e4_mem_normalizer_M₁ hlet hv⟩ (e4_mem_H hlet) (-1) hkt
  obtain ⟨g, hg, hgc⟩ := hF.conj_t₂
  have hgN : g ∈ Subgroup.normalizer (M₁ : Set G) := by
    have hsup : H₂ ⊔ Subgroup.zpowers (e 4) ≤ Subgroup.normalizer (M₁ : Set G) :=
      sup_le (H₂_le_normalizer_M₁ hlet hv) (Subgroup.zpowers_le.mpr (e4_mem_normalizer_M₁ hlet hv))
    exact hsup hg
  set nt : Subgroup.normalizer (M₁ : Set G) := ⟨e 4, e4_mem_normalizer_M₁ hlet hv⟩ with hnt
  set nz : Subgroup.normalizer (M₁ : Set G) := ⟨zOf e, zOf_mem_normalizer_M₁ hone hlet hv⟩
    with hnz
  set ng : Subgroup.normalizer (M₁ : Set G) := ⟨g, hgN⟩ with hng
  have hrel : ng * nt = (nt * nz) * ng := Subtype.ext (by
    show g * e 4 = e 4 * zOf e * g
    rw [← hgc]
    group)
  have hAB : rhoMat b ng * rhoMat b nt = rhoMat b nt * rhoMat b nz * rhoMat b ng := by
    rw [← rhoMat_mul, ← rhoMat_mul, ← rhoMat_mul, hrel]
  have hAinv : rhoMat b ng⁻¹ * rhoMat b ng = 1 := by
    rw [← rhoMat_mul, inv_mul_cancel, rhoMat_one]
  have hAinv' : rhoMat b ng * rhoMat b ng⁻¹ = 1 := by
    rw [← rhoMat_mul, mul_inv_cancel, rhoMat_one]
  have htr : (rhoMat b nt).trace = (rhoMat b nt * rhoMat b nz).trace := by
    have h1 : rhoMat b nt * rhoMat b nz = rhoMat b ng * rhoMat b nt * rhoMat b ng⁻¹ := by
      rw [hAB, Matrix.mul_assoc, hAinv', Matrix.mul_one]
    rw [h1, Matrix.trace_mul_cycle, hAinv, Matrix.one_mul]
  have hBC00 : (rhoMat b nt * rhoMat b nz) 0 0 = -1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, t00, t01, t02, z00, z10, z20]
  have hBC11 : (rhoMat b nt * rhoMat b nz) 1 1 = -rhoMat b nt 1 1 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, t10, z01, z11, z21]
  have hBC22 : (rhoMat b nt * rhoMat b nz) 2 2 = -rhoMat b nt 2 2 := by
    simp [Matrix.mul_apply, Fin.sum_univ_three, t20, z02, z22, z12]
  have htrace : rhoMat b nt 1 1 + rhoMat b nt 2 2 = 0 := by
    rw [Matrix.trace_fin_three, Matrix.trace_fin_three, hBC00, hBC11, hBC22, t00] at htr
    exact zmod3_trace_t _ _ htr
  have hB2 : rhoMat b nt * rhoMat b nt = 1 := by
    rw [← rhoMat_mul, show nt * nt = 1 from Subtype.ext (e4_sq hlet), rhoMat_one]
  have hB11 := congrFun (congrFun hB2 1) 1
  simp [Matrix.mul_apply, Fin.sum_univ_three, t01, t10] at hB11
  unfold Y0Set
  simp only [Set.mem_setOf_eq, rhoGL_val]
  refine ⟨t01, t02, t10, t20, ?_⟩
  rw [t00]
  push_cast
  exact (zmod3_det_t (rhoMat b nt 1 1) (rhoMat b nt 1 2) (rhoMat b nt 2 1) (rhoMat b nt 2 2)
    (by linear_combination hB11) htrace).symm

end DetH

section MOne

variable {H H₁ H₂ M : Subgroup G} {e : Fin 6 → G}

theorem card_M₁ {M₁ M₂ Pb Np Nm : Subgroup G} (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm)
    (hPb : Nat.card Pb = 27) : Nat.card M₁ = 27 := by
  rcases hL.cor.cases with h | h | h
  · exact absurd (h.2.symm.trans hPb) (by norm_num)
  · exact h.1
  · exact absurd (h.2.symm.trans hPb) (by norm_num)

theorem card_cent_e0 [Finite G] {M₁ M₂ Pb Np Nm : Subgroup G} (hone : G23One H H₁ H₂)
    (hL : Local3 e H H₁ H₂ M₁ M₂ Pb Np Nm) (hPb : Nat.card Pb = 27) :
    Nat.card (Subgroup.centralizer {e 0}) = 648 := by
  rw [card_of_centComplement hL.v₁.compl, card_M₁ hL hPb, card_H₂ hone]

end MOne

end CFSG.GH74.QTGen4.Recog.G23.P7

end
