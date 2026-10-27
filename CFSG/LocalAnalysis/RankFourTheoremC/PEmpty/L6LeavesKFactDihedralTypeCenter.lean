module

public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType

open Subgroup

theorem mul_mem_of_notMem_of_index_two_aux {G : Type} [Group G] {K : Subgroup G}
    (hK : K.index = 2) {x y : G} (hx : x ∉ K) (hy : y ∉ K) : x * y ∈ K := by
  obtain ⟨a, -, hall⟩ := Subgroup.index_eq_two_iff_exists_notMem_and.mp hK
  have hz : ∀ z : G, z ∉ K → z * a ∈ K := fun z hz' => (hall z).resolve_right hz'
  have hy' : y⁻¹ ∉ K := fun h => hy (by simpa using K.inv_mem h)
  have h1 : x * a ∈ K := hz x hx
  have h2 : y⁻¹ * a ∈ K := hz y⁻¹ hy'
  have h3 : x * y = (x * a) * (y⁻¹ * a)⁻¹ := by simp [mul_assoc]
  rw [h3]
  exact K.mul_mem h1 (K.inv_mem h2)

theorem commutative_of_four_abelian_index_two {H : Type} [Group H] [Finite H]
    (N : Fin 4 → Subgroup H) (hab : ∀ k, ∀ a ∈ N k, ∀ b ∈ N k, a * b = b * a)
    (hidx : ∀ k, (N k).index = 2) (hinj : Function.Injective N) :
    ∀ a b : H, a * b = b * a := by
  classical
  by_contra hnab
  have hnab' : ¬ ∀ a b : H, a * b = b * a := hnab
  haveI : ∀ k, (N k).Normal := fun k => Subgroup.normal_of_index_eq_two (hidx k)
  have hcov : ∀ i j, i ≠ j → ∀ y : H, ∃ a ∈ N i, ∃ b ∈ N j, y = a * b := by
    intro i j hij y
    have hne : N j ≠ N i := fun h => hij (hinj h).symm
    have hnle : ¬ N j ≤ N i := by
      intro hle
      have hcoat : IsCoatom (N j) :=
        Subgroup.isCoatom_of_index_prime (by rw [hidx j]; exact Nat.prime_two)
      have hlt : N j < N i := lt_of_le_of_ne hle hne
      have htop : N i = ⊤ := hcoat.2 (N i) hlt
      have h2 := hidx i
      rw [htop, Subgroup.index_top] at h2
      exact absurd h2 (by norm_num)
    obtain ⟨b₀, hb₀j, hb₀i⟩ := SetLike.not_le_iff_exists.mp hnle
    by_cases hy : y ∈ N i
    · exact ⟨y, hy, 1, (N j).one_mem, (mul_one y).symm⟩
    · have h1 : y * b₀⁻¹ ∈ N i :=
        mul_mem_of_notMem_of_index_two_aux (hidx i) hy
          (fun h => hb₀i (by simpa using (N i).inv_mem h))
      exact ⟨y * b₀⁻¹, h1, b₀, hb₀j, by simp⟩
  have hsup : ∀ i j, i ≠ j → N i ⊔ N j = ⊤ := by
    intro i j hij
    refine eq_top_iff.mpr fun y _ => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hcov i j hij y
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right hb)
  have hD : ∀ i j, i ≠ j → (N i ⊓ N j).index = 4 := by
    intro i j hij
    have h1 : (N i ⊓ N j).relIndex (N i) * (N i).index = (N i ⊓ N j).index :=
      Subgroup.relIndex_mul_index inf_le_left
    have h2 : (N i ⊓ N j).relIndex (N i) = (N j).relIndex (N i) :=
      Subgroup.inf_relIndex_left (N i) (N j)
    have h3 : (N j).relIndex (N i) = 2 := by
      have h := Subgroup.relIndex_sup_right (H := N i) (K := N j)
      rw [hsup i j hij, Subgroup.relIndex_top_right, hidx j] at h
      exact h.symm
    rw [h2, h3, hidx i] at h1
    omega
  set Z : Subgroup H := Subgroup.center H with hZdef
  have hDZ : ∀ i j, i ≠ j → N i ⊓ N j ≤ Z := by
    intro i j hij x hx
    obtain ⟨hxi, hxj⟩ := Subgroup.mem_inf.mp hx
    rw [hZdef, Subgroup.mem_center_iff]
    intro g
    obtain ⟨a, ha, b, hb, hg⟩ := hcov i j hij g
    have hax : a * x = x * a := hab i a ha x hxi
    have hbx : b * x = x * b := hab j b hb x hxj
    rw [hg]
    calc a * b * x = a * (b * x) := by rw [mul_assoc]
      _ = a * (x * b) := by rw [hbx]
      _ = (a * x) * b := by rw [mul_assoc]
      _ = (x * a) * b := by rw [hax]
      _ = x * (a * b) := by rw [mul_assoc]
  have hZ4 : Z.index = 4 := by
    have hdvd : Z.index ∣ 2 ^ 2 := by
      have h := Subgroup.relIndex_mul_index (hDZ 0 1 (by decide))
      rw [hD 0 1 (by decide)] at h
      exact Dvd.intro_left _ h
    obtain ⟨i, hi, hZi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    interval_cases i
    ·
      exfalso
      have hZtop : Z = ⊤ := Subgroup.index_eq_one.mp (by simpa using hZi)
      apply hnab'
      intro a b
      have ha : a ∈ Z := by rw [hZtop]; exact Subgroup.mem_top a
      rw [hZdef, Subgroup.mem_center_iff] at ha
      exact (ha b).symm
    ·
      exfalso
      have hcard : Nat.card (H ⧸ Z) = 2 := by
        have h2 : Z.index = 2 := by simpa using hZi
        exact h2
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      haveI : IsCyclic (H ⧸ Z) := isCyclic_of_prime_card hcard
      have hcomm : IsMulCommutative H :=
        MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center (QuotientGroup.mk' Z)
          (le_of_eq ((QuotientGroup.ker_mk' Z).trans hZdef))
      exact hnab' fun a b => hcomm.is_comm.comm a b
    · simpa using hZi
  have hDeq : ∀ i j, i ≠ j → N i ⊓ N j = Z := by
    intro i j hij
    apply le_antisymm (hDZ i j hij)
    have h := Subgroup.relIndex_mul_index (hDZ i j hij)
    rw [hD i j hij, hZ4] at h
    have h1 : (N i ⊓ N j).relIndex Z = 1 := by omega
    exact Subgroup.relIndex_eq_one.mp h1
  have hZle : ∀ k, Z ≤ N k := by
    intro k
    fin_cases k
    · rw [← hDeq 0 1 (by decide)]; exact inf_le_left
    · rw [← hDeq 1 0 (by decide)]; exact inf_le_left
    · rw [← hDeq 2 0 (by decide)]; exact inf_le_left
    · rw [← hDeq 3 0 (by decide)]; exact inf_le_left
  have hcardH : Nat.card H = 4 * Nat.card Z := by
    have h := Subgroup.card_mul_index Z
    rw [hZ4] at h
    omega
  have hcardN : ∀ k, Nat.card (N k) = 2 * Nat.card Z := by
    intro k
    have h := Subgroup.card_mul_index (N k)
    rw [hidx k, hcardH] at h
    omega
  set AS : Fin 4 → Set H := fun k => (N k : Set H) \ (Z : Set H) with hAS
  have hZn : (Z : Set H).ncard = Nat.card Z := (Nat.card_coe_set_eq (Z : Set H)).symm
  have hNn : ∀ k, (N k : Set H).ncard = 2 * Nat.card Z := fun k => by
    rw [← Nat.card_coe_set_eq]
    exact hcardN k
  have hAScard : ∀ k, (AS k).ncard = (Z : Set H).ncard := by
    intro k
    have hsub : (Z : Set H) ⊆ (N k : Set H) := SetLike.coe_subset_coe.mpr (hZle k)
    have hu : (Z : Set H) ∪ AS k = (N k : Set H) := Set.union_diff_cancel hsub
    have hdisj : Disjoint (Z : Set H) (AS k) := Set.disjoint_sdiff_right
    have h := Set.ncard_union_eq hdisj
    rw [hu, hNn k] at h
    omega
  have hAS_disj : ∀ k l, k ≠ l → Disjoint (AS k) (AS l) := by
    intro k l hkl
    rw [Set.disjoint_left]
    intro x hxk hxl
    have hxk' : x ∈ N k ∧ x ∉ Z := hxk
    have hxl' : x ∈ N l ∧ x ∉ Z := hxl
    have hmem : x ∈ N k ⊓ N l := Subgroup.mem_inf.mpr ⟨hxk'.1, hxl'.1⟩
    rw [hDeq k l hkl] at hmem
    exact hxk'.2 hmem
  have hZpos : 0 < (Z : Set H).ncard := (Set.ncard_pos (Set.toFinite _)).mpr ⟨1, Z.one_mem⟩
  have hunion : ((AS 0 ∪ AS 1) ∪ AS 2 ∪ AS 3).ncard = 4 * (Z : Set H).ncard := by
    have d1 : Disjoint (AS 0) (AS 1) := hAS_disj 0 1 (by decide)
    have d2 : Disjoint (AS 0 ∪ AS 1) (AS 2) :=
      Set.disjoint_union_left.mpr ⟨hAS_disj 0 2 (by decide), hAS_disj 1 2 (by decide)⟩
    have d3 : Disjoint ((AS 0 ∪ AS 1) ∪ AS 2) (AS 3) :=
      Set.disjoint_union_left.mpr ⟨Set.disjoint_union_left.mpr
        ⟨hAS_disj 0 3 (by decide), hAS_disj 1 3 (by decide)⟩, hAS_disj 2 3 (by decide)⟩
    rw [Set.ncard_union_eq d3, Set.ncard_union_eq d2, Set.ncard_union_eq d1, hAScard,
      hAScard, hAScard, hAScard]
    omega
  have hsub_compl : (AS 0 ∪ AS 1) ∪ AS 2 ∪ AS 3 ⊆ (Z : Set H)ᶜ := by
    intro x hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact hx.2
    · exact hx.2
    · exact hx.2
    · exact hx.2
  have hcompl := Set.ncard_add_ncard_compl (Z : Set H)
  have hle := Set.ncard_le_ncard hsub_compl
  omega

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KDType
