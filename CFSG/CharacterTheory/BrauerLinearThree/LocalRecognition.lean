module

public import CFSG.CharacterTheory.BrauerLinearThree.RootAnalysis
public import CFSG.LinearAlgebra.DesarguesianPlanes.RootRecognition

public section

namespace CFSG.BrauerLinearThree

open Matrix CFSG.DesarguesianPlanes
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hcard : Nat.card G * Nat.card Z =
    Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1))
  (hcent : ∀ Q : G, Q ≠ 1 → Q ^ ringChar F = 1 →
    Nat.card (Subgroup.centralizer ({Q} : Set G)) * Nat.card Z ∣
        Nat.card F ^ 3 * (Nat.card F - 1) ∧
      ((∀ g : G, g * Q * g⁻¹ ∉ rootX₁ φ) →
        Nat.card (Subgroup.centralizer ({Q} : Set G)) ∣ Nat.card F ^ 3))

section PCore

variable {Y : G} (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)
  (N : Subgroup G) (hN : N ≤ Subgroup.centralizer {rootUp φ 1})
  (hNp : IsPGroup (ringChar F) N)
  (hNall : ∀ x ∈ Subgroup.centralizer ({rootUp φ 1} : Set G), ∀ k : ℕ,
    x ^ (ringChar F ^ k) = 1 → x ∈ N)

include hZ hZodd h2 hJ hY₁ hY₂ hcard hcent hN hNp hNall in
theorem brauerRootRelations_of_pcore [Finite G] [IsSimpleGroup G] : BrauerRootRelations φ Y := by
  classical
  have hp : (ringChar F).Prime := CharP.char_is_prime F _
  have : Fact (ringChar F).Prime := ⟨hp⟩
  obtain ⟨f, hf, hq⟩ := exists_card_eq_ringChar_pow F
  have hq0 : 0 < Nat.card F := Nat.card_pos
  have hT : ∀ i j, ∀ t, IsTorus φ t → (rootSub φ Y i j).map (conjHom t) = rootSub φ Y i j :=
    fun i j t ht => torus_map_rootSub φ hZ hZodd h2 hJ hY₁ hY₂ ht i j
  have hC3 := cube_dvd_card_centralizer_rootUp_one φ hZ hZodd h2 hJ hY₁ hY₂ hcard N hN hNp hNall
  have hNcard : Nat.card N = Nat.card F ^ 3 := by
    apply Nat.dvd_antisymm (card_dvd_cube_of_isPGroup hZ hcard hNp)
    have h3 : ringChar F ^ (f * 3) ∣
        Nat.card (Subgroup.centralizer ({rootUp φ 1} : Set G)) := by
      rwa [hq, ← pow_mul] at hC3
    obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime (ringChar F) h3
    have hK'p : IsPGroup (ringChar F) K' := IsPGroup.of_card hK'
    have hle : K'.map (Subgroup.centralizer ({rootUp φ 1} : Set G)).subtype ≤ N := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨k, hk⟩ := hK'p ⟨y, hy⟩
      apply hNall _ y.2 k
      have := congrArg
        (fun w : K' => ((w : Subgroup.centralizer ({rootUp φ 1} : Set G)) : G)) hk
      simpa using this
    have := Subgroup.card_dvd_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hK', pow_mul,
      ← hq] at this
  have hN0 : (N ⊓ Subgroup.centralizer {J} : Subgroup G) = rootX₁ φ := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxN, hxJ⟩ := Subgroup.mem_inf.mp hx
      exact mem_rootX₁_of_mem_pcore φ hZ hZodd h2 N hN hNp hxN
        (Subgroup.mem_centralizer_singleton_iff.mp hxJ).symm
    · exact le_inf (rootX₁_le_pcore φ N hNall) (rootSub_01_le_centralizer φ (Y := Y))
  have hNid := card_eq_mul_of_isPGroup φ hZ hZodd h2 hJ N hNp
    (fun m hm => conj_J_mem_pcore φ N hN hNp hNall hm)
    (fun m hm => conj_invJ₁_mem_pcore φ N hN hNp hNall hm)
  rw [hN0, card_rootX₁ hZ, hNcard] at hNid
  have ha : Nat.card (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) ≤ Nat.card F := by
    rcases pcore_inf_invJ₁_le φ hZ hZodd h2 hJ hY₁ hY₂ N hN hNp hNall with hA | hA
    · rw [← card_rootSub_12 hZ (φ := φ) (Y := Y)]
      exact Subgroup.card_le_of_le hA
    · rw [← card_rootSub_21 hZ (φ := φ) (Y := Y)]
      exact Subgroup.card_le_of_le hA
  have hb : Nat.card (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) ≤ Nat.card F := by
    rcases pcore_inf_invJ₂_le φ hZ hZodd h2 hJ hY₁ hY₂ N hN hNp hNall with hA | hA
    · rw [← card_rootSub_20 hZ (φ := φ) (Y := Y)]
      exact Subgroup.card_le_of_le hA
    · rw [← card_rootSub_02 hZ (φ := φ) (Y := Y)]
      exact Subgroup.card_le_of_le hA
  have hab : Nat.card (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) *
      Nat.card (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) =
      Nat.card F * Nat.card F := by
    apply Nat.eq_of_mul_eq_mul_left hq0
    rw [← mul_assoc, ← hNid]
    ring
  have ha' : Nat.card (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) = Nat.card F := by
    have h1 : Nat.card F * Nat.card F ≤
        Nat.card (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) * Nat.card F := by
      rw [← hab]
      exact Nat.mul_le_mul_left _ hb
    have := Nat.le_of_mul_le_mul_right h1 hq0
    omega
  have hb' : Nat.card (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) = Nat.card F := by
    have h1 : Nat.card F * Nat.card F ≤
        Nat.card F * Nat.card (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) := by
      rw [← hab]
      exact Nat.mul_le_mul_right _ ha
    have := Nat.le_of_mul_le_mul_left h1 hq0
    omega
  have hcomm : ∀ i j, rootSub φ Y i j ≤ N → Commutes (rootSub φ Y 0 1) (rootSub φ Y i j) :=
    fun i j hle => commutes_rootX₁_of_commute_rootUp_one φ hZ (hT i j)
      (fun a ha => Subgroup.mem_centralizer_singleton_iff.mp (hN (hle ha)))
  have habel : Commutes (rootSub φ Y 0 1) (rootSub φ Y 1 2) → False := by
    intro h01
    have h12 : Commutes (rootSub φ Y 1 2) (rootSub φ Y 2 0) := by
      simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h01
    have h20 : Commutes (rootSub φ Y 2 0) (rootSub φ Y 0 1) := by
      simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h12
    obtain ⟨hle, hdvd⟩ :=
      sup_three_le_pcore_of_commutes φ hZ hZodd h2 hJ hY₁ hY₂ N hNp hNall h01 h20
    have hHN : (rootSub φ Y 0 1 ⊔ rootSub φ Y 1 2 ⊔ rootSub φ Y 2 0 : Subgroup G) = N :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hNcard]; exact Nat.le_of_dvd Nat.card_pos hdvd)
    have hc : Commutes (rootSub φ Y 0 1 ⊔ rootSub φ Y 1 2 ⊔ rootSub φ Y 2 0 : Subgroup G)
        (rootSub φ Y 0 1 ⊔ rootSub φ Y 1 2 ⊔ rootSub φ Y 2 0 : Subgroup G) :=
      commutes_sup (commutes_sup (comm_rootX₁ (φ := φ)) comm_rootSub_12 h01) comm_rootSub_20
        (commutes_sup_left h20.symm h12)
    rw [hHN] at hc
    exact false_of_pcore_comm φ hZ hZodd h2 hJ hcard hcent N hN hNp hNall hc hNcard
  have hJ₁eq : (N ⊓ Subgroup.centralizer {invJ₁ φ} : Subgroup G) = rootSub φ Y 2 1 := by
    rcases pcore_inf_invJ₁_le φ hZ hZodd h2 hJ hY₁ hY₂ N hN hNp hNall with hA | hA
    · exfalso
      have hEq := Subgroup.eq_of_le_of_card_ge hA (by rw [card_rootSub_12 hZ, ha'])
      exact habel (hcomm 1 2 (by rw [← hEq]; exact inf_le_left))
    · exact Subgroup.eq_of_le_of_card_ge hA (by rw [card_rootSub_21 hZ, ha'])
  have hJ₂eq : (N ⊓ Subgroup.centralizer {invJ₂ φ} : Subgroup G) = rootSub φ Y 0 2 := by
    rcases pcore_inf_invJ₂_le φ hZ hZodd h2 hJ hY₁ hY₂ N hN hNp hNall with hA | hA
    · exfalso
      have hEq := Subgroup.eq_of_le_of_card_ge hA (by rw [card_rootSub_20 hZ, hb'])
      have h02 := hcomm 2 0 (by rw [← hEq]; exact inf_le_left)
      have : Commutes (rootSub φ Y 1 2) (rootSub φ Y 0 1) := by
        simpa using commutes_succ hZ hZodd h2 hJ hY₁ hY₂ h02
      exact habel this.symm
    · exact Subgroup.eq_of_le_of_card_ge hA (by rw [card_rootSub_02 hZ, hb'])
  have h21N : rootSub φ Y 2 1 ≤ N := by rw [← hJ₁eq]; exact inf_le_left
  have h02N : rootSub φ Y 0 2 ≤ N := by rw [← hJ₂eq]; exact inf_le_left
  have hc21 := hcomm 2 1 h21N
  have hc02 := hcomm 0 2 h02N
  obtain ⟨hle', hdvd'⟩ := sup_three_le_pcore φ hZ hZodd h2 hJ N hNp hNall (rootSub φ Y 0 1)
    (rootSub φ Y 2 1) (rootSub φ Y 0 2) (rootSub_01_le_centralizer φ)
    (rootSub_21_le_centralizer φ hY₁) (rootSub_02_le_centralizer φ hY₁ hY₂) (card_rootX₁ hZ)
    (card_rootSub_21 hZ) (card_rootSub_02 hZ) (pow_ringChar_of_mem_rootSub_01 φ)
    (pow_ringChar_of_mem_rootSub_21 φ) (pow_ringChar_of_mem_rootSub_02 φ) (hT 0 1) (hT 2 1)
    (hT 0 2) (fun x hx => hN (rootX₁_le_pcore φ N hNall hx)) (fun x hx => hN (h21N hx))
    (fun x hx => hN (h02N hx))
  have hH'N : (rootSub φ Y 0 1 ⊔ rootSub φ Y 2 1 ⊔ rootSub φ Y 0 2 : Subgroup G) = N :=
    Subgroup.eq_of_le_of_card_ge hle' (by rw [hNcard]; exact Nat.le_of_dvd Nat.card_pos hdvd')
  have hNX : Commutes (rootSub φ Y 0 1) N := by
    rw [← hH'N]
    exact (commutes_sup_left (commutes_sup_left (comm_rootX₁ (φ := φ)) hc21.symm)
      hc02.symm).symm
  have hNodd : Odd (Nat.card N) := by
    rw [hNcard]
    exact (odd_card_F h2).pow
  have hcommIn : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ rootX₁ φ :=
    commutatorElement_mem_of_fixed_le (M := N) (N := rootX₁ φ) hNodd (J_mul_self hJ)
      (fun x hx => conj_J_mem_pcore φ N hN hNp hNall hx) hNX
      (fun n hn => commute_J_of_mem_rootX₁ hn)
      (fun x hx hxJ => mem_rootX₁_of_mem_pcore φ hZ hZodd h2 N hN hNp hx hxJ)
  refine ⟨hc21, hc02, fun a ha b hb => hcommIn a (h21N ha) b (h02N hb), ?_⟩
  by_contra hcon
  have h2102 : Commutes (rootSub φ Y 2 1) (rootSub φ Y 0 2) := by
    intro a ha b hb
    by_contra hab'
    exact hcon ⟨a, ha, b, hb, fun h => hab' (commutatorElement_eq_one_iff_commute.mp h)⟩
  have hc : Commutes (rootSub φ Y 0 1 ⊔ rootSub φ Y 2 1 ⊔ rootSub φ Y 0 2 : Subgroup G)
      (rootSub φ Y 0 1 ⊔ rootSub φ Y 2 1 ⊔ rootSub φ Y 0 2 : Subgroup G) :=
    commutes_sup (commutes_sup (comm_rootX₁ (φ := φ)) comm_rootSub_21 hc21) comm_rootSub_02
      (commutes_sup_left hc02 h2102)
  rw [hH'N] at hc
  exact false_of_pcore_comm φ hZ hZodd h2 hJ hcard hcent N hN hNp hNall hc hNcard

end PCore

include hZ hZodd h2 hJ hcard hcent in
theorem brauerRootRelations_of_local [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) :
    ∃ Y : G, Y⁻¹ * J * Y = invJ₁ φ ∧ Y⁻¹ * invJ₁ φ * Y = invJ₂ φ ∧ BrauerRootRelations φ Y := by
  obtain ⟨Y, hY₁, hY₂⟩ := exists_Y φ hZ hZodd h2 hJ hnonab
  obtain ⟨N, hN, hNp, hNall⟩ := exists_pcore_centralizer φ hZ hZodd h2 hJ hcard hcent
    (rootUp_one_ne_one φ hZ) (rootUp_pow_ringChar φ 1)
  exact ⟨Y, hY₁, hY₂,
    brauerRootRelations_of_pcore φ hZ hZodd h2 hJ hcard hcent hY₁ hY₂ N hN hNp hNall⟩

omit [Finite F] in
theorem card_SL_three [Finite F] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 3) F) =
      Nat.card F ^ 3 * (Nat.card F ^ 3 - 1) * (Nat.card F ^ 2 - 1) := by
  let : Fintype F := Fintype.ofFinite F
  have h := Matrix.card_SL_mul_card_units (n := Fin 3) (R := F)
  rw [Matrix.card_GL_field, Nat.card_units, Fin.prod_univ_three, ← Nat.card_eq_fintype_card] at h
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at h
  have hq : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < Nat.card F - 1)
  rw [h]
  have h1 : 1 ≤ Nat.card F := by omega
  have h2' : Nat.card F ≤ Nat.card F ^ 3 := Nat.le_self_pow (by norm_num) _
  have h3 : Nat.card F ^ 2 ≤ Nat.card F ^ 3 := Nat.pow_le_pow_right h1 (by norm_num)
  have h4 : 1 ≤ Nat.card F ^ 3 := Nat.one_le_pow _ _ h1
  have h5 : 1 ≤ Nat.card F ^ 2 := Nat.one_le_pow _ _ h1
  zify [h1, h2', h3, h4, h5]
  ring

include hZ hZodd h2 hJ hcard hcent in
theorem statedClassicalModel_of_local [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (p f : ℕ) (hp : p.Prime) (hf : 1 ≤ f)
    (hF : Nat.card F = p ^ f) : CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSL 3 p f := by
  obtain ⟨Y, hY₁, hY₂, hR⟩ := brauerRootRelations_of_local φ hZ hZodd h2 hJ hcard hcent hnonab
  refine statedClassicalModel_of_brauerRootRelations hnonab hZ hZodd h2 hJ hY₁ hY₂ hR ?_ p f hp hf
    hF
  rw [card_SL_three]
  calc Nat.card G ≤ Nat.card G * Nat.card Z := Nat.le_mul_of_pos_right _ Nat.card_pos
    _ = _ := hcard

end CFSG.BrauerLinearThree
