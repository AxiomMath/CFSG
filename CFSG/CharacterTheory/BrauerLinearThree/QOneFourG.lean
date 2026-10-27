module

public import CFSG.CharacterTheory.BrauerLinearThree.QOneOrder
public import CFSG.CharacterTheory.BrauerLinearThree.FourGLocal

public section

namespace CFSG.BrauerLinearThree.QOne

open Matrix CFSG.DesarguesianPlanes

section Subgroup

variable {G : Type} [Group G] {K : Subgroup G}

theorem centralizer_singleton_eq_subgroupOf (x : K) :
    Subgroup.centralizer ({x} : Set K) =
      (Subgroup.centralizer ({(x : G)} : Set G)).subgroupOf K := by
  ext y
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

theorem card_subgroupOf_of_le {A : Subgroup G} (h : A ≤ K) :
    Nat.card (A.subgroupOf K) = Nat.card A :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

theorem card_centralizer_singleton_subgroup (x : K) :
    Nat.card (Subgroup.centralizer ({x} : Set K)) =
      Nat.card (Subgroup.centralizer ({(x : G)} : Set G) ⊓ K : Subgroup G) := by
  rw [centralizer_singleton_eq_subgroupOf, ← Subgroup.subgroupOf_map_subtype,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective K)]

theorem card_centralizer_singleton_subgroup_of_le (x : K)
    (h : Subgroup.centralizer ({(x : G)} : Set G) ≤ K) :
    Nat.card (Subgroup.centralizer ({x} : Set K)) =
      Nat.card (Subgroup.centralizer ({(x : G)} : Set G)) := by
  rw [centralizer_singleton_eq_subgroupOf, card_subgroupOf_of_le h]

theorem card_centralizer_closure_pair_subgroup (x y : K)
    (h : Subgroup.centralizer ({(x : G)} : Set G) ≤ K) :
    Nat.card (Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup K) : Set K)) =
      Nat.card (Subgroup.centralizer
        ((Subgroup.closure {(x : G), (y : G)} : Subgroup G) : Set G)) := by
  have hle : Subgroup.centralizer ({(x : G)} : Set G) ⊓ Subgroup.centralizer ({(y : G)} : Set G)
      ≤ K := inf_le_left.trans h
  have heq : Subgroup.centralizer ((Subgroup.closure {x, y} : Subgroup K) : Set K) =
      (Subgroup.centralizer ({(x : G)} : Set G) ⊓
        Subgroup.centralizer ({(y : G)} : Set G)).subgroupOf K := by
    rw [Subgroup.centralizer_closure, CFSG.Wreathed.BrauerWreathedOrder.centralizer_pair_eq,
      centralizer_singleton_eq_subgroupOf, centralizer_singleton_eq_subgroupOf]
    ext w
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [heq, card_subgroupOf_of_le hle, Subgroup.centralizer_closure,
    CFSG.Wreathed.BrauerWreathedOrder.centralizer_pair_eq]

theorem exists_wreath_subgroup [Finite G] (n : ℕ) (S : Sylow 2 G) (S₁ S₂ T : G)
    (hSK : (S : Subgroup G) ≤ K) (hgen : Subgroup.closure {S₁, S₂, T} = (S : Subgroup G))
    (hcard : Nat.card (S : Subgroup G) = 2 ^ (2 * n + 1)) (hS₁ : S₁ ^ 2 ^ n = 1)
    (hS₂ : S₂ ^ 2 ^ n = 1) (hT : T ^ 2 = 1) (hcomm : S₁ * S₂ = S₂ * S₁)
    (hconj : T⁻¹ * S₁ * T = S₂) :
    ∃ (S' : Sylow 2 K) (S₁' S₂' T' : K), (S₁' : G) = S₁ ∧ (S₂' : G) = S₂ ∧ (T' : G) = T ∧
      Subgroup.closure {S₁', S₂', T'} = (S' : Subgroup K) ∧
      Nat.card (S' : Subgroup K) = 2 ^ (2 * n + 1) ∧
      S₁' ^ 2 ^ n = 1 ∧ S₂' ^ 2 ^ n = 1 ∧ T' ^ 2 = 1 ∧ S₁' * S₂' = S₂' * S₁' ∧
      T'⁻¹ * S₁' * T' = S₂' := by
  have hmem : ∀ x ∈ ({S₁, S₂, T} : Set G), x ∈ K := fun x hx =>
    hSK (hgen ▸ Subgroup.subset_closure hx)
  refine ⟨S.subtype hSK, ⟨S₁, hmem _ (by simp)⟩, ⟨S₂, hmem _ (by simp)⟩, ⟨T, hmem _ (by simp)⟩,
    rfl, rfl, rfl, ?_, ?_, Subtype.ext (by simpa using hS₁), Subtype.ext (by simpa using hS₂),
    Subtype.ext (by simpa using hT), Subtype.ext (by simpa using hcomm),
    Subtype.ext (by simpa using hconj)⟩
  · apply Subgroup.map_injective (Subgroup.subtype_injective K)
    rw [Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hSK, MonoidHom.map_closure, ← hgen]
    congr 1
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
  · rw [Sylow.coe_subtype, card_subgroupOf_of_le hSK, hcard]

theorem card_centralizer_inf_conj [Finite G] (g a b : G) :
    Nat.card (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G) :
        Subgroup G) =
      Nat.card (Subgroup.centralizer ({g⁻¹ * a * g} : Set G) ⊓
        Subgroup.centralizer ({g⁻¹ * b * g} : Set G) : Subgroup G) := by
  have hmap : (Subgroup.centralizer ({a} : Set G) ⊓ Subgroup.centralizer ({b} : Set G)).map
      (conjHom g⁻¹) = Subgroup.centralizer ({g⁻¹ * a * g} : Set G) ⊓
        Subgroup.centralizer ({g⁻¹ * b * g} : Set G) := by
    ext y
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      conjHom_apply, inv_inv]
    constructor
    · rintro ⟨x, ⟨hxa, hxb⟩, rfl⟩
      constructor
      · calc g⁻¹ * x * g * (g⁻¹ * a * g) = g⁻¹ * (x * a) * g := by group
          _ = g⁻¹ * (a * x) * g := by rw [hxa]
          _ = g⁻¹ * a * g * (g⁻¹ * x * g) := by group
      · calc g⁻¹ * x * g * (g⁻¹ * b * g) = g⁻¹ * (x * b) * g := by group
          _ = g⁻¹ * (b * x) * g := by rw [hxb]
          _ = g⁻¹ * b * g * (g⁻¹ * x * g) := by group
    · rintro ⟨hya, hyb⟩
      refine ⟨g * y * g⁻¹, ⟨?_, ?_⟩, by group⟩
      · calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * a * g) * y) * g⁻¹ := by rw [hya]
          _ = a * (g * y * g⁻¹) := by group
      · calc g * y * g⁻¹ * b = g * (y * (g⁻¹ * b * g)) * g⁻¹ := by group
          _ = g * ((g⁻¹ * b * g) * y) * g⁻¹ := by rw [hyb]
          _ = b * (g * y * g⁻¹) := by group
  rw [← hmap, card_map_conjHom]

end Subgroup

theorem false_of_order_formulas {g k cD cJ q : ℕ} (hq : 1 ≤ q) (hg : 0 < g) (hcD : 0 < cD)
    (hkg : k ≤ g) (hG : g * (cD ^ 2 * (q + 1) ^ 2) = cJ ^ 3 * (q ^ 2 + q + 1))
    (hK : k * cD ^ 2 = cJ * cJ ^ 2) : False := by
  have h1 : g * cD ^ 2 * (q + 1) ^ 2 = k * cD ^ 2 * (q ^ 2 + q + 1) := by
    calc g * cD ^ 2 * (q + 1) ^ 2 = g * (cD ^ 2 * (q + 1) ^ 2) := by ring
      _ = cJ ^ 3 * (q ^ 2 + q + 1) := hG
      _ = (cJ * cJ ^ 2) * (q ^ 2 + q + 1) := by ring
      _ = k * cD ^ 2 * (q ^ 2 + q + 1) := by rw [hK]
  have h2 : k * cD ^ 2 * (q ^ 2 + q + 1) ≤ g * cD ^ 2 * (q ^ 2 + q + 1) := by gcongr
  have h3 : g * cD ^ 2 * (q ^ 2 + q + 1) < g * cD ^ 2 * (q + 1) ^ 2 :=
    Nat.mul_lt_mul_of_pos_left (by nlinarith) (by positivity)
  omega

variable {G : Type} [Group G] {F : Type} [Field F] [Finite F] {Z : Subgroup (GL (Fin 2) F)}
  [Z.Normal] {J : G} (φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z)
  (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F) (hZodd : Odd (Nat.card Z))
  (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)

omit [Finite F] in
include hZ hZodd h2 in
theorem centralizer_inf_diag_eq_fourV {a b : Fˣ} (hab : a ≠ b) :
    (Subgroup.centralizer ({J} : Set G) ⊓
        Subgroup.centralizer ({linearCentralizerHom φ (diagGL a b)} : Set G) : Subgroup G) =
      Subgroup.centralizer (fourV φ : Set G) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxJ, hxd⟩ := Subgroup.mem_inf.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxJ hxd
    exact mem_centralizer_fourV_of_commute_diag φ hZ hZodd h2 hab hxJ.symm hxd
  · intro x hx
    have hxT := (mem_centralizer_fourV φ).mp hx
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxT.1.symm, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact commute_of_mem_centralizer_fourV φ hZ hZodd h2 hx
      ((mem_centralizer_fourV φ).mpr (isTorus_diag φ a b))

include φ hZ hZodd h2 hJ in
theorem centralizer_eq_of_mem_centerSub (h5 : BrauerWreathedTypeOnePrincipalBlockStatement)
    [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hq : Nat.card F % 4 = 1) {z : G} (hz : z ∈ centerSub φ) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) = Subgroup.centralizer ({J} : Set G) := by
  obtain ⟨n, S, S₁, S₂, T, hn, hgen, hcard, hS₁, hS₂, hT, hcomm, hconj, hSC, hJpow, hJ₂pow⟩ :=
    exists_wreath_sylow_of_G φ hZ hZodd h2 hJ hq
  obtain ⟨h6, hA⟩ := caseOneA_of_simple φ hnonab n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT hcomm
    hconj hJpow hJ₂pow
  have hG := typeOne_order_formula h5 hZ hZodd hq n hn S S₁ S₂ T hgen hcard hS₁ hS₂ hT hcomm
    hconj hJpow hJ₂pow hA φ h6
  set K := Subgroup.centralizer ({z} : Set G) with hKdef
  have hCK : Subgroup.centralizer ({J} : Set G) ≤ K :=
    centralizer_J_le_centralizer_of_mem_centerSub φ hz
  obtain ⟨S', S₁', S₂', T', e₁, e₂, e₃, hgen', hcard', hS₁', hS₂', hT', hcomm', hconj'⟩ :=
    exists_wreath_subgroup n S S₁ S₂ T (hSC.trans hCK) hgen hcard hS₁ hS₂ hT hcomm hconj
  have hJK : J ∈ K := hCK (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  have hJ₂K : invJ₂ φ ∈ K := hCK (linearCentralizerHom_mem φ _)
  set J' : K := ⟨J, hJK⟩ with hJ'def
  set J₂' : K := ⟨invJ₂ φ, hJ₂K⟩ with hJ₂'def
  have hJ'pow : (S₁'⁻¹ * S₂'⁻¹) ^ 2 ^ (n - 1) = J' := Subtype.ext (by simpa [e₁, e₂] using hJpow)
  have hJ₂'pow : S₁' ^ 2 ^ (n - 1) = J₂' := Subtype.ext (by simpa [e₁] using hJ₂pow)
  have hA' : ∃ g ∈ Subgroup.centralizer ({J'} : Set K), g⁻¹ * T' * g = J₂' := by
    obtain ⟨g, hg, hgT⟩ := hA
    refine ⟨⟨g, hCK hg⟩, ?_, Subtype.ext (by simpa [e₃] using hgT)⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    exact Subtype.ext hg
  have ψ : Subgroup.centralizer ({J'} : Set K) ≃* GL (Fin 2) F ⧸ Z :=
    ((MulEquiv.subgroupCongr (centralizer_singleton_eq_subgroupOf J')).trans
      (Subgroup.subgroupOfEquivOfLe hCK)).trans φ
  have hKcases := typeOne_or_typeTwo_order h5 hZ hZodd hq n hn S' S₁' S₂' T' hgen' hcard' hS₁'
    hS₂' hT' hcomm' hconj' hJ'pow hJ₂'pow hA' ψ
  rw [card_centralizer_singleton_subgroup_of_le J' hCK,
    card_centralizer_closure_pair_subgroup J' J₂' hCK,
    card_centralizer_singleton_subgroup J₂'] at hKcases
  have hcD0 : 0 < Nat.card (Subgroup.centralizer
      ((Subgroup.closure {J, invJ₂ φ} : Subgroup G) : Set G)) := Nat.card_pos
  rcases hKcases with hK | hK
  ·
    exfalso
    have hKG : Nat.card K = Nat.card G := by
      apply Nat.eq_of_mul_eq_mul_right (by positivity :
        0 < Nat.card (Subgroup.centralizer
          ((Subgroup.closure {J, invJ₂ φ} : Subgroup G) : Set G)) ^ 2 * (Nat.card F + 1) ^ 2)
      rw [hK, hG]
    have hKtop := Subgroup.eq_top_of_card_eq K hKG
    apply hz1
    apply eq_one_of_mem_center_of_simple hnonab
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ K := hKtop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  ·
    obtain ⟨Y, hY₁, hY₂⟩ := exists_Y φ hZ hZodd h2 hJ hnonab
    have hY₃ := conj_Y_invJ₂ φ hZ hZodd h2 hJ hY₁ hY₂
    have hYN : Y ∈ Subgroup.normalizer (fourV φ : Set G) := by
      simpa using (Subgroup.normalizer _).inv_mem
        (inv_mem_normalizer_fourV φ hZ hZodd h2 hJ hY₁ hY₂)
    have hz'D : Y⁻¹ * z * Y ∈ Subgroup.centralizer (fourV φ : Set G) :=
      inv_mul_mul_mem_centralizer_fourV φ hYN (mem_centralizer_fourV_of_mem_centerSub φ hz)
    obtain ⟨a, b, hab⟩ := (mem_centralizer_fourV_iff φ hZ hZodd h2).mp hz'D
    have hconjcard := card_centralizer_inf_conj Y (invJ₂ φ) z
    rw [hY₃, hab] at hconjcard
    replace hK : Nat.card K * Nat.card (Subgroup.centralizer
        ((Subgroup.closure {J, invJ₂ φ} : Subgroup G) : Set G)) ^ 2 =
        Nat.card (Subgroup.centralizer ({J} : Set G)) *
          Nat.card (Subgroup.centralizer ({J} : Set G) ⊓
            Subgroup.centralizer ({linearCentralizerHom φ (diagGL a b)} : Set G) :
              Subgroup G) ^ 2 := by
      rw [← hconjcard]
      exact hK
    by_cases hab' : a = b
    ·
      exfalso
      subst hab'
      have hcen : linearCentralizerHom φ (diagGL a a) ∈ centerSub φ := by
        rw [mem_centerSub]
        refine ⟨a, ?_⟩
        congr 1
        ext i j
        fin_cases i <;> fin_cases j <;> simp [diagGL, Matrix.GeneralLinearGroup.scalar]
      rw [inf_eq_left.mpr (centralizer_J_le_centralizer_of_mem_centerSub φ hcen)] at hK
      exact false_of_order_formulas (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne') Nat.card_pos
        hcD0 (Subgroup.card_le_card_group K) hG hK
    ·
      rw [centralizer_inf_diag_eq_fourV φ hZ hZodd h2 hab',
        ← centralizer_closure_J_invJ₂ φ hZ hZodd h2 hJ] at hK
      have hKJ : Nat.card K = Nat.card (Subgroup.centralizer ({J} : Set G)) :=
        Nat.eq_of_mul_eq_mul_right (by positivity) hK
      exact (Subgroup.eq_of_le_of_card_ge hCK hKJ.le).symm

end CFSG.BrauerLinearThree.QOne
