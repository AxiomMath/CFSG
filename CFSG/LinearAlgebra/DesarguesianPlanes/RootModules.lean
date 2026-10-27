module

public import CFSG.LinearAlgebra.DesarguesianPlanes.RootRelations

public section

namespace CFSG.DesarguesianPlanes

open Matrix
open scoped commutatorElement

variable {G : Type*} [Group G] {F : Type} [Field F] {Z : Subgroup (GL (Fin 2) F)} [Z.Normal]
  {J : G} {φ : Subgroup.centralizer ({J} : Set G) ≃* GL (Fin 2) F ⧸ Z} {Y : G}

theorem comm_of_mem_map_conjHom {H : Subgroup G} (hH : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) (g : G) :
    ∀ a ∈ H.map (conjHom g), ∀ b ∈ H.map (conjHom g), a * b = b * a := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, hH a ha b hb, map_mul]

theorem comm_rootX₁ : ∀ a ∈ rootX₁ φ, ∀ b ∈ rootX₁ φ, a * b = b * a := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
  rw [← map_mul, mul_comm, map_mul]

theorem comm_rootX₂ : ∀ a ∈ rootX₂ φ, ∀ b ∈ rootX₂ φ, a * b = b * a := by
  rintro _ ⟨c, rfl⟩ _ ⟨d, rfl⟩
  rw [← map_mul, mul_comm, map_mul]

theorem card_map_conjHom (H : Subgroup G) (g : G) : Nat.card (H.map (conjHom g)) = Nat.card H :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

section Card

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
include hZ

theorem card_rootX₁ : Nat.card (rootX₁ φ) = Nat.card F := by
  rw [Nat.card_congr (MonoidHom.ofInjective (f := upHom φ) ?_).toEquiv.symm]
  · exact Nat.card_congr (Multiplicative.toAdd)
  · intro c d h
    exact Multiplicative.toAdd.injective (rootUp_injective φ hZ h)

theorem card_rootX₂ : Nat.card (rootX₂ φ) = Nat.card F := by
  rw [Nat.card_congr (MonoidHom.ofInjective (f := lowHom φ) ?_).toEquiv.symm]
  · exact Nat.card_congr (Multiplicative.toAdd)
  · intro c d h
    exact Multiplicative.toAdd.injective (rootLow_injective φ hZ h)


theorem card_rootSub_02 : Nat.card (rootSub φ Y 0 2) = Nat.card F := by
  rw [rootSub_02, card_map_conjHom, card_rootX₂ hZ]

theorem card_rootSub_12 : Nat.card (rootSub φ Y 1 2) = Nat.card F := by
  rw [rootSub_12, card_map_conjHom, card_rootX₁ hZ]

theorem card_rootSub_21 : Nat.card (rootSub φ Y 2 1) = Nat.card F := by
  rw [rootSub_21, card_map_conjHom, card_rootX₂ hZ]

theorem card_rootSub_20 : Nat.card (rootSub φ Y 2 0) = Nat.card F := by
  rw [rootSub_20, card_map_conjHom, card_rootX₁ hZ]

end Card

theorem comm_rootSub_02 : ∀ a ∈ rootSub φ Y 0 2, ∀ b ∈ rootSub φ Y 0 2, a * b = b * a :=
  comm_of_mem_map_conjHom comm_rootX₂ _

theorem comm_rootSub_12 : ∀ a ∈ rootSub φ Y 1 2, ∀ b ∈ rootSub φ Y 1 2, a * b = b * a :=
  comm_of_mem_map_conjHom comm_rootX₁ _

theorem comm_rootSub_21 : ∀ a ∈ rootSub φ Y 2 1, ∀ b ∈ rootSub φ Y 2 1, a * b = b * a :=
  comm_of_mem_map_conjHom comm_rootX₂ _

theorem comm_rootSub_20 : ∀ a ∈ rootSub φ Y 2 0, ∀ b ∈ rootSub φ Y 2 0, a * b = b * a :=
  comm_of_mem_map_conjHom comm_rootX₁ _

theorem pow_ringChar_of_mem_rootX₁ {x : G} (hx : x ∈ rootX₁ φ) : x ^ ringChar F = 1 := by
  obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp hx
  exact rootUp_pow_ringChar φ c

theorem pow_ringChar_of_mem_rootX₂ {x : G} (hx : x ∈ rootX₂ φ) : x ^ ringChar F = 1 := by
  obtain ⟨c, rfl⟩ := (mem_rootX₂ φ).mp hx
  exact rootLow_pow_ringChar φ c

theorem pow_ringChar_of_mem_map {H : Subgroup G} (hH : ∀ x ∈ H, x ^ ringChar F = 1) (g : G) :
    ∀ x ∈ H.map (conjHom g), x ^ ringChar F = 1 := by
  rintro _ ⟨x, hx, rfl⟩
  rw [← map_pow, hH x hx, map_one]

theorem commute_J_of_mem_rootX₁ {x : G} (hx : x ∈ rootX₁ φ) : J * x = x * J := by
  obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp hx
  exact linearCentralizerHom_commute φ _

theorem commute_J_of_mem_rootX₂ {x : G} (hx : x ∈ rootX₂ φ) : J * x = x * J := by
  obtain ⟨c, rfl⟩ := (mem_rootX₂ φ).mp hx
  exact linearCentralizerHom_commute φ _

theorem commute_conj_of_mem_map {H : Subgroup G} {a : G} (hH : ∀ x ∈ H, a * x = x * a) (g : G) :
    ∀ x ∈ H.map (conjHom g), (g * a * g⁻¹) * x = x * (g * a * g⁻¹) := by
  rintro _ ⟨x, hx, rfl⟩
  exact commute_conj g (hH x hx)

section Inter

variable (hZ : Z ≤ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 2) F)
  (hZodd : Odd (Nat.card Z)) (h2 : (2 : F) ≠ 0) (hJ : orderOf J = 2)
  (hY₁ : Y⁻¹ * J * Y = invJ₁ φ) (hY₂ : Y⁻¹ * invJ₁ φ * Y = invJ₂ φ)

include hY₁ in
theorem commute_invJ₁_of_mem {x : G} (hx : x ∈ rootSub φ Y 1 2 ∨ x ∈ rootSub φ Y 2 1) :
    invJ₁ φ * x = x * invJ₁ φ := by
  have h := commute_conj_of_mem_map (H := rootX₁ φ) (fun _ hx => commute_J_of_mem_rootX₁ hx) Y⁻¹
  have h' := commute_conj_of_mem_map (H := rootX₂ φ) (fun _ hx => commute_J_of_mem_rootX₂ hx) Y⁻¹
  rw [inv_inv, hY₁] at h h'
  rcases hx with hx | hx
  · exact h x hx
  · exact h' x hx

include hY₁ hY₂ in
theorem commute_invJ₂_of_mem {x : G} (hx : x ∈ rootSub φ Y 0 2 ∨ x ∈ rootSub φ Y 2 0) :
    invJ₂ φ * x = x * invJ₂ φ := by
  have hJ2 : (Y ^ 2)⁻¹ * J * ((Y ^ 2)⁻¹)⁻¹ = invJ₂ φ := by
    rw [inv_inv, show (Y ^ 2)⁻¹ * J * Y ^ 2 = Y⁻¹ * (Y⁻¹ * J * Y) * Y by
      simp only [pow_succ, pow_zero, one_mul, _root_.mul_inv_rev, mul_assoc], hY₁, hY₂]
  have h := commute_conj_of_mem_map (H := rootX₁ φ) (fun _ hx => commute_J_of_mem_rootX₁ hx)
    (Y ^ 2)⁻¹
  have h' := commute_conj_of_mem_map (H := rootX₂ φ) (fun _ hx => commute_J_of_mem_rootX₂ hx)
    (Y ^ 2)⁻¹
  rw [hJ2] at h h'
  rcases hx with hx | hx
  · exact h' x hx
  · exact h x hx

include hZ hZodd h2 hJ in
theorem eq_one_of_commute_invJ₁_invJ₂ [Finite F] {x : G} (h₁ : invJ₁ φ * x = x * invJ₁ φ)
    (h₂ : invJ₂ φ * x = x * invJ₂ φ) (hp : x ^ ringChar F = 1) : x = 1 := by
  classical
  let : Fintype F := Fintype.ofFinite F
  have hJx : J * x = x * J := by
    rw [← invJ₂_mul_invJ₁ φ hZ hZodd h2 hJ, mul_assoc, h₁, ← mul_assoc, h₂, mul_assoc]
  obtain ⟨a, b, rfl⟩ := (isTorus_iff φ hZ hZodd h2 x).mp ⟨hJx, h₁⟩
  exact eq_one_of_pow_ringChar_of_pow_card_sub_one hp (diag_pow_card_sub_one φ a b)

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem inter_02_12 [Finite F] : ∀ x ∈ rootSub φ Y 0 2, x ∈ rootSub φ Y 1 2 → x = 1 := by
  intro x hx hx'
  apply eq_one_of_commute_invJ₁_invJ₂ hZ hZodd h2 hJ
    (commute_invJ₁_of_mem hY₁ (Or.inl hx'))
    (commute_invJ₂_of_mem hY₁ hY₂ (Or.inl hx))
  exact pow_ringChar_of_mem_map (fun _ h => pow_ringChar_of_mem_rootX₂ h) _ x hx

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem inter_21_20 [Finite F] : ∀ x ∈ rootSub φ Y 2 1, x ∈ rootSub φ Y 2 0 → x = 1 := by
  intro x hx hx'
  apply eq_one_of_commute_invJ₁_invJ₂ hZ hZodd h2 hJ
    (commute_invJ₁_of_mem hY₁ (Or.inr hx))
    (commute_invJ₂_of_mem hY₁ hY₂ (Or.inr hx'))
  exact pow_ringChar_of_mem_map (fun _ h => pow_ringChar_of_mem_rootX₂ h) _ x hx


theorem eq_one_of_commute_all {H K : Subgroup G}
    (hHt : ∀ t, IsTorus φ t → H.map (conjHom t) = H) (hK : TorusTransitive φ K)
    (hnt : NonTriv K H) {v : G} (hv : v ∈ K) (hcomm : ∀ a ∈ H, a * v = v * a) : v = 1 := by
  by_contra hv1
  obtain ⟨b, hb, a, ha, hab⟩ := hnt
  apply hab
  by_cases hb1 : b = 1
  · rw [hb1, commutatorElement_one_left]
  obtain ⟨t, ht, htv⟩ := hK v hv b hb hv1 hb1
  have ha' : a ∈ H.map (conjHom t) := by rw [hHt t ht]; exact ha
  obtain ⟨a', ha'', rfl⟩ := ha'
  rw [← htv, ← map_commutatorElement, commutatorElement_eq_one_iff_commute.mpr (hcomm a' ha'').symm,
    map_one]

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem isRootModule_upper [Finite F] (hR : BrauerRootRelations φ Y) :
    IsRootModule (linearCentralizerHom φ) (rootSub φ Y 0 2) (rootSub φ Y 1 2) where
  comm₁ := comm_rootSub_02
  comm₂ := comm_rootSub_12
  comm₁₂ := (hR.commutes_12_02 hZ hZodd h2 hJ hY₁ hY₂).symm
  inter := inter_02_12 hZ hZodd h2 hJ hY₁ hY₂
  card₁ := card_rootSub_02 hZ
  card₂ := card_rootSub_12 hZ
  up₁ := fun c v hv => hR.commutes_X₁_X₂_two _ ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) v hv
  up₂ := fun c v hv => (hR.commIn_12_01_02 hZ hZodd h2 hJ hY₁ hY₂).symm _
    ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) v hv
  low₂ := fun c v hv => (hR.commutes_12_10 hZ hZodd h2 hJ hY₁ hY₂).symm _
    ((mem_rootX₂ φ).mpr ⟨c, rfl⟩) v hv
  low₁ := fun c v hv => (hR.commIn_02_10_12 hZ hZodd h2 hJ hY₁ hY₂).symm _
    ((mem_rootX₂ φ).mpr ⟨c, rfl⟩) v hv
  nondeg := fun v hv hcomm => by
    apply eq_one_of_commute_all (H := rootSub φ Y 0 1) (K := rootSub φ Y 1 2)
      (fun t ht => torus_map_rootSub φ hZ hZodd h2 hJ hY₁ hY₂ ht 0 1)
      (rootSub_transitive φ hZ hZodd h2 hJ hY₁ hY₂ (by decide))
      (hR.nonTriv_12_01 hZ hZodd h2 hJ hY₁ hY₂) hv
    intro a ha
    obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp ha
    exact hcomm c

include hZ hZodd h2 hJ hY₁ hY₂ in
theorem isRootModule_lower [Finite F] (hR : BrauerRootRelations φ Y) :
    IsRootModule (linearCentralizerHom φ) (rootSub φ Y 2 1) (rootSub φ Y 2 0) where
  comm₁ := comm_rootSub_21
  comm₂ := comm_rootSub_20
  comm₁₂ := (hR.commutes_20_21 hZ hZodd h2 hJ hY₁ hY₂).symm
  inter := inter_21_20 hZ hZodd h2 hJ hY₁ hY₂
  card₁ := card_rootSub_21 hZ
  card₂ := card_rootSub_20 hZ
  up₁ := fun c v hv => hR.commutes_X₁_X₂_one _ ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) v hv
  up₂ := fun c v hv => hR.commIn_01_20_21 hZ hZodd h2 hJ hY₁ hY₂ _
    ((mem_rootX₁ φ).mpr ⟨c, rfl⟩) v hv
  low₂ := fun c v hv => (hR.commutes_20_10 hZ hZodd h2 hJ hY₁ hY₂).symm _
    ((mem_rootX₂ φ).mpr ⟨c, rfl⟩) v hv
  low₁ := fun c v hv => hR.commIn_10_21_20 hZ hZodd h2 hJ hY₁ hY₂ _
    ((mem_rootX₂ φ).mpr ⟨c, rfl⟩) v hv
  nondeg := fun v hv hcomm => by
    apply eq_one_of_commute_all (H := rootSub φ Y 0 1) (K := rootSub φ Y 2 0)
      (fun t ht => torus_map_rootSub φ hZ hZodd h2 hJ hY₁ hY₂ ht 0 1)
      (rootSub_transitive φ hZ hZodd h2 hJ hY₁ hY₂ (by decide))
      (hR.nonTriv_01_20 hZ hZodd h2 hJ hY₁ hY₂).symm hv
    intro a ha
    obtain ⟨c, rfl⟩ := (mem_rootX₁ φ).mp ha
    exact hcomm c

end Inter

end CFSG.DesarguesianPlanes
