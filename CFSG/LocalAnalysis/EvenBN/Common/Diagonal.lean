module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.LocalAnalysis.EvenBN.Common

open Subgroup

universe u

variable {G : Type u} [Group G]

theorem conj_mem_map_conj_inv {A : Subgroup G} (t : G) {a : G} (ha : a ∈ A) :
    t⁻¹ * a * t ∈ A.map (MulAut.conj t⁻¹).toMonoidHom :=
  ⟨a, ha, by simp⟩

theorem mem_map_conj_inv_iff {A : Subgroup G} {t x : G} :
    x ∈ A.map (MulAut.conj t⁻¹).toMonoidHom ↔ t * x * t⁻¹ ∈ A := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    simpa [mul_assoc] using ha
  · intro hx
    refine ⟨t * x * t⁻¹, hx, ?_⟩
    simp [mul_assoc]

section Diagonal

variable {A : Subgroup G} {t : G} (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥)
include hcomm

theorem commute_conj_of_commutator_eq_bot {a b : G} (ha : a ∈ A) (hb : b ∈ A) :
    b * (t⁻¹ * a * t) = (t⁻¹ * a * t) * b :=
  (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hb) _
    (conj_mem_map_conj_inv t ha)).symm

omit hcomm in
@[expose] def diagonalHom (A : Subgroup G) (t : G)
    (hcomm : ⁅A, A.map (MulAut.conj t⁻¹).toMonoidHom⁆ = ⊥) : A →* G :=
  MonoidHom.mk' (fun a => (a : G) * (t⁻¹ * a * t)) fun a b => by
    have h := commute_conj_of_commutator_eq_bot hcomm a.2 b.2
    change (a : G) * b * (t⁻¹ * ((a : G) * b) * t) = (a * (t⁻¹ * a * t)) * (b * (t⁻¹ * b * t))
    calc (a : G) * b * (t⁻¹ * ((a : G) * b) * t)
        = a * (b * (t⁻¹ * a * t)) * (t⁻¹ * b * t) := by group
      _ = a * ((t⁻¹ * a * t) * b) * (t⁻¹ * b * t) := by rw [h]
      _ = (a * (t⁻¹ * a * t)) * (b * (t⁻¹ * b * t)) := by group

theorem diagonalHom_apply (a : A) : diagonalHom A t hcomm a = (a : G) * (t⁻¹ * a * t) :=
  rfl

theorem diagonalHom_apply_of_mul_self (ht : t * t = 1) (a : A) :
    diagonalHom A t hcomm a = (a : G) * (t * a * t) := by
  rw [diagonalHom_apply, inv_eq_of_mul_eq_one_right ht]

theorem range_diagonalHom_le (ht : t * t = 1) :
    (diagonalHom A t hcomm).range ≤ centralizer ({t} : Set G) := by
  rintro _ ⟨a, rfl⟩
  rw [mem_centralizer_singleton_iff, diagonalHom_apply_of_mul_self hcomm ht]
  have h := commute_conj_of_commutator_eq_bot hcomm a.2 a.2
  rw [inv_eq_of_mul_eq_one_right ht] at h
  calc (a : G) * (t * a * t) * t = (t * a * t) * a * t := by rw [h]
    _ = t * (a * (t * a * t)) := by group

theorem diagonalHom_eq_one_iff (a : A) :
    diagonalHom A t hcomm a = 1 ↔ t⁻¹ * a * t = (a : G)⁻¹ := by
  rw [diagonalHom_apply]
  constructor
  · exact eq_inv_of_mul_eq_one_right
  · intro h
    rw [h, mul_inv_cancel]

theorem map_ker_diagonalHom_le :
    (diagonalHom A t hcomm).ker.map A.subtype ≤ A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom := by
  rintro _ ⟨a, ha, rfl⟩
  refine ⟨a.2, ?_⟩
  have h := (diagonalHom_eq_one_iff hcomm a).mp ha
  have hinv : (a : G)⁻¹ ∈ A.map (MulAut.conj t⁻¹).toMonoidHom := h ▸ conj_mem_map_conj_inv t a.2
  change (a : G) ∈ _
  simpa using inv_mem hinv

theorem inf_le_center_sup :
    A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom ≤
      (A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom) ⊓
        centralizer ((A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom : Subgroup G) : Set G) := by
  rintro z ⟨hzA, hzAt⟩
  have hle : A ⊔ A.map (MulAut.conj t⁻¹).toMonoidHom ≤ centralizer ({z} : Set G) := by
    refine sup_le (fun b hb => ?_) (fun b hb => ?_)
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hb) z hzAt).symm
    · exact mem_centralizer_singleton_iff.mpr
        (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm hzA) b hb)
  exact ⟨mem_sup_left hzA, mem_centralizer_iff.mpr fun g hg =>
    mem_centralizer_singleton_iff.mp (hle hg)⟩

theorem ker_diagonalHom_le_center : (diagonalHom A t hcomm).ker ≤ center A := by
  intro a ha
  have haAt : (a : G) ∈ A.map (MulAut.conj t⁻¹).toMonoidHom :=
    (map_ker_diagonalHom_le hcomm ⟨a, ha, rfl⟩).2
  rw [mem_center_iff]
  intro b
  exact Subtype.ext (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm b.2)
    _ haAt).symm

theorem odd_card_ker_diagonalHom_of_le {M : Subgroup G}
    (hM : A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom ≤ M) (hodd : Odd (Nat.card M)) :
    Odd (Nat.card (diagonalHom A t hcomm).ker) := by
  refine hodd.of_dvd_nat ?_
  rw [← card_map_of_injective A.subtype_injective]
  exact card_dvd_of_le ((map_ker_diagonalHom_le hcomm).trans hM)

theorem odd_card_ker_diagonalHom_of_centralizer_le [Finite G] (ht : t * t = 1)
    (hC : centralizer ((diagonalHom A t hcomm).range : Set G) ⊓ centralizer ({t} : Set G) ≤
      zpowers t)
    (hA : ∃ x ∈ (diagonalHom A t hcomm).range, ∃ y ∈ (diagonalHom A t hcomm).range,
      x * y ≠ y * x) :
    Odd (Nat.card (diagonalHom A t hcomm).ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (diagonalHom A t hcomm).ker :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨⟨a, hker⟩, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
  rw [orderOf_mk] at hz
  have haz : orderOf (a : G) = 2 := by rw [orderOf_coe, hz]
  have hcen : a ∈ center A := ker_diagonalHom_le_center hcomm hker
  rw [MonoidHom.mem_ker] at hker
  have haa : (a : G) * a = 1 := by rw [← sq, ← haz, pow_orderOf_eq_one]
  have hne : (a : G) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at haz
    exact absurd haz (by norm_num)
  have hat : t⁻¹ * a * t = a := by
    rw [(diagonalHom_eq_one_iff hcomm a).mp hker]
    exact inv_eq_of_mul_eq_one_right haa
  have hacent : (a : G) ∈ centralizer ((diagonalHom A t hcomm).range : Set G) := by
    rw [mem_centralizer_iff]
    rintro _ ⟨b, rfl⟩
    rw [diagonalHom_apply]
    have h1 : (b : G) * a = a * b := congrArg Subtype.val (mem_center_iff.mp hcen b)
    have h2 := commute_conj_of_commutator_eq_bot hcomm b.2 a.2
    calc (b : G) * (t⁻¹ * b * t) * a = b * ((t⁻¹ * b * t) * a) := by group
      _ = b * (a * (t⁻¹ * b * t)) := by rw [← h2]
      _ = a * (b * (t⁻¹ * b * t)) := by rw [← mul_assoc, h1, mul_assoc]
  have hact : (a : G) ∈ centralizer ({t} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (a : G) * t = t * (t⁻¹ * a * t) := by group
      _ = t * a := by rw [hat]
  have hat' : (a : G) = t := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hC ⟨hacent, hact⟩)
    have ht2 : t ^ (2 : ℤ) = 1 := by rw [zpow_two, ht]
    rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · rw [← two_mul, zpow_mul, ht2, one_zpow] at hk
      exact absurd hk.symm hne
    · rw [zpow_add, zpow_mul, ht2, one_zpow, one_mul, zpow_one] at hk
      exact hk.symm
  have hAab : ∀ x y : A, x * y = y * x := by
    intro x y
    have htx : t⁻¹ * x * t = x := by
      have h1' : (x : G) * t = t * x := by
        have := congrArg Subtype.val (mem_center_iff.mp hcen x)
        rw [← hat']
        exact this
      calc t⁻¹ * (x : G) * t = t⁻¹ * (x * t) := by group
        _ = x := by rw [h1']; group
    have h3 := commute_conj_of_commutator_eq_bot hcomm x.2 y.2
    rw [htx] at h3
    exact Subtype.ext h3.symm
  obtain ⟨_, ⟨x, rfl⟩, _, ⟨y, rfl⟩, hxy⟩ := hA
  exact hxy (by rw [← map_mul, ← map_mul, hAab])

theorem injective_diagonalHom [Finite G] [Group.IsPerfect A] {L : Subgroup G}
    (hL : (diagonalHom A t hcomm).range = L) (hodd : Odd (Nat.card (diagonalHom A t hcomm).ker))
    (hcov : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* L),
      Function.Surjective π → π.ker ≤ center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    Function.Injective (diagonalHom A t hcomm) := by
  set δ := diagonalHom A t hcomm with hδ
  let π : A →* L := (MulEquiv.subgroupCongr hL).toMonoidHom.comp δ.rangeRestrict
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hL).surjective.comp δ.rangeRestrict_surjective
  have hker : π.ker = δ.ker := by
    ext a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change MulEquiv.subgroupCongr hL (δ.rangeRestrict a) = 1 ↔ δ a = 1
    rw [MulEquiv.map_eq_one_iff]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hbot := hcov A π hπ (hker ▸ ker_diagonalHom_le_center hcomm) (hker ▸ hodd)
  rw [hker] at hbot
  exact (MonoidHom.ker_eq_bot_iff δ).mp hbot

theorem exists_mulEquiv_diagonalHom [Finite G] [Group.IsPerfect A] {L : Subgroup G}
    (hL : (diagonalHom A t hcomm).range = L) (hodd : Odd (Nat.card (diagonalHom A t hcomm).ker))
    (hcov : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* L),
      Function.Surjective π → π.ker ≤ center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    ∃ e : A ≃* L, ∀ a : A, (e a : G) = (a : G) * (t⁻¹ * a * t) := by
  set δ := diagonalHom A t hcomm with hδ
  have hinj := injective_diagonalHom hcomm hL hodd hcov
  let π : A →* L := (MulEquiv.subgroupCongr hL).toMonoidHom.comp δ.rangeRestrict
  have hπ : Function.Surjective π :=
    (MulEquiv.subgroupCongr hL).surjective.comp δ.rangeRestrict_surjective
  have hπinj : Function.Injective π := fun a b hab => hinj (congrArg Subtype.val hab)
  exact ⟨MulEquiv.ofBijective π ⟨hπinj, hπ⟩, fun a => rfl⟩

theorem inf_eq_bot_of_center_eq_bot {L : Subgroup G}
    (hinj : Function.Injective (diagonalHom A t hcomm)) (hL : (diagonalHom A t hcomm).range = L)
    (hZ : center L = ⊥) :
    A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨hzA, hzAt⟩
  set δ := diagonalHom A t hcomm with hδ
  have hzL : δ ⟨z, hzA⟩ ∈ L := hL ▸ ⟨⟨z, hzA⟩, rfl⟩
  have hcen : (⟨δ ⟨z, hzA⟩, hzL⟩ : L) ∈ center L := by
    rw [mem_center_iff]
    rintro ⟨_, hg⟩
    rw [← hL] at hg
    obtain ⟨b, rfl⟩ := hg
    apply Subtype.ext
    change δ b * δ ⟨z, hzA⟩ = δ ⟨z, hzA⟩ * δ b
    have hbz : (b : G) * z = z * b :=
      (mem_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hcomm b.2) z hzAt).symm
    have hbz' : b * (⟨z, hzA⟩ : A) = ⟨z, hzA⟩ * b := Subtype.ext hbz
    rw [← map_mul, ← map_mul, hbz']
  rw [hZ, mem_bot] at hcen
  have h1 : δ ⟨z, hzA⟩ = δ 1 := by
    rw [map_one]
    exact congrArg Subtype.val hcen
  have := hinj h1
  rw [mem_bot]
  exact congrArg Subtype.val this

theorem diagonal_identification [Finite G] [Group.IsPerfect A] {L : Subgroup G}
    (hL : (diagonalHom A t hcomm).range = L) (hZ : center L = ⊥)
    (hodd : Odd (Nat.card (diagonalHom A t hcomm).ker))
    (hcov : ∀ (E : Type u) [Group E] [Finite E] [Group.IsPerfect E] (π : E →* L),
      Function.Surjective π → π.ker ≤ center E → Odd (Nat.card π.ker) → π.ker = ⊥) :
    A ⊓ A.map (MulAut.conj t⁻¹).toMonoidHom = ⊥ ∧
      ∃ e : A ≃* L, ∀ a : A, (e a : G) = (a : G) * (t⁻¹ * a * t) :=
  ⟨inf_eq_bot_of_center_eq_bot hcomm (injective_diagonalHom hcomm hL hodd hcov) hL hZ,
    exists_mulEquiv_diagonalHom hcomm hL hodd hcov⟩

end Diagonal

theorem isPerfect_subgroup_iff_commutator_eq (H : Subgroup G) : Group.IsPerfect H ↔ ⁅H, H⁆ = H := by
  have hmap : (commutator H).map H.subtype = ⁅H, H⁆ := by
    rw [_root_.commutator_def, map_commutator, ← MonoidHom.range_eq_map, range_subtype]
  have htop : (⊤ : Subgroup H).map H.subtype = H := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  constructor
  · intro hH
    rw [← hmap, hH.commutator_eq_top, htop]
  · intro hH
    refine ⟨map_injective H.subtype_injective ?_⟩
    rw [hmap, htop, hH]

theorem isPerfect_sup_of_isPerfect {K₁ K₂ : Subgroup G} [Group.IsPerfect K₁] [Group.IsPerfect K₂] :
    Group.IsPerfect (K₁ ⊔ K₂ : Subgroup G) := by
  rw [isPerfect_subgroup_iff_commutator_eq]
  have h1 := (isPerfect_subgroup_iff_commutator_eq K₁).mp inferInstance
  have h2 := (isPerfect_subgroup_iff_commutator_eq K₂).mp inferInstance
  exact le_antisymm (commutator_le_self _) (sup_le (h1.ge.trans
    (commutator_mono le_sup_left le_sup_left)) (h2.ge.trans
    (commutator_mono le_sup_right le_sup_right)))

end CFSG.LocalAnalysis.EvenBN.Common
