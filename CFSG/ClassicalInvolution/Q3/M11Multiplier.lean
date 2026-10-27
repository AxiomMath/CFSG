module

public import CFSG.ClassicalInvolution.Q3.CentralTwoKernel
public import CFSG.ClassicalInvolution.Q3.M11Kernel

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Blueprint CFSG.Sporadic.Mathieu Equiv

section Sylow

abbrev m11SdX : Perm (Fin 11) :=
  List.formPerm [1, 2, 8, 9, 5, 7, 10, 4] * List.formPerm [3, 6]

abbrev m11SdY : Perm (Fin 11) :=
  List.formPerm [2, 9] * List.formPerm [3, 6] * List.formPerm [4, 7] * List.formPerm [8, 10]

private theorem m11SdX_eq : m11SdX = m11gB ^ 2 * m11gA * m11gB ^ 2 * m11gA * m11gB⁻¹ * m11gA *
    m11gB⁻¹ * m11gA * m11gB * m11gA := by decide +kernel

private theorem m11SdY_eq : m11SdY = m11gB ^ 2 * m11gA * m11gB * m11gA⁻¹ * m11gB⁻¹ * m11gB⁻¹ *
    m11gA⁻¹ * m11gB⁻¹ * m11gA⁻¹ * m11gB⁻¹ * m11gA⁻¹ * m11gB * m11gA * m11gB⁻¹ * m11gA * m11gB *
    m11gA * m11gB⁻¹ * m11gB⁻¹ := by decide +kernel

private theorem mem_word_x {H : Subgroup (Perm (Fin 11))} {A B : Perm (Fin 11)} (hA : A ∈ H)
    (hB : B ∈ H) : B ^ 2 * A * B ^ 2 * A * B⁻¹ * A * B⁻¹ * A * B * A ∈ H := by
  repeat' first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | assumption

private theorem mem_word_y {H : Subgroup (Perm (Fin 11))} {A B : Perm (Fin 11)} (hA : A ∈ H)
    (hB : B ∈ H) : B ^ 2 * A * B * A⁻¹ * B⁻¹ * B⁻¹ * A⁻¹ * B⁻¹ * A⁻¹ * B⁻¹ * A⁻¹ * B * A * B⁻¹ *
      A * B * A * B⁻¹ * B⁻¹ ∈ H := by
  repeat' first
    | apply Subgroup.mul_mem
    | apply Subgroup.inv_mem
    | apply Subgroup.pow_mem
    | assumption

theorem m11SdX_mem : m11SdX ∈ NativeSporadic.M11 := by
  rw [m11SdX_eq]; exact mem_word_x m11a.2 m11b.2

theorem m11SdY_mem : m11SdY ∈ NativeSporadic.M11 := by
  rw [m11SdY_eq]; exact mem_word_y m11a.2 m11b.2

theorem m11SdX_pow_eight : m11SdX ^ 8 = 1 := by decide +kernel

private theorem m11SdX_pow_four : m11SdX ^ 4 ≠ 1 := by decide +kernel

theorem m11SdY_sq : m11SdY ^ 2 = 1 := by decide +kernel

theorem m11SdY_conj : m11SdY * m11SdX * m11SdY⁻¹ = m11SdX ^ 3 := by decide +kernel

private theorem m11Sd_mul_x : ∀ i : Fin 8, ∀ j : Fin 2,
    m11SdX * (m11SdX ^ i.val * m11SdY ^ j.val) = m11SdX ^ ((i.val + 1) % 8) * m11SdY ^ j.val := by
  decide +kernel

private theorem m11Sd_mul_y : ∀ i : Fin 8, ∀ j : Fin 2,
    m11SdY * (m11SdX ^ i.val * m11SdY ^ j.val) =
      m11SdX ^ ((3 * i.val) % 8) * m11SdY ^ ((j.val + 1) % 2) := by decide +kernel

private theorem m11Sd_mul_xinv : ∀ i : Fin 8, ∀ j : Fin 2,
    m11SdX⁻¹ * (m11SdX ^ i.val * m11SdY ^ j.val) = m11SdX ^ ((i.val + 7) % 8) * m11SdY ^ j.val := by
  decide +kernel

private theorem m11Sd_mul_yinv : ∀ i : Fin 8, ∀ j : Fin 2,
    m11SdY⁻¹ * (m11SdX ^ i.val * m11SdY ^ j.val) =
      m11SdX ^ ((3 * i.val) % 8) * m11SdY ^ ((j.val + 1) % 2) := by decide +kernel

private theorem m11Sd_inj : ∀ p q : Fin 8 × Fin 2, m11SdX ^ p.1.val * m11SdY ^ p.2.val =
    m11SdX ^ q.1.val * m11SdY ^ q.2.val → p = q := by decide +kernel

@[expose] def m11SdMap (p : Fin 8 × Fin 2) : Perm (Fin 11) := m11SdX ^ p.1.val * m11SdY ^ p.2.val

theorem m11Sd_closure_le_range :
    ∀ g ∈ Subgroup.closure ({m11SdX, m11SdY} : Set (Perm (Fin 11))), ∃ p, m11SdMap p = g := by
  intro g hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨(0, 0), by simp only [m11SdMap, Fin.val_zero, pow_zero, mul_one]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨⟨i, j⟩, rfl⟩ := ih
    rcases hx with rfl | hx
    · exact ⟨(⟨(i.val + 1) % 8, Nat.mod_lt _ (by norm_num)⟩, j), (m11Sd_mul_x i j).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨(⟨(3 * i.val) % 8, Nat.mod_lt _ (by norm_num)⟩,
        ⟨(j.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩), (m11Sd_mul_y i j).symm⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨⟨i, j⟩, rfl⟩ := ih
    rcases hx with rfl | hx
    · exact ⟨(⟨(i.val + 7) % 8, Nat.mod_lt _ (by norm_num)⟩, j), (m11Sd_mul_xinv i j).symm⟩
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨(⟨(3 * i.val) % 8, Nat.mod_lt _ (by norm_num)⟩,
        ⟨(j.val + 1) % 2, Nat.mod_lt _ (by norm_num)⟩), (m11Sd_mul_yinv i j).symm⟩

theorem m11SdMap_mem (p : Fin 8 × Fin 2) :
    m11SdMap p ∈ Subgroup.closure ({m11SdX, m11SdY} : Set (Perm (Fin 11))) :=
  Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_insert _ _)) _)
    (Subgroup.pow_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))) _)

private theorem m11Sd_card_closure :
    Nat.card (Subgroup.closure ({m11SdX, m11SdY} : Set (Perm (Fin 11)))) = 16 := by
  let f : Fin 8 × Fin 2 → ↥(Subgroup.closure ({m11SdX, m11SdY} : Set (Perm (Fin 11)))) :=
    fun p => ⟨m11SdMap p, m11SdMap_mem p⟩
  have hf : Function.Bijective f := by
    refine ⟨fun p q hpq => m11Sd_inj p q (congrArg Subtype.val hpq), fun g => ?_⟩
    obtain ⟨p, hp⟩ := m11Sd_closure_le_range g g.2
    exact ⟨p, Subtype.ext hp⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_prod, Nat.card_fin, Nat.card_fin]

@[expose] def m11SdS : Subgroup ↥NativeSporadic.M11 :=
  Subgroup.closure ({⟨m11SdX, m11SdX_mem⟩, ⟨m11SdY, m11SdY_mem⟩} : Set ↥NativeSporadic.M11)

private theorem m11SdS_map : m11SdS.map NativeSporadic.M11.subtype =
    Subgroup.closure ({m11SdX, m11SdY} : Set (Perm (Fin 11))) := by
  rw [m11SdS, MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton]
  rfl

theorem card_m11SdS : Nat.card m11SdS = 16 := by
  rw [← Subgroup.card_map_of_injective NativeSporadic.M11.subtype_injective, m11SdS_map]
  exact m11Sd_card_closure

theorem exists_m11SdMap_eq_of_mem {s : ↥NativeSporadic.M11} (hs : s ∈ m11SdS) :
    ∃ p, m11SdMap p = (s : Perm (Fin 11)) := by
  apply m11Sd_closure_le_range
  rw [← m11SdS_map]
  exact ⟨s, hs, rfl⟩

theorem exists_semidihedral_sylow :
    ∃ x y : ↥NativeSporadic.M11,
      Nat.card (Subgroup.closure ({x, y} : Set ↥NativeSporadic.M11)) = 16 ∧
        orderOf x = 8 ∧ y ^ 2 = 1 ∧ y * x * y⁻¹ = x ^ 3 := by
  refine ⟨⟨m11SdX, m11SdX_mem⟩, ⟨m11SdY, m11SdY_mem⟩, card_m11SdS, ?_, ?_, ?_⟩
  · have h8 : (⟨m11SdX, m11SdX_mem⟩ : ↥NativeSporadic.M11) ^ 8 = 1 :=
      Subtype.ext (by simpa using m11SdX_pow_eight)
    have h4 : ¬ (⟨m11SdX, m11SdX_mem⟩ : ↥NativeSporadic.M11) ^ 2 ^ 2 = 1 := fun h =>
      m11SdX_pow_four (by simpa using congrArg Subtype.val h)
    exact orderOf_eq_prime_pow (p := 2) (n := 2) h4 h8
  · exact Subtype.ext (by simpa using m11SdY_sq)
  · exact Subtype.ext (by simpa using m11SdY_conj)

end Sylow

section Multiplier

theorem injective_of_perfect_central_two {E : Type*} [Group E] [Finite E]
    (π : E →* ↥NativeSporadic.M11) (hπ : Function.Surjective π) (hper : Group.IsPerfect E)
    (hcen : π.ker ≤ Subgroup.center E) (h2 : IsPGroup 2 π.ker) : Function.Injective π := by
  obtain ⟨x, y, hS, hx8, hy2, hyx⟩ := exists_semidihedral_sylow
  set S := Subgroup.closure ({x, y} : Set ↥NativeSporadic.M11) with hSdef
  have hidx : S.index = 495 := by
    have := Subgroup.card_mul_index S
    rw [hS, card_m11_kernel] at this
    omega
  have hodd : ¬ 2 ∣ S.index := by rw [hidx]; norm_num
  obtain ⟨a, ha⟩ := hπ x
  obtain ⟨b, hb⟩ := hπ y
  set H : Subgroup E := S.comap π with hH
  have hxS : x ∈ S := Subgroup.subset_closure (Set.mem_insert _ _)
  have hyS : y ∈ S := Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have haH : a ∈ H := by rw [hH, Subgroup.mem_comap, ha]; exact hxS
  have hbH : b ∈ H := by rw [hH, Subgroup.mem_comap, hb]; exact hyS
  set a' : ↥H := ⟨a, haH⟩ with ha'
  set b' : ↥H := ⟨b, hbH⟩ with hb'
  set Z : Subgroup ↥H := π.ker.subgroupOf H with hZ
  have hmemZ : ∀ g : ↥H, g ∈ Z ↔ π (g : E) = 1 := fun g => by
    rw [hZ, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
  have hZc : Z ≤ Subgroup.center ↥H := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_center_iff.mp (hcen (Subgroup.mem_subgroupOf.mp hz)) (g : E)
  have hπa : π (a' : E) = x := ha
  have hπb : π (b' : E) = y := hb
  have hgen : Subgroup.closure ({a', b'} : Set ↥H) ⊔ Z = ⊤ := by
    rw [eq_top_iff]
    intro h _
    set ρ : ↥H →* ↥NativeSporadic.M11 := π.comp H.subtype with hρ
    have hmap : (Subgroup.closure ({a', b'} : Set ↥H)).map ρ = S := by
      rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_singleton, hSdef,
        show ρ a' = x from hπa, show ρ b' = y from hπb]
    have hhS : ρ h ∈ S := h.2
    rw [← hmap] at hhS
    obtain ⟨c, hc, hch⟩ := Subgroup.mem_map.mp hhS
    have hcZ : c⁻¹ * h ∈ Z := by
      rw [hmemZ]
      have : π ((c : E)) = π (h : E) := hch
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, this, inv_mul_cancel]
    have : h = c * (c⁻¹ * h) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hc hcZ
  have h2' : b' ^ 2 ∈ Z := by
    rw [hmemZ]
    simpa [map_pow, hπb] using hy2
  have h3' : b' * a' * b'⁻¹ * (a' ^ 3)⁻¹ ∈ Z := by
    rw [hmemZ]
    have : y * x * y⁻¹ * (x ^ 3)⁻¹ = 1 := by rw [hyx]; group
    simpa [map_mul, map_inv, map_pow, hπa, hπb] using this
  have h4' : ∀ k : ℕ, a' ^ k ∈ Z → 8 ∣ k := by
    intro k hk
    rw [hmemZ] at hk
    have : x ^ k = 1 := by simpa [map_pow, hπa] using hk
    rw [← hx8]
    exact orderOf_dvd_of_pow_eq_one this
  have hbot := CentralKernel.inf_commutator_eq_bot_of_sd16 Z hZc a' b' hgen h2' h3' h4'
  rw [← MonoidHom.ker_eq_bot_iff]
  refine eq_bot_iff.mpr fun z hz => ?_
  obtain ⟨hzS, hzc⟩ := CentralKernel.mem_commutator_of_central_kernel π hπ hper hcen h2 S hodd hz
  have hz' : (⟨z, hzS⟩ : ↥H) ∈ Z ⊓ commutator ↥H :=
    ⟨(hmemZ _).mpr (MonoidHom.mem_ker.mp hz), hzc⟩
  rw [hbot, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val hz'

end Multiplier

end CFSG.ClassicalInvolution.Q3
