module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
public import CFSG.HardMathSupport.Solomon.Proving.SU32Carrier
import all CFSG.GH74.QTGen4.Leaves.F112.PSU32Model
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape

section Abstract

variable {H : Type*} [Group H]

structure Heis3Rel (S D Z : H) : Prop where
  central : ∀ x : H, Z * x = x * Z
  Z_cube : Z ^ 3 = 1
  S_cube : S ^ 3 = 1
  D_cube : D ^ 3 = 1
  S_D : S * D = Z ^ 2 * (D * S)

variable {S D Z : H}

theorem Heis3Rel.pow_comm (h : Heis3Rel S D Z) (n : ℕ) (x : H) : Z ^ n * x = x * Z ^ n :=
  (Commute.pow_left (h.central x) n).eq

theorem Heis3Rel.mul_pow_mul (h : Heis3Rel S D Z) (n : ℕ) (x y : H) :
    x * (Z ^ n * y) = Z ^ n * (x * y) := by
  rw [← mul_assoc, ← h.pow_comm n x, mul_assoc]

theorem Heis3Rel.S_mul_D_pow (h : Heis3Rel S D Z) (j : ℕ) :
    S * D ^ j = Z ^ (2 * j) * (D ^ j * S) := by
  induction j with
  | zero => simp
  | succ j ih =>
    calc S * D ^ (j + 1) = (S * D) * D ^ j := by rw [pow_succ', mul_assoc]
      _ = Z ^ 2 * (D * (S * D ^ j)) := by rw [h.S_D]; simp only [mul_assoc]
      _ = Z ^ 2 * (D * (Z ^ (2 * j) * (D ^ j * S))) := by rw [ih]
      _ = Z ^ 2 * (Z ^ (2 * j) * (D * (D ^ j * S))) := by rw [h.mul_pow_mul]
      _ = Z ^ (2 * (j + 1)) * (D ^ (j + 1) * S) := by
        rw [← mul_assoc, ← pow_add, ← mul_assoc D, ← pow_succ' D j,
          show 2 + 2 * j = 2 * (j + 1) by ring]

theorem Heis3Rel.S_pow_mul_D_pow (h : Heis3Rel S D Z) (k j : ℕ) :
    S ^ k * D ^ j = Z ^ (2 * (k * j)) * (D ^ j * S ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc S ^ (k + 1) * D ^ j = S * (S ^ k * D ^ j) := by rw [pow_succ', mul_assoc]
      _ = S * (Z ^ (2 * (k * j)) * (D ^ j * S ^ k)) := by rw [ih]
      _ = Z ^ (2 * (k * j)) * (S * (D ^ j * S ^ k)) := by rw [h.mul_pow_mul]
      _ = Z ^ (2 * (k * j)) * ((S * D ^ j) * S ^ k) := by rw [← mul_assoc S]
      _ = Z ^ (2 * (k * j)) * ((Z ^ (2 * j) * (D ^ j * S)) * S ^ k) := by
        rw [h.S_mul_D_pow]
      _ = Z ^ (2 * (k * j)) * (Z ^ (2 * j) * (D ^ j * (S * S ^ k))) := by
        rw [mul_assoc (Z ^ (2 * j)), mul_assoc (D ^ j)]
      _ = Z ^ (2 * ((k + 1) * j)) * (D ^ j * S ^ (k + 1)) := by
        rw [← mul_assoc, ← pow_add, ← pow_succ' S k,
          show 2 * (k * j) + 2 * j = 2 * ((k + 1) * j) by ring]

theorem Heis3Rel.mul_form (h : Heis3Rel S D Z) (i j k i' j' k' : ℕ) :
    (Z ^ i * D ^ j * S ^ k) * (Z ^ i' * D ^ j' * S ^ k') =
      Z ^ (i + i' + 2 * (k * j')) * D ^ (j + j') * S ^ (k + k') := by
  calc (Z ^ i * D ^ j * S ^ k) * (Z ^ i' * D ^ j' * S ^ k')
      = Z ^ i * (D ^ j * (S ^ k * (Z ^ i' * (D ^ j' * S ^ k')))) := by simp only [mul_assoc]
    _ = Z ^ i * (D ^ j * (Z ^ i' * (S ^ k * (D ^ j' * S ^ k')))) := by rw [h.mul_pow_mul]
    _ = Z ^ i * (Z ^ i' * (D ^ j * (S ^ k * (D ^ j' * S ^ k')))) := by rw [h.mul_pow_mul]
    _ = Z ^ i * (Z ^ i' * (D ^ j * ((S ^ k * D ^ j') * S ^ k'))) := by simp only [mul_assoc]
    _ = Z ^ i * (Z ^ i' * (D ^ j * ((Z ^ (2 * (k * j')) * (D ^ j' * S ^ k)) * S ^ k'))) := by
        rw [h.S_pow_mul_D_pow]
    _ = Z ^ i * (Z ^ i' * (Z ^ (2 * (k * j')) * (D ^ j * (D ^ j' * (S ^ k * S ^ k'))))) := by
        simp only [mul_assoc]; rw [h.mul_pow_mul (2 * (k * j')) (D ^ j)]
    _ = Z ^ (i + i' + 2 * (k * j')) * D ^ (j + j') * S ^ (k + k') := by
        rw [pow_add Z (i + i'), pow_add Z i i', pow_add D, pow_add S]; simp only [mul_assoc]

theorem cube_mul_eq_one {u v c : H} (hcu : ∀ x, c * x = x * c)
    (hvu : v * u = c * (u * v)) (hc : c ^ 3 = 1) (hu : u ^ 3 = 1) (hv : v ^ 3 = 1) :
    (u * v) ^ 3 = 1 := by
  have e1 : ∀ w, v * (u * w) = c * (u * (v * w)) := by
    intro w; rw [← mul_assoc, hvu, mul_assoc, mul_assoc]
  have e2 : ∀ x w, x * (c * w) = c * (x * w) := by
    intro x w; rw [← mul_assoc, ← hcu x, mul_assoc]
  have e3 : v * (v * (u * v)) = c * (c * (u * (v * (v * v)))) := by
    rw [e1 v, e2, e1 (v * v), e2]
  have e6 : ∀ x y w, x * (y * (c * w)) = c * (x * (y * w)) := by
    intro x y w; rw [e2, e2]
  calc (u * v) ^ 3 = u * (v * (u * (v * (u * v)))) := by rw [pow_three]; simp only [mul_assoc]
    _ = u * (c * (u * (v * (v * (u * v))))) := by rw [e1]
    _ = c * (u * (u * (v * (v * (u * v))))) := by rw [e2]
    _ = c * (u * (u * (c * (c * (u * (v * (v * v))))))) := by rw [e3]
    _ = c * (c * (c * (u * (u * (u * (v * (v * v))))))) := by
        rw [e6 u u (c * (u * (v * (v * v)))), e6 u u (u * (v * (v * v)))]
    _ = c ^ 3 * (u ^ 3 * v ^ 3) := by simp only [pow_three, mul_assoc]
    _ = 1 := by rw [hc, hu, hv]; simp

theorem Heis3Rel.cube_form (h : Heis3Rel S D Z) (i j k : ℕ) : (Z ^ i * D ^ j * S ^ k) ^ 3 = 1 := by
  have hcomm : Commute (Z ^ i) (D ^ j * S ^ k) := Commute.pow_left (h.central _) i
  have hy : (D ^ j * S ^ k) ^ 3 = 1 := by
    refine cube_mul_eq_one (c := Z ^ (2 * (k * j))) (h.pow_comm _) (h.S_pow_mul_D_pow k j) ?_ ?_ ?_
    · rw [← pow_mul, mul_comm, pow_mul, h.Z_cube, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, h.D_cube, one_pow]
    · rw [← pow_mul, mul_comm, pow_mul, h.S_cube, one_pow]
  rw [mul_assoc, hcomm.mul_pow, hy, mul_one, ← pow_mul, mul_comm, pow_mul, h.Z_cube, one_pow]

@[expose] def heisSubgroup (h : Heis3Rel S D Z) : Subgroup H where
  carrier := {x | ∃ i j k : ℕ, x = Z ^ i * D ^ j * S ^ k}
  mul_mem' := by
    rintro _ _ ⟨i, j, k, rfl⟩ ⟨i', j', k', rfl⟩
    exact ⟨_, _, _, h.mul_form i j k i' j' k'⟩
  one_mem' := ⟨0, 0, 0, by simp⟩
  inv_mem' := by
    rintro _ ⟨i, j, k, rfl⟩
    have hx := h.cube_form i j k
    have hinv : (Z ^ i * D ^ j * S ^ k)⁻¹ = (Z ^ i * D ^ j * S ^ k) * (Z ^ i * D ^ j * S ^ k) :=
      inv_eq_of_mul_eq_one_right (by rw [← pow_three]; exact hx)
    rw [hinv]
    exact ⟨_, _, _, h.mul_form i j k i j k⟩

theorem mem_heisSubgroup (h : Heis3Rel S D Z) {x : H} :
    x ∈ heisSubgroup h ↔ ∃ i j k : ℕ, x = Z ^ i * D ^ j * S ^ k := Iff.rfl

theorem Heis3Rel.cube_of_mem (h : Heis3Rel S D Z) {x : H} (hx : x ∈ heisSubgroup h) :
    x ^ 3 = 1 := by
  obtain ⟨i, j, k, rfl⟩ := hx
  exact h.cube_form i j k

theorem Heis3Rel.Z_mem (h : Heis3Rel S D Z) : Z ∈ heisSubgroup h := ⟨1, 0, 0, by simp⟩

theorem Heis3Rel.D_mem (h : Heis3Rel S D Z) : D ∈ heisSubgroup h := ⟨0, 1, 0, by simp⟩

theorem Heis3Rel.S_mem (h : Heis3Rel S D Z) : S ∈ heisSubgroup h := ⟨0, 0, 1, by simp⟩

theorem Heis3Rel.S_mul_D_ne (h : Heis3Rel S D Z) (hZ : Z ≠ 1) : S * D ≠ D * S := by
  intro hc
  have h2 : Z ^ 2 = 1 := by
    have := h.S_D
    rw [hc] at this
    exact mul_eq_right.mp this.symm
  apply hZ
  calc Z = Z ^ 3 * (Z ^ 2)⁻¹ := by group
    _ = 1 := by rw [h.Z_cube, h2]; simp

theorem card_heisSubgroup [Finite H] (hH : Nat.card H = 216) (h : Heis3Rel S D Z) (hZ : Z ≠ 1) :
    Nat.card (heisSubgroup h) = 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hp : IsPGroup 3 (heisSubgroup h) := fun x => ⟨1, by
    apply Subtype.ext
    simpa using h.cube_of_mem x.2⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hp
  have hdvd : Nat.card (heisSubgroup h) ∣ 216 := hH ▸ Subgroup.card_subgroup_dvd_card _
  have hnc : ¬ (∀ a b : heisSubgroup h, a * b = b * a) := by
    intro hab
    have := hab ⟨S, h.S_mem⟩ ⟨D, h.D_mem⟩
    exact h.S_mul_D_ne hZ (congrArg Subtype.val this)
  have hn3 : n < 4 := by
    by_contra hcon
    have hcon := not_lt.mp hcon
    have h81 : 3 ^ 4 ∣ 216 := (pow_dvd_pow 3 hcon).trans (hn ▸ hdvd)
    norm_num at h81
  interval_cases n
  · exfalso
    have hs := (Nat.card_eq_one_iff_unique.mp (by rw [hn]; norm_num)).1
    exact hnc fun a b => Subsingleton.elim _ _
  · exfalso
    haveI : IsCyclic (heisSubgroup h) := isCyclic_of_prime_card (p := 3) (by rw [hn]; norm_num)
    exact hnc (isMulCommutative_iff.mp (IsCyclic.isMulCommutative))
  · exfalso
    exact hnc (isMulCommutative_iff.mp (IsPGroup.isMulCommutative_of_card_eq_prime_sq hn))
  · rw [hn]; norm_num

theorem Heis3Rel.conj_mem (h : Heis3Rel S D Z) {F : H}
    (hFS : F * S = D * F) (hFD : F * D = S ^ 2 * F) {x : H} (hx : x ∈ heisSubgroup h) :
    F * x * F⁻¹ ∈ heisSubgroup h := by
  obtain ⟨i, j, k, rfl⟩ := hx
  have hZ' : MulAut.conj F Z = Z := by
    rw [MulAut.conj_apply, ← h.central F, mul_assoc]; group
  have hD' : MulAut.conj F D = S ^ 2 := by
    rw [MulAut.conj_apply, hFD]; group
  have hS' : MulAut.conj F S = D := by
    rw [MulAut.conj_apply, hFS]; group
  rw [← MulAut.conj_apply, map_mul, map_mul, map_pow, map_pow, map_pow, hZ', hD', hS', ← pow_mul]
  exact mul_mem (mul_mem (pow_mem h.Z_mem i) (pow_mem h.S_mem _)) (pow_mem h.D_mem k)

theorem Heis3Rel.F_mem_normalizer [Finite H] (h : Heis3Rel S D Z) {F : H}
    (hFS : F * S = D * F) (hFD : F * D = S ^ 2 * F) :
    F ∈ Subgroup.normalizer (heisSubgroup h : Set H) :=
  Subgroup.mem_normalizer_fintype fun _ hx => h.conj_mem hFS hFD hx

theorem heisSubgroup_normal [Finite H] (hH : Nat.card H = 216) (h : Heis3Rel S D Z) (hZ : Z ≠ 1)
    {F : H} (hFN : F ∈ Subgroup.normalizer (heisSubgroup h : Set H)) (hF : orderOf F = 4) :
    (heisSubgroup h).Normal := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E := heisSubgroup h with hE
  have hcE : Nat.card E = 27 := card_heisSubgroup hH h hZ
  set N := Subgroup.normalizer (E : Set H) with hNdef
  have h27 : 27 ∣ Nat.card N := hcE ▸ Subgroup.card_dvd_of_le Subgroup.le_normalizer
  have h4 : 4 ∣ Nat.card N := by
    have := orderOf_dvd_natCard (⟨F, hFN⟩ : N)
    rwa [Subgroup.orderOf_mk, hF] at this
  have h108 : 108 ∣ Nat.card N := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 4) h27 h4
    simpa using this
  have hidx : Nat.card N * N.index = 216 := hH ▸ N.card_mul_index
  have hidx2 : N.index = 1 ∨ N.index = 2 := by
    obtain ⟨m, hm⟩ := h108
    rw [hm] at hidx
    have hm2 : m * N.index = 2 := by
      have h' : 108 * (m * N.index) = 108 * 2 := by rw [← mul_assoc]; exact hidx
      omega
    have hdvd : N.index ∣ 2 := ⟨m, by rw [← hm2]; ring⟩
    exact (Nat.dvd_prime Nat.prime_two).mp hdvd
  have hEindex : E.index = 8 := by
    have := E.card_mul_index
    rw [hcE, hH] at this
    omega
  have hP : IsPGroup 3 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa using h.cube_of_mem x.2⟩
  let P : Sylow 3 H := hP.toSylow (by rw [hEindex]; norm_num)
  have hmod := card_sylow_modEq_one 3 H
  rw [Sylow.card_eq_index_normalizer P] at hmod
  have hPE : (P : Set H) = (E : Set H) := rfl
  rw [hPE] at hmod
  have hN1 : N.index = 1 := by
    rcases hidx2 with h1 | h2
    · exact h1
    · exfalso
      change N.index ≡ 1 [MOD 3] at hmod
      rw [h2] at hmod
      exact absurd hmod (by decide)
  exact Subgroup.normalizer_eq_top_iff.mp (Subgroup.index_eq_one.mp hN1)

theorem odd_mem_heisSubgroup [Finite H] (hH : Nat.card H = 216) (h : Heis3Rel S D Z)
    (hZ : Z ≠ 1) [(heisSubgroup h).Normal] {x : H} (hx : Odd (orderOf x)) :
    x ∈ heisSubgroup h := by
  set E := heisSubgroup h with hE
  have hcE : Nat.card E = 27 := card_heisSubgroup hH h hZ
  have hEindex : E.index = 8 := by
    have := E.card_mul_index
    rw [hcE, hH] at this
    omega
  have hdvd : orderOf x ∣ 8 * 27 := by
    have := orderOf_dvd_natCard x
    rw [hH] at this
    exact this
  have hcop : Nat.Coprime (orderOf x) 8 := by
    have h2 : Nat.Coprime (orderOf x) 2 := Nat.coprime_two_right.mpr hx
    simpa using Nat.Coprime.pow_right 3 h2
  have h27 : x ^ 27 = 1 := orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_left hdvd)
  have h8 : x ^ 8 ∈ E := hEindex ▸ Subgroup.pow_index_mem E x
  have hxx : x = (x ^ 8) ^ 17 := by
    calc x = (x ^ 27) ^ 5 * x := by rw [h27]; simp
      _ = (x ^ 8) ^ 17 := by rw [← pow_mul, ← pow_mul, ← pow_succ]
  rw [hxx]
  exact pow_mem h8 17

theorem closure_two_eq_top [Finite H] (hH : Nat.card H = 216) (h : Heis3Rel S D Z) (hZ : Z ≠ 1)
    {F : H} (hFS : F * S = D * F) (hFD : F * D = S ^ 2 * F) (hF4 : F ^ 4 = 1) :
    Subgroup.closure {x : H | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ := by
  set N2 := Subgroup.closure {x : H | ∃ k : ℕ, x ^ (2 ^ k) = 1} with hN2
  have mem2 : ∀ x : H, x ^ 2 = 1 → x ∈ N2 := fun x hx =>
    Subgroup.subset_closure ⟨1, by simpa using hx⟩
  have hFF : F ^ 2 * F ^ 2 = 1 := by rw [← pow_add]; exact hF4
  have hP2 : (F ^ 2) ^ 2 = 1 := by rw [← pow_mul]; exact hF4
  have hFS2 : F * S ^ 2 = D ^ 2 * F := by
    calc F * S ^ 2 = (F * S) * S := by rw [pow_two, mul_assoc]
      _ = D * F * S := by rw [hFS]
      _ = D * (F * S) := by rw [mul_assoc]
      _ = D * (D * F) := by rw [hFS]
      _ = D ^ 2 * F := by rw [pow_two, mul_assoc]
  have hPD : F ^ 2 * D = D ^ 2 * F ^ 2 := by
    calc F ^ 2 * D = F * (F * D) := by rw [pow_two, mul_assoc]
      _ = F * (S ^ 2 * F) := by rw [hFD]
      _ = (F * S ^ 2) * F := by rw [mul_assoc]
      _ = D ^ 2 * F * F := by rw [hFS2]
      _ = D ^ 2 * F ^ 2 := by rw [mul_assoc, ← pow_two]
  have hPS : F ^ 2 * S = S ^ 2 * F ^ 2 := by
    calc F ^ 2 * S = F * (F * S) := by rw [pow_two, mul_assoc]
      _ = F * (D * F) := by rw [hFS]
      _ = (F * D) * F := by rw [mul_assoc]
      _ = S ^ 2 * F * F := by rw [hFD]
      _ = S ^ 2 * F ^ 2 := by rw [mul_assoc, ← pow_two]
  have hPm : F ^ 2 ∈ N2 := mem2 _ hP2
  have conj2 : ∀ g : H, g * F ^ 2 * g⁻¹ ∈ N2 := fun g =>
    mem2 _ (by rw [conj_pow, hP2]; group)
  have hDm : D ∈ N2 := by
    have : D = F ^ 2 * (D * F ^ 2 * D⁻¹) := by
      calc D = D ^ 2 * (F ^ 2 * F ^ 2) * D⁻¹ := by rw [hFF]; group
        _ = (D ^ 2 * F ^ 2) * F ^ 2 * D⁻¹ := by simp only [mul_assoc]
        _ = (F ^ 2 * D) * F ^ 2 * D⁻¹ := by rw [hPD]
        _ = F ^ 2 * (D * F ^ 2 * D⁻¹) := by simp only [mul_assoc]
    rw [this]
    exact mul_mem hPm (conj2 D)
  have hSm : S ∈ N2 := by
    have : S = F ^ 2 * (S * F ^ 2 * S⁻¹) := by
      calc S = S ^ 2 * (F ^ 2 * F ^ 2) * S⁻¹ := by rw [hFF]; group
        _ = (S ^ 2 * F ^ 2) * F ^ 2 * S⁻¹ := by simp only [mul_assoc]
        _ = (F ^ 2 * S) * F ^ 2 * S⁻¹ := by rw [hPS]
        _ = F ^ 2 * (S * F ^ 2 * S⁻¹) := by simp only [mul_assoc]
    rw [this]
    exact mul_mem hPm (conj2 S)
  have hZ2 : Z ^ 2 ∈ N2 := by
    have : Z ^ 2 = S * D * S⁻¹ * D⁻¹ := by rw [h.S_D]; group
    rw [this]
    exact mul_mem (mul_mem (mul_mem hSm hDm) (inv_mem hSm)) (inv_mem hDm)
  have hZm : Z ∈ N2 := by
    have : Z = (Z ^ 2) ^ 2 := by
      calc Z = Z ^ 3 * Z := by rw [h.Z_cube, one_mul]
        _ = (Z ^ 2) ^ 2 := by group
    rw [this]
    exact pow_mem hZ2 2
  have hE_le : heisSubgroup h ≤ N2 := by
    rintro _ ⟨i, j, k, rfl⟩
    exact mul_mem (mul_mem (pow_mem hZm i) (pow_mem hDm j)) (pow_mem hSm k)
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime (G := H) 2 (n := 3)
    (by rw [hH]; norm_num)
  have hT_le : T ≤ N2 := by
    intro x hx
    apply Subgroup.subset_closure
    refine ⟨3, ?_⟩
    have := pow_card_eq_one' (G := T) (x := ⟨x, hx⟩)
    rw [hT] at this
    simpa using congrArg Subtype.val this
  have h27 : 27 ∣ Nat.card N2 := by
    have := Subgroup.card_dvd_of_le hE_le
    rwa [card_heisSubgroup hH h hZ] at this
  have h8 : 8 ∣ Nat.card N2 := by
    have := Subgroup.card_dvd_of_le hT_le
    rwa [hT] at this
  have h216 : 216 ∣ Nat.card N2 := by
    have := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 27 8) h27 h8
    simpa using this
  have hle : Nat.card N2 ∣ 216 := hH ▸ Subgroup.card_subgroup_dvd_card N2
  exact Subgroup.eq_top_of_card_eq _ (by rw [hH]; exact Nat.dvd_antisymm hle h216)

theorem shape_of_relations [Finite H] (hH : Nat.card H = 216) (h : Heis3Rel S D Z) (hZ : Z ≠ 1)
    {F : H} (hFS : F * S = D * F) (hFD : F * D = S ^ 2 * F) (hF2 : F ^ 2 ≠ 1) (hF4 : F ^ 4 = 1) :
    Subgroup.closure {x : H | ∃ k : ℕ, x ^ (2 ^ k) = 1} = ⊤ ∧
      ∀ x ∈ Subgroup.closure {x : H | x ∈ (⊤ : Subgroup H) ∧ Odd (orderOf x)}, x ^ 3 = 1 := by
  refine ⟨closure_two_eq_top hH h hZ hFS hFD hF4, ?_⟩
  have hord : orderOf F = 4 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := F) (by simpa using hF2)
      (by simpa using hF4)
    simpa using this
  haveI := heisSubgroup_normal hH h hZ (h.F_mem_normalizer hFS hFD) hord
  intro x hx
  refine h.cube_of_mem ?_
  have hle : Subgroup.closure {x : H | x ∈ (⊤ : Subgroup H) ∧ Odd (orderOf x)} ≤
      heisSubgroup h :=
    (Subgroup.closure_le _).mpr fun y hy => odd_mem_heisSubgroup hH h hZ hy.2
  exact hle hx

end Abstract

section Matrices

open CFSG.GH74.QTGen4.Leaves.F112 CFSG.Open

variable {K : Type} [Field K] (o : OmegaData K)

@[expose] noncomputable def sZ : SUg K := zS o.ω o.cube

theorem mat_sZ : mat (sZ o) = Matrix.scalar (Fin 3) o.ω := rfl

theorem sZ_central (x : SUg K) : sZ o * x = x * sZ o := by
  apply su_ext
  rw [mat_mul, mat_mul, mat_sZ]
  exact (Matrix.scalar_commute o.ω (fun r => Commute.all _ _) _).eq

theorem sZ_cube : sZ o ^ 3 = 1 := by
  apply su_ext
  rw [mat_pow, mat_sZ, mat_one, ← map_pow, o.cube, map_one]

theorem sZ_ne_one : sZ o ≠ 1 := by
  intro h
  have h1 := congrArg mat h
  rw [mat_sZ, mat_one] at h1
  have hω1 : o.ω = 1 := by simpa using congrFun (congrFun h1 0) 0
  have hq := o.hω
  rw [hω1] at hq
  have h01 : (1 : K) = 0 := by linear_combination hq + o.h2
  exact one_ne_zero h01

theorem sS_mul_sD :
    OmegaData.sS o * OmegaData.sD o = sZ o ^ 2 * (OmegaData.sD o * OmegaData.sS o) := by
  apply su_ext
  simp only [mat_mul, mat_pow, OmegaData.sS, OmegaData.sD, mat_suMk, mat_sZ]
  rw [mat_S_D o.hω o.h2, ← map_pow, Matrix.smul_eq_diagonal_mul, Matrix.scalar_apply]

theorem sF_mul_sS : OmegaData.sF o * OmegaData.sS o = OmegaData.sD o * OmegaData.sF o := by
  apply su_ext
  simp only [mat_mul, OmegaData.sS, OmegaData.sD, OmegaData.sF, mat_suMk]
  exact mat_F_S o.hω o.h2

theorem sF_mul_sD : OmegaData.sF o * OmegaData.sD o = OmegaData.sS o ^ 2 * OmegaData.sF o := by
  apply su_ext
  simp only [mat_mul, mat_pow, OmegaData.sS, OmegaData.sD, OmegaData.sF, mat_suMk, pow_two]
  exact mat_F_D o.hω o.h2

theorem mat_F_F : (mF o.ω : Matrix (Fin 3) (Fin 3) K) * mF o.ω = mP := by
  have hω := o.hω
  have h2 := o.h2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mF, mP, Matrix.mul_apply, Fin.sum_univ_three] <;> grind

theorem mat_P_P : (mP : Matrix (Fin 3) (Fin 3) K) * mP = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [mP, Matrix.mul_apply, Fin.sum_univ_three]

theorem sF_sq : OmegaData.sF o ^ 2 = OmegaData.sP o := by
  apply su_ext
  simp only [mat_pow, OmegaData.sF, OmegaData.sP, mat_suMk, pow_two]
  exact mat_F_F o

theorem sP_sq : OmegaData.sP o ^ 2 = 1 := by
  apply su_ext
  simp only [mat_pow, OmegaData.sP, mat_suMk, pow_two, mat_one]
  exact mat_P_P

theorem sP_ne_one : OmegaData.sP o ≠ 1 := by
  intro h
  have h1 := congrArg mat h
  simp only [OmegaData.sP, mat_suMk, mat_one] at h1
  have h11 := congrFun (congrFun h1 1) 1
  simp [mP] at h11

theorem sF_sq_ne_one : OmegaData.sF o ^ 2 ≠ 1 := by
  rw [sF_sq]
  exact sP_ne_one o

theorem sF_four : OmegaData.sF o ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, sF_sq, sP_sq]

theorem card_SUg [Finite K] (hK : Nat.card K = 4) : Nat.card (SUg K) = 216 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := CFSG.HardMathSupport.Solomon.Proving.charP_two_of_card_four K hK
  have h2 := CFSG.SectionRank.OddCover.card_statedSU_three (K := K) (p := 2) (f := 1)
    (by rw [hK]; norm_num)
  rw [pow_one] at h2
  rw [SUg, h2]
  norm_num

end Matrices

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SUThreeTwoShape

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.GH74.QTGen4.Leaves.F112 KFactProofs.SUThreeTwoShape

theorem kFactSUThreeTwoShape_holds : KFactSUThreeTwoShape := by
  intro K _ _ hK
  obtain ⟨ω, hω, h2⟩ := exists_omega hK
  let o : OmegaData K := ⟨ω, hω, h2⟩
  have hrel : Heis3Rel (OmegaData.sS o) (OmegaData.sD o) (sZ o) :=
    ⟨sZ_central o, sZ_cube o, OmegaData.sS_cube o, OmegaData.sD_cube o, sS_mul_sD o⟩
  exact shape_of_relations (card_SUg hK) hrel (sZ_ne_one o) (sF_mul_sS o) (sF_mul_sD o)
    (sF_sq_ne_one o) (sF_four o)

end CFSG.LocalAnalysis.RankThreeTheoremC
