module

public import CFSG.ClassicalInvolution.AschTight.Sec6Gen64C
public import CFSG.ClassicalInvolution.AschTight.HypOmegaGenMod
public import CFSG.ClassicalInvolution.Asc77.AscL62Lem33
public import CFSG.ClassicalInvolution.AschTight.Sec71Basic
public import CFSG.ClassicalInvolution.AschTight.Sec71Rel

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {W R K : Subgroup G} {u r z : G}

theorem DData.isSylow2In_centralizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hd : DData Ω W R K u r z) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {y : G} (hyW : y ∈ W)
    (hy2 : y * y = 1) (hry : r * y * r⁻¹ = y * z) :
    IsSylow2In (Subgroup.zpowers u) (K ⊓ Subgroup.centralizer ({y} : Set G)) := by
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  refine ⟨le_inf hd.U_le_K (Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr (hWc u hd.u_memW y hyW))), hU2,
    fun P hPC hP2 hUP => ?_⟩
  by_contra hne
  obtain ⟨m, hm⟩ := Subgroup.card_dvd_of_le hUP
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [mul_one] at hm
    exact hne (Subgroup.eq_of_le_of_card_ge hUP hm.le).symm
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hm
    exact Nat.card_pos.ne' hm
  have hcard : Nat.card R ≤ Nat.card P := by
    rw [hd.card, hm, Nat.card_zpowers, mul_comm 2]
    exact Nat.mul_le_mul_left _ (by omega)
  have hPsyl := hd.sylow.of_natCard_le hP2 (hPC.trans inf_le_left) hcard
  have hmem := lemma_3_3_member_involution hp hq hΩ hd.memK hPsyl hy2 (hd.le_normalizer hyW)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hPC hx).2) r hd.r_memK
  rw [comm_eq_of_conj (k := 1) (hWc y hyW z hd.z_memW) (by rw [zpow_one]; exact hry),
    zpow_one] at hmem
  have hz1 : z = 1 := by
    have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
      (isPGroup_zpowers_of_mul_self_eq_one (by rw [← mul_inv_rev, hd.uinv.sq, inv_one])
        (inv_ne_one.mpr hd.uinv.ne_one))
    exact inv_eq_one.mp this
  exact hd.uinv.ne_one hz1

theorem DData.inf_centralizer_le_normalizer (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hΩ : HypOmegaMod p f Ω) (hd : DData Ω W R K u r z)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {y : G} (hyW : y ∈ W) (hy2 : y * y = 1)
    (hry : r * y * r⁻¹ = y * z) {A : Subgroup G} (hA : A ∈ Ω) {zA : G}
    (hzA : IsUniqueInvolution A zA) (hzAy : zA = y ∨ zA = y * z) {V : Subgroup G}
    (hVA : V ≤ A) (hVW : V ≤ W) (hV2 : IsPGroup 2 ↥V) (hV4 : 4 ≤ Nat.card V) :
    K ⊓ Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (A : Set G) := by
  have hrz : r * z * r⁻¹ = z := hd.uinv.conj_eq (conjSub_eq_self_of_mem hd.r_memK)
  have hzAW : zA ∈ W := by
    rcases hzAy with rfl | rfl
    · exact hyW
    · exact W.mul_mem hyW hd.z_memW
  have hrzA : r * zA * r⁻¹ = zA * z := by
    rcases hzAy with rfl | rfl
    · exact hry
    · calc r * (y * z) * r⁻¹ = (r * y * r⁻¹) * (r * z * r⁻¹) := by group
        _ = y * z * z := by rw [hry, hrz]
  have hzAz : zA ≠ z := by
    intro h
    rw [h, hrz] at hrzA
    apply hd.uinv.ne_one
    calc z = z * z * z⁻¹ := by group
      _ = 1 := by rw [← hrzA, mul_inv_cancel]
  have hKA : K ≠ A := fun h => hzAz (hzA.eq (h ▸ hd.uinv))
  have hsyl := hd.isSylow2In_centralizer hp hq hΩ hWc hzAW hzA.sq hrzA
  have hle := Sec6Gen.inf_centralizer_le_normalizer (hypOmegaGen_of_mod hp hq hΩ) hd.memK hA
    hKA hzA hsyl inferInstance (by rw [Nat.card_zpowers]; exact hd.four_le) hVA hV2 hV4
    (hVW.trans hd.le_normalizer) (fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hWc x (hVW hx) zA hzAW))
  intro x hx
  refine hle ⟨hx.1, ?_⟩
  show x ∈ Subgroup.centralizer ({zA} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hxy : x * y = y * x := Subgroup.mem_centralizer_singleton_iff.mp hx.2
  have hxz : z * x = x * z := hd.uinv.commute_of_mem hx.1
  rcases hzAy with rfl | rfl
  · exact hxy
  · calc x * (y * z) = (x * y) * z := by group
      _ = (y * x) * z := by rw [hxy]
      _ = y * (x * z) := by group
      _ = y * (z * x) := by rw [hxz]
      _ = y * z * x := by group

theorem DData.conjSub_mem_orbit (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hd : DData Ω W R K u r z) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) {y : G} (hyW : y ∈ W)
    (hy2 : y * y = 1) (hry : r * y * r⁻¹ = y * z) {𝒪 : Set (Subgroup G)}
    (h𝒪r : ∀ A ∈ 𝒪, conjSub r A ∈ 𝒪)
    (h𝒪 : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = z ∨ zA = y ∨ zA = y * z) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V)
    {x : G} (hx : x ∈ K ⊓ Subgroup.normalizer ((Subgroup.closure {z, y} : Subgroup G) : Set G)) :
    ∀ A ∈ 𝒪, conjSub x A ∈ 𝒪 := by
  have hC : ∀ x' ∈ K ⊓ Subgroup.centralizer ({y} : Set G), ∀ A ∈ 𝒪, conjSub x' A = A := by
    intro x' hx' A hA
    obtain ⟨hAΩ, zA, hzA, hzA3, V, hVA, hVW, hV2, hV4⟩ := h𝒪 A hA
    apply mem_normalizer_iff_conjSub_eq.mp
    rcases hzA3 with h | h | h
    · subst h
      by_cases hAK : A = K
      · rw [hAK]
        exact Subgroup.le_normalizer hx'.1
      · exact hΩ.le_normalizer_of_twin hd.memK hAΩ (Ne.symm hAK) hd.uinv hzA hx'.1
    · exact hd.inf_centralizer_le_normalizer hp hq hΩ hWc hyW hy2 hry hAΩ hzA (Or.inl h) hVA
        hVW hV2 hV4 hx'
    · exact hd.inf_centralizer_le_normalizer hp hq hΩ hWc hyW hy2 hry hAΩ hzA (Or.inr h) hVA
        hVW hV2 hV4 hx'
  have hzy : z * y = y * z := hWc z hd.z_memW y hyW
  have hxz : x * z * x⁻¹ = z := hd.uinv.conj_eq (conjSub_eq_self_of_mem hx.1)
  have hxy : x * y * x⁻¹ ∈ Subgroup.closure ({z, y} : Set G) :=
    (Subgroup.mem_normalizer_iff.mp hx.2 y).mp (Subgroup.subset_closure (by simp))
  rw [mem_closure_pair_iff hd.uinv.sq hy2 hzy] at hxy
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [mul_one, mul_inv_cancel, one_mul] at hry
    exact hd.uinv.ne_one hry.symm
  intro A hA
  rcases hxy with h | h | h | h
  · exact absurd (conj_eq_one_iff.mp h) hy1
  · exfalso
    rw [← hxz] at h
    have hyz : y = z := mul_left_cancel (mul_right_cancel h)
    rw [hyz, hd.uinv.conj_eq (conjSub_eq_self_of_mem hd.r_memK), hd.uinv.sq] at hry
    exact hd.uinv.ne_one hry
  · have hx' : x ∈ K ⊓ Subgroup.centralizer ({y} : Set G) := by
      refine ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [h]
    rw [hC x hx' A hA]
    exact hA
  · have hry' : r⁻¹ * y * r = y * z := by rw [hd.conj_inv_eq hWc hyW, hry]
    have hx' : x * r⁻¹ ∈ K ⊓ Subgroup.centralizer ({y} : Set G) := by
      refine ⟨K.mul_mem hx.1 (K.inv_mem hd.r_memK), Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have e : x * r⁻¹ * y * (x * r⁻¹)⁻¹ = y := by
        calc x * r⁻¹ * y * (x * r⁻¹)⁻¹ = x * (r⁻¹ * y * r) * x⁻¹ := by group
          _ = (x * y * x⁻¹) * (x * z * x⁻¹) := by rw [hry']; group
          _ = z * y * z := by rw [h, hxz]
          _ = y := by rw [hzy, mul_assoc, hd.uinv.sq, mul_one]
      calc x * r⁻¹ * y = (x * r⁻¹ * y * (x * r⁻¹)⁻¹) * (x * r⁻¹) := by group
        _ = y * (x * r⁻¹) := by rw [e]
    have e : conjSub x A = conjSub (x * r⁻¹) (conjSub r A) := by
      rw [← conjSub_mul, inv_mul_cancel_right]
    rw [e, hC _ hx' _ (h𝒪r A hA)]
    exact h𝒪r A hA

end CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
