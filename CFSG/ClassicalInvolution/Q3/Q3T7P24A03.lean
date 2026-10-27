module

public import CFSG.ClassicalInvolution.Q3.Q3T7P24A02
public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame
import CFSG.ClassicalInvolution.Q3.Q3T7P24EngA

public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace CFSG.ClassicalInvolution.Q3.Q3T8

abbrev _root_.CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.Frame4 :=
  @CFSG.ClassicalInvolution.Asc77.T7E.Frame4

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem involution_cases {K K' : Subgroup G} {z : G} (hs : Hyp23Setting Ω K K' z)
    {S : Sylow 2 G} {R R' : Subgroup G} (hR : IsSylow2In R K) (hR' : IsSylow2In R' K')
    (hRS : R ≤ (S : Subgroup G)) (hR'S : R' ≤ (S : Subgroup G)) {b b' u : G} (hb : b ∈ R)
    (hb' : b' ∈ R') (ob : orderOf b = 4) (ob' : orderOf b' = 4) (huK : u ∈ K ⊔ K')
    (huS : u ∈ (S : Subgroup G)) (hu2 : u * u = 1) (hu1 : u ≠ 1) (huz : u ≠ z)
    (hub : u * b = b * u) (hub' : u * b' = b' * u) : u = b * b' ∨ u = z * (b * b') := by
  exact CFSG.ClassicalInvolution.Q3.Q3T8.Asc77.T7E.involution_cases_of hs.stand.hyp hs.stand.mem hs.hK' hs.hne hs.hz hR hR' hRS
    hR'S hb hb' ob ob' huK huS hu2 hu1 huz hub hub'
end T7E
end Asc77

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K : Subgroup G} {u r z : G}

theorem DData.isSylow2In_centralizer (hΩ : Asc77.HypOmegaMod Ω)
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
  have hmem := Q3T7P24.lemma33_involution hΩ hd.memK hPsyl hy2 (hd.le_normalizer hyW)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp (hPC hx).2) r hd.r_memK
  rw [comm_eq_of_conj (k := 1) (hWc y hyW z hd.z_memW) (by rw [zpow_one]; exact hry),
    zpow_one] at hmem
  have hz1 : z = 1 := by
    have := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard K) hmem
      (isPGroup_zpowers_of_mul_self_eq_one (by rw [← mul_inv_rev, hd.uinv.sq, inv_one])
        (inv_ne_one.mpr hd.uinv.ne_one))
    exact inv_eq_one.mp this
  exact hd.uinv.ne_one hz1

theorem DData.inf_centralizer_le_normalizer (hΩ : Asc77.HypOmegaMod Ω) (hd : DData Ω W R K u r z)
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
  have hsyl := hd.isSylow2In_centralizer hΩ hWc hzAW hzA.sq hrzA
  have hle := Sec6Gen.inf_centralizer_le_normalizer (hypOmegaGen_of_mod hΩ) hd.memK hA
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

theorem DData.conjSub_mem_orbit (hΩ : Asc77.HypOmegaMod Ω)
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
    · exact hd.inf_centralizer_le_normalizer hΩ hWc hyW hy2 hry hAΩ hzA (Or.inl h) hVA
        hVW hV2 hV4 hx'
    · exact hd.inf_centralizer_le_normalizer hΩ hWc hyW hy2 hry hAΩ hzA (Or.inr h) hVA
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
end Disconnected.AschTight.Sec71

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W R K T J : Subgroup G} {u r z v t j : G}

theorem false_of_not_four_dvd (hΩ : Asc77.HypOmegaMod Ω)
    (hd : DData Ω W R K u r z) (hd' : DData Ω W T J v t j)
    (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hKJ : K ≠ J) (hzj : z ≠ j) {i k : ℤ}
    (hi : r * v * r⁻¹ = v * u ^ i) (hk : t * u * t⁻¹ = u * v ^ k) (hio : Odd i) (hko : Odd k)
    (hbad : ¬ (4 : ℤ) ∣ i * k - 1) (hA : AEmpty Ω K) : False := by
  obtain ⟨hJs, hJn⟩ := case_three_of_odd hΩ hd hd' hWc hKJ hk hko
  obtain ⟨g, hg, hgK⟩ := hA J hJs hJn z j hd.uinv hd'.uinv
  have hrj : r * j * r⁻¹ = j * z := by
    have := conj_pow_eq (hWc u hd.u_memW v hd'.u_memW) hi (orderOf u / 2)
    rwa [hd.j_eq hΩ hd', hd.z_eq, zpow_eq_self_of_odd hd.uinv.sq hio] at this
  have htz : t * z * t⁻¹ = z * j := by
    rw [conj_z_eq hΩ hd hd' hWc hk, zpow_eq_self_of_odd hd'.uinv.sq hko]
  have hrz : r * z * r⁻¹ = z := hd.uinv.conj_eq (conjSub_eq_self_of_mem hd.r_memK)
  have htj : t * j * t⁻¹ = j := hd'.uinv.conj_eq (conjSub_eq_self_of_mem hd'.r_memK)
  have hzj' : z * j = j * z := hWc z hd.z_memW j hd'.z_memW
  have hZ := fun {x : G} => mem_closure_pair_iff (x := x) hd.uinv.sq hd'.uinv.sq hzj'
  set H₀ := Subgroup.closure ({r, t} : Set G) with hH₀
  have hrH : r ∈ H₀ := Subgroup.subset_closure (by simp)
  have htH : t ∈ H₀ := Subgroup.subset_closure (by simp)
  have hH₀W : H₀ ≤ Subgroup.normalizer (W : Set G) := by
    rw [hH₀, Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · subst x
      exact hd.r_normW
    · rw [Set.mem_singleton_iff] at h
      subst x
      exact hd'.r_normW
  have hH₀Z : H₀ ≤ Subgroup.normalizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) := by
    rw [hH₀, Subgroup.closure_le]
    intro x hx
    rcases hx with h | h
    · subst x
      refine mem_normalizer_closure_pair ?_ ?_
      · rw [hrz, hZ]
        exact Or.inr (Or.inl rfl)
      · rw [hrj, hZ, ← hzj']
        exact Or.inr (Or.inr (Or.inr rfl))
    · rw [Set.mem_singleton_iff] at h
      subst x
      refine mem_normalizer_closure_pair ?_ ?_
      · rw [htz, hZ]
        exact Or.inr (Or.inr (Or.inr rfl))
      · rw [htj, hZ]
        exact Or.inr (Or.inr (Or.inl rfl))
  set 𝒪 : Set (Subgroup G) := {A | ∃ w ∈ H₀, A = conjSub w K} with h𝒪def
  obtain ⟨n, hn⟩ := hd.orderOf_eq
  have hU2 : IsPGroup 2 ↥(Subgroup.zpowers u) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have h𝒪 : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = z ∨ zA = j ∨ zA = z * j) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V := by
    rintro A ⟨w, hw, rfl⟩
    refine ⟨hΩ.conjInvariant w K hd.memK, w * z * w⁻¹, hd.uinv.conj w, ?_,
      conjSub w (Subgroup.zpowers u), conjSub_mono hd.U_le_K, ?_, isPGroup_conjSub w hU2,
      by rw [natCard_conjSub, Nat.card_zpowers]; exact hd.four_le⟩
    · have hzZ : w * z * w⁻¹ ∈ Subgroup.closure ({z, j} : Set G) :=
        conj_mem_of_mem_normalizer (hH₀Z hw) (Subgroup.subset_closure (by simp))
      rw [hZ] at hzZ
      rcases hzZ with h | h | h | h
      · exact absurd (conj_eq_one_iff.mp h) hd.uinv.ne_one
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · rw [← mem_normalizer_iff_conjSub_eq.mp (hH₀W hw)]
      exact conjSub_mono hd.U_le_W
  have h𝒪K : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = z ∨ zA = j ∨ zA = j * z) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V := by
    intro A hA
    obtain ⟨h1, zA, h2, h3, h4⟩ := h𝒪 A hA
    exact ⟨h1, zA, h2, by rw [← hzj']; exact h3, h4⟩
  have h𝒪J : ∀ A ∈ 𝒪, A ∈ Ω ∧ ∃ zA : G, IsUniqueInvolution A zA ∧
      (zA = j ∨ zA = z ∨ zA = z * j) ∧
      ∃ V : Subgroup G, V ≤ A ∧ V ≤ W ∧ IsPGroup 2 ↥V ∧ 4 ≤ Nat.card V := by
    intro A hA
    obtain ⟨h1, zA, h2, h3, h4⟩ := h𝒪 A hA
    refine ⟨h1, zA, h2, ?_, h4⟩
    rcases h3 with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr h)
  have h𝒪r : ∀ A ∈ 𝒪, conjSub r A ∈ 𝒪 := by
    rintro A ⟨w, hw, rfl⟩
    exact ⟨r * w, H₀.mul_mem hrH hw, (conjSub_mul r w K).symm⟩
  have h𝒪t : ∀ A ∈ 𝒪, conjSub t A ∈ 𝒪 := by
    rintro A ⟨w, hw, rfl⟩
    exact ⟨t * w, H₀.mul_mem htH hw, (conjSub_mul t w K).symm⟩
  have hgen : ∀ x ∈ ((K ⊓ Subgroup.normalizer
      ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) : Subgroup G) : Set G) ∪
      (J ⊓ Subgroup.normalizer ((Subgroup.closure ({z, j} : Set G) : Subgroup G) : Set G) :
        Subgroup G), ∀ A ∈ 𝒪, conjSub x A ∈ 𝒪 := by
    intro x hx
    rcases hx with hx | hx
    · exact hd.conjSub_mem_orbit hΩ hWc hd'.z_memW hd'.uinv.sq hrj h𝒪r h𝒪K hx
    · have hx' : x ∈ J ⊓ Subgroup.normalizer
          ((Subgroup.closure ({j, z} : Set G) : Subgroup G) : Set G) := by
        rw [Set.pair_comm]
        exact hx
      exact hd'.conjSub_mem_orbit hΩ hWc hd.z_memW hd.uinv.sq htz h𝒪t h𝒪J hx'
  have hpN : ∀ x ∈ pairNormalizers K J z j, ∀ A ∈ 𝒪, conjSub x A ∈ 𝒪 := by
    intro x hx
    rw [pairNormalizers, Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction'' with
    | mem x hx => exact hgen x hx
    | inv_mem x hx =>
      refine hgen x⁻¹ ?_
      rcases hx with hx | hx
      · exact Or.inl (Subgroup.inv_mem _ hx)
      · exact Or.inr (Subgroup.inv_mem _ hx)
    | one =>
      intro A hA
      rwa [conjSub_one]
    | mul x y _ _ hx hy =>
      intro A hA
      rw [conjSub_mul]
      exact hx _ (hy A hA)
  have hJ𝒪 : J ∈ 𝒪 := hgK ▸ hpN g hg K ⟨1, H₀.one_mem, (conjSub_one K).symm⟩
  obtain ⟨w, hw, hwJ⟩ := hJ𝒪
  exact conj_ne_of_quad hΩ hd hd' hWc hzj hi hk hko hbad hw (hH₀W hw) hwJ.symm
end Disconnected.AschTight.Sec71

end

section

namespace Disconnected.AschTight.Sec71
open CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected.AschTight.Sec71
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Asc77

theorem l7_1_proved : Asc77.L7_1 := by
  intro G _ _ Ω hΩ hcl hAe W hW R hR T hT u r v t hu hRur hv hTvt
  have : Fact (Q3CL.ClassicalClause Ω) := ⟨hcl⟩
  obtain ⟨K, z, hd⟩ := exists_dData hΩ hW hR hu hRur
  obtain ⟨J, j, hd'⟩ := exists_dData hΩ hW hT hv hTvt
  have hW2 := Sec7.isPGroup_of_mem_WSet hW
  have hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x := by
    obtain ⟨η, hη, hWη⟩ := id hW
    rw [hWη]
    obtain ⟨S, hS, hinv⟩ := hη
    exact ((Asc77.l6_9_proved G Ω hΩ S).2 η hS hinv).1
  by_cases hKJ : K = J
  · subst hKJ
    exact ⟨cap_case_one hΩ hd hd' hW2 hWc, Or.inl ⟨K, hd.memK, hd.le, hd'.le⟩⟩
  obtain ⟨i, hi⟩ := hd.exists_rel hd'.u_memW (hd.le_normalizer hd'.u_memW)
  obtain ⟨k, hk⟩ := hd'.exists_rel hd.u_memW (hd'.le_normalizer hd.u_memW)
  by_cases hzj : z = j
  · obtain ⟨hJ, hc⟩ := case_two_of_twin hΩ hd hd' hKJ hzj
    exact ⟨cap_case_two hd hd' hW2 hWc hc,
      Or.inr (Or.inl ⟨K, hd.memK, J, hd'.memK, hd.le, hd'.le, hJ, hc⟩)⟩
  by_cases hie : Even i
  · have hke := even_of_even hΩ hd hd' hWc hzj hi hk hie
    obtain ⟨hJ, hc⟩ := case_two_of_even hΩ hd hd' hWc hKJ hzj hi hk hie hke
    exact ⟨cap_case_two hd hd' hW2 hWc hc,
      Or.inr (Or.inl ⟨K, hd.memK, J, hd'.memK, hd.le, hd'.le, hJ, hc⟩)⟩
  have hio : Odd i := Int.not_even_iff_odd.mp hie
  have hko : Odd k := by
    by_contra hko'
    exact hie (even_of_even hΩ hd' hd hWc (Ne.symm hzj) hk hi
      (Int.not_odd_iff_even.mp hko'))
  obtain ⟨hJs, hJn⟩ := case_three_of_odd hΩ hd hd' hWc hKJ hk hko
  have h4 : (4 : ℤ) ∣ i * k - 1 := by
    by_contra hbad
    exact false_of_not_four_dvd hΩ hd hd' hWc hKJ hzj hi hk hio hko hbad
      (hAe K hd.memK)
  have hL := conj_eq_of_four_dvd hΩ hd hd' hW2 hWc hzj hi hk hio h4
  have hik := rel_of_conj_eq hΩ hd hd' hWc hzj hi hk hL
  have hbraid := braid_of_conj_eq hΩ hd hd' hWc hi hk hL
  refine ⟨cap_case_three hd hd' hW2 hWc hzj hi hk hko hbraid, Or.inr (Or.inr ⟨K, hd.memK, J,
    hd'.memK, hd.le, hd'.le, hJs, hJn, v ^ k, ?_, ?_, ?_⟩)⟩
  · obtain ⟨n, hn⟩ := hd'.orderOf_eq
    exact zpowers_zpow_eq_of_odd hn hko
  · rw [hd'.conj_inv_eq hWc hd.u_memW, hk, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have hvk : v ^ k ∈ W := W.zpow_mem hd'.u_memW k
    have huv : Commute u v := hWc u hd.u_memW v hd'.u_memW
    rw [hd.conj_inv_eq hWc hvk, ← conj_zpow, hi, ((huv.zpow_left i).symm).mul_zpow, ← zpow_mul,
      hik, mul_inv_cancel]
    exact Subgroup.one_mem _
end Disconnected.AschTight.Sec71

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution.Generic
namespace Thompson
open CFSG.ClassicalInvolution.Asc77.Thompson
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.conj_inv_eq_conj (c :
    Q3CL.Thompson.Ctx Ω W) (ρ : Rep Ω W) {x : G} (hx : x ∈ W) :
    ρ.r⁻¹ * x * ρ.r = ρ.r * x * ρ.r⁻¹ := by
  have hsq : ρ.r * ρ.r ∈ W := Q3CL.Thompson.D_sq_mem c.hΩ c.hW ρ.hR ρ.hr
  have hrN : ρ.r ∈ Subgroup.normalizer (W : Set G) := ρ.r_mem_normalizer
  have hy : ρ.r⁻¹ * x * ρ.r ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hrN) x).mp hx
    simpa using this
  have h := c.comm_W _ hsq _ hy
  calc ρ.r⁻¹ * x * ρ.r = ((ρ.r * ρ.r) * (ρ.r⁻¹ * x * ρ.r)) * (ρ.r * ρ.r)⁻¹ := by
        rw [h]; group
    _ = ρ.r * x * ρ.r⁻¹ := by group

theorem _root_.CFSG.ClassicalInvolution.Q3.Q3CL.Thompson.Ctx.rel_exact [hcl : Fact
    (Q3CL.ClassicalClause Ω)] (c : Q3CL.Thompson.Ctx Ω W) {ρ σ : Rep Ω W} (hne : ρ.K ≠ σ.K)
    (hnot : σ.K ∉ omegaNbr Ω ρ.K) {u : G} (hu : Subgroup.zpowers u = ρ.R ⊓ W) {v : G}
    (hv : Subgroup.zpowers v = σ.R ⊓ W) :
    ∃ v' : G, Subgroup.zpowers v' = Subgroup.zpowers v ∧ σ.r * u * σ.r⁻¹ = u * v' ∧
      ρ.r * v' * ρ.r⁻¹ = v' * u := by
  have hρcl := eq_closure_pair c.hΩ c.hW ρ.hR hu ρ.hr ρ.hrW
  have hσcl := eq_closure_pair c.hΩ c.hW σ.hR hv σ.hr σ.hrW
  obtain ⟨-, hcases⟩ := Disconnected.AschTight.Sec71.l7_1_proved G Ω c.hΩ hcl.out c.hA W
    c.hW ρ.R ρ.hR σ.R σ.hR u ρ.r v σ.r hu hρcl hv hσcl
  have h8 : ∀ (K : Subgroup G) (R : Subgroup G), IsSylow2In R K → R ∈ DSet Ω W → 4 ≤ Nat.card R :=
    fun K R hR hRD => by
      have := c.hΩ.eight_le_of_mem_RSet hRD.1
      omega
  have hρ2 : IsPGroup 2 ρ.R := ρ.hRK.2.1
  have hσ2 : IsPGroup 2 σ.R := σ.hRK.2.1
  have hρ8 := h8 ρ.K ρ.R ρ.hRK ρ.hR
  have hσ8 := h8 σ.K σ.R σ.hRK σ.hR
  rcases hcases with ⟨J, hJ, hRJ, hTJ⟩ | ⟨J, hJ, J', hJ', hRJ, hTJ', hnbr, -⟩ |
      ⟨J, hJ, J', hJ', hRJ, hTJ', -, -, v', hv', h1, h2⟩
  · exfalso
    exact hne ((c.hΩ.eq_of_le_of_le ρ.hK hJ hρ2 hρ8 ρ.hRK.1 hRJ).trans
      (c.hΩ.eq_of_le_of_le σ.hK hJ hσ2 hσ8 σ.hRK.1 hTJ).symm)
  · exfalso
    have e1 : ρ.K = J := c.hΩ.eq_of_le_of_le ρ.hK hJ hρ2 hρ8 ρ.hRK.1 hRJ
    have e2 : σ.K = J' := c.hΩ.eq_of_le_of_le σ.hK hJ' hσ2 hσ8 σ.hRK.1 hTJ'
    rw [e1, e2] at hnot
    exact hnot hnbr
  · have hv'W : v' ∈ W := by
      have : v' ∈ Subgroup.zpowers v := hv' ▸ Subgroup.mem_zpowers v'
      rw [hv] at this
      exact this.2
    have huW : u ∈ W := by
      have : u ∈ Subgroup.zpowers u := Subgroup.mem_zpowers u
      rw [hu] at this
      exact this.2
    have hσN : σ.r ∈ Subgroup.normalizer (W : Set G) := σ.r_mem_normalizer
    have hρN : ρ.r ∈ Subgroup.normalizer (W : Set G) := ρ.r_mem_normalizer
    refine ⟨v', hv', ?_, ?_⟩
    · have ha : σ.r⁻¹ * u * σ.r ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hσN) u).mp huW
        simpa using this
      have hb : (u * v')⁻¹ ∈ W := W.inv_mem (W.mul_mem huW hv'W)
      have h3 := eq_one_of_mem_inf_OCW c.hW (W.mul_mem ha hb) h1
      have h4 : σ.r⁻¹ * u * σ.r = u * v' := mul_inv_eq_one.mp h3
      rw [← c.conj_inv_eq_conj σ huW, h4]
    · have ha : ρ.r⁻¹ * v' * ρ.r ∈ W := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρN) v').mp hv'W
        simpa using this
      have hb : (v' * u)⁻¹ ∈ W := W.inv_mem (W.mul_mem hv'W huW)
      have h3 := eq_one_of_mem_inf_OCW c.hW (W.mul_mem ha hb) h2
      have h4 : ρ.r⁻¹ * v' * ρ.r = v' * u := mul_inv_eq_one.mp h3
      rw [← c.conj_inv_eq_conj ρ hv'W, h4]
end Thompson
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem inf_W_conj_of_img (c : Q3CL.Thompson.Ctx Ω W) {m : G}
    (hm : m ∈ Subgroup.normalizer (W : Set G)) (σ ρ₀ : Thompson.Rep Ω W)
    (h : σ.img = Thompson.piG W m * ρ₀.img * (Thompson.piG W m)⁻¹) :
    σ.K ⊓ W = conjSub m (ρ₀.K ⊓ W) := by
  have hK : σ.K = conjSub m ρ₀.K :=
    c.K_eq_of_img_eq σ (T7D.conjRep c.hΩ hm ρ₀) (by rw [T7D.conjRep_img]; exact h)
  rw [hK, conjSub_inf_W hm]
namespace Frame4
open CFSG.ClassicalInvolution.Asc77.T7E.Frame4

theorem exists_gens [hcl : Fact (Q3CL.ClassicalClause Ω)] (c : Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω
    W) :
    ∃ x₁ x₂ x₃ : G, Subgroup.zpowers x₁ = F.ρ.R ⊓ W ∧ Subgroup.zpowers x₂ = F.ρ'.R ⊓ W ∧
    Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W ∧
    F.ρ.r * x₁ * F.ρ.r⁻¹ = x₁⁻¹ ∧ F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂ ∧ F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁ ∧
    F.ρ'.r * x₁ * F.ρ'.r⁻¹ = x₁ ∧ F.ρ'.r * x₂ * F.ρ'.r⁻¹ = x₂⁻¹ ∧
    F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂ ∧
    F.ρ₃.r * x₁ * F.ρ₃.r⁻¹ = x₁ * x₃ ∧ F.ρ₃.r * x₂ * F.ρ₃.r⁻¹ = x₂ * x₃ ∧
    F.ρ₃.r * x₃ * F.ρ₃.r⁻¹ = x₃⁻¹ := by
  obtain ⟨x₁, h₁⟩ := Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW F.ρ.hR
  obtain ⟨v₂, hv₂⟩ := Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW F.ρ'.hR
  obtain ⟨v₃, hv₃⟩ := Thompson.exists_zpowers_eq_inf_W c.hΩ c.hW F.ρ₃.hR
  obtain ⟨x₃, hx₃, hs₁, hr₃⟩ := c.rel_exact F.hne₁ F.hn₁ h₁ hv₃
  have h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W := hx₃.trans hv₃
  obtain ⟨x₂, hx₂, ht₃, hs₂⟩ := c.rel_exact (F.hne₂.symm) F.hn₂' h₃ hv₂
  have h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W := hx₂.trans hv₂
  have m₁ : x₁ ∈ F.ρ.K ⊓ W := mem_inf_of_mem_inf (h₁ ▸ Subgroup.mem_zpowers x₁)
  have m₂ : x₂ ∈ F.ρ'.K ⊓ W := mem_inf_of_mem_inf (h₂ ▸ Subgroup.mem_zpowers x₂)
  have m₃ : x₃ ∈ F.ρ₃.K ⊓ W := mem_inf_of_mem_inf (h₃ ▸ Subgroup.mem_zpowers x₃)
  have cen : ∀ (ρ σ : Thompson.Rep Ω W), σ.K ∈ omegaNbr Ω ρ.K → ∀ {x : G}, x ∈ σ.K ⊓ W →
      ρ.r * x * ρ.r⁻¹ = x := fun ρ σ hnbr x hx => by
    rw [c.centralizes ρ σ hnbr hx]
    group
  refine ⟨x₁, x₂, x₃, h₁, h₂, h₃, c.conj_inv F.ρ m₁, cen _ _ F.hnbr m₂, hr₃,
    cen _ _ F.hnbr' m₁, c.conj_inv F.ρ' m₂, ht₃, hs₁, hs₂, c.conj_inv F.ρ₃ m₃⟩

theorem orders (c : Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω W) {x₁ x₂ x₃ : G}
    (h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W) (h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W)
    (h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W) :
    ∃ m : ℕ, 0 < m ∧ orderOf x₁ = 4 * m ∧ orderOf x₂ = 4 * m ∧ orderOf x₃ = 4 * m ∧
      x₁ ^ (2 * m) = F.z ∧ x₂ ^ (2 * m) = F.z ∧ x₃ ^ (2 * m) = F.j := by
  have hord : ∀ (ρ : Thompson.Rep Ω W) (x : G), Subgroup.zpowers x = ρ.R ⊓ W →
      2 * orderOf x = Nat.card ρ.R := by
    intro ρ x hx
    have h1 : orderOf x = Nat.card ↥(ρ.R ⊓ W) := by rw [← Nat.card_zpowers, hx]
    rw [h1]
    exact (Q3CL.Thompson.D_card c.hΩ c.hW ρ.hR).symm
  obtain ⟨N, hcard⟩ : ∃ N : ℕ, ∀ ρ : Thompson.Rep Ω W, Nat.card ρ.R = 2 ^ N :=
    by
      obtain ⟨N, hN⟩ := F.ρ.hRK.2.1.exists_card_eq
      exact ⟨N, fun ρ =>
          (CFSG.ClassicalInvolution.Disconnected.AschTight.Sec6Gen.natCard_isSylow2In_eq c.hΩ ρ.hK
          F.ρ.hK ρ.hRK
        F.ρ.hRK).trans hN⟩
  have h4 : 4 ≤ orderOf x₁ := by
    have := (Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW F.ρ.hR F.ρ.hK F.ρ.hRK).2.2.2.1
    rwa [← h₁, Nat.card_zpowers] at this
  have e₁ := hord F.ρ x₁ h₁
  have e₂ := hord F.ρ' x₂ h₂
  have e₃ := hord F.ρ₃ x₃ h₃
  rw [hcard] at e₁ e₂ e₃
  have hN3 : 3 ≤ N := by
    by_contra hlt
    have : 2 ^ N ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨k, hk⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have hpow : (2 : ℕ) ^ N = 8 * 2 ^ k := by rw [hk, pow_add]; ring
  have hm : 0 < 2 ^ k := pow_pos (by norm_num) k
  have o₁ : orderOf x₁ = 4 * 2 ^ k := by omega
  have o₂ : orderOf x₂ = 4 * 2 ^ k := by omega
  have o₃ : orderOf x₃ = 4 * 2 ^ k := by omega
  have m₁ : x₁ ∈ F.ρ.K := F.ρ.hRK.1 (h₁ ▸ Subgroup.mem_zpowers x₁ : x₁ ∈ F.ρ.R ⊓ W).1
  have m₂ : x₂ ∈ F.ρ'.K := F.ρ'.hRK.1 (h₂ ▸ Subgroup.mem_zpowers x₂ : x₂ ∈ F.ρ'.R ⊓ W).1
  have m₃ : x₃ ∈ F.ρ₃.K := F.ρ₃.hRK.1 (h₃ ▸ Subgroup.mem_zpowers x₃ : x₃ ∈ F.ρ₃.R ⊓ W).1
  exact ⟨2 ^ k, hm, o₁, o₂, o₃, pow_half_eq F.hz m₁ hm o₁, pow_half_eq F.hz' m₂ hm o₂,
    pow_half_eq F.hj m₃ hm o₃⟩

theorem W_le_closure (c : Q3CL.Thompson.Ctx Ω W) (F : Frame4 Ω W)
    {e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap)
    (hab : T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ')
    (hcomm : T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ)
    (hac : T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ) {x₁ x₂ x₃ : G}
    (h₁ : Subgroup.zpowers x₁ = F.ρ.R ⊓ W) (h₂ : Subgroup.zpowers x₂ = F.ρ'.R ⊓ W)
    (h₃ : Subgroup.zpowers x₃ = F.ρ₃.R ⊓ W) (r₂ : F.ρ.r * x₂ * F.ρ.r⁻¹ = x₂)
    (r₃ : F.ρ.r * x₃ * F.ρ.r⁻¹ = x₃ * x₁)
    (t₃ : F.ρ'.r * x₃ * F.ρ'.r⁻¹ = x₃ * x₂) :
    W ≤ Subgroup.closure ({x₁, x₂, x₃} : Set G) := by
  set Wc := Subgroup.closure ({x₁, x₂, x₃} : Set G) with hWc
  have hx₁ : x₁ ∈ Wc := Subgroup.subset_closure (by simp)
  have hx₂ : x₂ ∈ Wc := Subgroup.subset_closure (by simp)
  have hx₃ : x₃ ∈ Wc := Subgroup.subset_closure (by simp)
  have hKW : ∀ ρ : Thompson.Rep Ω W, ρ.K ⊓ W = ρ.R ⊓ W := fun ρ =>
    (Q3CL.Thompson.inf_W_of_mem_D c.hΩ c.hW ρ.hR ρ.hK ρ.hRK).1.symm
  have hsq : ∀ ρ : Thompson.Rep Ω W, ρ.img * ρ.img = 1 := fun ρ =>
    congrArg Subtype.val
      (Thompson.muDelta_mul_self c.hΩ c.hW (T7D.imgQ_mem ρ))
  have hinv : ∀ ρ : Thompson.Rep Ω W, ρ.img⁻¹ = ρ.img := fun ρ =>
    inv_eq_of_mul_eq_one_right (hsq ρ)
  have key : ∀ σ : Thompson.Rep Ω W, σ.K ⊓ W ≤ Wc := by
    intro σ
    rcases swap_word_cases he (T7D.imgQ_mem F.ρ) (T7D.imgQ_mem F.ρ') (T7D.imgQ_mem F.ρ₃) hab
      hcomm hac (T7D.imgQ_mem σ) with h | h | h | h | h | h
    · rw [c.K_eq_of_img_eq σ F.ρ (congrArg Subtype.val h), hKW, ← h₁]
      exact Subgroup.zpowers_le.mpr hx₁
    · rw [c.K_eq_of_img_eq σ F.ρ' (congrArg Subtype.val h), hKW, ← h₂]
      exact Subgroup.zpowers_le.mpr hx₂
    · rw [c.K_eq_of_img_eq σ F.ρ₃ (congrArg Subtype.val h), hKW, ← h₃]
      exact Subgroup.zpowers_le.mpr hx₃
    · have e1 : σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img := congrArg Subtype.val h
      have hval : σ.img = Thompson.piG W F.ρ.r * F.ρ₃.img * (Thompson.piG W F.ρ.r)⁻¹ := by
        show σ.img = F.ρ.img * F.ρ₃.img * F.ρ.img⁻¹
        rw [hinv]
        exact e1
      rw [inf_W_conj_of_img c F.ρ.r_mem_normalizer σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers', r₃]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem hx₃ hx₁)
    · have e1 : σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img := congrArg Subtype.val h
      have hval : σ.img = Thompson.piG W F.ρ'.r * F.ρ₃.img * (Thompson.piG W F.ρ'.r)⁻¹ := by
        show σ.img = F.ρ'.img * F.ρ₃.img * F.ρ'.img⁻¹
        rw [hinv]
        exact e1
      rw [inf_W_conj_of_img c F.ρ'.r_mem_normalizer σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers', t₃]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem hx₃ hx₂)
    · have e1 : σ.img = F.ρ.img * F.ρ'.img * F.ρ₃.img * F.ρ'.img * F.ρ.img :=
        congrArg Subtype.val h
      have hm : F.ρ.r * F.ρ'.r ∈ Subgroup.normalizer (W : Set G) :=
        Subgroup.mul_mem _ F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
      have hpm : Thompson.piG W (F.ρ.r * F.ρ'.r) = F.ρ.img * F.ρ'.img :=
        Thompson.piG_mul F.ρ.r_mem_normalizer F.ρ'.r_mem_normalizer
      have hval : σ.img = Thompson.piG W (F.ρ.r * F.ρ'.r) * F.ρ₃.img *
          (Thompson.piG W (F.ρ.r * F.ρ'.r))⁻¹ := by
        rw [hpm, mul_inv_rev, hinv, hinv, e1]
        simp only [mul_assoc]
      rw [inf_W_conj_of_img c hm σ F.ρ₃ hval, hKW, ← h₃, conjSub_zpowers']
      have : (F.ρ.r * F.ρ'.r) * x₃ * (F.ρ.r * F.ρ'.r)⁻¹ = x₃ * x₁ * x₂ := by
        calc (F.ρ.r * F.ρ'.r) * x₃ * (F.ρ.r * F.ρ'.r)⁻¹
            = F.ρ.r * (F.ρ'.r * x₃ * F.ρ'.r⁻¹) * F.ρ.r⁻¹ := by group
          _ = F.ρ.r * (x₃ * x₂) * F.ρ.r⁻¹ := by rw [t₃]
          _ = (F.ρ.r * x₃ * F.ρ.r⁻¹) * (F.ρ.r * x₂ * F.ρ.r⁻¹) := by group
          _ = x₃ * x₁ * x₂ := by rw [r₃, r₂]
      rw [this]
      exact Subgroup.zpowers_le.mpr (Wc.mul_mem (Wc.mul_mem hx₃ hx₁) hx₂)
  obtain ⟨η, ⟨S₀, hη, -⟩, hWη⟩ := c.hW
  obtain ⟨S, hWS⟩ := Thompson.exists_sylow_ge_of_mem_WSet c.hW
  have hηW : ∀ V ∈ η, V ≤ W := fun V hV => hWη ▸ le_iSup₂ (f := fun U (_ : U ∈ η) => U) V hV
  intro w hw
  rw [hWη] at hw
  refine (iSup₂_le (fun V hV => ?_) : (⨆ V ∈ η, V : Subgroup G) ≤ Wc) hw
  have hVU : V ∈ USet Ω := (hη.1 hV).1
  obtain ⟨J, hJ, hVJ⟩ := c.hΩ.exists_member_of_mem_USet hVU
  obtain ⟨T, hTD, hTJ⟩ := Q3CL.Thompson.exists_sylow_mem_DSet c.hΩ c.hW hWS hJ hVU hVJ
    ((hηW V hV).trans hWS)
  obtain ⟨σ, hσK, -⟩ := T7D.exists_rep c.hΩ c.hW hJ hTJ hTD
  have := key σ
  rw [hσK] at this
  exact (le_inf hVJ (hηW V hV)).trans this
end Frame4
end T7E
end Asc77

end

section

namespace Asc77
open CFSG.ClassicalInvolution.Asc77
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
    CFSG.ClassicalInvolution.Disconnected
namespace T7E
open CFSG.ClassicalInvolution.Asc77.T7E
variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
  {W : Subgroup G}

theorem exists_frame4_of_sylow [IsSimpleGroup G] {K K' : Subgroup G} {z : G}
    (hs : Hyp23Setting Ω K K' z) (hW : W ∈ WSet Ω) (hS4 : MuIsoS4 Ω W) {R R' : Subgroup G}
    (hRsyl : IsSylow2In R K) (hR'syl : IsSylow2In R' K') (hRD : R ∈ DSet Ω W)
    (hR'D : R' ∈ DSet Ω W) :
    ∃ (e : ↥(muGroup Ω W) ≃* Equiv.Perm (Fin 4)) (F : Frame4 Ω W),
      (∀ x, x ∈ Thompson.muDelta Ω W ↔ (e x).IsSwap) ∧ F.ρ.K = K ∧ F.ρ'.K = K' ∧ F.ρ.R = R ∧
      F.ρ'.R = R' ∧ F.z = z ∧ T7D.imgQ F.ρ ≠ T7D.imgQ F.ρ' ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ' = T7D.imgQ F.ρ' * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ ∧
      T7D.imgQ F.ρ' * T7D.imgQ F.ρ₃ ≠ T7D.imgQ F.ρ₃ * T7D.imgQ F.ρ' := by
  have hst : AscStand Ω K := hs.stand
  have hΩ : HypOmegaMod Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK' : K' ∈ Ω := hs.hK'.1
  have hz : IsUniqueInvolution K z := hs.hz
  have hz' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hz hs.hK'
  have c : Q3CL.Thompson.Ctx Ω W := T7D.ctx_of_stand hst hW
  obtain ⟨e, he⟩ := T7D.exists_swap_equiv hs hW hS4
  obtain ⟨ρ, hρK, hρR⟩ := T7D.exists_rep hΩ hW hK hRsyl hRD
  obtain ⟨ρ', hρ'K, hρ'R⟩ := T7D.exists_rep hΩ hW hK' hR'syl hR'D
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hne : ρ.K ≠ ρ'.K := by
    rw [hρK, hρ'K]
    exact hs.hne.symm
  have hρnbr : ρ'.K ∈ omegaNbr Ω ρ.K := by
    have hperp : K' ∈ KPerp Ω K := by rw [hs.perp]; exact Or.inr rfl
    rw [hρK, hρ'K]
    rcases hperp with e | e
    · exact absurd e hs.hne
    · exact e
  have hcomm : ρ.img * ρ'.img = ρ'.img * ρ.img := c.comm_of_omega ρ ρ' hρnbr
  have hρnbr' : ρ.K ∈ omegaNbr Ω ρ'.K := c.omega_of_comm ρ' ρ hne.symm hcomm.symm
  have hab : T7D.imgQ ρ ≠ T7D.imgQ ρ' := fun h =>
    hne (c.K_eq_of_img_eq ρ ρ' (congrArg Subtype.val h))
  have hcommQ : T7D.imgQ ρ * T7D.imgQ ρ' = T7D.imgQ ρ' * T7D.imgQ ρ := Subtype.ext hcomm
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ :=
    S4.exists_third he (T7D.imgQ_mem ρ) (T7D.imgQ_mem ρ') hab hcommQ
  obtain ⟨ρ₃, hρ₃⟩ := Thompson.exists_rep_of_mem_muDelta hc₃Δ
  have hc₃ : T7D.imgQ ρ₃ = c₃ := Subtype.ext hρ₃
  have hac' : T7D.imgQ ρ * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ := by rw [hc₃]; exact hac
  have hbc' : T7D.imgQ ρ' * T7D.imgQ ρ₃ ≠ T7D.imgQ ρ₃ * T7D.imgQ ρ' := by rw [hc₃]; exact hbc
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac' (by
    have h1 : T7D.imgQ ρ = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ ρ₃ h)
    rw [← h1])
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc' (by
    have h1 : T7D.imgQ ρ' = T7D.imgQ ρ₃ := Subtype.ext (c.img_eq_of_K_eq ρ' ρ₃ h)
    rw [← h1])
  obtain ⟨j, hj⟩ := hΩ.exists_uniqueInvolution ρ₃.hK
  refine ⟨e, ⟨ρ, ρ', ρ₃, z, j, hzρ, hzρ', hj, hρnbr, hρnbr', hne₁, hne₂, ?_, ?_, ?_, ?_⟩, he,
    hρK, hρ'K, hρR, hρ'R, rfl, hab, hcommQ, hac', hbc'⟩
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ ρ₃ h))
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ' ρ₃ h))
  · exact fun h => hac' (Subtype.ext (c.comm_of_omega ρ₃ ρ h).symm)
  · exact fun h => hbc' (Subtype.ext (c.comm_of_omega ρ₃ ρ' h).symm)
end T7E
end Asc77

end

end CFSG.ClassicalInvolution.Q3.Q3T8
