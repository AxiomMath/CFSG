module

public import CFSG.GF2Type.Aschbacher1976Full.HSPartCardBound
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Bad

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup MulAction

section Orbit

variable {G : Type*} [Group G]

theorem orbit_conjAct_eq (x : G) : orbit (ConjAct G) x = conjugatesOf x := by
  ext y
  rw [ConjAct.mem_orbit_conjAct]
  exact isConj_comm

theorem card_orbit_conjAct (x : G) :
    Nat.card (orbit (ConjAct G) x) = (centralizer {x} : Subgroup G).index := by
  rw [Nat.card_coe_set_eq, orbit_conjAct_eq, Subgroup.index_centralizer_eq_ncard]

theorem exists_card_orbit_eq_pow [Finite G] (hG : IsPGroup 2 G) (x : G) :
    ∃ n : ℕ, Nat.card (orbit (ConjAct G) x) = 2 ^ n := by
  rw [card_orbit_conjAct]
  exact hG.index _

theorem four_dvd_card_orbit [Finite G] (hG : IsPGroup 2 G) (x : G)
    (h : 8 ≤ Nat.card (orbit (ConjAct G) x)) : 4 ∣ Nat.card (orbit (ConjAct G) x) := by
  obtain ⟨n, hn⟩ := exists_card_orbit_eq_pow hG x
  rw [hn] at h ⊢
  have h3 : 3 ≤ n := by
    by_contra hlt
    have : 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (Nat.pow_dvd_pow 2 (by omega : 2 ≤ n))

theorem card_le_card_orbit_mul [Finite G] {T F : Subgroup G} (hFT : F ≤ T) {u : G} (hu : u ∈ T) :
    Nat.card F ≤ Nat.card (orbit (ConjAct T) (⟨u, hu⟩ : T)) *
      Nat.card (F ⊓ centralizer {u} : Subgroup G) := by
  have h1 : Nat.card (orbit (ConjAct T) (⟨u, hu⟩ : T)) =
      (centralizer {(⟨u, hu⟩ : T)} : Subgroup T).index := card_orbit_conjAct _
  have h2 : (centralizer {(⟨u, hu⟩ : T)} : Subgroup T).relIndex (F.subgroupOf T) ≤
      (centralizer {(⟨u, hu⟩ : T)} : Subgroup T).index := by
    rw [← relIndex_top_right]
    exact relIndex_le_of_le_right le_top
      (by rw [relIndex_top_right]; exact Subgroup.FiniteIndex.index_ne_zero)
  have h3 := relIndex_mul_card (centralizer {(⟨u, hu⟩ : T)} : Subgroup T) (F.subgroupOf T)
  have h4 : Nat.card (F.subgroupOf T) = Nat.card F :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFT).toEquiv
  have h5 : Nat.card ((centralizer {(⟨u, hu⟩ : T)} : Subgroup T) ⊓ F.subgroupOf T : Subgroup T) ≤
      Nat.card (F ⊓ centralizer {u} : Subgroup G) := by
    refine Nat.card_le_card_of_injective
      (fun y => (⟨((y : T) : G), (Subgroup.mem_inf.mp y.2).2, ?_⟩ : ↥(F ⊓ centralizer {u}))) ?_
    · have h' := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp y.2).1
      exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h')
    · intro a b hab
      have h' := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h')
  calc Nat.card F = Nat.card (F.subgroupOf T) := h4.symm
    _ = _ := h3.symm
    _ ≤ Nat.card (orbit (ConjAct T) (⟨u, hu⟩ : T)) *
        Nat.card (F ⊓ centralizer {u} : Subgroup G) := by
      rw [h1]
      exact Nat.mul_le_mul h2 h5

end Orbit

section Setting

variable {G : Type} [Group G] [Finite G] {z : G} {Z A : Subgroup G} {T : Sylow 2 G} {k : G}

theorem conjugate_zpowers (x g : G) : conjugate (zpowers x) g = zpowers (g⁻¹ * x * g) := by
  show (zpowers x).map (MulAut.conj g⁻¹).toMonoidHom = zpowers (g⁻¹ * x * g)
  rw [MonoidHom.map_zpowers]
  simp [MulAut.conj_apply]

theorem commute_of_sq_eq_one {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : (a * b) ^ 2 = 1) :
    a * b = b * a := by
  have h1 : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rwa [← sq])
  have h2 : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by rwa [← sq])
  have h3 : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by rwa [← sq])
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b * a := by rw [mul_inv_rev, h1, h2]

theorem commute_k_of_mem_F (c : BL.Ctx z 2 Z A T) (hZk : Z = zpowers k) {x : G} (hx : x ∈ Fz z) :
    x * k = k * x :=
  (Width.Z_comm_F c.hD (hZk ▸ mem_zpowers k) hx).symm

theorem ZF_conj_eq_zpowers (c : BL.Ctx z 2 Z A T) (hZk : Z = zpowers k) (g : G) :
    ZF (g⁻¹ * z * g) = zpowers (g⁻¹ * k * g) := by
  rw [c.ZF_conj_eq g, hZk, conjugate_zpowers]

theorem odd_relIndex (c : BL.Ctx z 2 Z A T) : Odd ((T : Subgroup G).relIndex (Hz z)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := relIndex_mul_index c.hTH
  have h2 : ¬ 2 ∣ (T : Subgroup G).index := T.not_dvd_index
  have h3 : ¬ 2 ∣ (T : Subgroup G).relIndex (Hz z) := fun h => h2 (h1 ▸ Dvd.dvd.mul_right h _)
  exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h3)

theorem not_commute_z_conj (c : BL.Ctx z 2 Z A T) (hti : HSTI z) (hZk : Z = zpowers k) {g : G}
    (hu : g⁻¹ * z * g * k ≠ k * (g⁻¹ * z * g)) : z * (g⁻¹ * k * g) ≠ g⁻¹ * k * g * z := by
  intro h
  have hkuH : g⁻¹ * k * g ∈ Hz z := Subgroup.mem_centralizer_singleton_iff.mpr h.symm
  have hzk : z * k = k * z :=
    Width.Z_comm_F c.hD c.hD.mem_z (c.Z_le_F (hZk ▸ mem_zpowers k))
  have hDinv : g⁻¹ * z * g ∈ Dinv z := by
    refine ⟨isConj_iff.mpr ⟨g⁻¹, by simp⟩, fun heq => hu ?_, ?_⟩
    · rw [heq]
      exact hzk
    · rw [ZF_conj_eq_zpowers c hZk g]
      exact zpowers_le.mpr hkuH
  exact hu (commute_k_of_mem_F c hZk (hti.2 _ hDinv).1)

theorem sq_eq_one_of_commute (c : BL.Ctx z 2 Z A T) (hti : HSTI z) (hZk : Z = zpowers k) {g : G}
    (hu : g⁻¹ * z * g * k ≠ k * (g⁻¹ * z * g)) {x : G} (hx : x ∈ Fz z)
    (hxu : x * (g⁻¹ * z * g) = g⁻¹ * z * g * x) : x ^ 2 = 1 := by
  rcases Width.sq_F c.hD c.hz hx with h1 | h1
  · exact h1
  exfalso
  obtain ⟨h, hh⟩ : ∃ h : G, h = g * x * g⁻¹ := ⟨_, rfl⟩
  have hxh : x = g⁻¹ * h * g := by rw [hh]; group
  have hhH : h ∈ Hz z := by
    rw [Subgroup.mem_centralizer_singleton_iff, hh]
    calc g * x * g⁻¹ * z = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * z * g * x) * g⁻¹ := by rw [hxu]
      _ = z * (g * x * g⁻¹) := by group
  have h2 := Width.sq_trivial c.hD c.hz hhH k (hZk ▸ mem_zpowers k)
  have h3 : h * h * k = k * (h * h) :=
    calc h * h * k = (h * (h * k * h⁻¹) * h⁻¹) * (h * h) := by group
      _ = k * (h * h) := by rw [h2]
  apply not_commute_z_conj c hti hZk hu
  have key : x ^ 2 * (g⁻¹ * k * g) = g⁻¹ * k * g * x ^ 2 :=
    calc x ^ 2 * (g⁻¹ * k * g) = g⁻¹ * (h * h * k) * g := by rw [hxh, sq]; group
      _ = g⁻¹ * (k * (h * h)) * g := by rw [h3]
      _ = g⁻¹ * k * g * x ^ 2 := by rw [hxh, sq]; group
  rwa [h1] at key

theorem eight_le_card_orbit (c : BL.Ctx z 2 Z A T) (hti : HSTI z) (hZk : Z = zpowers k)
    {u : G} (huT : u ∈ (T : Subgroup G)) (huz : IsConj z u) (huk : u * k ≠ k * u) :
    8 ≤ Nat.card (orbit (ConjAct (T : Subgroup G)) (⟨u, huT⟩ : (T : Subgroup G))) := by
  obtain ⟨g, rfl⟩ := BL.exists_inv_conj huz
  have hsq : ∀ x ∈ Fz z ⊓ centralizer {g⁻¹ * z * g}, x ^ 2 = 1 := fun x hx =>
    sq_eq_one_of_commute c hti hZk huk hx.1 (Subgroup.mem_centralizer_singleton_iff.mp hx.2)
  have hU : CFSG.Open.IsElemAbelian 2 (Fz z ⊓ centralizer {g⁻¹ * z * g}) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hsq⟩
    exact commute_of_sq_eq_one (hsq a a.2) (hsq b b.2) (hsq _ (Subgroup.mul_mem _ a.2 b.2))
  have hle8 : Nat.card (Fz z ⊓ centralizer {g⁻¹ * z * g} : Subgroup G) ≤ 8 := by
    have := Card.card_elemAbelian_le c.hD c.hz inf_le_left hU
    simpa using this
  have h64 : Nat.card (Fz z) = 64 := by
    have := Width.card_Fz c.hD c.hz
    simpa using this
  have hmain := card_le_card_orbit_mul c.F_le_T huT
  by_contra hlt
  rw [not_le] at hlt
  have : Nat.card (orbit (ConjAct (T : Subgroup G)) (⟨g⁻¹ * z * g, huT⟩ : (T : Subgroup G))) *
      Nat.card (Fz z ⊓ centralizer {g⁻¹ * z * g} : Subgroup G) ≤ 7 * 8 :=
    Nat.mul_le_mul (by omega) hle8
  omega

theorem four_dvd_card_orbit_of_ne (c : BL.Ctx z 2 Z A T) (hti : HSTI z) (hZk : Z = zpowers k)
    {u : G} (huT : u ∈ (T : Subgroup G)) (huz : IsConj z u) (huk : u * k ≠ k * u) :
    4 ∣ Nat.card (orbit (ConjAct (T : Subgroup G)) (⟨u, huT⟩ : (T : Subgroup G))) :=
  four_dvd_card_orbit T.isPGroup' _ (eight_le_card_orbit c hti hZk huT huz huk)

end Setting

end CFSG.GF2Type.Aschbacher1976Full.HS.Bad
