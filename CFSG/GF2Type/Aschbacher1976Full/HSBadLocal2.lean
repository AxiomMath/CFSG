module

public import CFSG.GF2Type.Aschbacher1976Full.HSBadLocal
public import CFSG.GF2Type.Aschbacher1976Full.HSBurnsideLayer2

public section

namespace CFSG.GF2Type.Aschbacher1976Full.HS.Bad

open CFSG CFSG.Blueprint CFSG.GF2Type.CenterFour Subgroup

variable {G : Type} [Group G] [Finite G] {z : G} {Z A : Subgroup G} {T : Sylow 2 G} {k : G}

structure Setup (z : G) (Z A : Subgroup G) (T : Sylow 2 G) (k : G) : Prop where
  ctx : BL.Ctx z 2 Z A T
  ti : HSTI z
  Zk : Z = zpowers k
  sq : k ^ 2 = z

theorem orderOf_conj_inv (x g : G) : orderOf (g⁻¹ * x * g) = orderOf x := by
  have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
  simpa [MulAut.conj_apply] using this

namespace Setup

variable (s : Setup z Z A T k)
include s

theorem ord : orderOf k = 4 := by
  have h := Nat.card_zpowers k
  rw [← s.Zk, s.ctx.hD.card_Z] at h
  exact h.symm

theorem ord_conj (g : G) : orderOf (g⁻¹ * k * g) = 4 := (orderOf_conj_inv k g).trans s.ord

theorem conj_sq (g : G) : (g⁻¹ * k * g) ^ 2 = g⁻¹ * z * g := by
  rw [← s.sq, pow_two, pow_two]
  group

end Setup

theorem eq_or_eq_inv_of_mem_zpowers {y y' : G} (hy : orderOf y = 4) (hy' : orderOf y' = 4)
    (h : y' ∈ zpowers y) : y' = y ∨ y' = y⁻¹ := by
  obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp h
  have hy4 : y ^ 4 = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  have hi : y ^ (i % 4) = y ^ i := by
    have := zpow_mod_orderOf y i
    rwa [hy] at this
  have h4 : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3 := by omega
  rcases h4 with h4 | h4 | h4 | h4
  · rw [h4, zpow_zero] at hi
    rw [← hi, orderOf_one] at hy'
    omega
  · left
    rw [h4, zpow_one] at hi
    exact hi.symm
  · exfalso
    rw [h4] at hi
    have h2 : (y ^ i) ^ 2 = 1 := by
      rw [← hi, ← zpow_natCast, ← zpow_mul]
      simpa using hy4
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hy'] at this
    omega
  · right
    rw [h4] at hi
    rw [← hi]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← zpow_add_one]
    norm_num
    exact hy4

namespace Setup

variable (s : Setup z Z A T k)
include s

theorem gen_eq_or_inv {g₁ g₂ : G} (h : g₁⁻¹ * z * g₁ = g₂⁻¹ * z * g₂) :
    g₁⁻¹ * k * g₁ = g₂⁻¹ * k * g₂ ∨ g₁⁻¹ * k * g₁ = (g₂⁻¹ * k * g₂)⁻¹ := by
  have hZF : zpowers (g₁⁻¹ * k * g₁) = zpowers (g₂⁻¹ * k * g₂) := by
    rw [← ZF_conj_eq_zpowers s.ctx s.Zk, ← ZF_conj_eq_zpowers s.ctx s.Zk, h]
  have hmem : g₁⁻¹ * k * g₁ ∈ zpowers (g₂⁻¹ * k * g₂) := hZF ▸ mem_zpowers _
  exact eq_or_eq_inv_of_mem_zpowers (s.ord_conj g₂) (s.ord_conj g₁) hmem

theorem invol_mem {g : G} (h : g⁻¹ * k * g ∈ (T : Subgroup G)) :
    IsConj z (g⁻¹ * z * g) ∧ ZF (g⁻¹ * z * g) ≤ (T : Subgroup G) :=
  ⟨isConj_iff.mpr ⟨g⁻¹, by simp⟩, by
    rw [ZF_conj_eq_zpowers s.ctx s.Zk g]
    exact zpowers_le.mpr h⟩

theorem invol_ne {g : G} (h : g⁻¹ * k * g ∉ zpowers k) : g⁻¹ * z * g ≠ z := by
  intro heq
  have := s.gen_eq_or_inv (g₁ := g) (g₂ := 1) (by simpa using heq)
  simp only [inv_one, one_mul, mul_one] at this
  rcases this with h1 | h1
  · exact h (by rw [h1]; exact mem_zpowers k)
  · exact h (by rw [h1]; exact inv_mem (mem_zpowers k))

end Setup

theorem eq_or_eq_mul (c : BL.Ctx z 2 Z A T) (hti : HSTI z)
    (hcard : Nat.card (ET (T : Subgroup G) z) = 4) {v w : G}
    (hv : IsConj z v ∧ ZF v ≤ (T : Subgroup G)) (hvz : v ≠ z)
    (hw : IsConj z w ∧ ZF w ≤ (T : Subgroup G)) (hwz : w ≠ z) : w = v ∨ w = v * z := by
  classical
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hwv, hwvz⟩ := hne
  have hz1 : z ≠ 1 := BL.ne_one_of_isConj c.hz (IsConj.refl z)
  have hv1 : v ≠ 1 := BL.ne_one_of_isConj c.hz hv.1
  have hw1 : w ≠ 1 := BL.ne_one_of_isConj c.hz hw.1
  have hzz : z * z = 1 := BL.mul_self_of_isConj c.hz (IsConj.refl z)
  have hvz1 : v * z ≠ 1 := fun h => hvz (by
    rw [← inv_eq_of_mul_eq_one_right hzz]
    exact eq_inv_of_mul_eq_one_left h)
  have hzvz : z ≠ v * z := fun h =>
    hv1 (mul_right_cancel (b := z) (by rw [one_mul]; exact h.symm))
  have hvvz : v ≠ v * z := fun h =>
    hz1 (mul_left_cancel (a := v) (by rw [mul_one]; exact h.symm))
  have hvw : v ≠ w := fun h => hwv h.symm
  have hvzw : v * z ≠ w := fun h => hwvz h.symm
  have hzE : z ∈ ET (T : Subgroup G) z :=
    (c.mem_ET_iff hti).mpr (Or.inr ⟨IsConj.refl z, by rw [c.ZF_self]; exact c.Z_le_T⟩)
  have hvE : v ∈ ET (T : Subgroup G) z := (c.mem_ET_iff hti).mpr (Or.inr hv)
  have hwE : w ∈ ET (T : Subgroup G) z := (c.mem_ET_iff hti).mpr (Or.inr hw)
  have hvzE : v * z ∈ ET (T : Subgroup G) z := (ET (T : Subgroup G) z).mul_mem hvE hzE
  have hS : ({1, z, v, v * z, w} : Finset G).card = 5 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_insert_of_notMem, Finset.card_singleton]
    all_goals simp [hz1.symm, hv1.symm, hvz1.symm, hw1.symm, hvz.symm, hzvz, hwz.symm, hvvz,
      hvw, hvzw]
  have hsub : (({1, z, v, v * z, w} : Finset G) : Set G) ⊆ (ET (T : Subgroup G) z : Set G) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    exacts [one_mem _, hzE, hvE, hvzE, hwE]
  have h5 := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_coe_finset, hS] at h5
  have h4 : (ET (T : Subgroup G) z : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  omega

theorem exists_conj_mul_z (c : BL.Ctx z 2 Z A T) {v : G} (hvF : v ∈ Fz z) (hv1 : v ≠ 1)
    (hvz : v ≠ z) (hv2 : v * v = 1) : ∃ a ∈ Fz z, a⁻¹ * v * a = v * z := by
  by_contra hno
  push Not at hno
  have hZ : v ∈ Z := by
    refine Width.mem_Z_of_comm c.hD c.hz hvF fun b hb => ?_
    by_contra hbv
    have hbF : b ∈ Fz z := c.hD.sup_eq ▸ Subgroup.mem_sup_right hb
    rcases Width.comm_F c.hD c.hz hbF hvF with h | h
    · exact hbv (commutatorElement_eq_one_iff_mul_comm.mp h).symm
    · have h' : b * v * b⁻¹ = z * v := by
        rw [commutatorElement_def] at h
        calc b * v * b⁻¹ = (b * v * b⁻¹ * v⁻¹) * v := by group
          _ = z * v := by rw [h]
      apply hno b⁻¹ ((Fz z).inv_mem hbF)
      rw [inv_inv, h']
      exact Width.Z_comm_F c.hD c.hD.mem_z hvF
  exact hvz (Width.involution_eq c.hD c.hz hZ (by rw [pow_two]; exact hv2) hv1)

namespace Setup

variable (s : Setup z Z A T k)
include s

theorem exists_a (hcard : Nat.card (ET (T : Subgroup G) z) = 4) {g₀ : G}
    (h₀ : g₀⁻¹ * k * g₀ ∈ (T : Subgroup G)) (h₀' : g₀⁻¹ * k * g₀ ∉ zpowers k) :
    ∃ a ∈ Fz z, (g₀ * a)⁻¹ * z * (g₀ * a) ≠ g₀⁻¹ * z * g₀ ∧
      ∀ g : G, g⁻¹ * k * g ∈ (T : Subgroup G) → g⁻¹ * k * g ∉ zpowers k →
        g⁻¹ * z * g = g₀⁻¹ * z * g₀ ∨ g⁻¹ * z * g = (g₀ * a)⁻¹ * z * (g₀ * a) := by
  have hv := s.invol_mem h₀
  have hvz := s.invol_ne h₀'
  have hvF : g₀⁻¹ * z * g₀ ∈ Fz z := s.ctx.VS_subset_F s.ti hv
  obtain ⟨a, haF, ha⟩ := exists_conj_mul_z s.ctx hvF (BL.ne_one_of_isConj s.ctx.hz hv.1) hvz
    (BL.mul_self_of_isConj s.ctx.hz hv.1)
  have e : (g₀ * a)⁻¹ * z * (g₀ * a) = g₀⁻¹ * z * g₀ * z := by
    rw [← ha]
    group
  have hz1 : z ≠ 1 := BL.ne_one_of_isConj s.ctx.hz (IsConj.refl z)
  refine ⟨a, haF, ?_, fun g hg hg' => ?_⟩
  · rw [e]
    intro h
    exact hz1 (mul_left_cancel (a := g₀⁻¹ * z * g₀) (by rw [mul_one]; exact h))
  · rcases eq_or_eq_mul s.ctx s.ti hcard hv hvz (s.invol_mem hg) (s.invol_ne hg') with h | h
    · exact Or.inl h
    · exact Or.inr (by rw [e]; exact h)

end Setup

@[expose] def KillsS (T : Subgroup G) (z k : G) {B : Type*} [CommGroup B] (ψ : ↥T →* B) : Prop :=
  ∀ (u : G) (hu : u ∈ T), IsConj z u → u * k = k * u → ψ ⟨u, hu⟩ = 1

namespace Setup

variable (s : Setup z Z A T k)
include s

theorem adm_of_mem {X : Subgroup G} {g : G} (hXg : X = zpowers (g⁻¹ * k * g))
    (hXT : X ≤ (T : Subgroup G)) (hXk : X ≠ zpowers k) :
    g⁻¹ * k * g ∈ (T : Subgroup G) ∧ g⁻¹ * k * g ∉ zpowers k := by
  refine ⟨hXT (hXg ▸ mem_zpowers _), fun hmem => hXk ?_⟩
  rw [hXg]
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hmem) ?_
  rw [Nat.card_zpowers, Nat.card_zpowers, s.ord, s.ord_conj g]

variable {B : Type*} [CommGroup B]

theorem psi_sq {ψ : ↥(T : Subgroup G) →* B} (hψ : KillsS (T : Subgroup G) z k ψ) {g : G}
    (h : g⁻¹ * k * g ∈ (T : Subgroup G)) :
    ψ ⟨g⁻¹ * k * g, h⟩ ^ 2 = 1 := by
  have hv := s.invol_mem h
  have hvF : g⁻¹ * z * g ∈ Fz z := s.ctx.VS_subset_F s.ti hv
  have hT : g⁻¹ * z * g ∈ (T : Subgroup G) := s.conj_sq g ▸ (T : Subgroup G).pow_mem h 2
  have e : (⟨g⁻¹ * k * g, h⟩ : (T : Subgroup G)) ^ 2 = ⟨g⁻¹ * z * g, hT⟩ :=
    Subtype.ext (s.conj_sq g)
  rw [← map_pow, e]
  exact hψ _ hT hv.1 (commute_k_of_mem_F s.ctx s.Zk hvF)

theorem psi_eq (hcard : Nat.card (ET (T : Subgroup G) z) = 4) {ψ : ↥(T : Subgroup G) →* B}
    (hψ : KillsS (T : Subgroup G) z k ψ) {g₀ : G} (h₀ : g₀⁻¹ * k * g₀ ∈ (T : Subgroup G))
    (h₀' : g₀⁻¹ * k * g₀ ∉ zpowers k) {g : G} (h : g⁻¹ * k * g ∈ (T : Subgroup G))
    (h' : g⁻¹ * k * g ∉ zpowers k) : ψ ⟨g⁻¹ * k * g, h⟩ = ψ ⟨g₀⁻¹ * k * g₀, h₀⟩ := by
  obtain ⟨a, haF, -, ha⟩ := s.exists_a hcard h₀ h₀'
  have haT : a ∈ (T : Subgroup G) := s.ctx.F_le_T haF
  have hsq := s.psi_sq hψ h₀
  have hinv : (ψ ⟨g₀⁻¹ * k * g₀, h₀⟩)⁻¹ = ψ ⟨g₀⁻¹ * k * g₀, h₀⟩ :=
    inv_eq_of_mul_eq_one_right (by rwa [← pow_two])
  have hmem : a⁻¹ * (g₀⁻¹ * k * g₀) * a ∈ (T : Subgroup G) :=
    (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem haT) h₀) haT
  have hconj : ψ ⟨a⁻¹ * (g₀⁻¹ * k * g₀) * a, hmem⟩ = ψ ⟨g₀⁻¹ * k * g₀, h₀⟩ := by
    have e : (⟨a⁻¹ * (g₀⁻¹ * k * g₀) * a, hmem⟩ : (T : Subgroup G)) =
        ⟨a, haT⟩⁻¹ * ⟨g₀⁻¹ * k * g₀, h₀⟩ * ⟨a, haT⟩ := rfl
    rw [e, map_mul, map_mul, map_inv, mul_comm (ψ ⟨a, haT⟩)⁻¹, mul_assoc, inv_mul_cancel, mul_one]
  have e2 : (g₀ * a)⁻¹ * k * (g₀ * a) = a⁻¹ * (g₀⁻¹ * k * g₀) * a := by group
  rcases ha g h h' with h1 | h1
  · rcases s.gen_eq_or_inv h1 with h2 | h2
    · exact congrArg ψ (Subtype.ext h2)
    · have e : (⟨g⁻¹ * k * g, h⟩ : (T : Subgroup G)) = (⟨g₀⁻¹ * k * g₀, h₀⟩)⁻¹ := Subtype.ext h2
      rw [e, map_inv, hinv]
  · rcases s.gen_eq_or_inv h1 with h2 | h2
    · rw [← hconj]
      exact congrArg ψ (Subtype.ext (h2.trans e2))
    · have e : (⟨g⁻¹ * k * g, h⟩ : (T : Subgroup G)) =
          (⟨a⁻¹ * (g₀⁻¹ * k * g₀) * a, hmem⟩)⁻¹ :=
        Subtype.ext (show g⁻¹ * k * g = (a⁻¹ * (g₀⁻¹ * k * g₀) * a)⁻¹ by rw [h2, e2])
      rw [e, map_inv, hconj, hinv]

theorem card_X_eq_two (hcard : Nat.card (ET (T : Subgroup G) z) = 4) {g₀ : G}
    (h₀ : g₀⁻¹ * k * g₀ ∈ (T : Subgroup G)) (h₀' : g₀⁻¹ * k * g₀ ∉ zpowers k) :
    Nat.card {X : Subgroup G // (∃ g : G, X = zpowers (g⁻¹ * k * g)) ∧ X ≤ (T : Subgroup G) ∧
      X ≠ zpowers k} = 2 := by
  obtain ⟨a, haF, hne, ha⟩ := s.exists_a hcard h₀ h₀'
  have haT : a ∈ (T : Subgroup G) := s.ctx.F_le_T haF
  have e2 : (g₀ * a)⁻¹ * k * (g₀ * a) = a⁻¹ * (g₀⁻¹ * k * g₀) * a := by group
  have hmem : (g₀ * a)⁻¹ * k * (g₀ * a) ∈ (T : Subgroup G) := by
    rw [e2]
    exact (T : Subgroup G).mul_mem ((T : Subgroup G).mul_mem ((T : Subgroup G).inv_mem haT) h₀) haT
  have hnot : (g₀ * a)⁻¹ * k * (g₀ * a) ∉ zpowers k := by
    intro hZ
    have hZ' : (g₀ * a)⁻¹ * k * (g₀ * a) ∈ Z := s.Zk ▸ hZ
    have hc := Width.Z_comm_F s.ctx.hD hZ' haF
    apply h₀'
    have : g₀⁻¹ * k * g₀ = (g₀ * a)⁻¹ * k * (g₀ * a) := by
      rw [e2]
      calc g₀⁻¹ * k * g₀ = a * (a⁻¹ * (g₀⁻¹ * k * g₀) * a) * a⁻¹ := by group
        _ = a * ((g₀ * a)⁻¹ * k * (g₀ * a)) * a⁻¹ := by rw [← e2]
        _ = ((g₀ * a)⁻¹ * k * (g₀ * a)) * a * a⁻¹ := by rw [← hc]
        _ = a⁻¹ * (g₀⁻¹ * k * g₀) * a := by rw [e2]; group
    rw [this]
    exact hZ
  have hX₁ : (∃ g : G, zpowers (g₀⁻¹ * k * g₀) = zpowers (g⁻¹ * k * g)) ∧
      zpowers (g₀⁻¹ * k * g₀) ≤ (T : Subgroup G) ∧ zpowers (g₀⁻¹ * k * g₀) ≠ zpowers k :=
    ⟨⟨g₀, rfl⟩, zpowers_le.mpr h₀, fun h => h₀' (h ▸ mem_zpowers _)⟩
  have hX₂ : (∃ g : G, zpowers ((g₀ * a)⁻¹ * k * (g₀ * a)) = zpowers (g⁻¹ * k * g)) ∧
      zpowers ((g₀ * a)⁻¹ * k * (g₀ * a)) ≤ (T : Subgroup G) ∧
      zpowers ((g₀ * a)⁻¹ * k * (g₀ * a)) ≠ zpowers k :=
    ⟨⟨g₀ * a, rfl⟩, zpowers_le.mpr hmem, fun h => hnot (h ▸ mem_zpowers _)⟩
  rw [Nat.card_eq_two_iff]
  refine ⟨⟨_, hX₁⟩, ⟨_, hX₂⟩, ?_, ?_⟩
  · intro hEq
    have hZ : zpowers (g₀⁻¹ * k * g₀) = zpowers ((g₀ * a)⁻¹ * k * (g₀ * a)) :=
      congrArg Subtype.val hEq
    have hmem2 : (g₀ * a)⁻¹ * k * (g₀ * a) ∈ zpowers (g₀⁻¹ * k * g₀) := hZ ▸ mem_zpowers _
    have hsq := s.conj_sq (g₀ * a)
    have hsq0 := s.conj_sq g₀
    have hzz := BL.mul_self_of_isConj s.ctx.hz (s.invol_mem h₀).1
    apply hne
    rcases eq_or_eq_inv_of_mem_zpowers (s.ord_conj g₀) (s.ord_conj (g₀ * a)) hmem2 with h | h
    · rw [← hsq, ← hsq0, h]
    · rw [← hsq, ← hsq0, h, inv_pow]
      exact inv_eq_of_mul_eq_one_right (by rw [hsq0]; exact hzz)
  · refine Set.eq_univ_iff_forall.mpr fun ⟨X, hX⟩ => ?_
    obtain ⟨⟨g, hXg⟩, hXT, hXk⟩ := hX
    obtain ⟨hg, hg'⟩ := s.adm_of_mem hXg hXT hXk
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases ha g hg hg' with h1 | h1
    · left
      refine Subtype.ext ?_
      show X = zpowers (g₀⁻¹ * k * g₀)
      rcases s.gen_eq_or_inv h1 with h2 | h2
      · rw [hXg, h2]
      · rw [hXg, h2, Subgroup.zpowers_inv]
    · right
      refine Subtype.ext ?_
      show X = zpowers ((g₀ * a)⁻¹ * k * (g₀ * a))
      rcases s.gen_eq_or_inv h1 with h2 | h2
      · rw [hXg, h2]
      · rw [hXg, h2, Subgroup.zpowers_inv]

theorem exists_c (hcard : Nat.card (ET (T : Subgroup G) z) = 4) {ψ : ↥(T : Subgroup G) →* B}
    (hψ : KillsS (T : Subgroup G) z k ψ) :
    ∃ cc : B, cc ^ 2 = 1 ∧
      (∀ (g : G) (h : g⁻¹ * k * g ∈ (T : Subgroup G)), g⁻¹ * k * g ∉ zpowers k →
        ψ ⟨g⁻¹ * k * g, h⟩ = cc) ∧
      Even (Nat.card {X : Subgroup G // (∃ g : G, X = zpowers (g⁻¹ * k * g)) ∧
        X ≤ (T : Subgroup G) ∧ X ≠ zpowers k}) := by
  by_cases hex : ∃ g₀ : G, g₀⁻¹ * k * g₀ ∈ (T : Subgroup G) ∧ g₀⁻¹ * k * g₀ ∉ zpowers k
  · obtain ⟨g₀, h₀, h₀'⟩ := hex
    refine ⟨ψ ⟨g₀⁻¹ * k * g₀, h₀⟩, s.psi_sq hψ h₀, fun g h h' => s.psi_eq hcard hψ h₀ h₀' h h', ?_⟩
    rw [s.card_X_eq_two hcard h₀ h₀']
    exact even_two
  · push Not at hex
    refine ⟨1, one_pow 2, fun g h h' => absurd (hex g h) h', ?_⟩
    haveI : IsEmpty {X : Subgroup G // (∃ g : G, X = zpowers (g⁻¹ * k * g)) ∧
        X ≤ (T : Subgroup G) ∧ X ≠ zpowers k} :=
      ⟨fun ⟨X, ⟨g, hXg⟩, hXT, hXk⟩ => by
        obtain ⟨hg, hg'⟩ := s.adm_of_mem hXg hXT hXk
        exact hg' (hex g hg)⟩
    rw [Nat.card_of_isEmpty]
    exact Even.zero

end Setup

end CFSG.GF2Type.Aschbacher1976Full.HS.Bad
