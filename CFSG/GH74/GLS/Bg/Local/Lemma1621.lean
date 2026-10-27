module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.GH74.GLS.Bg

open Subgroup

namespace L1621

theorem cyclic_invol_unique {C : Type*} [Group C] [Finite C] [IsCyclic C] {a b : C}
    (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  have := Fintype.ofFinite C
  have h := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) (by norm_num)
  by_contra hab
  have hsub : ({1, a, b} : Finset C) ⊆ Finset.univ.filter (fun x => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> simp [ha, hb]
  have hcard : ({1, a, b} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simpa using hab
    · simp [ha1.symm, hb1.symm]
  have := Finset.card_le_card hsub
  omega

variable {X : Type*} [Group X]

structure Hyp (P U : Subgroup X) (z u : X) : Prop where
  UP : U ≤ P
  Unorm : ∀ g ∈ P, ∀ v ∈ U, g * v * g⁻¹ ∈ U
  Ucard : Nat.card U = 4
  Uexp : ∀ a ∈ U, a * a = 1
  zP : z ∈ P
  zsq : z * z = 1
  zne : z ≠ 1
  zcent : ∀ g ∈ P, g * z = z * g
  cinv : ∀ v ∈ P, (∀ g ∈ P, g * v = v * g) → v * v = 1 → v ≠ 1 → v = z
  zU : z ∈ U
  uU : u ∈ U
  une1 : u ≠ 1
  unez : u ≠ z

section
variable {P U : Subgroup X} {z u : X} (h : Hyp P U z u)
include h

theorem Hyp.central_invol_eq {v : X} (hv : v ∈ P) (hvc : ∀ g ∈ P, g * v = v * g)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) : v = z := h.cinv v hv hvc hv2 hv1

theorem Hyp.U_comm {a b : X} (ha : a ∈ U) (hb : b ∈ U) : a * b = b * a := by
  have h1 := h.Uexp a ha
  have h2 := h.Uexp b hb
  have h3 := h.Uexp (a * b) (mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right h1
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right h2
  have hab' : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right h3
  rw [mul_inv_rev, ha', hb'] at hab'
  exact hab'.symm

end

theorem Hyp.of_cyclic [Finite X] {P U : Subgroup X} {z u : X} (hP : IsPGroup 2 ↥P)
    (hcyc : IsCyclic ↥(center ↥P)) (hUP : U ≤ P) (hUn : ∀ g ∈ P, ∀ v ∈ U, g * v * g⁻¹ ∈ U)
    (hU : Nat.card U = 4) (hexp : ∀ a ∈ U, a * a = 1) (hzP : z ∈ P) (hzsq : z * z = 1)
    (hz1 : z ≠ 1) (hzc : ∀ g ∈ P, g * z = z * g) (hu : u ∈ U) (hu1 : u ≠ 1) (huz : u ≠ z) :
    Hyp P U z u := by
  have cinv : ∀ v ∈ P, (∀ g ∈ P, g * v = v * g) → v * v = 1 → v ≠ 1 → v = z := by
    intro v hv hvc hv2 hv1
    have hvZ : (⟨v, hv⟩ : ↥P) ∈ center ↥P := mem_center_iff.mpr fun g => Subtype.ext (hvc g g.2)
    have hzZ : (⟨z, hzP⟩ : ↥P) ∈ center ↥P :=
      mem_center_iff.mpr fun g => Subtype.ext (hzc g g.2)
    have key := cyclic_invol_unique (C := ↥(center ↥P))
      (a := ⟨⟨v, hv⟩, hvZ⟩) (b := ⟨⟨z, hzP⟩, hzZ⟩)
      (by ext; simpa [pow_two] using hv2) (by ext; simpa [pow_two] using hzsq)
      (by intro e; apply hv1; simpa using congrArg (fun w : ↥(center ↥P) => (w : ↥P).1) e)
      (by intro e; apply hz1; simpa using congrArg (fun w : ↥(center ↥P) => (w : ↥P).1) e)
    simpa using congrArg (fun w : ↥(center ↥P) => (w : ↥P).1) key
  have hnil : Group.IsNilpotent ↥P := hP.isNilpotent
  have hN : (U.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    exact hUn g g.2 n hn
  have hne : U.subgroupOf P ≠ ⊥ := by
    intro hbot
    have : (⟨u, hUP hu⟩ : ↥P) ∈ U.subgroupOf P := hu
    rw [hbot, mem_bot] at this
    exact hu1 (congrArg Subtype.val this)
  have hc := hnil.inf_center_ne_bot_of_normal hne
  obtain ⟨w, hw1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hc
  have hwU : ((w : ↥P) : X) ∈ U := w.2.1
  have hwcen : (w : ↥P) ∈ center ↥P := w.2.2
  have hwc : ∀ g ∈ P, g * ((w : ↥P) : X) = ((w : ↥P) : X) * g := by
    intro g hg
    exact congrArg Subtype.val ((mem_center_iff.mp hwcen) ⟨g, hg⟩)
  have hw2 : ((w : ↥P) : X) * ((w : ↥P) : X) = 1 := hexp _ hwU
  have hw1' : ((w : ↥P) : X) ≠ 1 := fun e => hw1 (Subtype.ext (Subtype.ext e))
  have hwz := cinv _ (w : ↥P).2 hwc hw2 hw1'
  exact ⟨hUP, hUn, hU, hexp, hzP, hzsq, hz1, hzc, cinv, hwz ▸ hwU, hu, hu1, huz⟩



abbrev Qs (P U : Subgroup X) : Subgroup X := P ⊓ centralizer (U : Set X)

section
variable {P U : Subgroup X} {z u : X} (h : Hyp P U z u)
include h

theorem U_elems {v : X} (hv : v ∈ U) : v = 1 ∨ v = z ∨ v = u ∨ v = z * u := by
  classical
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨h1, h2, h3, h4⟩ := hcon
  have hz := h.zU
  have hz1 := h.zne
  have hu1 := h.une1
  have huz := h.unez
  have hzu1 : z * u ≠ 1 := by
    intro e
    apply huz
    have : u = z⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [this]
    exact inv_eq_of_mul_eq_one_right h.zsq
  have hzuz : z ≠ z * u := by
    intro e
    apply hu1
    exact (mul_eq_left.mp e.symm)
  have huzu : u ≠ z * u := by
    intro e
    apply hz1
    exact (mul_eq_right.mp e.symm)
  have hsub : (({1, z, u, z * u, v} : Finset X) : Set X) ⊆ (U : Set X) := by
    intro x hx
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact one_mem U
    · exact hz
    · exact h.uU
    · exact mul_mem hz h.uU
    · exact hv
  have hcard : ({1, z, u, z * u, v} : Finset X).card = 5 := by
    have e5 : z * u ∉ ({v} : Finset X) := by simpa using Ne.symm h4
    have e4 : u ∉ ({z * u, v} : Finset X) := by simp [huzu, Ne.symm h3]
    have e3 : z ∉ ({u, z * u, v} : Finset X) := by simp [huz.symm, hzuz, Ne.symm h2]
    have e2 : (1 : X) ∉ ({z, u, z * u, v} : Finset X) := by
      simp [hz1.symm, hu1.symm, hzu1.symm, Ne.symm h1]
    rw [Finset.card_insert_of_notMem e2, Finset.card_insert_of_notMem e3,
      Finset.card_insert_of_notMem e4, Finset.card_insert_of_notMem e5, Finset.card_singleton]
  have h4' : (U : Set X).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact h.Ucard
  have hfin : (U : Set X).Finite := Set.finite_of_ncard_ne_zero (by omega)
  have := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_coe_finset, hcard] at this
  omega

theorem conj_u {g : X} (hg : g ∈ P) : g * u * g⁻¹ = u ∨ g * u * g⁻¹ = z * u := by
  have hmem : g * u * g⁻¹ ∈ U := h.Unorm g hg u h.uU
  rcases U_elems h hmem with e | e | e | e
  · exfalso
    apply h.une1
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  · exfalso
    apply h.unez
    have hzc := h.zcent g hg
    calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
      _ = g⁻¹ * z * g := by rw [e]
      _ = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hzc]
      _ = z := by group
  · exact Or.inl e
  · exact Or.inr e

theorem exists_a : ∃ a ∈ P, a * u * a⁻¹ = z * u := by
  by_contra hcon
  simp only [not_exists, not_and] at hcon
  have hall : ∀ g ∈ P, g * u = u * g := by
    intro g hg
    rcases conj_u h hg with e | e
    · calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [e]
    · exact absurd e (hcon g hg)
  exact h.unez (h.central_invol_eq (h.UP h.uU) hall (h.Uexp u h.uU) h.une1)

theorem mem_Qs {g : X} : g ∈ Qs P U ↔ g ∈ P ∧ g * u * g⁻¹ = u := by
  constructor
  · rintro ⟨hgP, hgc⟩
    refine ⟨hgP, ?_⟩
    have := mem_centralizer_iff.mp hgc u h.uU
    calc g * u * g⁻¹ = u * g * g⁻¹ := by rw [← this]
      _ = u := by group
  · rintro ⟨hgP, hgu⟩
    refine ⟨hgP, mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hgu' : g * u = u * g := by
      calc g * u = g * u * g⁻¹ * g := by group
        _ = u * g := by rw [hgu]
    rcases U_elems h hv with e | e | e | e
    · subst e; simp
    · subst e; exact (h.zcent g hgP).symm
    · subst e; exact hgu'.symm
    · subst e
      calc z * u * g = z * (u * g) := by group
        _ = z * (g * u) := by rw [hgu']
        _ = (z * g) * u := by group
        _ = (g * z) * u := by rw [h.zcent g hgP]
        _ = g * (z * u) := by group

end


section
variable {P U : Subgroup X} {z u : X} (h : Hyp P U z u)
include h

theorem u_mem_Qs : u ∈ Qs P U :=
  (mem_Qs h).mpr ⟨h.UP h.uU, by group⟩

theorem z_mem_Qs : z ∈ Qs P U := by
  refine (mem_Qs h).mpr ⟨h.zP, ?_⟩
  have hc := h.U_comm h.zU h.uU
  calc z * u * z⁻¹ = u * z * z⁻¹ := by rw [hc]
    _ = u := by group

theorem P_normalizes_Qs {g q : X} (hg : g ∈ P) (hq : q ∈ Qs P U) : g * q * g⁻¹ ∈ Qs P U := by
  rw [mem_Qs h] at hq ⊢
  obtain ⟨hqP, hqu⟩ := hq
  refine ⟨mul_mem (mul_mem hg hqP) (inv_mem hg), ?_⟩
  have hw : g⁻¹ * u * g = u ∨ g⁻¹ * u * g = z * u := by
    have := conj_u h (inv_mem hg)
    simpa using this
  have hqu' : q * u = u * q := by
    calc q * u = q * u * q⁻¹ * q := by group
      _ = u * q := by rw [hqu]
  have hqz : q * z = z * q := h.zcent q hqP
  have hqw : q * (g⁻¹ * u * g) = (g⁻¹ * u * g) * q := by
    rcases hw with e | e
    · rw [e]; exact hqu'
    · rw [e]
      calc q * (z * u) = (q * z) * u := by group
        _ = (z * q) * u := by rw [hqz]
        _ = z * (q * u) := by group
        _ = z * (u * q) := by rw [hqu']
        _ = z * u * q := by group
  calc g * q * g⁻¹ * u * (g * q * g⁻¹)⁻¹ = g * (q * (g⁻¹ * u * g) * q⁻¹) * g⁻¹ := by group
    _ = g * (g⁻¹ * u * g) * g⁻¹ := by
        congr 2
        calc q * (g⁻¹ * u * g) * q⁻¹ = (g⁻¹ * u * g) * q * q⁻¹ := by rw [hqw]
          _ = g⁻¹ * u * g := by group
    _ = u := by group

theorem P_cover {a : X} (ha : a ∈ P) (hau : a * u * a⁻¹ = z * u) {g : X} (hg : g ∈ P) :
    g ∈ Qs P U ∨ ∃ q ∈ Qs P U, g = a * q := by
  rcases conj_u h hg with e | e
  · exact Or.inl ((mem_Qs h).mpr ⟨hg, e⟩)
  · right
    refine ⟨a⁻¹ * g, ?_, by group⟩
    rw [mem_Qs h]
    refine ⟨mul_mem (inv_mem ha) hg, ?_⟩
    have hazu : a⁻¹ * (z * u) * a = u := by
      calc a⁻¹ * (z * u) * a = a⁻¹ * (a * u * a⁻¹) * a := by rw [hau]
        _ = u := by group
    calc a⁻¹ * g * u * (a⁻¹ * g)⁻¹ = a⁻¹ * (g * u * g⁻¹) * a := by group
      _ = a⁻¹ * (z * u) * a := by rw [e]
      _ = u := hazu

theorem a_sq_mem {a : X} (ha : a ∈ P) (hau : a * u * a⁻¹ = z * u) : a * a ∈ Qs P U := by
  rw [mem_Qs h]
  refine ⟨mul_mem ha ha, ?_⟩
  have hz := h.zcent a ha
  calc a * a * u * (a * a)⁻¹ = a * (a * u * a⁻¹) * a⁻¹ := by group
    _ = a * (z * u) * a⁻¹ := by rw [hau]
    _ = (a * z * a⁻¹) * (a * u * a⁻¹) := by group
    _ = z * (z * u) := by
        rw [hau]
        congr 1
        calc a * z * a⁻¹ = z * a * a⁻¹ := by rw [hz]
          _ = z := by group
    _ = u := by
        calc z * (z * u) = (z * z) * u := by group
          _ = u := by rw [h.zsq]; group

theorem U_iff {v : X} :
    v ∈ U ↔ (v ∈ Qs P U ∧ (∀ q ∈ Qs P U, q * v = v * q) ∧ v * v = 1) := by
  constructor
  · intro hv
    refine ⟨?_, ?_, h.Uexp v hv⟩
    · rw [mem_Qs h]
      refine ⟨h.UP hv, ?_⟩
      have := h.U_comm hv h.uU
      calc v * u * v⁻¹ = u * v * v⁻¹ := by rw [this]
        _ = u := by group
    · intro q hq
      exact (mem_centralizer_iff.mp hq.2 v hv).symm
  · rintro ⟨hvQ, hvc, hv2⟩
    obtain ⟨a, haP, hau⟩ := exists_a h
    have hvP : v ∈ P := hvQ.1
    have hv'Q : a * v * a⁻¹ ∈ Qs P U := P_normalizes_Qs h haP hvQ
    have hainvQ : ∀ q ∈ Qs P U, a⁻¹ * q * a ∈ Qs P U := fun q hq => by
      have := P_normalizes_Qs h (inv_mem haP) hq
      simpa using this
    obtain ⟨v', hv'def⟩ : ∃ v', v' = a * v * a⁻¹ := ⟨_, rfl⟩
    rw [← hv'def] at hv'Q
    have hv'c : ∀ q ∈ Qs P U, q * v' = v' * q := by
      intro q hq
      have h1 := hvc (a⁻¹ * q * a) (hainvQ q hq)
      calc q * v' = a * ((a⁻¹ * q * a) * v) * a⁻¹ := by rw [hv'def]; group
        _ = a * (v * (a⁻¹ * q * a)) * a⁻¹ := by rw [h1]
        _ = v' * q := by rw [hv'def]; group
    have hv'2 : v' * v' = 1 := by
      calc v' * v' = a * (v * v) * a⁻¹ := by rw [hv'def]; group
        _ = 1 := by rw [hv2]; group
    have hvv' : v * v' = v' * v := (hvc v' hv'Q).symm
    obtain ⟨c, hcdef⟩ : ∃ c, c = v' * v := ⟨_, rfl⟩
    have ha2Q := a_sq_mem h haP hau
    have hca : a * c * a⁻¹ = c := by
      have h2 : (a * a) * v = v * (a * a) := hvc _ ha2Q
      calc a * c * a⁻¹ = (a * v' * a⁻¹) * (a * v * a⁻¹) := by rw [hcdef]; group
        _ = ((a * a) * v * (a * a)⁻¹) * v' := by rw [hv'def]; group
        _ = v * v' := by rw [h2]; group
        _ = c := by rw [hvv', hcdef]
    have hc2 : c * c = 1 := by
      calc c * c = (v' * v) * (v' * v) := by rw [hcdef]
        _ = v' * (v * v') * v := by group
        _ = v' * (v' * v) * v := by rw [hvv']
        _ = (v' * v') * (v * v) := by group
        _ = 1 := by rw [hv'2, hv2]; group
    have hcQ : ∀ q ∈ Qs P U, q * c = c * q := by
      intro q hq
      calc q * c = q * v' * v := by rw [hcdef]; group
        _ = v' * q * v := by rw [hv'c q hq]
        _ = v' * (q * v) := by group
        _ = v' * (v * q) := by rw [hvc q hq]
        _ = c * q := by rw [hcdef]; group
    have hac : a * c = c * a := by
      calc a * c = a * c * a⁻¹ * a := by group
        _ = c * a := by rw [hca]
    have hcP : ∀ g ∈ P, g * c = c * g := by
      intro g hg
      rcases P_cover h haP hau hg with hgQ | ⟨q, hq, rfl⟩
      · exact hcQ g hgQ
      · calc a * q * c = a * (q * c) := by group
          _ = a * (c * q) := by rw [hcQ q hq]
          _ = (a * c) * q := by group
          _ = (c * a) * q := by rw [hac]
          _ = c * (a * q) := by group
    have hcmemP : c ∈ P := by rw [hcdef]; exact mul_mem hv'Q.1 hvP
    by_cases hc1 : c = 1
    · have hvv : v' = v := by
        have e1 : v' * v = 1 := by rw [← hcdef]; exact hc1
        calc v' = v' * v * v⁻¹ := by group
          _ = v⁻¹ := by rw [e1]; group
          _ = v := inv_eq_of_mul_eq_one_right hv2
      have hav : a * v = v * a := by
        calc a * v = a * v * a⁻¹ * a := by group
          _ = v' * a := by rw [← hv'def]
          _ = v * a := by rw [hvv]
      have hvcP : ∀ g ∈ P, g * v = v * g := by
        intro g hg
        rcases P_cover h haP hau hg with hgQ | ⟨q, hq, rfl⟩
        · exact hvc g hgQ
        · calc a * q * v = a * (q * v) := by group
            _ = a * (v * q) := by rw [hvc q hq]
            _ = (a * v) * q := by group
            _ = (v * a) * q := by rw [hav]
            _ = v * (a * q) := by group
      by_cases hv1 : v = 1
      · rw [hv1]; exact one_mem U
      · have := h.central_invol_eq hvP hvcP hv2 hv1
        rw [this]; exact h.zU
    · have hcz : c = z := h.central_invol_eq hcmemP hcP hc2 hc1
      have hv'z : v' = z * v := by
        have e1 : v' * v = z := by rw [← hcdef]; exact hcz
        calc v' = v' * v * v⁻¹ := by group
          _ = z * v⁻¹ := by rw [e1]
          _ = z * v := by rw [inv_eq_of_mul_eq_one_right hv2]
      have huQ := u_mem_Qs h
      have hzQ := z_mem_Qs h
      have hvz : z * v = v * z := hvc z hzQ
      have hvu : u * v = v * u := hvc u huQ
      obtain ⟨w, hwdef⟩ : ∃ w, w = v * u := ⟨_, rfl⟩
      have hwP : w ∈ P := by rw [hwdef]; exact mul_mem hvP (h.UP h.uU)
      have hwQ : ∀ q ∈ Qs P U, q * w = w * q := by
        intro q hq
        have hqu : q * u = u * q := by
          have := ((mem_Qs h).mp hq).2
          calc q * u = q * u * q⁻¹ * q := by group
            _ = u * q := by rw [this]
        calc q * w = (q * v) * u := by rw [hwdef]; group
          _ = (v * q) * u := by rw [hvc q hq]
          _ = v * (q * u) := by group
          _ = v * (u * q) := by rw [hqu]
          _ = w * q := by rw [hwdef]; group
      have haw : a * w * a⁻¹ = w := by
        calc a * w * a⁻¹ = (a * v * a⁻¹) * (a * u * a⁻¹) := by rw [hwdef]; group
          _ = (z * v) * (z * u) := by rw [← hv'def, hv'z, hau]
          _ = z * (v * z) * u := by group
          _ = z * (z * v) * u := by rw [hvz]
          _ = (z * z) * (v * u) := by group
          _ = w := by rw [h.zsq, hwdef]; group
      have hwa : a * w = w * a := by
        calc a * w = a * w * a⁻¹ * a := by group
          _ = w * a := by rw [haw]
      have hwcP : ∀ g ∈ P, g * w = w * g := by
        intro g hg
        rcases P_cover h haP hau hg with hgQ | ⟨q, hq, rfl⟩
        · exact hwQ g hgQ
        · calc a * q * w = a * (q * w) := by group
            _ = a * (w * q) := by rw [hwQ q hq]
            _ = (a * w) * q := by group
            _ = (w * a) * q := by rw [hwa]
            _ = w * (a * q) := by group
      have hw2 : w * w = 1 := by
        calc w * w = v * (u * v) * u := by rw [hwdef]; group
          _ = v * (v * u) * u := by rw [hvu]
          _ = (v * v) * (u * u) := by group
          _ = 1 := by rw [hv2, h.Uexp u h.uU]; group
      by_cases hw1 : w = 1
      ·
        have e1 : v * u = 1 := by rw [← hwdef]; exact hw1
        have : v = u := by
          calc v = v * u * u⁻¹ := by group
            _ = u⁻¹ := by rw [e1]; group
            _ = u := inv_eq_of_mul_eq_one_right (h.Uexp u h.uU)
        rw [this]; exact h.uU
      · have hwz := h.central_invol_eq hwP hwcP hw2 hw1
        have e1 : v * u = z := by rw [← hwdef]; exact hwz
        have : v = z * u := by
          calc v = v * u * u⁻¹ := by group
            _ = z * u⁻¹ := by rw [e1]
            _ = z * u := by rw [inv_eq_of_mul_eq_one_right (h.Uexp u h.uU)]
        rw [this]; exact mul_mem h.zU h.uU

theorem conj_mem_U {n : X} (hn : n ∈ normalizer ((Qs P U : Subgroup X) : Set X)) {v : X}
    (hv : v ∈ U) : n * v * n⁻¹ ∈ U := by
  rw [mem_normalizer_iff] at hn
  obtain ⟨hvQ, hvc, hv2⟩ := (U_iff h).mp hv
  refine (U_iff h).mpr ⟨(hn v).mp hvQ, ?_, ?_⟩
  · intro q hq
    have hq' : n⁻¹ * q * n ∈ Qs P U := by
      have e1 : n * (n⁻¹ * q * n) * n⁻¹ = q := by group
      exact (hn (n⁻¹ * q * n)).mpr (by rw [e1]; exact hq)
    have e2 := hvc _ hq'
    calc q * (n * v * n⁻¹) = n * ((n⁻¹ * q * n) * v) * n⁻¹ := by group
      _ = n * (v * (n⁻¹ * q * n)) * n⁻¹ := by rw [e2]
      _ = n * v * n⁻¹ * q := by group
  · calc n * v * n⁻¹ * (n * v * n⁻¹) = n * (v * v) * n⁻¹ := by group
      _ = 1 := by rw [hv2]; group

end


theorem mem_smul_sylow (P : Sylow 2 X) (g y : X) :
    y ∈ ((g • P : Sylow 2 X) : Subgroup X) ↔ g⁻¹ * y * g ∈ (P : Subgroup X) := by
  rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def]

theorem card_eq_of_index_odd [Finite X] {P : Subgroup X} (hP : IsPGroup 2 ↥P)
    (hi : ¬ 2 ∣ P.index) : Nat.card P = 2 ^ (Nat.card X).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hm : Nat.card P * P.index = Nat.card X := Subgroup.card_mul_index P
  have hidx : P.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hfac : (Nat.card X).factorization 2 = k := by
    rw [← hm, hk, Nat.factorization_mul (pow_ne_zero _ (by norm_num)) hidx]
    simp [Nat.Prime.factorization_pow Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hi]
  rw [hfac, hk]

section
variable {P U : Subgroup X} {z u : X} (h : Hyp P U z u)
include h

theorem exists_conj_sylow [Finite X] (hpg : IsPGroup 2 ↥P) (hsyl : ¬ 2 ∣ P.index)
    (hconj : IsConj z u) : ∃ e : X, e * z * e⁻¹ = u ∧
    Qs P U ≤ P.map (MulAut.conj e).toMonoidHom := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  have hcardP := card_eq_of_index_odd hpg hsyl
  let SP : Sylow 2 X := Sylow.ofCard P hcardP
  have hSP : (SP : Subgroup X) = P := rfl
  set C : Subgroup X := centralizer ({u} : Set X) with hC
  have hQP : Qs P U ≤ P := inf_le_left
  have hQC : Qs P U ≤ C := by
    intro q hq
    exact (mem_centralizer_iff.mpr fun v hv => by
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact (mem_centralizer_iff.mp hq.2 v h.uU))
  have hP1C : P.map (MulAut.conj c).toMonoidHom ≤ C := by
    rintro y ⟨p, hp, rfl⟩
    refine mem_centralizer_iff.mpr fun v hv => ?_
    rw [Set.mem_singleton_iff] at hv
    subst hv
    have hzc := h.zcent p hp
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hc]
    calc c * z * c⁻¹ * (c * p * c⁻¹) = c * (z * p) * c⁻¹ := by group
      _ = c * (p * z) * c⁻¹ := by rw [hzc]
      _ = c * p * c⁻¹ * (c * z * c⁻¹) := by group
  have hP1card : Nat.card (P.map (MulAut.conj c).toMonoidHom) = Nat.card P :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hfacC : (Nat.card C).factorization 2 = (Nat.card X).factorization 2 := by
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_subgroup_dvd_card C) 2
    · have hdvd : Nat.card P ∣ Nat.card C := by
        rw [← hP1card]
        exact Subgroup.card_dvd_of_le hP1C
      rw [hcardP] at hdvd
      exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd
  have hQp : IsPGroup 2 ↥((Qs P U).subgroupOf C) :=
    IsPGroup.of_equiv (hpg.to_le hQP) (Subgroup.subgroupOfEquivOfLe hQC).symm
  obtain ⟨S2, hS2⟩ := hQp.exists_le_sylow
  obtain ⟨T, hT⟩ := Sylow.exists_comap_subtype_eq S2
  have hTcard : Nat.card (T : Subgroup X) = 2 ^ (Nat.card X).factorization 2 :=
    Sylow.card_eq_multiplicity T
  have hS2card : Nat.card (S2 : Subgroup ↥C) = 2 ^ (Nat.card X).factorization 2 := by
    rw [Sylow.card_eq_multiplicity S2, hfacC]
  have hTC : (T : Subgroup X) ≤ C := by
    have hle : (T : Subgroup X) ⊓ C ≤ (T : Subgroup X) := inf_le_left
    have hmap : (((T : Subgroup X).comap C.subtype)).map C.subtype = C ⊓ (T : Subgroup X) := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype]
    have hcard1 : Nat.card ((T : Subgroup X).comap C.subtype) =
        Nat.card (C ⊓ (T : Subgroup X) : Subgroup X) := by
      rw [← hmap]
      exact (Subgroup.card_map_of_injective C.subtype_injective).symm
    have hcard : Nat.card (T : Subgroup X) ≤ Nat.card ((T : Subgroup X) ⊓ C : Subgroup X) := by
      rw [hTcard, inf_comm, ← hcard1, hT, hS2card]
    have := Subgroup.eq_of_le_of_card_ge hle hcard
    exact inf_eq_left.mp this
  have hQT : Qs P U ≤ (T : Subgroup X) := by
    intro q hq
    have h1 : (⟨q, hQC hq⟩ : C) ∈ (S2 : Subgroup ↥C) :=
      hS2 (by simpa [Subgroup.mem_subgroupOf] using hq)
    rw [← hT] at h1
    exact h1
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X SP T
  have hTmem : ∀ y, y ∈ (T : Subgroup X) ↔ g⁻¹ * y * g ∈ P := by
    intro y
    rw [← hg, mem_smul_sylow]
    rfl
  refine ⟨g, ?_, ?_⟩
  · have huT : u ∈ (T : Subgroup X) := hQT (u_mem_Qs h)
    obtain ⟨v, hv⟩ : ∃ v, v = g⁻¹ * u * g := ⟨_, rfl⟩
    have hvP : v ∈ P := by rw [hv]; exact (hTmem u).mp huT
    have hvc : ∀ p ∈ P, p * v = v * p := by
      intro p hp
      have hpT : g * p * g⁻¹ ∈ (T : Subgroup X) := (hTmem _).mpr (by
        have e0 : g⁻¹ * (g * p * g⁻¹) * g = p := by group
        rw [e0]; exact hp)
      have := mem_centralizer_iff.mp (hTC hpT) u (Set.mem_singleton u)
      calc p * v = g⁻¹ * (g * p * g⁻¹ * u) * g := by rw [hv]; group
        _ = g⁻¹ * (u * (g * p * g⁻¹)) * g := by rw [this]
        _ = v * p := by rw [hv]; group
    have hv2 : v * v = 1 := by
      calc v * v = g⁻¹ * (u * u) * g := by rw [hv]; group
        _ = 1 := by rw [h.Uexp u h.uU]; group
    have hv1 : v ≠ 1 := by
      intro e
      apply h.une1
      calc u = g * v * g⁻¹ := by rw [hv]; group
        _ = 1 := by rw [e]; group
    have hvz : v = z := h.central_invol_eq hvP hvc hv2 hv1
    calc g * z * g⁻¹ = g * v * g⁻¹ := by rw [hvz]
      _ = u := by rw [hv]; group
  · intro q hq
    refine ⟨g⁻¹ * q * g, (hTmem q).mp (hQT hq), ?_⟩
    simp [MulAut.conj_apply]
    group

end


theorem mem_conjSub {P : Subgroup X} {e g : X} :
    g ∈ P.map (MulAut.conj e).toMonoidHom ↔ e⁻¹ * g * e ∈ P := by
  constructor
  · rintro ⟨p, hp, rfl⟩
    have e0 : e⁻¹ * (e * p * e⁻¹) * e = p := by group
    simpa [MulAut.conj_apply, e0] using hp
  · intro hg
    exact ⟨e⁻¹ * g * e, hg, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩

section
variable {P U : Subgroup X} {z u : X} (h : Hyp P U z u)
include h

theorem U_le_Qs : U ≤ Qs P U := fun _ hv =>
  ⟨h.UP hv, mem_centralizer_iff.mpr fun _ hw => h.U_comm hw hv⟩

theorem card_P_eq : Nat.card ↥P = 2 * Nat.card ↥(Qs P U) := by
  obtain ⟨a, haP, hau⟩ := exists_a h
  have hidx : ((Qs P U).subgroupOf P).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haP⟩, fun b => ?_⟩
    have hb : (b : X) ∈ P := b.2
    have hbz : (b : X) * z * (b : X)⁻¹ = z := by rw [h.zcent _ hb]; group
    have hmemb : b ∈ (Qs P U).subgroupOf P ↔ (b : X) * u * (b : X)⁻¹ = u := by
      rw [Subgroup.mem_subgroupOf, mem_Qs h]
      exact ⟨fun hh => hh.2, fun hh => ⟨hb, hh⟩⟩
    have hmemba : b * ⟨a, haP⟩ ∈ (Qs P U).subgroupOf P ↔
        z * ((b : X) * u * (b : X)⁻¹) = u := by
      rw [Subgroup.mem_subgroupOf, mem_Qs h]
      have e1 : (↑(b * (⟨a, haP⟩ : ↥P)) : X) * u * (↑(b * (⟨a, haP⟩ : ↥P)) : X)⁻¹ =
          z * ((b : X) * u * (b : X)⁻¹) := by
        calc (↑(b * (⟨a, haP⟩ : ↥P)) : X) * u * (↑(b * (⟨a, haP⟩ : ↥P)) : X)⁻¹
            = (b : X) * (a * u * a⁻¹) * (b : X)⁻¹ := by simp only [Subgroup.coe_mul]; group
          _ = (b : X) * (z * u) * (b : X)⁻¹ := by rw [hau]
          _ = ((b : X) * z * (b : X)⁻¹) * ((b : X) * u * (b : X)⁻¹) := by group
          _ = z * ((b : X) * u * (b : X)⁻¹) := by rw [hbz]
      rw [e1]
      exact ⟨fun hh => hh.2, fun hh => ⟨mul_mem hb haP, hh⟩⟩
    rcases conj_u h hb with e | e
    · refine Or.inr ⟨hmemb.mpr e, fun hh => ?_⟩
      have := hmemba.mp hh
      rw [e] at this
      exact h.zne (mul_eq_right.mp this)
    · refine Or.inl ⟨hmemba.mpr ?_, fun hh => ?_⟩
      · rw [e]
        calc z * (z * u) = (z * z) * u := by group
          _ = u := by rw [h.zsq]; group
      · have := hmemb.mp hh
        rw [e] at this
        exact h.zne (mul_eq_right.mp this)
  have h1 := Subgroup.card_mul_index ((Qs P U).subgroupOf P)
  have h2 : Nat.card ↥((Qs P U).subgroupOf P) = Nat.card ↥(Qs P U) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2, hidx] at h1
  omega

theorem conj_norm_Q [Finite X] {e : X} (hQR : Qs P U ≤ P.map (MulAut.conj e).toMonoidHom)
    {g q : X} (hg : g ∈ P.map (MulAut.conj e).toMonoidHom) (hq : q ∈ Qs P U) :
    g * q * g⁻¹ ∈ Qs P U := by
  set R := P.map (MulAut.conj e).toMonoidHom with hR
  have hcard : Nat.card ↥R = 2 * Nat.card ↥(Qs P U) := by
    rw [hR, Subgroup.card_map_of_injective (MulAut.conj e).injective]
    exact card_P_eq h
  have hidx : ((Qs P U).subgroupOf R).index = 2 := by
    have h1 := Subgroup.card_mul_index ((Qs P U).subgroupOf R)
    have h2 : Nat.card ↥((Qs P U).subgroupOf R) = Nat.card ↥(Qs P U) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
    rw [h2, hcard] at h1
    have hpos : 0 < Nat.card ↥(Qs P U) := Nat.card_pos
    have h3 : Nat.card ↥(Qs P U) * ((Qs P U).subgroupOf R).index = Nat.card ↥(Qs P U) * 2 := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_left hpos h3
  have : ((Qs P U).subgroupOf R).Normal := Subgroup.normal_of_index_eq_two hidx
  have hq' : (⟨q, hQR hq⟩ : ↥R) ∈ (Qs P U).subgroupOf R := hq
  have := this.conj_mem _ hq' ⟨g, hg⟩
  exact this

theorem R_mem_normalizer [Finite X] {e : X} (hQR : Qs P U ≤ P.map (MulAut.conj e).toMonoidHom)
    {g : X} (hg : g ∈ P.map (MulAut.conj e).toMonoidHom) :
    g ∈ normalizer ((Qs P U : Subgroup X) : Set X) := by
  rw [mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    exact conj_norm_Q h hQR hg hq
  · intro hq
    have hg' : g⁻¹ ∈ P.map (MulAut.conj e).toMonoidHom := inv_mem hg
    have h1 := conj_norm_Q h hQR hg' hq
    have e0 : g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q := by group
    rw [e0] at h1
    exact h1

theorem normQ_le_normU {n : X} (hn : n ∈ normalizer ((Qs P U : Subgroup X) : Set X)) :
    n ∈ normalizer (U : Set X) := by
  rw [mem_normalizer_iff]
  intro v
  constructor
  · intro hv
    exact conj_mem_U h hn hv
  · intro hv
    have hn' : n⁻¹ ∈ normalizer ((Qs P U : Subgroup X) : Set X) := inv_mem hn
    have h1 := conj_mem_U h hn' hv
    have e0 : n⁻¹ * (n * v * n⁻¹) * n⁻¹⁻¹ = v := by group
    rw [e0] at h1
    exact h1

theorem hyp_conj [Finite X] {e : X} (hez : e * z * e⁻¹ = u)
    (hQR : Qs P U ≤ P.map (MulAut.conj e).toMonoidHom) :
    Hyp (P.map (MulAut.conj e).toMonoidHom) U u z where
  UP := fun v hv => hQR (U_le_Qs h hv)
  Unorm := fun g hg _ hv => conj_mem_U h (R_mem_normalizer h hQR hg) hv
  Ucard := h.Ucard
  Uexp := h.Uexp
  zP := mem_conjSub.mpr (by
    have : e⁻¹ * u * e = z := by rw [← hez]; group
    rw [this]; exact h.zP)
  zsq := h.Uexp u h.uU
  zne := h.une1
  zcent := by
    rintro g ⟨p, hp, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hez]
    calc e * p * e⁻¹ * (e * z * e⁻¹) = e * (p * z) * e⁻¹ := by group
      _ = e * (z * p) * e⁻¹ := by rw [h.zcent p hp]
      _ = e * z * e⁻¹ * (e * p * e⁻¹) := by group
  cinv := by
    intro v hv hvc hv2 hv1
    have hvP : e⁻¹ * v * e ∈ P := mem_conjSub.mp hv
    have hc : ∀ g ∈ P, g * (e⁻¹ * v * e) = (e⁻¹ * v * e) * g := by
      intro g hg
      have hgR : e * g * e⁻¹ ∈ P.map (MulAut.conj e).toMonoidHom :=
        mem_conjSub.mpr (by
          have e0 : e⁻¹ * (e * g * e⁻¹) * e = g := by group
          rw [e0]; exact hg)
      have := hvc _ hgR
      calc g * (e⁻¹ * v * e) = e⁻¹ * ((e * g * e⁻¹) * v) * e := by group
        _ = e⁻¹ * (v * (e * g * e⁻¹)) * e := by rw [this]
        _ = (e⁻¹ * v * e) * g := by group
    have hsq : (e⁻¹ * v * e) * (e⁻¹ * v * e) = 1 := by
      calc (e⁻¹ * v * e) * (e⁻¹ * v * e) = e⁻¹ * (v * v) * e := by group
        _ = 1 := by rw [hv2]; group
    have hne : e⁻¹ * v * e ≠ 1 := by
      intro e1
      apply hv1
      calc v = e * (e⁻¹ * v * e) * e⁻¹ := by group
        _ = 1 := by rw [e1]; group
    have hz' := h.central_invol_eq hvP hc hsq hne
    calc v = e * (e⁻¹ * v * e) * e⁻¹ := by group
      _ = e * z * e⁻¹ := by rw [hz']
      _ = u := hez
  zU := h.uU
  uU := h.zU
  une1 := h.zne
  unez := Ne.symm h.unez

theorem exists_ab [Finite X] (hpg : IsPGroup 2 ↥P) (hsyl : ¬ 2 ∣ P.index) (hconj : IsConj z u) :
    ∃ a b : X, a ∈ normalizer ((Qs P U : Subgroup X) : Set X) ∧
      b ∈ normalizer ((Qs P U : Subgroup X) : Set X) ∧
      a * z * a⁻¹ = z ∧ a * u * a⁻¹ = z * u ∧ b * u * b⁻¹ = u ∧ b * z * b⁻¹ = u * z := by
  obtain ⟨a, haP, hau⟩ := exists_a h
  obtain ⟨e, hez, hQR⟩ := exists_conj_sylow h hpg hsyl hconj
  have h' := hyp_conj h hez hQR
  obtain ⟨b, hbR, hbz⟩ := exists_a h'
  refine ⟨a, b, ?_, R_mem_normalizer h hQR hbR, ?_, hau, ?_, hbz⟩
  · rw [mem_normalizer_iff]
    intro q
    constructor
    · exact fun hq => P_normalizes_Qs h haP hq
    · intro hq
      have h1 := P_normalizes_Qs h (inv_mem haP) hq
      have e0 : a⁻¹ * (a * q * a⁻¹) * a⁻¹⁻¹ = q := by group
      rw [e0] at h1
      exact h1
  · rw [h.zcent a haP]; group
  · rw [h'.zcent b hbR]; group

end


theorem eq_top_of_two_elements {α : Type*} [Finite α] (hα : Nat.card α = 3)
    (H : Subgroup (Equiv.Perm α)) {s t : Equiv.Perm α} (hs : s ∈ H) (ht : t ∈ H) (hs1 : s ≠ 1)
    (hst : s ≠ t) (ht1 : t ≠ 1) (hs2 : s * s = 1) : H = ⊤ := by
  have h6 : Nat.card (Equiv.Perm α) = 6 := by rw [Nat.card_perm, hα]; rfl
  have hdvd : Nat.card H ∣ 6 := h6 ▸ Subgroup.card_subgroup_dvd_card H
  have h2 : 2 ∣ Nat.card H := by
    have ho : orderOf (⟨s, hs⟩ : H) = 2 := by
      refine orderOf_eq_prime (by ext1; simpa [pow_two] using hs2) ?_
      intro e
      exact hs1 (by simpa using congrArg Subtype.val e)
    rw [← ho]
    exact orderOf_dvd_natCard _
  have h3 : 3 ≤ Nat.card H := by
    let f : Fin 3 → H := ![1, ⟨s, hs⟩, ⟨t, ht⟩]
    have hf : Function.Injective f := by
      intro i j hij
      have e01 : (1 : H) ≠ ⟨s, hs⟩ := fun e => hs1 (by simpa using (congrArg Subtype.val e).symm)
      have e02 : (1 : H) ≠ ⟨t, ht⟩ := fun e => ht1 (by simpa using (congrArg Subtype.val e).symm)
      have e12 : (⟨s, hs⟩ : H) ≠ ⟨t, ht⟩ := fun e => hst (congrArg Subtype.val e)
      fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [f] at hij; tauto)
    simpa using Nat.card_le_card_of_injective f hf
  have hc : Nat.card H = 6 := by
    have hle : Nat.card H ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    obtain ⟨k, hk⟩ := h2
    interval_cases hH : Nat.card H <;> omega
  exact Subgroup.eq_top_of_card_eq H (hc.trans h6.symm)

section Perm3

variable {X : Type*} [Group X] (U : Subgroup X)

abbrev Us : Type _ := {v : X // v ∈ U ∧ v ≠ 1}

@[expose] def Us.smul' (n : normalizer (U : Set X)) (v : Us U) : Us U :=
  ⟨(n : X) * v * (n : X)⁻¹, (mem_normalizer_iff.mp n.2 v).mp v.2.1, fun e => v.2.2 (by
    have e0 : (v : X) = (n : X)⁻¹ * ((n : X) * v * (n : X)⁻¹) * n := by group
    rw [e0, e]; group)⟩

instance : MulAction (normalizer (U : Set X)) (Us U) where
  smul := Us.smul' U
  one_smul v := Subtype.ext (by simp [HSMul.hSMul, SMul.smul, Us.smul'])
  mul_smul a b v := Subtype.ext (by simp [HSMul.hSMul, SMul.smul, Us.smul']; group)

theorem Us.coe_smul (n : normalizer (U : Set X)) (v : Us U) :
    (((n • v : Us U)) : X) = (n : X) * v * (n : X)⁻¹ := rfl

end Perm3


section Perm3b

variable {X : Type*} [Group X] (U : Subgroup X)

theorem phi_coe (n : normalizer (U : Set X)) (v : Us U) :
    (((MulAction.toPermHom (normalizer (U : Set X)) (Us U)) n v : Us U) : X) =
      (n : X) * v * (n : X)⁻¹ := by
  rw [MulAction.toPermHom_apply, MulAction.toPerm_apply]
  exact Us.coe_smul U n v

theorem ker_Us : (MulAction.toPermHom (normalizer (U : Set X)) (Us U)).ker =
    (centralizer (U : Set X)).subgroupOf (normalizer (U : Set X)) := by
  ext n
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_centralizer_iff]
  constructor
  · intro hn v hv
    by_cases hv1 : v = 1
    · subst hv1; simp
    · have e1 := congrArg (fun σ : Equiv.Perm (Us U) => ((σ ⟨v, hv, hv1⟩ : Us U) : X)) hn
      simp only [phi_coe, Equiv.Perm.coe_one, id_eq] at e1
      calc v * (n : X) = (n : X) * v * (n : X)⁻¹ * n := by rw [e1]
        _ = n * v := by group
  · intro hn
    refine Equiv.ext fun v => Subtype.ext ?_
    rw [phi_coe]
    simp only [Equiv.Perm.coe_one, id_eq]
    rw [← hn v v.2.1]
    group

end Perm3b

section
variable {P U : Subgroup X} {z u : X} (h : Hyp P U z u)
include h

theorem zu_ne_one : z * u ≠ 1 := by
  intro e
  apply h.unez
  have : u = z⁻¹ := eq_inv_of_mul_eq_one_right e
  rw [this]
  exact inv_eq_of_mul_eq_one_right h.zsq

theorem z_ne_zu : z ≠ z * u := fun e => h.une1 (mul_eq_left.mp e.symm)

theorem u_ne_zu : u ≠ z * u := fun e => h.zne (mul_eq_right.mp e.symm)

theorem card_Us : Nat.card (Us U) = 3 := by
  let f : Fin 3 → Us U :=
    ![⟨z, h.zU, h.zne⟩, ⟨u, h.uU, h.une1⟩, ⟨z * u, mul_mem h.zU h.uU, zu_ne_one h⟩]
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have h01 : z ≠ u := Ne.symm h.unez
      have h02 : z ≠ z * u := z_ne_zu h
      have h12 : u ≠ z * u := u_ne_zu h
      have hij' := congrArg Subtype.val hij
      have hz1 : z ≠ 1 := h.zne
      have hu1 : u ≠ 1 := h.une1
      fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp [f] at hij'; tauto)
    · intro v
      rcases U_elems h v.2.1 with e | e | e | e
      · exact absurd e v.2.2
      · exact ⟨0, Subtype.ext e.symm⟩
      · exact ⟨1, Subtype.ext e.symm⟩
      · exact ⟨2, Subtype.ext e.symm⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm.trans (by simp)

theorem s3_main (a b : X) (ha : a ∈ normalizer ((Qs P U : Subgroup X) : Set X))
    (hb : b ∈ normalizer ((Qs P U : Subgroup X) : Set X))
    (haz : a * z * a⁻¹ = z) (hau : a * u * a⁻¹ = z * u) (hbu : b * u * b⁻¹ = u)
    (hbz : b * z * b⁻¹ = u * z) :
    (∀ n ∈ normalizer (U : Set X), ∃ m ∈ normalizer ((Qs P U : Subgroup X) : Set X),
      ∀ v ∈ U, n * v * n⁻¹ = m * v * m⁻¹) ∧
    Nonempty (↥(normalizer (U : Set X)) ⧸
      (centralizer (U : Set X)).subgroupOf (normalizer (U : Set X)) ≃* Equiv.Perm (Fin 3)) := by
  have haU : a ∈ normalizer (U : Set X) := normQ_le_normU h ha
  have hbU : b ∈ normalizer (U : Set X) := normQ_le_normU h hb
  have hfin : Finite (Us U) := Nat.finite_of_card_ne_zero (by rw [card_Us h]; norm_num)
  have hzu : u * z = z * u := h.U_comm h.uU h.zU
  let φ := MulAction.toPermHom (normalizer (U : Set X)) (Us U)
  let aN : normalizer (U : Set X) := ⟨a, haU⟩
  let bN : normalizer (U : Set X) := ⟨b, hbU⟩
  let zs : Us U := ⟨z, h.zU, h.zne⟩
  let us : Us U := ⟨u, h.uU, h.une1⟩
  let zus : Us U := ⟨z * u, mul_mem h.zU h.uU, zu_ne_one h⟩
  have hUs : ∀ v : Us U, v = zs ∨ v = us ∨ v = zus := by
    intro v
    rcases U_elems h v.2.1 with e | e | e | e
    · exact absurd e v.2.2
    · exact Or.inl (Subtype.ext e)
    · exact Or.inr (Or.inl (Subtype.ext e))
    · exact Or.inr (Or.inr (Subtype.ext e))
  have hzu_ne : zs ≠ us := fun e => h.unez (congrArg Subtype.val e).symm
  have hzzu_ne : zs ≠ zus := fun e => z_ne_zu h (congrArg Subtype.val e)
  have huzu_ne : us ≠ zus := fun e => u_ne_zu h (congrArg Subtype.val e)
  have conj_mul : ∀ n x y : X, n * (x * y) * n⁻¹ = (n * x * n⁻¹) * (n * y * n⁻¹) := by
    intro n x y; group
  have a_zs : φ aN zs = zs := Subtype.ext (by rw [phi_coe]; exact haz)
  have a_us : φ aN us = zus := Subtype.ext (by rw [phi_coe]; exact hau)
  have a_zus : φ aN zus = us := Subtype.ext (by
    rw [phi_coe]
    show a * (z * u) * a⁻¹ = u
    rw [conj_mul, haz, hau]
    calc z * (z * u) = (z * z) * u := by group
      _ = u := by rw [h.zsq]; group)
  have b_us : φ bN us = us := Subtype.ext (by rw [phi_coe]; exact hbu)
  have b_zs : φ bN zs = zus := Subtype.ext (by rw [phi_coe]; show b * z * b⁻¹ = z * u; rw [hbz, hzu])
  have b_zus : φ bN zus = zs := Subtype.ext (by
    rw [phi_coe]
    show b * (z * u) * b⁻¹ = z
    rw [conj_mul, hbz, hbu, hzu]
    calc z * u * u = z * (u * u) := by group
      _ = z := by rw [h.Uexp u h.uU]; group)
  have ha1 : φ aN ≠ 1 := by
    intro e
    have := congrArg (fun σ : Equiv.Perm (Us U) => σ us) e
    simp only [a_us, Equiv.Perm.coe_one, id_eq] at this
    exact huzu_ne this.symm
  have hb1 : φ bN ≠ 1 := by
    intro e
    have := congrArg (fun σ : Equiv.Perm (Us U) => σ zs) e
    simp only [b_zs, Equiv.Perm.coe_one, id_eq] at this
    exact hzzu_ne this.symm
  have hab : φ aN ≠ φ bN := by
    intro e
    have := congrArg (fun σ : Equiv.Perm (Us U) => σ zs) e
    simp only [a_zs, b_zs] at this
    exact hzzu_ne this
  have haa : φ aN * φ aN = 1 := by
    refine Equiv.ext fun v => ?_
    rw [Equiv.Perm.mul_apply]
    rcases hUs v with rfl | rfl | rfl
    · rw [a_zs, a_zs]; rfl
    · rw [a_us, a_zus]; rfl
    · rw [a_zus, a_us]; rfl
  set Kq : Subgroup (normalizer (U : Set X)) :=
    (normalizer ((Qs P U : Subgroup X) : Set X)).subgroupOf (normalizer (U : Set X)) with hKq
  have haK : aN ∈ Kq := Subgroup.mem_subgroupOf.mpr ha
  have hbK : bN ∈ Kq := Subgroup.mem_subgroupOf.mpr hb
  have hH : Kq.map φ = ⊤ :=
    eq_top_of_two_elements (card_Us h) _ ⟨aN, haK, rfl⟩ ⟨bN, hbK, rfl⟩ ha1 hab hb1 haa
  have hsurj : Function.Surjective φ := by
    intro σ
    have hσ : σ ∈ Kq.map φ := by rw [hH]; exact Subgroup.mem_top σ
    obtain ⟨k, _, hk⟩ := hσ
    exact ⟨k, hk⟩
  refine ⟨?_, ?_⟩
  · intro n hn
    have hσ : φ ⟨n, hn⟩ ∈ Kq.map φ := by rw [hH]; exact Subgroup.mem_top _
    obtain ⟨k, hkK, hk⟩ := hσ
    refine ⟨(k : X), Subgroup.mem_subgroupOf.mp hkK, fun v hv => ?_⟩
    by_cases hv1 : v = 1
    · subst hv1; simp
    · have e1 : (k : X) * v * (k : X)⁻¹ = n * v * n⁻¹ :=
        congrArg (fun σ : Equiv.Perm (Us U) => ((σ ⟨v, hv, hv1⟩ : Us U) : X)) hk
      exact e1.symm
  · have hker := ker_Us U
    have hnorm : ((centralizer (U : Set X)).subgroupOf (normalizer (U : Set X))).Normal := by
      rw [← hker]; infer_instance
    exact ⟨((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hsurj)).trans
      (Equiv.permCongrHom (Finite.equivFinOfCardEq (card_Us h)))⟩

end

end L1621

structure Thompson1621Concl {X : Type*} [Group X] (P U : Subgroup X) : Prop where
  normalizer_le :
    normalizer ((P ⊓ centralizer (U : Set X) : Subgroup X) : Set X) ≤ normalizer (U : Set X)
  same_action : ∀ n ∈ normalizer (U : Set X),
    ∃ m ∈ normalizer ((P ⊓ centralizer (U : Set X) : Subgroup X) : Set X),
      ∀ v ∈ U, n * v * n⁻¹ = m * v * m⁻¹
  iso_S3 : Nonempty (↥(normalizer (U : Set X)) ⧸
    (centralizer (U : Set X)).subgroupOf (normalizer (U : Set X)) ≃* Equiv.Perm (Fin 3))

theorem thompson_lemma_16_21 {X : Type*} [Group X] [Finite X] {P U : Subgroup X} {z u : X}
    (hP : IsPGroup 2 ↥P) (hsyl : ¬ 2 ∣ P.index) (hcyc : IsCyclic ↥(center ↥P))
    (hUP : U ≤ P) (hUn : ∀ g ∈ P, ∀ v ∈ U, g * v * g⁻¹ ∈ U) (hU : Nat.card U = 4)
    (hexp : ∀ a ∈ U, a * a = 1) (hzP : z ∈ P) (hzsq : z * z = 1) (hz1 : z ≠ 1)
    (hzc : ∀ g ∈ P, g * z = z * g) (hu : u ∈ U) (huz : u ∉ zpowers z) (hconj : IsConj z u) :
    Thompson1621Concl P U := by
  have h := L1621.Hyp.of_cyclic hP hcyc hUP hUn hU hexp hzP hzsq hz1 hzc hu
    (fun e => huz (e ▸ one_mem _)) (fun e => huz (e ▸ mem_zpowers z))
  obtain ⟨a, b, ha, hb, haz, hau, hbu, hbz⟩ := L1621.exists_ab h hP hsyl hconj
  obtain ⟨hsame, hs3⟩ := L1621.s3_main h a b ha hb haz hau hbu hbz
  exact ⟨fun n hn => L1621.normQ_le_normU h hn, hsame, hs3⟩

end CFSG.GH74.GLS.Bg
