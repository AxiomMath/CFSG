module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G]

@[expose] def gamma1 (U S : Subgroup G) : Subgroup G :=
  ⨆ w ∈ U, ⨆ (_ : w ≠ 1), S ⊓ Subgroup.centralizer ({w} : Set G)

theorem inf_centralizer_le_gamma1 {U S : Subgroup G} {w : G} (hw : w ∈ U) (hw1 : w ≠ 1) :
    S ⊓ Subgroup.centralizer ({w} : Set G) ≤ gamma1 U S :=
  le_iSup₂_of_le w hw (le_iSup_of_le hw1 le_rfl)

theorem exists_ne_one_fixed [Finite G] {X : Subgroup G} (hX : IsPGroup 2 X) (hX1 : X ≠ ⊥) {w : G}
    (hw2 : w * w = 1) (hwX : conjSub w X = X) : ∃ x ∈ X, x ≠ 1 ∧ w * x * w⁻¹ = x := by
  classical
  have : Fintype X := Fintype.ofFinite _
  have hmem : ∀ x ∈ X, w * x * w⁻¹ ∈ X := fun x hx => hwX ▸ conj_mem_conjSub hx
  let f : Function.End X := fun x => ⟨w * x * w⁻¹, hmem x x.2⟩
  have hf : f ^ 2 ^ 1 = 1 := by
    funext x
    apply Subtype.ext
    show w * (w * (x : G) * w⁻¹) * w⁻¹ = x
    have : w * (w * (x : G) * w⁻¹) * w⁻¹ = (w * w) * x * (w * w)⁻¹ := by group
    rw [this, hw2]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1) hf
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp hX)
  have hn0 : n ≠ 0 := by
    rintro rfl
    apply hX1
    rw [pow_zero] at hn
    exact (Subgroup.card_eq_one).mp hn
  have heven : 2 ∣ Fintype.card X := by
    rw [← Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 hn0
  have hfix1 : (1 : X) ∈ Function.fixedPoints f := by
    apply Subtype.ext
    simp [f]
  have hdvd : 2 ∣ Fintype.card (Function.fixedPoints f) :=
    (Nat.ModEq.dvd_iff hmod (by norm_num)).mp heven
  have hlt : 1 < Fintype.card (Function.fixedPoints f) := by
    have hpos : 0 < Fintype.card (Function.fixedPoints f) :=
      Fintype.card_pos_iff.mpr ⟨⟨1, hfix1⟩⟩
    have := Nat.le_of_dvd hpos hdvd
    omega
  obtain ⟨⟨y, hy⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card hlt ⟨1, hfix1⟩
  refine ⟨y, y.2, fun h => hne ?_, congrArg Subtype.val hy⟩
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem mul_conj_mem_inf_centralizer {X S : Subgroup G} (hXS : X ≤ S) {w : G} (hw : w ∈ S)
    (hw2 : w * w = 1) (hcomm : Commutes X (conjSub w X)) {x : G} (hx : x ∈ X) :
    x * (w * x * w⁻¹) ∈ S ⊓ Subgroup.centralizer ({w} : Set G) := by
  have hxS : x ∈ S := hXS hx
  have hc : x * (w * x * w⁻¹) = (w * x * w⁻¹) * x := hcomm x hx _ (conj_mem_conjSub hx)
  have e : w * (x * (w * x * w⁻¹)) * w⁻¹ = (w * x * w⁻¹) * x := by
    have : w * (x * (w * x * w⁻¹)) * w⁻¹ = (w * x * w⁻¹) * ((w * w) * x * (w * w)⁻¹) := by group
    rw [this, hw2]
    simp
  have e2 : w * (x * (w * x * w⁻¹)) * w⁻¹ = x * (w * x * w⁻¹) := by rw [e, hc]
  have hcent : x * (w * x * w⁻¹) ∈ Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * (w * x * w⁻¹) * w = (w * (x * (w * x * w⁻¹)) * w⁻¹) * w := by rw [e2]
      _ = w * (x * (w * x * w⁻¹)) := by group
  exact ⟨S.mul_mem hxS (S.mul_mem (S.mul_mem hw hxS) (S.inv_mem hw)), hcent⟩

theorem lemma_3_10 [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) {Δ : Set (Subgroup G)}
    (hΔS : ∀ X ∈ Δ, X ≤ S) (hinv : ∀ X ∈ Δ, ∀ s ∈ S, conjSub s X ∈ Δ)
    (hcomm : ∀ X ∈ Δ, ∀ Y ∈ Δ, X ≠ Y → Commutes X Y) {u v : G} (hu : u ∈ S) (hv : v ∈ S)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) (huv : u ≠ v) (hu2 : u * u = 1) (hv2 : v * v = 1)
    (hc : u * v = v * u) {X : Subgroup G} (hX : X ∈ Δ)
    (hΦ : ∃ x ∈ X, x * x ≠ 1 ∨ ∃ y ∈ X, x * y ≠ y * x) :
    gamma1 (Subgroup.closure {u, v}) S ⊓ X ≠ ⊥ := by
  set U : Subgroup G := Subgroup.closure {u, v} with hU
  set Γ : Subgroup G := gamma1 U S with hΓ
  have hXS : X ≤ S := hΔS X hX
  have hX2 : IsPGroup 2 X := hS.to_le hXS
  have huU : u ∈ U := Subgroup.subset_closure (by simp)
  have hvU : v ∈ U := Subgroup.subset_closure (by simp)
  have huvU : u * v ∈ U := U.mul_mem huU hvU
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huv1 : u * v ≠ 1 := by
    intro h
    apply huv
    have := inv_eq_of_mul_eq_one_right h
    rwa [hui] at this
  have huv2 : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by group
      _ = u * (u * v) * v := by rw [hc]
      _ = (u * u) * (v * v) := by group
      _ = 1 := by rw [hu2, hv2]; simp
  have hne1 : X ≠ ⊥ := by
    obtain ⟨x, hx, h | ⟨y, hy, h⟩⟩ := hΦ
    · rw [Ne, Subgroup.eq_bot_iff_forall]
      intro hb
      exact h (by rw [hb x hx]; simp)
    · rw [Ne, Subgroup.eq_bot_iff_forall]
      intro hb
      apply h
      rw [hb x hx]
      simp
  by_cases hA : ∃ w, w ∈ ({u, v, u * v} : Set G) ∧ conjSub w X = X
  ·
    obtain ⟨w, hw, hwX⟩ := hA
    have hwU : w ∈ U := by
      rcases hw with rfl | rfl | rfl
      · exact huU
      · exact hvU
      · exact huvU
    have hw1 : w ≠ 1 := by
      rcases hw with rfl | rfl | rfl
      · exact hu1
      · exact hv1
      · exact huv1
    have hw2 : w * w = 1 := by
      rcases hw with rfl | rfl | rfl
      · exact hu2
      · exact hv2
      · exact huv2
    obtain ⟨x, hx, hx1, hxw⟩ := exists_ne_one_fixed hX2 hne1 hw2 hwX
    have hxc : x ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have : w * x = x * w := by
        calc w * x = (w * x * w⁻¹) * w := by group
          _ = x * w := by rw [hxw]
      exact this.symm
    have hxΓ : x ∈ Γ := inf_centralizer_le_gamma1 hwU hw1 ⟨hXS hx, hxc⟩
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hb
    exact hx1 (hb x ⟨hxΓ, hx⟩)
  · push Not at hA
    have hu' : conjSub u X ≠ X := hA u (by simp)
    have hv' : conjSub v X ≠ X := hA v (by simp)
    have huv' : conjSub (u * v) X ≠ X := hA (u * v) (by simp)
    have hXu : conjSub u X ∈ Δ := hinv X hX u hu
    have hXv : conjSub v X ∈ Δ := hinv X hX v hv
    have hXXu : X ≠ conjSub u X := fun h => hu' h.symm
    have hXXv : X ≠ conjSub v X := fun h => hv' h.symm
    have hXuXv : conjSub u X ≠ conjSub v X := by
      intro h
      apply huv'
      calc conjSub (u * v) X = conjSub u (conjSub v X) := conjSub_mul u v X
        _ = conjSub u (conjSub u X) := by rw [← h]
        _ = conjSub (u * u) X := (conjSub_mul u u X).symm
        _ = X := by rw [hu2, conjSub_one]
    have c1 : Commutes X (conjSub u X) := hcomm X hX _ hXu hXXu
    have c2 : Commutes X (conjSub v X) := hcomm X hX _ hXv hXXv
    have c3 : Commutes (conjSub u X) (conjSub v X) := hcomm _ hXu _ hXv hXuXv
    have hA' : ∀ x ∈ X, x * (u * x * u⁻¹) ∈ Γ := fun x hx =>
      inf_centralizer_le_gamma1 huU hu1 (mul_conj_mem_inf_centralizer hXS hu hu2 c1 hx)
    have hB' : ∀ x ∈ X, x * (v * x * v⁻¹) ∈ Γ := fun x hx =>
      inf_centralizer_le_gamma1 hvU hv1 (mul_conj_mem_inf_centralizer hXS hv hv2 c2 hx)
    have hpu : (u * v) * u = v := by
      calc (u * v) * u = (v * u) * u := by rw [hc]
        _ = v * (u * u) := by group
        _ = v := by rw [hu2]; simp
    have hpv : (u * v) * v = u := by
      calc (u * v) * v = u * (v * v) := by group
        _ = u := by rw [hv2]; simp
    have hC' : ∀ x ∈ X, (u * x * u⁻¹) * (v * x * v⁻¹) ∈ Γ := by
      intro x hx
      have hxS : x ∈ S := hXS hx
      have hy : u * x * u⁻¹ ∈ conjSub u X := conj_mem_conjSub hx
      have hz : v * x * v⁻¹ ∈ conjSub v X := conj_mem_conjSub hx
      have hyz : (u * x * u⁻¹) * (v * x * v⁻¹) = (v * x * v⁻¹) * (u * x * u⁻¹) := c3 _ hy _ hz
      have e1 : (u * v) * (u * x * u⁻¹) * (u * v)⁻¹ = v * x * v⁻¹ := by
        calc (u * v) * (u * x * u⁻¹) * (u * v)⁻¹ = ((u * v) * u) * x * ((u * v) * u)⁻¹ := by group
          _ = v * x * v⁻¹ := by rw [hpu]
      have e2 : (u * v) * (v * x * v⁻¹) * (u * v)⁻¹ = u * x * u⁻¹ := by
        calc (u * v) * (v * x * v⁻¹) * (u * v)⁻¹ = ((u * v) * v) * x * ((u * v) * v)⁻¹ := by group
          _ = u * x * u⁻¹ := by rw [hpv]
      have e : (u * v) * ((u * x * u⁻¹) * (v * x * v⁻¹)) * (u * v)⁻¹ =
          (u * x * u⁻¹) * (v * x * v⁻¹) := by
        calc (u * v) * ((u * x * u⁻¹) * (v * x * v⁻¹)) * (u * v)⁻¹
            = ((u * v) * (u * x * u⁻¹) * (u * v)⁻¹) * ((u * v) * (v * x * v⁻¹) * (u * v)⁻¹) := by
              group
          _ = (v * x * v⁻¹) * (u * x * u⁻¹) := by rw [e1, e2]
          _ = (u * x * u⁻¹) * (v * x * v⁻¹) := hyz.symm
      have hcent : (u * x * u⁻¹) * (v * x * v⁻¹) ∈ Subgroup.centralizer ({u * v} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc (u * x * u⁻¹) * (v * x * v⁻¹) * (u * v)
            = ((u * v) * ((u * x * u⁻¹) * (v * x * v⁻¹)) * (u * v)⁻¹) * (u * v) := by rw [e]
          _ = (u * v) * ((u * x * u⁻¹) * (v * x * v⁻¹)) := by group
      exact inf_centralizer_le_gamma1 huvU huv1
        ⟨S.mul_mem (S.mul_mem (S.mul_mem hu hxS) (S.inv_mem hu))
          (S.mul_mem (S.mul_mem hv hxS) (S.inv_mem hv)), hcent⟩
    have hsq : ∀ x ∈ X, x * x ∈ Γ := by
      intro x hx
      have hy : u * x * u⁻¹ ∈ conjSub u X := conj_mem_conjSub hx
      have hz : v * x * v⁻¹ ∈ conjSub v X := conj_mem_conjSub hx
      have hxy : x * (u * x * u⁻¹) = (u * x * u⁻¹) * x := c1 x hx _ hy
      have e : x * x = (x * (u * x * u⁻¹)) * (x * (v * x * v⁻¹)) *
          ((u * x * u⁻¹) * (v * x * v⁻¹))⁻¹ := by
        calc x * x = x * ((u * x * u⁻¹) * x) * (u * x * u⁻¹)⁻¹ := by
              rw [← hxy]
              group
          _ = _ := by group
      rw [e]
      exact Γ.mul_mem (Γ.mul_mem (hA' x hx) (hB' x hx)) (Γ.inv_mem (hC' x hx))
    have hcom : ∀ x ∈ X, ∀ x' ∈ X, x * x' * x⁻¹ * x'⁻¹ ∈ Γ := by
      intro x hx x' hx'
      have hy : u * x * u⁻¹ ∈ conjSub u X := conj_mem_conjSub hx
      have hz : v * x' * v⁻¹ ∈ conjSub v X := conj_mem_conjSub hx'
      have hyx' : (u * x * u⁻¹) * x' = x' * (u * x * u⁻¹) := (c1 x' hx' _ hy).symm
      have hzx : x * (v * x' * v⁻¹) = (v * x' * v⁻¹) * x := c2 x hx _ hz
      have hyz : (u * x * u⁻¹) * (v * x' * v⁻¹) = (v * x' * v⁻¹) * (u * x * u⁻¹) := c3 _ hy _ hz
      have hAB : (x * (u * x * u⁻¹)) * (x' * (v * x' * v⁻¹)) =
          (x * x') * ((u * x * u⁻¹) * (v * x' * v⁻¹)) := by
        calc (x * (u * x * u⁻¹)) * (x' * (v * x' * v⁻¹))
            = x * ((u * x * u⁻¹) * x') * (v * x' * v⁻¹) := by group
          _ = x * (x' * (u * x * u⁻¹)) * (v * x' * v⁻¹) := by rw [hyx']
          _ = (x * x') * ((u * x * u⁻¹) * (v * x' * v⁻¹)) := by group
      have hBA : (x' * (v * x' * v⁻¹)) * (x * (u * x * u⁻¹)) =
          (x' * x) * ((u * x * u⁻¹) * (v * x' * v⁻¹)) := by
        calc (x' * (v * x' * v⁻¹)) * (x * (u * x * u⁻¹))
            = x' * ((v * x' * v⁻¹) * x) * (u * x * u⁻¹) := by group
          _ = x' * (x * (v * x' * v⁻¹)) * (u * x * u⁻¹) := by rw [hzx]
          _ = (x' * x) * ((v * x' * v⁻¹) * (u * x * u⁻¹)) := by group
          _ = (x' * x) * ((u * x * u⁻¹) * (v * x' * v⁻¹)) := by rw [hyz]
      have key : x * x' * x⁻¹ * x'⁻¹ =
          ((x * (u * x * u⁻¹)) * (x' * (v * x' * v⁻¹)) * (x * (u * x * u⁻¹))⁻¹ *
            (x' * (v * x' * v⁻¹))⁻¹) := by
        calc x * x' * x⁻¹ * x'⁻¹
            = ((x * x') * ((u * x * u⁻¹) * (v * x' * v⁻¹))) *
                ((x' * x) * ((u * x * u⁻¹) * (v * x' * v⁻¹)))⁻¹ := by group
          _ = _ := by rw [← hAB, ← hBA]; group
      rw [key]
      exact Γ.mul_mem (Γ.mul_mem (Γ.mul_mem (hA' x hx) (hB' x' hx')) (Γ.inv_mem (hA' x hx)))
        (Γ.inv_mem (hB' x' hx'))
    rw [Ne, Subgroup.eq_bot_iff_forall]
    intro hb
    obtain ⟨x, hx, h | ⟨y, hy, h⟩⟩ := hΦ
    · exact h (hb _ ⟨hsq x hx, X.mul_mem hx hx⟩)
    · have hmem : x * y * x⁻¹ * y⁻¹ ∈ Γ ⊓ X :=
        ⟨hcom x hx y hy, X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)⟩
      have := hb _ hmem
      apply h
      calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
        _ = y * x := by rw [this]; simp

end CFSG.ClassicalInvolution.Asc77
