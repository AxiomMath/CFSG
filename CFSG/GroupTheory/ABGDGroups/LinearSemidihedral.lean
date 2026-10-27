module

public import CFSG.GroupTheory.QuasiDihedralFusion.Defs

public section

namespace CFSG.ABGDGroups

open CFSG.Open CFSG.QuasiDihedralFusion
open CFSG.GorensteinWalter (HasDihedralSylowTwo)

section Model

variable {n : ℕ}

theorem semidihedral_exists_orderOf_eq_eight (hn : 4 ≤ n) :
    ∃ x : SemidihedralGroup n, orderOf x = 8 := by
  have hr : orderOf (CFSG.Semidihedral.r n) = 2 ^ (n - 1) :=
    CFSG.Semidihedral.orderOf_r n (by omega)
  refine ⟨CFSG.Semidihedral.r n ^ 2 ^ (n - 4), ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (by rw [hr]; exact Nat.pow_dvd_pow 2 (by omega)), hr,
    Nat.pow_div (by omega) (by norm_num), show n - 1 - (n - 4) = 3 by omega]

theorem semidihedral_card_le_four (hn : 4 ≤ n) (X : Subgroup (SemidihedralGroup n))
    (hX : ∀ x ∈ X, x ^ 2 = 1) : Nat.card X ≤ 4 := by
  set D := CFSG.Semidihedral.dihedralSubgroup n
  have hXD : X ≤ D := by
    intro x hx
    by_cases h1 : x = 1
    · rw [h1]
      exact D.one_mem
    · exact CFSG.Semidihedral.involution_mem_dihedralSubgroup n (by omega) x
        (orderOf_eq_prime (hX x hx) h1)
  let e : DihedralGroup (2 ^ (n - 2)) ≃* D := CFSG.Semidihedral.dihedralEquiv n hn
  set W : Subgroup (DihedralGroup (2 ^ (n - 2))) := (X.subgroupOf D).map e.symm.toMonoidHom
  have hWcard : Nat.card W = Nat.card X := by
    change Nat.card ((X.subgroupOf D).map e.symm.toMonoidHom) = _
    rw [Subgroup.card_map_of_injective (f := e.symm.toMonoidHom) e.symm.injective]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXD).toEquiv
  have hW2 : ∀ w ∈ W, w ^ 2 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow]
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hX _ hx)
    rw [hx2, map_one]
  rw [← hWcard]
  rcases CFSG.GorensteinWalter.subgroups_dihedral_twoGroup_cyclic_or_dihedral
      (m := n - 2) (by omega) W with hcyc | ⟨k, hk, ⟨eW⟩⟩
  · obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := W)
    have hcard : Nat.card W = orderOf g :=
      (orderOf_eq_card_of_forall_mem_zpowers hg).symm
    have hg2 : orderOf g ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hW2 _ g.property))
    have := Nat.le_of_dvd (by norm_num) hg2
    omega
  · have hr : orderOf (eW.symm (DihedralGroup.r 1)) = 2 ^ k := by
      rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_r_one]
    have hr2 : 2 ^ k ∣ 2 := by
      rw [← hr]
      exact orderOf_dvd_of_pow_eq_one
        (Subtype.ext (by simpa using hW2 _ (eW.symm (DihedralGroup.r 1)).property))
    have hk1 : k ≤ 1 := by
      have := Nat.le_of_dvd (by norm_num) hr2
      by_contra hk2
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [Nat.card_congr eW.toEquiv, DihedralGroup.nat_card]
    obtain rfl : k = 1 := by omega
    norm_num

theorem semidihedral_not_dihedral (hn : 4 ≤ n) {m : ℕ}
    (e : DihedralGroup (2 ^ m) ≃* SemidihedralGroup n) : False := by
  set D := CFSG.Semidihedral.dihedralSubgroup n
  have hinv : ∀ i, e (DihedralGroup.sr i) ∈ D := fun i =>
    CFSG.Semidihedral.involution_mem_dihedralSubgroup n (by omega) _
      (by rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr])
  have hall : ∀ x, e x ∈ D := by
    rintro (i | i)
    · rw [show DihedralGroup.r i = DihedralGroup.sr 0 * DihedralGroup.sr i by
        rw [DihedralGroup.sr_mul_sr, sub_zero], map_mul]
      exact D.mul_mem (hinv 0) (hinv i)
    · exact hinv i
  have htop : D = ⊤ := eq_top_iff.mpr fun y _ => by
    obtain ⟨x, rfl⟩ := e.surjective y
    exact hall x
  have h1 : Nat.card D = CFSG.Semidihedral.modulus n := CFSG.Semidihedral.dihedralSubgroup_card n hn
  rw [htop, Subgroup.card_top, CFSG.Semidihedral.card n (by omega),
    CFSG.Semidihedral.modulus] at h1
  have := Nat.pow_right_injective (le_refl 2) h1
  omega

end Model

section Ambient

variable {H : Type*} [Group H] [Finite H] {n : ℕ}

omit [Finite H] in
theorem exists_orderOf_eq_eight_of_hasSemidihedralSylow (hSD : HasSemidihedralSylow H n) :
    ∃ x : H, orderOf x = 8 := by
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨f⟩ := hSD.2 S
  obtain ⟨x, hx⟩ := semidihedral_exists_orderOf_eq_eight hSD.1
  refine ⟨(f x : H), ?_⟩
  rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
  exact hx

omit [Finite H] in
theorem card_le_four_of_hasSemidihedralSylow (hSD : HasSemidihedralSylow H n)
    {X : Subgroup H} (hX : ∀ x ∈ X, x ^ 2 = 1) : Nat.card X ≤ 4 := by
  have h2 : IsPGroup 2 X := fun x => ⟨1, Subtype.ext (by simpa using hX _ x.property)⟩
  obtain ⟨S, hXS⟩ := h2.exists_le_sylow
  obtain ⟨f⟩ := hSD.2 S
  have h := semidihedral_card_le_four hSD.1 ((X.subgroupOf S).map f.symm.toMonoidHom) (by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have hx2 : x ^ 2 = 1 := Subtype.ext (by simpa using hX _ hx)
    rw [hx2, map_one])
  rwa [Subgroup.card_map_of_injective f.symm.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXS).toEquiv] at h

theorem false_of_hasSemidihedralSylow_of_kleinFour (hSD : HasSemidihedralSylow H n)
    {V : Subgroup H} (hV : IsKleinFour V) {t : H} (ht : t ^ 2 = 1) (htV : t ∉ V)
    (hc : ∀ v ∈ V, v * t = t * v) : False := by
  have hV2 : ∀ v ∈ V, v ^ 2 = 1 := fun v hv => by
    have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
    rw [hV.exponent_two] at h
    simpa using congrArg Subtype.val h
  have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := fun v hv w hw => by
    have h1 := hV2 _ (V.mul_mem hv hw)
    have h2 := hV2 v hv
    have h3 := hV2 w hw
    rw [sq] at h1 h2 h3
    calc v * w = v * (v * w * (v * w)) * w := by rw [h1, mul_one]
      _ = (v * v) * w * v * (w * w) := by group
      _ = w * v := by rw [h2, h3, one_mul, mul_one]
  have htt : t * t = 1 := by rw [← sq]; exact ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hct : ∀ x, (x ∈ V ∨ x * t ∈ V) → x * t = t * x := by
    rintro x (hx | hx)
    · exact hc x hx
    · have h := hc _ hx
      have h' : x = t * x * t := by
        calc x = x * t * t := by rw [mul_assoc, htt, mul_one]
          _ = t * (x * t) := h
          _ = t * x * t := by rw [mul_assoc]
      calc x * t = t * x * t * t := by rw [← h']
        _ = t * x := by rw [mul_assoc, htt, mul_one]
  let X : Subgroup H :=
    { carrier := {x | x ∈ V ∨ x * t ∈ V}
      mul_mem' := by
        rintro x y hx' hy'
        have hyt := hct y hy'
        rcases hx' with hx | hx <;> rcases hy' with hy | hy
        · exact Or.inl (V.mul_mem hx hy)
        · exact Or.inr (by rw [mul_assoc]; exact V.mul_mem hx hy)
        · right
          have : x * y * t = x * t * y := by rw [mul_assoc, hyt, ← mul_assoc]
          rw [this]
          exact V.mul_mem hx hy
        · left
          have : x * y = x * t * (y * t) := by
            rw [hyt, ← mul_assoc, mul_assoc x t t, htt, mul_one]
          rw [this]
          exact V.mul_mem hx hy
      one_mem' := Or.inl V.one_mem
      inv_mem' := by
        rintro x hx'
        have hxt := hct x hx'
        rcases hx' with hx | hx
        · exact Or.inl (V.inv_mem hx)
        · right
          have hcomm : x⁻¹ * t = t * x⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq, mul_assoc, ← hxt, ← mul_assoc, inv_mul_cancel, one_mul]
          have : x⁻¹ * t = (x * t)⁻¹ := by rw [mul_inv_rev, htinv, hcomm]
          rw [this]
          exact V.inv_mem hx }
  have hX2 : ∀ x ∈ X, x ^ 2 = 1 := by
    rintro x hx'
    have hxt := hct x hx'
    rcases hx' with hx | hx
    · exact hV2 x hx
    · have h := hV2 _ hx
      rw [sq] at h ⊢
      calc x * x = x * t * (x * t) := by
            rw [mul_assoc x t, ← mul_assoc t x t, ← hxt, mul_assoc x t t, htt, mul_one]
        _ = 1 := h
  have hlt : V < X := by
    refine lt_of_le_of_ne (fun v hv => Or.inl hv) ?_
    intro hVX
    apply htV
    have htX : t ∈ X := Or.inr (by rw [htt]; exact V.one_mem)
    rw [← hVX] at htX
    exact htX
  have hcard := Subgroup.card_lt_of_lt hlt
  have h4 := card_le_four_of_hasSemidihedralSylow hSD hX2
  rw [hV.card_four] at hcard
  omega

omit [Finite H] in
theorem not_hasDihedralSylowTwo_of_hasSemidihedralSylow (hSD : HasSemidihedralSylow H n) :
    ¬ HasDihedralSylowTwo H := by
  intro hD
  obtain ⟨S⟩ : Nonempty (Sylow 2 H) := inferInstance
  obtain ⟨f⟩ := hSD.2 S
  obtain ⟨m, -, ⟨e⟩⟩ := hD S
  exact semidihedral_not_dihedral hSD.1 (e.symm.trans f.symm)

end Ambient

end CFSG.ABGDGroups
