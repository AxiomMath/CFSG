module

public import CFSG.ClassicalGroups.SpecialLinear.QuasisimpleCartanRank

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type*} [Group H]
  (π : SpecialLinearGroup (Fin n) F →* H)

omit [Finite F] [CharP F 2] in
theorem injOn_unitriangular (hker : π.ker ≤ LinearFlag.scalars n F) :
    Set.InjOn π (LinearFlag.unitriangular n F) := by
  intro a ha b hb hab
  have hm : a⁻¹ * b ∈ LinearFlag.unitriangular n F ⊓ π.ker := by
    refine ⟨?_, ?_⟩
    · exact (LinearFlag.unitriangular n F).mul_mem
        ((LinearFlag.unitriangular n F).inv_mem ha) hb
    · exact MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hab, inv_mul_cancel])
  have hscal : a⁻¹ * b ∈ LinearFlag.scalars n F := hker hm.2
  have hbot : a⁻¹ * b ∈ (⊥ : Subgroup (SpecialLinearGroup (Fin n) F)) := by
    rw [← LinearFlag.unitriangular_inf_scalars (n := n) (K := F)]
    exact ⟨hm.1, hscal⟩
  rw [Subgroup.mem_bot, inv_mul_eq_one] at hbot
  exact hbot

theorem mem_map_unitriangular_of_mem_range (hker : π.ker ≤ LinearFlag.scalars n F) {d : H}
    (hdr : d ∈ π.range)
    (hdU : d ∈ Subgroup.normalizer ((LinearFlag.unitriangular n F).map π : Set H))
    (hd2 : d * d = 1) : d ∈ (LinearFlag.unitriangular n F).map π := by
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hdr
    have hsub : Subsingleton (Fin 0) := ⟨fun a _ => a.elim0⟩
    have hsubSL : Subsingleton (SpecialLinearGroup (Fin 0) F) :=
      @Matrix.SpecialLinearGroup.subsingleton_of_subsingleton (Fin 0) _ _ F _ hsub
    have hg1 : g = 1 := @Subsingleton.elim _ hsubSL g 1
    rw [← hg, hg1]
    exact Subgroup.mem_map_of_mem π (LinearFlag.unitriangular 0 F).one_mem
  · have hU2 : IsPGroup 2 (LinearFlag.unitriangular n F) := by
      obtain ⟨m, -, hmcard⟩ :=
        @FiniteField.card F _ (Fintype.ofFinite F) 2 _
      refine IsPGroup.of_card (n := (m : ℕ) * (n * (n - 1) / 2)) ?_
      rw [LinearFlag.card_unitriangular (K := F) (n := n),
        @Nat.card_eq_fintype_card F (Fintype.ofFinite F), hmcard, pow_mul]
    have hZodd : Odd (Nat.card (LinearFlag.scalars n F)) :=
      (CFSG.ClassicalGroups.SpecialLinear.odd_card_sub_one_of_char_two (F := F)).of_dvd_nat
        (LinearFlag.card_scalars_dvd (K := F) (n := n) hn)
    have key : ∀ (h : SpecialLinearGroup (Fin n) F) (e : H), π h = e →
        e ∈ Subgroup.normalizer ((LinearFlag.unitriangular n F).map π : Set H) →
        ∀ u ∈ LinearFlag.unitriangular n F,
          h * u * h⁻¹ ∈ LinearFlag.unitriangular n F := by
      intro h e hhe heU u hu
      have hconj_mem : π (h * u * h⁻¹) ∈ (LinearFlag.unitriangular n F).map π := by
        rw [map_mul, map_mul, map_inv, hhe]
        exact (Subgroup.mem_normalizer_iff.mp heU (π u)).mp
          (Subgroup.mem_map_of_mem π hu)
      obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.mp hconj_mem
      let z : SpecialLinearGroup (Fin n) F := u'⁻¹ * (h * u * h⁻¹)
      have hzker : z ∈ π.ker := by
        refine MonoidHom.mem_ker.mpr ?_
        dsimp [z]
        rw [map_mul, map_inv, hu'eq, inv_mul_cancel]
      have hzscal : z ∈ LinearFlag.scalars n F := hker hzker
      have hzcenter : z ∈ Subgroup.center (SpecialLinearGroup (Fin n) F) :=
        LinearFlag.scalars_le_center n F hzscal
      have hheq : h * u * h⁻¹ = u' * z := by
        dsimp [z]
        group
      obtain ⟨a, ha⟩ := hU2.exists_orderOf_eq_pow (⟨u', hu'⟩ : LinearFlag.unitriangular n F)
      obtain ⟨b, hb⟩ := hU2.exists_orderOf_eq_pow (⟨u, hu⟩ : LinearFlag.unitriangular n F)
      have ha' : orderOf u' = 2 ^ a := by
        rw [Subgroup.orderOf_coe (⟨u', hu'⟩ : LinearFlag.unitriangular n F)]
        exact ha
      have hb' : orderOf u = 2 ^ b := by
        rw [Subgroup.orderOf_coe (⟨u, hu⟩ : LinearFlag.unitriangular n F)]
        exact hb
      have hconj_order : orderOf (h * u * h⁻¹) ∣ 2 ^ b := by
        rw [← hb']
        exact orderOf_map_dvd
          (MulAut.conj h : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) u
      have hcomm : Commute u'⁻¹ (h * u * h⁻¹) := by
        rw [hheq]
        exact ((Commute.refl u').mul_right
          (Subgroup.mem_center_iff.mp hzcenter u')).inv_left
      have hz2 : orderOf z ∣ 2 ^ (a + b) := by
        have hdiv := hcomm.orderOf_mul_dvd_lcm
        rw [show u'⁻¹ * (h * u * h⁻¹) = z from rfl] at hdiv
        refine hdiv.trans (Nat.lcm_dvd ?_ ?_)
        · rw [orderOf_inv, ha']
          exact Nat.pow_dvd_pow 2 (by omega)
        · exact hconj_order.trans (Nat.pow_dvd_pow 2 (by omega))
      have hzcard : orderOf z ∣ Nat.card (LinearFlag.scalars n F) :=
        (LinearFlag.scalars n F).orderOf_dvd_natCard hzscal
      have hz1 : z = 1 := by
        have hdvd : orderOf z ∣
            Nat.gcd (2 ^ (a + b)) (Nat.card (LinearFlag.scalars n F)) :=
          Nat.dvd_gcd hz2 hzcard
        rw [((hZodd.coprime_two_left).pow_left (a + b)).gcd_eq_one] at hdvd
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd)
      rw [hheq, hz1, mul_one]
      exact hu'
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hdr
    have hgN : g ∈ Subgroup.normalizer
        (LinearFlag.unitriangular n F : Set (SpecialLinearGroup (Fin n) F)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact key g d hg hdU x hx
      · intro hx
        have hx' : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ ∈ LinearFlag.unitriangular n F :=
          key g⁻¹ d⁻¹ (by rw [map_inv, hg])
            ((Subgroup.normalizer _).inv_mem hdU) (g * x * g⁻¹) hx
        simpa [mul_assoc] using hx'
    have hgB : g ∈ LinearFlag.upperTriangular n F := by
      rw [← LinearFlag.normalizer_unitriangular (n := n) (K := F)]
      exact hgN
    have hg2ker : g * g ∈ π.ker :=
      MonoidHom.mem_ker.mpr (by rw [map_mul, hg, hd2])
    have hoddK : Odd (Nat.card (π.ker)) :=
      hZodd.of_dvd_nat (Subgroup.card_dvd_of_le hker)
    have hcop : (Nat.card (π.ker)).Coprime 2 := Nat.coprime_two_right.mpr hoddK
    obtain ⟨c, hc2sub⟩ := hcop.pow_left_bijective.surjective ⟨g * g, hg2ker⟩
    have hcK : (c : SpecialLinearGroup (Fin n) F) ∈ π.ker := c.2
    have hcscal : (c : SpecialLinearGroup (Fin n) F) ∈ LinearFlag.scalars n F := hker hcK
    have hc2 : (c : SpecialLinearGroup (Fin n) F) * (c : SpecialLinearGroup (Fin n) F) =
        g * g := by
      have := congrArg Subtype.val hc2sub
      simpa [pow_two] using this
    let g' : SpecialLinearGroup (Fin n) F := g * (c : SpecialLinearGroup (Fin n) F)⁻¹
    have hg'B : g' ∈ LinearFlag.upperTriangular n F :=
      (LinearFlag.upperTriangular n F).mul_mem hgB
        ((LinearFlag.upperTriangular n F).inv_mem
          (LinearFlag.scalars_le_upperTriangular n F hcscal))
    have hc_center : (c : SpecialLinearGroup (Fin n) F) ∈
        Subgroup.center (SpecialLinearGroup (Fin n) F) :=
      LinearFlag.scalars_le_center n F hcscal
    have hc_comm_c : Commute g (c : SpecialLinearGroup (Fin n) F) :=
      Subgroup.mem_center_iff.mp hc_center g
    have hc_comm : Commute g ((c : SpecialLinearGroup (Fin n) F)⁻¹) := hc_comm_c.inv_right
    have hg'2 : g' * g' = 1 := by
      have hcalc : g * (c : SpecialLinearGroup (Fin n) F)⁻¹ *
          (g * (c : SpecialLinearGroup (Fin n) F)⁻¹) =
          (g * g) * ((c : SpecialLinearGroup (Fin n) F)⁻¹ *
            (c : SpecialLinearGroup (Fin n) F)⁻¹) := by
        calc g * (c : SpecialLinearGroup (Fin n) F)⁻¹ *
              (g * (c : SpecialLinearGroup (Fin n) F)⁻¹)
            = g * ((c : SpecialLinearGroup (Fin n) F)⁻¹ * g) *
                (c : SpecialLinearGroup (Fin n) F)⁻¹ := by group
          _ = g * (g * (c : SpecialLinearGroup (Fin n) F)⁻¹) *
                (c : SpecialLinearGroup (Fin n) F)⁻¹ := by rw [← hc_comm.eq]
          _ = (g * g) * ((c : SpecialLinearGroup (Fin n) F)⁻¹ *
                (c : SpecialLinearGroup (Fin n) F)⁻¹) := by group
      dsimp [g']
      rw [hcalc, ← hc2]
      group
    have hg'U : g' ∈ LinearFlag.unitriangular n F := by
      rw [LinearFlag.mem_unitriangular]
      refine ⟨LinearFlag.mem_upperTriangular.mp hg'B, ?_⟩
      intro i
      have hmat : ((g' : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) * ((g' : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) = 1 := by
        have := congrArg
          (fun x : SpecialLinearGroup (Fin n) F => (x : Matrix (Fin n) (Fin n) F)) hg'2
        simpa [SpecialLinearGroup.coe_mul] using this
      have hupp : ((g' : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F).IsUpperTriangular :=
        LinearFlag.mem_upperTriangular_iff_isUpperTriangular.mp hg'B
      have hdiag : ((g' : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i *
          ((g' : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i = 1 := by
        rw [← LinearFlag.mul_apply_self_of_isUpperTriangular hupp hupp, hmat, one_apply_eq]
      have hsq : (((g' : SpecialLinearGroup (Fin n) F) :
          Matrix (Fin n) (Fin n) F) i i) ^ 2 = 1 := by
        rw [pow_two]
        exact hdiag
      rcases sq_eq_one_iff.mp hsq with h1 | hneg
      · exact h1
      · rw [hneg, neg_one_eq_one_iff.mpr (ringChar.eq F 2)]
    refine Subgroup.mem_map.mpr ⟨g', hg'U, ?_⟩
    dsimp [g']
    rw [map_mul, map_inv, hg, MonoidHom.mem_ker.mp hcK, inv_one, mul_one]

theorem exists_unitriangular_lift (hker : π.ker ≤ LinearFlag.scalars n F) {D : Subgroup H}
    (hDr : D ≤ π.range)
    (hDU : D ≤ Subgroup.normalizer ((LinearFlag.unitriangular n F).map π : Set H))
    (hD2 : ∀ d ∈ D, d * d = 1) :
    ∃ A₀ : Subgroup (SpecialLinearGroup (Fin n) F),
      A₀ ≤ LinearFlag.unitriangular n F ∧ A₀.map π = D ∧ Set.InjOn π A₀ ∧
        Nat.card A₀ = Nat.card D := by
  classical
  let A₀ : Subgroup (SpecialLinearGroup (Fin n) F) :=
    LinearFlag.unitriangular n F ⊓ D.comap π
  have hA₀_le : A₀ ≤ LinearFlag.unitriangular n F := inf_le_left
  have hmap : A₀.map π = D := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact ha.2
    · intro d hd
      have hdU : d ∈ (LinearFlag.unitriangular n F).map π :=
        mem_map_unitriangular_of_mem_range π hker (hDr hd) (hDU hd) (hD2 d hd)
      obtain ⟨u, hu, hueq⟩ := Subgroup.mem_map.mp hdU
      exact Subgroup.mem_map.mpr
        ⟨u, ⟨hu, Subgroup.mem_comap.mpr (by rw [hueq]; exact hd)⟩, hueq⟩
  have hinj : Set.InjOn π (A₀ : Set (SpecialLinearGroup (Fin n) F)) :=
    (injOn_unitriangular π hker).mono hA₀_le
  refine ⟨A₀, hA₀_le, hmap, hinj, ?_⟩
  have hset : (D : Set H) = π '' (A₀ : Set (SpecialLinearGroup (Fin n) F)) := by
    rw [← hmap]
    rfl
  calc Nat.card A₀ = (A₀ : Set (SpecialLinearGroup (Fin n) F)).ncard :=
        Nat.card_coe_set_eq _
    _ = (π '' (A₀ : Set (SpecialLinearGroup (Fin n) F))).ncard :=
        (hinj.ncard_image).symm
    _ = (D : Set H).ncard := by rw [← hset]
    _ = Nat.card D := Nat.card_coe_set_eq _

end CFSG.LieType.SpecialLinear
