module

public import CFSG.LargeExtraspecial.S12LinAlg

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

@[expose] noncomputable def CXbar12 (g : G) : Subgroup S.O :=
  S.Mbar ⊓ centralizer (S.Xbar12 g : Set S.O)

variable {S}

theorem CXbar12_le_Mbar {g : G} : S.CXbar12 g ≤ S.Mbar := inf_le_left

theorem commute_of_mem_CXbar12 {g : G} {c x : S.O} (hc : c ∈ S.CXbar12 g)
    (hx : x ∈ S.Xbar12 g) : c * x = x * c :=
  (mem_centralizer_iff.mp hc.2 x hx).symm

theorem Mbar_le_normalizer_CXbar12 {g : G} : S.Mbar ≤ normalizer (S.CXbar12 g : Set S.O) := by
  intro m hm
  refine mem_normalizer_of_conj_le (fun c hc => ?_) (fun c hc => ?_)
  · refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hm hc.1) (S.Mbar.inv_mem hm),
      mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : m⁻¹ * x * m⁻¹⁻¹ ∈ S.Xbar12 g :=
      (mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 (S.Mbar.inv_mem hm)) x).mp hx
    have e := commute_of_mem_CXbar12 hc hx'
    calc x * (m * c * m⁻¹) = m * ((m⁻¹ * x * m⁻¹⁻¹) * c) * m⁻¹ := by group
      _ = m * (c * (m⁻¹ * x * m⁻¹⁻¹)) * m⁻¹ := by rw [e]
      _ = m * c * m⁻¹ * x := by group
  · have hm' := S.Mbar.inv_mem hm
    refine ⟨S.Mbar.mul_mem (S.Mbar.mul_mem hm' hc.1) (S.Mbar.inv_mem hm'),
      mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : m * x * m⁻¹ ∈ S.Xbar12 g :=
      (mem_normalizer_iff.mp (Mbar_le_normalizer_Xbar12 hm) x).mp hx
    have e := commute_of_mem_CXbar12 hc hx'
    calc x * (m⁻¹ * c * m⁻¹⁻¹) = m⁻¹ * ((m * x * m⁻¹) * c) * m := by group
      _ = m⁻¹ * (c * (m * x * m⁻¹)) * m := by rw [e]
      _ = m⁻¹ * c * m⁻¹⁻¹ * x := by group

theorem CXbar12_inf_fixSub12_eq_bot {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) :
    S.CXbar12 g ⊓ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) = ⊥ := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hC : S12NoNormalTwo (S.CXbar12 g) :=
    S.s12_noNormalTwo_Mbar.of_normal CXbar12_le_Mbar Mbar_le_normalizer_CXbar12
  have hK : S12NoNormalTwo (S.CXbar12 g ⊓ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt))) := by
    refine hC.of_normal inf_le_left fun c hc => ?_
    have hc' : c⁻¹ ∈ S.CXbar12 g := (S.CXbar12 g).inv_mem hc
    refine mem_normalizer_of_conj_le (fun k hk => ⟨?_, ?_⟩) (fun k hk => ⟨?_, ?_⟩)
    · exact (S.CXbar12 g).mul_mem ((S.CXbar12 g).mul_mem hc hk.1) hc'
    · exact conj_mem_fixSub12 (commute_of_mem_CXbar12 hc htX) hk.2
    · exact (S.CXbar12 g).mul_mem ((S.CXbar12 g).mul_mem hc' hk.1)
        ((S.CXbar12 g).inv_mem hc')
    · exact conj_mem_fixSub12 (commute_of_mem_CXbar12 hc' htX) hk.2
  have haW := (S.timmesfeld_12_6 haQ hne ht htA).1
  refine S.s12_eq_bot_of_fix haQ hne hn hK (inf_le_left.trans CXbar12_le_Mbar)
    (fun k hk => hk.2 _ haW) fun ℓ hℓ => ?_
  have hcomm : ∀ {x : S.O}, x ∈ S.Lbar g → x * t = t * x := fun {x} hx =>
    congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨x, hx⟩ ⟨t, ht⟩)
  have hℓM := S.Lbar_le_Mbar g hℓ
  have hℓ' : ℓ⁻¹ ∈ S.Lbar g := (S.Lbar g).inv_mem hℓ
  refine mem_normalizer_of_conj_le (fun k hk => ⟨?_, ?_⟩) (fun k hk => ⟨?_, ?_⟩)
  · exact (mem_normalizer_iff.mp (Mbar_le_normalizer_CXbar12 hℓM) k).mp hk.1
  · exact conj_mem_fixSub12 (hcomm hℓ) hk.2
  · exact (mem_normalizer_iff.mp (Mbar_le_normalizer_CXbar12 (S.Mbar.inv_mem hℓM)) k).mp hk.1
  · exact conj_mem_fixSub12 (hcomm hℓ') hk.2

theorem eq_of_agree_CXbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {c c' : S.O} (hc : c ∈ S.CXbar12 g)
    (hc' : c' ∈ S.CXbar12 g)
    (h : ∀ w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt),
      (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w = (c' : S.Qt ≃ₗ[ZMod 2] S.Qt) w) : c = c' := by
  have hK := CXbar12_inf_fixSub12_eq_bot haQ hne hn ht htA
  have hmem : c⁻¹ * c' ∈ S.CXbar12 g ⊓ S.fixSub12 (commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) := by
    refine ⟨(S.CXbar12 g).mul_mem ((S.CXbar12 g).inv_mem hc) hc', fun w hw => ?_⟩
    rw [Subgroup.coe_mul, LinearEquiv.mul_apply, ← h w hw, ← LinearEquiv.mul_apply,
      ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  rw [hK, mem_bot] at hmem
  calc c = c * (c⁻¹ * c') := by rw [hmem, mul_one]
    _ = c' := by group

theorem CXbar12_apply_mem {g : G} {t : S.O} (htX : t ∈ S.Xbar12 g) {c : S.O}
    (hc : c ∈ S.CXbar12 g) {w : S.Qt} (hw : w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt)) :
    (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt) :=
  apply_mem_commSpace_of_commute (commute_of_mem_CXbar12 hc htX) hw

theorem CXbar12_pow_six {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {c : S.O} (hc : c ∈ S.CXbar12 g) :
    c ^ 6 = 1 := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have h6 := s12_pow_six_apply htA.2.2.2.1 (x := (c : S.Qt ≃ₗ[ZMod 2] S.Qt))
    (fun w hw => CXbar12_apply_mem htX hc hw)
    (fun w hw => CXbar12_apply_mem htX ((S.CXbar12 g).inv_mem hc) hw)
  refine eq_of_agree_CXbar12 haQ hne hn ht htA ((S.CXbar12 g).pow_mem hc 6)
    (S.CXbar12 g).one_mem fun w hw => ?_
  rw [Subgroup.coe_pow, h6 w hw]
  rfl

theorem exists_pow_three_CXbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) (hC : S.CXbar12 g ≠ ⊥) :
    ∃ z ∈ S.CXbar12 g, z ≠ 1 ∧ z ^ 3 = 1 := by
  by_contra hcon
  push Not at hcon
  have h2 : IsPGroup 2 (S.CXbar12 g) := by
    rintro ⟨c, hc⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
    by_contra hc2
    exact hcon (c ^ 2) ((S.CXbar12 g).pow_mem hc 2) hc2
      (by rw [← pow_mul]; exact CXbar12_pow_six haQ hne hn ht htA hc)
  have hN : S12NoNormalTwo (S.CXbar12 g) :=
    S.s12_noNormalTwo_Mbar.of_normal CXbar12_le_Mbar Mbar_le_normalizer_CXbar12
  exact hC (hN _ le_rfl h2 le_normalizer)

theorem exists_moved_CXbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {c : S.O} (hc : c ∈ S.CXbar12 g)
    (hc1 : c ≠ 1) :
    ∃ w ∈ commSpace (t : S.Qt ≃ₗ[ZMod 2] S.Qt), (c : S.Qt ≃ₗ[ZMod 2] S.Qt) w ≠ w := by
  by_contra hcon
  push Not at hcon
  exact hc1 (eq_of_agree_CXbar12 haQ hne hn ht htA hc (S.CXbar12 g).one_mem
    fun w hw => by rw [hcon w hw]; rfl)

theorem conj_eq_or_CXbar12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {z : S.O} (hz : z ∈ S.CXbar12 g)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) {m : S.O} (hm : m ∈ S.Mbar) :
    m * z * m⁻¹ = z ∨ m * z * m⁻¹ = z ^ 2 := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  have hz' : m * z * m⁻¹ ∈ S.CXbar12 g :=
    (mem_normalizer_iff.mp (Mbar_le_normalizer_CXbar12 hm) z).mp hz
  have hz'1 : m * z * m⁻¹ ≠ 1 := fun e => hz1 (by
    calc z = m⁻¹ * (m * z * m⁻¹) * m := by group
      _ = 1 := by rw [e]; group)
  have hz'3 : (m * z * m⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hz3]
    group
  have hc3 : ((z : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hz3]
    rfl
  have hc'3 : ((m * z * m⁻¹ : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hz'3]
    rfl
  rcases s12_eq_or_eq_sq_of_pow_three htA.2.2.2.1 hc3 hc'3
      (fun w hw => CXbar12_apply_mem htX hz hw) (fun w hw => CXbar12_apply_mem htX hz' hw)
      (exists_moved_CXbar12 haQ hne hn ht htA hz hz1)
      (exists_moved_CXbar12 haQ hne hn ht htA hz' hz'1) with h | h
  · left
    exact eq_of_agree_CXbar12 haQ hne hn ht htA hz' hz h
  · right
    refine eq_of_agree_CXbar12 haQ hne hn ht htA hz' ((S.CXbar12 g).pow_mem hz 2) fun w hw => ?_
    rw [h w hw, Subgroup.coe_pow]

theorem fixSpace_sq_eq_of_pow_three {z : S.O} (hz3 : z ^ 3 = 1) {v : S.Qt}
    (hv : ((z ^ 2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v) :
    (z : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
  have e3 : ((z ^ 3 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by rw [hz3]; rfl
  rw [pow_succ', Subgroup.coe_mul, LinearEquiv.mul_apply, hv] at e3
  exact e3

theorem fixSpace_eq_bot_or_isReducible12 {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {z : S.O} (hz : z ∈ S.CXbar12 g)
    (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1) :
    fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥ ∨ S.IsReducible12 := by
  by_cases hb : fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) = ⊥
  · exact Or.inl hb
  · right
    refine ⟨fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt), hb, fun ht' => hz1 ?_, fun m v hv => ?_⟩
    · refine Subtype.ext (OrthoF2.eq_one_of_forall_apply_eq fun v => ?_)
      have : v ∈ fixSpace (z : S.Qt ≃ₗ[ZMod 2] S.Qt) := ht' ▸ Submodule.mem_top
      exact mem_fixSpace.mp this
    · have hm : S.ρ m ∈ S.Mbar := ⟨m, rfl⟩
      have hmz : (S.ρ m)⁻¹ * z * (S.ρ m)⁻¹⁻¹ = z ∨ (S.ρ m)⁻¹ * z * (S.ρ m)⁻¹⁻¹ = z ^ 2 :=
        conj_eq_or_CXbar12 haQ hne hn ht htA hz hz1 hz3 (S.Mbar.inv_mem hm)
      rw [mem_fixSpace]
      have hv' := mem_fixSpace.mp hv
      rcases hmz with h | h
      ·
        have hzm : z * S.ρ m = S.ρ m * z := by
          calc z * S.ρ m = S.ρ m * ((S.ρ m)⁻¹ * z * (S.ρ m)⁻¹⁻¹) := by group
            _ = S.ρ m * z := by rw [h]
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hzm, Subgroup.coe_mul,
          LinearEquiv.mul_apply, hv']
      ·
        have hzm : z * S.ρ m = S.ρ m * z ^ 2 := by
          calc z * S.ρ m = S.ρ m * ((S.ρ m)⁻¹ * z * (S.ρ m)⁻¹⁻¹) := by group
            _ = S.ρ m * z ^ 2 := by rw [h]
        have hz2v : ((z ^ 2 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
          rw [pow_two, Subgroup.coe_mul, LinearEquiv.mul_apply, hv', hv']
        rw [← LinearEquiv.mul_apply, ← Subgroup.coe_mul, hzm, Subgroup.coe_mul,
          LinearEquiv.mul_apply, hz2v]

end Setting

end CFSG.LargeExtraspecial
