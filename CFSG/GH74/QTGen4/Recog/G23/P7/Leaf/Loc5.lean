module

public import CFSG.GH74.QTGen4.Recog.G23.P7.Leaf.Loc5B
public import CFSG.GH74.QTGen4.Recog.G23.P7.OpenLeaves

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GH74.QTGen4.Recog.G23.P7

open CFSG.Open CFSG.Quasithin.G23Type CFSG.GH74.QTGen4.Recog.G23 CFSG.CosetTable

variable {G : Type} [Group G]

theorem leafLoc5 : LeafLoc5 := by
  intro G _ _ T H H₁ H₂ M e M₁ M₂ Pb Np Nm hS hF hO hL hPb hM
  have hone : G23One H H₁ H₂ := hS.ctx.one
  have hlet : HLetters H H₁ H₂ e := hS.lets
  have hv1 : VertexCore e H (e 0) H₂ M₁ := hL.v₁
  have hv2 : VertexCore e H (e 2) H₁ M₂ := hL.v₂
  have hpb : PbarCore e Pb := hL.pb
  have hnp : MixedCore e (e 0 * e 2) Np := hL.np
  have hnm : MixedCore e (e 0 * (e 2)⁻¹) Nm := hL.nm
  have hcor : Cor37 e M₁ M₂ Pb := hL.cor
  have hP : Nat.card ↥(Psub e) = 9 := hF.card_P
  set z : G := zOf e with hz
  have rel1 : e 0 ^ 3 = 1 := by
    rw [pow_three]
    have := hlet.rels [(0, true), (0, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel2 : e 2 ^ 3 = 1 := by
    rw [pow_three]
    have := hlet.rels [(2, true), (2, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel3 : (e 1)⁻¹ * (e 0)⁻¹ * e 1 * (e 0)⁻¹ * (e 1)⁻¹ * e 0 = 1 := by
    have := hlet.rels [(1, false), (0, false), (1, true), (0, false), (1, false), (0, true)]
      (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel5 : (e 3)⁻¹ * (e 2)⁻¹ * e 3 * (e 2)⁻¹ * (e 3)⁻¹ * e 2 = 1 := by
    have := hlet.rels [(3, false), (2, false), (3, true), (2, false), (3, false), (2, true)]
      (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel7 : e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹ = 1 := by
    have := hlet.rels [(0, true), (1, true), (0, true), (1, true), (3, false), (2, false),
      (3, false), (2, false)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel8 : (e 0)⁻¹ * (e 2)⁻¹ * e 0 * e 2 = 1 := by
    have := hlet.rels [(0, false), (2, false), (0, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel12 : e 4 * e 4 = 1 := by
    have := hlet.rels [(4, true), (4, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel13 : e 4 * e 0 * e 4 * e 0 = 1 := by
    have := hlet.rels [(4, true), (0, true), (4, true), (0, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel14 : e 4 * e 1 * e 4 * e 1 = 1 := by
    have := hlet.rels [(4, true), (1, true), (4, true), (1, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel15 : e 4 * e 2 * e 4 * e 2 = 1 := by
    have := hlet.rels [(4, true), (2, true), (4, true), (2, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have rel16 : e 4 * e 3 * e 4 * e 3 = 1 := by
    have := hlet.rels [(4, true), (3, true), (4, true), (3, true)] (by simp [g23WordsH])
    simpa [FreeGroup.lift_mk, mul_assoc] using this
  have hzz : z = e 0 * e 1 * (e 0 * e 1) := by rw [hz]; exact pow_two _
  have hz23 : z = e 2 * e 3 * (e 2 * e 3) := by
    have h1 : e 0 * e 1 * (e 0 * e 1) = e 2 * e 3 * (e 2 * e 3) := by
      calc e 0 * e 1 * (e 0 * e 1)
          = (e 0 * e 1 * e 0 * e 1 * (e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹) *
              ((e 3)⁻¹ * (e 2)⁻¹ * (e 3)⁻¹ * (e 2)⁻¹)⁻¹ := by group
        _ = e 2 * e 3 * (e 2 * e 3) := by rw [rel7, one_mul]; group
    rw [hzz]
    exact h1
  have he0H : e 0 ∈ H := by
    rw [← hlet.gen]
    exact Subgroup.subset_closure ⟨0, rfl⟩
  have he2H : e 2 ∈ H := by
    rw [← hlet.gen]
    exact Subgroup.subset_closure ⟨2, rfl⟩
  have he4H : e 4 ∈ H := by
    rw [← hlet.gen]
    exact Subgroup.subset_closure ⟨4, rfl⟩
  have he3H₂ : e 3 ∈ H₂ := by
    rw [← hlet.gen₂]
    exact Subgroup.subset_closure (by simp)
  have he2H₂ : e 2 ∈ H₂ := by
    rw [← hlet.gen₂]
    exact Subgroup.subset_closure (by simp)
  have he0H₁ : e 0 ∈ H₁ := by
    rw [← hlet.gen₁]
    exact Subgroup.subset_closure (by simp)
  have he1H₁ : e 1 ∈ H₁ := by
    rw [← hlet.gen₁]
    exact Subgroup.subset_closure (by simp)
  have hzH₁ : z ∈ H₁ := by
    rw [hzz]
    exact H₁.mul_mem (H₁.mul_mem he0H₁ he1H₁) (H₁.mul_mem he0H₁ he1H₁)
  have hzH₂ : z ∈ H₂ := by
    rw [hz23]
    exact H₂.mul_mem (H₂.mul_mem he2H₂ he3H₂) (H₂.mul_mem he2H₂ he3H₂)
  have hzK : z ∈ H₁ ⊓ H₂ := Subgroup.mem_inf.mpr ⟨hzH₁, hzH₂⟩
  have hz2 : z * z = 1 := by
    have h1 := orderOf_dvd_natCard (⟨z, hzK⟩ : ↥(H₁ ⊓ H₂))
    rw [hone.card_inf] at h1
    have h2 : (⟨z, hzK⟩ : ↥(H₁ ⊓ H₂)) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
    have h3 : z ^ 2 = 1 := congrArg Subtype.val h2
    rw [pow_two] at h3
    exact h3
  have hK_unique : ∀ x ∈ H₁ ⊓ H₂, x ≠ 1 → x = z := by
    intro x hx hx1
    obtain ⟨y0, _, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(H₁ ⊓ H₂))).mp hone.card_inf
    have h1 := huniq ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
    have hzne : z ≠ 1 := by
      intro h1'
      have hpbz : Pb ⊓ Subgroup.centralizer ({z} : Set G) = Psub e := hpb.inf_cent_z
      have hle : Pb ≤ Pb ⊓ Subgroup.centralizer ({z} : Set G) := by
        intro p hp
        refine Subgroup.mem_inf.mpr ⟨hp, ?_⟩
        rw [Subgroup.mem_centralizer_singleton_iff, h1', mul_one, one_mul]
      rw [hpbz] at hle
      have hc := Subgroup.card_le_of_le hle
      rw [hPb, hP] at hc
      omega
    have h2 := huniq ⟨z, hzK⟩ (fun h => hzne (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)
  have hzne : z ≠ 1 := by
    intro h1'
    have hpbz : Pb ⊓ Subgroup.centralizer ({z} : Set G) = Psub e := hpb.inf_cent_z
    have hle : Pb ≤ Pb ⊓ Subgroup.centralizer ({z} : Set G) := by
      intro p hp
      refine Subgroup.mem_inf.mpr ⟨hp, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, h1', mul_one, one_mul]
    rw [hpbz] at hle
    have hc := Subgroup.card_le_of_le hle
    rw [hPb, hP] at hc
    omega
  have hzCP : z ∈ Subgroup.centralizer (Psub e : Set G) := by
    have h1 : z ∈ Subgroup.centralizer (Psub e : Set G) ⊓ H := by
      rw [hF.centP]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
    exact h1.1
  have hHz : ∀ x ∈ H, x * z = z * x := by
    intro x hx
    rw [hone.eq_centralizer] at hx
    exact (Subgroup.mem_centralizer_iff.mp hx z hzK).symm
  have hCz : ∀ y : G, y * z = z * y → y ∈ H := by
    intro y hy
    rw [hone.eq_centralizer, Subgroup.mem_centralizer_iff]
    intro g hg
    rcases eq_or_ne g 1 with rfl | hg1
    · simp
    · rw [hK_unique g hg hg1]
      exact hy.symm
  have hP0 : e 0 ∈ Psub e := Subgroup.subset_closure (by simp)
  have hP2 : e 2 ∈ Psub e := Subgroup.subset_closure (by simp)
  have hz_e0 : z * e 0 = e 0 * z := (Subgroup.mem_centralizer_iff.mp hzCP (e 0) hP0).symm
  have hz_e2 : z * e 2 = e 2 * z := (Subgroup.mem_centralizer_iff.mp hzCP (e 2) hP2).symm
  have hzC1 : z ∈ Subgroup.centralizer ({e 0} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hz_e0
  have hzC2 : z ∈ Subgroup.centralizer ({e 2} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hz_e2
  have hc02 : e 0 * e 2 = e 2 * e 0 := loc5_comm_of_rel rel8
  have hPH : Psub e ≤ H := by
    apply (Subgroup.closure_le _).mpr
    intro x hx
    rcases hx with h | h
    · rw [h]; exact he0H
    · rw [h]; exact he2H
  have hP_ord : Nat.card ↥(Psub e) = 9 := hP
  have ht_inv : (e 4)⁻¹ = e 4 := inv_eq_of_mul_eq_one_right rel12
  have hte0 : e 4 * e 0 * (e 4)⁻¹ = (e 0)⁻¹ := loc5_conj_inv rel12 rel13
  have hte1 : e 4 * e 1 * (e 4)⁻¹ = (e 1)⁻¹ := loc5_conj_inv rel12 rel14
  have hte2 : e 4 * e 2 * (e 4)⁻¹ = (e 2)⁻¹ := loc5_conj_inv rel12 rel15
  have hte3 : e 4 * e 3 * (e 4)⁻¹ = (e 3)⁻¹ := loc5_conj_inv rel12 rel16
  have hc1 : e 4 * z * (e 4)⁻¹ = (e 0)⁻¹ * (e 1)⁻¹ * ((e 0)⁻¹ * (e 1)⁻¹) := by
    rw [hzz]
    calc e 4 * (e 0 * e 1 * (e 0 * e 1)) * (e 4)⁻¹
        = (e 4 * e 0 * (e 4)⁻¹) * (e 4 * e 1 * (e 4)⁻¹) *
            ((e 4 * e 0 * (e 4)⁻¹) * (e 4 * e 1 * (e 4)⁻¹)) := by group
      _ = _ := by rw [hte0, hte1]
  have hc2 : e 4 * z * (e 4)⁻¹ = (e 2)⁻¹ * (e 3)⁻¹ * ((e 2)⁻¹ * (e 3)⁻¹) := by
    rw [hz23]
    calc e 4 * (e 2 * e 3 * (e 2 * e 3)) * (e 4)⁻¹
        = (e 4 * e 2 * (e 4)⁻¹) * (e 4 * e 3 * (e 4)⁻¹) *
            ((e 4 * e 2 * (e 4)⁻¹) * (e 4 * e 3 * (e 4)⁻¹)) := by group
      _ = _ := by rw [hte2, hte3]
  have ht_ne_one : e 4 ≠ 1 := by
    intro h1
    have hsub : H ≤ Subgroup.centralizer ({e 4} : Set G) := by
      intro y _
      rw [h1, Subgroup.mem_centralizer_singleton_iff, mul_one, one_mul]
    have hinf : Subgroup.centralizer ({e 4} : Set G) ⊓ H = H := inf_eq_right.mpr hsub
    have h8 := hF.card_cent_t
    rw [hinf, hF.card_H] at h8
    omega
  have ht_ne_z : e 4 ≠ z := by
    intro h1
    have hsub : H ≤ Subgroup.centralizer ({e 4} : Set G) := by
      intro y hy
      rw [h1, Subgroup.mem_centralizer_singleton_iff]
      exact hHz y hy
    have hinf : Subgroup.centralizer ({e 4} : Set G) ⊓ H = H := inf_eq_right.mpr hsub
    have h8 := hF.card_cent_t
    rw [hinf, hF.card_H] at h8
    omega
  have htz_conj : e 4 * z * (e 4)⁻¹ = z := by
    have hmem : e 4 * z * (e 4)⁻¹ ∈ H₁ ⊓ H₂ := by
      apply Subgroup.mem_inf.mpr
      constructor
      · rw [hc1]
        exact H₁.mul_mem (H₁.mul_mem (H₁.inv_mem he0H₁) (H₁.inv_mem he1H₁))
          (H₁.mul_mem (H₁.inv_mem he0H₁) (H₁.inv_mem he1H₁))
      · rw [hc2]
        exact H₂.mul_mem (H₂.mul_mem (H₂.inv_mem he2H₂) (H₂.inv_mem he3H₂))
          (H₂.mul_mem (H₂.inv_mem he2H₂) (H₂.inv_mem he3H₂))
    have hne : e 4 * z * (e 4)⁻¹ ≠ 1 := by
      intro h
      apply hzne
      calc z = (e 4)⁻¹ * (e 4 * z * (e 4)⁻¹) * e 4 := by group
        _ = 1 := by rw [h]; group
    exact hK_unique _ hmem hne
  have htz : e 4 * z = z * e 4 := by
    calc e 4 * z = (e 4 * z * (e 4)⁻¹) * e 4 := by group
      _ = z * e 4 := by rw [htz_conj]
  have hzt : z * e 4 = e 4 * z := htz.symm
  have htz_inv : (e 4 * z) * (e 4 * z) = 1 := by
    calc e 4 * z * (e 4 * z) = e 4 * (z * e 4) * z := by group
      _ = e 4 * (e 4 * z) * z := by rw [hzt]
      _ = (e 4 * e 4) * (z * z) := by group
      _ = 1 := by rw [rel12, hz2, mul_one]
  have hPbt : ∀ m ∈ Pb, e 4 * m * (e 4)⁻¹ ∈ Pb := fun m hm => hpb.conj_t m hm
  have hH2le : H₂ ≤ Subgroup.centralizer ({e 0} : Set G) := hv1.compl.right_le
  have hH1le : H₁ ≤ Subgroup.centralizer ({e 2} : Set G) := hv2.compl.right_le
  have hM1le : M₁ ≤ Subgroup.centralizer ({e 0} : Set G) := hv1.compl.left_le
  have hM2le : M₂ ≤ Subgroup.centralizer ({e 2} : Set G) := hv2.compl.left_le
  have hs1M1 : e 0 ∈ M₁ := by
    have h1 : e 0 ∈ M₁ ⊓ H := by
      rw [hv1.inf_H]
      exact Subgroup.mem_zpowers _
    exact h1.1
  have hs2M2 : e 2 ∈ M₂ := by
    have h1 : e 2 ∈ M₂ ⊓ H := by
      rw [hv2.inf_H]
      exact Subgroup.mem_zpowers _
    exact h1.1
  have hM1H : ∀ x ∈ M₁, x ∈ H → x ∈ Subgroup.zpowers (e 0) := by
    intro x hx hxH
    have h1 : x ∈ M₁ ⊓ H := Subgroup.mem_inf.mpr ⟨hx, hxH⟩
    rw [hv1.inf_H] at h1
    exact h1
  have hM2H : ∀ x ∈ M₂, x ∈ H → x ∈ Subgroup.zpowers (e 2) := by
    intro x hx hxH
    have h1 : x ∈ M₂ ⊓ H := Subgroup.mem_inf.mpr ⟨hx, hxH⟩
    rw [hv2.inf_H] at h1
    exact h1
  have hσA1 : e 0 ∈ M₁ ⊓ Subgroup.centralizer (M₁ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hs1M1, Subgroup.mem_centralizer_iff.mpr
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mp (hM1le hm))⟩
  have hσA2 : e 2 ∈ M₂ ⊓ Subgroup.centralizer (M₂ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hs2M2, Subgroup.mem_centralizer_iff.mpr
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mp (hM2le hm))⟩
  have hc20 : e 2 * e 0 = e 0 * e 2 := hc02.symm
  have hzN1 : z ∈ Subgroup.normalizer (M₁ : Set G) :=
    loc5_normalizer_of hzC1 hv1.compl.conj_mem
  have hzN2 : z ∈ Subgroup.normalizer (M₂ : Set G) :=
    loc5_normalizer_of hzC2 hv2.compl.conj_mem
  have hτN1 : e 2 ∈ Subgroup.normalizer (M₁ : Set G) :=
    loc5_normalizer_of (Subgroup.mem_centralizer_singleton_iff.mpr hc20) hv1.compl.conj_mem
  have hτN2 : e 0 ∈ Subgroup.normalizer (M₂ : Set G) :=
    loc5_normalizer_of (Subgroup.mem_centralizer_singleton_iff.mpr hc02) hv2.compl.conj_mem
  have he3N1 : e 3 ∈ Subgroup.normalizer (M₁ : Set G) :=
    loc5_normalizer_of (hH2le he3H₂) hv1.compl.conj_mem
  have he1N2 : e 1 ∈ Subgroup.normalizer (M₂ : Set G) :=
    loc5_normalizer_of (hH1le he1H₁) hv2.compl.conj_mem
  have ht_N1 : e 4 ∈ Subgroup.normalizer (M₁ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro m
    constructor
    · intro hm
      exact hv1.conj_t m hm
    · intro hm
      have h := hv1.conj_t _ hm
      have e1 : e 4 * (e 4 * m * (e 4)⁻¹) * (e 4)⁻¹ = (e 4 * e 4) * m * (e 4 * e 4)⁻¹ := by
        group
      rw [e1, rel12] at h
      simpa using h
  have hσ0ne : e 0 ≠ 1 := by
    intro h0
    have hle : Psub e ≤ Subgroup.zpowers (e 2) := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases hx with h | h
      · rw [h, h0]; exact Subgroup.one_mem _
      · rw [h]; exact Subgroup.mem_zpowers _
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hP] at hc
    have hd : orderOf (e 2) ∣ 3 := orderOf_dvd_of_pow_eq_one rel2
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hσ2ne : e 2 ≠ 1 := by
    intro h2
    have hle : Psub e ≤ Subgroup.zpowers (e 0) := by
      apply (Subgroup.closure_le _).mpr
      intro x hx
      rcases hx with h | h
      · rw [h]; exact Subgroup.mem_zpowers _
      · rw [h, h2]; exact Subgroup.one_mem _
    have hc := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hP] at hc
    have hd : orderOf (e 0) ∣ 3 := orderOf_dvd_of_pow_eq_one rel1
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hord2 : orderOf (e 2) = 3 := by
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime rel2 hσ2ne
  have hA1 : Nat.card ↥(M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) = 27 := hM.card_Z₁
  have hA2 : Nat.card ↥(M₂ ⊓ Subgroup.centralizer (M₂ : Set G)) = 27 := hM.card_Z₂
  have hσA1 : e 0 ∈ M₁ ⊓ Subgroup.centralizer (M₁ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hs1M1, Subgroup.mem_centralizer_iff.mpr
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mp (hM1le hm))⟩
  have hσA2 : e 2 ∈ M₂ ⊓ Subgroup.centralizer (M₂ : Set G) :=
    Subgroup.mem_inf.mpr ⟨hs2M2, Subgroup.mem_centralizer_iff.mpr
      (fun m hm => Subgroup.mem_centralizer_singleton_iff.mp (hM2le hm))⟩
  obtain ⟨Am1, hAm1, hAm1card, hdec1⟩ :=
    loc5_inv_part z (e 0) M₁ hM.exp₁ hA1 hzN1 hσA1 rel1 hσ0ne hz_e0 hz2 hM.zinv₁
  have hτnot1 : ¬ ∀ a ∈ M₁ ⊓ Subgroup.centralizer (M₁ : Set G), e 2 * a = a * e 2 := by
    intro hc
    haveI : Nontrivial ↥Am1 :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hAm1card]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥Am1)
    have hxA := (hAm1 x.1).mp x.2
    exact loc5_not_central rel5 hz23 (M₁ ⊓ Subgroup.centralizer (M₁ : Set G))
      (fun a ha => loc5_conj_center he3N1 ha) hc (fun a ha => hM.exp₁ a ha.1)
      ⟨x.1, hxA.1, fun h => hx (Subtype.ext h), hxA.2⟩
  obtain ⟨Fix1, hFix1, hFix1card, hK1card⟩ :=
    loc5_tau_part z (e 0) (e 2) M₁ Am1 hM.exp₁ hA1 hσA1 hAm1 hAm1card hdec1 hzN1 hτN1
      hz_e2 rel2 hσ2ne hc02 hz_e0 rel1 hσ0ne hτnot1
  obtain ⟨Am2, hAm2, hAm2card, hdec2⟩ :=
    loc5_inv_part z (e 2) M₂ hM.exp₂ hA2 hzN2 hσA2 rel2 hσ2ne hz_e2 hz2 hM.zinv₂
  have hτnot2 : ¬ ∀ a ∈ M₂ ⊓ Subgroup.centralizer (M₂ : Set G), e 0 * a = a * e 0 := by
    intro hc
    haveI : Nontrivial ↥Am2 :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hAm2card]; norm_num)
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥Am2)
    have hxA := (hAm2 x.1).mp x.2
    exact loc5_not_central rel3 hzz (M₂ ⊓ Subgroup.centralizer (M₂ : Set G))
      (fun a ha => loc5_conj_center he1N2 ha) hc (fun a ha => hM.exp₂ a ha.1)
      ⟨x.1, hxA.1, fun h => hx (Subtype.ext h), hxA.2⟩
  obtain ⟨Fix2, hFix2, hFix2card, hK2card⟩ :=
    loc5_tau_part z (e 2) (e 0) M₂ Am2 hM.exp₂ hA2 hσA2 hAm2 hAm2card hdec2 hzN2 hτN2
      hz_e0 rel1 hσ0ne hc20 hz_e2 rel2 hσ2ne hτnot2
  have hY1card : Nat.card ↥(M₁ ⊓ Subgroup.centralizer ({e 2} : Set G)) = 27 := by
    have := hcor.card_Pb₂
    omega
  have hY2card : Nat.card ↥(M₂ ⊓ Subgroup.centralizer ({e 0} : Set G)) = 27 := by
    have := hcor.card_Pb₁
    omega
  have hPbY2 : Pb = (M₁ ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔ Subgroup.zpowers (e 2) :=
    hcor.Pb_eq₂
  have hPbY1 : Pb = (M₂ ⊓ Subgroup.centralizer ({e 0} : Set G)) ⊔ Subgroup.zpowers (e 0) :=
    hcor.Pb_eq₁
  have hY1Pb : M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) ≤ Pb := by
    rw [hPbY2]; exact le_sup_left
  have hY2Pb : M₂ ⊓ Subgroup.centralizer ({e 0} : Set G) ≤ Pb := by
    rw [hPbY1]; exact le_sup_left
  have hZ1Pb : Subgroup.zpowers (e 2) ≤ Pb := by
    rw [hPbY2]; exact le_sup_right
  have hZ0Pb : Subgroup.zpowers (e 0) ≤ Pb := by
    rw [hPbY1]; exact le_sup_right
  have hY1ab : ∀ a ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G),
      ∀ b ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G), a * b = b * a := by
    obtain ⟨v, hvY, hvK⟩ : ∃ v ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G),
        v ∉ M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G) := by
      by_contra hcon
      push_neg at hcon
      have hle : M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) ≤
          M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G) := hcon
      have := Subgroup.card_le_of_le hle
      omega
    have hK1Y : M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G) ≤
        M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) := fun x hx => ⟨hx.1.1, hx.2⟩
    have hLle : (M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
        Subgroup.zpowers v ≤ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) :=
      sup_le hK1Y (Subgroup.zpowers_le.mpr hvY)
    have hvL : v ∈ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
        Subgroup.zpowers v := Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
    have hlt : Nat.card ↥(M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) <
        Nat.card ↥((M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
          Subgroup.zpowers v) := by
      refine lt_of_le_of_ne (Subgroup.card_le_of_le le_sup_left) ?_
      intro hc
      apply hvK
      have heq := Subgroup.eq_of_le_of_card_ge (le_sup_left : (M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ≤ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔ Subgroup.zpowers v) hc.symm.le
      rw [heq]
      exact hvL
    have hL27 : Nat.card ↥((M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
          Subgroup.zpowers v) = 27 := by
      have hdvd : Nat.card ↥((M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
          Subgroup.zpowers v) ∣ 27 := by
        rw [← hY1card]; exact Subgroup.card_dvd_of_le hLle
      have hle27 := Nat.le_of_dvd (by norm_num) hdvd
      have h9 := hlt
      rw [hK1card] at h9
      generalize Nat.card ↥((M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
          Subgroup.zpowers v) = n at *
      interval_cases n <;> first | rfl | omega | (norm_num at hdvd)
    have hLY : (M₁ ⊓ Subgroup.centralizer (M₁ : Set G) ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔
        Subgroup.zpowers v = M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hLle (by rw [hL27, hY1card])
    have hvcomm : ∀ y ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G), y * v = v * y := by
      have hsub : M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) ≤ Subgroup.centralizer ({v} : Set G) := by
        rw [← hLY]
        apply sup_le
        · intro k hk
          rw [Subgroup.mem_centralizer_singleton_iff]
          exact (Subgroup.mem_centralizer_iff.mp hk.1.2 v hvY.1).symm
        · apply Subgroup.zpowers_le.mpr
          exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.mp (hsub hy)
    intro a ha b hb
    have hsubA : M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) ≤ Subgroup.centralizer ({a} : Set G) := by
      rw [← hLY]
      apply sup_le
      · intro k hk
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hk.1.2 a ha.1).symm
      · apply Subgroup.zpowers_le.mpr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (hvcomm a ha).symm
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hsubA hb)).symm
  have hzb : ∀ b ∈ Subgroup.zpowers (e 2), ∀ d ∈ Subgroup.zpowers (e 2), b * d = d * b := by
    intro b hb d hd
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hd
    exact ((Commute.refl (e 2)).zpow_zpow i j).eq
  have hcommZ : ∀ c ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G),
      ∀ b ∈ Subgroup.zpowers (e 2), c * b = b * c := by
    intro c hc b hb
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hc' : Commute c (e 2) := Subgroup.mem_centralizer_singleton_iff.mp hc.2
    exact (hc'.zpow_right j).eq
  have hnorm2 : ∀ t ∈ Subgroup.zpowers (e 2), ∀ y ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G),
      t * y * t⁻¹ ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) := by
    intro t ht y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hc : Commute y (e 2) := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have e1 : (e 2) ^ k * y * ((e 2) ^ k)⁻¹ = y := by
      rw [← (hc.zpow_right k).eq]; group
    rw [e1]; exact hy
  have hPbab : ∀ x ∈ Pb, ∀ y ∈ Pb, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ (M₁ ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔ Subgroup.zpowers (e 2) := by
      rw [← hPbY2]; exact hx
    have hy' : y ∈ (M₁ ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔ Subgroup.zpowers (e 2) := by
      rw [← hPbY2]; exact hy
    obtain ⟨a, ha, b, hb, rfl⟩ := (loc5_mem_sup hnorm2).mp hx'
    obtain ⟨c, hc, d, hd, rfl⟩ := (loc5_mem_sup hnorm2).mp hy'
    have hac := hY1ab a ha c hc
    have hbd := hzb b hb d hd
    have hbc := (hcommZ c hc b hb).symm
    have had := hcommZ a ha d hd
    calc a * b * (c * d) = a * (b * c) * d := by group
      _ = a * (c * b) * d := by rw [hbc]
      _ = (a * c) * (b * d) := by group
      _ = (c * a) * (d * b) := by rw [hac, hbd]
      _ = c * (a * d) * b := by group
      _ = c * (d * a) * b := by rw [had]
      _ = c * d * (a * b) := by group
  have hPbexp : ∀ x ∈ Pb, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ (M₁ ⊓ Subgroup.centralizer ({e 2} : Set G)) ⊔ Subgroup.zpowers (e 2) := by
      rw [← hPbY2]; exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (loc5_mem_sup hnorm2).mp hx'
    have hcm : Commute a b := hPbab a (hY1Pb ha) b (hZ1Pb hb)
    have hb3 : b ^ 3 = 1 := by
      have h := orderOf_dvd_of_mem_zpowers hb
      rw [hord2] at h
      exact orderOf_dvd_iff_pow_eq_one.mp h
    rw [hcm.mul_pow, hM.exp₁ a ha.1, hb3, mul_one]
  have hzPb : ∀ x ∈ Pb, z * x * z⁻¹ ∈ Pb := fun x hx => hpb.compl.conj_mem z hzCP x hx
  obtain ⟨W, hW⟩ : ∃ W : Subgroup G, ∀ x, x ∈ W ↔ (x ∈ Pb ∧ z * x * z⁻¹ = x⁻¹) := by
    refine ⟨{ carrier := {x | x ∈ Pb ∧ z * x * z⁻¹ = x⁻¹}
              mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro x y ⟨hx, hzx⟩ ⟨hy, hzy⟩
      refine ⟨Pb.mul_mem hx hy, ?_⟩
      calc z * (x * y) * z⁻¹ = (z * x * z⁻¹) * (z * y * z⁻¹) := by group
        _ = x⁻¹ * y⁻¹ := by rw [hzx, hzy]
        _ = (x * y)⁻¹ := by
          rw [mul_inv_rev]; exact hPbab _ (Pb.inv_mem hx) _ (Pb.inv_mem hy)
    · exact ⟨Pb.one_mem, by group⟩
    · rintro x ⟨hx, hzx⟩
      refine ⟨Pb.inv_mem hx, ?_⟩
      calc z * x⁻¹ * z⁻¹ = (z * x * z⁻¹)⁻¹ := by group
        _ = x⁻¹⁻¹ := by rw [hzx]
  have hpbz : Pb ⊓ Subgroup.centralizer ({z} : Set G) = Psub e := hpb.inf_cent_z
  have hzzconj : ∀ x : G, z * (z * x * z⁻¹) * z⁻¹ = x := by
    intro x
    calc z * (z * x * z⁻¹) * z⁻¹ = (z * z) * x * (z * z)⁻¹ := by group
      _ = x := by rw [hz2]; group
  have hfixP : ∀ u ∈ Pb, z * u * z⁻¹ = u → u ∈ Psub e := by
    intro u hu hzu
    rw [← hpbz]
    refine Subgroup.mem_inf.mpr ⟨hu, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * z = (z * u * z⁻¹) * z := by rw [hzu]
      _ = z * u := by group
  have hzsq : ∀ x ∈ Pb, z * (x * (z * x * z⁻¹)) * z⁻¹ = x * (z * x * z⁻¹) := by
    intro x hx
    have hcx : (z * x * z⁻¹) * x = x * (z * x * z⁻¹) := hPbab _ (hzPb x hx) _ hx
    calc z * (x * (z * x * z⁻¹)) * z⁻¹ = (z * x * z⁻¹) * (z * (z * x * z⁻¹) * z⁻¹) := by group
      _ = (z * x * z⁻¹) * x := by rw [hzzconj x]
      _ = x * (z * x * z⁻¹) := hcx
  have hPWinf : ∀ p ∈ Psub e, p ∈ W → p = 1 := by
    intro p hp hpW
    have hpPb : p ∈ Pb := hpb.P_le hp
    have hzp : z * p * z⁻¹ = p⁻¹ := ((hW p).mp hpW).2
    have hpz : z * p * z⁻¹ = p := by
      have h1 : p * z = z * p := Subgroup.mem_centralizer_iff.mp hzCP p hp
      calc z * p * z⁻¹ = (p * z) * z⁻¹ := by rw [h1]
        _ = p := by group
    have hpp : p * p = 1 := by
      have h2 : p = p⁻¹ := hpz.symm.trans hzp
      exact mul_eq_one_iff_eq_inv.mpr h2
    have h3 := hPbexp p hpPb
    rw [pow_three, hpp, mul_one] at h3
    exact h3
  have hzY1 : ∀ y ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G),
      z * y * z⁻¹ ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨hv1.compl.conj_mem z hzC1 y hy.1, ?_⟩
    have hyc : Commute y (e 2) := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact loc5_conj_commute hz_e2 hyc.eq
  have hzY2 : ∀ y ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G),
      z * y * z⁻¹ ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G) := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨hv2.compl.conj_mem z hzC2 y hy.1, ?_⟩
    have hyc : Commute y (e 0) := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact loc5_conj_commute hz_e0 hyc.eq
  have hnorm0 : ∀ t ∈ Subgroup.zpowers (e 0), ∀ y ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G),
      t * y * t⁻¹ ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G) := by
    intro t ht y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hc : Commute y (e 0) := Subgroup.mem_centralizer_singleton_iff.mp hy.2
    have e1 : (e 0) ^ k * y * ((e 0) ^ k)⁻¹ = y := by
      rw [← (hc.zpow_right k).eq]; group
    rw [e1]; exact hy
  have hinter : Subgroup.zpowers (e 0) ⊓ Subgroup.zpowers (e 2) = ⊥ :=
    loc5_inter_bot rel1 hσ0ne rel2 hσ2ne hP
  have h2H : Subgroup.zpowers (e 2) ≤ H := Subgroup.zpowers_le.mpr he2H
  have h0H : Subgroup.zpowers (e 0) ≤ H := Subgroup.zpowers_le.mpr he0H
  have hYs1 : ∀ y ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G),
      y ∈ Subgroup.zpowers (e 2) → y = 1 := by
    intro y hy hyz
    have hy0 : y ∈ Subgroup.zpowers (e 0) := hM1H y hy.1 (h2H hyz)
    have hmem : y ∈ Subgroup.zpowers (e 0) ⊓ Subgroup.zpowers (e 2) :=
      Subgroup.mem_inf.mpr ⟨hy0, hyz⟩
    rw [hinter] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hYs2 : ∀ y ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G),
      y ∈ Subgroup.zpowers (e 0) → y = 1 := by
    intro y hy hyz
    have hy2 : y ∈ Subgroup.zpowers (e 2) := hM2H y hy.1 (h0H hyz)
    have hmem : y ∈ Subgroup.zpowers (e 0) ⊓ Subgroup.zpowers (e 2) :=
      Subgroup.mem_inf.mpr ⟨hyz, hy2⟩
    rw [hinter] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hWY1 : ∀ x ∈ W, x ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G) := by
    intro x hx
    obtain ⟨hxP, hzx⟩ := (hW x).mp hx
    exact loc5_le_of_inv hPbab hY1Pb hzY1 hnorm2 (le_of_eq hPbY2) hYs1 hZ1Pb hz_e2 rel2
      x hxP hzx
  have hWY2 : ∀ x ∈ W, x ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G) := by
    intro x hx
    obtain ⟨hxP, hzx⟩ := (hW x).mp hx
    exact loc5_le_of_inv hPbab hY2Pb hzY2 hnorm0 (le_of_eq hPbY1) hYs2 hZ0Pb hz_e0 rel1
      x hxP hzx
  have hY1W : ∀ x ∈ M₁ ⊓ Subgroup.centralizer ({e 2} : Set G), z * x * z⁻¹ = x⁻¹ → x ∈ W :=
    fun x hx hzx => (hW x).mpr ⟨hY1Pb hx, hzx⟩
  have hY2W : ∀ x ∈ M₂ ⊓ Subgroup.centralizer ({e 0} : Set G), z * x * z⁻¹ = x⁻¹ → x ∈ W :=
    fun x hx hzx => (hW x).mpr ⟨hY2Pb hx, hzx⟩
  have hdecW : ∀ x ∈ Pb, ∃ p ∈ Psub e, ∃ w ∈ W, x = p * w := by
    intro x hx
    obtain ⟨c, hcdef⟩ : ∃ c : G, c = z * x * z⁻¹ := ⟨_, rfl⟩
    have hcP : c ∈ Pb := by rw [hcdef]; exact hzPb x hx
    have hxc : c * x = x * c := by rw [hcdef]; exact hPbab _ (hzPb x hx) _ hx
    obtain ⟨u, hudef⟩ : ∃ u : G, u = x * c := ⟨_, rfl⟩
    obtain ⟨v, hvdef⟩ : ∃ v : G, v = x * c⁻¹ := ⟨_, rfl⟩
    have hu : u ∈ Pb := by rw [hudef]; exact Pb.mul_mem hx hcP
    have hv : v ∈ Pb := by rw [hvdef]; exact Pb.mul_mem hx (Pb.inv_mem hcP)
    have huz : z * u * z⁻¹ = u := by
      rw [hudef]
      calc z * (x * c) * z⁻¹ = (z * x * z⁻¹) * (z * c * z⁻¹) := by group
        _ = c * (z * c * z⁻¹) := by rw [← hcdef]
        _ = c * x := by rw [hcdef, hzzconj x]
        _ = x * c := hxc
    have hvz : z * v * z⁻¹ = v⁻¹ := by
      rw [hvdef]
      calc z * (x * c⁻¹) * z⁻¹ = (z * x * z⁻¹) * (z * c⁻¹ * z⁻¹) := by group
        _ = c * (z * c⁻¹ * z⁻¹) := by rw [← hcdef]
        _ = c * (z * c * z⁻¹)⁻¹ := by group
        _ = c * x⁻¹ := by rw [hcdef, hzzconj x]
        _ = (x * c⁻¹)⁻¹ := by group
    have huv : u * v = x * x := by
      rw [hudef, hvdef]
      calc x * c * (x * c⁻¹) = x * (c * x) * c⁻¹ := by group
        _ = x * (x * c) * c⁻¹ := by rw [hxc]
        _ = x * x := by group
    have hfour : (x * x) * (x * x) = x := by
      have h3 := hPbexp x hx
      calc (x * x) * (x * x) = x * x ^ 3 := by rw [pow_three]; simp only [mul_assoc]
        _ = x := by rw [h3, mul_one]
    have hprod : (u * u) * (v * v) = x := by
      have hcomm : u * v = v * u := hPbab u hu v hv
      calc (u * u) * (v * v) = u * (u * v) * v := by group
        _ = u * (v * u) * v := by rw [hcomm]
        _ = (u * v) * (u * v) := by group
        _ = (x * x) * (x * x) := by rw [huv]
        _ = x := hfour
    have hpz : z * (u * u) * z⁻¹ = u * u := by
      calc z * (u * u) * z⁻¹ = (z * u * z⁻¹) * (z * u * z⁻¹) := by group
        _ = u * u := by rw [huz]
    have hwz : z * (v * v) * z⁻¹ = (v * v)⁻¹ := by
      calc z * (v * v) * z⁻¹ = (z * v * z⁻¹) * (z * v * z⁻¹) := by group
        _ = v⁻¹ * v⁻¹ := by rw [hvz]
        _ = (v * v)⁻¹ := by group
    exact ⟨u * u, hfixP _ (Pb.mul_mem hu hu) hpz, v * v, (hW _).mpr ⟨Pb.mul_mem hv hv, hwz⟩,
      hprod.symm⟩
  have hPWsup : Psub e ⊔ W = Pb := by
    apply le_antisymm
    · exact sup_le hpb.P_le (fun x hx => ((hW x).mp hx).1)
    · intro x hx
      obtain ⟨p, hp, w, hw, rfl⟩ := hdecW x hx
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hp) (Subgroup.mem_sup_right hw)
  have hcardW1 : 81 ≤ Nat.card ↥(Psub e) * Nat.card ↥W := by
    have h1 := loc5_card_sup_le (S := Psub e) (T := W) (fun t ht s hs => by
      have htPb := ((hW t).mp ht).1
      have hsPb := hpb.P_le hs
      have e1 : t * s * t⁻¹ = s := by
        rw [hPbab _ htPb _ hsPb]; group
      rw [e1]; exact hs)
    rw [hPWsup, hPb] at h1
    exact h1
  have hcardW2 : Nat.card ↥W * Nat.card ↥(Psub e) ≤ 81 := by
    have hWPb : ∀ x ∈ W, x ∈ Pb := fun x hx => ((hW x).mp hx).1
    have hinj : Function.Injective (fun q : ↥W × ↥(Psub e) =>
        (⟨(q.1 : G) * (q.2 : G), Pb.mul_mem (hWPb _ q.1.2) (hpb.P_le q.2.2)⟩ : ↥Pb)) := by
      rintro ⟨⟨w₁, hw₁⟩, ⟨p₁, hp₁⟩⟩ ⟨⟨w₂, hw₂⟩, ⟨p₂, hp₂⟩⟩ h
      have h' : w₁ * p₁ = w₂ * p₂ := congrArg Subtype.val h
      have hmem : w₂⁻¹ * w₁ = p₂ * p₁⁻¹ := by
        calc w₂⁻¹ * w₁ = w₂⁻¹ * (w₁ * p₁) * p₁⁻¹ := by group
          _ = w₂⁻¹ * (w₂ * p₂) * p₁⁻¹ := by rw [h']
          _ = p₂ * p₁⁻¹ := by group
      have hWmem : w₂⁻¹ * w₁ ∈ W := W.mul_mem (W.inv_mem hw₂) hw₁
      have hPmem : p₂ * p₁⁻¹ ∈ Psub e := (Psub e).mul_mem hp₂ ((Psub e).inv_mem hp₁)
      have h1 : w₂⁻¹ * w₁ = 1 := hPWinf _ (by rw [hmem]; exact hPmem) hWmem
      have h2 : p₂ * p₁⁻¹ = 1 := by rw [← hmem]; exact h1
      have hw : w₁ = w₂ := (inv_mul_eq_one.mp h1).symm
      have hp : p₂ = p₁ := mul_inv_eq_one.mp h2
      subst hw
      subst hp
      rfl
    have h2 := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hPb] at h2
    exact h2
  have hWcard : Nat.card ↥W = 9 := by
    rw [hP] at hcardW1 hcardW2
    omega
  have hM12W : M₁ ⊓ M₂ ≤ W := by
    intro x hx
    have hxM1 : x ∈ M₁ := hx.1
    have hxM2 : x ∈ M₂ := hx.2
    have hxC2 : x ∈ Subgroup.centralizer ({e 2} : Set G) := hM2le hxM2
    have hxPb : x ∈ Pb := hY1Pb (Subgroup.mem_inf.mpr ⟨hxM1, hxC2⟩)
    have hcM1 : z * x * z⁻¹ ∈ M₁ := hv1.compl.conj_mem z hzC1 x hxM1
    have hcM2 : z * x * z⁻¹ ∈ M₂ := hv2.compl.conj_mem z hzC2 x hxM2
    have hxc : (z * x * z⁻¹) * x = x * (z * x * z⁻¹) := hPbab _ (hzPb x hxPb) _ hxPb
    have huPb : x * (z * x * z⁻¹) ∈ Pb := Pb.mul_mem hxPb (hzPb x hxPb)
    have huP : x * (z * x * z⁻¹) ∈ Psub e := hfixP _ huPb (hzsq x hxPb)
    have hu1 : x * (z * x * z⁻¹) ∈ M₁ := M₁.mul_mem hxM1 hcM1
    have hu2 : x * (z * x * z⁻¹) ∈ M₂ := M₂.mul_mem hxM2 hcM2
    have hu1' := hM1H _ hu1 (hPH huP)
    have hu2' := hM2H _ hu2 (hPH huP)
    have hu0 : x * (z * x * z⁻¹) = 1 := by
      have hmem : x * (z * x * z⁻¹) ∈ Subgroup.zpowers (e 0) ⊓ Subgroup.zpowers (e 2) :=
        Subgroup.mem_inf.mpr ⟨hu1', hu2'⟩
      rw [hinter] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hcinv : z * x * z⁻¹ = x⁻¹ := (mul_eq_one_iff_inv_eq.mp hu0).symm
    exact (hW x).mpr ⟨hxPb, hcinv⟩
  have hM12card : Nat.card ↥(M₁ ⊓ M₂) ≤ 9 := by
    rw [← hWcard]
    exact Subgroup.card_le_of_le hM12W
  have hℓ1 : W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) = Fix1 := by
    ext x
    rw [Subgroup.mem_inf, hFix1 x]
    constructor
    · rintro ⟨hxW, hxA⟩
      exact ⟨hxA, ((hW x).mp hxW).2, (Subgroup.mem_inf.mp (hWY1 x hxW)).2⟩
    · rintro ⟨hxA, hzx, hxC⟩
      exact ⟨hY1W x (Subgroup.mem_inf.mpr ⟨hxA.1, hxC⟩) hzx, hxA⟩
  have hℓ2 : W ⊓ (M₂ ⊓ Subgroup.centralizer (M₂ : Set G)) = Fix2 := by
    ext x
    rw [Subgroup.mem_inf, hFix2 x]
    constructor
    · rintro ⟨hxW, hxA⟩
      exact ⟨hxA, ((hW x).mp hxW).2, (Subgroup.mem_inf.mp (hWY2 x hxW)).2⟩
    · rintro ⟨hxA, hzx, hxC⟩
      exact ⟨hY2W x (Subgroup.mem_inf.mpr ⟨hxA.1, hxC⟩) hzx, hxA⟩
  have hcardℓ1 : Nat.card ↥(W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G))) = 3 := by
    rw [hℓ1]; exact hFix1card
  have hcardℓ2 : Nat.card ↥(W ⊓ (M₂ ⊓ Subgroup.centralizer (M₂ : Set G))) = 3 := by
    rw [hℓ2]; exact hFix2card
  have hM1card : Nat.card ↥M₁ = 243 := hM.card₁
  have hM2card : Nat.card ↥M₂ = 243 := hM.card₂
  have hsupcard : 6561 ≤ Nat.card ↥(M₁ ⊔ M₂) := by
    have hN := Subgroup.relIndex_mul_card (H := M₁) (K := M₁ ⊔ M₂)
    rw [inf_eq_left.mpr le_sup_left, hM1card] at hN
    have hN2 := Subgroup.relIndex_mul_card (H := M₁) (K := M₂)
    rw [hM2card] at hN2
    have hR0 : M₁.relIndex (M₁ ⊔ M₂) ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hN
      have : 0 < Nat.card ↥(M₁ ⊔ M₂) := Nat.card_pos
      omega
    have hle := Subgroup.relIndex_le_of_le_right (H := M₁) (le_sup_right : M₂ ≤ M₁ ⊔ M₂) hR0
    have hr27 : 27 ≤ M₁.relIndex M₂ := by
      by_contra hlt
      push_neg at hlt
      have := Nat.mul_le_mul (show M₁.relIndex M₂ ≤ 26 by omega) hM12card
      omega
    omega
  have hH2card : Nat.card ↥H₂ = 24 := by
    obtain ⟨φ⟩ := hone.iso_two
    rw [Nat.card_congr φ.toEquiv]
    have := Fintype.ofFinite (ZMod 3)
    rw [Matrix.card_SL_field]
    simp [ZMod.card]
  have hH1card : Nat.card ↥H₁ = 24 := by
    obtain ⟨φ⟩ := hone.iso_one
    rw [Nat.card_congr φ.toEquiv]
    have := Fintype.ofFinite (ZMod 3)
    rw [Matrix.card_SL_field]
    simp [ZMod.card]
  have hCe0 : Nat.card ↥(Subgroup.centralizer ({e 0} : Set G)) ≤ 5832 := by
    rw [← hv1.compl.sup_eq]
    have := loc5_card_sup_le (S := M₁) (T := H₂)
      (fun t ht s hs => hv1.compl.conj_mem t (hH2le ht) s hs)
    rw [hM1card, hH2card] at this
    omega
  have hCe2 : Nat.card ↥(Subgroup.centralizer ({e 2} : Set G)) ≤ 5832 := by
    rw [← hv2.compl.sup_eq]
    have := loc5_card_sup_le (S := M₂) (T := H₁)
      (fun t ht s hs => hv2.compl.conj_mem t (hH1le ht) s hs)
    rw [hM2card, hH1card] at this
    omega
  have hz2' : z ^ 2 = 1 := by rw [pow_two]; exact hz2
  have hzord : Nat.card ↥(Subgroup.zpowers z) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hz2' hzne
  have hz_e2inv : z * (e 2)⁻¹ = (e 2)⁻¹ * z := by
    calc z * (e 2)⁻¹ = (e 2)⁻¹ * (e 2 * z) * (e 2)⁻¹ := by group
      _ = (e 2)⁻¹ * (z * e 2) * (e 2)⁻¹ := by rw [hz_e2]
      _ = (e 2)⁻¹ * z := by group
  have hzCnp : z ∈ Subgroup.centralizer ({e 0 * e 2} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc z * (e 0 * e 2) = (z * e 0) * e 2 := by group
        _ = (e 0 * z) * e 2 := by rw [hz_e0]
        _ = e 0 * (z * e 2) := by group
        _ = e 0 * (e 2 * z) := by rw [hz_e2]
        _ = e 0 * e 2 * z := by group)
  have hzCnm : z ∈ Subgroup.centralizer ({e 0 * (e 2)⁻¹} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by
      calc z * (e 0 * (e 2)⁻¹) = (z * e 0) * (e 2)⁻¹ := by group
        _ = (e 0 * z) * (e 2)⁻¹ := by rw [hz_e0]
        _ = e 0 * (z * (e 2)⁻¹) := by group
        _ = e 0 * ((e 2)⁻¹ * z) := by rw [hz_e2inv]
        _ = e 0 * (e 2)⁻¹ * z := by group)
  have hCnp : Nat.card ↥(Subgroup.centralizer ({e 0 * e 2} : Set G)) ≤ 1458 := by
    have hsupeq : Np ⊔ Subgroup.zpowers z = Subgroup.centralizer ({e 0 * e 2} : Set G) :=
      hnp.compl.sup_eq
    rw [← hsupeq]
    have hzsub : Subgroup.zpowers z ≤ Subgroup.centralizer ({e 0 * e 2} : Set G) :=
      Subgroup.zpowers_le.mpr hzCnp
    have := loc5_card_sup_le (S := Np) (T := Subgroup.zpowers z)
      (fun t ht s hs => hnp.compl.conj_mem t (hzsub ht) s hs)
    rw [hzord] at this
    have hNp : Nat.card ↥Np ≤ 729 := by
      have := hnp.card_le
      norm_num at this
      exact this
    have := Nat.mul_le_mul hNp (le_refl 2)
    omega
  have hCnm : Nat.card ↥(Subgroup.centralizer ({e 0 * (e 2)⁻¹} : Set G)) ≤ 1458 := by
    have hsupeq : Nm ⊔ Subgroup.zpowers z = Subgroup.centralizer ({e 0 * (e 2)⁻¹} : Set G) :=
      hnm.compl.sup_eq
    rw [← hsupeq]
    have hzsub : Subgroup.zpowers z ≤ Subgroup.centralizer ({e 0 * (e 2)⁻¹} : Set G) :=
      Subgroup.zpowers_le.mpr hzCnm
    have := loc5_card_sup_le (S := Nm) (T := Subgroup.zpowers z)
      (fun t ht s hs => hnm.compl.conj_mem t (hzsub ht) s hs)
    rw [hzord] at this
    have hNm : Nat.card ↥Nm ≤ 729 := by
      have := hnm.card_le
      norm_num at this
      exact this
    have := Nat.mul_le_mul hNm (le_refl 2)
    omega
  have hPbound : ∀ p ∈ Psub e, p ≠ 1 →
      Nat.card ↥(Subgroup.centralizer ({p} : Set G)) ≤ 5832 := by
    intro p hp hp1
    obtain ⟨q, hq, k, hkq⟩ := loc5_P_cases hc02 rel1 hσ0ne rel2 hσ2ne hp hp1
    refine le_trans (Subgroup.card_le_of_le (loc5_cent_le hkq)) ?_
    rcases hq with rfl | rfl | rfl | rfl
    · exact hCe0
    · exact hCe2
    · exact le_trans hCnp (by norm_num)
    · exact le_trans hCnm (by norm_num)
  have hℓne : W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) ≠
      W ⊓ (M₂ ⊓ Subgroup.centralizer (M₂ : Set G)) := by
    intro hEq
    haveI : Nontrivial ↥(W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G))) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hcardℓ1]; norm_num)
    obtain ⟨y, hy⟩ := exists_ne (1 : ↥(W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G))))
    have hyI := Subgroup.mem_inf.mp y.2
    have hxW : (y : G) ∈ W := hyI.1
    have hxA1 : (y : G) ∈ M₁ ⊓ Subgroup.centralizer (M₁ : Set G) := hyI.2
    have hx1 : (y : G) ≠ 1 := fun h => hy (Subtype.ext h)
    generalize (y : G) = x at hxW hxA1 hx1
    have hxL2 : x ∈ W ⊓ (M₂ ⊓ Subgroup.centralizer (M₂ : Set G)) := by
      rw [← hEq]; exact Subgroup.mem_inf.mpr ⟨hxW, hxA1⟩
    have hxA2 : x ∈ M₂ ⊓ Subgroup.centralizer (M₂ : Set G) := (Subgroup.mem_inf.mp hxL2).2
    have hzx : z * x * z⁻¹ = x⁻¹ := ((hW x).mp hxW).2
    have hxPb : x ∈ Pb := ((hW x).mp hxW).1
    have hx3 : x ^ 3 = 1 := hM.exp₁ x hxA1.1
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hxord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have htxL : e 4 * x * (e 4)⁻¹ ∈ W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) := by
      refine Subgroup.mem_inf.mpr ⟨(hW _).mpr ⟨hPbt x hxPb, ?_⟩, loc5_conj_center ht_N1 hxA1⟩
      calc z * (e 4 * x * (e 4)⁻¹) * z⁻¹ = (z * e 4) * x * (z * e 4)⁻¹ := by group
        _ = (e 4 * z) * x * (e 4 * z)⁻¹ := by rw [hzt]
        _ = e 4 * (z * x * z⁻¹) * (e 4)⁻¹ := by group
        _ = e 4 * x⁻¹ * (e 4)⁻¹ := by rw [hzx]
        _ = (e 4 * x * (e 4)⁻¹)⁻¹ := by group
    have hxL : x ∈ W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) :=
      Subgroup.mem_inf.mpr ⟨hxW, hxA1⟩
    have hLz : W ⊓ (M₁ ⊓ Subgroup.centralizer (M₁ : Set G)) = Subgroup.zpowers x :=
      (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxL)
        (by rw [Nat.card_zpowers, hxord, hcardℓ1])).symm
    have hmemz : e 4 * x * (e 4)⁻¹ ∈ Subgroup.zpowers x := by
      rw [← hLz]; exact htxL
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmemz
    obtain ⟨n, hn3, hnx⟩ := loc5_zpow_red hxord k
    rw [hnx] at hk
    have hfinal : ∀ u : G, u * u = 1 → u ≠ 1 → u * x * u⁻¹ = x → False := by
      intro u hu2 hu1 hux
      have hu_ord : orderOf u = 2 := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hu2) hu1
      obtain ⟨g, hg⟩ := isConj_iff.mp (hO u hu_ord)
      have hxu : x * u = u * x := by
        calc x * u = (u * x * u⁻¹) * u := by rw [hux]
          _ = u * x := by group
      have hgu : g⁻¹ * u * g = z := by
        calc g⁻¹ * u * g = g⁻¹ * (g * z * g⁻¹) * g := by rw [hg]
          _ = z := by group
      have hxc : (g⁻¹ * x * g) * z = z * (g⁻¹ * x * g) := by
        calc (g⁻¹ * x * g) * z = g⁻¹ * x * (g * z * g⁻¹) * g := by group
          _ = g⁻¹ * x * u * g := by rw [hg]
          _ = g⁻¹ * (x * u) * g := by group
          _ = g⁻¹ * (u * x) * g := by rw [hxu]
          _ = (g⁻¹ * u * g) * (g⁻¹ * x * g) := by group
          _ = z * (g⁻¹ * x * g) := by rw [hgu]
      have hxH : g⁻¹ * x * g ∈ H := hCz _ hxc
      have hx'3 : (g⁻¹ * x * g) ^ 3 = 1 := by
        have h := conj_pow (a := g⁻¹) (b := x) (i := 3)
        rw [inv_inv] at h
        rw [h, hx3, mul_one]
        group
      have hx'1 : g⁻¹ * x * g ≠ 1 := by
        intro h
        apply hx1
        calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
          _ = 1 := by rw [h]; group
      obtain ⟨c0, _, hc0⟩ := hF.order3 _ hxH hx'3 hx'1
      have hp1 : c0 * (g⁻¹ * x * g) * c0⁻¹ ≠ 1 := by
        intro h
        apply hx'1
        calc g⁻¹ * x * g = c0⁻¹ * (c0 * (g⁻¹ * x * g) * c0⁻¹) * c0 := by group
          _ = 1 := by rw [h]; group
      have hcp := loc5_card_centralizer_conj (c0 * g⁻¹) x
      have hpeq : (c0 * g⁻¹) * x * (c0 * g⁻¹)⁻¹ = c0 * (g⁻¹ * x * g) * c0⁻¹ := by group
      rw [hpeq] at hcp
      have hbound := hPbound _ hc0 hp1
      rw [hcp] at hbound
      have hsubC : M₁ ⊔ M₂ ≤ Subgroup.centralizer ({x} : Set G) := by
        apply sup_le
        · intro m hm
          exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxA1.2 m hm)
        · intro m hm
          exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hxA2.2 m hm)
      have hle := Subgroup.card_le_of_le hsubC
      omega
    interval_cases n
    ·
      rw [pow_zero] at hk
      apply hx1
      calc x = (e 4)⁻¹ * (e 4 * x * (e 4)⁻¹) * e 4 := by group
        _ = 1 := by rw [← hk]; group
    ·
      rw [pow_one] at hk
      exact hfinal (e 4) rel12 ht_ne_one hk.symm
    ·
      have hx2 : x ^ 2 * x = 1 := by rw [← pow_succ]; exact hx3
      have hx2i : x ^ 2 = x⁻¹ := eq_inv_of_mul_eq_one_left hx2
      have hux2 : e 4 * x * (e 4)⁻¹ = x⁻¹ := by rw [← hk]; exact hx2i
      have hu1z : e 4 * z ≠ 1 := by
        intro h
        apply ht_ne_z
        calc e 4 = e 4 * (z * z) := by rw [hz2, mul_one]
          _ = e 4 * z * z := by group
          _ = z := by rw [h, one_mul]
      apply hfinal (e 4 * z) htz_inv hu1z
      calc e 4 * z * x * (e 4 * z)⁻¹ = e 4 * (z * x * z⁻¹) * (e 4)⁻¹ := by group
        _ = e 4 * x⁻¹ * (e 4)⁻¹ := by rw [hzx]
        _ = (e 4 * x * (e 4)⁻¹)⁻¹ := by group
        _ = x := by rw [hux2, inv_inv]
  refine ⟨W, ?_⟩
  exact
    { mstruct := hM
      card_Pb := hPb
      W_le₁ := fun x hx => hWY1 x hx
      W_le₂ := fun x hx => hWY2 x hx
      card_W := hWcard
      W_inv := fun w hw => ((hW w).mp hw).2
      W_eq₁ := hY1W
      W_eq₂ := hY2W
      card_ℓ₁ := hcardℓ1
      card_ℓ₂ := hcardℓ2
      ℓ_ne := hℓne }

end CFSG.GH74.QTGen4.Recog.G23.P7
