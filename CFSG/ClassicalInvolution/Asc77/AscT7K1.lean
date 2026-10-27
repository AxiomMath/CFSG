module

public import CFSG.ClassicalInvolution.Asc77.AscT7EFrame
public import CFSG.ClassicalInvolution.Asc77.WP3LayerSec

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Balance.Bootstrap

namespace T7K

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {z u e g : G}

theorem e_mem_inf (hd : Hyp23bData Ω K K' W z u e g) :
    e ∈ W ⊓ centerIn (Subgroup.normalizer (W : Set G)) := by
  rw [← hd.he]
  exact Subgroup.subset_closure rfl

theorem comm_e (hd : Hyp23bData Ω K K' W z u e g) {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) : x * e = e * x :=
  T7E.Frame4.commutes_of_mem_centerIn (e_mem_inf hd).2 hx

theorem comm_e_of_mem_W (hd : Hyp23bData Ω K K' W z u e g) {x : G} (hx : x ∈ W) :
    x * e = e * x :=
  comm_e hd (Subgroup.le_normalizer hx)


theorem g_mem_normalizer (hd : Hyp23bData Ω K K' W z u e g) :
    g ∈ Subgroup.normalizer (W : Set G) :=
  Thompson.MGrp_le_normalizer Ω W hd.hg

theorem sup_le_centralizer (hs : Hyp23Setting p f Ω K K' z) :
    K ⊔ K' ≤ Subgroup.centralizer ({z} : Set G) := by
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  refine sup_le (fun w hw => ?_) (fun w hw => ?_)
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hs.hz.commute_of_mem hw).symm
  · exact Subgroup.mem_centralizer_singleton_iff.mpr (hzK'.commute_of_mem hw).symm

theorem exists_sylow_D (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∃ R R' : Subgroup G, IsSylow2In R K ∧ IsSylow2In R' K' ∧ Commutes R R' ∧
      R ≤ Subgroup.normalizer (W : Set G) ∧ R' ≤ Subgroup.normalizer (W : Set G) := by
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  obtain ⟨S, R, R', hWS, hR, hR', hRS, hR'S⟩ := T7D.exists_sylow_frame hs hd.hW hd.hzW
  have hRD := Thompson.mem_DSet_of_le_sylow hp hq hΩ hd.hW hWS
    (mem_RSet_of_isSylow2In hst.mem hR) hRS
  have hR'D := Thompson.mem_DSet_of_le_sylow hp hq hΩ hd.hW hWS
    (mem_RSet_of_isSylow2In hs.hK'.1 hR') hR'S
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  have h2 : IsPGroup 2 ↥(R ⊔ R') := S.isPGroup'.to_le (sup_le hRS hR'S)
  exact ⟨R, R', hR, hR', hΩ.commutes_of_twin_of_isPGroup hst.mem hs.hK'.1 hs.hne.symm hs.hz hzK'
    hR.1 hR'.1 h2, hRD.2, hR'D.2⟩


theorem e_not_mem_sup (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    e ∉ K ⊔ K' := by
  intro he
  have hst := hs.stand
  have hp : p ≠ 2 := hst.odd
  have hq : 5 ≤ p ^ f := hst.five
  have hΩ : HypOmegaMod p f Ω := hst.hyp
  have hK : K ∈ Ω := hst.mem
  have hK'Ω : K' ∈ Ω := hs.hK'.1
  have hzK' : IsUniqueInvolution K' z := isUniqueInvolution_of_mem_twinSet hs.hz hs.hK'
  obtain ⟨R, R', hR, hR', hc, hRN, hR'N⟩ := exists_sylow_D hs hd
  have hQ : IsSylow2In (R ⊔ R') (K ⊔ K') :=
    T7A.isSylow2In_sup_of_twin hp hΩ hK hK'Ω hs.hne hs.hz hzK' hR hR' hc
  have he2 : e * e = 1 := hd.he2
  have hle : R ⊔ R' ≤ Subgroup.centralizer ({e} : Set G) := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hRN hr))
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e hd (hR'N hr))
  have hcz : Subgroup.centralizer (Subgroup.zpowers e : Set G) = Subgroup.centralizer {e} := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have heN : R ⊔ R' ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) := by
    refine hle.trans ?_
    rw [← hcz]
    exact Subgroup.centralizer_le_normalizer _
  have hpe : IsPGroup 2 (Subgroup.zpowers e) := isPGroup_zpowers_of_mul_self_eq_one he2 hd.he1
  have hpg : IsPGroup 2 ↥((R ⊔ R') ⊔ Subgroup.zpowers e) := hQ.2.1.to_sup_of_normal_right' hpe heN
  have heQ : e ∈ R ⊔ R' := by
    have := hQ.2.2 _ (sup_le hQ.1 (Subgroup.zpowers_le.mpr he)) hpg le_sup_left
    rw [← this]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
  obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commutes hc heQ
  have hbr : ∀ r ∈ R, b * r = r * b := fun r hr => (hc r hr b hb).symm
  have hac : ∀ r ∈ R, a * r = r * a := by
    intro r hr
    have h1 : r * e = e * r := comm_e hd (hRN hr)
    rw [hab] at h1
    have h2 : r * a * b = a * r * b := by
      calc r * a * b = r * (a * b) := by group
        _ = (a * b) * r := h1
        _ = a * (b * r) := by group
        _ = a * (r * b) := by rw [hbr r hr]
        _ = a * r * b := by group
    exact (mul_right_cancel h2).symm
  have hbc : ∀ r ∈ R', b * r = r * b := by
    intro r hr
    have h1 : r * e = e * r := comm_e hd (hR'N hr)
    rw [hab] at h1
    have har : a * r = r * a := hc a ha r hr
    have h2 : a * (r * b) = a * (b * r) := by
      calc a * (r * b) = (a * r) * b := by group
        _ = (r * a) * b := by rw [har]
        _ = r * (a * b) := by group
        _ = (a * b) * r := h1
        _ = a * (b * r) := by group
    exact (mul_left_cancel h2).symm
  have hapg : IsPGroup 2 (Subgroup.zpowers a) := hR.2.1.to_le (Subgroup.zpowers_le.mpr ha)
  have hbpg : IsPGroup 2 (Subgroup.zpowers b) := hR'.2.1.to_le (Subgroup.zpowers_le.mpr hb)
  have haK : a ∈ K := hR.1 ha
  have hbK' : b ∈ K' := hR'.1 hb
  have hatq : a ∈ trivialOnQuot K := (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hapg hK).mpr
    ⟨R, hR, fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hac r hr).symm⟩
  have hbtq : b ∈ trivialOnQuot K' := (mem_trivialOnQuot_iff_exists_sylow hp hq hΩ hbpg hK'Ω).mpr
    ⟨R', hR', fun r hr => Subgroup.mem_centralizer_singleton_iff.mpr (hbc r hr).symm⟩
  have ha1z : a = 1 ∨ a = z := hΩ.center_two hp hq hK hs.hz a haK hapg
    (fun y hy => (mem_trivialOnQuot_iff.mp hatq).2 y hy)
  have hb1z : b = 1 ∨ b = z := hΩ.center_two hp hq hK'Ω hzK' b hbK' hbpg
    (fun y hy => (mem_trivialOnQuot_iff.mp hbtq).2 y hy)
  have hez : e = z := by
    have hz2 : z * z = 1 := hs.hz.sq
    rcases ha1z with h1 | h1 <;> rcases hb1z with h2 | h2
    · exact absurd (by rw [hab, h1, h2]; simp) hd.he1
    · rw [hab, h1, h2]; simp
    · rw [hab, h1, h2]; simp
    · exact absurd (by rw [hab, h1, h2]; exact hz2) hd.he1
  have hgz : g * z * g⁻¹ = z := by
    have := comm_e hd (g_mem_normalizer hd)
    rw [hez] at this
    calc g * z * g⁻¹ = (z * g) * g⁻¹ := by rw [this]
      _ = z := by group
  have h3 := hd.hgt
  rw [hgz, hez] at h3
  have : u = 1 := by
    have h4 : u * z = 1 * z := by rw [one_mul]; exact h3.symm
    exact mul_right_cancel h4
  exact hd.hu1 this


theorem comm_uz (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    u * z = z * u :=
  Subgroup.mem_centralizer_singleton_iff.mp (sup_le_centralizer hs hd.hu)

theorem comm_gen (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    ∀ a ∈ ({u * e, u, z} : Set G), ∀ b ∈ ({u * e, u, z} : Set G), a * b = b * a := by
  have c1 : Commute u e := comm_e_of_mem_W hd hd.huW
  have c2 : Commute u z := comm_uz hs hd
  have c3 : Commute z e := comm_e_of_mem_W hd hd.hzW
  have c4 : Commute (u * e) u := Commute.mul_left (Commute.refl u) c1.symm
  have c5 : Commute (u * e) z := Commute.mul_left c2 c3.symm
  intro a ha b hb
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
  · exact (Commute.refl _).eq
  · exact c4.eq
  · exact c5.eq
  · exact c4.symm.eq
  · exact (Commute.refl _).eq
  · exact c2.eq
  · exact c5.symm.eq
  · exact c2.symm.eq
  · exact (Commute.refl _).eq


theorem B_isElemAbelian (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    IsElemAbelian 2 (Subgroup.closure ({u * e, u, z} : Set G)) := by
  have hcomm := T7A.commutes_closure (comm_gen hs hd)
  have hue : u * e = e * u := comm_e_of_mem_W hd hd.huW
  have hsq : ∀ a ∈ ({u * e, u, z} : Set G), a * a = 1 := by
    intro a ha
    rcases ha with rfl | rfl | rfl
    · calc u * e * (u * e) = u * (e * u) * e := by group
        _ = u * (u * e) * e := by rw [← hue]
        _ = (u * u) * (e * e) := by group
        _ = 1 := by rw [hd.hu2, hd.he2]; group
    · exact hd.hu2
    · exact hs.hz.sq
  refine ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩
  rw [pow_two]
  exact T7A.sq_closure hsq (comm_gen hs hd) x hx

theorem B_natCard (hs : Hyp23Setting p f Ω K K' z) (hd : Hyp23bData Ω K K' W z u e g) :
    Nat.card ↥(Subgroup.closure ({u * e, u, z} : Set G)) = 8 := by
  have hD := T7A.isElemAbelian2_closure_pair hd.hu2 hs.hz.sq hd.hu1 hs.hz.ne_one hd.huz
    (comm_uz hs hd)
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact hd.he2) hd.he1
  have hsub : ∀ x ∈ ({u * e, u, z} : Set G), x ∈ Subgroup.closure ({u, z} : Set G) ⊔
      Subgroup.zpowers e := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
    · exact Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hcl : Subgroup.closure ({u * e, u, z} : Set G) =
      Subgroup.closure ({u, z} : Set G) ⊔ Subgroup.zpowers e := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).mpr hsub
    · refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.closure_le]
        intro x hx
        rcases hx with rfl | rfl
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
      · have : e = u⁻¹ * (u * e) := by group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
          (Subgroup.subset_closure (by simp))
  have hcomm : Commutes (Subgroup.closure ({u, z} : Set G)) (Subgroup.zpowers e) := by
    have hle : Subgroup.closure ({u, z} : Set G) ≤ Subgroup.centralizer ({e} : Set G) := by
      rw [Subgroup.closure_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e_of_mem_W hd hd.huW)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (comm_e_of_mem_W hd hd.hzW)
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
    exact (this.zpow_right i).eq
  have hinf : Subgroup.closure ({u, z} : Set G) ⊓ Subgroup.zpowers e = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rcases T7A.eq_one_or_eq_of_mem_zpowers he2 hx.2 with h1 | h1
    · rw [h1]
      exact Subgroup.one_mem _
    · exfalso
      refine e_not_mem_sup hs hd ?_
      have hle : Subgroup.closure ({u, z} : Set G) ≤ K ⊔ K' := by
        rw [Subgroup.closure_le]
        intro y hy
        rcases hy with rfl | rfl
        · exact hd.hu
        · exact Subgroup.mem_sup_left hs.hz.mem
      rw [← h1]
      exact hle hx.1
  have hN := T7A.card_sup_mul_card_inf (T7A.le_normalizer_of_commutes hcomm)
  rw [hinf, Subgroup.card_bot, Nat.card_zpowers, he2, hD.1, mul_one] at hN
  rw [hcl, sup_comm, hN]
  norm_num

end T7K
