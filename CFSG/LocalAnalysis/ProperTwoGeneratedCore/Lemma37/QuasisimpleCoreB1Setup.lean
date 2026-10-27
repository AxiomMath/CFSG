module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1SetupMixed
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.QuasisimpleCoreB1SetupPsi

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore

open CFSG.Open CFSG.ProperTwoGeneratedCore.Assembly

variable {J : Type} [Group J] [Finite J] {Q : Sylow 2 J} {B : Subgroup J} {u : J}

namespace CaseB1

variable {T : Sylow 2 (quasiNormalizer u)} {L : Subgroup (QuasiQuotient u)} {M : ℕ}

theorem two_le_pRank (hb : CaseB1 Q B T L M) : 2 ≤ CFSG.Open.pRank 2 (partCSylow T) := by
  have h := hb.setting
  have hc := hb.partC
  obtain ⟨q, hq, -, -, hqq, -, -, -⟩ := quaternion_exists_pair hc.quaternion.some hc.mem_left
    hc.order
  have hu := hc.self_mem
  have hne : ∀ c ∈ Subgroup.center J, q * u ≠ c := by
    intro c hcZ hqu
    have hqP : q ∈ partCRight T L := by
      rw [show q = c * u⁻¹ by rw [← hqu]; group]
      exact (partCRight T L).mul_mem (hb.center_le_partCRight hcZ)
        ((partCRight T L).inv_mem hu)
    rcases hc.mem_inf q hq hqP with rfl | rfl
    · exact h.centralElt_ne_one (by rw [← hqq, one_mul])
    · exact h.centralElt_ne_one (h.centralElt_mul_self.symm.trans hqq).symm
  have hsq : q * u * (q * u) = 1 := by
    calc q * u * (q * u) = q * (u * q) * u := by group
      _ = q * (q * u) * u := by rw [hc.commute q hq u hu]
      _ = q * q * (u * u) := by group
      _ = 1 := by rw [hqq, hc.sq, h.centralElt_mul_self]
  exact two_le_pRank_of_commuting_involutions ((partCSylow T).mul_mem (hc.left_le hq)
    (hc.right_le hu)) (hc.left_le hc.mem_left)
    (orderOf_eq_prime (by rw [pow_two]; exact hsq) (hne 1 (one_mem _)))
    h.orderOf_centralElt (hne _ h.centralElt_mem_center) (h.commute_centralElt _)

theorem mem_normalizer_of_mk_mem (hb : CaseB1 Q B T L M) {g : J}
    (hg : (g : J ⧸ Subgroup.center J) ∈
      Subgroup.normalizer (b1S T : Set (J ⧸ Subgroup.center J))) :
    g ∈ Subgroup.normalizer (partCSylow T : Set J) := by
  have hcomap : (b1S T).comap (QuotientGroup.mk' (Subgroup.center J)) = partCSylow T :=
    Subgroup.comap_map_eq_self (by
      rw [QuotientGroup.ker_mk']
      exact hb.center_le_partCSylow)
  rw [← hcomap, ← Subgroup.comap_normalizer_eq_of_surjective _ (QuotientGroup.mk'_surjective _)]
  exact hg

theorem normalizer_le (hb : CaseB1 Q B T L M) :
    Subgroup.normalizer (b1S T : Set (J ⧸ Subgroup.center J)) ≤ b1Bar B := by
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  exact (hb.setting.mk_mem_map_iff g).mpr (hb.setting.normalizer_le hb.partCSylow_le
    hb.two_le_pRank (hb.mem_normalizer_of_mk_mem hy))

theorem normalizer_le_centralizer (hb : CaseB1 Q B T L M) :
    Subgroup.normalizer (b1S T : Set (J ⧸ Subgroup.center J)) ≤
      Subgroup.centralizer {(u : J ⧸ Subgroup.center J)} := by
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact ((hb.setting.mem_normalizer_zpowers_iff_commute hb.partC.sq).mp
    (hb.normalizer_partCSylow_le (hb.mem_normalizer_of_mk_mem hy))).eq

theorem commute_of_mem_X_of_mem_S (hb : CaseB1 Q B T L M) {x s : J ⧸ Subgroup.center J}
    (hx : x ∈ b1X T L) (hs : s ∈ b1S T) : Commute x s := by
  have h2 : (hb.psi ⟨x, hb.X_le_S hx⟩).2 = 1 := (hb.mem_X_iff_psi _).mp hx
  have key : hb.psi (⟨x, hb.X_le_S hx⟩ * ⟨s, hs⟩) = hb.psi (⟨s, hs⟩ * ⟨x, hb.X_le_S hx⟩) := by
    rw [map_mul, map_mul]
    refine Prod.ext (dihedralGroup_two_mul_comm _ _) ?_
    rw [Prod.snd_mul, Prod.snd_mul, h2, one_mul, mul_one]
  exact congrArg Subtype.val (hb.psi.injective key)

theorem subgroupOf_X_le_center (hb : CaseB1 Q B T L M) :
    (b1X T L).subgroupOf (b1S T) ≤ Subgroup.center (b1S T) := fun _ hx =>
  Subgroup.mem_center_iff.mpr fun s =>
    Subtype.ext (hb.commute_of_mem_X_of_mem_S (Subgroup.mem_subgroupOf.mp hx) s.2).eq.symm

theorem centralSylow (hb : CaseB1 Q B T L M) {x : J ⧸ Subgroup.center J} (hx : x ∈ b1X T L) :
    CFSG.ShultStronglyClosedTI.InvolutionPointCentralSylow x :=
  ⟨hb.sylow, hb.X_le_S hx, hb.subgroupOf_X_le_center (Subgroup.mem_subgroupOf.mpr hx)⟩

theorem mk_mem_center (hb : CaseB1 Q B T L M) :
    (⟨(u : J ⧸ Subgroup.center J), hb.mk_mem_S⟩ : b1S T) ∈ Subgroup.center (b1S T) :=
  Subgroup.mem_center_iff.mpr fun s => Subtype.ext (hb.commute_mk_of_mem_S s.2).eq

theorem psi_mk (hb : CaseB1 Q B T L M) :
    hb.psi ⟨(u : J ⧸ Subgroup.center J), hb.mk_mem_S⟩ =
      (1, DihedralGroup.r ((M / 2 : ℕ) : ZMod M)) := by
  have h1 : (hb.psi ⟨(u : J ⧸ Subgroup.center J), hb.mk_mem_S⟩).1 = 1 :=
    (hb.mem_D_iff_psi _).mp hb.mk_mem_D
  refine Prod.ext h1 (dihedralGroup_eq_of_mem_center hb.even (by have := hb.four_le; omega) ?_ ?_)
  · refine Subgroup.mem_center_iff.mpr fun b => ?_
    have key := congrArg (fun s => (hb.psi s).2)
      (Subgroup.mem_center_iff.mp hb.mk_mem_center (hb.psi.symm (1, b)))
    simpa only [map_mul, MulEquiv.apply_symm_apply, Prod.snd_mul] using key
  · intro h2
    exact hb.mk_ne_one (congrArg Subtype.val ((MulEquiv.map_eq_one_iff hb.psi).mp
      (Prod.ext h1 h2)))

theorem eq_mk_or_exists_sr (hb : CaseB1 Q B T L M) {d : J ⧸ Subgroup.center J}
    (hd : d ∈ b1D T L) (hd2 : orderOf d = 2) :
    d = (u : J ⧸ Subgroup.center J) ∨
      ∃ i : ZMod M, hb.psi ⟨d, hb.D_le_S hd⟩ = (1, DihedralGroup.sr i) := by
  have : NeZero M := ⟨hb.ne_zero⟩
  have h1 : (hb.psi ⟨d, hb.D_le_S hd⟩).1 = 1 := (hb.mem_D_iff_psi _).mp hd
  have hss : hb.psi ⟨d, hb.D_le_S hd⟩ * hb.psi ⟨d, hb.D_le_S hd⟩ = 1 := by
    rw [← map_mul, MulEquiv.map_eq_one_iff]
    exact Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, ← hd2, pow_orderOf_eq_one]; rfl)
  rcases hψ : (hb.psi ⟨d, hb.D_le_S hd⟩).2 with i | i
  · left
    have hr : DihedralGroup.r i * DihedralGroup.r i = 1 := by
      rw [← hψ, ← Prod.snd_mul, hss, Prod.snd_one]
    have hr1 : DihedralGroup.r i ≠ 1 := by
      intro h
      rw [h] at hψ
      have hd1 : d = 1 := congrArg Subtype.val ((MulEquiv.map_eq_one_iff hb.psi).mp
        (Prod.ext h1 hψ))
      rw [hd1, orderOf_one] at hd2
      exact absurd hd2 (by decide)
    rw [dihedralGroup_r_eq_half hb.even hr hr1] at hψ
    exact congrArg Subtype.val (hb.psi.injective ((Prod.ext h1 hψ).trans hb.psi_mk.symm))
  · exact Or.inr ⟨i, Prod.ext h1 hψ⟩

theorem isMixedInv_psi_symm_iff (hb : CaseB1 Q B T L M) (a : DihedralGroup 2)
    (b : DihedralGroup M) :
    IsMixedInv ((hb.psi.symm (a, b) : b1S T) : J ⧸ Subgroup.center J) ↔
      a ≠ 1 ∧ orderOf b = 2 := by
  have hx := hb.psi_symm_mem_X a
  have hd := hb.psi_symm_mem_D b
  have hx1 : ((hb.psi.symm (a, 1) : b1S T) : J ⧸ Subgroup.center J) = 1 ↔ a = 1 := by
    rw [OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, Prod.mk_eq_one]
    exact ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩
  have hdo : orderOf ((hb.psi.symm (1, b) : b1S T) : J ⧸ Subgroup.center J) = orderOf b := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Prod.orderOf, orderOf_one, Nat.lcm_one_left]
  rw [hb.coe_psi_symm_eq_mul]
  constructor
  · intro hm
    obtain ⟨hxne, hdne⟩ := (hb.isMixedInv_mul_iff hx hd hm.orderOf_eq).mp hm
    refine ⟨fun ha => hxne (hx1.mpr ha), ?_⟩
    rw [← hdo]
    refine orderOf_eq_prime ?_ hdne
    have hss := pow_orderOf_eq_one (((hb.psi.symm (a, 1) : b1S T) : J ⧸ Subgroup.center J) *
      ((hb.psi.symm (1, b) : b1S T) : J ⧸ Subgroup.center J))
    rwa [hm.orderOf_eq, (hb.commute_of_mem_X_of_mem_D hx hd).mul_pow, pow_two (_ : J ⧸ _),
      hb.mul_self_of_mem_X hx, one_mul] at hss
  · rintro ⟨ha, hb2⟩
    exact hb.isMixedInv_mul hx hd (fun h => ha (hx1.mp h)) (hdo.trans hb2)

noncomputable def psiX (hb : CaseB1 Q B T L M) : b1X T L ≃* DihedralGroup 2 :=
  MulEquiv.ofBijective ((MonoidHom.fst _ _).comp
    (hb.psi.toMonoidHom.comp (Subgroup.inclusion hb.X_le_S)))
    ⟨fun x y hxy => by
      have hx := (hb.mem_X_iff_psi ⟨x, hb.X_le_S x.2⟩).mp x.2
      have hy := (hb.mem_X_iff_psi ⟨y, hb.X_le_S y.2⟩).mp y.2
      have h := congrArg Subtype.val (hb.psi.injective (Prod.ext hxy (hx.trans hy.symm)))
      exact Subtype.ext h,
    fun a => ⟨⟨_, hb.psi_symm_mem_X a⟩, by
      change (hb.psi (Subgroup.inclusion hb.X_le_S ⟨_, hb.psi_symm_mem_X a⟩)).1 = a
      rw [show Subgroup.inclusion hb.X_le_S ⟨_, hb.psi_symm_mem_X a⟩ = hb.psi.symm (a, 1) from
        rfl, MulEquiv.apply_symm_apply]⟩⟩

theorem card_X (hb : CaseB1 Q B T L M) : Nat.card (b1X T L) = 4 := by
  rw [Nat.card_congr hb.psiX.toEquiv, DihedralGroup.nat_card]

end CaseB1

end CFSG.ProperTwoGeneratedCore.Lemma37.QuasisimpleCore
