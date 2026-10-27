module

public import CFSG.GH74.Uniqueness.Section12Transport
public import CFSG.GH74.Uniqueness.Section12BenderSub
public import CFSG.GH74.Uniqueness.Section12Center

public section

namespace CFSG.GH74.Uniqueness

open Subgroup
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

theorem ZDSetup.zHull_L (S : ZDSetup X Z M) (c : Ctx12 Z M) : zHull Z c.L = c.L :=
  IsProductDisconnected.zHull_lSubgroup S.invariant c.ht c.hz M

theorem ZDSetup.inter_subset_L (S : ZDSetup X Z M) (c : Ctx12 Z M) :
    Z ∩ (M : Set X) ⊆ (c.L : Set X) :=
  S.prodDisc.inter_le_lSubgroup S.invariant c.ht c.htM c.hz c.hzM

theorem Ctx12.not_L_le (c : Ctx12 Z M) : ¬ c.L ≤ M := fun hle => c.htM (hle c.t_mem_L)

theorem Ctx12.nonempty_inter (c : Ctx12 Z M) :
    (Z ∩ ((c.L ⊓ M : Subgroup X) : Set X)).Nonempty :=
  ⟨c.z, c.hz, mem_inf.mpr ⟨c.z_mem_L, c.hzM⟩⟩

theorem Ctx12.conj_mem_D (hZ : IsInvariantInvolutionSet Z) (c : Ctx12 Z M) {g : X}
    (hg : g ∈ c.D) : c.t * g * c.t⁻¹ ∈ c.D := by
  have ht2 : c.t * c.t = 1 := hZ.mul_self_eq_one c.ht
  obtain ⟨hgM, hgt⟩ := mem_inf.mp hg
  rw [Bender.mem_conjugate_iff_mul_inv] at hgt
  refine mem_inf.mpr ⟨hgt, ?_⟩
  rw [Bender.mem_conjugate_iff_mul_inv]
  have e : c.t * (c.t * g * c.t⁻¹) * c.t⁻¹ = g := by
    calc c.t * (c.t * g * c.t⁻¹) * c.t⁻¹ = (c.t * c.t) * g * (c.t * c.t)⁻¹ := by group
      _ = g := by rw [ht2]; group
  rw [e]
  exact hgM

theorem ZDSetup.benderSub_L
    (S : ZDSetup X Z M) (c : Ctx12 Z M) :
    ∃ n i e : ℕ, BenderSub Z M c.L n i e := by
  obtain ⟨y, hy, hyz, hyzc⟩ := S.exists_commuting_ne c.hz
  have hyM : y ∈ M :=
    S.prodDisc.centralizer_le_of_mem c.hz c.hzM (mem_centralizer_singleton_iff.mpr hyzc)
  have hyL : y ∈ c.L := S.inter_subset_L c ⟨hy, hyM⟩
  have hns := S.not_solvable_zHull_of_ne c.hL c.not_L_le
    (⟨c.hz, mem_inf.mpr ⟨c.z_mem_L, c.hzM⟩⟩ : c.z ∈ Z ∩ ((c.L ⊓ M : Subgroup X) : Set X))
    (⟨hy, mem_inf.mpr ⟨hyL, hyM⟩⟩ : y ∈ Z ∩ ((c.L ⊓ M : Subgroup X) : Set X)) (Ne.symm hyz)
  obtain ⟨n, i, e, hB⟩ := S.benderSub_exists c.hL c.not_L_le c.nonempty_inter hns
  rw [S.zHull_L c] at hB
  exact ⟨n, i, e, hB⟩

theorem ZDSetup.benderSub_L_ne_three
    (S : ZDSetup X Z M) (c : Ctx12 Z M) {n e : ℕ}
    (hB : BenderSub Z M c.L n 3 e) : False := by
  have hZ := S.invariant
  have ht2 : c.t * c.t = 1 := hZ.mul_self_eq_one c.ht
  have hti : c.t⁻¹ = c.t := inv_eq_of_mul_eq_one_right ht2
  obtain ⟨T, hT⟩ := hB.borel
  set π := QuotientGroup.mk' (center ↥c.L) with hπ
  have hC : center ↥c.L ≤ (M ⊓ c.L).subgroupOf c.L := by
    intro x hx
    have hxz : c.zL * x = x * c.zL := mem_center_iff.mp hx c.zL
    have hxM : (x : X) ∈ M := S.prodDisc.centralizer_le_of_mem c.hz c.hzM
      (mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hxz).symm)
    exact mem_subgroupOf.mpr (mem_inf.mpr ⟨hxM, x.2⟩)
  have hodd : Odd (Nat.card (center ↥c.L)) := by
    have h1 := odd_card_pPrimeCoreIn c.L
    rwa [hB.core, card_map_of_injective c.L.subtype_injective] at h1
  have hmapB : ∀ x : ↥c.L, (x : X) ∈ M → π x ∈ Bender.borel (T : Subgroup (↥c.L ⧸ center ↥c.L)) := by
    intro x hx
    change π x ∈ normalizer _
    rw [← hT]
    exact mem_map_of_mem π (mem_subgroupOf.mpr (mem_inf.mpr ⟨hx, x.2⟩))
  have htb2 : π c.tL * π c.tL = 1 := by rw [← map_mul, c.tL_mul_self hZ, map_one]
  have htbT : π c.tL ∉ Bender.borel (T : Subgroup (↥c.L ⧸ center ↥c.L)) := by
    intro hmem
    change π c.tL ∈ normalizer _ at hmem
    rw [← hT] at hmem
    obtain ⟨m, hm, hmt⟩ := hmem
    have h1 : m⁻¹ * c.tL ∈ center ↥c.L := QuotientGroup.eq.mp hmt
    have h2 : c.tL ∈ (M ⊓ c.L).subgroupOf c.L := by
      have := ((M ⊓ c.L).subgroupOf c.L).mul_mem hm (hC h1)
      simpa using this
    exact c.htM (mem_inf.mp (mem_subgroupOf.mp h2)).1
  have hzb1 : π c.zL ≠ 1 := by
    intro h1
    have hzC : c.zL ∈ center ↥c.L := (QuotientGroup.eq_one_iff c.zL).mp h1
    have hord : orderOf c.zL = 2 := by
      rw [orderOf_mk]
      exact hZ.1 c.z c.hz
    have hdvd : orderOf c.zL ∣ Nat.card (center ↥c.L) := by
      have := orderOf_dvd_natCard (⟨c.zL, hzC⟩ : center ↥c.L)
      rwa [Subgroup.orderOf_mk] at this
    rw [hord] at hdvd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdvd)
  have hzb2 : orderOf (π c.zL) = 2 := by
    apply orderOf_eq_prime _ hzb1
    have hzz : c.zL * c.zL = 1 := Subtype.ext (hZ.mul_self_eq_one c.hz)
    rw [sq, ← map_mul, hzz, map_one]
  have hc := hB.bender.benderCore T htb2 htbT
  have hzbR : π c.zL ∈ Bender.rootCenter (T : Subgroup (↥c.L ⧸ center ↥c.L)) :=
    hc.center_of_involution _ (hmapB c.zL c.hzM) hzb2
  apply hB.bender.lemma_3_2_h_unitary_ne_top T htb2 htbT hzbR hzb1
  set H := closure ({π c.zL, π c.tL} : Set (↥c.L ⧸ center ↥c.L)) ⊔
    ⁅Bender.cartan (T : Subgroup (↥c.L ⧸ center ↥c.L)) (π c.tL), zpowers (π c.tL)⁆ with hH
  have hLle : c.L ≤ (H.comap π).map c.L.subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · rw [zpowers_le]
      exact ⟨c.zL, mem_sup_left (subset_closure (Set.mem_insert _ _)), rfl⟩
    · rw [zpowers_le]
      exact ⟨c.tL, mem_sup_left (subset_closure (Set.mem_insert_of_mem _ rfl)), rfl⟩
    · rw [commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rcases eq_one_or_eq_of_mem_zpowers ht2 hg₁ with rfl | rfl
      · rw [commutatorElement_one_left]
        exact one_mem _
      · have hg₂D : g₂ ∈ c.D := pPrimeCoreIn_le _ hg₂
        have hkL : ⁅c.t, g₂⁆ ∈ c.L :=
          c.kGrp_le_L (commutator_mem_commutator (mem_zpowers c.t) hg₂)
        have hkD : ⁅c.t, g₂⁆ ∈ c.D := by
          rw [commutatorElement_def]
          exact c.D.mul_mem (c.conj_mem_D hZ hg₂D) (c.D.inv_mem hg₂D)
        have hkinv : c.t * ⁅c.t, g₂⁆ * c.t = ⁅c.t, g₂⁆⁻¹ := by
          rw [commutatorElement_def]
          calc c.t * (c.t * g₂ * c.t⁻¹ * g₂⁻¹) * c.t
              = (c.t * c.t) * g₂ * c.t⁻¹ * g₂⁻¹ * c.t := by group
            _ = g₂ * c.t⁻¹ * g₂⁻¹ * c.t := by rw [ht2, one_mul]
            _ = g₂ * c.t * g₂⁻¹ * c.t⁻¹ := by rw [hti]
            _ = (c.t * g₂ * c.t⁻¹ * g₂⁻¹)⁻¹ := by group
        refine ⟨⟨_, hkL⟩, mem_sup_right ?_, rfl⟩
        rw [hc.mem_commutator_cartan_iff]
        constructor
        · change π ⟨_, hkL⟩ ∈ Bender.borel (T : Subgroup (↥c.L ⧸ center ↥c.L)) ⊓
            conjugate (Bender.borel (T : Subgroup (↥c.L ⧸ center ↥c.L))) (π c.tL)
          refine mem_inf.mpr ⟨hmapB _ (mem_inf.mp hkD).1, ?_⟩
          rw [Bender.mem_conjugate_iff_mul_inv, ← map_inv, ← map_mul, ← map_mul]
          exact hmapB _ (Bender.mem_conjugate_iff_mul_inv.mp (mem_inf.mp hkD).2)
        · rw [← map_mul, ← map_mul, ← map_inv]
          congr 1
          exact Subtype.ext hkinv
  have hH'top : H.comap π = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hLle x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  refine eq_top_iff.mpr fun y _ => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center ↥c.L) y
  have hx : x ∈ H.comap π := hH'top ▸ mem_top x
  exact hx

theorem ZDSetup.lemma122a
    (S : ZDSetup X Z M) (c : Ctx12 Z M) :
    ∃ n i : ℕ, (i = 1 ∨ i = 2) ∧ 2 ≤ n ∧ Bender.BenderType ↥c.L n i 1 ∧
      (∃ Q : Sylow 2 ↥c.L,
        (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) ∧
      ∀ y ∈ c.L, orderOf y = 2 → y ∈ Z := by
  obtain ⟨n, i, e, hB⟩ := S.benderSub_L c
  have hi : i = 1 ∨ i = 2 := by
    rcases hB.bender.cases' with ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩ | ⟨rfl, -, -⟩
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (S.benderSub_L_ne_three c hB).elim
  have he : e = 1 := by
    rcases hB.bender.cases' with ⟨-, he, -⟩ | ⟨-, he, -⟩ | ⟨hi3, -, -⟩
    · exact he
    · exact he
    · omega
  subst he
  have hodd : Odd (Nat.card (center ↥c.L)) := by
    have h1 := odd_card_pPrimeCoreIn c.L
    rwa [hB.core, card_map_of_injective c.L.subtype_injective] at h1
  have hgen : closure {x : ↥c.L | x * x = 1} = ⊤ := by
    have hle : c.L ≤ (closure {x : ↥c.L | x * x = 1}).map c.L.subtype := by
      have h1 : zHull Z c.L ≤ (closure {x : ↥c.L | x * x = 1}).map c.L.subtype := by
        refine (closure_le _).mpr fun y hy => ?_
        refine ⟨⟨y, hy.2⟩, subset_closure ?_, rfl⟩
        exact Subtype.ext (S.invariant.mul_self_eq_one hy.1)
      rwa [S.zHull_L c] at h1
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨y, hy, hyx⟩ := hle x.2
    rwa [show y = x from Subtype.ext hyx] at hy
  have hcen : center ↥c.L = ⊥ := center_eq_bot_of_benderType hi hgen hodd hB.bender
  have hBL : Bender.BenderType ↥c.L n i 1 := benderType_of_center_eq_bot hB.bender hcen
  obtain ⟨T, hT⟩ := hB.borel
  obtain ⟨Q, hQ⟩ := exists_sylow_normalizer_eq_of_center_eq_bot hcen hT
  exact ⟨n, i, hi, hBL.two_le.2, hBL, ⟨Q, hQ⟩, hB.invol⟩

end CFSG.GH74.Uniqueness
