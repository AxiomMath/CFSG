module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P37Lift
public import CFSG.GH74.GLS.C3.Layer1.Thm1P38Gen
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RJ
public import CFSG.GH74.GLS.C3.Layer1.Thm1P39RStmt

public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

section EA

variable {G : Type} [Group G]

theorem isElementaryAbelian_zpowers_of_mul_self {a : G} (ha : a * a = 1) :
    IsElementaryAbelian 2 ↥(zpowers a) := by
  refine isElementaryAbelian_two (zpowers a) ?_ ?_
  · intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow_self a i j).eq
  · intro u hu
    rcases Thm1P310.eq_one_or_eq_of_mem_zpowers ha hu with h | h
    · rw [h]
      simp
    · rw [h]
      exact ha

theorem isElementaryAbelian_sup_of_commute {V W : Subgroup G} (hV : IsElementaryAbelian 2 ↥V)
    (hW : IsElementaryAbelian 2 ↥W) (hc : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) :
    IsElementaryAbelian 2 ↥(V ⊔ W) := by
  have hV' := isElementaryAbelian_two_data V hV
  have hW' := isElementaryAbelian_two_data W hW
  refine isElementaryAbelian_two (V ⊔ W) ?_ ?_
  · intro x hx y hy
    obtain ⟨v₁, hv₁, w₁, hw₁, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hc hx
    obtain ⟨v₂, hv₂, w₂, hw₂, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hc hy
    calc v₁ * w₁ * (v₂ * w₂) = v₁ * (w₁ * v₂) * w₂ := by group
      _ = v₁ * (v₂ * w₁) * w₂ := by rw [← hc v₂ hv₂ w₁ hw₁]
      _ = (v₁ * v₂) * (w₁ * w₂) := by group
      _ = (v₂ * v₁) * (w₂ * w₁) := by rw [hV'.1 v₁ hv₁ v₂ hv₂, hW'.1 w₁ hw₁ w₂ hw₂]
      _ = v₂ * (v₁ * w₂) * w₁ := by group
      _ = v₂ * (w₂ * v₁) * w₁ := by rw [hc v₁ hv₁ w₂ hw₂]
      _ = v₂ * w₂ * (v₁ * w₁) := by group
  · intro x hx
    obtain ⟨v, hv, w, hw, rfl⟩ := Thm1P310.exists_mul_of_mem_sup hc hx
    calc v * w * (v * w) = v * (w * v) * w := by group
      _ = v * (v * w) * w := by rw [← hc v hv w hw]
      _ = (v * v) * (w * w) := by group
      _ = 1 := by rw [hV'.2 v hv, hW'.2 w hw, one_mul]

end EA

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

namespace Env37

variable (E : Env37 x y K T V W f z)

include E

theorem liftData : LiftData (Back.actHom E.hKN) (T.subgroupOf (centralizer ({x} : Set G)))
    ((T ⊓ K).subgroupOf (centralizer ({x} : Set G))) ⟨f, E.hfC⟩ ⟨z, E.hCx E.hzP.1⟩ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set φ := Back.actHom E.hKN with hφ
  have hTC : T ≤ C := E.hCx
  have hPC : T ⊓ K ≤ C := inf_le_left.trans hTC
  have hKC : K ≤ C := E.cfg.hKx
  have hzC : z ∈ C := hTC E.hzP.1
  have hPker : ∀ p ∈ (T ⊓ K).subgroupOf C, φ p = 1 → p = 1 := by
    intro p hp hφp
    have hp' : (p : G) ∈ T ⊓ K := hp
    have h1 := Back.actHom_of_mem E.hKN hp'.2 p.2
    have h2 : (MulAut.conj (QuotientGroup.mk (⟨(p : G), hp'.2⟩ : ↥K) : kBar K)) =
        MulAut.conj 1 := by
      rw [map_one, ← h1]
      exact hφp
    have h3 := E.hcen h2
    have h4 : (⟨(p : G), hp'.2⟩ : ↥K) ∈ pPrimeCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h3
    have h5 : (p : G) ∈ pPrimeCoreOf 2 K := Back.Setup91.mem_pPrimeCoreOf_iff.2 ⟨hp'.2, h4⟩
    have h6 := Back.Setup91.inf_pPrimeCoreOf_eq_bot K E.cfg.setup.sylowT.isPGroup
    have h7 : (p : G) ∈ T ⊓ pPrimeCoreOf 2 K := ⟨hp'.1, h5⟩
    rw [h6, Subgroup.mem_bot] at h7
    exact Subtype.ext h7
  have hSylK : IsSylowOf 2 ((T ⊓ K).subgroupOf C) (K.subgroupOf C) := by
    have h := E.hPK
    rw [← isSylowOf_map_subtype_iff C, Subgroup.subgroupOf_map_subtype,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hPC, inf_eq_left.2 hKC]
    exact h
  have hSyl : IsSylowOf 2 (((T ⊓ K).subgroupOf C).map φ) (innAut (kBar K)) := by
    have := isSylowOf_map_hom φ hSylK
    rwa [hφ, map_actHom_K hKC E.hKN] at this
  refine ⟨E.cfg.setup.sylowT.isPGroup.comap_subtype, fun a ha =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.1 ha).1, ?_, hPker, hSyl, ?_, ?_, ?_, ?_,
    E.hfout, Subgroup.mem_subgroupOf.2 E.hzP, ?_, ?_, ?_⟩
  · intro t ht p hp
    have ht' : (t : G) ∈ T := ht
    have hp' : (p : G) ∈ T ⊓ K := hp
    refine Subgroup.mem_subgroupOf.2 ⟨?_, ?_⟩
    · exact T.mul_mem (T.mul_mem ht' hp'.1) (T.inv_mem ht')
    · exact E.hKN t t.2 p hp'.2
  · obtain ⟨n, hn3, hd⟩ := E.hdih
    exact ⟨n, hn3, isDihedralTwoGroup_of_equiv (Subgroup.subgroupOfEquivOfLe hPC) hd⟩
  · exact Subgroup.mem_subgroupOf.2 E.hfT
  · rw [Subgroup.orderOf_mk]
    exact E.cfg.hf2
  · intro p hp
    exact Subtype.ext (E.hfP p hp)
  · rw [Subgroup.orderOf_mk]
    exact E.hz2'
  · intro t ht
    exact Subtype.ext (E.hzc t ht)
  · intro w hw hwc
    have hw' : (w : G) ∈ T ⊓ K := hw
    rcases E.hzu w hw' (fun p hp => congrArg Subtype.val
        (hwc ⟨p, hPC hp⟩ (Subgroup.mem_subgroupOf.2 hp))) with h | h
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)

theorem ker_le_zpowers (k : ↥(centralizer ({x} : Set G)))
    (hkT : k ∈ T.subgroupOf (centralizer ({x} : Set G))) (hk : Back.actHom E.hKN k = 1) :
    (k : G) ∈ zpowers x := by
  have h1 : k ∈ (Back.actHom E.hKN).ker := hk
  rw [Back.actHom_ker E.hKN] at h1
  have h2 : (k : G) ∈ CMK (centralizer ({x} : Set G)) K := h1
  exact E.Q_le ⟨hkT, h2⟩

theorem card_map_ge {A : Subgroup G} (hAT : A ≤ T) (hA : IsElementaryAbelian 2 ↥A)
    (hA16 : 16 ≤ Nat.card ↥A) :
    8 ≤ Nat.card ↥((A.subgroupOf (centralizer ({x} : Set G))).map (Back.actHom E.hKN)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  set φ := Back.actHom E.hKN with hφ
  have hAC : A ≤ C := hAT.trans E.hCx
  show 8 ≤ Nat.card ↥((A.subgroupOf C).map φ)
  have hker : Nat.card ↥(A.subgroupOf C ⊓ φ.ker) ≤ 2 := by
    have hinf : A.subgroupOf C ⊓ (CMK C K).subgroupOf C = (A ⊓ CMK C K).subgroupOf C := by
      ext a
      simp [Subgroup.mem_subgroupOf]
    rw [hφ, Back.actHom_ker E.hKN, hinf]
    have hle : A ⊓ CMK C K ≤ C := inf_le_left.trans hAC
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    obtain ⟨hab, hsq⟩ := Back.forall_of_isElementaryAbelian hA
    exact E.hQ2 _ inf_le_right (Back.isElementaryAbelian_of_forall
      (fun u hu v hv => hab u hu.1 v hv.1) (fun u hu => hsq u hu.1))
  have h := Thm1.card_eq_card_map_mul_card_inf_ker φ (A.subgroupOf C)
  have hcard : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
  by_contra hlt
  push Not at hlt
  have h16 : 16 ≤ Nat.card ↥(A.subgroupOf C) := hcard ▸ hA16
  rw [h] at h16
  have h14 : Nat.card ↥((A.subgroupOf C).map φ) * Nat.card ↥(A.subgroupOf C ⊓ φ.ker) ≤ 7 * 2 :=
    Nat.mul_le_mul (by omega) hker
  exact absurd (h16.trans h14) (by norm_num)

theorem J_le_P (hAJ : AutLevelJ (kBar K)) {A : Subgroup G} (hAT : A ≤ T)
    (hA : IsElementaryAbelian 2 ↥A) (hA16 : 16 ≤ Nat.card ↥A) :
    A ≤ (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have D := E.liftData
  have hAC : A ≤ C := hAT.trans E.hCx
  have hA'T : A.subgroupOf C ≤ T.subgroupOf C := fun a ha =>
    Subgroup.mem_subgroupOf.2 (hAT (Subgroup.mem_subgroupOf.1 ha))
  have hA'el : IsElementaryAbelian 2 ↥(A.subgroupOf C) := by
    have := hA
    exact IsElementaryAbelian.subgroupOf hAC
  have key := D.J_le hAJ hA'T hA'el (E.card_map_ge hAT hA hA16)
  intro a ha
  have h1 := key (Subgroup.mem_subgroupOf.2 ha : (⟨a, hAC ha⟩ : ↥C) ∈ A.subgroupOf C)
  have hle : (T ⊓ K).subgroupOf C ⊔ zpowers (⟨f, E.hfC⟩ : ↥C) ⊔
      (T.subgroupOf C ⊓ (Back.actHom E.hKN).ker) ≤
      ((T ⊓ K) ⊔ (zpowers f ⊔ zpowers x)).comap C.subtype := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro p hp
      exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hp)
    · rw [zpowers_le]
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (mem_zpowers f))
    · intro k hk
      exact Subgroup.mem_sup_right (Subgroup.mem_sup_right
        (E.ker_le_zpowers k hk.1 (MonoidHom.mem_ker.1 hk.2)))
  exact hle h1

theorem f_not_mem_P : f ∉ T ⊓ K := fun hf => E.hfout (E.actHom_inner_of_mem_P f hf E.hfC)

theorem x_not_mem_P : x ∉ T ⊓ K := by
  intro hx
  have D := E.liftData
  have hxC : x ∈ centralizer ({x} : Set G) := mem_centralizer_singleton_iff.2 rfl
  have h := D.hPker ⟨x, hxC⟩ (Subgroup.mem_subgroupOf.2 hx) E.actHom_x
  have h1 : x = 1 := congrArg Subtype.val h
  have h2 := E.cfg.hx2
  rw [h1, orderOf_one] at h2
  omega

theorem fx_not_mem_P : f * x ∉ T ⊓ K := by
  intro h
  have hC : f * x ∈ centralizer ({x} : Set G) := E.hCx (T.mul_mem E.hfT E.hxT)
  exact E.actHom_f_mul_outer x (Subgroup.mem_sup_right (mem_zpowers x)) hC
    (E.actHom_inner_of_mem_P (f * x) h hC)

theorem inf_E_eq_bot : (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hgP, hgE⟩
  rw [Subgroup.mem_bot]
  rcases Thm1G33.klein_cases E.hf2 E.hx2 E.hfx hgE with h | h | h | h
  · exact h
  · exact absurd (h ▸ hgP) E.f_not_mem_P
  · exact absurd (h ▸ hgP) E.x_not_mem_P
  · exact absurd (h ▸ hgP) E.fx_not_mem_P

theorem card_P : ∃ n : ℕ, 3 ≤ n ∧ Nat.card ↥(T ⊓ K) = 2 ^ n := by
  obtain ⟨n, hn3, hdn⟩ := E.hdih
  obtain ⟨k, hk, hk2, ⟨ρ⟩⟩ := hdn.2
  refine ⟨n, hn3, ?_⟩
  rw [Nat.card_congr ρ.toEquiv, DihedralGroup.nat_card]
  exact hk.symm

theorem exists_invol_ne_z : ∃ s ∈ T ⊓ K, orderOf s = 2 ∧ s ≠ z := by
  by_contra hno
  push Not at hno
  obtain ⟨n, hn3, hdn⟩ := E.hdih
  have hle : T ⊓ K ≤ zpowers z := by
    refine (le_closure_invol_of_dihedral hdn.2).trans ((Subgroup.closure_le _).2 ?_)
    rintro u ⟨hu, hu2⟩
    rw [hno u hu hu2]
    exact mem_zpowers z
  have h1 : Nat.card ↥(T ⊓ K) ≤ Nat.card ↥(zpowers z) := Subgroup.card_le_of_le hle
  rw [Nat.card_zpowers, E.hz2'] at h1
  obtain ⟨m, hm3, hm⟩ := E.card_P
  have h8 : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  omega

theorem klein_le_J (hG : C3Hyp G) {a : G} (haP : a ∈ T ⊓ K) (ha2 : orderOf a = 2) (haz : a ≠ z) :
    zpowers a ⊔ zpowers z ⊔ (zpowers f ⊔ zpowers x) ≤ thompsonJ2 T := by
  have haa : a * a = 1 := by
    have := pow_orderOf_eq_one a
    rwa [ha2, sq] at this
  have haz' : a * z = z * a := E.hzc a haP.1
  have haf : a * f = f * a := (E.hfP a haP).symm
  have hax : a * x = x * a := E.hxc a haP.1
  have hzf : z * f = f * z := E.hfz.symm
  have hzx : z * x = x * z := E.hzx
  set V : Subgroup G := zpowers a ⊔ zpowers z with hV
  set W : Subgroup G := zpowers f ⊔ zpowers x with hW
  have hVea : IsElementaryAbelian 2 ↥V := by
    refine isElementaryAbelian_sup_of_commute (isElementaryAbelian_zpowers_of_mul_self haa)
      (isElementaryAbelian_zpowers_of_mul_self E.hzz) ?_
    intro v hv w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hv
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_zpow (show Commute a z from haz') i j).eq
  have hWea : IsElementaryAbelian 2 ↥W := by
    refine isElementaryAbelian_sup_of_commute (isElementaryAbelian_zpowers_of_mul_self E.hf2)
      (isElementaryAbelian_zpowers_of_mul_self E.hx2) ?_
    intro v hv w hw
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hv
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hw
    exact (Commute.zpow_zpow (show Commute f x from E.hfx) i j).eq
  have hVf : V ≤ centralizer ({f} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 haf))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzf))
  have hVx : V ≤ centralizer ({x} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 hax))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 hzx))
  have hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v := by
    intro v hv w hw
    have hW' : W ≤ centralizer ({v} : Set G) :=
      sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2
          (mem_centralizer_singleton_iff.1 (hVf hv)).symm))
        (zpowers_le.2 (mem_centralizer_singleton_iff.2
          (mem_centralizer_singleton_iff.1 (hVx hv)).symm))
    exact (mem_centralizer_singleton_iff.1 (hW' hw)).symm
  have hAea : IsElementaryAbelian 2 ↥(V ⊔ W) := isElementaryAbelian_sup_of_commute hVea hWea hVW
  have hAT : V ⊔ W ≤ T :=
    sup_le (sup_le (zpowers_le.2 haP.1) (zpowers_le.2 E.hzP.1))
      (sup_le (zpowers_le.2 E.hfT) (zpowers_le.2 E.hxT))
  have hVP : V ≤ T ⊓ K := sup_le (zpowers_le.2 haP) (zpowers_le.2 E.hzP)
  have hVcard : Nat.card ↥V = 4 := Thm1P38.card_klein_of_comm ha2 E.hz2' haz' haz
  have hWcard : Nat.card ↥W = 4 := Thm1P38.card_klein_of_comm E.cfg.hf2 E.cfg.hx2 E.hfx E.hfne
  have hnorm : W ≤ normalizer (V : Set G) := by
    refine le_trans (fun w hw => mem_centralizer_iff.2 fun v hv => hVW v hv w hw)
      (Subgroup.centralizer_le_normalizer _)
  have hdisj : Disjoint V W := by
    refine Subgroup.disjoint_def.2 ?_
    intro g hgV hgW
    have : g ∈ (T ⊓ K) ⊓ (zpowers f ⊔ zpowers x) := ⟨hVP hgV, hgW⟩
    rw [E.inf_E_eq_bot, Subgroup.mem_bot] at this
    exact this
  have hAcard : Nat.card ↥(V ⊔ W) = 16 := by
    rw [GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj, hVcard,
      hWcard]
  refine Thm1P39R.le_thompsonJ2 hAT hAea fun B _ hB => ?_
  rw [hAcard]
  exact Thm1P39R.card_le_sixteen_of_pRank hG.pRank_eq_four hB

theorem le_J (hG : C3Hyp G) : (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) ≤ thompsonJ2 T := by
  obtain ⟨s, hs, hs2, hsz⟩ := E.exists_invol_ne_z
  have hs' := E.klein_le_J hG hs hs2 hsz
  have hP : T ⊓ K ≤ thompsonJ2 T := by
    obtain ⟨n, hn3, hdn⟩ := E.hdih
    refine (le_closure_invol_of_dihedral hdn.2).trans ((Subgroup.closure_le _).2 ?_)
    rintro u ⟨hu, hu2⟩
    by_cases huz : u = z
    · rw [huz]
      exact hs' (Subgroup.mem_sup_left (Subgroup.mem_sup_right (mem_zpowers z)))
    · exact (E.klein_le_J hG hu hu2 huz)
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers u)))
  exact sup_le hP (le_sup_right.trans hs')

theorem J_eq (hG : C3Hyp G) (hAJ : AutLevelJ (kBar K)) :
    thompsonJ2 T = (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) := by
  refine le_antisymm (iSup₂_le fun A hA => ?_) (E.le_J hG)
  obtain ⟨hAT, hAel, hAmax⟩ := hA
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := E.hE₁
  exact E.J_le_P hAJ hAT hAel ((hE₁16.trans (hAmax E₁ hE₁T hE₁)))

theorem zCenter_J_eq (hJ : thompsonJ2 T = (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x)) :
    zCenter (thompsonJ2 T) = zpowers z ⊔ zpowers f ⊔ zpowers x := by
  rw [hJ]
  have hEsub : zpowers f ⊔ zpowers x ≤ zpowers z ⊔ zpowers f ⊔ zpowers x :=
    sup_le (le_trans le_sup_right le_sup_left) le_sup_right
  apply le_antisymm
  · intro g hg
    obtain ⟨p, hp, e, he, rfl⟩ := Thm1P310.exists_mul_of_mem_sup
      (fun u hu w hw => (E.hEP w hw u hu).symm) hg.1
    have hpc : ∀ q ∈ T ⊓ K, p * q = q * p := by
      intro q hq
      have h1 := hg.2 q (Subgroup.mem_sup_left hq)
      have h2 : e * q = q * e := E.hEP e he q hq
      have h3 : q * p * e = p * q * e := by
        calc q * p * e = q * (p * e) := by group
          _ = p * e * q := h1
          _ = p * (e * q) := by group
          _ = p * (q * e) := by rw [h2]
          _ = p * q * e := by group
      exact (mul_right_cancel h3).symm
    rcases E.hzu p hp hpc with h | h
    · rw [h, one_mul]
      exact hEsub he
    · rw [h]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left (mem_zpowers z))) (hEsub he)
  · have hzJ : (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) ≤ centralizer ({z} : Set G) :=
      sup_le (fun p hp => mem_centralizer_singleton_iff.2 (E.hzc p hp.1))
        (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 E.hfz))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 E.hzx.symm)))
    have hfJ : (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) ≤ centralizer ({f} : Set G) :=
      sup_le (fun p hp => mem_centralizer_singleton_iff.2 (E.hfP p hp).symm)
        (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 E.hfx.symm)))
    have hxJ : (T ⊓ K) ⊔ (zpowers f ⊔ zpowers x) ≤ centralizer ({x} : Set G) :=
      sup_le (fun p hp => E.hCx hp.1)
        (sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 E.hfx))
          (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)))
    refine sup_le (sup_le (zpowers_le.2 ⟨Subgroup.mem_sup_left E.hzP, fun h hh =>
      mem_centralizer_singleton_iff.1 (hzJ hh)⟩) (zpowers_le.2 ⟨?_, fun h hh =>
      mem_centralizer_singleton_iff.1 (hfJ hh)⟩)) (zpowers_le.2 ⟨?_, fun h hh =>
      mem_centralizer_singleton_iff.1 (hxJ hh)⟩)
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_left (mem_zpowers f))
    · exact Subgroup.mem_sup_right (Subgroup.mem_sup_right (mem_zpowers x))

theorem normalizer_eq (hAJ : AutLevelJ (kBar K)) {P₀ : Subgroup G}
    (hP₀ : IsDihedralMaxIn P₀ (T ⊓ K)) :
    T ⊓ centralizer ({f} : Set G) = T ⊓ normalizer (P₀ : Set G) := by
  set C : Subgroup G := centralizer ({x} : Set G) with hC
  have D := E.liftData
  have hTC : T ≤ C := E.hCx
  have hPC : T ⊓ K ≤ C := inf_le_left.trans hTC
  obtain ⟨hP₀P, hcard, hdih⟩ := hP₀
  have hP₀C : P₀ ≤ C := hP₀P.trans hPC
  have hP₀' : IsDihedralMaxIn (P₀.subgroupOf C) ((T ⊓ K).subgroupOf C) := by
    refine ⟨fun a ha => Subgroup.mem_subgroupOf.2 (hP₀P (Subgroup.mem_subgroupOf.1 ha)), ?_, ?_⟩
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPC).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀C).toEquiv]
      exact hcard
    · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₀C).toEquiv]
      exact SP.Local.CtW.isDihedralOrder_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP₀C).symm hdih
  obtain ⟨E₁, hE₁T, hE₁, hE₁16⟩ := E.hE₁
  have hE₁C : E₁ ≤ C := hE₁T.trans hTC
  have hE₁'T : E₁.subgroupOf C ≤ T.subgroupOf C := fun a ha =>
    Subgroup.mem_subgroupOf.2 (hE₁T (Subgroup.mem_subgroupOf.1 ha))
  have hE₁'el : IsElementaryAbelian 2 ↥(E₁.subgroupOf C) := by
    have := hE₁
    exact IsElementaryAbelian.subgroupOf hE₁C
  have hZ : ∀ k ∈ T.subgroupOf C ⊓ (Back.actHom E.hKN).ker, ∀ s ∈ T.subgroupOf C,
      k * s = s * k := by
    intro k hk s hs
    apply Subtype.ext
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (E.ker_le_zpowers k hk.1 (MonoidHom.mem_ker.1 hk.2))
    have hsx : (s : G) * x = x * (s : G) := E.hxc s hs
    show (k : G) * s = s * k
    rw [← hj]
    exact (Commute.zpow_left (show Commute x (s : G) from hsx.symm) j).eq
  have key := D.normalizer_iff hAJ hE₁'T hE₁'el (E.card_map_ge hE₁T hE₁ hE₁16) hZ hP₀'
  ext t
  constructor
  · rintro ⟨htT, htc⟩
    refine ⟨htT, Thm1L3.mem_normalizer_of_conj_le fun u hu => ?_⟩
    have hcomm : t * f = f * t := mem_centralizer_singleton_iff.1 htc
    have := (key ⟨t, hTC htT⟩ (Subgroup.mem_subgroupOf.2 htT)).2 (Subtype.ext hcomm)
    exact this ⟨u, hP₀C hu⟩ (Subgroup.mem_subgroupOf.2 hu)
  · rintro ⟨htT, htN⟩
    refine ⟨htT, mem_centralizer_singleton_iff.2 ?_⟩
    have := (key ⟨t, hTC htT⟩ (Subgroup.mem_subgroupOf.2 htT)).1 (fun u hu =>
      Subgroup.mem_subgroupOf.2 ((Subgroup.mem_normalizer_iff.1 htN (u : G)).1
        (Subgroup.mem_subgroupOf.1 hu)))
    exact congrArg Subtype.val this


end Env37

theorem thm1_L37_of_rel
    (h2hb : IVK.IVK_1_2h_b) (h102 : B_ivk_10_2) (hL34 : B_gen4_noL34_elem)
    (hP31s : B_thm1_P31s_rel) (hP31c : B_thm1_P31c_rel) (h35 : B_thm1_L35_rel) :
    B_thm1_L37_rel := by
  intro G _ _ hG hNo x y K T V W f z cfg _ hVW h5
  have E : Env37 x y K T V W f z :=
    env37_of_rel h2hb h102 hL34 hP31s hP31c h35 hG hNo cfg hVW h5
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_l2_model_of_hasL2Model E.hshape
  have hAJ : AutLevelJ (kBar K) := autLevelJ_of_L2 h2hb hF e
  have hJ := E.J_eq hG hAJ
  exact ⟨⟨hJ, E.inf_E_eq_bot⟩, E.zCenter_J_eq hJ, fun P₀ hP₀ => E.normalizer_eq hAJ hP₀⟩

end CFSG.GH74.GLS.C3.Layer1.Thm1P38
