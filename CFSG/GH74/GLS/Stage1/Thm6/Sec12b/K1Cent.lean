module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.K1Count
public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9b

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

variable {G : Type} [Group G] [Finite G]

structure K1Ctx (G : Type) [Group G] [Finite G] (x z : G) (S T P Q Rd F V : Subgroup G) :
    Prop where
  base : HBase G x S T P Q Rd F
  hz : HZ T P z
  h127 : After127 G x z S T P Q Rd F
  h4 : Nat.card (omegaZ T) = 4
  VP : V ≤ P
  V4 : IsFour V
  zV : z ∈ V
  Ec : T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) =
    V ⊔ Subgroup.zpowers x
  P8 : 8 ≤ Nat.card P
  dih : IP_Rd_dihedral x Rd
  fuse : IP_Rd_fuse x P Rd
  Tn : IP_T_normal x z T P Rd

namespace K1Ctx

variable {x z : G} {S T P Q Rd F V : Subgroup G} (c : K1Ctx G x z S T P Q Rd F V)
include c

theorem PX_disj : P ⊓ Subgroup.zpowers x = ⊥ := by
  rw [← c.h127.Q_eq]; exact c.base.PQ_disjoint

theorem R_le_Rd : P ⊔ Subgroup.zpowers x ≤ Rd := by
  rw [← c.h127.Q_eq]; exact c.base.R_le_Rd

theorem P_le_Rd : P ≤ Rd := le_sup_left.trans c.R_le_Rd

theorem x_mem_Rd : x ∈ Rd := c.R_le_Rd (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

theorem R_index : (P ⊔ Subgroup.zpowers x).relIndex Rd ≤ 2 := by
  rw [← c.h127.Q_eq]; exact c.base.R_index_le_two

theorem Z_eq : omegaZ T = Subgroup.zpowers x ⊔ Subgroup.zpowers z := c.base.Z_eq c.hz c.h4

theorem Z_le_R : omegaZ T ≤ P ⊔ Subgroup.zpowers x := by
  rw [c.Z_eq]
  exact sup_le le_sup_right ((Subgroup.zpowers_le).2 (Subgroup.mem_sup_left c.hz.z_mem_P))

theorem inv_mem_Rd {a : G} (haT : a ∈ T) (ha2 : a * a = 1) : a ∈ Rd :=
  c.h127.omega1_le (Subgroup.subset_closure ⟨haT, ha2⟩)

theorem EV_le_R : V ⊔ Subgroup.zpowers x ≤ P ⊔ Subgroup.zpowers x :=
  sup_le (c.VP.trans le_sup_left) le_sup_right

theorem EV_le_Rd : V ⊔ Subgroup.zpowers x ≤ Rd := c.EV_le_R.trans c.R_le_Rd

theorem EV_ab : IsElemAb2 (V ⊔ Subgroup.zpowers x) :=
  isElemAb2_sup_zpowers c.V4 c.base.x_sq (fun v hv => c.base.x_central v (c.base.P_le_T (c.VP hv)))

theorem EV_card : Nat.card (V ⊔ Subgroup.zpowers x : Subgroup G) = 8 := card_E c.base c.VP c.V4

theorem P_comm_x : ∀ p ∈ P, ∀ b ∈ Subgroup.zpowers x, p * b = b * p := by
  intro p hp b hb
  rcases zpowers_sq_cases c.base.x_sq hb with rfl | rfl
  · simp
  · exact (c.base.x_central p (c.base.P_le_T hp)).symm

theorem rd_eq_T {F' : Subgroup G} (hF'T : F' ≤ T) (hFinf : F' ⊓ Rd = Subgroup.zpowers x)
    (hTeq : Rd ⊔ F' = T)
    (hc1 : ∀ w ∈ F', w ^ 4 = 1 → (∀ p ∈ P, w * p = p * w) ∧
      ∀ b ∈ Rd, w * b * w⁻¹ * b⁻¹ ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers z) :
    Rd = T := by
  classical
  have hF : F' ≤ Subgroup.zpowers x := by
    by_contra hnle
    obtain ⟨f, hfF', hfx⟩ := IsConcreteLE.not_le_iff_exists.1 hnle
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 c.base.T_pgroup) ⟨f, hF'T hfF'⟩
    have hm' : orderOf f = 2 ^ m := by rw [← hm]; exact (Subgroup.orderOf_mk f _).symm
    have hex : ∃ j : ℕ, f ^ (2 ^ j) ∈ Subgroup.zpowers x :=
      ⟨m, by rw [← hm', pow_orderOf_eq_one]; exact Subgroup.one_mem _⟩
    obtain ⟨j, hj, hjmin⟩ : ∃ j : ℕ, f ^ (2 ^ j) ∈ Subgroup.zpowers x ∧
        ∀ i < j, f ^ (2 ^ i) ∉ Subgroup.zpowers x :=
      ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact hfx (by simpa using hj)
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hw : f ^ (2 ^ i) * f ^ (2 ^ i) = f ^ (2 ^ (i + 1)) := by
      rw [← pow_add, pow_succ, mul_two]
    have hwF : f ^ (2 ^ i) ∈ F' := Subgroup.pow_mem F' hfF' _
    have hwT : f ^ (2 ^ i) ∈ T := hF'T hwF
    have hww : f ^ (2 ^ i) * f ^ (2 ^ i) = x := by
      rw [hw]
      rcases zpowers_sq_cases c.base.x_sq hj with h1 | h1
      · exfalso
        have h2 : f ^ (2 ^ i) * f ^ (2 ^ i) = 1 := by rw [hw, h1]
        have h3 : f ^ (2 ^ i) ∈ F' ⊓ Rd := ⟨hwF, c.inv_mem_Rd hwT h2⟩
        rw [hFinf] at h3
        exact hjmin i (by omega) h3
      · exact h1
    set w := f ^ (2 ^ i) with hwdef
    have hw4 : w ^ 4 = 1 := by
      have : w ^ 4 = (w * w) * (w * w) := by simp [pow_succ, mul_assoc]
      rw [this, hww, c.base.x_sq]
    have hwP := (hc1 w hwF hw4).1
    have hwE : w ∈ T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
      refine ⟨hwT, Subgroup.mem_centralizer_iff.2 (fun e he => ?_)⟩
      have hle : V ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({w} : Set G) :=
        sup_le (fun v hv => Subgroup.mem_centralizer_singleton_iff.2 (hwP v (c.VP hv)).symm)
          ((Subgroup.zpowers_le).2
            (Subgroup.mem_centralizer_singleton_iff.2 (c.base.x_central w hwT)))
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)
    rw [c.Ec] at hwE
    have h1 := (c.EV_ab w hwE).1
    rw [hww] at h1
    exact c.base.x_ne_one h1
  apply le_antisymm c.base.Rd_le_T
  rw [← hTeq]
  exact sup_le le_rfl (hF.trans ((Subgroup.zpowers_le).2 c.x_mem_Rd))

theorem Ea_facts {a : G} (haT : a ∈ T) (ha2 : a * a = 1) (haZ : a ∉ omegaZ T) :
    IsElemAb2 (omegaZ T ⊔ Subgroup.zpowers a) ∧
      Nat.card (omegaZ T ⊔ Subgroup.zpowers a : Subgroup G) = 8 ∧
      omegaZ T ⊔ Subgroup.zpowers a ≤ Rd := by
  have hcomm : ∀ u ∈ omegaZ T, ∀ b ∈ Subgroup.zpowers a, u * b = b * u := by
    intro u hu b hb
    exact hu.2.2 b ((Subgroup.zpowers_le).2 haT hb)
  have ha1 : a ≠ 1 := fun e => haZ (by rw [e]; exact (omegaZ T).one_mem)
  have hdisj : omegaZ T ⊓ Subgroup.zpowers a = ⊥ := by
    rw [eq_bot_iff]
    rintro b ⟨hbZ, hba⟩
    rcases zpowers_sq_cases ha2 hba with rfl | rfl
    · exact Subgroup.one_mem _
    · exact absurd hbZ haZ
  refine ⟨(omegaZ_isElemAb2 T).sup (isElemAb2_zpowers ha2) hcomm, ?_, ?_⟩
  · rw [card_sup_of_commute hcomm hdisj, c.h4, card_zpowers_of_sq ha2 ha1]
  · exact sup_le (fun u hu => c.inv_mem_Rd hu.1 hu.2.1)
      ((Subgroup.zpowers_le).2 (c.inv_mem_Rd haT ha2))

omit [Finite G] c in
theorem cent_le_cent_Ea {a : G} :
    T ⊓ Subgroup.centralizer {a} ≤
      T ⊓ Subgroup.centralizer ((omegaZ T ⊔ Subgroup.zpowers a : Subgroup G) : Set G) := by
  rintro g ⟨hgT, hga⟩
  refine ⟨hgT, Subgroup.mem_centralizer_iff.2 (fun e he => ?_)⟩
  have hle : omegaZ T ⊔ Subgroup.zpowers a ≤ Subgroup.centralizer ({g} : Set G) :=
    sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.2 (hu.2.2 g hgT))
      ((Subgroup.zpowers_le).2 (Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_singleton_iff.1 hga).symm))
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle he)

theorem card_cent_le_of_conj {a t : G} (ht : t ∈ T)
    (he : omegaZ T ⊔ Subgroup.zpowers a = Hconj t (V ⊔ Subgroup.zpowers x)) :
    Nat.card (T ⊓ Subgroup.centralizer {a} : Subgroup G) ≤ 8 := by
  have heq : T ⊓ Subgroup.centralizer ((omegaZ T ⊔ Subgroup.zpowers a : Subgroup G) : Set G) =
      Hconj t (V ⊔ Subgroup.zpowers x) := by
    rw [he]
    calc T ⊓ Subgroup.centralizer ((Hconj t (V ⊔ Subgroup.zpowers x) : Subgroup G) : Set G)
        = Hconj t T ⊓ Hconj t (Subgroup.centralizer
            ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) := by
          rw [Hconj_self_of_mem ht, Hconj_centralizer_sub]
      _ = Hconj t (T ⊓ Subgroup.centralizer ((V ⊔ Subgroup.zpowers x : Subgroup G) : Set G)) :=
          (Hconj_inf _ _ _).symm
      _ = Hconj t (V ⊔ Subgroup.zpowers x) := by rw [c.Ec]
  calc Nat.card (T ⊓ Subgroup.centralizer {a} : Subgroup G)
      ≤ Nat.card (T ⊓ Subgroup.centralizer
          ((omegaZ T ⊔ Subgroup.zpowers a : Subgroup G) : Set G) : Subgroup G) :=
        Subgroup.card_le_of_le cent_le_cent_Ea
    _ = 8 := by rw [heq, Hconj_card, c.EV_card]

theorem card_cent_le_of_dih {a : G} (haT : a ∈ T) (ha2 : a * a = 1) (haZ : a ∉ omegaZ T)
    {D : Subgroup G} (hDT : D ≤ T) (hT : D ⊔ Subgroup.zpowers x = T)
    (hDx : D ⊓ Subgroup.zpowers x = ⊥) (hD : IsDihedral2 D) (hD8 : 8 ≤ Nat.card D) {d : G}
    (hdD : d ∈ D) (hda : d = a ∨ d = a * x) :
    Nat.card (T ⊓ Subgroup.centralizer {a} : Subgroup G) ≤ 8 := by
  obtain ⟨ρ, s, j, hdat⟩ := dihData_of_dih c.base.T_pgroup hDT hD hD8
  have hxa : x * a = a * x := c.base.x_central a haT
  have hd2 : d * d = 1 := by
    rcases hda with rfl | rfl
    · exact ha2
    · calc a * x * (a * x) = a * (x * a) * x := by group
        _ = a * (a * x) * x := by rw [hxa]
        _ = (a * a) * (x * x) := by group
        _ = 1 := by rw [ha2, c.base.x_sq, one_mul]
  have hxZ := c.base.x_mem_Z
  have haZ' : d ∉ omegaZ T := by
    intro hdZ
    apply haZ
    rcases hda with rfl | rfl
    · exact hdZ
    · have := (omegaZ T).mul_mem hdZ hxZ
      rwa [mul_assoc, c.base.x_sq, mul_one] at this
  have hzc : ∀ b ∈ Subgroup.zpowers x, ∀ t ∈ T, b * t = t * b := by
    intro b hb t ht
    rcases zpowers_sq_cases c.base.x_sq hb with rfl | rfl
    · simp
    · exact c.base.x_central t ht
  rcases hdat.inv_cases d hdD hd2 with e | e | ⟨i, e⟩
  · exact (haZ' (by rw [e]; exact (omegaZ T).one_mem)).elim
  · exfalso
    apply haZ'
    refine ⟨hDT hdD, hd2, fun t ht => ?_⟩
    have ht' := ht
    rw [← hT] at ht'
    have hc' : ∀ a' ∈ D, ∀ b ∈ Subgroup.zpowers x, a' * b = b * a' :=
      fun a' ha' b hb => (hzc b hb a' (hDT ha')).symm
    obtain ⟨u, hu, b, hb, rfl⟩ := mem_sup_of_commute hc' ht'
    have h1 : d * u = u * d := by rw [e]; exact hdat.z0_central u hu
    have h2 : d * b = b * d := (hzc b hb d (hDT hdD)).symm
    calc d * (u * b) = (d * u) * b := by group
      _ = (u * d) * b := by rw [h1]
      _ = u * (d * b) := by group
      _ = u * (b * d) := by rw [h2]
      _ = u * b * d := by group
  · have h4 := hdat.card_inf_centralizer_refl_le i
    rw [← e] at h4
    have h8 := card_inf_centralizer_le_of_sup c.base.x_sq c.base.x_central hDT hT hDx (hDT hdD)
    have hle : T ⊓ Subgroup.centralizer {a} ≤ T ⊓ Subgroup.centralizer {d} := by
      rintro t ⟨htT, hta⟩
      refine ⟨htT, ?_⟩
      rcases hda with rfl | rfl
      · exact hta
      · have hta' : t * a = a * t := Subgroup.mem_centralizer_singleton_iff.1 hta
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have hxt : x * t = t * x := c.base.x_central t htT
        calc t * (a * x) = (t * a) * x := by group
          _ = (a * t) * x := by rw [hta']
          _ = a * (t * x) := by group
          _ = a * (x * t) := by rw [hxt]
          _ = a * x * t := by group
    calc Nat.card (T ⊓ Subgroup.centralizer {a} : Subgroup G)
        ≤ Nat.card (T ⊓ Subgroup.centralizer {d} : Subgroup G) := Subgroup.card_le_of_le hle
      _ ≤ 2 * Nat.card (D ⊓ Subgroup.centralizer {d} : Subgroup G) := h8
      _ ≤ 8 := by omega

theorem complement_facts {a : G} (haT : a ∈ T) (ha2 : a * a = 1) (haRd : a ∈ Rd)
    (haR : a ∉ P ⊔ Subgroup.zpowers x) :
    (P ⊔ Subgroup.zpowers a) ⊓ Subgroup.zpowers x = ⊥ ∧
      (P ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers x = Rd ∧ P ⊔ Subgroup.zpowers a ≤ Rd := by
  have hmem : ∀ y ∈ P ⊔ Subgroup.zpowers a, y ∈ P ∨ ∃ p ∈ P, y = a * p := by
    intro y hy
    obtain ⟨a', ha', p, hp, rfl⟩ := mem_sup_zpowers_of_normalIn c.base.P_normal haT hy
    rcases zpowers_sq_cases ha2 ha' with e | e
    · left; rw [e, one_mul]; exact hp
    · right; exact ⟨p, hp, by rw [e]⟩
  have hinf : (P ⊔ Subgroup.zpowers a) ⊓ Subgroup.zpowers x = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyD, hyx⟩
    rcases zpowers_sq_cases c.base.x_sq hyx with h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · exfalso
      rw [h1] at hyD
      rcases hmem _ hyD with hxP | ⟨p, hp, hxp⟩
      · exact c.base.x_not_mem_P hxP
      · apply haR
        have : a = x * p⁻¹ := by rw [hxp]; group
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
          (Subgroup.mem_sup_left (P.inv_mem hp))
  have hmono : P ⊔ Subgroup.zpowers x ≤ (P ⊔ Subgroup.zpowers a) ⊔ Subgroup.zpowers x :=
    sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hleRd : P ⊔ Subgroup.zpowers a ≤ Rd := sup_le c.P_le_Rd ((Subgroup.zpowers_le).2 haRd)
  refine ⟨hinf, le_antisymm (sup_le hleRd ((Subgroup.zpowers_le).2 c.x_mem_Rd)) ?_, hleRd⟩
  intro r hr
  by_cases hrR : r ∈ P ⊔ Subgroup.zpowers x
  · exact hmono hrR
  · have h1 := relIndex_two_mul_mem c.R_index hr (Rd.inv_mem haRd) hrR
      (fun h => haR (by simpa using (P ⊔ Subgroup.zpowers x).inv_mem h))
    have : r = (r * a⁻¹) * a := by group
    rw [this]
    exact Subgroup.mul_mem _ (hmono h1)
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)))

theorem card_cent_le {a : G} (haT : a ∈ T) (ha2 : a * a = 1) (haZ : a ∉ omegaZ T) :
    Nat.card (T ⊓ Subgroup.centralizer {a} : Subgroup G) ≤ 8 := by
  obtain ⟨hEab, hE8, hERd⟩ := c.Ea_facts haT ha2 haZ
  rcases c.Tn with h1 | ⟨F', hF'T, _, _, hFinf, hTeq, hc1, _, _⟩
  · obtain ⟨t, ht, he⟩ := h1 _ _ c.EV_le_Rd hERd c.EV_ab hEab c.EV_card hE8
    exact c.card_cent_le_of_conj ht he
  · have hRdT : Rd = T := c.rd_eq_T hF'T hFinf hTeq hc1
    have haRd : a ∈ Rd := c.inv_mem_Rd haT ha2
    by_cases haR : a ∈ P ⊔ Subgroup.zpowers x
    · by_cases hR : P ⊔ Subgroup.zpowers x = Rd
      · obtain ⟨p, hp, b, hb, rfl⟩ := mem_sup_of_commute c.P_comm_x haR
        have hda : p = p * b ∨ p = p * b * x := by
          rcases zpowers_sq_cases c.base.x_sq hb with rfl | rfl
          · left; rw [mul_one]
          · right; rw [mul_assoc, c.base.x_sq, mul_one]
        exact c.card_cent_le_of_dih haT ha2 haZ c.base.P_le_T (hR.trans hRdT) c.PX_disj
          (c.dih P c.P_le_Rd c.PX_disj hR) c.P8 hp hda
      · have hEaR : omegaZ T ⊔ Subgroup.zpowers a ≤ P ⊔ Subgroup.zpowers x :=
          sup_le c.Z_le_R ((Subgroup.zpowers_le).2 haR)
        obtain ⟨r, hr, he⟩ := c.fuse hR _ _ c.EV_le_R hEaR c.EV_ab hEab c.EV_card hE8
        exact c.card_cent_le_of_conj (c.base.Rd_le_T hr) he
    · obtain ⟨hinf, hsup, hleRd⟩ := c.complement_facts haT ha2 haRd haR
      have hD8 : 8 ≤ Nat.card (P ⊔ Subgroup.zpowers a : Subgroup G) :=
        c.P8.trans (Subgroup.card_le_of_le le_sup_left)
      exact c.card_cent_le_of_dih haT ha2 haZ (hleRd.trans c.base.Rd_le_T) (hsup.trans hRdT) hinf
        (c.dih _ hleRd hinf hsup) hD8 (Subgroup.mem_sup_right (Subgroup.mem_zpowers a)) (Or.inl rfl)

end K1Ctx

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
