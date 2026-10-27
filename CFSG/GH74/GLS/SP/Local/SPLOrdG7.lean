module

public import CFSG.GH74.GLS.SP.Local.SPLOrdG6
public import CFSG.GH74.GLS.SP.Local.SPLOrdZ0
public import CFSG.GH74.GLS.SP.Local.SPLOrdAr
public import CFSG.GH74.GLS.SP.Local.SPLOrdCl
public import CFSG.GH74.GLS.SP.Local.SPLOrdG4

public section

open Subgroup DihedralGroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.GH74.GLS CFSG.GH74.BNPair
open CFSG.GH74.GLS.LU.Local CFSG.GH74.GLS.SP
open scoped Pointwise commutatorElement

namespace CFSG.GH74.GLS.SP.Local

section G7

variable {G : Type} [Group G] [Finite G] (D : SPLNot3 G)

@[expose] def SPLNot3.P1 (D : SPLNot3 G) : Set G := {a | ∃ g ∈ D.K₁, a = g * D.t * g⁻¹}

@[expose] def SPLNot3.P2 (D : SPLNot3 G) : Set G :=
  {a | a ∈ D.K₁ ⊔ D.K₂ ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ D.z}

omit [Finite G] in
theorem Utset_eq : Utset D = D.P1 ∪ D.P2 := rfl

@[expose] noncomputable def diagI (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    ↥D.K₁ →* ↥D.I :=
  (diagHom D hs).codRestrict D.I (by
    intro k
    rw [I_eq_diag D hs hc]
    exact ⟨k, rfl⟩)

theorem diagI_surjective (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Function.Surjective (diagI D hs hc) := by
  intro γ
  have : (γ : G) ∈ (diagHom D hs).range := by rw [← I_eq_diag D hs hc]; exact γ.2
  obtain ⟨k, hk⟩ := this
  exact ⟨k, Subtype.ext hk⟩

theorem ker_diagI_card (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card (diagI D hs hc).ker = 2 := by
  have hker : (diagI D hs hc).ker = (diagHom D hs).ker := MonoidHom.ker_codRestrict _ _ _
  rw [hker]
  exact ker_diagHom D hs

theorem sq_eq_z_iff (hs : SPLSetup D.toSPLNot0) {k : G} (hk : k ∈ D.K₁) :
    k * k = D.z ↔ orderOf (k * (D.t * k * D.t⁻¹)) = 2 := by
  have htt := t_mul_t D hs
  have hzz := z_mul_z D hs
  have hz1 := z_ne_one D hs
  have hu : D.t * k * D.t⁻¹ ∈ D.K₂ := t_conj_K₁ D hs k hk
  have hcomm : k * (D.t * k * D.t⁻¹) = (D.t * k * D.t⁻¹) * k := hs.comps.comm k hk _ hu
  have hsq : (k * (D.t * k * D.t⁻¹)) * (k * (D.t * k * D.t⁻¹)) =
      (k * k) * ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹)) := by
    calc (k * (D.t * k * D.t⁻¹)) * (k * (D.t * k * D.t⁻¹))
        = k * ((D.t * k * D.t⁻¹) * k) * (D.t * k * D.t⁻¹) := by group
      _ = k * (k * (D.t * k * D.t⁻¹)) * (D.t * k * D.t⁻¹) := by rw [← hcomm]
      _ = (k * k) * ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹)) := by group
  have hk1 : ¬ (k * (D.t * k * D.t⁻¹) = 1 ∧ k * k = D.z) := by
    rintro ⟨h1, h2⟩
    have h3 : k = (D.t * k * D.t⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hkK₂ : k ∈ D.K₂ := by rw [h3]; exact D.K₂.inv_mem hu
    have hkz : k ∈ zpowers D.z := by rw [← hs.comps.inf_eq]; exact ⟨hk, hkK₂⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hkz
    rcases zpow_z_cases D hs j with h4 | h4
    · rw [h4] at hj
      rw [← hj, one_mul] at h2
      exact hz1 h2.symm
    · rw [h4] at hj
      rw [← hj, hzz] at h2
      exact hz1 h2.symm
  constructor
  · intro hkk
    have hsq' : (k * (D.t * k * D.t⁻¹)) * (k * (D.t * k * D.t⁻¹)) = 1 := by
      rw [hsq, hkk]
      have e : (D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹) = D.t * (k * k) * D.t⁻¹ := by group
      rw [e, hkk]
      have : D.t * D.z * D.t⁻¹ = D.z := t_conj_z D hs
      rw [this, hzz]
    refine orderOf_eq_prime (by rw [pow_two]; exact hsq') ?_
    intro h1
    exact hk1 ⟨h1, hkk⟩
  · intro hord
    have hsq' : (k * (D.t * k * D.t⁻¹)) * (k * (D.t * k * D.t⁻¹)) = 1 := by
      have := pow_orderOf_eq_one (k * (D.t * k * D.t⁻¹))
      rw [hord, pow_two] at this
      exact this
    have hK₂ : k * k ∈ D.K₂ := by
      have h' : (k * k) * ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹)) = 1 := by rw [← hsq]; exact hsq'
      have : k * k = ((D.t * k * D.t⁻¹) * (D.t * k * D.t⁻¹))⁻¹ := eq_inv_of_mul_eq_one_left h'
      rw [this]
      exact D.K₂.inv_mem (D.K₂.mul_mem hu hu)
    have hk2 : k * k ∈ zpowers D.z := by
      rw [← hs.comps.inf_eq]; exact ⟨D.K₁.mul_mem hk hk, hK₂⟩
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hk2
    rcases zpow_z_cases D hs j with h1 | h1
    · exfalso
      rw [h1] at hj
      have hone : k * (D.t * k * D.t⁻¹) = 1 := by
        rcases K₁_inv_unique D hs hk hj.symm with h2 | h2
        · rw [h2]; group
        · rw [h2, t_conj_z D hs, hzz]
      rw [hone, orderOf_one] at hord
      exact absurd hord (by norm_num)
    · rw [h1] at hj; exact hj.symm

theorem card_sq_eq_z (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card {u : ↥D.K₁ // (u : G) * u = D.z} = 2 * Nat.card {γ : ↥D.I // orderOf γ = 2} := by
  have h := card_subtype_comp (diagI D hs hc) (diagI_surjective D hs hc) (fun γ => orderOf γ = 2)
  rw [ker_diagI_card D hs hc] at h
  rw [← h]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun u => ?_)
  rw [sq_eq_z_iff D hs u.2, ← Subgroup.orderOf_coe (diagI D hs hc u)]
  rfl

theorem card_P1 (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.P1 = Nat.card ↥D.I := by
  have h := tclass_card D.K₁ D.K₂ D.z D.t hs.comps.comm hs.comps.inf_eq hs.syl.z_inv
    (t_mul_t D hs) (z_comm_t D hs) (t_not_mem_K D hs) (t_conj_K₁ D hs) (t_conj_K₂ D hs)
  have h2 := card_K₁_eq D hs hc
  have : Nat.card ↥D.P1 = Nat.card {a : G // ∃ g ∈ D.K₁, a = g * D.t * g⁻¹} := rfl
  omega

theorem card_P2 (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥D.P2 = 2 * Nat.card {γ : ↥D.I // orderOf γ = 2} ^ 2 := by
  have h := Jone_card D.K₁ D.K₂ D.z D.t hs.comps.comm hs.comps.inf_eq hs.syl.z_inv
    (t_mul_t D hs) (z_comm_t D hs) (t_not_mem_K D hs) (t_conj_K₁ D hs) (t_conj_K₂ D hs)
    (fun a ha haa => K₁_inv_unique D hs ha haa)
  rw [card_sq_eq_z D hs hc] at h
  have : Nat.card ↥D.P2 = Nat.card {a : G // a ∈ D.K₁ ⊔ D.K₂ ∧ a * a = 1 ∧ a ≠ 1 ∧ a ≠ D.z} := rfl
  rw [this]
  nlinarith [h]

theorem P1_disjoint_P2 (hs : SPLSetup D.toSPLNot0) : Disjoint D.P1 D.P2 := by
  rw [Set.disjoint_left]
  rintro a ⟨g, hg, rfl⟩ ⟨hK, -⟩
  apply t_not_mem_K D hs
  have hgK : g ∈ D.K₁ ⊔ D.K₂ := Subgroup.mem_sup_left hg
  have : D.t = g⁻¹ * (g * D.t * g⁻¹) * g := by group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hgK) hK) hgK

theorem card_Utset (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card ↥(Utset D) = Nat.card ↥D.I + 2 * Nat.card {γ : ↥D.I // orderOf γ = 2} ^ 2 := by
  rw [Utset_eq, Nat.card_coe_set_eq, Set.ncard_union_eq (P1_disjoint_P2 D hs) (Set.toFinite _)
    (Set.toFinite _), ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq, card_P1 D hs hc,
    card_P2 D hs hc]

omit [Finite G] in
theorem orderOf_of_mem_Utset (hs : SPLSetup D.toSPLNot0) {a : G} (ha : a ∈ Utset D) :
    orderOf a = 2 := by
  rcases ha with ⟨g, -, rfl⟩ | ⟨-, haa, ha1, -⟩
  · rw [CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj
      (show IsConj D.t (g * D.t * g⁻¹) from isConj_iff.mpr ⟨g, rfl⟩).symm]
    exact hs.syl.t_ord
  · exact orderOf_eq_two_of_sq a haa ha1

theorem card_tclass_inter_C (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) :
    Nat.card {b : G // IsConj D.t b ∧ b ∈ centralizer ({D.z} : Set G)} =
      Nat.card ↥D.I + 2 * Nat.card {γ : ↥D.I // orderOf γ = 2} ^ 2 := by
  rw [← card_Utset D hs hc]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun b => ?_)
  constructor
  · rintro ⟨hb, hbC⟩
    have hb2 : orderOf b = 2 := by
      rw [← CFSG.ShultStronglyClosedTI.InvolutionCounting.orderOf_eq_of_isConj hb]
      exact hs.syl.t_ord
    exact (Ut_iff D hs hc hbC hb2).mp hb
  · intro hb
    have hbC : b ∈ D.C := Utset_le_C D hs hb
    exact ⟨(Ut_iff D hs hc hbC (orderOf_of_mem_Utset D hs hb)).mpr hb, hbC⟩

theorem card_Zt (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) {ι : ℕ}
    (hι : ι = Nat.card {γ : ↥D.I // orderOf γ = 2}) (hιd : ι * D.d = Nat.card ↥D.I) :
    Nat.card {a : G // IsConj D.z a ∧ a ∈ D.Ct} = D.d / 2 + ι := by
  have h := card_conj_inter_comm D.z D.t
  rw [card_tclass_inter_C D hs hc, ← hι] at h
  have hCt : Nat.card ↥(centralizer ({D.t} : Set G)) = Nat.card ↥D.I * (2 * D.d) * Nat.card ↥D.F :=
    card_Ct D hs hc
  have hC : Nat.card ↥(centralizer ({D.z} : Set G)) = 2 * (2 * Nat.card ↥D.I ^ 2) * Nat.card ↥D.F := by
    have e1 : Nat.card ↥(centralizer ({D.z} : Set G)) = Nat.card ↥D.C := rfl
    rw [e1, card_C D hs hc, card_Kt D hs, card_K D hs hc]
  rw [hCt, hC] at h
  have hZ : Nat.card {a : G // IsConj D.z a ∧ a ∈ centralizer ({D.t} : Set G)} =
      Nat.card {a : G // IsConj D.z a ∧ a ∈ D.Ct} := rfl
  rw [hZ] at h
  set n := Nat.card ↥D.I with hn
  set f := Nat.card ↥D.F with hf
  set Z := Nat.card {a : G // IsConj D.z a ∧ a ∈ D.Ct} with hZdef
  have hfpos : 0 < f := Nat.card_pos
  have hnpos : 0 < n := Nat.card_pos
  have hd4 := d_pos D hs
  have hdev : 2 ∣ D.d := dvd_two_d D hs
  have h2 : D.d * (n + 2 * ι ^ 2) = 2 * n * Z := by
    have h3 : (2 * n * f) * (D.d * (n + 2 * ι ^ 2)) = (2 * n * f) * (2 * n * Z) := by
      calc (2 * n * f) * (D.d * (n + 2 * ι ^ 2)) = n * (2 * D.d) * f * (n + 2 * ι ^ 2) := by ring
        _ = 2 * (2 * n ^ 2) * f * Z := h
        _ = (2 * n * f) * (2 * n * Z) := by ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
  have h4 : D.d * ι = n := by rw [mul_comm]; exact hιd
  have h5 : n * (D.d + 2 * ι) = n * (2 * Z) := by
    calc n * (D.d + 2 * ι) = D.d * n + 2 * (D.d * ι) * ι := by rw [h4]; ring
      _ = D.d * (n + 2 * ι ^ 2) := by rw [← h4]; ring
      _ = 2 * n * Z := h2
      _ = n * (2 * Z) := by ring
  have h6 := Nat.eq_of_mul_eq_mul_left hnpos h5
  obtain ⟨m, hm⟩ := hdev
  omega

structure ChatData (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d]
    (hd : 2 ∣ D.d) where
  g₀ : G
  hzrel : D.z * g₀ * D.z⁻¹ = g₀⁻¹
  ht : g₀ ^ (D.d / 2) = D.t
  Φ : (↥D.I ⋊[dihAct (sigmaAut D hc) (sigmaAut_sq D hc) hd] DihedralGroup D.d) ≃* ↥D.Chat
  hΦr : ∀ (i : ↥D.I) (k : ZMod D.d), (Φ ⟨i, r k⟩ : G) = i * g₀ ^ k.val
  hΦsr : ∀ (i : ↥D.I) (k : ZMod D.d), (Φ ⟨i, sr k⟩ : G) = i * (D.z * g₀ ^ k.val)

theorem nonempty_chatData (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d]
    (hd : 2 ∣ D.d) : Nonempty (ChatData D hs hc hd) := by
  obtain ⟨g₀, hzrel, ht, Φ, hΦr, hΦsr⟩ := chat_iso D hs hc hd
  exact ⟨⟨g₀, hzrel, ht, Φ, hΦr, hΦsr⟩⟩

variable {D}

theorem conj_z_of_mem_Z0 (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d]
    {hd : 2 ∣ D.d} (cd : ChatData D hs hc hd) {w : ↥D.I ⋊[dihAct (sigmaAut D hc)
      (sigmaAut_sq D hc) hd] DihedralGroup D.d}
    (hw : w ∈ Z0 (sigmaAut D hc) (sigmaAut_sq D hc) hd) : IsConj D.z (cd.Φ w : G) := by
  rcases hw with ⟨k, hk, rfl⟩ | ⟨i, hi1, hii, rfl⟩
  · rw [cd.hΦsr]
    have hkv : k.val % 2 = 0 := by rw [← par_eq_val_mod_two hd]; exact hk
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k.val = 2 * m := ⟨k.val / 2, by omega⟩
    have := isConj_z_refl D cd.hzrel (m : ℤ)
    have e : cd.g₀ ^ k.val = cd.g₀ ^ (2 * (m : ℤ)) := by
      rw [hm, ← zpow_natCast]; push_cast; rfl
    rw [e]
    simpa using this
  · rw [cd.hΦr]
    have hval : ((D.d / 2 : ℕ) : ZMod D.d).val = D.d / 2 :=
      ZMod.val_natCast_of_lt (by have := d_pos D hs; omega)
    rw [hval, cd.ht]
    have hi' : (i : G) ∈ D.I := i.2
    have hii' : (i : G) * i = 1 := by
      have := congrArg Subtype.val hii
      simpa using this
    have hi1' : (i : G) ≠ 1 := fun h => hi1 (Subtype.ext h)
    exact isConj_z_it D hs hc hi' hii' hi1'

theorem marks_iff (hs : SPLSetup D.toSPLNot0) (hc : SPL2Ct D.toSPLNot2) [NeZero D.d]
    {hd : 2 ∣ D.d} (cd : ChatData D hs hc hd) {ι : ℕ}
    (hι : ι = Nat.card {γ : ↥D.I // orderOf γ = 2}) (hιd : ι * D.d = Nat.card ↥D.I) (b : G) :
    (IsConj D.z b ∧ b ∈ D.Ct) ↔
      ∃ w ∈ Z0 (sigmaAut D hc) (sigmaAut_sq D hc) hd, (cd.Φ w : G) = b := by
  set S : Set G := {b | IsConj D.z b ∧ b ∈ D.Ct} with hS
  set T : Set G := (fun w => (cd.Φ w : G)) '' Z0 (sigmaAut D hc) (sigmaAut_sq D hc) hd with hT
  have hTS : T ⊆ S := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨conj_z_of_mem_Z0 hs hc cd hw, Chat_le_Ct D hs hc (cd.Φ w).2⟩
  have hinj : Function.Injective (fun w => (cd.Φ w : G)) := fun w w' h =>
    cd.Φ.injective (Subtype.ext h)
  have hTcard : T.ncard = D.d / 2 + ι := by
    rw [hT, Set.ncard_image_of_injective _ hinj, ← Nat.card_coe_set_eq,
      card_Z0 (sigmaAut D hc) (sigmaAut_sq D hc) hd, hι]
  have hScard : S.ncard = D.d / 2 + ι := by
    rw [← Nat.card_coe_set_eq]
    exact card_Zt D hs hc hι hιd
  have hST : T = S := Set.eq_of_subset_of_ncard_le hTS (by rw [hTcard, hScard]) (Set.toFinite _)
  constructor
  · intro hb
    have : b ∈ S := hb
    rw [← hST] at this
    obtain ⟨w, hw, hwb⟩ := this
    exact ⟨w, hw, hwb⟩
  · rintro ⟨w, hw, rfl⟩
    exact hTS ⟨w, hw, rfl⟩

end G7

end CFSG.GH74.GLS.SP.Local
