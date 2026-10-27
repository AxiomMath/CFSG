module

public import CFSG.GF2Type.Smith1980Orth.GoodT
public import CFSG.GF2Type.Smith1980Orth.FourW4

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1980Orth

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S4
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem OrthData.exists_conj_mem_Q_of_width_eq_four [IsSimpleGroup G]
    (hAS : S14.AschbacherSmithW4Input) (O : OrthData S) (hw : S.width = 4) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra hW
  push Not at hW
  obtain ⟨e⟩ := hAS G S hw (fun P hP => (O.card_le_of_isPGroup_of_width_eq_four hw P hP).trans
    (by norm_num)) hW
  have h := FS77.factorization_card_timmesfeldPSU (m := 6) (by norm_num)
  rw [← Nat.card_congr e.toEquiv] at h
  exact O.factorization_ne_fifteen hw (by rw [h])

namespace W4

variable (S) in
@[expose] noncomputable def Cb (k t : S.O) : Subgroup S.O :=
  S.Mbar ⊓ centralizer ((zpowers k ⊔ zpowers t : Subgroup S.O) : Set S.O)

variable {k t : S.O}

theorem comm_of_mem_Cb {c x : S.O} (hc : c ∈ Cb S k t) (hx : x ∈ zpowers k ⊔ zpowers t) :
    x * c = c * x :=
  mem_centralizer_iff.mp hc.2 x hx

theorem k_comm_of_mem_Cb {c : S.O} (hc : c ∈ Cb S k t) : k * c = c * k :=
  comm_of_mem_Cb hc (mem_sup_left (mem_zpowers k))

theorem t_comm_of_mem_Cb {c : S.O} (hc : c ∈ Cb S k t) : t * c = c * t :=
  comm_of_mem_Cb hc (mem_sup_right (mem_zpowers t))

theorem apply_mem_Vt_of_mem_Cb {g : G} (H : Hyp4 S g) {c : S.O} (hc : c ∈ Cb S k t) {u : S.Qt}
    (hu : u ∈ Vt S g t) : (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u ∈ Vt S g t := by
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hc.1
  exact apply_mem_Vt H.conj_mem (t_comm_of_mem_Cb hc).symm hu

section Gen

variable (htt : t * t = 1) (hk3 : k ^ 3 = 1) (htk : t * k * t⁻¹ = k⁻¹)
include htt hk3 htk

omit hk3 in
theorem conj_zpow_k (n : ℤ) : t * k ^ n * t⁻¹ = k ^ (-n) := by
  rw [← conj_zpow, htk, inv_zpow']

omit htt htk in
theorem zpow_eq_one_of_eq_neg {n : ℤ} (h : k ^ n = k ^ (-n)) : k ^ n = 1 := by
  have h2 : k ^ (2 * n) = 1 := by
    rw [two_mul, zpow_add]
    nth_rewrite 2 [h]
    rw [← zpow_add, add_neg_cancel, zpow_zero]
  have h3 : k ^ (3 * n) = 1 := by
    rw [zpow_mul, show k ^ (3 : ℤ) = 1 by exact_mod_cast hk3, one_zpow]
  calc k ^ n = k ^ (3 * n) * (k ^ (2 * n))⁻¹ := by
        rw [← zpow_neg, ← zpow_add]
        congr 1
        ring
    _ = 1 := by rw [h2, h3, inv_one, mul_one]

theorem mem_sup_cases {s : S.O} (hs : s ∈ zpowers k ⊔ zpowers t) :
    ∃ n : ℤ, s = k ^ n ∨ s = k ^ n * t := by
  have hle : zpowers t ≤ normalizer ((zpowers k : Subgroup S.O) : Set S.O) :=
    zpowers_le.mpr (S4.mem_normalizer_of_conj_le fun p hp => by
      obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hp
      rw [conj_zpow_k htt htk n]
      exact zpow_mem (mem_zpowers k) _)
  have hs' : s ∈ ((zpowers k : Subgroup S.O) : Set S.O) *
      ((zpowers t : Subgroup S.O) : Set S.O) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ hle]
    exact hs
  obtain ⟨o, ho, m, hm, rfl⟩ := Set.mem_mul.mp hs'
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp ho
  rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp hm with rfl | rfl
  · exact ⟨n, Or.inl (mul_one _)⟩
  · exact ⟨n, Or.inr rfl⟩

theorem eq_one_or_eq_of_comm {s : S.O} (hs : s ∈ zpowers k ⊔ zpowers t) (hst : s * t = t * s) :
    s = 1 ∨ s = t := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  obtain ⟨n, rfl | rfl⟩ := mem_sup_cases htt hk3 htk hs
  · left
    have h1 : t * k ^ n * t⁻¹ = k ^ n := by rw [← hst, mul_inv_cancel_right]
    rw [conj_zpow_k htt htk] at h1
    exact zpow_eq_one_of_eq_neg hk3 h1.symm
  · right
    have h2 : t * (k ^ n * t) = t * k ^ n * t⁻¹ := by rw [hti, mul_assoc]
    rw [mul_assoc, htt, mul_one, h2, conj_zpow_k htt htk] at hst
    rw [zpow_eq_one_of_eq_neg hk3 hst, one_mul]

theorem t_not_mem_Cb (hk1 : k ≠ 1) : t ∉ Cb S k t := by
  intro h
  have h1 := k_comm_of_mem_Cb h
  have h2 : k = k⁻¹ := by rw [← htk, ← h1, mul_inv_cancel_right]
  have hkk : k * k = 1 := by
    nth_rewrite 2 [h2]
    exact mul_inv_cancel k
  have h3 : k ^ 3 = k := by rw [pow_three, hkk, mul_one]
  exact hk1 (h3.symm.trans hk3)

variable (hdec : ∀ {x : S.O}, x ∈ S.Mbar → ∃ s ∈ zpowers k ⊔ zpowers t, ∃ c ∈ Cb S k t,
  x = s * c)
include hdec

theorem exists_mem_Cb_of_comm {x : S.O} (hxM : x ∈ S.Mbar) (hxt : x * t = t * x) :
    ∃ c ∈ Cb S k t, x = c ∨ x = t * c := by
  obtain ⟨s, hs, c, hc, rfl⟩ := hdec hxM
  have hct := t_comm_of_mem_Cb hc
  have hst : s * t = t * s := by
    have h2 : s * t * c = t * s * c := by
      calc s * t * c = s * (t * c) := mul_assoc _ _ _
        _ = s * (c * t) := by rw [hct]
        _ = s * c * t := (mul_assoc _ _ _).symm
        _ = t * (s * c) := hxt
        _ = t * s * c := (mul_assoc _ _ _).symm
    exact mul_right_cancel h2
  rcases eq_one_or_eq_of_comm htt hk3 htk hs hst with rfl | rfl
  · exact ⟨c, hc, Or.inl (one_mul c)⟩
  · exact ⟨c, hc, Or.inr rfl⟩

theorem conj_k_cases {x : S.O} (hxM : x ∈ S.Mbar) : x * k * x⁻¹ = k ∨ x * k * x⁻¹ = k⁻¹ := by
  obtain ⟨s, hs, c, hc, rfl⟩ := hdec hxM
  have hck : c * k * c⁻¹ = k := by rw [← k_comm_of_mem_Cb hc, mul_inv_cancel_right]
  have e : s * c * k * (s * c)⁻¹ = s * (c * k * c⁻¹) * s⁻¹ := by group
  rw [e, hck]
  obtain ⟨n, rfl | rfl⟩ := mem_sup_cases htt hk3 htk hs
  · left
    rw [(Commute.zpow_self k n).eq, mul_inv_cancel_right]
  · right
    have e2 : k ^ n * t * k * (k ^ n * t)⁻¹ = k ^ n * (t * k * t⁻¹) * (k ^ n)⁻¹ := by group
    rw [e2, htk, ((Commute.refl k).inv_right.zpow_left n).eq, mul_inv_cancel_right]

end Gen

theorem Nbar_le_zpowers {g : G} (H : Hyp4 S g) (ht : t ∈ S.Lbar g) (hirr : ¬ S.IsReducible)
    (hk3 : k ^ 3 = 1) (htk : t * k * t⁻¹ = k⁻¹)
    (hdec : ∀ {x : S.O}, x ∈ S.Mbar → ∃ s ∈ zpowers k ⊔ zpowers t, ∃ c ∈ Cb S k t,
      x = s * c) :
    Nbar S g t ≤ zpowers t := by
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (S6.self_mem_Nbar H ht).2
  set F : Submodule (ZMod 2) S.Qt := Submodule.span (ZMod 2)
    {v | ∃ u ∈ Vt S g t, ∃ n : ℤ, v = ((k ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u} with hF
  have hgen : ∀ {x : S.O}, x ∈ S.Mbar → ∀ u ∈ Vt S g t, ∀ n : ℤ,
      (x : S.Qt ≃ₗ[ZMod 2] S.Qt) (((k ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u) ∈ F := by
    intro x hx u hu n
    obtain ⟨s, hs, c, hc, rfl⟩ := hdec hx
    have hcu := apply_mem_Vt_of_mem_Cb H hc hu
    have hck : c * k ^ n = k ^ n * c :=
      ((Commute.zpow_left (k_comm_of_mem_Cb hc) n).eq).symm
    obtain ⟨j, rfl | rfl⟩ := mem_sup_cases htt hk3 htk hs
    · refine Submodule.subset_span ⟨(c : S.Qt ≃ₗ[ZMod 2] S.Qt) u, hcu, j + n, ?_⟩
      have e : k ^ j * c * k ^ n = k ^ (j + n) * c := by
        rw [mul_assoc, hck, ← mul_assoc, ← zpow_add]
      calc ((k ^ j * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) (((k ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
          = ((k ^ j * c * k ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := rfl
        _ = ((k ^ (j + n) * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by rw [e]
        _ = _ := rfl
    · refine Submodule.subset_span ⟨(c : S.Qt ≃ₗ[ZMod 2] S.Qt) u, hcu, j - n, ?_⟩
      have h1 : t * k ^ n = k ^ (-n) * t := by
        rw [← conj_zpow_k htt htk n]
        group
      have e : k ^ j * t * c * k ^ n = k ^ (j - n) * (t * c) := by
        calc k ^ j * t * c * k ^ n = k ^ j * t * (c * k ^ n) := by group
          _ = k ^ j * t * (k ^ n * c) := by rw [hck]
          _ = k ^ j * (t * k ^ n) * c := by group
          _ = k ^ j * (k ^ (-n) * t) * c := by rw [h1]
          _ = k ^ (j - n) * (t * c) := by rw [sub_eq_add_neg, zpow_add]; group
      calc ((k ^ j * t * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
            (((k ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
          = ((k ^ j * t * c * k ^ n : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := rfl
        _ = ((k ^ (j - n) * (t * c) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by rw [e]
        _ = ((k ^ (j - n) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)
              ((t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u)) := rfl
        _ = _ := by rw [htV _ hcu]
  have hinv : ∀ m : S.M, ∀ v ∈ F, ((S.ρ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v ∈ F := by
    intro m v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨u, hu, n, rfl⟩ := hv
      exact hgen (MonoidHom.mem_range.mpr ⟨m, rfl⟩) u hu n
    | zero => simp
    | add u w _ _ hu hw => rw [map_add]; exact add_mem hu hw
    | smul a u _ hu => rw [map_smul]; exact Submodule.smul_mem _ a hu
  have haF : S.cl (g * S.z * g⁻¹) ∈ F :=
    Submodule.subset_span ⟨_, cl_a_mem_Vt ht, 0, by simp⟩
  have hFtop : F = ⊤ := by
    by_contra hne
    refine hirr ⟨F, fun h => ?_, hne, hinv⟩
    rw [h] at haF
    exact cl_conj_z_ne_zero S H.conj_mem H.conj_ne ((Submodule.mem_bot _).mp haF)
  intro n hn
  have hnM : n ∈ S.Mbar := S4.Rbar_le_Mbar hn.1
  have hnt : n * t = t * n := S4.commute_of_mem_Rbar H.conj_mem hn.1
  obtain ⟨c, hc, hnc⟩ := exists_mem_Cb_of_comm htt hk3 htk hdec hnM hnt
  have hcV : ∀ u ∈ Vt S g t, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u = u := by
    intro u hu
    rcases hnc with rfl | rfl
    · exact hn.2 u hu
    · calc (c : S.Qt ≃ₗ[ZMod 2] S.Qt) u
          = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u) :=
            (htV _ (apply_mem_Vt_of_mem_Cb H hc hu)).symm
        _ = u := hn.2 u hu
  have hcF : ∀ v ∈ F, (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨u, hu, m, rfl⟩ := hv
      have hck : c * k ^ m = k ^ m * c :=
        ((Commute.zpow_left (k_comm_of_mem_Cb hc) m).eq).symm
      calc (c : S.Qt ≃ₗ[ZMod 2] S.Qt) (((k ^ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u)
          = ((c * k ^ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := rfl
        _ = ((k ^ m * c : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) u := by rw [hck]
        _ = ((k ^ m : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) u) := rfl
        _ = _ := by rw [hcV u hu]
    | zero => simp
    | add u w _ _ hu hw => rw [map_add, hu, hw]
    | smul a u _ hu => rw [map_smul, hu]
  have hc1 : c = 1 := Subtype.ext (LinearEquiv.ext fun v => hcF v (hFtop ▸ Submodule.mem_top))
  rcases hnc with rfl | rfl
  · rw [hc1]
    exact one_mem _
  · rw [hc1, mul_one]
    exact mem_zpowers t

theorem card_RmodN_dvd {g : G} (H : Hyp4 S g) (ht : t ∈ S.Lbar g) (hirr : ¬ S.IsReducible)
    (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) (htk : t * k * t⁻¹ = k⁻¹)
    (hdec : ∀ {x : S.O}, x ∈ S.Mbar → ∃ s ∈ zpowers k ⊔ zpowers t, ∃ c ∈ Cb S k t,
      x = s * c) :
    Nat.card (RmodN S g t) ∣ Nat.card (Cb S k t) := by
  have htt : t * t = 1 := S4.mul_self_of_mem_Lbar S H.conj_mem ht
  have hN := Nbar_le_zpowers H ht hirr hk3 htk hdec
  have htV : ∀ v ∈ Vt S g t, (t : S.Qt ≃ₗ[ZMod 2] S.Qt) v = v := (S6.self_mem_Nbar H ht).2
  have hmem : ∀ y : (Cb S k t).subgroupOf (Rbar S g t),
      resV H.conj_mem t (y : Rbar S g t) ∈ RmodN S g t := fun y => by
    rw [← range_resV H.conj_mem t]
    exact ⟨_, rfl⟩
  let f : (Cb S k t).subgroupOf (Rbar S g t) → RmodN S g t := fun y => ⟨_, hmem y⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h0 : resV H.conj_mem t ((a : Rbar S g t)⁻¹ * (b : Rbar S g t)) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact congrArg Subtype.val hab
    have h1 := (resV_eq_one_iff H.conj_mem _).mp h0
    have hC : (((a : Rbar S g t)⁻¹ * (b : Rbar S g t) : Rbar S g t) : S.O) ∈ Cb S k t :=
      mul_mem (inv_mem (mem_subgroupOf.mp a.2)) (mem_subgroupOf.mp b.2)
    rcases (Setting.mem_zpowers_iff_of_mul_self htt).mp (hN h1) with h | h
    · have h2 : (a : Rbar S g t)⁻¹ * (b : Rbar S g t) = 1 := Subtype.ext h
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    · exfalso
      rw [h] at hC
      exact t_not_mem_Cb htt hk3 htk hk1 hC
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    rw [← range_resV H.conj_mem t] at he
    obtain ⟨r, rfl⟩ := he
    have hrt := S4.commute_of_mem_Rbar H.conj_mem r.2
    obtain ⟨c, hc, hrc⟩ := exists_mem_Cb_of_comm htt hk3 htk hdec (S4.Rbar_le_Mbar r.2) hrt
    have htR : t ∈ Rbar S g t := Lbar_le_Rbar ht ht
    have hcR : c ∈ Rbar S g t := by
      rcases hrc with h | h
      · rw [← h]
        exact r.2
      · have e : c = t⁻¹ * (r : S.O) := by rw [h, inv_mul_cancel_left]
        rw [e]
        exact mul_mem (inv_mem htR) r.2
    refine ⟨⟨⟨c, hcR⟩, mem_subgroupOf.mpr hc⟩, Subtype.ext (LinearEquiv.ext fun v => ?_)⟩
    apply Subtype.ext
    change ((resV H.conj_mem t ⟨c, hcR⟩ v : Vt S g t) : S.Qt) = ((resV H.conj_mem t r v :
      Vt S g t) : S.Qt)
    rw [coe_resV_apply, coe_resV_apply]
    change (c : S.Qt ≃ₗ[ZMod 2] S.Qt) v = (((r : Rbar S g t) : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt) v
    rcases hrc with h | h
    · rw [h]
    · rw [h]
      change _ = (t : S.Qt ≃ₗ[ZMod 2] S.Qt) ((c : S.Qt ≃ₗ[ZMod 2] S.Qt) v)
      rw [htV _ (apply_mem_Vt_of_mem_Cb H hc v.2)]
  let ψ : (Cb S k t).subgroupOf (Rbar S g t) →* Cb S k t :=
    { toFun := fun y => ⟨((y : Rbar S g t) : S.O), mem_subgroupOf.mp y.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := by
    intro a b h
    have h' : ((a : Rbar S g t) : S.O) = ((b : Rbar S g t) : S.O) :=
      congrArg (fun x : Cb S k t => (x : S.O)) h
    exact Subtype.ext (Subtype.ext h')
  calc Nat.card (RmodN S g t) = Nat.card ((Cb S k t).subgroupOf (Rbar S g t)) :=
        (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    _ ∣ Nat.card (Cb S k t) := Subgroup.card_dvd_of_injective ψ hψ

theorem card_RmodN_of_a6Case {g : G} {H : Hyp4 S g} {C : Cons311 S g} {ht : t ∈ S.Lbar g}
    {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} (hA : A6Case H C ht ht1 hVQ) :
    Nat.card (RmodN S g t) = 360 := by
  have hβ := beta_isAlt H C ht ht1 hVQ
  have hnd := beta_nondegenerate H C ht ht1 hVQ
  obtain ⟨-, -, hi, -⟩ := S45Q.commutator_isometryGroup_four hβ hnd hA.finrank_eq
  obtain ⟨Φ⟩ := S45Q.nonempty_isometryGroup_equiv_perm hβ hnd hA.finrank_eq
  rw [hA.eq_commutator]
  set Sp := TauCeti.BilinForm.isometryGroup (beta H C ht ht1 hVQ)
  have hSp : Nat.card Sp = 720 := by
    rw [Nat.card_congr Φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hm := (⁅Sp, Sp⁆.subgroupOf Sp).card_mul_index
  change _ * ⁅Sp, Sp⁆.relIndex Sp = _ at hm
  rw [Nat.card_congr (subgroupOfEquivOfLe (commutator_le_self Sp)).toEquiv, hi, hSp] at hm
  omega

theorem not_pgl25Case_of_dvd {g : G} {H : Hyp4 S g} {C : Cons311 S g} {ht : t ∈ S.Lbar g}
    {ht1 : t ≠ 1} {hVQ : ¬ V S g t ≤ S.Qa g} {n : ℕ} (hdvd : Nat.card (RmodN S g t) ∣ n)
    (hn : ¬ 5 ∣ n) : ¬ PGL25Case H C ht ht1 hVQ := fun hP => by
  have h15 := S45Q.fifteen_dvd_card_of_transitive hP.finrank_eq (aV_ne_zero H ht) hP.transitive
  exact hn ((Nat.dvd_trans (by norm_num : 5 ∣ 15) h15).trans hdvd)

theorem goodT_of_width_eq_four (hCE : CentralExtInput.{0}) {g : G} (H : Hyp4 S g)
    (hNo : NoA2 S g) (C : Cons311 S g) (ht : t ∈ S.Lbar g) (ht1 : t ≠ 1)
    (hR : Rbar S g t ≠ S.Lbar g) (hirr : ¬ S.IsReducible) (hnoAll : S11.NoA2All S)
    (hk1 : k ≠ 1) (hk3 : k ^ 3 = 1) (htk : t * k * t⁻¹ = k⁻¹)
    (hdec : ∀ {x : S.O}, x ∈ S.Mbar → ∃ s ∈ zpowers k ⊔ zpowers t, ∃ c ∈ Cb S k t,
      x = s * c)
    (hC : Nat.card (Cb S k t) ∣ 72 ∨ Nat.card (Cb S k t) ∣ 120)
    (hPGL : Nat.card (Cb S k t) ∣ 120 → ∀ hVQ : ¬ V S g t ≤ S.Qa g,
      ¬ PGL25Case H C ht ht1 hVQ) :
    GoodT S g t ∧ finrank (ZMod 2) (Vt S g t) = S.width := by
  have hN : Nbar S g t = zpowers t :=
    le_antisymm (Nbar_le_zpowers H ht hirr hk3 htk hdec) (zpowers_le.mpr (S6.self_mem_Nbar H ht))
  have hdvd := card_RmodN_dvd H ht hirr hk1 hk3 htk hdec
  rcases timmesfeld_4_5 H hNo C ht ht1 with h | hL | ⟨hVQ, hSp | hA | hΩ | hP⟩
  · exact absurd h hR
  · exact (S7.timmesfeld_7_1 H hNo C ht ht1 hN hL).elim
  · exact (S7.not_spCase H hNo C ht ht1 hN hCE hSp).elim
  · exfalso
    rw [card_RmodN_of_a6Case hA] at hdvd
    rcases hC with h | h
    · have := Nat.le_of_dvd (by norm_num) (hdvd.trans h)
      omega
    · have := Nat.le_of_dvd (by norm_num) (hdvd.trans h)
      omega
  · exact ⟨⟨⟨H, hNo, C, ht, ht1, hR, hVQ, hN, hirr, hnoAll⟩, hΩ⟩,
      (S7.width_eq_finrank_of_omegaCase H hNo C ht ht1 hN hΩ).symm⟩
  · exfalso
    by_cases h72 : Nat.card (Cb S k t) ∣ 72
    · exact not_pgl25Case_of_dvd (hdvd.trans h72) (by norm_num) hP
    · exact hPGL (hC.resolve_left h72) hVQ hP

@[expose] def PGL25W4Free : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (O : OrthData S),
    S.width = 4 → ¬ timmesfeldPlusType O.q → ¬ S.IsReducible → S11.NoA2All S →
    ∀ (g : G) (H : Hyp4 S g), NoA2 S g → ∀ (C : Cons311 S g) (t k : S.O) (ht : t ∈ S.Lbar g)
      (ht1 : t ≠ 1) (hVQ : ¬ V S g t ≤ S.Qa g), k ∈ S.Mbar → k ≠ 1 → k ^ 3 = 1 →
      t * k * t⁻¹ = k⁻¹ →
      (∀ {x : S.O}, x ∈ S.Mbar → ∃ s ∈ zpowers k ⊔ zpowers t, ∃ c ∈ Cb S k t, x = s * c) →
      Rbar S g t ≠ S.Lbar g → Nbar S g t = zpowers t → ¬ PGL25Case H C ht ht1 hVQ

end W4

end CFSG.GF2Type.Smith1980Orth
