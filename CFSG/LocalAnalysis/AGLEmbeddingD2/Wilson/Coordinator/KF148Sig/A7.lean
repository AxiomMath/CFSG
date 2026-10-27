module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.Transport
public import Certificates.Certificate12647

public section

namespace CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.A7

open Equiv Subgroup CFSG.GH74.GLS A7Sig148


theorem stmt_holds : A7Sig148.stmt := of_decide_eq_true Certificates.certificate12647

@[expose] def E0 : Subgroup (alternatingGroup (Fin 7)) where
  carrier := {x | (x : Perm (Fin 7)) ∈ E0l}
  mul_mem' {_ _} ha hb := stmt_holds.1 _ ha _ hb
  one_mem' := List.mem_cons_self ..
  inv_mem' {_} ha := stmt_holds.2.1 _ ha

theorem mem_E0 {x : alternatingGroup (Fin 7)} : x ∈ E0 ↔ (x : Perm (Fin 7)) ∈ E0l := Iff.rfl

theorem card_alt7 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem card_E0 : Nat.card E0 = 9 := by
  have e : ↥E0 ≃ {σ : Perm (Fin 7) // σ ∈ E0l.toFinset} :=
    { toFun := fun x => ⟨(x : alternatingGroup (Fin 7)), List.mem_toFinset.mpr x.2⟩
      invFun := fun σ => ⟨⟨σ.1, Equiv.Perm.mem_alternatingGroup.mpr
          (stmt_holds.2.2.2.1 _ (List.mem_toFinset.mp σ.2))⟩, List.mem_toFinset.mp σ.2⟩
      left_inv := fun x => rfl
      right_inv := fun σ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup stmt_holds.2.2.1]
  rfl

@[expose] noncomputable def toSylow {E : Subgroup (alternatingGroup (Fin 7))}
    (hE : Nat.card E = 9) : Sylow 3 (alternatingGroup (Fin 7)) :=
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  (IsPGroup.of_card (n := 2) (by rw [hE]; norm_num) : IsPGroup 3 E).toSylow (by
    have h1 := Subgroup.card_mul_index E
    rw [hE, card_alt7] at h1
    omega)

theorem coe_toSylow {E : Subgroup (alternatingGroup (Fin 7))} (hE : Nat.card E = 9) :
    (toSylow hE : Subgroup (alternatingGroup (Fin 7))) = E := rfl

theorem exists_map_conj_eq_E0 {E : Subgroup (alternatingGroup (Fin 7))} (hE : Nat.card E = 9) :
    ∃ g : alternatingGroup (Fin 7), E.map (MulAut.conj g).toMonoidHom = E0 := by
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 7)) (toSylow hE)
    (toSylow card_E0)
  refine ⟨g, ?_⟩
  have h := congrArg (fun P : Sylow 3 (alternatingGroup (Fin 7)) =>
    (P : Subgroup (alternatingGroup (Fin 7)))) hg
  simp only [Sylow.coe_subgroup_smul, coe_toSylow] at h
  rw [← h]
  ext y
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rwa [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, inv_smul_smul]
  · intro hy
    exact ⟨_, hy, by rw [MulEquiv.coe_toMonoidHom, ← MulAut.smul_def, smul_inv_smul]⟩

theorem dvd_two_of_dvd_six {n : ℕ} (h6 : n ∣ 6) (h3 : ¬ 3 ∣ n) : n ∣ 2 := by
  have hn : n ≤ 6 := Nat.le_of_dvd (by norm_num) h6
  revert h6 h3
  interval_cases n <;> decide

theorem mem_V_of_mem_core {K : Subgroup (alternatingGroup (Fin 7))}
    {x : alternatingGroup (Fin 7)} (hx : x ∈ E0) (hx1 : x ≠ 1) {w : alternatingGroup (Fin 7)}
    (hw : w ∈ pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set (alternatingGroup (Fin 7))))) :
    w ∈ K ∧ ((w : Perm (Fin 7)) ∈ V1l ∨ (w : Perm (Fin 7)) ∈ V2l) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc, rfl⟩ := hw
  have hcm := mem_inf.1 c.2
  refine ⟨hcm.1, ?_⟩
  have hcomm : (c : alternatingGroup (Fin 7)) * x = x * c := mem_centralizer_singleton_iff.1 hcm.2
  have hord : ¬ 3 ∣ orderOf ((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
    have h1 : orderOf c = orderOf (⟨c, hc⟩ : pPrimeCore 3 _) := (Subgroup.orderOf_mk c hc).symm
    rw [h1]
    intro h3
    have h2 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.pPrimeCore_coprime_card (p := 3)
        (G := ↥(K ⊓ centralizer ({x} : Set (alternatingGroup (Fin 7))))))
    exact h2 (h3.trans (orderOf_dvd_natCard _))
  have hx1' : (x : Perm (Fin 7)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  have hsign : Perm.sign ((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) = 1 :=
    Equiv.Perm.mem_alternatingGroup.mp (c : alternatingGroup (Fin 7)).2
  have hcomm' : ((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) * x =
      x * ((c : alternatingGroup (Fin 7)) : Perm (Fin 7)) := by
    have := congrArg Subtype.val hcomm
    exact this
  obtain ⟨h6, h2⟩ := stmt_holds.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ hx hx1' _ hsign hcomm'
  apply h2
  have hd := dvd_two_of_dvd_six (orderOf_dvd_of_pow_eq_one h6) hord
  exact orderOf_dvd_iff_pow_eq_one.mp hd

theorem mem_of_orb {K : Subgroup (alternatingGroup (Fin 7))}
    (hN : E0 ≤ normalizer (K : Set (alternatingGroup (Fin 7)))) {l : List (Perm (Fin 7))}
    (hl : Orb l) {t : alternatingGroup (Fin 7)} (htK : t ∈ K)
    (htl : (t : Perm (Fin 7)) ∈ l) (ht1 : (t : Perm (Fin 7)) ≠ 1) {u : Perm (Fin 7)}
    (hu : u ∈ l) : ∃ k ∈ K, (k : Perm (Fin 7)) = u := by
  rcases hl _ htl ht1 u hu with rfl | ⟨y, hy, rfl⟩
  · exact ⟨1, K.one_mem, rfl⟩
  · have hyA : y ∈ alternatingGroup (Fin 7) :=
      Equiv.Perm.mem_alternatingGroup.mpr (stmt_holds.2.2.2.1 y hy)
    refine ⟨⟨y, hyA⟩ * t * ⟨y, hyA⟩⁻¹, (mem_normalizer_iff.1 (hN hy) t).1 htK, rfl⟩

theorem eq_bot_of_isPerfect_of_comm {G : Type*} [Group G] {K : Subgroup G}
    (hKp : Group.IsPerfect K) (hc : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : K = ⊥ := by
  have h1 : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hKp
  have h2 : ⁅K, K⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact hc b hb a ha
  rw [← h1, h2]

theorem eq_top_of_E0 {K : Subgroup (alternatingGroup (Fin 7))}
    (hN : E0 ≤ normalizer (K : Set (alternatingGroup (Fin 7)))) (hKp : Group.IsPerfect K)
    (hK1 : K ≠ ⊥)
    (hgen : K ≤ ⨆ (x : alternatingGroup (Fin 7)) (_ : x ∈ E0) (_ : x ≠ 1),
      pPrimeCoreOf 3 (K ⊓ centralizer ({x} : Set (alternatingGroup (Fin 7))))) : K = ⊤ := by
  obtain ⟨hmE, hiE, hndE, hevE, -, hmV1, hiV1, hevV1, hcV1, hmV2, hiV2, hevV2, hcV2, -,
    horb1, horb2, hwords⟩ := stmt_holds
  set S : Set (alternatingGroup (Fin 7)) :=
    {k | k ∈ K ∧ ((k : Perm (Fin 7)) ∈ V1l ∨ (k : Perm (Fin 7)) ∈ V2l)} with hS
  have hKS : K ≤ closure S := by
    refine hgen.trans (iSup_le fun x => iSup_le fun hx => iSup_le fun hx1 => ?_)
    intro w hw
    exact subset_closure (mem_V_of_mem_core hx hx1 hw)
  have hab : ∀ l : List (Perm (Fin 7)), Comm l → (∀ k ∈ S, (k : Perm (Fin 7)) ∈ l) → False := by
    intro l hl hSl
    apply hK1
    apply eq_bot_of_isPerfect_of_comm hKp
    have hpw : S.Pairwise Commute := by
      intro a ha b hb _
      exact Subtype.ext (hl _ (hSl a ha) _ (hSl b hb))
    have hcc := closure_le_centralizer_centralizer S
    intro a ha b hb
    exact Set.centralizer_centralizer_comm_of_comm hpw _ (hcc (hKS ha)) _ (hcc (hKS hb))
  by_cases h1 : ∃ t ∈ K, (t : Perm (Fin 7)) ∈ V1l ∧ (t : Perm (Fin 7)) ≠ 1
  · by_cases h2 : ∃ t ∈ K, (t : Perm (Fin 7)) ∈ V2l ∧ (t : Perm (Fin 7)) ≠ 1
    · obtain ⟨t1, ht1K, ht1l, ht11⟩ := h1
      obtain ⟨t2, ht2K, ht2l, ht21⟩ := h2
      have hgensK : ∀ g ∈ gens, g ∈ K.map (alternatingGroup (Fin 7)).subtype := by
        intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · obtain ⟨k, hk, hkg⟩ := mem_of_orb hN horb1 ht1K ht1l ht11 (List.mem_of_mem_tail hg)
          exact ⟨k, hk, hkg⟩
        · obtain ⟨k, hk, hkg⟩ := mem_of_orb hN horb2 ht2K ht2l ht21 (List.mem_of_mem_tail hg)
          exact ⟨k, hk, hkg⟩
      have hword : ∀ w : List ℕ, wordProd w ∈ K.map (alternatingGroup (Fin 7)).subtype := by
        intro w
        unfold wordProd
        refine list_prod_mem fun g hg => ?_
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
        by_cases hi : i < gens.length
        · rw [List.getD_eq_getElem _ _ hi]
          exact hgensK _ (List.getElem_mem hi)
        · rw [List.getD_eq_default _ _ (by omega)]
          exact Subgroup.one_mem _
      have hA : alternatingGroup (Fin 7) ≤ K.map (alternatingGroup (Fin 7)).subtype := by
        have hle : closure {σ : Perm (Fin 7) | σ.IsThreeCycle} ≤
            K.map (alternatingGroup (Fin 7)).subtype := by
          rw [closure_le]
          intro σ hσ
          obtain ⟨w, -, hw⟩ := hwords σ hσ
          rw [← hw]
          exact hword w
        rwa [Equiv.Perm.closure_three_cycles_eq_alternating] at hle
      rw [eq_top_iff]
      intro x _
      obtain ⟨k, hk, hkx⟩ := hA x.2
      rwa [← Subtype.ext hkx]
    · refine (hab V1l hcV1 fun k hk => ?_).elim
      rcases hk.2 with h | h
      · exact h
      · by_contra hk1
        exact h2 ⟨k, hk.1, h, fun h' => hk1 (h' ▸ List.mem_cons_self ..)⟩
  · refine (hab V2l hcV2 fun k hk => ?_).elim
    rcases hk.2 with h | h
    · by_contra hk1
      exact h1 ⟨k, hk.1, h, fun h' => hk1 (h' ▸ List.mem_cons_self ..)⟩
    · exact h

theorem inspectSig148_alt7 : InspectSig148 (alternatingGroup (Fin 7)) (· = ⊤) := by
  rw [inspectSig148_iff]
  intro E K hEK
  obtain ⟨g, hg⟩ := exists_map_conj_eq_E0 hEK.1
  have h := hEK.map (MulAut.conj g)
  rw [hg] at h
  have htop := eq_top_of_E0 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2
  rw [eq_top_iff]
  intro x _
  have hx : (MulAut.conj g) x ∈ K.map (MulAut.conj g).toMonoidHom := by
    rw [htop]; exact mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  rwa [← (MulAut.conj g).injective hyx]

end CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF148Sig.A7
