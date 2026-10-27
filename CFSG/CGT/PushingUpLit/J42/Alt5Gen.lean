module

public import CFSG.CGT.PushingUpLit.J42.Alt5Len
public import CFSG.CGT.PushingUpLit.J42.Alt5Sylow
public import CFSG.CGT.PushingUpLit.SolK.GenFourA8

public section

namespace CFSG.CGT.PushingUpLit.SolK

open CFSG CFSG.Assembly CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit.BHS CFSG.Quasithin
  CFSG.Quasithin.G6 CFSG.GH74 Equiv Equiv.Perm

theorem mem_closure_pairVec {d : ℕ} (j : Fin d) (s : Finset (Fin d)) :
    ∀ v : ↥(coreMod d), (∀ i, i ∉ s → i ≠ j → vcoord v i = 0) →
      v ∈ Subgroup.closure (Set.range fun b : Fin d => pairVec b j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro v hv
    have hv1 : v = 1 := by
      refine vcoord_ext fun i => ?_
      by_cases hij : i = j
      · subst hij
        have hsum := sum_vcoord v
        rw [Finset.sum_eq_single i (fun b _ hb => hv b (Finset.notMem_empty b) hb)
          (fun h => absurd (Finset.mem_univ i) h)] at hsum
        rw [hsum, vcoord_one]
      · rw [hv i (Finset.notMem_empty i) hij, vcoord_one]
    rw [hv1]
    exact Subgroup.one_mem _
  | insert a s ha ih =>
    intro v hv
    by_cases haj : a = j
    · subst haj
      exact ih v fun i his hij => hv i (by simp [his, hij]) hij
    · by_cases hva : vcoord v a = 1
      · have hmem : pairVec a j ∈ Subgroup.closure (Set.range fun b : Fin d => pairVec b j) :=
          Subgroup.subset_closure ⟨a, rfl⟩
        have hv' : v * pairVec a j ∈
            Subgroup.closure (Set.range fun b : Fin d => pairVec b j) := by
          refine ih _ fun i his hij => ?_
          rw [vcoord_mul, vcoord_pairVec]
          by_cases hia : i = a
          · subst hia
            simp [hva, hij]
            decide
          · rw [hv i (by simp [his, hia]) hij]
            simp [hia, hij]
        have hpp : pairVec a j * pairVec a j = 1 := by rw [pairVec_mul, pairVec_self]
        have hv2 : v = (v * pairVec a j) * pairVec a j := by
          rw [mul_assoc, hpp, mul_one]
        rw [hv2]
        exact Subgroup.mul_mem _ hv' hmem
      · have hva0 : vcoord v a = 0 := by
          generalize vcoord v a = c at hva ⊢
          revert c
          decide
        refine ih v fun i his hij => ?_
        by_cases hia : i = a
        · subst hia
          exact hva0
        · exact hv i (by simp [his, hia]) hij

theorem closure_pairVec_eq_top {d : ℕ} (j : Fin d) :
    Subgroup.closure (Set.range fun b : Fin d => pairVec b j) = ⊤ :=
  eq_top_iff.2 fun v _ =>
    mem_closure_pairVec j Finset.univ v fun i hi _ => absurd (Finset.mem_univ i) hi

theorem sectionalTwoRankLE_four_of_elem {V : Type*} [Group V] [Finite V] (hV : Nat.card V = 64)
    (hE : ∀ P : Subgroup V, Nat.card ↥P = 32 → ∃ x ∈ P, x * x ≠ 1)
    (hgen : ∃ s : Finset V, s.card ≤ 4 ∧ Subgroup.closure (s : Set V) = ⊤) :
    SectionalTwoRankLE V 4 := by
  classical
  intro P hP
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).1 hP
  have hdvd : Nat.card P ∣ Nat.card V := Subgroup.card_subgroup_dvd_card P
  have hm6 : m ≤ 6 := by
    rw [hm, hV] at hdvd
    have : 2 ^ m ∣ 2 ^ 6 := by simpa using hdvd
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 this
  by_cases hm4 : m ≤ 4
  · obtain ⟨t, -, ht, hcard⟩ := exists_gen_of_start P ∅ (by simp) 0 (by simp)
    refine ⟨t, ?_, ht⟩
    rw [hm] at hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 (by simpa using hcard)
    omega
  · by_cases hm5 : m = 5
    · subst hm5
      have hP32 : Nat.card P = 32 := by rw [hm]; norm_num
      obtain ⟨x, hxP, hx2⟩ := hE P hP32
      have hord : orderOf x ∣ 2 ^ 5 := by
        have : orderOf x ∣ Nat.card P := by
          have := orderOf_dvd_natCard (⟨x, hxP⟩ : P)
          rwa [Subgroup.orderOf_mk] at this
        rw [hP32] at this
        norm_num
        exact this
      have hx4 : 4 ≤ orderOf x := by
        obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
        by_contra hlt
        have hk1 : k ≤ 1 := by
          by_contra hk2
          have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
          omega
        have hx2' : x ^ 2 = 1 := by
          have : orderOf x ∣ 2 := by
            rw [hkx]
            interval_cases k <;> simp
          exact orderOf_dvd_iff_pow_eq_one.1 this
        exact hx2 (by rw [← pow_two]; exact hx2')
      have h4 : 2 ^ (1 + 1) ≤ Nat.card (Subgroup.closure (({x} : Finset V) : Set V)) := by
        rw [Finset.coe_singleton, ← Subgroup.zpowers_eq_closure, Nat.card_zpowers]
        simpa using hx4
      obtain ⟨t, -, ht, hcard⟩ := exists_gen_of_start P {x} (by simpa using hxP) 1 h4
      refine ⟨t, ?_, ht⟩
      rw [hP32] at hcard
      have : 2 ^ (t.card + 1) ≤ 2 ^ 5 := by simpa using hcard
      have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
      omega
    · have hm6' : m = 6 := by omega
      subst hm6'
      have hPtop : P = ⊤ := Subgroup.eq_top_of_card_eq P (by rw [hm, hV]; norm_num)
      obtain ⟨s, hs, hsP⟩ := hgen
      exact ⟨s, hs, by rw [hsP, hPtop]⟩

theorem closure_eq_top_of_image {H : Type*} [Group H] (T : Subgroup H) (s : Set ↥T)
    (h : Subgroup.closure (T.subtype '' s) = T) : Subgroup.closure s = ⊤ := by
  apply Subgroup.map_injective T.subtype_injective
  rw [MonoidHom.map_closure, h, Subgroup.map_top, Subgroup.range_subtype]

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)

namespace SolCfg

include S

theorem closure_eq_TOf_alt (hT : TightData S) (hQe : QElem S) (hR : RSmall S) {w r : G}
    (hw : w ∈ S.D.W) (hr : r ∈ rOf M X) (hcard : (vsupp (S.D.β ⟨w, hw⟩)).card = 4)
    (hKM : ¬ CGOf (w * r) ≤ M) :
    ∃ t₁ t₂ q₀ : G, t₁ ∈ TOf M (w * r) ∧ t₂ ∈ TOf M (w * r) ∧ q₀ ∈ TOf M (w * r) ∧
      Subgroup.closure ({t₁, t₂, q₀} : Set G) = TOf M (w * r) := by
  classical
  have hRbot := S.rOf_eq_bot hT hQe hR hw hr hcard hKM
  have hQW := S.pCoreOf_eq_W_of_rOf_bot hRbot
  have hF : FourGroup (vsupp (S.D.β ⟨w, hw⟩)) (S.TN (w * r)) :=
    S.fourGroup_theta hw hr hcard (TOf_le_M M _) (TOf_le_C M _) (isPGroup_TOf M _)
      (fun k hk u hu => normalized_TOf M (w * r) hk hu)
  have hN : S.TN (w * r) ≠ ⊥ := S.TN_ne_bot hT hQe hR hw hr hcard hKM
  have h4 : Nat.card ↥(S.TN (w * r)) = 4 := hF.card_eq_four hcard hN
  generalize vsupp (S.D.β ⟨w, hw⟩) = I at hF hcard
  obtain ⟨a, haI⟩ : I.Nonempty := Finset.card_pos.1 (by omega)
  have hIc : Iᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
  obtain ⟨j, hj⟩ := Finset.card_eq_one.1 hIc
  have hout : ∀ b, b ∉ I → b = j := fun b hb => by
    have : b ∈ Iᶜ := Finset.mem_compl.2 hb
    rw [hj] at this
    exact Finset.mem_singleton.1 this
  have hjI : j ∉ I := by
    have : j ∈ Iᶜ := by rw [hj]; exact Finset.mem_singleton_self j
    exact Finset.mem_compl.1 this
  obtain ⟨σ₁, hσ₁N, hσ₁1⟩ : ∃ σ ∈ S.TN (w * r), σ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hN (eq_bot_iff.2 fun σ hσ => Subgroup.mem_bot.2 (hcon σ hσ))
  obtain ⟨σ₂, hσ₂N, hσ₂1, hσ₂ne⟩ := hF.exists_ne hcard hN σ₁
  obtain ⟨u₁, hu₁T, hu₁⟩ := S.mem_TN.1 hσ₁N
  obtain ⟨u₂, hu₂T, hu₂⟩ := S.mem_TN.1 hσ₂N
  let q0W : ↥S.D.W := S.D.β.symm (pairVec a j)
  have hq0β : S.D.β q0W = pairVec a j := S.D.β.apply_symm_apply _
  have hq0T : (q0W : G) ∈ TOf M (w * r) :=
    S.Q_le_TOf hT (S.mul_mem_Q hw hr) (S.W_le_Q q0W.2)
  refine ⟨(u₁ : G), (u₂ : G), (q0W : G), hu₁T, hu₂T, hq0T, ?_⟩
  set H : Subgroup G := Subgroup.closure ({(u₁ : G), (u₂ : G), (q0W : G)} : Set G) with hH
  have hu₁H : (u₁ : G) ∈ H := Subgroup.subset_closure (by simp)
  have hu₂H : (u₂ : G) ∈ H := Subgroup.subset_closure (by simp)
  have hq0H : (q0W : G) ∈ H := Subgroup.subset_closure (by simp)
  have hHT : H ≤ TOf M (w * r) := by
    rw [hH, Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl <;> assumption
  refine le_antisymm hHT ?_
  have hHθle : (H.subgroupOf M).map S.θ ≤ S.TN (w * r) := by
    intro σ hσ
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hσ
    exact S.mem_TN.2 ⟨m, hHT (Subgroup.mem_subgroupOf.1 hm), rfl⟩
  have hσ₁H : σ₁ ∈ (H.subgroupOf M).map S.θ :=
    Subgroup.mem_map.2 ⟨u₁, Subgroup.mem_subgroupOf.2 hu₁H, hu₁⟩
  have hσ₂H : σ₂ ∈ (H.subgroupOf M).map S.θ :=
    Subgroup.mem_map.2 ⟨u₂, Subgroup.mem_subgroupOf.2 hu₂H, hu₂⟩
  have hcard3 : 3 ≤ Nat.card ↥((H.subgroupOf M).map S.θ) := by
    have h3 : ({1, σ₁, σ₂} : Set (Perm (Fin (2 * 2 + 1)))).ncard = 3 :=
      Set.ncard_eq_three.2 ⟨1, σ₁, σ₂, hσ₁1.symm, hσ₂1.symm, hσ₂ne.symm, rfl⟩
    calc 3 = ({1, σ₁, σ₂} : Set (Perm (Fin (2 * 2 + 1)))).ncard := h3.symm
      _ ≤ (((H.subgroupOf M).map S.θ : Subgroup _) : Set (Perm (Fin (2 * 2 + 1)))).ncard :=
          Set.ncard_le_ncard (by
            intro y hy
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
            rcases hy with rfl | rfl | rfl
            · exact Subgroup.one_mem _
            · exact hσ₁H
            · exact hσ₂H) (Set.toFinite _)
      _ = Nat.card ↥((H.subgroupOf M).map S.θ) := (Nat.card_coe_set_eq _).symm
  have hdvd : Nat.card ↥((H.subgroupOf M).map S.θ) ∣ Nat.card ↥(S.TN (w * r)) :=
    Subgroup.card_dvd_of_le hHθle
  rw [h4] at hdvd
  have hc4 : Nat.card ↥((H.subgroupOf M).map S.θ) = 4 := by
    have hle4 : Nat.card ↥((H.subgroupOf M).map S.θ) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    rcases (by omega : Nat.card ↥((H.subgroupOf M).map S.θ) = 3 ∨
        Nat.card ↥((H.subgroupOf M).map S.θ) = 4) with h | h
    · rw [h] at hdvd
      omega
    · exact h
  have hθeq : (H.subgroupOf M).map S.θ = S.TN (w * r) :=
    Subgroup.eq_of_le_of_card_ge hHθle (by rw [h4, hc4])
  have hqb : ∀ b, ∃ w' : ↥S.D.W, (w' : G) ∈ H ∧ S.D.β w' = pairVec b j := by
    intro b
    by_cases hbI : b ∈ I
    · obtain ⟨σ, hσN, hσa⟩ := hF.transitive hcard hN haI hbI
      have hσH : σ ∈ (H.subgroupOf M).map S.θ := hθeq ▸ hσN
      obtain ⟨h, hhH, hhσ⟩ := Subgroup.mem_map.1 hσH
      have hhH' : (h : G) ∈ H := Subgroup.mem_subgroupOf.1 hhH
      have hW : (h : G) * (q0W : G) * (h : G)⁻¹ ∈ S.D.W := S.W_normalized h.2 q0W.2
      refine ⟨⟨(h : G) * (q0W : G) * (h : G)⁻¹, hW⟩, ?_, ?_⟩
      · exact H.mul_mem (H.mul_mem hhH' hq0H) (H.inv_mem hhH')
      · have h1 := S.θ_spec h q0W hW
        rw [h1, hq0β, hhσ, coreAct_pairVec, hσa, hF.fix σ hσN j hjI]
    · have hbj : b = j := hout b hbI
      subst hbj
      exact ⟨1, H.one_mem, by rw [map_one, pairVec_self]⟩
  have hWH : ∀ w' : ↥S.D.W, (w' : G) ∈ H := by
    intro w'
    let K0 : Subgroup ↥(coreMod (2 * 2 + 1)) :=
      (H.subgroupOf S.D.W).map S.D.β.toMonoidHom
    have hK0 : Subgroup.closure (Set.range fun b : Fin (2 * 2 + 1) => pairVec b j) ≤ K0 := by
      rw [Subgroup.closure_le]
      rintro _ ⟨b, rfl⟩
      obtain ⟨w'', hw''H, hw''β⟩ := hqb b
      exact ⟨w'', Subgroup.mem_subgroupOf.2 hw''H, hw''β⟩
    rw [closure_pairVec_eq_top] at hK0
    obtain ⟨w'', hw''H, hw''β⟩ := (hK0 (Subgroup.mem_top (S.D.β w')) : S.D.β w' ∈ K0)
    have hww : w'' = w' := S.D.β.injective hw''β
    rw [← hww]
    exact Subgroup.mem_subgroupOf.1 hw''H
  intro t ht
  have htM : t ∈ M := TOf_le_M M _ ht
  have hθt : S.θ ⟨t, htM⟩ ∈ S.TN (w * r) := S.mem_TN.2 ⟨⟨t, htM⟩, ht, rfl⟩
  rw [← hθeq] at hθt
  obtain ⟨h, hhH, hhθ⟩ := Subgroup.mem_map.1 hθt
  have hhH' : (h : G) ∈ H := Subgroup.mem_subgroupOf.1 hhH
  have hM' : t * (h : G)⁻¹ ∈ M := M.mul_mem htM (M.inv_mem h.2)
  have hq : t * (h : G)⁻¹ ∈ pCoreOf 2 M := by
    refine S.mem_Q_of_theta_eq_one hR hM' ?_
    have : (⟨t * (h : G)⁻¹, hM'⟩ : ↥M) = ⟨t, htM⟩ * h⁻¹ := rfl
    rw [this, map_mul, map_inv, hhθ, mul_inv_cancel]
  have hqH : t * (h : G)⁻¹ ∈ H := by
    rw [hQW] at hq
    exact hWH ⟨_, hq⟩
  have hteq : t = (t * (h : G)⁻¹) * (h : G) := by group
  rw [hteq]
  exact H.mul_mem hqH hhH'

theorem gen4_degree_five_of_alt (hT : TightData S) (hR : RSmall S)
    (hA : ∀ m : ↥M, S.θ m ∈ alternatingGroup (Fin (2 * 2 + 1))) (hC : ¬ CentInM S) :
    SectionalTwoRankLE G 4 := by
  classical
  have hQe : QElem S := SolCfg.RSmall.elem S hR
  obtain ⟨w, hw, r, hr, hcard, hKM⟩ := S.exists_len_four_of_not_centInM hT hA hC
  obtain ⟨P, hP⟩ := S.exists_sylow_eq_TOf_alt hT hQe hR hA hw hr hcard hKM
  refine SectionalTwoRankLE.of_sylow P ?_
  rw [hP]
  have hRbot := S.rOf_eq_bot hT hQe hR hw hr hcard hKM
  refine sectionalTwoRankLE_four_of_elem (S.card_TOf_eq hT hQe hR hw hr hcard hKM) ?_ ?_
  · intro P' hP'
    by_contra hcon
    push Not at hcon
    set E : Subgroup G := P'.map (TOf M (w * r)).subtype with hE
    have hsq : ∀ x ∈ E, x * x = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (hcon y hy)
    have hEA : CFSG.Open.IsElemAbelian 2 E := by
      refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
      · have ha : (a : G) * (a : G) = 1 := hsq a a.2
        have hb : (b : G) * (b : G) = 1 := hsq b b.2
        have hab : ((a : G) * (b : G)) * ((a : G) * (b : G)) = 1 := hsq (a * b) (E.mul_mem a.2 b.2)
        have h1 : ((a : G) * (b : G))⁻¹ = (a : G) * (b : G) := inv_eq_of_mul_eq_one_right hab
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, inv_eq_of_mul_eq_one_right hb] at h1
        exact h1.symm
      · rw [pow_two]
        exact hsq x hx
    have hET : E ≤ TOf M (w * r) := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have h1 := (S.elem_le_of_len_four hT hw hr hcard hET hEA).1
    have h2 : Nat.card ↥E = 32 := by
      rw [hE, Subgroup.card_map_of_injective (TOf M (w * r)).subtype_injective, hP']
    have h3 := S.card_pCoreOf_of_rOf_bot hRbot
    omega
  · obtain ⟨t₁, t₂, q₀, h₁, h₂, h₃, hcl⟩ := S.closure_eq_TOf_alt hT hQe hR hw hr hcard hKM
    refine ⟨{⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨q₀, h₃⟩}, Finset.card_le_three.trans (by norm_num), ?_⟩
    refine closure_eq_top_of_image _ _ ?_
    have himg : (TOf M (w * r)).subtype ''
        ((({⟨t₁, h₁⟩, ⟨t₂, h₂⟩, ⟨q₀, h₃⟩} : Finset ↥(TOf M (w * r)))) : Set ↥(TOf M (w * r))) =
        {t₁, t₂, q₀} := by
      simp [Set.image_insert_eq]
    rw [himg]
    exact hcl

end SolCfg

end CFSG.CGT.PushingUpLit.SolK
