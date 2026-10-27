module

public import CFSG.LocalAnalysis.QuasithinUnique.EscapingLocalAux

public section

namespace CFSG.QuasithinUnique

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem le_pCoreOf_of_le_normalizer {N K : Subgroup G} (hNK : N ≤ K)
    (hK : K ≤ Subgroup.normalizer (N : Set G)) (hN : IsPGroup 2 N) : N ≤ pCoreOf 2 K :=
  CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 N K hNK
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hK) hN

omit [Finite G] in
private theorem eq_one_of_isPGroup_of_odd_orderOf {P : Subgroup G} (hP : IsPGroup 2 P) {y : G}
    (hy : y ∈ P) (hodd : Odd (orderOf y)) : y = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP ⟨y, hy⟩
  have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_coe (⟨y, hy⟩ : P)).trans hk
  rw [hk'] at hodd
  have hk0 : k = 0 := by
    by_contra hne
    exact (Nat.not_even_iff_odd.mpr hodd) (Nat.even_pow.mpr ⟨even_two, hne⟩)
  rw [hk0, pow_zero] at hk'
  exact orderOf_eq_one_iff.mp hk'

private theorem isPGroup_two_of_forall_odd_orderOf {C : Subgroup G}
    (h : ∀ y ∈ C, Odd (orderOf y) → y = 1) : IsPGroup 2 C := by
  apply IsPGroup.of_card (n := (Nat.card C).primeFactorsList.length)
  apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
  intro prime hprime hdvd
  by_contra hne
  have : Fact prime.Prime := ⟨hprime⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' prime hdvd
  have hyodd : Odd (orderOf (y : G)) := by
    rw [Subgroup.orderOf_coe, hy]
    exact hprime.odd_of_ne_two hne
  have hy1 : (y : G) = 1 := h y y.2 hyodd
  have horder : orderOf y = 1 := by
    rw [← Subgroup.orderOf_coe y, hy1, orderOf_one]
  exact hprime.ne_one (hy.symm.trans horder)

omit [Finite G] in
theorem isSylowTwoOf_of_le {T M : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTM : T ≤ M) :
    IsSylowTwoOf T M := by
  refine ⟨hTM, hT.2.1, fun h2 => hT.2.2 ?_⟩
  change 2 ∣ T.relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact h2.trans (Subgroup.relIndex_dvd_index_of_le hTM)

theorem charTwo_of_pCore_centralizer_le {M N : Subgroup G} (hM : CharTwo M) (hNM : N ≤ M)
    (hC : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ N) : CharTwo N := by
  set P := pCoreOf 2 M with hP
  set Q := pCoreOf 2 N with hQ
  have hP2 : IsPGroup 2 P := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 M
  have hQ2 : IsPGroup 2 Q := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 N
  have hNP : N ≤ Subgroup.normalizer (P : Set G) :=
    hNM.trans (CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M)
  have hNQ : N ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 N
  have hQN : Q ≤ N := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 N
  have hNCQ : N ≤ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) :=
    hNQ.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer Q)
  have hR : P ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    refine le_pCoreOf_of_le_normalizer hC ?_ (hP2.to_le inf_le_left)
    exact CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf N P _ hNP hNCQ
  have hodd : ∀ y ∈ N ⊓ Subgroup.centralizer (Q : Set G), Odd (orderOf y) → y = 1 := by
    intro y hy hyodd
    obtain ⟨a, ha⟩ := hP2.exists_card_eq
    have hcop : (Nat.card P).Coprime (Nat.card (Subgroup.zpowers y)) := by
      rw [ha, Nat.card_zpowers]
      exact Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hyodd)
    have hyzp : Subgroup.zpowers y ≤ Subgroup.centralizer (Q : Set G) :=
      Subgroup.zpowers_le.mpr hy.2
    have hcentral := CFSG.RankThreeCoreUniqueness.Helpers.ambient_subgroup_axb_centralizer_le 2
      Nat.prime_two Q (Subgroup.zpowers y) P hQ2 hP2 hcop (hQN.trans hNP)
      (Subgroup.zpowers_le.mpr (hNP hy.1)) hyzp
      (hyzp.trans (Subgroup.centralizer_le hR)) (Subgroup.mem_zpowers y)
    have hyP : y ∈ P := hM ⟨hNM hy.1, hcentral⟩
    exact eq_one_of_isPGroup_of_odd_orderOf hP2 hyP hyodd
  have hC2 : IsPGroup 2 (N ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) :=
    isPGroup_two_of_forall_odd_orderOf hodd
  exact le_pCoreOf_of_le_normalizer inf_le_left
    (CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf N N _
      Subgroup.le_normalizer hNCQ) hC2

omit [Finite G] in
theorem CharTwo.of_normal_of_centralizer_le {K H : Subgroup G} (hK : CharTwo K) (hKH : K ≤ H)
    (hn : (K.subgroupOf H).Normal)
    (hC : H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ≤ K) : CharTwo H := by
  intro x hx
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn
  have hKQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer ((CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 K).trans hKH)
      (hHK.trans
        (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_localGroup_le_normalizer_pCoreOf 2 K))
      (CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 K)
  have hxc : x ∈ Subgroup.centralizer (pCoreOf 2 K : Set G) :=
    Subgroup.centralizer_le (by exact_mod_cast hKQ) hx.2
  exact hKQ (hK ⟨hC hx, hxc⟩)

private theorem charTwo_map_subtype_of_isSubnormal {K : Subgroup G} (hK : CharTwo K)
    {Y : Subgroup K} (hY : Y.IsSubnormal) : CharTwo (Y.map K.subtype) := by
  induction hY with
  | top =>
    rw [Subgroup.map_top, Subgroup.range_subtype]
    exact hK
  | step Y Z hYZ hZ hN ih =>
    refine ih.of_normal (Subgroup.map_mono hYZ) ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_mono hYZ)]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hYZ] at hN
    exact (Subgroup.map_mono hN).trans (Subgroup.le_normalizer_map _)

theorem CharTwo.of_isSubnormal {K X : Subgroup G} (hK : CharTwo K) (hXK : X ≤ K)
    (hX : (X.subgroupOf K).IsSubnormal) : CharTwo X := by
  have := charTwo_map_subtype_of_isSubnormal hK hX
  rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXK] at this

theorem charTwo_of_centralizer_sup_le_of_le_normalizer {M X H : Subgroup G} (hM : CharTwo M)
    (hXM : X ≤ M) (hX : IsPGroup 2 X)
    (hH : X ⊔ (M ⊓ Subgroup.centralizer (X : Set G)) ≤ H)
    (hHN : H ≤ M ⊓ Subgroup.normalizer (X : Set G)) : CharTwo H := by
  have hXH : X ≤ H := le_sup_left.trans hH
  have hKH : M ⊓ Subgroup.centralizer (X : Set G) ≤ H := le_sup_right.trans hH
  have hHM : H ≤ M := hHN.trans inf_le_left
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := hHN.trans inf_le_right
  have hHK : H ≤ Subgroup.normalizer
      ((M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.common_normalizer_le_normalizer_inf H M _
      (hHM.trans Subgroup.le_normalizer)
      (hHX.trans (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_centralizer X))
  have hXQ : X ≤ pCoreOf 2 H := le_pCoreOf_of_le_normalizer hXH hHX hX
  refine CharTwo.of_normal_of_centralizer_le (hM.inf_centralizer hXM hX) hKH
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hHK) ?_
  intro x hx
  exact ⟨hHM hx.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hXQ) hx.2⟩

theorem charTwo_inf_iInf_normalizer {M : Subgroup G} (hM : CharTwo M) :
    ∀ (n : ℕ) (B : Fin n → Subgroup G), (∀ i, IsPGroup 2 (B i)) → (∀ i, B i ≤ M) →
      (∀ i j, i ≤ j → B j ≤ Subgroup.normalizer (B i : Set G)) →
      CharTwo (M ⊓ ⨅ i, Subgroup.normalizer (B i : Set G)) := by
  intro n
  induction n with
  | zero =>
    intro B _ _ _
    simpa using hM
  | succ n ih =>
    intro B h2 hBM hBN
    have h' := ih (fun i => B i.castSucc) (fun i => h2 _) (fun i => hBM _)
      (fun i j hij => hBN _ _ (Fin.castSucc_le_castSucc_iff.mpr hij))
    have hlast : B (Fin.last n) ≤
        M ⊓ ⨅ i : Fin n, Subgroup.normalizer (B i.castSucc : Set G) :=
      le_inf (hBM _) (le_iInf fun i => hBN i.castSucc (Fin.last n) (Fin.castSucc_lt_last i).le)
    have hstep := h'.inf_normalizer hlast (h2 _)
    have heq : M ⊓ ⨅ i : Fin (n + 1), Subgroup.normalizer (B i : Set G) =
        (M ⊓ ⨅ i : Fin n, Subgroup.normalizer (B i.castSucc : Set G)) ⊓
          Subgroup.normalizer (B (Fin.last n) : Set G) := by
      apply le_antisymm
      · refine le_inf (le_inf inf_le_left (le_iInf fun i => ?_))
          (inf_le_right.trans (iInf_le _ (Fin.last n)))
        exact inf_le_right.trans (iInf_le _ i.castSucc)
      · refine le_inf (inf_le_left.trans inf_le_left) (le_iInf fun i => ?_)
        refine Fin.lastCases ?_ (fun j => ?_) i
        · exact inf_le_right
        · exact (inf_le_left.trans inf_le_right).trans (iInf_le _ j)
    rwa [heq]

theorem charTwo_of_eq_iInf_normalizer {M H : Subgroup G} (hM : CharTwo M) (hHM : H ≤ M) {n : ℕ}
    (B : Fin n → Subgroup G) (hB : ∀ i, IsPGroup 2 (B i))
    (hBN : ∀ i j, i ≤ j → B j ≤ H ⊓ Subgroup.normalizer (B i : Set G))
    (hH : H = ⨅ i, M ⊓ Subgroup.normalizer (B i : Set G)) : CharTwo H := by
  have heq : H = M ⊓ ⨅ i, Subgroup.normalizer (B i : Set G) := by
    apply le_antisymm
    · refine le_inf hHM (le_iInf fun i => ?_)
      have hi : H ≤ M ⊓ Subgroup.normalizer (B i : Set G) := by
        rw [hH]
        exact iInf_le (fun i => M ⊓ Subgroup.normalizer (B i : Set G)) i
      exact hi.trans inf_le_right
    · rw [hH]
      exact le_iInf fun i => inf_le_inf_left M (iInf_le _ i)
  rw [heq]
  exact charTwo_inf_iInf_normalizer hM n B hB
    (fun i => ((hBN i i le_rfl).trans inf_le_left).trans hHM)
    (fun i j hij => (hBN i j hij).trans inf_le_right)

omit [Finite G] in
theorem charTwo_normalizer_of_normal_in_sylow
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T U : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hU : IsPGroup 2 U) (hU1 : U ≠ ⊥) (hUT : U ≤ T)
    (hUn : (U.subgroupOf T).Normal) : CharTwo (Subgroup.normalizer (U : Set G)) := by
  have hTU : T ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUT).mp hUn
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let S : Sylow 2 G := hT.2.1.toSylow hT2
  exact hev _ ⟨U, hU1, hU, rfl⟩ ⟨S, hTU⟩

omit [Finite G] in
theorem charTwo_of_isTwoLocal_of_isSylowTwoOf_le
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T M : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hM : IsTwoLocal M) (hTM : T ≤ M) : CharTwo M := by
  have hT2 : ¬ 2 ∣ T.index := by
    rw [← Subgroup.relIndex_top_right]
    exact hT.2.2
  let S : Sylow 2 G := hT.2.1.toSylow hT2
  exact hev M hM ⟨S, hTM⟩

theorem charTwo_of_isTwoLocal_of_pCore_centralizer_le
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T M N : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hM : IsTwoLocal M) (hTM : T ≤ M) (hNM : N ≤ M)
    (hC : pCoreOf 2 M ⊓ Subgroup.centralizer (pCoreOf 2 N : Set G) ≤ N) : CharTwo N :=
  charTwo_of_pCore_centralizer_le (charTwo_of_isTwoLocal_of_isSylowTwoOf_le hev hT hM hTM) hNM hC

theorem charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot
    (hev : CFSG.Assembly.Quasithin.quasithinEvenCharacteristic G) {T H : Subgroup G}
    (hT : IsSylowTwoOf T ⊤) (hTH : T ≤ H) (hH : pCoreOf 2 H ≠ ⊥) : CharTwo H := by
  have hHM : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 H
  have hMloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hH, CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 H, rfl⟩
  have hTM : T ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := hTH.trans hHM
  have hMS : pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 H : Set G)) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le hT hTM)
  exact charTwo_of_isTwoLocal_of_pCore_centralizer_le hev hT hMloc hTM hHM
    (inf_le_left.trans (hMS.trans hTH))

theorem charTwo_of_relIndex_le_two {M S M₁ : Subgroup G} (hM : CharTwo M) (hS : IsSylowTwoOf S M)
    (hM₁ : M₁ ≤ M) (hindex : M₁.relIndex S ≤ 2) : CharTwo M₁ := by
  set Q := pCoreOf 2 M with hQ
  have hQS : Q ≤ S := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hQM : Q ≤ M := CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 M
  have hMQ : M ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 M
  have hM₂M : M₁ ⊔ Q ≤ M := sup_le hM₁ hQM
  have hM₂ : CharTwo (M₁ ⊔ Q) :=
    charTwo_of_pCore_centralizer_le hM hM₂M (inf_le_left.trans le_sup_right)
  have hconj : ∀ g ∈ M, ∀ x ∈ Q, g⁻¹ * x * g ∈ Q := fun g hg x hx => by
    simpa using Subgroup.le_normalizer_iff.mp hMQ g⁻¹ (M.inv_mem hg) x hx
  have hrel : M₁.relIndex S = 1 ∨ M₁.relIndex S = 2 := by
    have : M₁.relIndex S ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have key : ∀ q ∈ Q, ∀ m ∈ M₁, q * m * q⁻¹ ∈ M₁ := by
    intro q hq m hm
    have hmM : m ∈ M := hM₁ hm
    have hxQ : m⁻¹ * q * m ∈ Q := hconj m hmM q hq
    have hc : m⁻¹ * q * m * q⁻¹ ∈ M₁ := by
      rcases hrel with h1 | h2
      · exact Subgroup.relIndex_eq_one.mp h1 (S.mul_mem (hQS hxQ) (S.inv_mem (hQS hq)))
      · have hidx : (M₁.subgroupOf S).index = 2 := h2
        have hmul := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨m⁻¹ * q * m, hQS hxQ⟩)
          (b := ⟨q⁻¹, S.inv_mem (hQS hq)⟩)
        have hiff : (m⁻¹ * q * m ∈ M₁) ↔ (q⁻¹ ∈ M₁) := by
          constructor
          · intro h
            have := M₁.mul_mem (M₁.mul_mem hm h) (M₁.inv_mem hm)
            have h' : q ∈ M₁ := by simpa [mul_assoc] using this
            exact M₁.inv_mem h'
          · intro h
            have h' : q ∈ M₁ := by simpa using M₁.inv_mem h
            exact M₁.mul_mem (M₁.mul_mem (M₁.inv_mem hm) h') hm
        exact hmul.mpr hiff
    have : q * m * q⁻¹ = m * (m⁻¹ * q * m * q⁻¹) := by group
    rw [this]
    exact M₁.mul_mem hm hc
  have hnorm : M₁ ⊔ Q ≤ Subgroup.normalizer (M₁ : Set G) := by
    refine sup_le Subgroup.le_normalizer fun q hq => ?_
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨fun hm => key q hq m hm, fun hm => ?_⟩
    have := key q⁻¹ (Q.inv_mem hq) _ hm
    simpa [mul_assoc] using this
  exact hM₂.of_normal le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hnorm)

end CFSG.QuasithinUnique
