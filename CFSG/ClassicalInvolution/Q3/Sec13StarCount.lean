module

public import CFSG.ClassicalInvolution.Generic.Frame

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

private theorem comm_uniqueInvolution {J : Subgroup G} {t : G} (ht : IsUniqueInvolution J t)
    {g : G} (hg : g ∈ J) : g * t = t * g :=
  mul_inv_eq_iff_eq_mul.1 (ht.conj_eq (conjSub_eq_self_of_mem hg))

private theorem orderOf_eq_four_of_noncomm {J : Subgroup G} (hJ8 : Nat.card J = 8)
    (hnab : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) {w : G} (hw : w ∈ J) (hw2 : w * w ≠ 1) :
    orderOf w = 4 := by
  have hdvd : orderOf w ∣ 8 := hJ8 ▸ J.orderOf_dvd_natCard hw
  have h1 : orderOf w ≠ 1 := fun h => hw2 (by rw [orderOf_eq_one_iff.1 h, mul_one])
  have h2 : orderOf w ≠ 2 := fun h => hw2 (by rw [← sq, ← h, pow_orderOf_eq_one])
  have h8 : orderOf w ≠ 8 := by
    intro h
    have heq : Subgroup.zpowers w = J :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hw) (by rw [hJ8, Nat.card_zpowers, h])
    obtain ⟨x, hx, y, hy, hxy⟩ := hnab
    rw [← heq, Subgroup.mem_zpowers_iff] at hx hy
    obtain ⟨m, rfl⟩ := hx
    obtain ⟨n, rfl⟩ := hy
    exact hxy (Commute.zpow_zpow_self w m n).eq
  obtain ⟨k, hk⟩ : ∃ k, orderOf w = k := ⟨_, rfl⟩
  rw [hk] at hdvd h1 h2 h8 ⊢
  have hpos : 0 < k := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
  have hle : k ≤ 8 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases k <;> omega

private theorem mul_self_eq_of_noncomm {J : Subgroup G} {t : G} (ht : IsUniqueInvolution J t)
    (hJ8 : Nat.card J = 8) (hnab : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) {w : G} (hw : w ∈ J)
    (hw1 : w ≠ 1) (hwt : w ≠ t) : w * w = t := by
  have hw2 : w * w ≠ 1 := fun h => (ht.unique w hw h).elim hw1 hwt
  have h4 : w ^ 4 = 1 := by
    rw [← orderOf_eq_four_of_noncomm hJ8 hnab hw hw2]
    exact pow_orderOf_eq_one w
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq] at h4
  exact (ht.unique _ (J.mul_mem hw hw) h4).resolve_left hw2

private theorem eq_one_or_eq_of_central {J : Subgroup G} {t : G} (ht : IsUniqueInvolution J t)
    (hJ8 : Nat.card J = 8) (hnab : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) {c : G} (hc : c ∈ J)
    (hcJ : ∀ y ∈ J, c * y = y * c) : c = 1 ∨ c = t := by
  by_contra hne
  obtain ⟨u, hu, v, hv, huv⟩ := hnab
  have hc2 := mul_self_eq_of_noncomm ht hJ8 ⟨u, hu, v, hv, huv⟩ hc (fun h => hne (Or.inl h))
    fun h => hne (Or.inr h)
  have hu1 : u ≠ 1 := by
    rintro rfl
    simp at huv
  have hut : u ≠ t := by
    rintro rfl
    exact huv (comm_uniqueInvolution ht hv).symm
  have hu2 := mul_self_eq_of_noncomm ht hJ8 ⟨u, hu, v, hv, huv⟩ hu hu1 hut
  have huc : u * c * (u * c) = 1 := by
    calc u * c * (u * c) = u * (c * u) * c := by group
      _ = u * (u * c) * c := by rw [hcJ u hu]
      _ = u * u * (c * c) := by group
      _ = 1 := by rw [hu2, hc2, ht.sq]
  have hcomm : u * c * v = v * (u * c) := by
    rcases ht.unique _ (J.mul_mem hu hc) huc with h | h
    · rw [h, one_mul, mul_one]
    · rw [h]
      exact (comm_uniqueInvolution ht hv).symm
  apply huv
  have : u * v * c = v * u * c := by
    calc u * v * c = u * (v * c) := mul_assoc _ _ _
      _ = u * (c * v) := by rw [hcJ v hv]
      _ = u * c * v := (mul_assoc _ _ _).symm
      _ = v * (u * c) := hcomm
      _ = v * u * c := (mul_assoc _ _ _).symm
  exact mul_right_cancel this

private theorem exists_mul_of_mem_sup {L M : Subgroup G}
    (hLM : ∀ x ∈ L, ∀ y ∈ M, x * y = y * x) {a : G} (ha : a ∈ L ⊔ M) :
    ∃ x ∈ L, ∃ m ∈ M, a = x * m := by
  rw [Subgroup.sup_eq_closure] at ha
  induction ha using Subgroup.closure_induction with
  | mem a ha =>
    rcases ha with ha | ha
    · exact ⟨a, ha, 1, M.one_mem, (mul_one a).symm⟩
    · exact ⟨1, L.one_mem, a, ha, (one_mul a).symm⟩
  | one => exact ⟨1, L.one_mem, 1, M.one_mem, (mul_one 1).symm⟩
  | mul a b _ _ iha ihb =>
    obtain ⟨x, hx, m, hm, rfl⟩ := iha
    obtain ⟨x', hx', m', hm', rfl⟩ := ihb
    refine ⟨x * x', L.mul_mem hx hx', m * m', M.mul_mem hm hm', ?_⟩
    calc x * m * (x' * m') = x * (m * x') * m' := by group
      _ = x * (x' * m) * m' := by rw [hLM x' hx' m hm]
      _ = x * x' * (m * m') := by group
  | inv a _ iha =>
    obtain ⟨x, hx, m, hm, rfl⟩ := iha
    refine ⟨x⁻¹, L.inv_mem hx, m⁻¹, M.inv_mem hm, ?_⟩
    rw [mul_inv_rev]
    exact (hLM x⁻¹ (L.inv_mem hx) m⁻¹ (M.inv_mem hm)).symm

private theorem card_mul_card_le_card_inf_mul_card_sup (A B : Subgroup G) :
    Nat.card A * Nat.card B ≤ Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) := by
  have e1 : B.relIndex A * Nat.card ↥(A ⊓ B) = Nat.card A := by
    rw [inf_comm, Subgroup.relIndex_mul_card]
  have e2 : B.relIndex (A ⊔ B) * Nat.card B = Nat.card ↥(A ⊔ B) := by
    have := Subgroup.relIndex_mul_card B (A ⊔ B)
    rwa [inf_eq_left.mpr le_sup_right] at this
  have hne0 : B.relIndex (A ⊔ B) ≠ 0 := by
    intro h
    rw [h] at e2
    have : 0 < Nat.card ↥(A ⊔ B) := Nat.card_pos
    omega
  have hle : B.relIndex A ≤ B.relIndex (A ⊔ B) :=
    Subgroup.relIndex_le_of_le_right le_sup_left hne0
  calc Nat.card A * Nat.card B = B.relIndex A * Nat.card ↥(A ⊓ B) * Nat.card B := by rw [e1]
    _ ≤ B.relIndex (A ⊔ B) * Nat.card ↥(A ⊓ B) * Nat.card B := by gcongr
    _ = Nat.card ↥(A ⊓ B) * Nat.card ↥(A ⊔ B) := by rw [← e2]; ring

private theorem card_le_card_of_forall_mem {K : Subgroup G} {s : Finset G}
    (h : ∀ x ∈ K, x ∈ s) : Nat.card K ≤ s.card := by
  rw [← Nat.card_eq_finsetCard]
  refine Nat.card_le_card_of_injective (fun x : K => (⟨x, h x x.2⟩ : s)) fun a b hab => ?_
  exact Subtype.ext (by simpa using congrArg (fun y : s => (y : G)) hab)

private theorem eight_le_card_sup_conjSub_inf {Q : Subgroup G} (hQ : Q.Normal) {t : G}
    (htQ : t ∈ Q) {L : Subgroup G} (hL8 : Nat.card L = 8) (hL'8 : Nat.card (conjSub t L) = 8)
    (hnab : ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x) {z : G} (hz : IsUniqueInvolution L z)
    (hzQ : z ∈ Q) (hc : Commutes L (conjSub t L)) :
    8 ≤ Nat.card ↥((L ⊔ conjSub t L) ⊓ Q) := by
  classical
  set L' := conjSub t L with hL'
  have hinf : Nat.card ↥(L ⊓ L') ≤ 2 := by
    refine (card_le_card_of_forall_mem (s := {1, z}) ?_).trans Finset.card_le_two
    intro x hx
    obtain ⟨hxL, hxL'⟩ := Subgroup.mem_inf.1 hx
    rcases eq_one_or_eq_of_central hz hL8 hnab hxL (fun y hy => (hc y hy x hxL').symm) with
      rfl | rfl <;> simp
  have hsup : 32 ≤ Nat.card ↥(L ⊔ L') := by
    have h := card_mul_card_le_card_inf_mul_card_sup L L'
    rw [hL8, hL'8] at h
    have := h.trans (Nat.mul_le_mul hinf le_rfl)
    omega
  have hL'Q : L' ≤ L ⊔ Q := by
    intro y hy
    rw [hL', mem_conjSub_iff] at hy
    have hy' : y = (t⁻¹ * y * t) * ((t⁻¹ * y * t)⁻¹ * t * (t⁻¹ * y * t)) * t⁻¹ := by group
    rw [hy']
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hy)
      (Subgroup.mem_sup_right (hQ.conj_mem' t htQ _))) (Subgroup.mem_sup_right (Q.inv_mem htQ))
  have hidx : Q.relIndex (L ⊔ L') ≤ 4 := by
    have hne0 : Q.relIndex (L ⊔ Q) ≠ 0 := by
      intro h
      have := Subgroup.relIndex_mul_card Q (L ⊔ Q)
      rw [h, zero_mul] at this
      exact Nat.card_pos.ne this
    have h1 : Q.relIndex (L ⊔ L') ≤ Q.relIndex (L ⊔ Q) :=
      Subgroup.relIndex_le_of_le_right (sup_le le_sup_left hL'Q) hne0
    rw [Subgroup.relIndex_sup_right] at h1
    have h2 := Subgroup.relIndex_mul_card Q L
    rw [hL8] at h2
    have h3 : 1 < Nat.card ↥(Q ⊓ L) := (Subgroup.one_lt_card_iff_ne_bot (H := Q ⊓ L)).2 fun h =>
      hz.ne_one ((Subgroup.eq_bot_iff_forall (Q ⊓ L)).1 h z (Subgroup.mem_inf.2 ⟨hzQ, hz.mem⟩))
    have h4 : Q.relIndex L * 2 ≤ 8 := h2 ▸ Nat.mul_le_mul le_rfl h3
    omega
  have h5 := Subgroup.relIndex_mul_card Q (L ⊔ L')
  rw [inf_comm] at h5
  have h6 : Nat.card ↥(L ⊔ L') ≤ 4 * Nat.card ↥((L ⊔ L') ⊓ Q) := by
    rw [← h5]
    exact Nat.mul_le_mul hidx le_rfl
  omega

theorem exists_comm_orderOf_four {J : Subgroup G} {t : G} (ht : IsUniqueInvolution J t)
    (hJ8 : Nat.card J = 8) (hnab : ∃ x ∈ J, ∃ y ∈ J, x * y ≠ y * x) {a : G}
    (ha : ∀ y ∈ J, a * y * a⁻¹ = y ∨ a * y * a⁻¹ = y * t) :
    ∃ u ∈ J, orderOf u = 4 ∧ a * u = u * a := by
  have key : ∀ w ∈ J, ∀ v ∈ J, w * v ≠ v * w → orderOf w = 4 := by
    intro w hw v hv hwv
    refine orderOf_eq_four_of_noncomm hJ8 hnab hw fun hw2 => hwv ?_
    rcases ht.unique w hw hw2 with rfl | rfl
    · rw [one_mul, mul_one]
    · exact (comm_uniqueInvolution ht hv).symm
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  rcases ha x hx with h1 | h1
  · exact ⟨x, hx, key x hx y hy hxy, mul_inv_eq_iff_eq_mul.1 h1⟩
  rcases ha y hy with h2 | h2
  · exact ⟨y, hy, key y hy x hx (Ne.symm hxy), mul_inv_eq_iff_eq_mul.1 h2⟩
  refine ⟨x * y, J.mul_mem hx hy, key _ (J.mul_mem hx hy) x hx fun h => hxy ?_, ?_⟩
  · have h' : x * (y * x) = x * (x * y) := by rw [← h, mul_assoc]
    exact (mul_left_cancel h').symm
  · refine mul_inv_eq_iff_eq_mul.1 ?_
    calc a * (x * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹) := by group
      _ = x * t * (y * t) := by rw [h1, h2]
      _ = x * (t * y) * t := by group
      _ = x * (y * t) * t := by rw [comm_uniqueInvolution ht hy]
      _ = x * y * (t * t) := by group
      _ = x * y := by rw [ht.sq, mul_one]

theorem exists_inner_of_mem_sup {L M : Subgroup G} (hLM : ∀ x ∈ L, ∀ y ∈ M, x * y = y * x)
    {a : G} (ha : a ∈ L ⊔ M) : ∃ x ∈ L, ∀ y ∈ L, a * y * a⁻¹ = x * y * x⁻¹ := by
  obtain ⟨x, hx, m, hm, rfl⟩ := exists_mul_of_mem_sup hLM ha
  refine ⟨x, hx, fun y hy => ?_⟩
  calc x * m * y * (x * m)⁻¹ = x * (m * y) * m⁻¹ * x⁻¹ := by group
    _ = x * (y * m) * m⁻¹ * x⁻¹ := by rw [hLM y hy m hm]
    _ = x * y * x⁻¹ := by group

theorem card_le_ncard_of_free {A J : Subgroup G} {𝓢 : Set (Subgroup G)} (h𝓢 : 𝓢.Finite)
    (hJA : ∀ a ∈ A, conjSub a J ∈ 𝓢) (hfree : ∀ a ∈ A, conjSub a J = J → a = 1) :
    Nat.card A ≤ 𝓢.ncard := by
  have := h𝓢.to_subtype
  rw [← Nat.card_coe_set_eq]
  refine Nat.card_le_card_of_injective (fun a : A => (⟨conjSub (a : G) J, hJA a a.2⟩ : 𝓢)) ?_
  intro a b hab
  have hab' : conjSub (a : G) J = conjSub (b : G) J := congrArg Subtype.val hab
  have h1 : conjSub ((b : G)⁻¹ * a) J = J := by
    rw [conjSub_mul, hab', conjSub_inv_conjSub]
  exact Subtype.ext (inv_mul_eq_one.1 (hfree _ (A.mul_mem (A.inv_mem b.2) a.2) h1)).symm

theorem ncard_le_sylow_eq {p : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
    (hΩ : ∀ g : G, ∀ L ∈ Ω, conjSub g L ∈ Ω) (S S' : Sylow p G) :
    {L | L ∈ Ω ∧ L ≤ (S : Subgroup G)}.ncard = {L | L ∈ Ω ∧ L ≤ (S' : Subgroup G)}.ncard := by
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G S S'
  have hS : ((g • S : Sylow p G) : Subgroup G) = conjSub g S := rfl
  have himg : conjSub g '' {L | L ∈ Ω ∧ L ≤ (S : Subgroup G)} =
      {L | L ∈ Ω ∧ L ≤ ((g • S : Sylow p G) : Subgroup G)} := by
    rw [hS]
    ext L
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨K, ⟨hK, hKS⟩, rfl⟩
      exact ⟨hΩ g K hK, conjSub_mono hKS⟩
    · rintro ⟨hL, hLS⟩
      refine ⟨conjSub g⁻¹ L, ⟨hΩ _ L hL, ?_⟩, conjSub_conjSub_inv g L⟩
      have := conjSub_mono (n := g⁻¹) hLS
      rwa [conjSub_inv_conjSub] at this
  rw [← himg, Set.ncard_image_of_injective _ (conjSub_injective g)]

theorem two_pow_le_card_iSup_inf {Q : Subgroup G} (hQ : Q.Normal) {t : G} (htQ : t ∈ Q)
    (ht2 : t * t = 1) (𝓟 : Finset (Subgroup G)) (hcard : ∀ L ∈ 𝓟, Nat.card L = 8)
    (hnab : ∀ L ∈ 𝓟, ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x)
    (hz : ∀ L ∈ 𝓟, ∃ z : G, IsUniqueInvolution L z ∧ z ∈ Q)
    (hcomm : ∀ L ∈ 𝓟, ∀ L' ∈ 𝓟, L ≠ L' → Commutes L L')
    (hstab : ∀ L ∈ 𝓟, conjSub t L ∈ 𝓟) (hmove : ∀ L ∈ 𝓟, conjSub t L ≠ L)
    (hne : 𝓟.Nonempty) :
    2 ^ (𝓟.card / 2 + 2) ≤ Nat.card ↥((⨆ L ∈ 𝓟, L) ⊓ Q) := by
  classical
  have htt : ∀ K : Subgroup G, conjSub t (conjSub t K) = K := fun K => by
    rw [← conjSub_mul, ht2, conjSub_one]
  induction 𝓟 using Finset.strongInduction with
  | H 𝓟 ih =>
  obtain ⟨L, hL⟩ := hne
  obtain ⟨z, hzL, hzQ⟩ := hz L hL
  have hL' : conjSub t L ∈ 𝓟 := hstab L hL
  obtain ⟨z', hzL', -⟩ := hz _ hL'
  have hLL' : conjSub t L ≠ L := hmove L hL
  set L' := conjSub t L with hL'def
  obtain ⟨𝓟', h𝓟'⟩ : ∃ 𝓟', 𝓟' = (𝓟.erase L).erase L' := ⟨_, rfl⟩
  have hmem' : ∀ M, M ∈ 𝓟' ↔ M ≠ L' ∧ M ≠ L ∧ M ∈ 𝓟 := fun M => by
    rw [h𝓟', Finset.mem_erase, Finset.mem_erase]
  have hP' : ∀ M ∈ 𝓟', M ∈ 𝓟 := fun M hM => ((hmem' M).1 hM).2.2
  have hsub : 𝓟' ⊂ 𝓟 := h𝓟' ▸ (Finset.erase_subset _ _).trans_ssubset (Finset.erase_ssubset hL)
  have hcard2 : 𝓟'.card + 2 = 𝓟.card := by
    have h1 := Finset.card_erase_of_mem hL
    have h2 := Finset.card_erase_of_mem (Finset.mem_erase.2 ⟨hLL', hL'⟩)
    have h3 : 1 < 𝓟.card := Finset.one_lt_card.2 ⟨L, hL, L', hL', hLL'.symm⟩
    rw [← h𝓟'] at h2
    omega
  have hstab' : ∀ M ∈ 𝓟', conjSub t M ∈ 𝓟' := by
    intro M hM
    obtain ⟨hML', hML, hM𝓟⟩ := (hmem' M).1 hM
    refine (hmem' _).2 ⟨fun h => hML (conjSub_injective t h), fun h => hML' ?_, hstab M hM𝓟⟩
    exact (htt M).symm.trans (congrArg (conjSub t) h)
  have hcLL' : Commutes L L' := hcomm L hL L' hL' hLL'.symm
  have hLQ8 : 8 ≤ Nat.card ↥((L ⊔ L') ⊓ Q) :=
    eight_le_card_sup_conjSub_inf hQ htQ (hcard L hL) (hcard L' hL') (hnab L hL) hzL hzQ hcLL'
  have hHP : L ⊔ L' ≤ ⨆ M ∈ 𝓟, M :=
    sup_le (le_iSup₂_of_le L hL le_rfl) (le_iSup₂_of_le L' hL' le_rfl)
  rcases 𝓟'.eq_empty_or_nonempty with h0 | hne'
  ·
    rw [h0, Finset.card_empty] at hcard2
    calc 2 ^ (𝓟.card / 2 + 2) = 8 := by rw [← hcard2]; norm_num
      _ ≤ Nat.card ↥((L ⊔ L') ⊓ Q) := hLQ8
      _ ≤ _ := Subgroup.card_le_of_le (inf_le_inf_right Q hHP)
  · have hIH := ih 𝓟' hsub (fun M hM => hcard M (hP' M hM)) (fun M hM => hnab M (hP' M hM))
      (fun M hM => hz M (hP' M hM)) (fun M hM M' hM' => hcomm M (hP' M hM) M' (hP' M' hM'))
      hstab' (fun M hM => hmove M (hP' M hM)) hne'
    have hM'P : (⨆ M ∈ 𝓟', M) ≤ ⨆ M ∈ 𝓟, M :=
      iSup₂_le fun M hM => le_iSup₂_of_le M (hP' M hM) le_rfl
    have hM'C : (⨆ M ∈ 𝓟', M) ≤ Subgroup.centralizer ((L ⊔ L' : Subgroup G) : Set G) := by
      refine iSup₂_le fun M hM m hm => ?_
      obtain ⟨hML', hML, hM𝓟⟩ := (hmem' M).1 hM
      have hle : L ⊔ L' ≤ Subgroup.centralizer (M : Set G) :=
        sup_le (fun y hy => Subgroup.mem_centralizer_iff.2 fun m' hm' =>
            hcomm M hM𝓟 L hL hML m' hm' y hy)
          (fun y hy => Subgroup.mem_centralizer_iff.2 fun m' hm' =>
            hcomm M hM𝓟 L' hL' hML' m' hm' y hy)
      exact Subgroup.mem_centralizer_iff.2 fun y hy =>
        (Subgroup.mem_centralizer_iff.1 (hle hy) m hm).symm
    have h4 : Nat.card ↥((L ⊔ L') ⊓ ⨆ M ∈ 𝓟', M) ≤ 4 := by
      refine (card_le_card_of_forall_mem (s := {1, z, z', z * z'}) ?_).trans Finset.card_le_four
      intro x hx
      obtain ⟨hxH, hxM⟩ := Subgroup.mem_inf.1 hx
      have hxC := hM'C hxM
      obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hcLL' hxH
      have haC : ∀ y ∈ L, a * y = y * a := by
        intro y hy
        have h1 := Subgroup.mem_centralizer_iff.1 hxC y (Subgroup.mem_sup_left hy)
        have h2 := hcLL' y hy b hb
        have : a * y * b = y * a * b := by
          calc a * y * b = a * (y * b) := mul_assoc _ _ _
            _ = a * (b * y) := by rw [h2]
            _ = a * b * y := (mul_assoc _ _ _).symm
            _ = y * (a * b) := h1.symm
            _ = y * a * b := (mul_assoc _ _ _).symm
        exact mul_right_cancel this
      have hbC : ∀ y ∈ L', b * y = y * b := by
        intro y hy
        have h1 := Subgroup.mem_centralizer_iff.1 hxC y (Subgroup.mem_sup_right hy)
        have h2 := hcLL' a ha y hy
        have : a * (b * y) = a * (y * b) := by
          calc a * (b * y) = a * b * y := (mul_assoc _ _ _).symm
            _ = y * (a * b) := h1.symm
            _ = y * a * b := (mul_assoc _ _ _).symm
            _ = a * y * b := by rw [h2]
            _ = a * (y * b) := mul_assoc _ _ _
        exact mul_left_cancel this
      rcases eq_one_or_eq_of_central hzL (hcard L hL) (hnab L hL) ha haC with rfl | rfl <;>
        rcases eq_one_or_eq_of_central hzL' (hcard L' hL') (hnab L' hL') hb hbC with
          rfl | rfl <;> simp
    have hprod := card_mul_card_le_card_inf_mul_card_sup ((L ⊔ L') ⊓ Q) ((⨆ M ∈ 𝓟', M) ⊓ Q)
    have hAB : Nat.card ↥((L ⊔ L') ⊓ Q ⊓ ((⨆ M ∈ 𝓟', M) ⊓ Q)) ≤ 4 :=
      (Subgroup.card_le_of_le (inf_le_inf inf_le_left inf_le_left)).trans h4
    have hsupP : Nat.card ↥((L ⊔ L') ⊓ Q ⊔ (⨆ M ∈ 𝓟', M) ⊓ Q) ≤
        Nat.card ↥((⨆ M ∈ 𝓟, M) ⊓ Q) :=
      Subgroup.card_le_of_le (sup_le (inf_le_inf_right Q hHP) (inf_le_inf_right Q hM'P))
    have h8N := (Nat.mul_le_mul hLQ8 hIH).trans (hprod.trans (Nat.mul_le_mul hAB le_rfl))
    rw [show 𝓟.card / 2 + 2 = 𝓟'.card / 2 + 2 + 1 by omega, pow_succ]
    omega

end CFSG.ClassicalInvolution.Q3.Sec13
