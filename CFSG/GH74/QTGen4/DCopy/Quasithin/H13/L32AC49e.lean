module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32AC49e
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC49a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC49c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

local notation "cS6" =>
  (MulAut.conjNormal : Equiv.Perm (Fin 6) →* MulAut CFSG.Quasithin.H13.L32A.C.Alt6.A6)

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem sup_l1_eq_N_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G}
    (hL1K : l1 T L V ≤ K) {π : ↥K →* Alt6.A6}
    (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = Alt6.D0) :
    Alt6.D0 ⊔ ((l1 T L V).subgroupOf K).map π = Alt6.N1 ∨
      Alt6.D0 ⊔ ((l1 T L V).subgroupOf K).map π = Alt6.N2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTl1 := T_le_normalizer_l1_F4 h1332 S
  set R := ((l1 T L V).subgroupOf K).map π with hR
  have hRP : Alt6.D0 ≤ Subgroup.normalizer (R : Set Alt6.A6) := by
    have one_dir : ∀ s : ↥K, (s : G) ∈ T → ∀ r ∈ R, π s * r * (π s)⁻¹ ∈ R := by
      rintro s hs _ ⟨x, hx, rfl⟩
      refine ⟨s * x * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      show (s : G) * x * (s : G)⁻¹ ∈ l1 T L V
      exact (Subgroup.mem_normalizer_iff.mp (hTl1 hs) x).mp hx
    intro p hp
    rw [← hD] at hp
    obtain ⟨s, hs, rfl⟩ := hp
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨one_dir s hs r, fun hr => ?_⟩
    have := one_dir s⁻¹ (T.inv_mem hs) _ hr
    simpa [mul_assoc] using this
  have hQ23 : IsTwoThree (Nat.card ↥(Alt6.D0 ⊔ R)) := by
    rw [card_sup_eq hRP]
    have hR : IsTwoThree (Nat.card R) := by
      have h2 := isTwoThree_card_sup hL3 (IsPGroup.of_bot) (show (⊥ : Subgroup G) ≤ _ from bot_le)
      rw [bot_sup_eq] at h2
      refine h2.of_dvd ?_
      have := Subgroup.card_map_dvd ((l1 T L V).subgroupOf K) π
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1K).toEquiv] at this
    have h8 : Nat.card ↥Alt6.D0 = 2 ^ 3 := Alt6.card_D0.trans (by norm_num)
    refine IsTwoThree.mul ((isTwoThree_two_pow 3).of_dvd ?_) hR
    rw [← h8]
    exact Subgroup.index_dvd_card _

  obtain ⟨y, hy, hyodd, hyK⟩ := exists_gen_not_mem hL3 K
  have hyl1 : y ∈ l1 T L V := Subgroup.subset_closure ⟨hy, hyodd⟩
  have hryQ : π ⟨y, hL1K hyl1⟩ ∈ Alt6.D0 ⊔ R :=
    Subgroup.mem_sup_right ⟨⟨y, hL1K hyl1⟩, hyl1, rfl⟩
  have hry1 : π ⟨y, hL1K hyl1⟩ ≠ 1 := fun h => hyK ((hker _).mp h)
  have hryodd : Odd (orderOf (π ⟨y, hL1K hyl1⟩)) := by
    refine Odd.of_dvd_nat hyodd ?_
    have := orderOf_map_dvd π ⟨y, hL1K hyl1⟩
    rwa [show orderOf (⟨y, hL1K hyl1⟩ : ↥K) = orderOf y from Subgroup.orderOf_mk _ _] at this
  have h3 : 3 ∣ Nat.card ↥(Alt6.D0 ⊔ R) := by
    obtain ⟨a, b, hab⟩ := hQ23
    have hdvd : orderOf (π ⟨y, hL1K hyl1⟩) ∣ 2 ^ a * 3 ^ b := by
      rw [← hab]
      have := orderOf_dvd_natCard (⟨_, hryQ⟩ : ↥(Alt6.D0 ⊔ R))
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (orderOf (π ⟨y, hL1K hyl1⟩)) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hryodd)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (hcop.dvd_of_dvd_mul_left hdvd)
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hry1 hj
    have hjd : 3 ^ j ∣ 2 ^ a * 3 ^ b := by
      rw [← hj]
      exact hdvd
    rw [hab]
    exact (dvd_pow_self 3 hj0).trans hjd
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card' 3 h3
  exact Alt6.eq_N_of_isTwoThree le_sup_left hQ23 r.2 ((Subgroup.orderOf_coe r).trans hr)

theorem T_conj_a6_F4
    (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4) {K : Subgroup G}
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {π : ↥K →* Alt6.A6}
    (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = Alt6.D0)
    (hQ : Alt6.D0 ⊔ ((l1 T L V).subgroupOf K).map π = Alt6.N1 ∨
      Alt6.D0 ⊔ ((l1 T L V).subgroupOf K).map π = Alt6.N2)
    (t : G) (ht : t ∈ H) (htT : t ∈ T) :
    indHom π hπ hker hKn hHN ⟨t, ht⟩ ∈ MonoidHom.range cS6 := by
  have hTl1 := T_le_normalizer_l1_F4 h1332 S
  set β := indHom π hπ hker hKn hHN ⟨t, ht⟩ with hβdef
  have hβ : ∀ k : ↥K, β (π k) = π (conjK (hKn ht) k) := indHom_apply π hπ hker hKn hHN _
  set R := ((l1 T L V).subgroupOf K).map π with hR
  have hP0 : ∀ p ∈ Alt6.D0, β p ∈ Alt6.D0 := by
    intro p hp
    rw [← hD] at hp ⊢
    obtain ⟨s, hs, rfl⟩ := hp
    refine ⟨conjK (hKn ht) s, ?_, (hβ s).symm⟩
    show ((conjK (hKn ht) s : ↥K) : G) ∈ T
    rw [conjK_apply]
    exact T.mul_mem (T.mul_mem htT hs) (T.inv_mem htT)
  have hRR : ∀ r ∈ R, β r ∈ R := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨conjK (hKn ht) x, ?_, (hβ x).symm⟩
    show ((conjK (hKn ht) x : ↥K) : G) ∈ l1 T L V
    rw [conjK_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hTl1 htT) x).mp hx
  have hPR : ∀ x ∈ Alt6.D0 ⊔ R, β x ∈ Alt6.D0 ⊔ R := by
    intro x hx
    have hle : (Alt6.D0 ⊔ R).map β.toMonoidHom ≤ Alt6.D0 ⊔ R := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (fun _ ⟨p, hp, hpe⟩ => hpe ▸ hP0 p hp)
        (fun _ ⟨r, hr, hre⟩ => hre ▸ hRR r hr)
    exact hle ⟨x, hx, rfl⟩
  refine Alt6.mem_range_conjNormal_of_normalizes β ?_
  rcases hQ with hq | hq
  · exact Or.inl fun x hx => hq ▸ hPR x (hq ▸ hx)
  · exact Or.inr fun x hx => hq ▸ hPR x (hq ▸ hx)

theorem not_isAlt_six_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h11 : Lemma14_7_11_F4) (h28 : Lemma14_7_28_F4)
    (h32 : Lemma14_7_32_F4) (h47 : Lemma14_7_47_F4) (h48 : Lemma14_7_48_F4) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) : ¬ IsAlt 6 (cStar K) := by
  intro hA
  obtain ⟨K', hcK', hHKT, -⟩ := h48 _ T L V H S
  have hKK' : K = K' := by
    have := hK
    rw [hcK'] at this
    exact this
  subst hKK'
  have hL1K := (h47 _ T L V H S K hK).1
  have hKn := le_normalizer_of_setting h37 h38 S hK (h32 _ T L V H S K hK)
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hL3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  obtain ⟨π, hπ, hker, hD⟩ := exists_pi_a6 hA hKH hKn hTsylH
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  have hQ := sup_l1_eq_N_F4 S h1332 hL3 hL1K hker hD
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = cS6 (π ⟨k, hk⟩ : Equiv.Perm (Fin 6)) := by
    intro k hk
    rw [← Alt6.conj_eq_conjNormal]
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ MonoidHom.range cS6 := by
    have hle : K ⊔ T ≤ ((MonoidHom.range cS6).comap β).map H.subtype :=
      sup_le (fun k hk => ⟨⟨k, hKH hk⟩, ⟨_, (hKin k hk).symm⟩, rfl⟩)
        (fun t ht => ⟨⟨t, hTH ht⟩,
          T_conj_a6_F4 S h1332 hKn hHN hπ hker hD hQ t (hTH ht) ht, rfl⟩)
    rw [← hHKT] at hle
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have e : y = y' := Subtype.ext hyy'.symm
    rw [e]
    exact hy'
  have hZ : Subgroup.center (cStar K) = ⊥ := by
    obtain ⟨φ⟩ := hA
    have hc := card_center_eq_of_mulEquiv φ
    rw [alternatingGroup.center_eq_bot (by simp), Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π hπ hker hKH hKn hHN cS6 Alt6.conjNormal_injective
    hInn fun x hx hxc => mem_pCoreOf_of_comm_F4 h28 S hcK' hL1K hKn hZ hx hxc
  have hψK : ∀ k (hk : k ∈ K), ψ ⟨k, hKH hk⟩ = (π ⟨k, hk⟩ : Equiv.Perm (Fin 6)) := by
    intro k hk
    apply Alt6.conjNormal_injective
    rw [hψ, hKin k hk]
  have hA6le : alternatingGroup (Fin 6) ≤ ψ.range := by
    intro a ha
    obtain ⟨k, hk⟩ := hπ ⟨a, ha⟩
    exact ⟨⟨k, hKH k.2⟩, (hψK k k.2).trans (congrArg Subtype.val hk)⟩
  have h720 : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨m, hm⟩ := Alt6.card_A6 ▸ Subgroup.card_dvd_of_le hA6le
  have hm2 : m ∣ 2 := by
    obtain ⟨n, hn⟩ := h720 ▸ Subgroup.card_subgroup_dvd_card ψ.range
    have h1 : 360 * (m * n) = 360 * 2 := by rw [← mul_assoc, ← hm, ← hn]
    exact ⟨n, (Nat.eq_of_mul_eq_mul_left (by norm_num) h1).symm⟩
  rcases (Nat.dvd_prime Nat.prime_two).1 hm2 with rfl | rfl
  ·
    have heq : alternatingGroup (Fin 6) = ψ.range :=
      Subgroup.eq_of_le_of_card_ge hA6le (by rw [hm, Alt6.card_A6])
    have hmem : ∀ y, ψ y ∈ alternatingGroup (Fin 6) := fun y => by
      rw [heq]
      exact MonoidHom.mem_range.mpr ⟨y, rfl⟩
    refine (h11 _ T L V H S).2.1 ⟨ψ.codRestrict _ hmem, fun a => ?_, ?_⟩
    · obtain ⟨k, rfl⟩ := hπ a
      exact ⟨⟨k, hKH k.2⟩, Subtype.ext (hψK k k.2)⟩
    · rw [MonoidHom.ker_codRestrict, hψker]
  ·
    have htop : ψ.range = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hm, h720])
    exact (h11 _ T L V H S).2.2 ⟨ψ, MonoidHom.range_eq_top.mp htop, hψker⟩

theorem lemma14_7_49_of_F4
    (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h11 : Lemma14_7_11_F4) (h28 : Lemma14_7_28_F4)
    (h32 : Lemma14_7_32_F4) (h47 : Lemma14_7_47_F4) (h48 : Lemma14_7_48_F4) : Lemma14_7_49_F4 :=
  fun _ _ _ _ _ _ _ S _ hK =>
    ⟨not_isPSL_three_two_F4 h1222 h1332 h1334 h37 h38 h11 h28 h32 h47 h48 S hK,
      not_isAlt_six_F4 h1222 h1332 h1334 h37 h38 h11 h28 h32 h47 h48 S hK⟩

end CFSG.Quasithin.H13.L32A.C
