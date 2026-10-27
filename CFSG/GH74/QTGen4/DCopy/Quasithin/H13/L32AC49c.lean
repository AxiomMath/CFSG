module

public import CFSG.GH74.QTGen4.Finite4
public import CFSG.Quasithin.H13.L32AC49c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A6Inputs13_3
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC30b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC49a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ACSk
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.StatementsL2
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A5Props
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A767a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A767b
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A769c
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770a
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770k
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A770n
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AStatements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NLem1434
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

local notation "innS" => CFSG.ComponentClassification.OuterAutomorphisms.inner A6.SL3.S

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem sup_l1_eq_X_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    (hL3 : (pCoreOf 2 (l1 T L V)).relIndex (l1 T L V) = 3) {K : Subgroup G}
    (hL1K : l1 T L V ≤ K) {π : ↥K →* A6.SL3.S}
    (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = A6.SL3.P0) :
    A6.SL3.P0 ⊔ ((l1 T L V).subgroupOf K).map π = A6.SL3.X1 ∨
      A6.SL3.P0 ⊔ ((l1 T L V).subgroupOf K).map π = A6.SL3.X2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTl1 := T_le_normalizer_l1_F4 h1332 S
  set R := ((l1 T L V).subgroupOf K).map π with hR
  have hRP : A6.SL3.P0 ≤ Subgroup.normalizer (R : Set A6.SL3.S) := by
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
  have hQ23 : IsTwoThree (Nat.card ↥(A6.SL3.P0 ⊔ R)) := by
    rw [card_sup_eq hRP]
    have hR : IsTwoThree (Nat.card R) := by
      have h2 := isTwoThree_card_sup hL3 (IsPGroup.of_bot) (show (⊥ : Subgroup G) ≤ _ from bot_le)
      rw [bot_sup_eq] at h2
      refine h2.of_dvd ?_
      have := Subgroup.card_map_dvd ((l1 T L V).subgroupOf K) π
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1K).toEquiv] at this
    obtain ⟨m, hm⟩ := A6.SL3.P0_sylow.1.exists_card_eq
    refine IsTwoThree.mul ((isTwoThree_two_pow m).of_dvd ?_) hR
    rw [← hm]
    exact Subgroup.index_dvd_card _
  rcases A6.SL3.overgroups_SL3 (A6.SL3.P0 ⊔ R) le_sup_left with h | h | h | h
  · exfalso
    obtain ⟨y, hy, hyodd, hyK⟩ := exists_gen_not_mem hL3 K
    have hyl1 : y ∈ l1 T L V := Subgroup.subset_closure ⟨hy, hyodd⟩
    have hyR : π ⟨y, hL1K hyl1⟩ ∈ A6.SL3.P0 := by
      rw [← h]
      exact Subgroup.mem_sup_right ⟨⟨y, hL1K hyl1⟩, hyl1, rfl⟩
    obtain ⟨n, hn⟩ := A6.SL3.P0_sylow.1 ⟨_, hyR⟩
    have hyn : (π ⟨y, hL1K hyl1⟩) ^ 2 ^ n = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    have hyo : (π ⟨y, hL1K hyl1⟩) ^ orderOf y = 1 := by
      rw [← map_pow, show (⟨y, hL1K hyl1⟩ : ↥K) ^ orderOf y = 1 from Subtype.ext (by
        simp [pow_orderOf_eq_one]), map_one]
    have h1 : orderOf (π ⟨y, hL1K hyl1⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyo)
        (Nat.Coprime.pow_right n (Nat.coprime_two_right.mpr hyodd)))
        (orderOf_dvd_of_pow_eq_one hyn)
    exact hyK ((hker _).mp (orderOf_eq_one_iff.mp h1))
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    rw [h, Subgroup.card_top, A6.SL3.card_S] at hQ23
    exact not_isTwoThree_168 hQ23

theorem T_inner_sl3_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4) {K : Subgroup G}
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {π : ↥K →* A6.SL3.S}
    (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = A6.SL3.P0)
    (hQ : A6.SL3.P0 ⊔ ((l1 T L V).subgroupOf K).map π = A6.SL3.X1 ∨
      A6.SL3.P0 ⊔ ((l1 T L V).subgroupOf K).map π = A6.SL3.X2)
    (t : G) (ht : t ∈ H) (htT : t ∈ T) : indHom π hπ hker hKn hHN ⟨t, ht⟩ ∈ innS := by
  have hTl1 := T_le_normalizer_l1_F4 h1332 S
  set β := indHom π hπ hker hKn hHN ⟨t, ht⟩ with hβdef
  have hβ : ∀ k : ↥K, β (π k) = π (conjK (hKn ht) k) := indHom_apply π hπ hker hKn hHN _
  set R := ((l1 T L V).subgroupOf K).map π with hR
  have hP0 : ∀ p ∈ A6.SL3.P0, β p ∈ A6.SL3.P0 := by
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
  have hPR : ∀ x ∈ A6.SL3.P0 ⊔ R, β x ∈ A6.SL3.P0 ⊔ R := by
    intro x hx
    have hle : (A6.SL3.P0 ⊔ R).map β.toMonoidHom ≤ A6.SL3.P0 ⊔ R := by
      rw [Subgroup.map_sup]
      exact sup_le_sup (fun _ ⟨p, hp, hpe⟩ => hpe ▸ hP0 p hp)
        (fun _ ⟨r, hr, hre⟩ => hre ▸ hRR r hr)
    exact hle ⟨x, hx, rfl⟩
  refine mem_inner_of_normalizes β hP0 ?_
  rcases hQ with hq | hq
  · exact Or.inl fun x hx => hq ▸ hPR x (hq ▸ hx)
  · exact Or.inr fun x hx => hq ▸ hPR x (hq ▸ hx)

theorem not_isPSL_three_two_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h11 : Lemma14_7_11_F4) (h28 : Lemma14_7_28_F4)
    (h32 : Lemma14_7_32_F4) (h47 : Lemma14_7_47_F4) (h48 : Lemma14_7_48_F4) (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) : ¬ IsPSL 3 2 1 (cStar K) := by
  intro hP
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
  obtain ⟨π, hπ, hker, hD⟩ := exists_pi_sl3 hP hKH hKn hTsylH
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  set β := indHom π hπ hker hKn hHN with hβdef
  have hβ : ∀ (y : ↥H) (k : ↥K), β y (π k) = π (conjK (hKn y.2) k) :=
    indHom_apply π hπ hker hKn hHN
  have hQ := sup_l1_eq_X_F4 S h1332 hL3 hL1K hker hD
  have hKin : ∀ k (hk : k ∈ K), β ⟨k, hKH hk⟩ = MulAut.conj (π ⟨k, hk⟩) := by
    intro k hk
    apply MulEquiv.ext
    intro a
    obtain ⟨x, rfl⟩ := hπ a
    rw [hβ, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
  have hInn : ∀ y : ↥H, β y ∈ (MulAut.conj : A6.SL3.S →* MulAut A6.SL3.S).range := by
    have hle : K ⊔ T ≤ ((innS).comap β).map H.subtype :=
      sup_le (fun k hk => ⟨⟨k, hKH hk⟩, ⟨π ⟨k, hk⟩, (hKin k hk).symm⟩, rfl⟩)
        (fun t ht => ⟨⟨t, hTH ht⟩,
          T_inner_sl3_F4 S h1332 hKn hHN hπ hker hD hQ t (hTH ht) ht, rfl⟩)
    rw [← hHKT] at hle
    intro y
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have e : y = y' := Subtype.ext hyy'.symm
    rw [e]
    exact hy'
  have hZ : Subgroup.center (cStar K) = ⊥ := by
    obtain ⟨φ⟩ := isPSL_three_two_iff.mp hP
    have hc := card_center_eq_of_mulEquiv φ
    rw [sl3_center_eq_bot, Subgroup.card_bot] at hc
    exact Subgroup.card_eq_one.mp hc
  obtain ⟨ψ, hψ, hψker⟩ := quotIso_of_range π hπ hker hKH hKn hHN MulAut.conj sl3_conj_injective
    hInn fun x hx hxc => mem_pCoreOf_of_comm_F4 h28 S hcK' hL1K hKn hZ hx hxc
  have hψs : Function.Surjective ψ := by
    intro g
    obtain ⟨k, rfl⟩ := hπ g
    refine ⟨⟨k, hKH k.2⟩, sl3_conj_injective ?_⟩
    rw [hψ, hKin k k.2]
  exact (h11 _ T L V H S).1 ⟨ψ, hψs, hψker⟩

end CFSG.Quasithin.H13.L32A.C
