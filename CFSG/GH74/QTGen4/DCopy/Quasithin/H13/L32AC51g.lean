module

public import CFSG.Quasithin.H13.L32AC51g
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC47k

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem uni_le_normalizer_F4 (h1332 : Stmt13_3_2_F4) (S : Setting147 G T L V H) {K : Subgroup G}
    {n : ℕ} {π : ↥K →* Lin.SLn n} (hD : (T.subgroupOf K).map π = unitriangular n (ZMod 2)) :
    unitriangular n (ZMod 2) ≤
      Subgroup.normalizer ((((l1 T L V).subgroupOf K).map π : Subgroup (Lin.SLn n)) :
        Set (Lin.SLn n)) := by
  have hTl1 := T_le_normalizer_l1_F4 h1332 S
  set R := ((l1 T L V).subgroupOf K).map π with hR
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

theorem exists_node_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) {K : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hL1K : l1 T L V ≤ K)
    {π : ↥K →* Lin.SLn n} (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = unitriangular n (ZMod 2)) :
    ∃ i₀, 1 ≤ i₀ ∧ i₀ < n ∧
      unitriangular n (ZMod 2) ⊔ ((l1 T L V).subgroupOf K).map π = Lin.par n i₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL3 := relIndex_l1_F4 h1222 h1332 h1334 S.hyp
  set R := ((l1 T L V).subgroupOf K).map π with hR
  have hRU := uni_le_normalizer_F4 h1332 S hD
  set d := (unitriangular n (ZMod 2)).relIndex (unitriangular n (ZMod 2) ⊔ R) with hdd

  have hd := relIndex_sup_dvd_card hRU
  have hRl : Nat.card R ∣ Nat.card (l1 T L V) := by
    have := Subgroup.card_map_dvd ((l1 T L V).subgroupOf K) π
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL1K).toEquiv] at this
  have hl1 : Nat.card (l1 T L V) = 3 * Nat.card (pCoreOf 2 (l1 T L V)) := by
    have hle : pCoreOf 2 (l1 T L V) ≤ l1 T L V := Subgroup.map_subtype_le _
    have := Subgroup.relIndex_mul_card (H := pCoreOf 2 (l1 T L V)) (K := l1 T L V)
    rw [inf_eq_left.mpr hle, hL3] at this
    exact this.symm
  obtain ⟨e, he⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
  have hodd : ¬ 2 ∣ d := fun h2 =>
    (Lin.uni_sylow (n := n) (by omega)).2 (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))
  have hcop : Nat.Coprime d (2 ^ e) :=
    Nat.Coprime.pow_right e ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_two).mpr hodd)))
  have hd3 : d ∣ 3 := by
    have h1 : d ∣ 3 * 2 ^ e := by
      rw [← he, ← hl1]
      exact hd.trans hRl
    exact hcop.dvd_of_dvd_mul_right h1
  have hle3 : d ≤ 3 := Nat.le_of_dvd (by norm_num) hd3
  rcases BinaryParabolic.eq_or_eq_parabolic le_sup_left hle3 with hUR | ⟨j, ⟨hj, hjn, hjP⟩, -⟩
  · exfalso
    obtain ⟨y, hy, hyodd, hyK⟩ := exists_gen_not_mem hL3 K
    have hyl1 : y ∈ l1 T L V := Subgroup.subset_closure ⟨hy, hyodd⟩
    have hyR : π ⟨y, hL1K hyl1⟩ ∈ unitriangular n (ZMod 2) := by
      rw [← hUR]
      exact Subgroup.mem_sup_right ⟨⟨y, hL1K hyl1⟩, hyl1, rfl⟩
    obtain ⟨m, hm⟩ := (Lin.uni_sylow (n := n) (by omega)).1 ⟨_, hyR⟩
    have hyn : (π ⟨y, hL1K hyl1⟩) ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    have hyo : (π ⟨y, hL1K hyl1⟩) ^ orderOf y = 1 := by
      rw [← map_pow, show (⟨y, hL1K hyl1⟩ : ↥K) ^ orderOf y = 1 from Subtype.ext (by
        simp [pow_orderOf_eq_one]), map_one]
    have h1 : orderOf (π ⟨y, hL1K hyl1⟩) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hyo)
        (Nat.Coprime.pow_right m (Nat.coprime_two_right.mpr hyodd)))
        (orderOf_dvd_of_pow_eq_one hyn)
    exact hyK ((hker _).mp (orderOf_eq_one_iff.mp h1))
  · exact ⟨j, hj, hjn, hjP⟩

theorem T_maps_F4 (h1332 : Stmt13_3_2_F4) (S : Setting147 G T L V H) {K : Subgroup G} {n : ℕ}
    (hKn : H ≤ Subgroup.normalizer (K : Set G))
    (hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G)) {π : ↥K →* Lin.SLn n}
    (hπ : Function.Surjective π) (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = unitriangular n (ZMod 2)) (t : G) (ht : t ∈ H)
    (htT : t ∈ T) :
    (∀ u ∈ unitriangular n (ZMod 2), indHom π hπ hker hKn hHN ⟨t, ht⟩ u ∈
      unitriangular n (ZMod 2)) ∧
    ∀ g ∈ unitriangular n (ZMod 2) ⊔ ((l1 T L V).subgroupOf K).map π,
      indHom π hπ hker hKn hHN ⟨t, ht⟩ g ∈
        unitriangular n (ZMod 2) ⊔ ((l1 T L V).subgroupOf K).map π := by
  have hTl1 := T_le_normalizer_l1_F4 h1332 S
  set β := indHom π hπ hker hKn hHN ⟨t, ht⟩ with hβdef
  have hβ : ∀ k : ↥K, β (π k) = π (conjK (hKn ht) k) := indHom_apply π hπ hker hKn hHN _
  set R := ((l1 T L V).subgroupOf K).map π with hR
  have hP0 : ∀ p ∈ unitriangular n (ZMod 2), β p ∈ unitriangular n (ZMod 2) := by
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
  refine ⟨hP0, fun x hx => ?_⟩
  have hle : (unitriangular n (ZMod 2) ⊔ R).map β.toMonoidHom ≤ unitriangular n (ZMod 2) ⊔ R := by
    rw [Subgroup.map_sup]
    exact sup_le_sup (fun _ ⟨p, hp, hpe⟩ => hpe ▸ hP0 p hp) (fun _ ⟨r, hr, hre⟩ => hre ▸ hRR r hr)
  exact hle ⟨x, hx, rfl⟩

end CFSG.Quasithin.H13.L32A.C
