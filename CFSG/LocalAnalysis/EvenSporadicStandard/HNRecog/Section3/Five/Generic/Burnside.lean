module

public import Mathlib.GroupTheory.Transfer
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

variable {G : Type*} [Group G]

private theorem mem_closure_pair_of_involutions {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) {g : G} :
    g ∈ Subgroup.closure ({x, y} : Set G) ↔ g = 1 ∨ g = x ∨ g = y ∨ g = x * y := by
  have hx' : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hyx : y * x = x * y := hxy.symm
  have hyx' : ∀ z, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, hyx, mul_assoc]
  constructor
  · intro hg
    induction hg using Subgroup.closure_induction with
    | mem z hz =>
      rcases hz with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    | one => exact Or.inl rfl
    | mul p q _ _ hp hq =>
      rcases hp with rfl | rfl | rfl | rfl <;> rcases hq with rfl | rfl | rfl | rfl <;>
        simp only [mul_assoc, one_mul, mul_one, hx, hy, hx', hyx, hyx', true_or, or_true]
    | inv z _ hz =>
      have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
      have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
      rcases hz with rfl | rfl | rfl | rfl <;>
        simp only [inv_one, hxinv, hyinv, mul_inv_rev, hyx, true_or, or_true]
  · rintro (rfl | rfl | rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (Or.inl rfl)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (Or.inl rfl))
        (Subgroup.subset_closure (Or.inr rfl))

private theorem commute_and_mul_self_of_mem_closure_pair {x y : G} (hx : x * x = 1)
    (hy : y * y = 1) (hxy : x * y = y * x) {g h : G}
    (hg : g ∈ Subgroup.closure ({x, y} : Set G)) (hh : h ∈ Subgroup.closure ({x, y} : Set G)) :
    g * h = h * g ∧ g * g = 1 := by
  have hx' : ∀ z, x * (x * z) = z := fun z => by rw [← mul_assoc, hx, one_mul]
  have hyx : y * x = x * y := hxy.symm
  have hyx' : ∀ z, y * (x * z) = x * (y * z) := fun z => by rw [← mul_assoc, hyx, mul_assoc]
  rw [mem_closure_pair_of_involutions hx hy hxy] at hg hh
  rcases hg with rfl | rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl | rfl <;>
    simp only [mul_assoc, one_mul, mul_one, hx, hy, hx', hyx, hyx', and_self]

private theorem card_closure_pair_of_involutions {x y : G} (hx : x * x = 1) (hy : y * y = 1)
    (hxy : x * y = y * x) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hne : x ≠ y) :
    Nat.card ↥(Subgroup.closure ({x, y} : Set G)) = 4 := by
  have hset : ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) = {1, x, y, x * y} := by
    ext g
    simp only [SetLike.mem_coe, mem_closure_pair_of_involutions hx hy hxy, Set.mem_insert_iff,
      Set.mem_singleton_iff]
  have hxy1 : x * y ≠ 1 := fun h => hne (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right hx])
  change Nat.card ((Subgroup.closure ({x, y} : Set G) : Subgroup G) : Set G) = 4
  rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem,
    Set.ncard_insert_of_notMem, Set.ncard_singleton]
  · simpa using hx1
  · simpa [not_or] using ⟨hne, hy1⟩
  · simpa [not_or, eq_comm] using ⟨hx1, hy1, hxy1⟩

private theorem exists_normal_two_complement_transport {K : Subgroup G} [Finite K]
    {T : Subgroup G} (hTK : T ≤ K) (P : Sylow 2 ↥K)
    (hPcoe : (P : Subgroup ↥K) = T.subgroupOf K)
    (hP : Subgroup.normalizer (P : Set ↥K) ≤ Subgroup.centralizer (P : Set ↥K)) :
    ∃ N : Subgroup G, N ≤ K ∧ (N.subgroupOf K).Normal ∧ ¬ 2 ∣ Nat.card ↥N ∧
      N ⊓ T = ⊥ ∧ N ⊔ T = K := by
  let N₀ : Subgroup ↥K := (MonoidHom.transferSylow P hP).ker
  have hcomp : Subgroup.IsComplement' N₀ P := MonoidHom.ker_transferSylow_isComplement' P hP
  have hN₀normal : N₀.Normal := MonoidHom.normal_ker (MonoidHom.transferSylow P hP)
  have hN₀card : ¬ 2 ∣ Nat.card ↥N₀ := MonoidHom.not_dvd_card_ker_transferSylow P hP
  refine ⟨N₀.map K.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · calc N₀.map K.subtype ≤ K.subtype.range := Subgroup.map_le_range (f := K.subtype) N₀
      _ = K := Subgroup.range_subtype K
  · have hsub : (N₀.map K.subtype).subgroupOf K = N₀ := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨y, hy, hyx⟩
        have hxy : y = x := K.subtype_injective hyx
        simpa [hxy] using hy
      · intro hx; exact ⟨x, hx, rfl⟩
    rw [hsub]; exact hN₀normal
  · rw [Subgroup.card_subtype K N₀]; exact hN₀card
  · apply le_antisymm _ bot_le
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxN, hxT⟩ := hx
    rw [Subgroup.mem_map] at hxN
    obtain ⟨y, hyN, hyx⟩ := hxN
    have hyP : y ∈ (P : Subgroup ↥K) := by
      rw [hPcoe, Subgroup.mem_subgroupOf]
      show ((y : ↥K) : G) ∈ T
      have hyx' : ((y : ↥K) : G) = x := hyx
      rw [hyx']
      exact hxT
    have hybot : y ∈ (⊥ : Subgroup ↥K) := hcomp.disjoint.le_bot ⟨hyN, hyP⟩
    have hy1 : y = 1 := by simpa using hybot
    have : x = 1 := by rw [← hyx, hy1]; rfl
    exact Subgroup.mem_bot.mpr this
  · have htop : (⊤ : Subgroup ↥K).map K.subtype = K := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · rintro ⟨y, -, rfl⟩; exact y.2
      · intro hx; exact ⟨⟨x, hx⟩, trivial, rfl⟩
    have hPmap : P.map K.subtype = T := by
      rw [hPcoe, Subgroup.map_subgroupOf_eq_of_le hTK]
    calc N₀.map K.subtype ⊔ T = N₀.map K.subtype ⊔ P.map K.subtype := by rw [hPmap]
      _ = (N₀ ⊔ P).map K.subtype := (Subgroup.map_sup N₀ P K.subtype).symm
      _ = (⊤ : Subgroup ↥K).map K.subtype := by rw [hcomp.sup_eq_top]
      _ = K := htop

theorem exists_normal_two_complement_of_klein {K : Subgroup G} [Finite K] {a u : G} (haK : a ∈ K)
    (huK : u ∈ K) (ha : a * a = 1) (hu : u * u = 1) (hau : a * u = u * a) (ha1 : a ≠ 1)
    (hu1 : u ≠ 1) (hne : a ≠ u) (hsyl : padicValNat 2 (Nat.card ↥K) = 2)
    (hfix : ∀ n ∈ K, n ∈ Subgroup.normalizer
      ((Subgroup.closure ({a, u} : Set G) : Subgroup G) : Set G) → n * a = a * n) :
    ∃ N : Subgroup G, N ≤ K ∧ (N.subgroupOf K).Normal ∧ ¬ 2 ∣ Nat.card ↥N ∧
      N ⊓ Subgroup.closure ({a, u} : Set G) = ⊥ ∧
      N ⊔ Subgroup.closure ({a, u} : Set G) = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Subgroup G := Subgroup.closure ({a, u} : Set G)
  have haT : a ∈ T := Subgroup.subset_closure (by simp)
  have huT : u ∈ T := Subgroup.subset_closure (by simp)
  have hTK : T ≤ K :=
    (Subgroup.closure_le (k := ({a, u} : Set G)) (K := K)).2 (by
      rintro x (rfl | rfl)
      · exact haK
      · exact huK)
  have hcardT : Nat.card T = 4 := card_closure_pair_of_involutions ha hu hau ha1 hu1 hne
  have hcardSub : Nat.card (T.subgroupOf K) = 4 := by
    rw [← Subgroup.card_subtype K (T.subgroupOf K),
      Subgroup.map_subgroupOf_eq_of_le hTK, hcardT]
  have hnotdvd : ¬ 2 ∣ (T.subgroupOf K).index := by
    intro h2
    obtain ⟨m, hm⟩ := h2
    have h8 : 2 ^ 3 ∣ Nat.card ↥K := by
      rw [← Subgroup.card_mul_index (T.subgroupOf K), hcardSub, hm]
      exact ⟨m, by ring⟩
    have hnot := pow_succ_padicValNat_not_dvd (p := 2) (n := Nat.card ↥K) Nat.card_pos.ne'
    rw [hsyl] at hnot
    exact hnot h8
  have hT2 : IsPGroup 2 (T.subgroupOf K) :=
    IsPGroup.of_card (n := 2) (by rw [hcardSub]; norm_num)
  let P : Sylow 2 ↥K := hT2.toSylow hnotdvd
  have hPcoe : (P : Subgroup ↥K) = T.subgroupOf K := IsPGroup.toSylow_coe hT2 hnotdvd
  have hPnle : Subgroup.normalizer (P : Set ↥K) ≤ Subgroup.centralizer (P : Set ↥K) := by
    intro n hn
    have hnGnorm : (n : G) ∈ Subgroup.normalizer (T : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxK : x ∈ K := hTK hx
        have hxP : (⟨x, hxK⟩ : ↥K) ∈ (P : Subgroup ↥K) := by
          show (⟨x, hxK⟩ : ↥K) ∈ T.subgroupOf K
          exact hx
        have hmem := ((Subgroup.mem_normalizer_iff.mp hn) (⟨x, hxK⟩ : ↥K)).mp hxP
        rw [hPcoe, Subgroup.mem_subgroupOf] at hmem
        simpa using hmem
      · intro hx
        have hyK : (n : G) * x * (n : G)⁻¹ ∈ K := hTK hx
        have hxK : x ∈ K := by
          have hx' : x = (n : G)⁻¹ * ((n : G) * x * (n : G)⁻¹) * (n : G) := by group
          rw [hx']
          exact K.mul_mem (K.mul_mem (K.inv_mem n.2) hyK) n.2
        exact ((Subgroup.mem_normalizer_iff.mp hn) (⟨x, hxK⟩ : ↥K)).mpr (by
          rw [hPcoe, Subgroup.mem_subgroupOf]
          show ((n : G) * x * (n : G)⁻¹) ∈ T
          exact hx)
    have hna : (n : G) * a = a * (n : G) := hfix (n : G) n.2 hnGnorm
    have hnu_mem : (n : G) * u * (n : G)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hnGnorm u).mp huT
    have hnu_sq : ((n : G) * u * (n : G)⁻¹) ^ 2 = 1 := by
      rw [sq]
      calc ((n : G) * u * (n : G)⁻¹) * ((n : G) * u * (n : G)⁻¹)
          = (n : G) * (u * u) * (n : G)⁻¹ := by group
        _ = 1 := by rw [hu]; group
    have hnu_ne_one : (n : G) * u * (n : G)⁻¹ ≠ 1 := by
      intro h
      have : u = 1 := by
        have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h
        simpa [mul_assoc] using this
      exact hu1 this
    have hnu_ne_a : (n : G) * u * (n : G)⁻¹ ≠ a := by
      intro h
      have hainv : (n : G)⁻¹ * a * (n : G) = a := by
        have h := congrArg (fun z => (n : G)⁻¹ * z) hna
        simpa [mul_assoc] using h.symm
      have : u = a := by
        have := congrArg (fun z => (n : G)⁻¹ * z * (n : G)) h
        simpa [hainv, mul_assoc] using this
      exact hne this.symm
    have hcases : (n : G) * u * (n : G)⁻¹ = u ∨ (n : G) * u * (n : G)⁻¹ = a * u := by
      have := (mem_closure_pair_of_involutions ha hu hau).mp hnu_mem
      rcases this with h | h | h | h
      · exact absurd h hnu_ne_one
      · exact absurd h hnu_ne_a
      · exact Or.inl h
      · exact Or.inr h
    rcases hcases with hcase | hcase
    · have hnu : (n : G) * u = u * (n : G) := by
        have := congrArg (fun z => z * (n : G)) hcase
        simpa [mul_assoc] using this
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hpT : (p : G) ∈ T := by
        have hp' : p ∈ T.subgroupOf K := hPcoe ▸ hp
        exact hp'
      apply Subtype.ext
      change (p : G) * (n : G) = (n : G) * (p : G)
      rcases (mem_closure_pair_of_involutions ha hu hau).mp hpT with h | h | h | h
      · rw [h]; simp
      · rw [h]; exact hna.symm
      · rw [h]; exact hnu.symm
      · rw [h]
        calc (a * u) * (n : G) = a * (u * (n : G)) := by group
          _ = a * ((n : G) * u) := by rw [hnu]
          _ = (a * (n : G)) * u := by group
          _ = ((n : G) * a) * u := by rw [hna]
          _ = (n : G) * (a * u) := by group
    · exfalso
      let M : Subgroup G := T ⊔ Subgroup.zpowers (n : G)
      have hTM : T ≤ M := le_sup_left
      have hMK : M ≤ K := sup_le hTK (Subgroup.zpowers_le.mpr n.2)
      have hnM : (n : G) ∈ M := Subgroup.mem_sup_right (Subgroup.mem_zpowers (n : G))
      have hnC : (n : G) ∉ Subgroup.centralizer (T : Set G) := by
        intro h
        have hcomm := (Subgroup.mem_centralizer_iff.mp h) u huT
        have hconj : (n : G) * u * (n : G)⁻¹ = u := by
          rw [← hcomm]; group
        rw [hcase] at hconj
        have : a = 1 := by
          have := congrArg (fun z => z * u) hconj
          simpa [hu, mul_assoc] using this
        exact ha1 this
      have hul : (n : G) * u = (a * u) * (n : G) := by
        calc (n : G) * u = ((n : G) * u * (n : G)⁻¹) * (n : G) := by group
          _ = (a * u) * (n : G) := by rw [hcase]
      have hn2a : (n : G) * (n : G) * a = a * ((n : G) * (n : G)) := by
        calc (n : G) * (n : G) * a = (n : G) * ((n : G) * a) := by group
          _ = (n : G) * (a * (n : G)) := by rw [hna]
          _ = ((n : G) * a) * (n : G) := by group
          _ = (a * (n : G)) * (n : G) := by rw [hna]
          _ = a * ((n : G) * (n : G)) := by group
      have hnau : (n : G) * (a * u) = u * (n : G) := by
        calc (n : G) * (a * u) = ((n : G) * a) * u := by group
          _ = (a * (n : G)) * u := by rw [hna]
          _ = a * ((n : G) * u) := by group
          _ = a * ((a * u) * (n : G)) := by rw [hul]
          _ = (a * (a * u)) * (n : G) := by group
          _ = u * (n : G) := by rw [← mul_assoc, ha, one_mul]
      have hn2u : (n : G) * (n : G) * u = u * ((n : G) * (n : G)) := by
        calc (n : G) * (n : G) * u = (n : G) * ((n : G) * u) := by group
          _ = (n : G) * ((a * u) * (n : G)) := by rw [hul]
          _ = ((n : G) * (a * u)) * (n : G) := by group
          _ = (u * (n : G)) * (n : G) := by rw [hnau]
          _ = u * ((n : G) * (n : G)) := by group
      have hn2cent : (n : G) * (n : G) ∈ Subgroup.centralizer (T : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        rcases (mem_closure_pair_of_involutions ha hu hau).mp ht with h | h | h | h
        · rw [h]; simp
        · rw [h]; exact hn2a.symm
        · rw [h]; exact hn2u.symm
        · rw [h]
          calc (a * u) * ((n : G) * (n : G))
              = a * (u * ((n : G) * (n : G))) := by group
            _ = a * (((n : G) * (n : G)) * u) := by rw [← hn2u]
            _ = (a * ((n : G) * (n : G))) * u := by group
            _ = (((n : G) * (n : G)) * a) * u := by rw [← hn2a]
            _ = ((n : G) * (n : G)) * (a * u) := by group
      have hMn : M ≤ Subgroup.normalizer (T : Set G) :=
        sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hnGnorm)
      let D : Subgroup ↥M := (Subgroup.centralizer (T : Set G)).subgroupOf M
      have hDeq : D = ((Subgroup.centralizer (T : Set G)).subgroupOf
          (Subgroup.normalizer (T : Set G))).comap (Subgroup.inclusion hMn) := by
        rw [Subgroup.comap_inclusion_subgroupOf]
      have hDnormal : D.Normal := by
        haveI : ((Subgroup.centralizer (T : Set G)).subgroupOf
            (Subgroup.normalizer (T : Set G))).Normal :=
          Subgroup.normal_subgroupOf_centralizer_normalizer (T : Set G)
        rw [hDeq]
        infer_instance
      haveI := hDnormal
      have hTsub_le_D : (T.subgroupOf M) ≤ D := by
        intro x hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [Subgroup.mem_subgroupOf]
        rw [Subgroup.mem_centralizer_iff]
        intro t ht
        exact (commute_and_mul_self_of_mem_closure_pair ha hu hau hx ht).1.symm
      let m : ↥M := ⟨(n : G), hnM⟩
      have hnD : m ∉ D := by
        intro h
        rw [Subgroup.mem_subgroupOf] at h
        exact hnC h
      let q : ↥M ⧸ D := QuotientGroup.mk' D m
      have hq_ne : q ≠ 1 := by
        intro h
        apply hnD
        have := (QuotientGroup.eq_one_iff (N := D) m).mp (by simpa [q] using h)
        simpa using this
      have hm2D : m * m ∈ D := by
        rw [Subgroup.mem_subgroupOf]
        show ((n : G) * (n : G)) ∈ Subgroup.centralizer (T : Set G)
        exact hn2cent
      have hq_sq : q * q = 1 := by
        change (QuotientGroup.mk' D m) * (QuotientGroup.mk' D m) = 1
        rw [← map_mul]
        change ((m * m : ↥M) : ↥M ⧸ D) = 1
        exact (QuotientGroup.eq_one_iff (N := D) (m * m)).mpr hm2D
      have hq_order : orderOf q = 2 :=
        orderOf_eq_prime (p := 2) (by simpa [sq] using hq_sq) hq_ne
      have h2dvdD : 2 ∣ D.index := by
        rw [Subgroup.index_eq_card]
        have := orderOf_dvd_natCard q
        rwa [hq_order] at this
      have h2dvdM : 2 ∣ T.relIndex M := by
        change 2 ∣ (T.subgroupOf M).index
        rw [← Subgroup.relIndex_mul_index (H := T.subgroupOf M) (K := D) hTsub_le_D]
        exact dvd_mul_of_dvd_right h2dvdD _
      have hnotdvdM : ¬ 2 ∣ T.relIndex M := by
        intro h
        apply (show ¬ 2 ∣ T.relIndex K from hnotdvd)
        have hdvd : T.relIndex M ∣ T.relIndex K := by
          rw [← Subgroup.relIndex_mul_relIndex (H := T) (K := M) (L := K) hTM hMK]
          exact dvd_mul_right _ _
        exact h.trans hdvd
      exact hnotdvdM h2dvdM
  exact exists_normal_two_complement_transport hTK P hPcoe hPnle

theorem exists_normal_two_complement_of_involution {K : Subgroup G} [Finite K] {a : G} (haK : a ∈ K)
    (ha : a * a = 1) (ha1 : a ≠ 1) (hsyl : padicValNat 2 (Nat.card ↥K) = 1) :
    ∃ N : Subgroup G, N ≤ K ∧ (N.subgroupOf K).Normal ∧ ¬ 2 ∣ Nat.card ↥N ∧
      N ⊓ Subgroup.zpowers a = ⊥ ∧ N ⊔ Subgroup.zpowers a = K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let T : Subgroup G := Subgroup.zpowers a
  have hTK : T ≤ K := Subgroup.zpowers_le.mpr haK
  have horder : orderOf a = 2 := orderOf_eq_prime (p := 2) (by simpa [sq] using ha) ha1
  have hcardT : Nat.card T = 2 := by
    change Nat.card (Subgroup.zpowers a) = 2
    rw [Nat.card_zpowers, horder]
  have hcardSub : Nat.card (T.subgroupOf K) = 2 := by
    rw [← Subgroup.card_subtype K (T.subgroupOf K),
      Subgroup.map_subgroupOf_eq_of_le hTK, hcardT]
  have hnotdvd : ¬ 2 ∣ (T.subgroupOf K).index := by
    intro h2
    obtain ⟨m, hm⟩ := h2
    have h4 : 2 ^ 2 ∣ Nat.card ↥K := by
      rw [← Subgroup.card_mul_index (T.subgroupOf K), hcardSub, hm]
      exact ⟨m, by ring⟩
    have hnot := pow_succ_padicValNat_not_dvd (p := 2) (n := Nat.card ↥K) Nat.card_pos.ne'
    rw [hsyl] at hnot
    exact hnot h4
  have hT2 : IsPGroup 2 (T.subgroupOf K) :=
    IsPGroup.of_card (n := 1) (by rw [hcardSub]; norm_num)
  let P : Sylow 2 ↥K := hT2.toSylow hnotdvd
  have hPcoe : (P : Subgroup ↥K) = T.subgroupOf K := IsPGroup.toSylow_coe hT2 hnotdvd
  have hPcard : Nat.card (P : Subgroup ↥K) = 2 := by rw [hPcoe]; exact hcardSub
  have hPcyc : IsCyclic P := isCyclic_of_prime_card (p := 2) hPcard
  have h2dvd : 2 ∣ Nat.card ↥K := dvd_of_one_le_padicValNat (by rw [hsyl])
  have hmin : (Nat.card ↥K).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2dvd
  have hP : Subgroup.normalizer (P : Set ↥K) ≤ Subgroup.centralizer (P : Set ↥K) :=
    hPcyc.normalizer_le_centralizer hmin
  exact exists_normal_two_complement_transport hTK P hPcoe hP

end CFSG.EvenSporadicStandard.HNRecog.Section3
