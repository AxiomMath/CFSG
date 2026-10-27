module

public import CFSG.ClassicalInvolution.AschTight.S1916HalfA
public import CFSG.ClassicalInvolution.AschTight.S1911C11

public section

namespace CFSG.ClassicalInvolution.Disconnected.AschTight.S1916

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {K : Subgroup G} {z : G}
  {S : Sylow 2 G} {W L : Subgroup G} {t : G} {V : Subgroup G}

theorem mem_centralizer_of_mem_cStar (hd : Sec19Data p f K z S W) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hx : x ∈ centralizerModOdd ⊤ K) :
    ∀ r ∈ (S : Subgroup G) ⊓ K, x * r = r * x :=
  fun _ hr => commute_of_mem_centralizerModOdd hx inf_le_right (S.isPGroup'.to_le inf_le_left)
    (mem_normalizer_inf_of_mem hxS ((sd_normalizer_eq hd).ge (hd.hSz hxS))) hr

theorem mem_cStar_of_mem_centralizer [IsSimpleGroup G] (hd : Sec19Data p f K z S W) {x : G}
    (hxS : x ∈ (S : Subgroup G)) (hxR : ∀ r ∈ (S : Subgroup G) ⊓ K, x * r = r * x) :
    x ∈ centralizerModOdd ⊤ K := by
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := (sd_normalizer_eq hd).ge (hd.hSz hxS)
  exact ⟨Subgroup.mem_top x, hxN, mem_normalizer_oddCoreOf_of_mem_normalizer hxN,
    fun k hk => commutator_mem_oddCoreOf_of_centralizes hd.tight (sd_isSylow2In_R hd)
      (S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hxS)) hxN (fun r hr => (hxR r hr).symm) hk⟩

theorem mem_W_inf_of_mem_centralizer_t [IsSimpleGroup G] (h11b : C19_11bTmp p f)
    (hd : Sec19DataT p f K z S W L t V) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxR : ∀ r ∈ (S : Subgroup G) ⊓ K, x * r = r * x) (hxt : x * t = t * x) :
    x ∈ W ⊓ sec19Y K z := by
  have hd0 := hd.toSec19Data
  have htb := hd.tight.toTightBranch
  have hxC : x ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun r hr => (hxR r hr).symm
  have hxtC : x ∈ Subgroup.centralizer ({t} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hxt
  obtain ⟨RL, hRL, w, hw, hc⟩ := S1911.exists_mul_eq_of_mem_A hd hxS hxC hxtC
  have hLN := S1911.centralizer_le_normalizer_member htb hd.memL hd.invL
  have hWt : W ≤ Subgroup.centralizer ({t} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (S1911.comm_of_mem hd0 y hy t (S1911.mem_W hd))
  have hcS : x * w⁻¹ ∈ (S : Subgroup G) := (S : Subgroup G).mul_mem hxS
    ((S : Subgroup G).inv_mem (hd.hWS hw.1))
  have hcL : x * w⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    Subgroup.mul_mem _ (hLN hxtC) (Subgroup.inv_mem _ (hLN (hWt hw.1)))
  have hcLs := S1911.mem_centralizerModOdd_of_mem_centralizer hd hcS hcL hRL hc
  have hcR : x * w⁻¹ ∈ Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hw.2)
  have hcW : x * w⁻¹ ∈ Subgroup.centralizer (W : Set G) := by
    have hle : W ≤ Subgroup.centralizer ({x * w⁻¹} : Set G) := by
      rw [S1911.sup_eq_inf_sup hd]
      refine sup_le (fun u hu => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hcR u ⟨hd.hWS hu.2, hu.1⟩))
      · have hvSL : v ∈ (S : Subgroup G) ⊓ L :=
          ⟨hd.hWS (hd.leW hv), S1911.le_member hd hv⟩
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (commute_of_mem_centralizerModOdd hcLs inf_le_right (S.isPGroup'.to_le inf_le_left)
            (mem_normalizer_inf (Subgroup.le_normalizer hcS) hcL) hvSL).symm
    exact Subgroup.mem_centralizer_iff.mpr fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hy))
  have hbot := h11b G K z S W L t V hd
  have hmem : x * w⁻¹ ∈ (S : Subgroup G) ⊓
      Subgroup.centralizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) ⊓
      Subgroup.centralizer (W : Set G) ⊓ centralizerModOdd ⊤ L := ⟨⟨⟨hcS, hcR⟩, hcW⟩, hcLs⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have hxw : x = w := by
    calc x = x * w⁻¹ * w := by group
      _ = w := by rw [hmem, one_mul]
  rw [hxw, S1911.inf_sec19Y_eq hd0]
  exact hw

theorem eq_of_mul_self_eq_one_of_isCyclic {C : Subgroup G} (hC : IsCyclic C) {a b : G}
    (ha : a ∈ C) (hb : b ∈ C) (ha2 : a * a = 1) (hb2 : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  classical
  have := Fintype.ofFinite C
  by_contra hab
  have hsub : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset C) ⊆
      Finset.univ.filter (fun x : C => x ^ 2 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hx with rfl | rfl | rfl
    · exact one_pow 2
    · exact Subtype.ext (by simpa [sq] using ha2)
    · exact Subtype.ext (by simpa [sq] using hb2)
  have h1 := Finset.card_le_card hsub
  have h2 := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) two_pos
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset C).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun h => hab (congrArg Subtype.val h)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => ha1 (congrArg Subtype.val h).symm,
        fun h => hb1 (congrArg Subtype.val h).symm⟩
  omega

theorem isUniqueInvolution_W_inf [IsSimpleGroup G] (hd : Sec19DataT p f K z S W L t V) :
    IsUniqueInvolution (W ⊓ sec19Y K z) z := by
  have hd0 := hd.toSec19Data
  have hzK := isUniqueInvolution_of_tight hd.tight.toTightBranch
  have hcyc := S1911.isCyclic_inf_sec19Y hd
  have hU2 : IsPGroup 2 ↥(K ⊓ W) := S.isPGroup'.to_le (inf_le_right.trans hd.hWS)
  have hU4 : 2 ≤ Nat.card ↥(K ⊓ W) := by
    rw [S1911.card_inf_eq_card hd]
    have := S1911.four_le_card hd
    omega
  have hzW : z ∈ W := (AscL62.mem_of_uniqueInvolution_of_pGroup hzK inf_le_left hU2 hU4).2
  have hzWY : z ∈ W ⊓ sec19Y K z := ⟨hzW, sd_mem_Y hd0⟩
  refine ⟨hzWY, hzK.ne_one, hzK.sq, fun y hy hy2 => ?_⟩
  by_cases hy1 : y = 1
  · exact Or.inl hy1
  exact Or.inr (eq_of_mul_self_eq_one_of_isCyclic hcyc hy hzWY hy2 hzK.sq hy1 hzK.ne_one)

theorem conj_t_eq_or_of_mem_centralizer [IsSimpleGroup G] (hd : Sec19DataT p f K z S W L t V)
    (hinv : ∀ s ∈ (S : Subgroup G), conjSub s W = W) {x : G} (hxS : x ∈ (S : Subgroup G))
    (hxR : ∀ r ∈ (S : Subgroup G) ⊓ K, x * r = r * x) :
    x * t * x⁻¹ = t ∨ x * t * x⁻¹ = t * z := by
  have hd0 := hd.toSec19Data
  have htW : t ∈ W := S1911.mem_W hd
  have htS : t ∈ (S : Subgroup G) := hd.hWS htW
  have hxW : x * t * x⁻¹ ∈ W := hinv x hxS ▸ conj_mem_conjSub htW
  have htN : t ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ K : Subgroup G) : Set G) :=
    mem_normalizer_inf_of_mem htS ((sd_normalizer_eq hd0).ge (hd0.hSz htS))
  have hcomm := commutator_comm_of_normalizes hxR htN
  have hcW : x * t * x⁻¹ * t⁻¹ ∈ W := W.mul_mem hxW (W.inv_mem htW)
  have hcY : x * t * x⁻¹ * t⁻¹ ∈ W ⊓ sec19Y K z := by
    rw [S1911.inf_sec19Y_eq hd0]
    exact ⟨hcW, Subgroup.mem_centralizer_iff.mpr fun r hr => (hcomm r hr).symm⟩
  exact conj_eq_or_of_mem (S1911.comm_of_mem hd0) htW hd.invL.sq hxW
    (isUniqueInvolution_W_inf hd) hcY

end CFSG.ClassicalInvolution.Disconnected.AschTight.S1916
