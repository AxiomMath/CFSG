module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporCert
public import CFSG.Sporadic.J4.QTOutChar

public section

namespace CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT

@[expose] noncomputable def zJ : J := eta uJ 11 1131

theorem zJ_sq :
    zJ * zJ = 1 := eta_sq (elem_uJ j4Facts.mat) 1131

theorem zJ_ne_one
    : zJ ≠ 1 := eta_ne_one j4Facts.mat (by norm_num) (by norm_num)

theorem aut_fix_zJ
    (α : MulAut J) (hα : ∀ x, α x ∈ P0 ↔ x ∈ P0) : α zJ = zJ := by
  have hM := j4Facts.mat
  have h1 := (Zc_invariant α hα 1 zJ).2
  have hz : zJ ∈ Zc 1 := by
    rw [Zc_eq hM j4Facts 1 (by norm_num)]
    exact ⟨1131, by simp [ucsMasks], rfl⟩
  have h2 := h1 hz
  rw [Zc_eq hM j4Facts 1 (by norm_num)] at h2
  obtain ⟨c, hc, hcz⟩ := h2
  simp only [ucsMasks, List.getD_cons_succ, List.getD_cons_zero, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exfalso
    rw [eta_zero] at hcz
    apply zJ_ne_one
    apply α.injective
    rw [hcz, map_one]
  · exact hcz

section Generic

variable {G : Type*} [Group G]

theorem map_eq_of_forall_iff {α : MulAut G} {K : Subgroup G} (h : ∀ x, α x ∈ K ↔ x ∈ K) :
    K.map α.toMonoidHom = K := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (h y).2 hy
  · intro hx
    exact ⟨α.symm x, (h _).1 (by simpa using hx), by simp⟩

theorem forall_iff_of_map_eq {α : MulAut G} {K : Subgroup G} (h : K.map α.toMonoidHom = K)
    (x : G) : α x ∈ K ↔ x ∈ K := by
  constructor
  · intro hx
    have : α x ∈ K.map α.toMonoidHom := by rw [h]; exact hx
    obtain ⟨y, hy, hyx⟩ := this
    have : y = x := α.injective hyx
    rw [← this]
    exact hy
  · intro hx
    have : α x ∈ K.map α.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [h] at this

end Generic

theorem Hj_forall_iff
    (α : MulAut J) (hα : ∀ x, α x ∈ P0 ↔ x ∈ P0) (x : J) :
    α x ∈ Hj ↔ x ∈ Hj :=
  Hj_of_Eg j4Facts α (eta_char j4Facts.mat j4Facts α hα) x

theorem centralizer_forall_iff
    (α : MulAut J) (hα : ∀ x, α x ∈ P0 ↔ x ∈ P0) (x : J) :
    α x ∈ Subgroup.centralizer ({zJ} : Set J) ↔ x ∈ Subgroup.centralizer ({zJ} : Set J) := by
  have hz := aut_fix_zJ α hα
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    apply α.injective
    rw [map_mul, map_mul, hz]
    exact h
  · intro h
    have := congrArg α h
    rw [map_mul, map_mul, hz] at this
    exact this

theorem centralizer_ne_top
    : Subgroup.centralizer ({zJ} : Set J) ≠ ⊤ := by
  intro h
  have hcen : zJ ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro g
    have : g ∈ Subgroup.centralizer ({zJ} : Set J) := by rw [h]; exact Subgroup.mem_top g
    exact (Subgroup.mem_centralizer_iff.1 this zJ rfl).symm
  have hle : Subgroup.zpowers zJ ≤ Subgroup.center J := Subgroup.zpowers_le.2 hcen
  have : (Subgroup.zpowers zJ).Normal := Subgroup.normal_of_le_center hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : orderOf zJ = 2 := orderOf_eq_prime (by rw [sq]; exact zJ_sq) zJ_ne_one
  have := isSimpleGroup_J j4Facts
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers zJ) with h1 | h1
  · apply zJ_ne_one
    have : zJ ∈ Subgroup.zpowers zJ := Subgroup.mem_zpowers zJ
    rw [h1, Subgroup.mem_bot] at this
    exact this
  · have hc : Nat.card (Subgroup.zpowers zJ) = Nat.card J := by rw [h1, Subgroup.card_top]
    rw [Nat.card_zpowers, hord, card_J j4Facts] at hc
    omega

theorem localPair_J4_of
    (hgen : ∃ g : J, g * zJ = zJ * g ∧ g ∉ Hj)
    (hC : GoodLocal (Subgroup.centralizer ({zJ} : Set J))) : LocalPair J := by
  have hM := j4Facts.mat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Sylow 2 J := Sylow.ofCard P0 (by rw [card_P0 hM j4Facts, card_J_factorization j4Facts])
  have hP : (P : Subgroup J) = P0 := Sylow.coe_ofCard _ _
  have hcoat := isCoatom_Hj j4Facts
  refine ⟨P0, Hj, Subgroup.centralizer {zJ}, ?_, ?_,
    fun α hα => map_eq_of_forall_iff (Hj_forall_iff α (forall_iff_of_map_eq hα)),
    fun α hα => map_eq_of_forall_iff (centralizer_forall_iff α (forall_iff_of_map_eq hα)),
    hcoat.ne_top, centralizer_ne_top, ?_, goodLocal_Hj, hC⟩
  · rw [← hP]
    exact P.isPGroup'
  · rw [← hP]
    exact P.not_dvd_index
  · obtain ⟨g, hgz, hgH⟩ := hgen
    have hlt : Hj < Hj ⊔ Subgroup.centralizer {zJ} := by
      refine lt_of_le_of_ne le_sup_left fun h => hgH ?_
      have hgC : g ∈ Subgroup.centralizer ({zJ} : Set J) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact hgz.symm
      rw [h]
      exact (le_sup_right : Subgroup.centralizer ({zJ} : Set J) ≤ Hj ⊔ _) hgC
    exact hcoat.lt_iff.1 hlt

end CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
