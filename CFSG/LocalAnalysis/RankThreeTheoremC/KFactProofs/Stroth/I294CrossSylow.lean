module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Card
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Bridge
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294Out
public import CFSG.LocalAnalysis.RankThreeTheoremC.NormalPlane

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3

open CFSG CFSG.Open Subgroup

section Basic

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y}
  {D : Subgroup Y}

theorem I294Cross.le_normalizer_inf_normal {Y : Type*} [Group Y] (Q L : Subgroup Y) [L.Normal] :
    Q ≤ normalizer ((Q ⊓ L : Subgroup Y) : Set Y) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · rintro ⟨hnQ, hnL⟩
    exact ⟨Q.mul_mem (Q.mul_mem hy hnQ) (Q.inv_mem hy),
      (inferInstance : L.Normal).conj_mem n hnL y⟩
  · rintro ⟨hnQ, hnL⟩
    refine ⟨?_, ?_⟩
    · have := Q.mul_mem (Q.mul_mem (Q.inv_mem hy) hnQ) hy
      simpa [mul_assoc] using this
    · have := (inferInstance : L.Normal).conj_mem _ hnL y⁻¹
      simpa [mul_assoc] using this

theorem I294Cfg.isPGroup_plane (h : I294Cfg p L z g D) : IsPGroup p D := by
  haveI := Fact.mk h.prime
  exact IsPGroup.of_card (n := 2) h.card

theorem I294Cfg.exists_sylow_ge (h : I294Cfg p L z g D) :
    ∃ P : Sylow p Y, D ≤ (P : Subgroup Y) := by
  haveI := Fact.mk h.prime
  exact h.isPGroup_plane.exists_le_sylow

theorem I294Cfg.pRank_sylow_eq (h : I294Cfg p L z g D) (P : Sylow p Y) :
    CFSG.Open.pRank p (P : Subgroup Y) = 3 := by
  haveI := Fact.mk h.prime
  exact (CFSG.SectionRank.pRank_sylow P).1.trans h.rank

theorem I294Cfg.inf_centralizer_line (h : I294Cfg p L z g D) {P : Subgroup Y} (hP : IsPGroup p P)
    (hDP : D ≤ P) {x : Y} (hx : x ∈ D)
    (hS : CFSG.ABGLocalTools.IsSylowOf p D (centralizer ({x} : Set Y))) :
    P ⊓ centralizer ({x} : Set Y) = D := by
  haveI := Fact.mk h.prime
  have hDC : D ≤ centralizer ({x} : Set Y) := fun d hd =>
    Subgroup.mem_centralizer_singleton_iff.2 (h.elem.comm hd hx)
  exact hS.eq_of_le (le_inf hDP hDC) inf_le_right hP.to_inf_left

theorem I294Cfg.inf_centralizer_self (h : I294Cfg p L z g D) {P : Subgroup Y} (hP : IsPGroup p P)
    (hDP : D ≤ P) : P ⊓ centralizer (D : Set Y) = D := by
  haveI := Fact.mk h.prime
  have hDC : D ≤ centralizer (D : Set Y) := fun d hd =>
    Subgroup.mem_centralizer_iff.2 fun e he => h.elem.comm he hd
  exact h.sylow.eq_of_le (le_inf hDP hDC) inf_le_right hP.to_inf_left

theorem I294Cfg.not_le_normalizer (h : I294Cfg p L z g D) {P : Sylow p Y}
    (hDP : D ≤ (P : Subgroup Y)) : ¬ (P : Subgroup Y) ≤ normalizer (D : Set Y) := by
  intro hN
  haveI := Fact.mk h.prime
  have h3 := three_le_pRank_sup_centralizer_of_normal_elemAbelian h.prime
    (h.pRank_sylow_eq P).ge hN h.elem h.card
  rw [h.inf_centralizer_self P.isPGroup' hDP, sup_idem] at h3
  have h2 : CFSG.Open.pRank p D ≤ 2 := by
    refine CFSG.SectionRank.pRank_le h.prime.one_lt fun E hED _ => ?_
    rw [← h.card]
    exact Subgroup.card_le_of_le hED
  omega

end Basic

section Normal

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y}
  {D : Subgroup Y}

theorem I294Cfg.not_isMulCommutative_inf (h : I294Cfg p L z g D) (hDL : D ≤ L) {P : Sylow p Y}
    (hDP : D ≤ (P : Subgroup Y)) : ¬ IsMulCommutative ↥((P : Subgroup Y) ⊓ L) := by
  intro hc
  obtain ⟨x, hxD, hx1, hxS⟩ := h.sylowLine
  have hxS' : x ∈ (P : Subgroup Y) ⊓ L := ⟨hDP hxD, hDL hxD⟩
  have hle : (P : Subgroup Y) ⊓ L ≤ centralizer ({x} : Set Y) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg Subtype.val (hc.is_comm.comm ⟨y, hy⟩ ⟨x, hxS'⟩)
    exact this
  have h1 : (P : Subgroup Y) ⊓ L ≤ D := by
    rw [← h.inf_centralizer_line P.isPGroup' hDP hxD hxS]
    exact le_inf inf_le_left hle
  have h2 : (P : Subgroup Y) ⊓ L = D := le_antisymm h1 (le_inf hDP hDL)
  refine h.not_le_normalizer hDP ?_
  rw [← h2]
  exact I294Cross.le_normalizer_inf_normal (P : Subgroup Y) L

theorem I294Cfg.pRank_normal_le_three (h : I294Cfg p L z g D) :
    CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 3 := by
  have := CFSG.SectionRank.pRank_top_le_of_injective h.prime.one_lt L.subtype L.subtype_injective
  exact this.trans h.rank.le

theorem I294Cfg.three_le_pRank_of_sylow_le (h : I294Cfg p L z g D) {P : Sylow p Y}
    (hPL : (P : Subgroup Y) ≤ L) : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥L) := by
  haveI := Fact.mk h.prime
  obtain ⟨E, hEP, hE, hEc⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p h.prime
    (P : Subgroup Y)
  rw [h.pRank_sylow_eq P] at hEc
  have hEL : E ≤ L := hEP.trans hPL
  have hE' : IsElemAbelian p (E.subgroupOf L) := hE.subgroupOf L
  have hc' : Nat.card (E.subgroupOf L) = p ^ 3 := by
    rw [← hEc]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  exact CFSG.SectionRank.le_pRank h.prime.one_lt le_top hE' hc'

theorem I294Cfg.false_of_sylow_le (h : I294Cfg p L z g D) {P : Sylow p Y}
    (hPL : (P : Subgroup Y) ≤ L) (hr : CFSG.Open.pRank p (⊤ : Subgroup ↥L) ≤ 2) : False := by
  have := h.three_le_pRank_of_sylow_le hPL
  omega

theorem I294Cfg.le_of_pAut_inner (h : I294Cfg p L z g D)
    (hI : ∀ α : MulAut ↥L, (∃ k : ℕ, α ^ p ^ k = 1) →
      α ∈ (MulAut.conj : ↥L →* MulAut ↥L).range)
    {P : Subgroup Y} (hP : IsPGroup p P) : P ≤ L := by
  intro y hy
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hk' : y ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have hα : (MulAut.conjNormal (H := L) y) ^ p ^ k = 1 := by
    rw [← map_pow, hk', map_one]
  obtain ⟨l, hl⟩ := hI _ ⟨k, hα⟩
  have h2 : MulAut.conjNormal (H := L) (l : Y) = MulAut.conjNormal (H := L) y := by
    rw [MulAut.conjNormal_val]
    exact hl
  have h3 : (l : Y) = y := i294_conjNormal_injective h.cent h2
  rw [← h3]
  exact l.2

end Normal

section Three

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y} {D : Subgroup Y}

theorem I294Cfg.le_of_dvd_eightyOne' (h : I294Cfg 3 L z g D) {P : Sylow 3 Y}
    (hDP : D ≤ (P : Subgroup Y)) (hL : 81 ∣ Nat.card L) : (P : Subgroup Y) ≤ L := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP81 : Nat.card P = 81 := h.card_sylow_eq_eightyOne P hDP
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup Y) (⊤ : Subgroup Y) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup Y) ⊓ L) L :=
    hPtop.inf_of_le_normalizer le_top (by
      intro y _
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn; exact (inferInstance : L.Normal).conj_mem n hn y
      · intro hn
        have := (inferInstance : L.Normal).conj_mem _ hn y⁻¹
        simpa [mul_assoc] using this)
  have hcard := hS.card_eq
  have h4 : 4 ≤ (Nat.card L).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (by simpa using hL)
  have h81 : 81 ≤ Nat.card ((P : Subgroup Y) ⊓ L : Subgroup Y) := by
    rw [hcard]
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (Nat.card L).factorization 3 := Nat.pow_le_pow_right (by norm_num) h4
  have heq : (P : Subgroup Y) ⊓ L = (P : Subgroup Y) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hP81]; exact h81)
  rw [← heq]
  exact inf_le_right

theorem I294Cfg.not_dvd_pow_five (h : I294Cfg 3 L z g D) : ¬ 3 ^ 5 ∣ Nat.card L := by
  intro h5
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hDP⟩ := h.exists_sylow_ge
  have hP81 : Nat.card P = 81 := h.card_sylow_eq_eightyOne P hDP
  have hPtop : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup Y) (⊤ : Subgroup Y) := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, P.isPGroup', ?_⟩
    rw [Subgroup.relIndex_top_right]
    exact P.not_dvd_index
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 ((P : Subgroup Y) ⊓ L) L :=
    hPtop.inf_of_le_normalizer le_top (by
      intro y _
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn; exact (inferInstance : L.Normal).conj_mem n hn y
      · intro hn
        have := (inferInstance : L.Normal).conj_mem _ hn y⁻¹
        simpa [mul_assoc] using this)
  have hcard := hS.card_eq
  have h5' : 5 ≤ (Nat.card L).factorization 3 :=
    (Nat.prime_three.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 h5
  have hle : Nat.card ((P : Subgroup Y) ⊓ L : Subgroup Y) ≤ Nat.card P :=
    Subgroup.card_le_of_le inf_le_left
  rw [hcard, hP81] at hle
  have : 3 ^ 5 ≤ 3 ^ (Nat.card L).factorization 3 := Nat.pow_le_pow_right (by norm_num) h5'
  omega

end Three

section Elem

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} [L.Normal] {z g : Y}
  {D : Subgroup Y}

theorem I294Cross.pRank_centralizer_le (hp : 1 < p) (x : ↥L) :
    CFSG.Open.pRank p (centralizer ({x} : Set ↥L)) ≤
      CFSG.Open.pRank p (centralizer ({(x : Y)} : Set Y)) := by
  refine (CFSG.SectionRank.pRank_le_map hp L.subtype L.subtype_injective _).trans
    (CFSG.SectionRank.pRank_mono hp ?_)
  rintro _ ⟨y, hy, rfl⟩
  have hy' : y ∈ centralizer ({x} : Set ↥L) := hy
  rw [Subgroup.mem_centralizer_singleton_iff] at hy' ⊢
  exact congrArg Subtype.val hy'

theorem I294Cfg.false_of_three_le_pRank_centralizer (h : I294Cfg p L z g D) (hDL : D ≤ L)
    (H : ∀ x : ↥L, orderOf x = p → 3 ≤ CFSG.Open.pRank p (centralizer ({x} : Set ↥L))) :
    False := by
  haveI := Fact.mk h.prime
  obtain ⟨x, hxD, hx1, hxS⟩ := h.sylowLine
  have hxo : orderOf (⟨x, hDL hxD⟩ : ↥L) = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime (h.elem.2 x hxD) hx1
  have h3 := H _ hxo
  have h4 := I294Cross.pRank_centralizer_le (Y := Y) (L := L) h.prime.one_lt ⟨x, hDL hxD⟩
  have h2 := pRank_centralizer_le_two_of_isSylowOf h.prime h.card hxS
  simp only at h4
  omega

end Elem

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3
