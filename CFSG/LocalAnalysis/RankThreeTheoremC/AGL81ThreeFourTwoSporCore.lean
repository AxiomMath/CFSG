module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoDefs
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoInf
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ThreeFourTwoTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped Pointwise

section PElements

variable {G : Type*} [Group G]

private theorem mem_of_pow_eq_one_of_le_sup {p : ℕ} {R T₀ : Subgroup G}
    (hRT : R ≤ T₀ ⊔ (R ⊓ centralizer (T₀ : Set G))) (hexp : ∀ t ∈ T₀, t ^ p = 1)
    (hw : ∀ w ∈ R ⊓ centralizer (T₀ : Set G), w ^ p = 1 → w ∈ T₀) {x : G} (hxR : x ∈ R)
    (hxp : x ^ p = 1) : x ∈ T₀ := by
  have hle : R ⊓ centralizer (T₀ : Set G) ≤ normalizer (T₀ : Set G) :=
    inf_le_right.trans (centralizer_le_normalizer _)
  have hx : x ∈ (T₀ : Set G) * ((R ⊓ centralizer (T₀ : Set G) : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left T₀ _ hle]
    exact hRT hxR
  obtain ⟨t, ht, c, hc, rfl⟩ := Set.mem_mul.mp hx
  have hcomm : Commute t c := mem_centralizer_iff.mp (mem_inf.mp hc).2 t ht
  have hcp : c ^ p = 1 := by
    have h1 := hcomm.mul_pow p
    rw [hxp, hexp t ht, one_mul] at h1
    exact h1.symm
  exact T₀.mul_mem ht (hw c hc hcp)

private theorem pRank_le_two_of_card_cube [Finite G] {p : ℕ} (hp : p.Prime) {T : Subgroup G}
    (hT : Nat.card T = p ^ 3) (hnab : ∃ x ∈ T, ∃ y ∈ T, x * y ≠ y * x) :
    CFSG.Open.pRank p T ≤ 2 := by
  obtain ⟨A, hAT, hA, hAc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt T
  by_contra h
  have hle : p ^ CFSG.Open.pRank p T ≤ p ^ 3 := by
    rw [← hAc, ← hT]
    exact Subgroup.card_le_of_le hAT
  have h3 : CFSG.Open.pRank p T = 3 := by
    have := (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
    omega
  have hAT' : A = T := Subgroup.eq_of_le_of_card_ge hAT (by rw [hT, hAc, h3])
  obtain ⟨x, hx, y, hy, hxy⟩ := hnab
  rw [← hAT'] at hx hy
  exact hxy (congrArg Subtype.val (hA.1.is_comm.comm (⟨x, hx⟩ : A) ⟨y, hy⟩))

end PElements

theorem threeFourTwoNoneAt_of_glbCore_eq_top {p : ℕ} {X : Type*} [Group X]
    (hX : IsSimpleGroup X) (hnab : ∃ a b : X, a * b ≠ b * a) (hout : Group.IsSolvable (Outer X))
    (hT : ∀ (K : Type) [Group K] [Finite K], Nonempty (K ≃* X) →
      ¬ p ∣ Nat.card (Outer K) ∧ ∀ T : Sylow p K, Nat.card (T : Subgroup K) = p ^ 3 ∧
        (∀ x ∈ (T : Subgroup K), x ^ p = 1) ∧
        (∃ x ∈ (T : Subgroup K), ∃ y ∈ (T : Subgroup K), x * y ≠ y * x) ∧
        GLBCore p 2 (T : Subgroup K) = ⊤ ∧
        ∀ A : Subgroup K, A ≤ T → IsElemAbelian p A → Nat.card A = p ^ 2 →
          GLBCore p 1 A = ⊤) :
    ThreeFourTwoNoneAt p X := by
  refine threeFourTwoNoneAt_of_inf hX hnab hout ?_
  intro Y _ _ K Y₀ E R hp _ hKn hKX _ _ _ hER hE hEc hcore _ hKY₀
  exfalso
  refine hKY₀ ?_
  haveI : Fact p.Prime := ⟨hp⟩
  haveI := hKn
  obtain ⟨hpK, hTK⟩ := hT K hKX
  obtain ⟨e⟩ := hKX
  have hZK : K ⊓ centralizer (K : Set Y) = ⊥ := by
    haveI : IsSimpleGroup K := MulEquiv.isSimpleGroup e
    obtain ⟨a, b, hab⟩ := hnab
    have hZ := CFSG.ComponentClassification.Helpers.center_eq_bot K
      ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
    rw [eq_bot_iff]
    rintro z ⟨hzK, hzC⟩
    have h : (⟨z, hzK⟩ : K) ∈ center K :=
      mem_center_iff.mpr fun g => Subtype.ext (mem_centralizer_iff.mp hzC g g.2)
    rw [hZ, mem_bot] at h
    exact mem_bot.mpr (congrArg Subtype.val h)
  obtain ⟨T, hT₀⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  obtain ⟨hTc, hTexp, hTnab, hcore2, hcore1⟩ := hTK T
  set T₀ : Subgroup Y := (R : Subgroup Y) ⊓ K with hT₀def
  have hT₀exp : ∀ t ∈ T₀, t ^ p = 1 := by
    rw [← hT₀]
    rintro _ ⟨t, ht, rfl⟩
    simpa using congrArg K.subtype (hTexp t ht)
  have hT₀c : Nat.card T₀ = p ^ 3 := by
    rw [← hT₀, card_map_of_injective K.subtype_injective, hTc]
  have hT₀nab : ∃ x ∈ T₀, ∃ y ∈ T₀, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hTnab
    refine ⟨x, hT₀ ▸ mem_map_of_mem K.subtype hx, y, hT₀ ▸ mem_map_of_mem K.subtype hy,
      fun h => hxy (Subtype.ext h)⟩
  have hT₀rk : CFSG.Open.pRank p T₀ ≤ 2 := pRank_le_two_of_card_cube hp hT₀c hT₀nab
  have hRT := sylow_le_sup_inf_centralizer_of_not_dvd R hZK hpK
  have hK : ∀ (k : ℕ) (P : Subgroup K), GLBCore p k P = ⊤ →
      (∀ Q : Subgroup K, Q ≤ P → k ≤ CFSG.Open.pRank p Q →
        normalizer ((Q.map K.subtype : Subgroup Y) : Set Y) ≤ Y₀) → K ≤ Y₀ := by
    intro k P hP hQ y hy
    have hle : GLBCore p k P ≤ Y₀.subgroupOf K := by
      refine sSup_le ?_
      rintro _ ⟨Q, hQP, hQk, rfl⟩ x hx
      exact mem_subgroupOf.mpr
        (hQ Q hQP hQk (le_normalizer_map K.subtype (mem_map_of_mem K.subtype hx)))
    exact mem_subgroupOf.mp (hle (hP ▸ mem_top (⟨y, hy⟩ : K)))
  by_cases hw : ∃ w ∈ (R : Subgroup Y) ⊓ centralizer (T₀ : Set Y), w ^ p = 1 ∧ w ∉ T₀
  ·
    obtain ⟨w, hwRC, hwp, hwT⟩ := hw
    refine hK 2 T hcore2 fun Q hQT hQ2 => ?_
    set Q' : Subgroup Y := Q.map K.subtype with hQ'def
    have hQ'T : Q' ≤ T₀ := by
      rw [← hT₀]
      exact map_mono hQT
    have hQ'2 : 2 ≤ CFSG.Open.pRank p Q' :=
      hQ2.trans (CFSG.SectionRank.pRank_le_map hp.one_lt K.subtype K.subtype_injective Q)
    have hQ'rk : CFSG.Open.pRank p Q' = 2 :=
      le_antisymm ((CFSG.SectionRank.pRank_mono hp.one_lt hQ'T).trans hT₀rk) hQ'2
    obtain ⟨B, hBQ, hB, hBc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt Q'
    rw [hQ'rk] at hBc
    have hwC : w ∈ (R : Subgroup Y) ⊓ centralizer (Q' : Set Y) :=
      ⟨(mem_inf.mp hwRC).1, centralizer_le (hQ'T : (Q' : Set Y) ⊆ T₀) (mem_inf.mp hwRC).2⟩
    have h3 : 3 ≤ CFSG.Open.pRank p (Q' ⊔ ((R : Subgroup Y) ⊓ centralizer (Q' : Set Y))) :=
      CFSG.AGLEmbedding.succ_le_pRank_of_isElemAbelian_of_mem_centralizer hp hB hBc hwp
        (fun h => hwT (hQ'T (hBQ h)))
        (centralizer_le ((hBQ.trans hQ'T) : (B : Set Y) ⊆ T₀) (mem_inf.mp hwRC).2)
        (hBQ.trans le_sup_left) (mem_sup_right hwC)
    have hQ'R : Q' ≤ R := hQ'T.trans inf_le_left
    have hR3 : 3 ≤ pRank p (R : Subgroup Y) := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      exact h3.trans (CFSG.SectionRank.pRank_mono hp.one_lt (sup_le hQ'R inf_le_left))
    rw [if_pos hR3] at hcore
    exact (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hQ'R hQ'2 h3).trans hcore
  ·
    push_neg at hw
    have hmem : ∀ x ∈ (R : Subgroup Y), x ^ p = 1 → x ∈ T₀ := fun x hx hxp =>
      mem_of_pow_eq_one_of_le_sup hRT hT₀exp hw hx hxp
    have hR2 : ¬ 3 ≤ pRank p (R : Subgroup Y) := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
      intro h3
      obtain ⟨A, hAR, hA, hAc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (R : Subgroup Y)
      have hAT : A ≤ T₀ := fun a ha => hmem a (hAR ha) (hA.2 a ha)
      have := CFSG.SectionRank.le_pRank hp.one_lt hAT hA hAc
      omega
    rw [if_neg hR2] at hcore
    have hET : E ≤ T₀ := fun x hx => hmem x (hER hx) (hE.2 x hx)
    set E' : Subgroup K := E.subgroupOf K with hE'def
    have hE'map : E'.map K.subtype = E := by
      rw [hE'def, subgroupOf_map_subtype]
      exact inf_eq_left.mpr (hET.trans inf_le_right)
    have hE'T : E' ≤ T := fun x hx => by
      have h1 : (x : Y) ∈ T₀ := hET (mem_subgroupOf.mp hx)
      rw [← hT₀] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      rwa [show y = x from Subtype.ext hyx] at hy
    have hEK : E ≤ K := hET.trans inf_le_right
    have hE'el : IsElemAbelian p E' := by
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · have h := congrArg Subtype.val (hE.1.is_comm.comm
          (⟨((a : K) : Y), mem_subgroupOf.mp a.2⟩ : E) ⟨((b : K) : Y), mem_subgroupOf.mp b.2⟩)
        simpa using h
      · simpa using hE.2 _ (mem_subgroupOf.mp hx)
    have hE'c : Nat.card E' = p ^ 2 := by
      rw [hE'def, Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv, hEc]
    refine hK 1 E' (hcore1 E' hE'T hE'el hE'c) fun Q hQE' hQ1 => ?_
    have hQE : Q.map K.subtype ≤ E := hE'map ▸ map_mono hQE'
    have hQr : 1 ≤ CFSG.Open.pRank p (Q.map K.subtype) :=
      hQ1.trans (CFSG.SectionRank.pRank_le_map hp.one_lt K.subtype K.subtype_injective Q)
    exact (le_sSup ⟨Q.map K.subtype, hQE, hQr, rfl⟩ :
      normalizer ((Q.map K.subtype : Subgroup Y) : Set Y) ≤ GLBCore p 1 E).trans hcore

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
