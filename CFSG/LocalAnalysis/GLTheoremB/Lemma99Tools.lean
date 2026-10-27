module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Proof

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Generic

variable {Q : Type*} [Group Q]

theorem commutator_le_iSup_conj (S Y : Subgroup Q) : ⁅S, Y⁆ ≤ ⨆ y ∈ Y, GLBConj y S := by
  have hconj : ∀ y ∈ Y, GLBConj y S ≤ ⨆ y ∈ Y, GLBConj y S := fun y hy =>
    le_iSup₂_of_le y hy le_rfl
  refine Subgroup.commutator_le.2 fun s hs y hy => ?_
  have h1 : s ∈ ⨆ y ∈ Y, GLBConj y S := hconj 1 Y.one_mem (by rw [gLBConj_one]; exact hs)
  have h2 : y * s⁻¹ * y⁻¹ ∈ ⨆ y ∈ Y, GLBConj y S := by
    refine hconj y⁻¹ (Y.inv_mem hy) ?_
    rw [mem_gLBConj]
    simpa [mul_assoc] using S.inv_mem hs
  rw [commutatorElement_def]
  have : s * y * s⁻¹ * y⁻¹ = s * (y * s⁻¹ * y⁻¹) := by group
  rw [this]
  exact Subgroup.mul_mem _ h1 h2

theorem mem_normalizer_biSup {ι : Type*} {s : Set ι} {F : ι → Subgroup Q} {g : Q}
    (h : ∀ i ∈ s, g ∈ Subgroup.normalizer (F i : Set Q)) :
    g ∈ Subgroup.normalizer ((⨆ i ∈ s, F i : Subgroup Q) : Set Q) := by
  rw [mem_normalizer_iff_gLBConj_eq]
  simp only [GLBConj, Subgroup.map_iSup]
  refine iSup_congr fun i => iSup_congr fun hi => ?_
  exact mem_normalizer_iff_gLBConj_eq.1 (h i hi)

theorem commutator_le_of_le_sup_centralizes {X A B' Y : Subgroup Q}
    (hXA : X ≤ Subgroup.normalizer (A : Set Q)) (hAB : A ≤ Subgroup.centralizer (B' : Set Q))
    (hXB : X ≤ Subgroup.centralizer (B' : Set Q)) (hY : Y ≤ A ⊔ B') : ⁅X, Y⁆ ≤ A := by
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup hAB (hY hy)
  have hxb : x * b * x⁻¹ = b := by
    have := (Subgroup.mem_centralizer_iff.1 (hXB hx)) b hb
    calc x * b * x⁻¹ = b * x * x⁻¹ := by rw [this]
      _ = b := by group
  have hxa : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hXA hx) a).1 ha
  rw [commutatorElement_def]
  have e : x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹) * a⁻¹ := by
    calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = (x * a * x⁻¹) * a⁻¹ := by rw [hxb]; group
  rw [e]
  exact A.mul_mem hxa (A.inv_mem ha)

end Generic

section Balanced

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem barX_le_centralizer_of_balanced (i11 : Input11_6) (l23 : Lemma23)
    (hSt : GLStanding G m p) {B : Subgroup G} (hB : IsBOneMax p B) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) {S L : Subgroup G} (hSC : S ≤ Subgroup.centralizer ({b} : Set G))
    (hS2 : IsPGroup 2 S) (hBS : B ≤ Subgroup.normalizer (S : Set G))
    (hL : GLAPComponent p (Subgroup.centralizer ({b} : Set G)) L)
    (hbal : IsStronglyLocallyOneBalanced p B b L) :
    barX p (Subgroup.centralizer ({b} : Set G)) S ≤
      Subgroup.centralizer ((barX p (Subgroup.centralizer ({b} : Set G)) L :
        Subgroup (↥(Subgroup.centralizer ({b} : Set G)) ⧸
          GLAPPrimeCore p ↥(Subgroup.centralizer ({b} : Set G)))) : Set _) := by
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({b} : Set G) with hC
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hSt hb1
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (l23 G m p hSt B hB) hBC
  have hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C) := by
    refine (glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
    rw [hSt.rank_eq]
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'.2.1 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hSt.card_eq hB]
  have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_input11_6 i11 hSt.kProper hp hp2 hCtop hBC hSC (l23 G m p hSt B hB)
      hrank hS2 hBS hL
  have hcomm : ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L :=
    hbal S (le_inf hSL hSC) (coprime_card_of_isPGroup_two hp hp2 hS2) (fun g hg => hBS hg.1)
  refine barX_le_centralizer fun s hs t ht _ _ => ?_
  have h3 : s * t * s⁻¹ * t⁻¹ ∈ ⁅S, L⁆ := Subgroup.commutator_mem_commutator hs ht
  rw [Subgroup.commutator_comm] at h3
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hcomm h3)

end Balanced

section Quasisimple

open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem normal_le_center_or_eq_top' (hQ : CFSG.Open.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  obtain ⟨hperf, hsimple⟩ := hQ
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hNorm : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro x hx
    have hmem : π x ∈ N.map π := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    simpa [π] using hmem
  · right
    have hNZ : ∀ x : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, x = n * z := by
      intro x
      have hx : π x ∈ N.map π := by rw [h]; exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hx
      refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
      have : π (n⁻¹ * x) = 1 := by rw [map_mul, map_inv, hnx, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp this
    have hcomm : ∀ a b : Q ⧸ N, a * b = b * a := by
      intro a b
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N a
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N b
      obtain ⟨n, hn, z, hz, rfl⟩ := hNZ x
      obtain ⟨m, hm, w, hw, rfl⟩ := hNZ y
      have hn1 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
      simp only [map_mul, hn1, hm1, one_mul]
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz w]
    have : Group.IsPerfect Q := ⟨hperf⟩
    have : IsMulCommutative (Q ⧸ N) := ⟨⟨hcomm⟩⟩
    have : Subsingleton (Q ⧸ N) := Group.IsPerfect.subsingleton_of_isMulCommutative
    rw [eq_top_iff]
    intro x _
    have : (QuotientGroup.mk' N x) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff x).mp this

theorem normal_subgroupOf_commutator {X K : Subgroup Q}
    (hXK : X ≤ Subgroup.normalizer (K : Set Q)) : (⁅X, K⁆.subgroupOf K).Normal := by
  have hJK : ⁅X, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx k hk => by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXK hx) k).1 hk) (K.inv_mem hk)
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hJK).2 fun a ha => ?_
  have key : ∀ a ∈ K, ∀ y ∈ ⁅X, K⁆, a * y * a⁻¹ ∈ ⁅X, K⁆ := by
    intro a ha
    have : ⁅X, K⁆ ≤ (⁅X, K⁆).comap (MulAut.conj a).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun x hx b hb => ?_
      show a * ⁅x, b⁆ * a⁻¹ ∈ ⁅X, K⁆
      have e : a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆⁻¹ * ⁅x, a * b⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (⁅X, K⁆).mul_mem ((⁅X, K⁆).inv_mem (Subgroup.commutator_mem_commutator hx ha))
        (Subgroup.commutator_mem_commutator hx (K.mul_mem ha hb))
    exact fun y hy => this hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key a ha y
  · intro h
    have := key a⁻¹ (K.inv_mem ha) _ h
    have e : a⁻¹ * (a * y * a⁻¹) * a⁻¹⁻¹ = y := by group
    rwa [e] at this

theorem commutator_eq_of_isQuasisimple {X K : Subgroup Q} (hK : CFSG.Open.IsQuasisimple ↥K)
    (hXK : X ≤ Subgroup.normalizer (K : Set Q))
    (hnc : ¬ X ≤ Subgroup.centralizer (K : Set Q)) : ⁅X, K⁆ = K := by
  have hJK : ⁅X, K⁆ ≤ K := Subgroup.commutator_le.2 fun x hx k hk => by
    rw [commutatorElement_def]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXK hx) k).1 hk) (K.inv_mem hk)
  have hn := normal_subgroupOf_commutator hXK
  rcases normal_le_center_or_eq_top' hK (⁅X, K⁆.subgroupOf K) with hc | htop
  · exfalso
    apply hnc
    have hJcent : ⁅X, K⁆ ≤ Subgroup.centralizer (K : Set Q) := by
      intro j hj k hk
      have hjK : j ∈ K := hJK hj
      have := Subgroup.mem_center_iff.1
        (hc (show (⟨j, hjK⟩ : ↥K) ∈ ⁅X, K⁆.subgroupOf K from (Subgroup.mem_subgroupOf).2 hj))
        ⟨k, hk⟩
      exact congrArg Subtype.val this
    have h1 : ⁅⁅X, K⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hJcent
    have h2 : ⁅⁅K, X⁆, K⁆ = ⊥ := by rwa [Subgroup.commutator_comm K X]
    have h3 : ⁅⁅K, K⁆, X⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h2 h1
    have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.1 ⟨hK.1⟩
    rw [hperf] at h3
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (by rwa [Subgroup.commutator_comm])
  · exact le_antisymm hJK (by
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ ⁅X, K⁆.subgroupOf K := htop ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf).1 this)

end Quasisimple

end CFSG.LocalAnalysis.GLTheoremB
