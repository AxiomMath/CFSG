module

public import CFSG.GH74.GLS.Balance.Bender.L55Red
public import CFSG.GH74.GLS.Balance.Bender.L55Local
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.GH74.GLS.Balance.Bender.L55Aux

public section

namespace CFSG.GH74.GLS.Balance

open Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

theorem l55_case_coprime {p : ℕ} [Fact p.Prime] (h52ii : BenderL52ii p) (hq43 : BenderQ43iii p)
    {m : ℕ} (ih : l55_Claim p m) {G : Type} [Group G] [Finite G] {X P N : Subgroup G}
    [X.Normal] [N.Normal] (hcard : Nat.card X ≤ m + 1) (hXp : IsPStar p ↥X) (hP : IsPGroup p ↥P)
    (hNX : N ≤ X) (hN1 : N ≠ ⊥) (hcop : Nat.Coprime p (Nat.card N)) :
    X ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) := by
  set π := QuotientGroup.mk' N with hπ
  have hXn' : (X.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hbar := ih (G ⧸ N) (X.map π) (P.map π)
    (Nat.lt_succ_iff.mp (lt_of_lt_of_le (l55_card_map_lt hNX hN1) hcard))
    (l55_isPStar_map h52ii π X hXp) (hP.map π) (l55_le_normalizer_of_normal _ _)
  have hNR : N ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) := by
    have h := hq43 G N P hP (l55_le_normalizer_of_normal N P) hcop
    calc N = ⁅N, P⁆ ⊔ (N ⊓ centralizer (P : Set G)) := h
      _ ≤ _ := sup_le_sup (Subgroup.commutator_mono hNX le_rfl) (inf_le_inf_right _ hNX)
  refine l55_of_map_le hNR ?_
  refine hbar.trans ?_
  rw [Subgroup.map_sup, Subgroup.map_commutator]
  refine sup_le_sup_left ?_ _
  have : Fact (IsPGroup p ↥P) := ⟨hP⟩
  have hc : centralizer ((P.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N)) =
      (centralizer (P : Set G)).map π :=
    CFSG.centralizer_map_quotient_eq_map_centralizer p P N inferInstance hcop
  rintro y ⟨hyX, hyC⟩
  obtain ⟨x, hx, rfl⟩ := hyX
  have hyC' : π x ∈ (centralizer (P : Set G)).map π := by rw [← hc]; exact hyC
  obtain ⟨c, hcC, hcx⟩ := hyC'
  have hxc : x⁻¹ * c ∈ N := QuotientGroup.eq.mp hcx.symm
  have hcX : c ∈ X := by
    have := X.mul_mem hx (hNX hxc)
    simpa using this
  exact ⟨c, ⟨hcX, hcC⟩, hcx⟩

theorem l55_case_pgroup {p : ℕ} [Fact p.Prime] (h52ii : BenderL52ii p) (h52iv : BenderL52iv p)
    (hq42 : BenderQ42iii p) {m : ℕ} (ih : l55_Claim p m) {G : Type} [Group G] [Finite G]
    {X P N : Subgroup G} [X.Normal] [N.Normal] (hcard : Nat.card X ≤ m + 1) (hXp : IsPStar p ↥X)
    (hP : IsPGroup p ↥P) (hPX : P ≤ normalizer (X : Set G)) (hsup : X ⊔ P = ⊤) (hNX : N ≤ X)
    (hN1 : N ≠ ⊥) (hmin : ∀ M : Subgroup G, M ≤ N → M.Normal → M = ⊥ ∨ M = N)
    (hNp : IsPGroup p ↥N) : X ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) := by
  set π := QuotientGroup.mk' N with hπ
  have hcentral : N.subgroupOf X ≤ center ↥X :=
    h52iv ↥X hXp (N.subgroupOf X) inferInstance hNp.comap_subtype
  have hXc : ∀ n ∈ N, ∀ x ∈ X, n * x = x * n := by
    intro n hn x hx
    have := Subgroup.mem_center_iff.mp
      (hcentral (show (⟨n, hNX hn⟩ : ↥X) ∈ N.subgroupOf X from hn)) ⟨x, hx⟩
    exact (congrArg Subtype.val this).symm
  have hNP : N ≤ centralizer (P : Set G) := l55_central_of_pgroup hP hNp hN1 hmin hXc hsup
  have hXbar : IsPStar p ↥(X.map π) := l55_isPStar_map h52ii π X hXp
  have hXn' : (X.map π).Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hbar := ih (G ⧸ N) (X.map π) (P.map π)
    (Nat.lt_succ_iff.mp (lt_of_lt_of_le (l55_card_map_lt hNX hN1) hcard))
    hXbar (hP.map π) (l55_le_normalizer_of_normal _ _)
  have hbar' : X.map π ≤ ⁅X.map π, P.map π⁆ ⊔
      oResOf p (X.map π ⊓ centralizer ((P.map π : Subgroup (G ⧸ N)) : Set (G ⧸ N))) :=
    l55_aux hXbar.oResOf_eq
      (fun c hc => l55_mem_normalizer_commutator (Subgroup.le_normalizer hc.1) hc.2) hbar
  rw [hq42 G X P N hPX hP hNX hXc] at hbar'
  have hNR : N ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) :=
    le_sup_of_le_right (le_inf hNX hNP)
  refine l55_of_map_le hNR ?_
  refine hbar'.trans ?_
  rw [Subgroup.map_sup, Subgroup.map_commutator]
  exact sup_le_sup_left (Subgroup.map_mono (oResOf_le p _)) _

theorem l55_normal_inf_centralizer {G : Type*} [Group G] (N : Subgroup G) [N.Normal] :
    (N ⊓ centralizer (N : Set G)).Normal := by
  refine ⟨fun z hz g => ⟨Subgroup.Normal.conj_mem inferInstance z hz.1 g, ?_⟩⟩
  show g * z * g⁻¹ ∈ centralizer (N : Set G)
  rw [mem_centralizer_iff]
  intro n hn
  have hn' : g⁻¹ * n * g ∈ N := by
    simpa using Subgroup.Normal.conj_mem inferInstance n hn g⁻¹
  have h1 := mem_centralizer_iff.mp hz.2 _ hn'
  calc n * (g * z * g⁻¹) = g * ((g⁻¹ * n * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * n * g)) * g⁻¹ := by rw [h1]
    _ = g * z * g⁻¹ * n := by group

theorem l55_case_nonab {p : ℕ} [Fact p.Prime] (h54 : BenderL54 p) (hq326 : BenderQ326) {m : ℕ}
    (ih : l55_Claim p m) {G : Type} [Group G] [Finite G] {X P N : Subgroup G} [N.Normal]
    (hcard : Nat.card X ≤ m + 1) (hXp : IsPStar p ↥X) (hP : IsPGroup p ↥P)
    (hPX : P ≤ normalizer (X : Set G)) (hNX : N ≤ X) (hN1 : N ≠ ⊥)
    (hmin : ∀ M : Subgroup G, M ≤ N → M.Normal → M = ⊥ ∨ M = N) (hdvd : p ∣ Nat.card N)
    (hnab : ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a) :
    X ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) := by
  obtain ⟨Q, hQ, hPQ⟩ := l55_exists_invariant_sylow (N := N) hP
  have hQ1 : Q ≠ ⊥ := l55_sylow_ne_bot hQ hdvd
  set C : Subgroup G := X ⊓ centralizer (Q : Set G) with hC
  set X₀ : Subgroup G := oResOf p C with hX₀
  have hNnX : (N.subgroupOf X).Normal := inferInstance
  have hX₀p : IsPStar p ↥X₀ := h54 G X N Q hXp hNX hNnX hQ
  have hXN : X ≤ N ⊔ X₀ :=
    l55_aux hXp.oResOf_eq (l55_le_normalizer_of_normal N C)
      ((isPStar_iff.mp hXp).2 N Q hNX hNnX hQ)
  have hX₀P : P ≤ normalizer (X₀ : Set G) := by
    apply l55_le_normalizer_oResOf
    intro g hg
    exact l55_normalizer_inf (hPX hg) (l55_mem_normalizer_centralizer (hPQ hg))
  have hX₀X : X₀ ≤ X := (oResOf_le p C).trans inf_le_left
  have hlt : X₀ < X := by
    refine lt_of_le_of_ne hX₀X ?_
    intro heq
    have hXQ : X ≤ centralizer (Q : Set G) := by
      intro x hx
      have : x ∈ X₀ := heq ▸ hx
      exact ((oResOf_le p C) this).2
    have hZn := l55_normal_inf_centralizer N
    rcases hmin (N ⊓ centralizer (N : Set G)) inf_le_left hZn with hZ | hZ
    · apply hQ1
      rw [eq_bot_iff]
      intro q hq
      have hqN : q ∈ N := hQ.1 hq
      have hqC : q ∈ centralizer (N : Set G) := by
        rw [mem_centralizer_iff]
        intro n hn
        exact (mem_centralizer_iff.mp (hXQ (hNX hn)) q hq).symm
      have : q ∈ N ⊓ centralizer (N : Set G) := ⟨hqN, hqC⟩
      rw [hZ] at this
      exact this
    · obtain ⟨a, ha, b, hb, hab⟩ := hnab
      apply hab
      have : a ∈ N ⊓ centralizer (N : Set G) := hZ.ge ha
      exact (mem_centralizer_iff.mp this.2 b hb).symm
  have hcardX₀ : Nat.card X₀ ≤ m :=
    Nat.lt_succ_iff.mp (lt_of_lt_of_le (Subgroup.card_lt_of_lt hlt) hcard)
  have hih := ih G X₀ P hcardX₀ hX₀p hP hX₀P
  have hN326 := hq326 G N P ‹N.Normal› hN1 hmin hnab
  calc X ≤ N ⊔ X₀ := hXN
    _ ≤ ⁅X, P⁆ ⊔ (X ⊓ centralizer (P : Set G)) :=
      sup_le (hN326.trans (sup_le_sup (Subgroup.commutator_mono hNX le_rfl)
          (inf_le_inf_right _ hNX)))
        (hih.trans (sup_le_sup (Subgroup.commutator_mono hX₀X le_rfl) (inf_le_inf_right _ hX₀X)))

end CFSG.GH74.GLS.Balance
