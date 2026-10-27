module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerRank
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Lvl

open Subgroup CFSG.Open

variable {G : Type} [Group G] [Finite G]

noncomputable def commHom {A B : Subgroup G} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hBA : B ≤ A) (x : G) (hcomm : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B) : ↥A →* ↥B where
  toFun a := ⟨x * a * x⁻¹ * (a : G)⁻¹, hcomm a a.2⟩
  map_one' := by ext; simp
  map_mul' a b := by
    ext
    simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
    have hxa : x * a * x⁻¹ ∈ A := by
      have := mul_mem (hBA (hcomm a a.2)) a.2
      simpa [mul_assoc] using this
    have hb : x * b * x⁻¹ * (b : G)⁻¹ ∈ A := hBA (hcomm b b.2)
    have e1 := hAc _ hxa _ hb
    have e2 := hAc _ (inv_mem a.2) _ hb
    calc x * (a * b) * x⁻¹ * ((a : G) * b)⁻¹
        = (x * a * x⁻¹) * (x * b * x⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (x * a * x⁻¹) * ((a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹)) := by
          rw [mul_assoc, ← e2]
      _ = x * a * x⁻¹ * (a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹) := by group

theorem level_lemma {p : ℕ} [hp : Fact p.Prime] {A B : Subgroup G} {x : G} {k : ℕ}
    (hA : IsElemAbelian p A) (hBA : B ≤ A) (hcomm : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ B)
    (hcard : Nat.card B * p ^ k ≤ Nat.card A) (hx : orderOf x = p) (hxA : x ∉ A) :
    k + 1 ≤ pRank p (centralizer ({x} : Set G)) := by
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val this
  set f := commHom hAc hBA x hcomm
  set C : Subgroup G := A ⊓ centralizer ({x} : Set G) with hC
  have hker : ∀ a : ↥A, a ∈ f.ker ↔ (a : G) ∈ C := by
    intro a
    rw [MonoidHom.mem_ker, hC, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h' : x * a * x⁻¹ * (a : G)⁻¹ = 1 := congrArg Subtype.val h
      refine ⟨a.2, ?_⟩
      have := mul_inv_eq_one.mp h'
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    · rintro ⟨-, h⟩
      ext
      change x * a * x⁻¹ * (a : G)⁻¹ = 1
      rw [← h]; group
  have hCcard : Nat.card A ≤ Nat.card C * Nat.card B := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    have h2 : Nat.card (↥A ⧸ f.ker) = Nat.card f.range :=
      Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have h3 : Nat.card f.range ≤ Nat.card B := Subgroup.card_le_card_group _
    have h4 : Nat.card f.ker = Nat.card C := by
      have hle : C ≤ A := inf_le_left
      rw [show f.ker = C.subgroupOf A from Subgroup.ext fun a => by
        rw [hker, Subgroup.mem_subgroupOf]]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    rw [h1, h2, h4, mul_comm]
    exact Nat.mul_le_mul_left _ h3
  have hCe : IsElemAbelian p C := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => hA.2 y (Subgroup.mem_inf.mp hy).1⟩
    ext
    exact hAc _ (Subgroup.mem_inf.mp a.2).1 _ (Subgroup.mem_inf.mp b.2).1
  have hCp : IsPGroup p C := fun y => ⟨1, by
    ext; simpa using hCe.2 y y.2⟩
  obtain ⟨s, hs⟩ := hCp.exists_card_eq
  have hks : k ≤ s := by
    have hBpos : 0 < Nat.card B := Nat.card_pos
    have : p ^ k ≤ p ^ s := by
      have := hcard.trans (hCcard.trans_eq (by rw [hs]))
      rw [mul_comm] at this
      exact Nat.le_of_mul_le_mul_right this hBpos
    exact (Nat.pow_le_pow_iff_right hp.out.one_lt).mp this
  have hZe : IsElemAbelian p (zpowers x) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      ext
      simp only [Subgroup.coe_mul, ← hi, ← hj]
      exact ((Commute.refl x).zpow_zpow i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
        one_zpow]
  have hZc : Nat.card (zpowers x) = p ^ 1 := by rw [Nat.card_zpowers, hx, pow_one]
  have hcomm' : ∀ a ∈ C, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hax : Commute a x :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ha).2
    exact (hax.zpow_right i).eq
  have hdisj : Disjoint C (zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro y hyC hyZ
    by_contra hy1
    apply hxA
    have hyA : y ∈ A := (Subgroup.mem_inf.mp hyC).1
    have hle : zpowers x ≤ zpowers y := by
      have hcard : Nat.card (zpowers y) = p := by
        have hdvd : Nat.card (zpowers y) ∣ Nat.card (zpowers x) :=
          Subgroup.card_dvd_of_le ((zpowers_le).mpr hyZ)
        rw [hZc, pow_one] at hdvd
        rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
        · exact absurd (by
            rw [Subgroup.card_eq_one, zpowers_eq_bot] at h; exact h) hy1
        · exact h
      exact (Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hyZ)
        (by rw [hcard, hZc, pow_one])).ge
    exact (zpowers_le.mpr hyA) (hle (mem_zpowers x))
  have hCle : C ≤ centralizer ({x} : Set G) := inf_le_right
  have hZle : zpowers x ≤ centralizer ({x} : Set G) := by
    rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  have := CFSG.LocalAnalysis.RankThreeTheoremC.add_le_pRank_of_commute hCe hZe hs hZc hcomm'
    hdisj hCle hZle
  omega

theorem outer_rank {p : ℕ} [hp : Fact p.Prime] {L E : Subgroup G} {x : G} {k : ℕ}
    (hE : IsElemAbelian p E) (hc : Nat.card E = p ^ k) (hEL : E ≤ L)
    (hEx : E ≤ centralizer ({x} : Set G)) (hx : orderOf x = p) (hxL : x ∉ L) :
    k + 1 ≤ pRank p (centralizer ({x} : Set G)) := by
  have hZe : IsElemAbelian p (zpowers x) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
      exact ((Commute.refl x).zpow_zpow i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hx, pow_orderOf_eq_one,
        one_zpow]
  have hZc : Nat.card (zpowers x) = p ^ 1 := by rw [Nat.card_zpowers, hx, pow_one]
  have hcomm' : ∀ a ∈ E, ∀ b ∈ zpowers x, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hax : Commute a x := Subgroup.mem_centralizer_singleton_iff.mp (hEx ha)
    exact (hax.zpow_right i).eq
  have hdisj : Disjoint E (zpowers x) := by
    rw [Subgroup.disjoint_def]
    intro y hyE hyZ
    by_contra hy1
    apply hxL
    have hle : zpowers x ≤ zpowers y := by
      have hcard : Nat.card (zpowers y) = p := by
        have hdvd : Nat.card (zpowers y) ∣ Nat.card (zpowers x) :=
          Subgroup.card_dvd_of_le ((zpowers_le).mpr hyZ)
        rw [hZc, pow_one] at hdvd
        rcases (Nat.dvd_prime hp.out).mp hdvd with h | h
        · exact absurd (by
            rw [Subgroup.card_eq_one, zpowers_eq_bot] at h; exact h) hy1
        · exact h
      exact (Subgroup.eq_of_le_of_card_ge ((zpowers_le).mpr hyZ)
        (by rw [hcard, hZc, pow_one])).ge
    exact (zpowers_le.mpr (hEL hyE)) (hle (mem_zpowers x))
  have hZle : zpowers x ≤ centralizer ({x} : Set G) := by
    rw [zpowers_le, Subgroup.mem_centralizer_singleton_iff]
  exact CFSG.LocalAnalysis.RankThreeTheoremC.add_le_pRank_of_commute hE hZe hc hZc hcomm'
    hdisj hEx hZle

theorem exists_conj_mem_sylow {p : ℕ} [Fact p.Prime] (P : Sylow p G) {x : G}
    (hx : orderOf x = p) : ∃ g : G, g * x * g⁻¹ ∈ (P : Subgroup G) := by
  have hxp : IsPGroup p (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨Q, hQ⟩ := hxp.exists_le_sylow
  obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq G P Q
  have hmem : x ∈ ((g • P : Sylow p G) : Subgroup G) := hQ (Subgroup.mem_zpowers x)
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmem
  obtain ⟨y, hy, hyx⟩ := hmem
  refine ⟨g⁻¹, ?_⟩
  have : g⁻¹ * x * g⁻¹⁻¹ = y := by
    rw [← hyx]
    simp [MulAut.conj_apply, mul_assoc]
  rw [this]
  exact hy

theorem three_le_pRank_of_witness {p : ℕ} [hp : Fact p.Prime] (P : Sylow p G) {A B : Subgroup G}
    (hAP : A ≤ P) (hA : IsElemAbelian p A) (hBA : B ≤ A)
    (hcomm : ∀ u ∈ (P : Subgroup G), ∀ a ∈ A, u * a * u⁻¹ * a⁻¹ ∈ B)
    (hcard : Nat.card B * p ^ 2 ≤ Nat.card A)
    (hbig : p ^ 3 ≤ Nat.card A ∨
      ((∀ u ∈ (P : Subgroup G), ∀ a ∈ A, u * a = a * u) ∧ 3 ≤ pRank p (⊤ : Subgroup G)))
    {y : G} (hy : orderOf y = p) : 3 ≤ pRank p (centralizer ({y} : Set G)) := by
  have hp1 := hp.out.one_lt
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow P hy
  set y' := g * y * g⁻¹
  have hy' : orderOf y' = p := by
    have : SemiconjBy g y y' := by simp only [SemiconjBy, y']; group
    rw [← hy]; exact this.orderOf_eq.symm
  have htr : pRank p (centralizer ({y'} : Set G)) ≤ pRank p (centralizer ({y} : Set G)) := by
    refine (CFSG.SectionRank.pRank_le_map hp1 (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective _).trans (CFSG.SectionRank.pRank_mono hp1 ?_)
    rintro _ ⟨c, hc, rfl⟩
    have hc : c * y' = y' * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    change g⁻¹ * c * g⁻¹⁻¹ ∈ _
    rw [inv_inv, Subgroup.mem_centralizer_singleton_iff]
    have : y = g⁻¹ * y' * g := by simp only [y']; group
    rw [this]
    calc g⁻¹ * c * g * (g⁻¹ * y' * g) = g⁻¹ * (c * y') * g := by group
      _ = g⁻¹ * (y' * c) * g := by rw [hc]
      _ = g⁻¹ * y' * g * (g⁻¹ * c * g) := by group
  refine le_trans ?_ htr
  by_cases hyA : y' ∈ A
  · rcases hbig with h3 | ⟨hcen, hrk⟩
    ·
      have hAc : A ≤ centralizer ({y'} : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hA.1.is_comm.comm ⟨a, ha⟩ ⟨y', hyA⟩
        simpa using (congrArg Subtype.val this)
      have hAp : IsPGroup p A := fun z => ⟨1, by ext; simpa using hA.2 z z.2⟩
      obtain ⟨r, hr⟩ := hAp.exists_card_eq
      have h3r : 3 ≤ r := by
        rw [hr] at h3; exact (Nat.pow_le_pow_iff_right hp1).mp h3
      exact h3r.trans (CFSG.SectionRank.le_pRank hp1 hAc hA hr)
    ·
      have hPc : (P : Subgroup G) ≤ centralizer ({y'} : Set G) := by
        intro u hu
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcen u hu y' hyA
      have hPr : pRank p (P : Subgroup G) = pRank p (⊤ : Subgroup G) := by
        refine le_antisymm (CFSG.SectionRank.pRank_mono hp1 le_top) ?_
        obtain ⟨E, -, hE, hEc⟩ := CFSG.SectionRank.exists_pRank hp1 (⊤ : Subgroup G)
        have hEp : IsPGroup p E := fun z => ⟨1, by ext; simpa using hE.2 z z.2⟩
        obtain ⟨Q, hQ⟩ := hEp.exists_le_sylow
        obtain ⟨h, rfl⟩ := MulAction.exists_smul_eq G Q P
        have := CFSG.SectionRank.pRank_le_map hp1 (MulAut.conj h).toMonoidHom
          (MulAut.conj h).injective E
        refine (CFSG.SectionRank.le_pRank hp1 le_rfl hE hEc).trans (this.trans
          (CFSG.SectionRank.pRank_mono hp1 ?_))
        rintro _ ⟨e, he, rfl⟩
        rw [Sylow.coe_subgroup_smul]
        exact Subgroup.smul_mem_pointwise_smul e (MulAut.conj h) _ (hQ he)
      calc 3 ≤ pRank p (⊤ : Subgroup G) := hrk
        _ = pRank p (P : Subgroup G) := hPr.symm
        _ ≤ _ := CFSG.SectionRank.pRank_mono hp1 hPc
  · exact level_lemma hA hBA (fun a ha => hcomm y' hg a ha) hcard hy' hyA

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD291Lvl
