module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64AsmRank1

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree

open CFSG.Open CFSG.SectionRank

@[expose] def ShapeSimple (P : Type) [Group P] [Finite P] : Prop :=
  (IsCyclic P ∧ 9 ≤ Nat.card P) ∨
    ((¬ ∀ a b : P, a * b = b * a) ∧ Open.pRank 3 (⊤ : Subgroup P) ≤ 2)

@[expose] def ShapeProd (P : Type) [Group P] [Finite P] : Prop :=
  ((¬ ∀ a b : P, a * b = b * a) ∧ Open.pRank 3 (⊤ : Subgroup P) ≤ 3) ∨
    (9 < Nat.card P ∧ Open.pRank 3 (⊤ : Subgroup P) ≤ 2) ∨
    (9 < Nat.card P ∧ Nat.card (Subgroup.center P) ≤ 9)

variable {Q : Type} [Group Q] [Finite Q]

theorem noncommCoprod_injective {A C : Subgroup Q} (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c)
    (hdisj : A ⊓ C = ⊥) :
    Function.Injective (MonoidHom.noncommCoprod A.subtype C.subtype
      (fun a c => hcomm a a.2 c c.2)) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, c⟩ hac
  change (a : Q) * c = 1 at hac
  have h1 : (a : Q) = (c : Q)⁻¹ := eq_inv_of_mul_eq_one_left hac
  have ha : (a : Q) ∈ A ⊓ C := ⟨a.2, h1 ▸ C.inv_mem c.2⟩
  rw [hdisj, Subgroup.mem_bot] at ha
  have hc : (c : Q) = 1 := by rw [ha, one_mul] at hac; exact hac
  exact Prod.ext (Subtype.ext ha) (Subtype.ext hc)

theorem two_add_pRank_le {A C : Subgroup Q} (hA : IsElemAbelian 3 A) (hA9 : Nat.card A = 9)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c) (hdisj : A ⊓ C = ⊥) :
    2 + Open.pRank 3 C ≤ Open.pRank 3 (⊤ : Subgroup Q) := by
  obtain ⟨E, hEC, hE, hEc⟩ := exists_pRank (by norm_num : 1 < 3) C
  have hcAE : ∀ a ∈ A, ∀ e ∈ E, Commute a e := fun a ha e he => hcomm a ha e (hEC he)
  have hdAE : A ⊓ E = ⊥ := le_bot_iff.mp (hdisj ▸ inf_le_inf_left A hEC)
  have hinj := noncommCoprod_injective hcAE hdAE
  have hAc : ∀ a b : A, a * b = b * a := fun a b => hA.1.is_comm.comm a b
  have hEcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  refine le_pRank_of_injective (A := ↥A × ↥E) (by norm_num) (fun x y => ?_) (fun x => ?_) ?_ _
    hinj le_top
  · exact Prod.ext (hAc _ _) (hEcomm _ _)
  · exact Prod.ext (Subtype.ext (hA.2 _ x.1.2)) (Subtype.ext (hE.2 _ x.2.2))
  · rw [Nat.card_prod, hA9, hEc]; ring

theorem card_le_three_of_pRank_le_one {N E : Subgroup Q} (hN : Open.pRank 3 N ≤ 1) (hEN : E ≤ N)
    (hE : IsElemAbelian 3 E) {j : ℕ} (hj : Nat.card E = 3 ^ j) : j ≤ 1 :=
  (le_pRank (by norm_num) hEN hE hj).trans hN

theorem pRank_le_quot_add_one (N : Subgroup Q) [N.Normal] (hN : Open.pRank 3 N ≤ 1) :
    Open.pRank 3 (⊤ : Subgroup Q) ≤ Open.pRank 3 (⊤ : Subgroup (Q ⧸ N)) + 1 := by
  obtain ⟨E, -, hE, hEc⟩ := exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup Q)
  set g : ↥E →* Q ⧸ N := (QuotientGroup.mk' N).comp E.subtype
  have hsplit : Nat.card E = Nat.card g.range * Nat.card g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
  have hdvd1 : Nat.card g.range ∣ 3 ^ Open.pRank 3 (⊤ : Subgroup Q) :=
    hEc ▸ Dvd.intro _ hsplit.symm
  have hdvd2 : Nat.card g.ker ∣ 3 ^ Open.pRank 3 (⊤ : Subgroup Q) :=
    hEc ▸ Dvd.intro_left _ hsplit.symm
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd2
  have hrange : g.range = E.map (QuotientGroup.mk' N) := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hi' : i ≤ Open.pRank 3 (⊤ : Subgroup (Q ⧸ N)) :=
    le_pRank (by norm_num) le_top (hrange ▸ isElemAbelian_map hE _) (hrange ▸ hi)
  have hkerE : g.ker.map E.subtype ≤ N := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mp hx
  have hkc : Nat.card (g.ker.map E.subtype) = 3 ^ j := by
    rw [Subgroup.card_map_of_injective E.subtype_injective, hj]
  have hkel : IsElemAbelian 3 (g.ker.map E.subtype) := by
    have := hE.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨x, -, hx⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, -, hy⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      change (a : Q) * b = b * a
      rw [← hx, ← hy]
      exact congrArg Subtype.val (mul_comm' x y)
    · rintro _ ⟨x, -, rfl⟩
      exact hE.2 _ x.2
  have hj' := card_le_three_of_pRank_le_one hN hkerE hkel hkc
  have hk : 3 ^ Open.pRank 3 (⊤ : Subgroup Q) = 3 ^ (i + j) := by
    rw [← hEc, hsplit, hi, hj, pow_add]
  have := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hk
  omega

theorem pRank_le_one_of_isCyclic {P : Type} [Group P] [Finite P] [IsCyclic P] :
    Open.pRank 3 (⊤ : Subgroup P) ≤ 1 := by
  refine pRank_le (by norm_num) fun E _ hE => ?_
  haveI : IsCyclic E := Subgroup.isCyclic E
  have hexp : Monoid.exponent E ∣ 3 :=
    Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext (hE.2 _ x.2)
  rw [IsCyclic.exponent_eq_card] at hexp
  simpa using Nat.le_of_dvd (by norm_num) hexp

theorem eq_bot_of_pRank_eq_zero {C : Subgroup Q} (hC : IsPGroup 3 C) (h : Open.pRank 3 C = 0) :
    C = ⊥ := by
  by_contra hne
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hne
  have h3 : 3 ∣ Nat.card C := by
    obtain ⟨k, hk⟩ := hC.exists_card_eq
    have h1 : 1 < Nat.card C := Finite.one_lt_card
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · exact dvd_pow_self 3 (by omega)
  obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) 3 h3
  have h1 : 1 ≤ Open.pRank 3 C := by
    refine le_pRank (H := C) (E := Subgroup.zpowers (c : Q)) (by norm_num)
      ((Subgroup.zpowers_le).mpr c.2) ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩ ?_
    · obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      change (a : Q) * b = b * a
      rw [← hm, ← hn, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have : (c : Q) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, ← hc, pow_orderOf_eq_one, Subgroup.coe_one]
      rw [this, one_zpow]
    · rw [Nat.card_zpowers, Subgroup.orderOf_coe, hc, pow_one]
  omega

theorem comm_of_sup {A C : Subgroup Q} (hgen : A ⊔ C = ⊤) (hAc : ∀ a ∈ A, ∀ b ∈ A, Commute a b)
    (hCc : ∀ a ∈ C, ∀ b ∈ C, Commute a b) (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c) :
    ∀ x y : Q, x * y = y * x := by
  have hA : A ≤ Subgroup.centralizer ((A ⊔ C : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (fun x hx y hy => (hAc y hy x hx).eq) (fun x hx y hy => ?_)
    exact (hcomm y hy x hx).eq
  have hC : C ≤ Subgroup.centralizer ((A ⊔ C : Subgroup Q) : Set Q) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (fun x hx y hy => (hcomm x hx y hy).eq.symm) (fun x hx y hy => ?_)
    exact (hCc y hy x hx).eq
  have htop := sup_le hA hC
  rw [hgen] at htop
  intro x y
  have hx : x ∈ Subgroup.centralizer ((⊤ : Subgroup Q) : Set Q) := htop (Subgroup.mem_top x)
  exact (Subgroup.mem_centralizer_iff.mp hx y (Subgroup.mem_top y)).symm

theorem comm_of_pRank_le_one {A C : Subgroup Q} (hC : IsPGroup 3 C) (hA : IsElemAbelian 3 A)
    (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c) (hgen : A ⊔ C = ⊤) (h : Open.pRank 3 C ≤ 1) :
    ∀ x y : Q, x * y = y * x := by
  haveI := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm.isCyclic_of_pRank_le_one
    Nat.prime_three (by norm_num) hC h
  have := hA.1
  refine comm_of_sup hgen (fun a ha b hb => ?_) (fun a ha b hb => ?_) hcomm
  · exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  · have hc : (⟨a, ha⟩ : C) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := IsCyclic.commutative.is_comm.comm _ _
    exact congrArg Subtype.val hc

theorem quot_comm (N : Subgroup Q) [N.Normal] (h : ∀ x y : Q, x * y = y * x) :
    ∀ a b : Q ⧸ N, a * b = b * a := by
  intro a b
  induction a using QuotientGroup.induction_on
  induction b using QuotientGroup.induction_on
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem false_of_shapeSimple (hQ : IsPGroup 3 Q) {A C : Subgroup Q} (N : Subgroup Q) [N.Normal]
    (hA : IsElemAbelian 3 A) (hA9 : Nat.card A = 9) (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c)
    (hdisj : A ⊓ C = ⊥) (hgen : A ⊔ C = ⊤) (hN : Open.pRank 3 N ≤ 1)
    (h : ShapeSimple (Q ⧸ N)) : False := by
  have hC : IsPGroup 3 C := hQ.to_subgroup C
  have h1 := two_add_pRank_le hA hA9 hcomm hdisj
  have h2 := pRank_le_quot_add_one N hN
  rcases h with ⟨hcyc, h9⟩ | ⟨hnc, hrk⟩
  · haveI := hcyc
    have h3 := pRank_le_one_of_isCyclic (P := Q ⧸ N)
    have hC0 : C = ⊥ := eq_bot_of_pRank_eq_zero hC (by omega)
    rw [hC0, sup_bot_eq] at hgen
    have hexp : Monoid.exponent (Q ⧸ N) ∣ 3 := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      induction x using QuotientGroup.induction_on with
      | H q =>
        have hq : q ∈ A := hgen ▸ Subgroup.mem_top q
        rw [← QuotientGroup.mk_pow, hA.2 q hq, QuotientGroup.mk_one]
    rw [IsCyclic.exponent_eq_card] at hexp
    have := Nat.le_of_dvd (by norm_num) hexp
    omega
  · have hC1 : Open.pRank 3 C ≤ 1 := by omega
    exact hnc (quot_comm N (comm_of_pRank_le_one hC hA hcomm hgen hC1))

theorem twentySeven_le_card_center (hQ : IsPGroup 3 Q) {A C : Subgroup Q}
    (hA : IsElemAbelian 3 A) (hA9 : Nat.card A = 9) (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c)
    (hdisj : A ⊓ C = ⊥) (hgen : A ⊔ C = ⊤) (hC1 : C ≠ ⊥) :
    27 ≤ Nat.card (Subgroup.center Q) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z : Subgroup Q := (Subgroup.center C).map C.subtype
  have hZC : Z ≤ C := Subgroup.map_subtype_le _
  have hcAZ : ∀ a ∈ A, ∀ z ∈ Z, Commute a z := fun a ha z hz => hcomm a ha z (hZC hz)
  have hdAZ : A ⊓ Z = ⊥ := le_bot_iff.mp (hdisj ▸ inf_le_inf_left A hZC)
  have hinj := noncommCoprod_injective hcAZ hdAZ
  have hAc : ∀ a ∈ A, ∀ b ∈ A, Commute a b := fun a ha b hb => by
    have := hA.1
    exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : A) ⟨b, hb⟩)
  have hAZ : A ⊔ Z ≤ Subgroup.center Q := by
    have hcen : ∀ x, (∀ y ∈ A, Commute x y) → (∀ y ∈ C, Commute x y) → x ∈ Subgroup.center Q := by
      intro x hxA hxC
      have hle : A ⊔ C ≤ Subgroup.centralizer ({x} : Set Q) :=
        sup_le (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hxA y hy).eq.symm)
          (fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hxC y hy).eq.symm)
      rw [hgen] at hle
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
    refine sup_le (fun a ha => hcen a (hAc a ha) (hcomm a ha)) ?_
    rintro _ ⟨z, hz, rfl⟩
    refine hcen _ (fun y hy => (hcomm y hy z z.2).symm) (fun y hy => ?_)
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz ⟨y, hy⟩).symm)
  have hrange : (MonoidHom.noncommCoprod A.subtype Z.subtype
      (fun a c => hcAZ a a.2 c c.2)).range ≤ A ⊔ Z := by
    rintro _ ⟨x, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)
  have hcard : Nat.card (↥A × ↥Z) ≤ Nat.card (Subgroup.center Q) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Subgroup.card_le_of_le (hrange.trans hAZ)
  have hZ3 : 3 ≤ Nat.card Z := by
    have hCp : IsPGroup 3 C := hQ.to_subgroup C
    haveI : Nontrivial C := (Subgroup.nontrivial_iff_ne_bot C).mpr hC1
    haveI := hCp.center_nontrivial
    rw [Subgroup.card_map_of_injective C.subtype_injective]
    obtain ⟨k, hk⟩ := (hCp.to_subgroup (Subgroup.center C)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center C) := Finite.one_lt_card
    rw [hk] at h1 ⊢
    rcases k with _ | k
    · simp at h1
    · calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [Nat.card_prod, hA9] at hcard
  omega

theorem false_of_shapeProd (hQ : IsPGroup 3 Q) {A C : Subgroup Q} (hA : IsElemAbelian 3 A)
    (hA9 : Nat.card A = 9) (hcomm : ∀ a ∈ A, ∀ c ∈ C, Commute a c) (hdisj : A ⊓ C = ⊥)
    (hgen : A ⊔ C = ⊤) (h : ShapeProd Q) : False := by
  have hC : IsPGroup 3 C := hQ.to_subgroup C
  have h1 := two_add_pRank_le hA hA9 hcomm hdisj
  have hcardC : C = ⊥ → Nat.card Q = 9 := fun hC0 => by
    rw [hC0, sup_bot_eq] at hgen
    rw [← Subgroup.card_top (G := Q), ← hgen, hA9]
  rcases h with ⟨hnc, hrk⟩ | ⟨h9, hrk⟩ | ⟨h9, hz⟩
  · exact hnc (comm_of_pRank_le_one hC hA hcomm hgen (by omega))
  · have := hcardC (eq_bot_of_pRank_eq_zero hC (by omega))
    omega
  · have hC1 : C ≠ ⊥ := fun hC0 => by have := hcardC hC0; omega
    have := twentySeven_le_card_center hQ hA hA9 hcomm hdisj hgen hC1
    omega

theorem shapeSimple_congr {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P'] (e : P ≃* P')
    (h : ShapeSimple P) : ShapeSimple P' := by
  rcases h with ⟨hc, h9⟩ | ⟨hnc, hr⟩
  · exact Or.inl ⟨isCyclic_of_surjective e.toMonoidHom e.surjective,
      (Nat.card_congr e.toEquiv) ▸ h9⟩
  · refine Or.inr ⟨fun hcomm => hnc fun a b => e.injective ?_, ?_⟩
    · rw [map_mul, map_mul, hcomm]
    · rw [← pRank_top_eq_of_mulEquiv (by norm_num) e]; exact hr

theorem shapeProd_congr {P P' : Type} [Group P] [Finite P] [Group P'] [Finite P'] (e : P ≃* P')
    (h : ShapeProd P) : ShapeProd P' := by
  have hcard := Nat.card_congr e.toEquiv
  have hrk : Open.pRank 3 (⊤ : Subgroup P) = Open.pRank 3 (⊤ : Subgroup P') :=
    pRank_top_eq_of_mulEquiv (by norm_num) e
  rcases h with ⟨hnc, hr⟩ | ⟨h9, hr⟩ | ⟨h9, hz⟩
  · refine Or.inl ⟨fun hcomm => hnc fun a b => e.injective ?_, hrk ▸ hr⟩
    rw [map_mul, map_mul, hcomm]
  · exact Or.inr (Or.inl ⟨hcard ▸ h9, hrk ▸ hr⟩)
  · exact Or.inr (Or.inr ⟨hcard ▸ h9, (Nat.card_congr (Subgroup.centerCongr e).toEquiv) ▸ hz⟩)

end CFSG.LocalAnalysis.RankThreeTheoremC.TenNineOneThree
