module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_CaseJgtJoin

public section

namespace CFSG.HardMathSupport.Timmesfeld.ComponentBalance

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

set_option linter.unusedSectionVars false

variable {Q : Type} [Group Q] [Finite Q]

theorem t113_normalizer_of_map {B L : Subgroup Q} {a : Q} (ha : a ∈ t113A B L)
    {S : Subgroup ↥L} (hS : S.map (t113Rho B L ⟨a, ha⟩).toMonoidHom = S) :
    a ∈ Subgroup.normalizer ((S.map L.subtype : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨s, hs, rfl⟩
    have h1 : t113Rho B L ⟨a, ha⟩ s ∈ S.map (t113Rho B L ⟨a, ha⟩).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hs
    rw [hS] at h1
    exact ⟨_, h1, rfl⟩
  · rintro ⟨s', hs', he⟩
    have hhL : h ∈ L := by
      refine ((Subgroup.mem_normalizer_iff.1 ha.1) h).2 ?_
      rw [← he]
      exact s'.2
    have hs'' : s' ∈ S.map (t113Rho B L ⟨a, ha⟩).toMonoidHom := by rw [hS]; exact hs'
    obtain ⟨s, hs, hse⟩ := hs''
    have hss : s = ⟨h, hhL⟩ := by
      apply (t113Rho B L ⟨a, ha⟩).injective
      apply Subtype.ext
      have := congrArg Subtype.val hse
      rw [show (((t113Rho B L ⟨a, ha⟩).toMonoidHom s : ↥L) : Q) =
        ((t113Rho B L ⟨a, ha⟩ s : ↥L) : Q) from rfl] at this
      rw [this]
      exact he
    exact ⟨⟨h, hhL⟩, hss ▸ hs, rfl⟩

theorem t113_mem_normalizer_of_centralizes {L S : Subgroup Q} (hSL : S ≤ L) {f : Q}
    (hf : ∀ l ∈ L, f * l = l * f) : f ∈ Subgroup.normalizer (S : Set Q) :=
  t113_mem_normalizer_of_commute fun j hj => hf j (hSL hj)

theorem t113_jgt_count (Tb : Tables113) {B L : Subgroup Q} {x : Q} (Tr : Triple113 B L x)
    (hL2 : IsL2TwoPowOdd ↥L)
    (hmax : ∀ E : Subgroup Q, IsElemAbelian 3 E →
      (∃ S : Subgroup Q, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set Q)) →
        Nat.card E ≤ Nat.card B)
    {g1 g2 g3 : Q}
    (h1 : GLBConj g1 L ≠ L) (h2 : GLBConj g2 L ≠ L) (h3 : GLBConj g3 L ≠ L)
    (h12 : GLBConj g1 L ≠ GLBConj g2 L) (h13 : GLBConj g1 L ≠ GLBConj g3 L)
    (h23 : GLBConj g2 L ≠ GLBConj g3 L)
    (hA : ∀ a ∈ t113A B L, a * g1 = g1 * a ∧ a * g2 = g2 * a ∧ a * g3 = g3 * a) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h2L, h3L, hcen⟩ := Tb.T0 ↥L hL2
  have Tri : Tri3 (GLBConj g1 L) (GLBConj g2 L) (GLBConj g3 L) :=
    ⟨Tr.comm_of_ne h12, Tr.comm_of_ne h13, Tr.comm_of_ne h23,
      fun z hz hc => Tr.eq_one_of_central hz hc, fun z hz hc => Tr.eq_one_of_central hz hc,
      fun z hz hc => Tr.eq_one_of_central hz hc⟩
  have LC : ∀ g : Q, GLBConj g L ≠ L → ∀ l ∈ L, ∀ w ∈ GLBConj g L, l * w = w * l := by
    intro g hg
    have := Tr.comm_of_ne (g := 1) (h := g) (by rw [gLBConj_one]; exact hg.symm)
    simpa only [gLBConj_one] using this
  have hB0pos : 0 < Nat.card (t113B0 B L) := Nat.card_pos
  have hcardB := Tr.card_B
  let Yg : Q → Subgroup Q := fun y =>
    Subgroup.zpowers (g1⁻¹ * y * g1) ⊔ Subgroup.zpowers (g2⁻¹ * y * g2) ⊔
      Subgroup.zpowers (g3⁻¹ * y * g3)
  have mem1 : ∀ y ∈ L, g1⁻¹ * y * g1 ∈ GLBConj g1 L := fun y hy => by
    rw [mem_gLBConj, show g1 * (g1⁻¹ * y * g1) * g1⁻¹ = y by group]; exact hy
  have mem2 : ∀ y ∈ L, g2⁻¹ * y * g2 ∈ GLBConj g2 L := fun y hy => by
    rw [mem_gLBConj, show g2 * (g2⁻¹ * y * g2) * g2⁻¹ = y by group]; exact hy
  have mem3 : ∀ y ∈ L, g3⁻¹ * y * g3 ∈ GLBConj g3 L := fun y hy => by
    rw [mem_gLBConj, show g3 * (g3⁻¹ * y * g3) * g3⁻¹ = y by group]; exact hy
  have YcommA : ∀ y : Q, ∀ f ∈ t113A B L, f * y = y * f → ∀ z ∈ Yg y, f * z = z * f := by
    intro y f hf hfy
    obtain ⟨c1, c2, c3⟩ := hA f hf
    exact t113_comm_join (t113_commute_conj c1 hfy) (t113_commute_conj c2 hfy)
      (t113_commute_conj c3 hfy)
  have B0commL : ∀ b ∈ t113B0 B L, ∀ l ∈ L, b * l = l * b := fun b hb l hl =>
    (Tr.B0_comm_K hb l (Tr.L_le_K hl)).symm
  have YcommB0 : ∀ y ∈ L, ∀ b ∈ t113B0 B L, ∀ z ∈ Yg y, b * z = z * b := fun y hy b hb =>
    YcommA y b (Tr.B0_mem_A hb) (B0commL b hb y hy)
  have Yspec : ∀ y ∈ L, orderOf y = 3 → IsElemAbelian 3 (Yg y) ∧ Nat.card (Yg y) = 27 ∧
      (∀ z ∈ Yg y, ∀ l ∈ L, z * l = l * z) ∧ (∀ z ∈ Yg y, z ∈ t113B0 B L → z = 1) := by
    intro y hy ho
    obtain ⟨hel, hcard, hone⟩ := Tri.zpowers_join (mem1 y hy) (mem2 y hy) (mem3 y hy)
      (by rw [t113_orderOf_conj, ho]) (by rw [t113_orderOf_conj, ho])
      (by rw [t113_orderOf_conj, ho])
    refine ⟨hel, hcard, ?_, ?_⟩
    · intro z hz l hl
      have hle : Yg y ≤ Subgroup.centralizer ({l} : Set Q) := by
        refine sup_le (sup_le ?_ ?_) ?_ <;> refine Subgroup.zpowers_le.2 ?_ <;>
          rw [Subgroup.mem_centralizer_singleton_iff]
        · exact (LC g1 h1 l hl _ (mem1 y hy)).symm
        · exact (LC g2 h2 l hl _ (mem2 y hy)).symm
        · exact (LC g3 h3 l hl _ (mem3 y hy)).symm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hz)
    · intro z hz hb
      refine hone z hz ?_ ?_ ?_
      · intro m hm
        exact t113_comm_gLBConj (hA z (Tr.B0_mem_A hb)).1 (B0commL z hb) m hm
      · intro m hm
        exact t113_comm_gLBConj (hA z (Tr.B0_mem_A hb)).2.1 (B0commL z hb) m hm
      · intro m hm
        exact t113_comm_gLBConj (hA z (Tr.B0_mem_A hb)).2.2 (B0commL z hb) m hm
  obtain ⟨y0', hy0'⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 3 h3L
  have hy0L : (y0' : Q) ∈ L := y0'.2
  have hy0o : orderOf (y0' : Q) = 3 := by rw [Subgroup.orderOf_coe, hy0']
  obtain ⟨u', hu'⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 h2L
  have huL : (u' : Q) ∈ L := u'.2
  have huo : orderOf (u' : Q) = 2 := by rw [Subgroup.orderOf_coe, hu']
  obtain ⟨S0, hS0ne, hS02, hS0L⟩ : ∃ S : Subgroup Q, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ L := by
    refine ⟨Subgroup.zpowers (u' : Q), ?_, ?_, Subgroup.zpowers_le.2 huL⟩
    · intro h
      have : (u' : Q) ∈ (⊥ : Subgroup Q) := h ▸ Subgroup.mem_zpowers _
      rw [Subgroup.mem_bot] at this
      rw [this, orderOf_one] at huo
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, huo]; norm_num)
  have normOfCent : ∀ S : Subgroup Q, S ≤ L → ∀ E : Subgroup Q,
      (∀ e ∈ E, ∀ l ∈ L, e * l = l * e) → E ≤ Subgroup.normalizer (S : Set Q) :=
    fun S hSL E hE e he => t113_mem_normalizer_of_centralizes hSL (hE e he)
  have hE1 : IsElemAbelian 3 (t113B0 B L ⊔ Yg y0') ∧
      Nat.card ↥(t113B0 B L ⊔ Yg y0') = Nat.card (t113B0 B L) * 27 := by
    obtain ⟨eY, cY, -, hYB0⟩ := Yspec _ hy0L hy0o
    have hi : t113B0 B L ⊓ Yg y0' = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      exact hYB0 z hz.2 hz.1
    obtain ⟨h1', h2'⟩ := t113_sup_elemAbelian Tr.B0_elem eY
      (fun p hp r hr => YcommB0 y0' hy0L p hp r hr) hi
    exact ⟨h1', by rw [h2', cY]⟩
  have hE1c : ∀ e ∈ t113B0 B L ⊔ Yg y0', ∀ l ∈ L, e * l = l * e := by
    have hle : t113B0 B L ⊔ Yg y0' ≤ Subgroup.centralizer (L : Set Q) := by
      refine sup_le (fun b hb => Subgroup.mem_centralizer_iff.2 fun l hl =>
        (B0commL b hb l hl).symm) (fun z hz => Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
      exact ((Yspec _ hy0L hy0o).2.2.1 z hz l hl).symm
    intro e he l hl
    exact (Subgroup.mem_centralizer_iff.1 (hle he) l hl).symm
  have h9 : 9 ≤ Nat.card (t113H B L) := by
    have := hmax _ hE1.1 ⟨S0, hS0ne, hS02, normOfCent S0 hS0L _ hE1c⟩
    rw [hE1.2, hcardB] at this
    by_contra hlt
    push Not at hlt
    nlinarith
  obtain ⟨hH9, hHin⟩ := Tb.T2 ↥L hL2 (t113H B L) Tr.H_elem
  have hH : Nat.card (t113H B L) = 9 := le_antisymm hH9 h9
  obtain ⟨α, hαH, hαout⟩ : ∃ α ∈ t113H B L, α ∉ innerAut113 ↥L := by
    by_contra hcon
    push Not at hcon
    have : t113H B L ⊓ innerAut113 ↥L = t113H B L := inf_eq_left.2 hcon
    rw [this] at hHin
    omega
  obtain ⟨⟨a, ha⟩, rfl⟩ := hαH
  have hα3 : t113Rho B L ⟨a, ha⟩ ^ 3 = 1 := Tr.H_elem.2 _ ⟨⟨a, ha⟩, rfl⟩
  have hα1 : t113Rho B L ⟨a, ha⟩ ≠ 1 := fun h => hαout (h ▸ (innerAut113 ↥L).one_mem)
  have hαo : orderOf (t113Rho B L ⟨a, ha⟩) = 3 := orderOf_eq_prime hα3 hα1
  obtain ⟨⟨y', hy'o, hy'fix⟩, S, hSne, hS2, hSα⟩ := Tb.T4 ↥L hL2 _ hαo hαout
  have hyL : (y' : Q) ∈ L := y'.2
  have hyo : orderOf (y' : Q) = 3 := by rw [Subgroup.orderOf_coe, hy'o]
  have hay : a * (y' : Q) = (y' : Q) * a := by
    have h := congrArg Subtype.val hy'fix
    have e : ((t113Rho B L ⟨a, ha⟩ y' : ↥L) : Q) = a * (y' : Q) * a⁻¹ := rfl
    rw [e] at h
    calc a * (y' : Q) = (a * (y' : Q) * a⁻¹) * a := by group
      _ = (y' : Q) * a := by rw [h]
  obtain ⟨eY2, cY2, hYc2, hYB02⟩ := Yspec _ hyL hyo
  obtain ⟨eF, cF, hFB, -⟩ := Tr.F_spec ha hαout
  have hFA : Subgroup.zpowers a ⊔ t113B0 B L ≤ t113A B L :=
    sup_le (Subgroup.zpowers_le.2 ha) (fun b hb => Tr.B0_mem_A hb)
  have hcomm : ∀ p ∈ Subgroup.zpowers a, ∀ r ∈ t113B0 B L, p * r = r * p := by
    rintro p ⟨n, rfl⟩ r hr
    have hc : Commute a r := Tr.comm_B ha.2 hr.1
    exact (hc.zpow_left n).eq
  have hE2 : IsElemAbelian 3 (Subgroup.zpowers a ⊔ t113B0 B L ⊔ Yg (y' : Q)) ∧
      Nat.card ↥(Subgroup.zpowers a ⊔ t113B0 B L ⊔ Yg (y' : Q)) =
        3 * Nat.card (t113B0 B L) * 27 := by
    have hi : (Subgroup.zpowers a ⊔ t113B0 B L) ⊓ Yg (y' : Q) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      rw [Subgroup.mem_bot]
      obtain ⟨hzF, hzY⟩ := hz
      obtain ⟨p, ⟨n, rfl⟩, r, hr, rfl⟩ := t113_mem_sup hcomm hzF
      beta_reduce at hzF hzY
      have hzA : a ^ n * r ∈ t113A B L :=
        (t113A B L).mul_mem ((t113A B L).zpow_mem ha n) (Tr.B0_mem_A hr)
      have e : (⟨a ^ n * r, hzA⟩ : ↥(t113A B L)) =
          (⟨a, ha⟩ : ↥(t113A B L)) ^ n * ⟨r, Tr.B0_mem_A hr⟩ := Subtype.ext (by simp)
      have hρ1 : t113Rho B L ⟨a ^ n * r, hzA⟩ = 1 := by
        ext l
        rw [Tr.rho_apply, MulAut.one_apply]
        have hc : (a ^ n * r) * (l : Q) = (l : Q) * (a ^ n * r) := hYc2 _ hzY l l.2
        calc (a ^ n * r) * (l : Q) * (a ^ n * r)⁻¹ = ((l : Q) * (a ^ n * r)) * (a ^ n * r)⁻¹ := by
              rw [hc]
          _ = l := by group
      have hr1 : t113Rho B L ⟨r, Tr.B0_mem_A hr⟩ = 1 := (Tr.rho_eq_one_iff _).2 hr
      rw [e, map_mul, Tr.rho_zpow, hr1, mul_one] at hρ1
      have h2 := Tr.pow_eq_one_of_inner ha hαout n (by rw [hρ1]; exact (innerAut113 ↥L).one_mem)
      rw [h2, one_mul] at hzY
      show a ^ n * r = 1
      rw [h2, one_mul]
      exact hYB02 r hzY hr
    have hFy : ∀ f ∈ Subgroup.zpowers a ⊔ t113B0 B L, f * (y' : Q) = (y' : Q) * f := by
      have hle : Subgroup.zpowers a ⊔ t113B0 B L ≤ Subgroup.centralizer ({(y' : Q)} : Set Q) := by
        refine sup_le (Subgroup.zpowers_le.2 ?_) (fun b hb => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]; exact hay
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact B0commL b hb _ hyL
      intro f hf
      exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hf))
    obtain ⟨h1', h2'⟩ := t113_sup_elemAbelian eF eY2
      (fun f hf z hz => YcommA y' f (hFA hf) (hFy f hf) z hz) hi
    exact ⟨h1', by rw [h2', cF, cY2]⟩
  have hS'L : S.map L.subtype ≤ L := Subgroup.map_subtype_le S
  have hS'ne : S.map L.subtype ≠ ⊥ := fun h =>
    hSne ((Subgroup.map_eq_bot_iff_of_injective S L.subtype_injective).1 h)
  have hS'2 : IsPGroup 2 (S.map L.subtype) :=
    hS2.of_equiv (Subgroup.equivMapOfInjective S L.subtype L.subtype_injective)
  have hE2n : Subgroup.zpowers a ⊔ t113B0 B L ⊔ Yg (y' : Q) ≤
      Subgroup.normalizer ((S.map L.subtype : Subgroup Q) : Set Q) := by
    refine sup_le (sup_le (Subgroup.zpowers_le.2 (t113_normalizer_of_map ha hSα))
      (fun b hb => t113_mem_normalizer_of_centralizes hS'L (B0commL b hb))) ?_
    intro z hz
    exact t113_mem_normalizer_of_centralizes hS'L fun l hl => hYc2 z hz l hl
  have := hmax _ hE2.1 ⟨_, hS'ne, hS'2, hE2n⟩
  rw [hE2.2, hcardB, hH] at this
  nlinarith

end CFSG.HardMathSupport.Timmesfeld.ComponentBalance
