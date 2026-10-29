module

public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma95A
import CFSG.LocalAnalysis.GLTheoremA.S4S.Prop415Hat
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevToolsK
public import CFSG.LocalAnalysis.GLTheoremA.S9.Inputs95
public import CFSG.LocalAnalysis.GLTheoremA.S9.Lemma94

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S9

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.UniquenessMaximal
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

structure Lemma95Inputs (G : Type) [Group G] [Finite G] (p : ℕ) : Prop where
  l93 : Lemma93Inputs G p
  lbal : LBalanceAt G p
  i145 : I145UsedAt G p
  i321 : I321UsedAt G p
  i713 : GL83.I_7_13_1
  i141 : I141At G p
  i2610 : I2610At G
  i67 : I67At G p
  rank3 : Rank3AutAt G
  dickson : InvolvedSL2At G
  i269 : I269At G

theorem le_normalizer_commutator {A K J : Subgroup G} (hA : J ≤ Subgroup.normalizer (A : Set G))
    (hK : J ≤ Subgroup.normalizer (K : Set G)) :
    J ≤ Subgroup.normalizer ((⁅A, K⁆ : Subgroup G) : Set G) := by
  intro j hj
  have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hA hj)
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.1 (hK hj)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator, h1, h2]

theorem card_of_index_eq {p : ℕ} (hp : p.Prime) {K E : Subgroup G} (hKE : K ≤ E)
    (hE : Nat.card E = p ^ 3) (hi : (K.subgroupOf E).index = p) : Nat.card K = p ^ 2 := by
  have h1 := Subgroup.card_mul_index (K.subgroupOf E)
  have h2 : Nat.card (K.subgroupOf E) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKE).toEquiv
  rw [h2, hi, hE] at h1
  have hp0 : 0 < p := hp.pos
  have : Nat.card K * p = p ^ 2 * p := by rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hp0 this

private theorem l95b_normalizer_centralizer {S : Set G} {g : G} (hg : ∀ s ∈ S, g * s = s * g) :
    g ∈ Subgroup.normalizer ((Subgroup.centralizer S : Subgroup G) : Set G) := by
  have key : ∀ g' : G, (∀ s ∈ S, g' * s = s * g') → (∀ s ∈ S, g'⁻¹ * s = s * g'⁻¹) →
      ∀ h ∈ Subgroup.centralizer S, g' * h * g'⁻¹ ∈ Subgroup.centralizer S := by
    intro g' hg' hginv h hh
    rw [Subgroup.mem_centralizer_iff] at hh ⊢
    intro s hs
    calc s * (g' * h * g'⁻¹) = (s * g') * h * g'⁻¹ := by group
      _ = (g' * s) * h * g'⁻¹ := by rw [← hg' s hs]
      _ = g' * (s * h) * g'⁻¹ := by group
      _ = g' * (h * s) * g'⁻¹ := by rw [hh s hs]
      _ = (g' * h) * (s * g'⁻¹) := by group
      _ = (g' * h) * (g'⁻¹ * s) := by rw [← hginv s hs]
      _ = (g' * h * g'⁻¹) * s := by group
  have hginv : ∀ s ∈ S, g⁻¹ * s = s * g⁻¹ := by
    intro s hs
    calc g⁻¹ * s = g⁻¹ * (s * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * s) * g⁻¹ := by rw [← hg s hs]
      _ = s * g⁻¹ := by group
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact key g hg hginv h
  · intro hh
    have h2 := key g⁻¹ hginv (fun s hs => by rw [inv_inv]; exact hg s hs) (g * h * g⁻¹) hh
    have e1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e1] at h2
    exact h2

open scoped Pointwise in
private theorem l95b_centralizer_sup_zpowers {E₀ : Subgroup G} {e : G}
    (hN : Subgroup.zpowers e ≤ Subgroup.normalizer (E₀ : Set G)) :
    Subgroup.centralizer ((E₀ ⊔ Subgroup.zpowers e : Subgroup G) : Set G) =
      Subgroup.centralizer (E₀ : Set G) ⊓ Subgroup.centralizer ({e} : Set G) := by
  apply le_antisymm
  · refine le_inf (Subgroup.centralizer_le fun h hh => Subgroup.mem_sup_left hh) ?_
    exact Subgroup.centralizer_le
      (Set.singleton_subset_iff.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers e)))
  · intro g hg
    have hgE : ∀ h ∈ (E₀ : Set G), h * g = g * h :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).1
    have hge : ∀ h ∈ ({e} : Set G), h * g = g * h :=
      Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hg).2
    rw [Subgroup.mem_centralizer_iff]
    have hmul : ((E₀ ⊔ Subgroup.zpowers e : Subgroup G) : Set G) =
        (E₀ : Set G) * (Subgroup.zpowers e : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left E₀ (Subgroup.zpowers e) hN
    intro h hh
    rw [hmul] at hh
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hag : a * g = g * a := hgE a ha
    have heg : e * g = g * e := hge e (Set.mem_singleton e)
    have hekg : e ^ k * g = g * e ^ k := Commute.zpow_left (show Commute e g from heg) k
    calc a * e ^ k * g = a * (e ^ k * g) := mul_assoc _ _ _
      _ = a * (g * e ^ k) := by rw [hekg]
      _ = (a * g) * e ^ k := (mul_assoc _ _ _).symm
      _ = (g * a) * e ^ k := by rw [hag]
      _ = g * (a * e ^ k) := mul_assoc _ _ _

private theorem l95b_mem_normalizer {p : ℕ} {B E₀ : Subgroup G} {g : G} (hB : IsElemAbelian p B)
    (hE₀B : E₀ ≤ B) (hg : g ∈ B) : g ∈ Subgroup.normalizer (E₀ : Set G) := by
  have hc : ∀ g' ∈ B, ∀ k ∈ E₀, g' * k * g'⁻¹ = k := fun g' hg' k hk => by
    rw [isElemAbelian_commute hB hg' (hE₀B hk), mul_inv_cancel_right]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rw [hc g hg h hh]
    exact hh
  · intro hh
    have h1 := hc g⁻¹ (B.inv_mem hg) _ hh
    have e1 : g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h := by group
    rw [e1] at h1
    rw [h1]
    exact hh

private theorem l95b_card_sup_zpowers {p : ℕ} (hp : p.Prime) {B E₀ : Subgroup G}
    (hB : IsElemAbelian p B) (hE₀B : E₀ ≤ B) (hE₀ : Nat.card E₀ = p ^ 2) {g : G} (hg : g ∈ B)
    (hg1 : g ≠ 1) (hgE : g ∉ E₀) : Nat.card ↥(E₀ ⊔ Subgroup.zpowers g) = p ^ 3 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime (hB.2 g hg) hg1
  have hzp : Nat.card (Subgroup.zpowers g) = p := by rw [Nat.card_zpowers, hord]
  have hN : Subgroup.zpowers g ≤ Subgroup.normalizer (E₀ : Set G) :=
    Subgroup.zpowers_le.2 (l95b_mem_normalizer hB hE₀B hg)
  have hinf : E₀ ⊓ Subgroup.zpowers g = ⊥ := by
    have hdvd : Nat.card ↥(E₀ ⊓ Subgroup.zpowers g) ∣ p := by
      rw [← hzp]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : E₀ ⊓ Subgroup.zpowers g = Subgroup.zpowers g :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (le_of_eq (by rw [hzp, h1]))
      have hg' : g ∈ E₀ ⊓ Subgroup.zpowers g := by
        rw [heq]
        exact Subgroup.mem_zpowers g
      exact hgE hg'.1
  have hcard := card_sup_mul_card_inf_of_le_normalizer hN
  rw [hinf, Subgroup.card_bot, hzp, hE₀, mul_one] at hcard
  rw [hcard]
  ring

private theorem l95b_isKGroup_of_le {C X : Subgroup G} (hC : CFSG.Open.IsKGroup ↥C)
    (hXC : X ≤ C) : CFSG.Open.IsKGroup ↥X :=
  CFSG.Open.IsKGroup.of_le hC hXC

private theorem l95b_pPrimeCore_quot {p : ℕ} (hp : p.Prime) {J : Subgroup G} :
    GLAPPrimeCore p (PQuot p J) = ⊥ :=
  CFSG.pPrimeCore_quotient_eq_bot hp

private theorem l95b_normal_zpowers {Q : Type} [Group Q] {w : Q} (hw : w ∈ Subgroup.center Q) :
    (Subgroup.zpowers w).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
  have hc : Commute g w := Subgroup.mem_center_iff.1 hw g
  rw [Subgroup.mem_zpowers_iff]
  exact ⟨k, by rw [(hc.zpow_right k).eq, mul_inv_cancel_right]⟩

private theorem l95b_center_pow {p : ℕ} (hp : p.Prime) {J : Subgroup G} :
    ∀ z ∈ Subgroup.center (PQuot p J), ∃ k : ℕ, z ^ (p ^ k) = 1 := by
  intro z hz
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e, n', hn', hzn⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos z).ne' p hp.one_lt.ne'
  have hw : orderOf (z ^ (p ^ e)) = n' := by
    rw [orderOf_pow' z (pow_ne_zero e hp.ne_zero), hzn,
      Nat.gcd_eq_right (dvd_mul_right _ _)]
    exact Nat.mul_div_cancel_left n' (pow_pos hp.pos e)
  have hwz : z ^ (p ^ e) ∈ Subgroup.center (PQuot p J) := Subgroup.pow_mem _ hz _
  have hcop : Nat.Coprime p (Nat.card (Subgroup.zpowers (z ^ (p ^ e)))) := by
    rw [Nat.card_zpowers, hw]
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 hn'
  have hmem : Subgroup.zpowers (z ^ (p ^ e)) ∈
      {K : Subgroup (PQuot p J) | K.Normal ∧ Nat.Coprime p (Nat.card K)} :=
    ⟨l95b_normal_zpowers hwz, hcop⟩
  have hle : Subgroup.zpowers (z ^ (p ^ e)) ≤ GLAPPrimeCore p (PQuot p J) := le_sSup hmem
  rw [l95b_pPrimeCore_quot hp, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact ⟨e, hle⟩

private theorem l95b_center_le_pCore {p : ℕ} (hp : p.Prime) {J : Subgroup G} :
    Subgroup.center (PQuot p J) ≤ CFSG.pCore p (PQuot p J) := by
  have hmem : Subgroup.center (PQuot p J) ∈
      {K : Subgroup (PQuot p J) | K.Normal ∧ IsPGroup p K} := by
    refine ⟨inferInstance, fun g => ?_⟩
    obtain ⟨k, hk⟩ := l95b_center_pow hp (g : PQuot p J) g.2
    exact ⟨k, Subtype.ext hk⟩
  exact le_sSup hmem

private theorem l95b_mem_oPPrimeP {p : ℕ} {J : Subgroup G} (c : ↥J)
    (hc : (QuotientGroup.mk c : PQuot p J) ∈ CFSG.pCore p (PQuot p J)) :
    (c : G) ∈ oPPrimeP p J := by
  unfold oPPrimeP
  exact Subgroup.mem_map.2 ⟨c, Subgroup.mem_comap.2 hc, rfl⟩

private theorem l95b_dvd_card_pQuot {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) : p ∣ Nat.card (PQuot p J) := by
  by_contra hdvd
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Nontrivial (PQuot p J) :=
    isQuasisimple_nontrivial (isQuasisimple_pQuot_of_glaPComponent hp hJ)
  have hcard : Nat.card ↥J = Nat.card (PQuot p J) * Nat.card ↥(GLAPPrimeCore p ↥J) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hcop : Nat.Coprime p (Nat.card ↥J) := by
    rw [hcard]
    exact Nat.Coprime.mul_right ((Nat.Prime.coprime_iff_not_dvd hp).2 hdvd)
      CFSG.pPrimeCore_coprime_card
  have hmem : (⊤ : Subgroup ↥J) ∈ {K : Subgroup ↥J | K.Normal ∧ Nat.Coprime p (Nat.card K)} := by
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_top]
    exact hcop
  have htop : GLAPPrimeCore p ↥J = ⊤ := top_le_iff.1 (le_sSup hmem)
  have hsub : Subsingleton (PQuot p J) := by
    refine ⟨fun a b => ?_⟩
    induction a using QuotientGroup.induction_on
    induction b using QuotientGroup.induction_on
    exact QuotientGroup.eq.2 (by rw [htop]; exact Subgroup.mem_top _)
  exact not_subsingleton (PQuot p J) hsub

private theorem l95b_eq_of_image_top {p : ℕ} (hp : p.Prime) {X J : Subgroup G}
    (hJ : GLAPComponent p X J) {N : Subgroup G} (hNJ : N ≤ J) (hNn : (N.subgroupOf J).Normal)
    (htop : (N.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) = ⊤) : N = J := by
  by_contra hne
  obtain ⟨hJX, hJsn, -, hmin⟩ := hJ
  have hlt : N < J := lt_of_le_of_ne hNJ hne
  have hsub : IsSubnormal N X := IsSubnormal.step hNJ hNn hJsn
  refine hmin N hlt hsub (le_antisymm ?_ ?_)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨x, Subgroup.mem_subgroupOf.2 (hNJ (Subgroup.mem_subgroupOf.1 hx)), rfl⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hxJ : (x : G) ∈ J := Subgroup.mem_subgroupOf.1 hx
    have hx'top : QuotientGroup.mk' (GLAPPrimeCore p ↥J) (⟨x, hxJ⟩ : ↥J) ∈
        (N.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 hx'top
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnx
    have hoX : (((n⁻¹ * (⟨x, hxJ⟩ : ↥J) : ↥J) : G)) ∈ GLAPPrimeCoreOf p J :=
      Subgroup.mem_map.2 ⟨_, hnx, rfl⟩
    have hoX' : (((n⁻¹ * (⟨x, hxJ⟩ : ↥J) : ↥J) : G)) ∈ GLAPPrimeCoreOf p X :=
      glaPPrimeCoreOf_le_of_isSubnormal hp hJsn hoX
    obtain ⟨oX, hoXmem, hoXv⟩ := Subgroup.mem_map.1 hoX'
    have hoXv' : ((oX : ↥X) : G) = ((n⁻¹ * (⟨x, hxJ⟩ : ↥J) : ↥J) : G) := hoXv
    have hnX : (n : G) ∈ N := Subgroup.mem_subgroupOf.1 hn
    refine Subgroup.mem_map.2 ⟨⟨(n : G), hJX (n.2)⟩, Subgroup.mem_subgroupOf.2 hnX, ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hgoal : (⟨(n : G), hJX n.2⟩ : ↥X)⁻¹ * x = oX := by
      apply Subtype.ext
      rw [hoXv']
      simp
    rw [hgoal]
    exact hoXmem

theorem exists_E_containing_x {p : ℕ} (hp : p.Prime) (hLB : LBalanceAt G p) {B : Subgroup G} {x : G}
    {L : Subgroup G} (h : H92 p B x L) (hX : CFSG.Open.IsKGroup ↥(cx x)) (hGB : IsGB p B L) :
    ∃ E : Subgroup G, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ x ∈ E ∧
      GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≠ ⊥ := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEB, hEel, hEcard, hEN, hne⟩ := hGB
  by_cases hxE : x ∈ E
  · exact ⟨E, hEB, hEel, hEcard, hxE, hne⟩
  have hB : IsElemAbelian p B := h.bmax.1
  have hxB : x ∈ B := h.mem
  have hx1 : x ≠ 1 := h.ne_one
  have hLx : L ≤ cx x := h.comp.1
  obtain ⟨K₀, hK₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E) p (n := 2)
    ⟨p, by rw [hEcard]; ring⟩
  obtain ⟨E₀, hE₀def⟩ : ∃ E₀ : Subgroup G, E₀ = K₀.map E.subtype := ⟨_, rfl⟩
  have hE₀E : E₀ ≤ E := by
    rw [hE₀def]
    exact Subgroup.map_subtype_le _
  have hE₀B : E₀ ≤ B := hE₀E.trans hEB
  have hE₀card : Nat.card E₀ = p ^ 2 := by
    rw [hE₀def, Subgroup.card_map_of_injective E.subtype_injective]
    exact hK₀
  have hlt : E₀ < E := by
    refine lt_of_le_of_ne hE₀E (fun heq => ?_)
    have h3 : Nat.card E₀ = Nat.card E := by rw [heq]
    rw [hE₀card, hEcard] at h3
    have h4 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    exact (ne_of_lt h4) h3
  obtain ⟨e, heE, heE₀⟩ := SetLike.exists_of_lt hlt
  have he1 : e ≠ 1 := fun h1 => heE₀ (by rw [h1]; exact E₀.one_mem)
  have heB : e ∈ B := hEB heE
  have hE' : E₀ ⊔ Subgroup.zpowers e = E := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le hE₀E (Subgroup.zpowers_le.2 heE)) ?_
    exact le_of_eq (by rw [l95b_card_sup_zpowers hp hEel hE₀E hE₀card heE he1 heE₀, hEcard])
  have hxE₀ : x ∉ E₀ := fun h' => hxE (hE₀E h')
  have hzeN : Subgroup.zpowers e ≤ Subgroup.normalizer (E₀ : Set G) :=
    Subgroup.zpowers_le.2 (l95b_mem_normalizer hEel hE₀E heE)
  have hzxN : Subgroup.zpowers x ≤ Subgroup.normalizer (E₀ : Set G) :=
    Subgroup.zpowers_le.2 (l95b_mem_normalizer hB hE₀B hxB)
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = L ⊓ Subgroup.centralizer (E₀ : Set G) := ⟨_, rfl⟩
  have hYL : Y ≤ L := by
    rw [hY]
    exact inf_le_left
  have hYx : Y ≤ cx x := hYL.trans hLx
  have hCE : L ⊓ Subgroup.centralizer (E : Set G) = Y ⊓ Subgroup.centralizer ({e} : Set G) := by
    rw [hY, ← hE', l95b_centralizer_sup_zpowers hzeN, inf_assoc]
  have hCE₁ : L ⊓ Subgroup.centralizer ((E₀ ⊔ Subgroup.zpowers x : Subgroup G) : Set G) = Y := by
    rw [l95b_centralizer_sup_zpowers hzxN, ← inf_assoc, ← hY]
    exact inf_eq_left.2 hYx
  obtain ⟨X, hXdef⟩ : ∃ X : Subgroup G, X = Y ⊔ Subgroup.zpowers e := ⟨_, rfl⟩
  have hYX : Y ≤ X := by
    rw [hXdef]
    exact le_sup_left
  have hzX : Subgroup.zpowers e ≤ X := by
    rw [hXdef]
    exact le_sup_right
  have heNY : e ∈ Subgroup.normalizer (Y : Set G) := by
    rw [hY]
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨hEN heE, l95b_normalizer_centralizer (S := (E₀ : Set G))
        (fun s hs => isElemAbelian_commute hEel heE (hE₀E hs))⟩
  have hzNY : Subgroup.zpowers e ≤ Subgroup.normalizer (Y : Set G) :=
    Subgroup.zpowers_le.2 heNY
  have hXN : X ≤ Subgroup.normalizer (Y : Set G) := by
    rw [hXdef]
    exact sup_le Subgroup.le_normalizer hzNY
  have hXC : X ≤ cx x := by
    rw [hXdef]
    exact sup_le hYx (Subgroup.zpowers_le.2
      (Subgroup.mem_centralizer_singleton_iff.2 (isElemAbelian_commute hB hxB heB).symm))
  have hIK : CFSG.Open.IsKGroup ↥X := l95b_isKGroup_of_le hX hXC
  have hXpow : IsPGroup p (Subgroup.zpowers e) := isPGroup_zpowers_of_mem hEel heE
  have hbal : GLAPLayer p (X ⊓ Subgroup.centralizer ({e} : Set G)) ≤ GLAPLayer p X := by
    have h0 := hLB X (Subgroup.zpowers e) hIK hzX hXpow
    rwa [S3.centralizer_zpowers] at h0
  have hYXsub : IsSubnormal Y X :=
    IsSubnormal.step hYX ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).2 hXN)
      (IsSubnormal.refl X)
  have hsub : IsSubnormal (L ⊓ Subgroup.centralizer (E : Set G))
      (X ⊓ Subgroup.centralizer ({e} : Set G)) := by
    rw [hCE]
    exact isSubnormal_inf hYXsub _
  have hcompA : ∀ K : Subgroup G, GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) K →
      K ≤ GLAPLayer p (X ⊓ Subgroup.centralizer ({e} : Set G)) :=
    fun K hK => le_sSup (glaPComponent_of_isSubnormal' hp hsub hK)
  have hXY : GLAPLayer p X ≤ GLAPLayer p Y := by
    refine sSup_le fun J hJ => ?_
    have hJX : J ≤ Y ⊔ Subgroup.zpowers e := hJ.1.trans (le_of_eq hXdef)
    have hJY : J ≤ Y :=
      chevTools_perfect_le_of_sup hp hzNY hXpow hJX (glaPComponent_perfect hJ)
    exact le_sSup (glaPComponent_of_le hp hJ hJY hYX)
  have hkey : GLAPLayer p (L ⊓ Subgroup.centralizer (E : Set G)) ≤ GLAPLayer p Y :=
    sSup_le fun K hK => (hcompA K hK).trans (hbal.trans hXY)
  refine ⟨E₀ ⊔ Subgroup.zpowers x, sup_le hE₀B (Subgroup.zpowers_le.2 hxB),
    isElemAbelian_mono hB (sup_le hE₀B (Subgroup.zpowers_le.2 hxB)),
    l95b_card_sup_zpowers hp hB hE₀B hE₀card hxB hx1 hxE₀,
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x), ?_⟩
  rw [hCE₁]
  intro h0
  exact hne (le_bot_iff.1 (hkey.trans h0.le))

structure EJ95 (p : ℕ) (B : Subgroup G) (x : G) (L E J : Subgroup G) : Prop where
  le : E ≤ B
  el : IsElemAbelian p E
  card : Nat.card E = p ^ 3
  mem : x ∈ E
  comp : GLAPComponent p (L ⊓ Subgroup.centralizer (E : Set G)) J
  not_L2 : p = 3 → catalogIs (PSimple p L) (fun i => isU6two i ∨ isF4two i ∨ isTE6two i) →
    ¬ catalogIs (PSimple p J) isL2prime

theorem exists_EJ {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G} (hc : S9Ctx G p)
    (hin : Lemma95Inputs G p) (hC : Contra92 p B x L q Q₁) (hGB : IsGB p B L) :
    ∃ E J : Subgroup G, EJ95 p B x L E J := by
  have hp : p.Prime := hc.ctx.prime
  have hX : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc hC.h.ne_one
  by_cases hex : p = 3 ∧ catalogIs (PSimple p L) (fun i => isU6two i ∨ isF4two i ∨ isTE6two i)
  · obtain ⟨hp3, hcat⟩ := hex
    subst hp3
    obtain ⟨E, hEB, hEel, hEcard, hCE, J, hJ, hJL2⟩ := hin.i2610 (cx x) L B x hX hC.h.comp hcat
      hC.h.bmax.1 hC.h.norm hC.h.ne_one hC.h.inf_centMod_eq hGB
    refine ⟨E, J, ⟨hEB, hEel, hEcard, ?_, hJ, fun _ _ => hJL2⟩⟩
    refine hCE ?_
    rw [hC.h.inf_centMod_eq]
    exact Subgroup.mem_zpowers x
  · obtain ⟨E, hEB, hEel, hEcard, hxE, hne⟩ := exists_E_containing_x hp hin.lbal hC.h hX hGB
    obtain ⟨J, hJ⟩ := (S3.glaPLayer_ne_bot_iff hp).1 hne
    exact ⟨E, J, ⟨hEB, hEel, hEcard, hxE, hJ, fun h3 hcat => absurd ⟨h3, hcat⟩ hex⟩⟩

theorem inf_oPPrimeP_le {p : ℕ} (hp : p.Prime) {J L : Subgroup G} (hJL : J ≤ L) :
    J ⊓ oPPrimeP p L ≤ oPPrimeP p J :=
  CFSG.LocalAnalysis.GLTheoremA.inf_oPPrimeP_le hp hJL

theorem residual_of_component {p : ℕ} (hp : p.Prime) {X J : Subgroup G} (hJ : GLAPComponent p X J) :
    ∀ N : Subgroup G, N ≤ J → (N.subgroupOf J).Normal → Nat.Coprime p (N.subgroupOf J).index → N = J := by
  intro N hNJ hNn hidx
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hfs : Function.Surjective (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) :=
    QuotientGroup.mk'_surjective _
  have hMn : ((N.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J))).Normal :=
    hNn.map _ hfs
  by_cases htop : (N.subgroupOf J).map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) = ⊤
  · exact l95b_eq_of_image_top hp hJ hNJ hNn htop
  · exfalso
    have hle := le_center_of_normal_of_isQuasisimple hQ hMn htop
    have hdvdi : (Subgroup.center (PQuot p J)).index ∣ (N.subgroupOf J).index :=
      (Subgroup.index_dvd_of_le hle).trans (Subgroup.index_map_dvd (N.subgroupOf J) hfs)
    have hcop : Nat.Coprime p (Subgroup.center (PQuot p J)).index :=
      Nat.Coprime.coprime_dvd_right hdvdi hidx
    have hdvd := Subgroup.card_commutator_dvd_index_center_pow (PQuot p J)
    rw [hQ.1, Subgroup.card_top] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hcop
      (hp.dvd_of_dvd_pow ((l95b_dvd_card_pQuot hp hJ).trans hdvd))

theorem inf_centralizer_le_oPPrimeP {p : ℕ} (hp : p.Prime) {X J Q : Subgroup G} (hJ : GLAPComponent p X J)
    (hQJ : J ≤ Subgroup.normalizer (Q : Set G)) (hne : ¬ J ≤ Subgroup.centralizer (Q : Set G)) :
    J ⊓ Subgroup.centralizer (Q : Set G) ≤ oPPrimeP p J := by
  have hconj : ∀ j ∈ J, ∀ c ∈ J ⊓ Subgroup.centralizer (Q : Set G),
      j * c * j⁻¹ ∈ J ⊓ Subgroup.centralizer (Q : Set G) := by
    intro j hj c hc
    obtain ⟨hcJ, hcQ⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨J.mul_mem (J.mul_mem hj hcJ) (J.inv_mem hj), ?_⟩
    rw [Subgroup.mem_centralizer_iff] at hcQ ⊢
    intro q hq
    have hq' : j⁻¹ * q * j ∈ (Q : Set G) := by
      have hiff := Subgroup.mem_normalizer_iff.1 (hQJ hj) (j⁻¹ * q * j)
      have e : j * (j⁻¹ * q * j) * j⁻¹ = q := by group
      rw [e] at hiff
      exact hiff.2 hq
    have hqc := hcQ _ hq'
    calc q * (j * c * j⁻¹) = (j * (j⁻¹ * q * j) * j⁻¹) * (j * c * j⁻¹) := by group
      _ = j * ((j⁻¹ * q * j) * c) * j⁻¹ := by group
      _ = j * (c * (j⁻¹ * q * j)) * j⁻¹ := by rw [hqc]
      _ = (j * c * j⁻¹) * (j * (j⁻¹ * q * j) * j⁻¹) := by group
      _ = (j * c * j⁻¹) * q := by
        congr 1
        group
  have hJN : J ≤ Subgroup.normalizer ((J ⊓ Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
    intro j hj
    rw [Subgroup.mem_normalizer_iff]
    intro c
    constructor
    · exact hconj j hj c
    · intro hc
      have h2 := hconj j⁻¹ (J.inv_mem hj) _ hc
      have e : j⁻¹ * (j * c * j⁻¹) * j⁻¹⁻¹ = c := by group
      rw [e] at h2
      exact h2
  have hCJ : J ⊓ Subgroup.centralizer (Q : Set G) ≤ J := inf_le_left
  have hCn : ((J ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCJ).2 hJN
  by_cases htop : ((J ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf J).map
      (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) = ⊤
  ·
    exfalso
    apply hne
    have hCeq : J ⊓ Subgroup.centralizer (Q : Set G) = J :=
      l95b_eq_of_image_top hp hJ hCJ hCn htop
    intro j hj
    have hj' : j ∈ J ⊓ Subgroup.centralizer (Q : Set G) := by
      rw [hCeq]
      exact hj
    exact hj'.2
  ·
    intro c hc
    have hcJ : c ∈ J := (inf_le_left : J ⊓ Subgroup.centralizer (Q : Set G) ≤ J) hc
    have hle := le_center_of_normal_of_isQuasisimple (isQuasisimple_pQuot_of_glaPComponent hp hJ)
      (hCn.map (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) (QuotientGroup.mk'_surjective _)) htop
    have hmem : (QuotientGroup.mk (⟨c, hcJ⟩ : ↥J) : PQuot p J) ∈
        ((J ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf J).map
          (QuotientGroup.mk' (GLAPPrimeCore p ↥J)) :=
      Subgroup.mem_map.2 ⟨⟨c, hcJ⟩, Subgroup.mem_subgroupOf.2 hc, rfl⟩
    exact l95b_mem_oPPrimeP ⟨c, hcJ⟩ (l95b_center_le_pCore hp (hle hmem))

theorem exists_D {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J : Subgroup G} (hc : S9Ctx G p)
    (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J) :
    ∃ D : Subgroup G, D ≤ E ∧ Nat.card D = p ^ 2 ∧
      (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≠ ⊥ := by
  have hp : p.Prime := hc.ctx.prime
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hC.setup.prime⟩
  by_contra hcon
  push Not at hcon
  have hJL : J ≤ L := hE.comp.1.trans inf_le_left
  have hEQ : E ≤ Subgroup.normalizer (Q₁ : Set G) :=
    fun e he => hC.setup.char (hC.h.norm (hE.le he))
  have hQ₁p : ¬ p ∣ Nat.card Q₁ := by
    have hQg : IsPGroup q Q₁ := fun g => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (hC.setup.exp g g.2)⟩
    obtain ⟨n, hn⟩ := hQg.exists_card_eq
    rw [hn]
    intro hdvd
    exact hC.setup.ne_p ((Nat.prime_dvd_prime_iff_eq hp hC.setup.prime).1
      (hp.dvd_of_dvd_pow hdvd)).symm
  haveI : Nontrivial ↥E := by
    rw [← Finite.one_lt_card_iff_nontrivial, hE.card]
    exact Nat.one_lt_pow (by norm_num) hp.one_lt
  have hgen := le_iSup_inf_centralizer_hyperplane (p := p) hE.el hEQ hQ₁p
  have hJC : J ≤ Subgroup.centralizer (Q₁ : Set G) := by
    rw [Subgroup.le_centralizer_iff]
    refine hgen.trans (iSup₂_le fun K hK => ?_)
    have hcard := card_of_index_eq hp hK.1 hE.card hK.2
    have h0 := hcon K hK.1 hcard
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 h0
  have h1 : J ≤ oPPrimeP p J := by
    intro g hg
    have : g ∈ J ⊓ oPPrimeP p L :=
      ⟨hg, hC.setup.cent ⟨hJL hg, hJC hg⟩⟩
    exact inf_oPPrimeP_le hp hJL this
  exact (pComponent_basic hp hE.comp).2.1 h1


theorem Contra92.coprime_card_of_le {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ : Subgroup G}
    (hC : Contra92 p B x L q Q₁) (hp : p.Prime) {A : Subgroup G} (hA : A ≤ Q₁) :
    Nat.Coprime p (Nat.card A) := by
  haveI : Fact q.Prime := ⟨hC.setup.prime⟩
  have hQg : IsPGroup q Q₁ := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hC.setup.exp g g.2)⟩
  obtain ⟨n, hn⟩ := (hQg.to_le hA).exists_card_eq
  rw [hn]
  exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp hC.setup.prime).2 (Ne.symm hC.setup.ne_p))

theorem EJ95.le_L {p : ℕ} {B : Subgroup G} {x : G} {L E J : Subgroup G} (hE : EJ95 p B x L E J) :
    J ≤ L := hE.comp.1.trans inf_le_left

theorem EJ95.le_centralizer {p : ℕ} {B : Subgroup G} {x : G} {L E J : Subgroup G}
    (hE : EJ95 p B x L E J) : J ≤ Subgroup.centralizer (E : Set G) :=
  hE.comp.1.trans inf_le_right

theorem J_le_normalizer_A {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D : Subgroup G}
    (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J) (hDE : D ≤ E) :
    J ≤ Subgroup.normalizer ((Q₁ ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) : Set G) := by
  have hJD : J ≤ Subgroup.centralizer (D : Set G) :=
    hE.le_centralizer.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hDE))
  have hJQ₁ : J ≤ Subgroup.normalizer (Q₁ : Set G) :=
    fun j hj => hC.setup.char (Subgroup.le_normalizer (hE.le_L hj))
  exact fun j hj => Subgroup.inf_normalizer_le_normalizer_inf
    ⟨hJQ₁ hj, Subgroup.le_normalizer (hJD hj)⟩

theorem Q₂_le_A {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D : Subgroup G}
    (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J) (hDE : D ≤ E) :
    (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≤
      Q₁ ⊓ Subgroup.centralizer (D : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (J_le_normalizer_A hC hE hDE)

theorem J_le_normalizer_Q₂ {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D : Subgroup G}
    (hC : Contra92 p B x L q Q₁) (hE : EJ95 p B x L E J) (hDE : D ≤ E) :
    J ≤ Subgroup.normalizer
      ((⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) : Set G) :=
  le_normalizer_commutator (J_le_normalizer_A hC hE hDE) Subgroup.le_normalizer

theorem Q₂_comm_self {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D : Subgroup G}
    (hc : S9Ctx G p) (hin : Lemma95Inputs G p) (hC : Contra92 p B x L q Q₁)
    (hE : EJ95 p B x L E J) (hDE : D ≤ E) :
    (⁅⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆, J⁆ : Subgroup G) =
      ⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ :=
  hin.i321 hc.ctx.prime _ J (hC.coprime_card_of_le hc.ctx.prime inf_le_left)
    (J_le_normalizer_A hC hE hDE) (residual_of_component hc.ctx.prime hE.comp)

theorem three_le_pRank_Q₂ {p q : ℕ} {B : Subgroup G} {x : G} {L Q₁ E J D : Subgroup G}
    (hc : S9Ctx G p) (hin : Lemma95Inputs G p) (hC : Contra92 p B x L q Q₁) (hGB : IsGB p B L)
    (hE : EJ95 p B x L E J) (hDE : D ≤ E)
    (hne : (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) ≠ ⊥) :
    3 ≤ CFSG.Open.pRank q (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) := by
  by_contra hlt
  push Not at hlt
  have hp : p.Prime := hc.ctx.prime
  have hp2 : p ≠ 2 := hc.ctx.odd
  have hq : q.Prime := hC.setup.prime
  have hq2 : q ≠ 2 := hC.setup.ne_two
  have hX : CFSG.Open.IsKGroup ↥(cx x) := isKGroup_cx hc hC.h.ne_one
  have hQ₂A := Q₂_le_A hC hE hDE
  have hQ₂N := J_le_normalizer_Q₂ hC hE hDE
  have hQ₂J := Q₂_comm_self hc hin hC hE hDE
  have hnc : ¬ J ≤ Subgroup.centralizer
      ((⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G) : Set G) := by
    intro hJc
    apply hne
    have h0 : (⁅⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆, J⁆ : Subgroup G) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (Subgroup.le_centralizer_iff.1 hJc)
    rw [hQ₂J] at h0
    exact h0
  have hCJ := inf_centralizer_le_oPPrimeP hp hE.comp hQ₂N hnc
  have hexp : ∀ g ∈ (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G), g ^ q = 1 :=
    fun g hg => hC.setup.exp g (hQ₂A hg).1
  have hcl : ∀ a ∈ (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G),
      ∀ b ∈ (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G),
      ∀ c ∈ (⁅Q₁ ⊓ Subgroup.centralizer (D : Set G), J⁆ : Subgroup G), ⁅a, b⁆ * c = c * ⁅a, b⁆ :=
    fun a ha b hb c hc' => hC.setup.class_two a (hQ₂A ha).1 b (hQ₂A hb).1 c (hQ₂A hc').1
  have hidx := index_commutator_le_of_pRank_le_two hq hq2 hexp hcl (by omega)
  obtain ⟨φ, hφ⟩ := exists_hom_GL2 hp hq hq2 hE.comp hexp hQ₂N hidx hCJ
  have hevenJ := even_core_of_hom hp hp2 hq hq2 hE.comp φ hφ
  have hinvJ := involvedSL2_of_hom hp hE.comp φ hφ
  have hodd141 := hin.i141 hp hp2 (cx x) L E J hX hC.h.comp hC.h.chev2 hE.el
    (fun e he => hC.h.norm (hE.le he)) hE.comp
  have hevenL : Even (Nat.card (GLAPPrimeCoreOf p L)) := by
    have h1 := Subgroup.relIndex_mul_card (H := GLAPPrimeCoreOf p L) (K := GLAPPrimeCoreOf p J)
    rw [← h1] at hevenJ
    have h2 : Even (Nat.card ↥(GLAPPrimeCoreOf p L ⊓ GLAPPrimeCoreOf p J)) := by
      rcases Nat.even_mul.1 hevenJ with h | h
      · exact absurd h (Nat.not_even_iff_odd.2 hodd141)
      · exact h
    have hdvd : Nat.card ↥(GLAPPrimeCoreOf p L ⊓ GLAPPrimeCoreOf p J) ∣
        Nat.card ↥(GLAPPrimeCoreOf p L) := Subgroup.card_dvd_of_le inf_le_left
    exact even_iff_two_dvd.2 (dvd_trans (even_iff_two_dvd.1 h2) hdvd)
  have h67 := hin.i67 hp hp2 (cx x) L B hX hC.h.comp hC.h.chev2 hevenL hC.odd hC.h.bmax.1 hC.h.norm
    (hC.h.pow_three_mul_le hc)
  have hp3 : p = 3 := hin.rank3 p (cx x) L B hp hp2 hC.h.comp hC.h.bmax.1 hC.h.norm
    (hC.h.pow_three_mul_le hc) h67
  subst hp3
  have hXJ : CFSG.Open.IsKGroup ↥(L ⊓ Subgroup.centralizer (E : Set G)) :=
    isKGroup_of_le_cx hc hC.h.ne_one (inf_le_left.trans hC.h.comp.1)
  obtain ⟨i, hi, f⟩ := h67
  rcases hi with hi | hi | hi | hi | hi | hi
  · exact notIsGB_of_I269 hc hin.lbal hin.i269 hC.h ⟨i, Or.inl hi, f⟩ hGB
  · exact notIsGB_of_I269 hc hin.lbal hin.i269 hC.h ⟨i, Or.inr (Or.inr (Or.inl hi)), f⟩ hGB
  · exact hE.not_L2 rfl ⟨i, Or.inr (Or.inl hi), f⟩
      (hin.dickson 3 q _ J hp hq hq2 hXJ hE.comp hinvJ)
  · exact notIsGB_of_I269 hc hin.lbal hin.i269 hC.h ⟨i, Or.inr (Or.inl hi), f⟩ hGB
  · exact hE.not_L2 rfl ⟨i, Or.inl hi, f⟩ (hin.dickson 3 q _ J hp hq hq2 hXJ hE.comp hinvJ)
  · exact hE.not_L2 rfl ⟨i, Or.inr (Or.inr hi), f⟩
      (hin.dickson 3 q _ J hp hq hq2 hXJ hE.comp hinvJ)

end CFSG.LocalAnalysis.GLTheoremA.S9
