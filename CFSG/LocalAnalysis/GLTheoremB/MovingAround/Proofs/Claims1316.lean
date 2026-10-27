module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1316
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.GH74.GLS.Stage2.Signalizer.L53Embed
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsOuterCent

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1316

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (IsEkIn)
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut innerAut)
open CFSG.GH74.GLS.Bg (kLowInfty Kfam Klow Kup classTwo gen zOf)
open scoped commutatorElement

@[expose] def GlaubermanTransfer : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ∀ S : Subgroup G, IsSylowIn p ⊤ S →
    CFSG.GH74.GLS.oResidual p ↥(Subgroup.normalizer ((kLowInfty S : Subgroup G) : Set G)) ≠ ⊤ →
      CFSG.GH74.GLS.oResidual p G ≠ ⊤

section KInfty

variable {G : Type} [Group G]

theorem Kfam_le (P : Subgroup G) : ∀ (n : ℕ), ∀ B ∈ Kfam P n, B ≤ P
  | 0, _, hB => hB.1
  | n + 1, B, hB => by
    have hB' : B ∈ (if Even n then Klow P (gen (Kfam P n)) else Kup P (gen (Kfam P n))) := hB
    split_ifs at hB'
    · exact hB'.1.1
    · exact hB'.1.1

theorem kLowInfty_le (P : Subgroup G) : kLowInfty P ≤ P := by
  show Subgroup.closure (⋃ B ∈ (⋃ i : ℕ, Kfam P (2 * i + 1)), (B : Set G)) ≤ P
  rw [Subgroup.closure_le]
  intro x hx
  obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hB
  exact Kfam_le P _ B hi hxB

theorem mem_Kfam_one {P N : Subgroup G} (hNP : N ≤ P)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hnorm : P ≤ Subgroup.normalizer (N : Set G)) :
    N ∈ Kfam P 1 := by
  have hNc : N ≤ Subgroup.centralizer (N : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.2 fun b hb => hcomm b hb a ha
  have hNN : ⁅N, N⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hNc
  have hcl : N ∈ classTwo P := ⟨hNP, by rw [hNN, Subgroup.commutator_bot_left]⟩
  have hgen : gen (Kfam P 0) ≤ P := by
    show Subgroup.closure (⋃ B ∈ classTwo P, (B : Set G)) ≤ P
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨B, hB, hxB⟩ := Set.mem_iUnion₂.1 hx
    exact hB.1 hxB
  show N ∈ (if Even 0 then Klow P (gen (Kfam P 0)) else Kup P (gen (Kfam P 0)))
  rw [if_pos (by decide : Even 0)]
  refine ⟨hcl, hgen.trans hnorm, fun A hA _ _ _ _ => ?_⟩
  rw [Subgroup.commutator_le]
  intro n hn a ha
  have haN : a ∈ Subgroup.normalizer (N : Set G) := hnorm (hA.1 ha)
  have hmem : ⁅n, a⁆ ∈ N := by
    rw [commutatorElement_def]
    have h1 : a * n⁻¹ * a⁻¹ ∈ N := (Subgroup.mem_set_normalizer_iff.1 haN n⁻¹).1 (N.inv_mem hn)
    have e : n * a * n⁻¹ * a⁻¹ = n * (a * n⁻¹ * a⁻¹) := by group
    rw [e]
    exact N.mul_mem hn h1
  exact ⟨hmem, hNc hmem⟩

theorem le_kLowInfty {P N : Subgroup G} (h : N ∈ Kfam P 1) : N ≤ kLowInfty P := by
  intro x hx
  exact Subgroup.subset_closure (Set.mem_iUnion₂.2 ⟨N, Set.mem_iUnion.2 ⟨0, h⟩, hx⟩)

theorem map_conj_eq_of_mem_normalizer {P : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) : P.map (MulAut.conj x).toMonoidHom = P := by
  ext y
  constructor
  · rintro ⟨y', hy', rfl⟩
    exact (Subgroup.mem_set_normalizer_iff.1 hx y').1 hy'
  · intro hy
    refine ⟨x⁻¹ * y * x, ?_, ?_⟩
    · apply (Subgroup.mem_set_normalizer_iff.1 hx (x⁻¹ * y * x)).2
      have e : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
      rw [e]
      exact hy
    · show x * (x⁻¹ * y * x) * x⁻¹ = y
      group

theorem mem_normalizer_kLowInfty {P : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    x ∈ Subgroup.normalizer ((kLowInfty P : Subgroup G) : Set G) := by
  have hmap := CFSG.GH74.GLS.Stage2.Signalizer.L53.kLowInfty_map' (MulAut.conj x).toMonoidHom
    (MulAut.conj x).injective P
  rw [map_conj_eq_of_mem_normalizer hx] at hmap
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [SetLike.mem_coe, hmap]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [SetLike.mem_coe, hmap] at hy
    obtain ⟨y', hy', e⟩ := hy
    have e' : x * y' * x⁻¹ = x * y * x⁻¹ := e
    have hyy : y' = y := by simpa using e'
    rw [← hyy]
    exact hy'

end KInfty

section Generic

variable {G : Type} [Group G]

theorem mem_normalizer_inf {X Y : Subgroup G} {g : G} (hX : g ∈ Subgroup.normalizer (X : Set G))
    (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff] at hX hY ⊢
  intro n
  exact ⟨fun hn => ⟨(hX n).1 hn.1, (hY n).1 hn.2⟩, fun hn => ⟨(hX n).2 hn.1, (hY n).2 hn.2⟩⟩

theorem omegaOne_le (p : ℕ) (Y : Subgroup G) : omegaOne p Y ≤ Y :=
  (Subgroup.closure_le _).2 fun _ hx => hx.1

theorem centerOf_le (R : Subgroup G) : centerOf R ≤ R := Subgroup.map_subtype_le _

theorem comm_of_mem_centerOf {R : Subgroup G} {c r : G} (hc : c ∈ centerOf R) (hr : r ∈ R) :
    r * c = c * r := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hc
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ht ⟨r, hr⟩)

theorem centerOf_comm {R : Subgroup G} : ∀ a ∈ centerOf R, ∀ b ∈ centerOf R, a * b = b * a :=
  fun _ ha _ hb => comm_of_mem_centerOf hb (centerOf_le R ha)

theorem le_normalizer_centerOf (R : Subgroup G) :
    R ≤ Subgroup.normalizer ((centerOf R : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.mem_set_normalizer_iff]
  intro c
  have hconj : ∀ c ∈ centerOf R, r * c * r⁻¹ = c := fun c hc => by
    rw [comm_of_mem_centerOf hc hr, mul_inv_cancel_right]
  constructor
  · intro hc
    rw [hconj c hc]
    exact hc
  · intro hc
    have hcomm := comm_of_mem_centerOf hc (R.inv_mem hr)
    have e : c = r * c * r⁻¹ := by
      calc c = r⁻¹ * (r * c * r⁻¹) * r := by group
        _ = (r * c * r⁻¹) * r⁻¹ * r := by rw [hcomm]
        _ = r * c * r⁻¹ := by group
    rw [SetLike.mem_coe, e]
    exact hc

theorem centerOf_le_kLowInfty (P : Subgroup G) : centerOf P ≤ kLowInfty P :=
  le_kLowInfty (mem_Kfam_one (centerOf_le P) centerOf_comm (le_normalizer_centerOf P))

theorem mem_commutator_of_oResidual_eq_top {X : Type*} [Group X] {p : ℕ}
    (htop : CFSG.GH74.GLS.oResidual p X = ⊤) {x : X} {k : ℕ} (hx : x ^ (p ^ k) = 1) :
    x ∈ commutator X := by
  let S : Subgroup (Abelianization X) :=
    { carrier := {a | Nat.Coprime (orderOf a) p}
      mul_mem' := fun {a b} ha hb =>
        Nat.Coprime.coprime_dvd_left (Commute.all a b).orderOf_mul_dvd_mul_orderOf
          (Nat.coprime_mul_iff_left.2 ⟨ha, hb⟩)
      one_mem' := by
        show Nat.Coprime (orderOf (1 : Abelianization X)) p
        rw [orderOf_one]
        exact Nat.coprime_one_left p
      inv_mem' := fun {a} ha => by
        show Nat.Coprime (orderOf a⁻¹) p
        rw [orderOf_inv]
        exact ha }
  have hle : CFSG.GH74.GLS.oResidual p X ≤ S.comap Abelianization.of := by
    show Subgroup.closure _ ≤ _
    rw [Subgroup.closure_le]
    intro y hy
    exact Nat.Coprime.coprime_dvd_left (orderOf_map_dvd Abelianization.of y) hy
  have hxS : Abelianization.of x ∈ S := hle (by rw [htop]; exact Subgroup.mem_top x)
  have hdvd : orderOf (Abelianization.of x) ∣ p ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have hc : Nat.Coprime (orderOf (Abelianization.of x)) p := hxS
  have h1 : orderOf (Abelianization.of x) = 1 := Nat.Coprime.eq_one_of_dvd (hc.pow_right k) hdvd
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  exact orderOf_eq_one_iff.1 h1

theorem le_commutator_of_oResidual_eq_top {X : Type*} [Group X] {p : ℕ}
    (htop : CFSG.GH74.GLS.oResidual p X = ⊤) {S : Subgroup X} (hS : IsPGroup p S) :
    S ≤ commutator X := by
  intro s hs
  obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
  refine mem_commutator_of_oResidual_eq_top htop (k := k) ?_
  have := congrArg Subtype.val hk
  simpa using this

theorem inducesInner_of_barAut_mem {p : ℕ} {L : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (L : Set G))
    (h : barAut p L ⟨x, hx⟩ ∈ innerAut (barOf p L)) : InducesInner p L x := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  have hkN : (k : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer k.2
  have hk : barAut p L ⟨k, hkN⟩ = MulAut.conj (QuotientGroup.mk k : barOf p L) := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.conj_apply,
        ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      rfl
  refine ⟨(k : G), k.2, ?_⟩
  show (k : G)⁻¹ * x ∈
    ((MonoidHom.ker (barAut p L)).map (Subgroup.normalizer (L : Set G)).subtype) ⊓ ⊤
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨(k : G)⁻¹ * x, (Subgroup.normalizer (L : Set G)).mul_mem
    ((Subgroup.normalizer (L : Set G)).inv_mem hkN) hx⟩, ?_, rfl⟩, Subgroup.mem_top _⟩
  rw [MonoidHom.mem_ker]
  have e : (⟨(k : G)⁻¹ * x, (Subgroup.normalizer (L : Set G)).mul_mem
      ((Subgroup.normalizer (L : Set G)).inv_mem hkN) hx⟩ : ↥(Subgroup.normalizer (L : Set G))) =
      (⟨k, hkN⟩ : ↥(Subgroup.normalizer (L : Set G)))⁻¹ * ⟨x, hx⟩ := rfl
  rw [e, map_mul, map_inv, hk, ← hq, inv_mul_cancel]

end Generic

section TransferControl

theorem eq_one_of_commutator_eq_top {Q : Type*} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime]
    (hQ : IsPGroup p Q) (h : commutator Q = ⊤) (q : Q) : q = 1 := by
  have hlcs : ∀ n, (⊤ : Subgroup Q).lowerCentralSeries n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [Subgroup.lowerCentralSeries_succ, ih, ← commutator_def, h]
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.1 hQ.isNilpotent
  have hq : q ∈ (⊤ : Subgroup Q).lowerCentralSeries n := by
    rw [hlcs n]
    exact Subgroup.mem_top q
  rw [hn, Subgroup.mem_bot] at hq
  exact hq

theorem isPGroup_quotient_oResidual {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    [(CFSG.GH74.GLS.oResidual p Y).Normal] : IsPGroup p (Y ⧸ CFSG.GH74.GLS.oResidual p Y) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H y =>
    have hn : orderOf y ≠ 0 := (orderOf_pos y).ne'
    obtain ⟨e, n', hn', hdec⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hp.ne_one
    refine ⟨e, ?_⟩
    have hpow : (y ^ p ^ e) ^ n' = 1 := by rw [← pow_mul, ← hdec, pow_orderOf_eq_one]
    have hdvd : orderOf (y ^ p ^ e) ∣ n' := orderOf_dvd_of_pow_eq_one hpow
    have hcop : Nat.Coprime n' p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hn').symm
    have hmem : y ^ p ^ e ∈ CFSG.GH74.GLS.oResidual p Y :=
      Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left hdvd hcop)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hmem

theorem oResidual_eq_top_of_sylow_le_commutator {Y : Type} [Group Y] [Finite Y] {p : ℕ}
    [hp : Fact p.Prime] (T : Sylow p Y) (hT : (T : Subgroup Y) ≤ commutator Y) :
    CFSG.GH74.GLS.oResidual p Y = ⊤ := by
  haveI : (CFSG.GH74.GLS.oResidual p Y).Normal := Lemma1316.oResidual_normal p Y
  have hQ : IsPGroup p (Y ⧸ CFSG.GH74.GLS.oResidual p Y) := isPGroup_quotient_oResidual hp.out
  have hf : Function.Surjective (QuotientGroup.mk' (CFSG.GH74.GLS.oResidual p Y)) :=
    QuotientGroup.mk'_surjective _
  have hTmap : (T : Subgroup Y).map (QuotientGroup.mk' (CFSG.GH74.GLS.oResidual p Y)) = ⊤ := by
    obtain ⟨n, hn⟩ := hQ.index ((T : Subgroup Y).map (QuotientGroup.mk' (CFSG.GH74.GLS.oResidual p Y)))
    have hdvd : p ^ n ∣ (T : Subgroup Y).index := by
      rw [← hn]
      exact Subgroup.index_map_dvd (T : Subgroup Y) hf
    rcases n with _ | n
    · rw [pow_zero] at hn
      exact Subgroup.index_eq_one.1 hn
    · exact absurd (dvd_trans (dvd_pow_self p n.succ_ne_zero) hdvd) T.not_dvd_index
  have hcomm : commutator (Y ⧸ CFSG.GH74.GLS.oResidual p Y) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← hTmap]
    refine (Subgroup.map_mono hT).trans ?_
    rw [commutator_def Y, Subgroup.map_commutator]
    exact Subgroup.commutator_mono le_top le_top
  rw [eq_top_iff]
  intro y _
  have h1 := eq_one_of_commutator_eq_top hQ hcomm
    (QuotientGroup.mk' (CFSG.GH74.GLS.oResidual p Y) y)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

@[expose] def sylowSubgroupOf {G : Type} [Group G] {p : ℕ} {S N : Subgroup G}
    (hS : IsSylowIn p ⊤ S) (hSN : S ≤ N) : Sylow p ↥N where
  toSubgroup := S.subgroupOf N
  isPGroup' := hS.2.1.comap_subtype
  is_maximal' := by
    intro Q hQ hle
    have hmap : Q.map N.subtype = S := by
      refine hS.2.2 _ le_top (hQ.map N.subtype) ?_
      intro s hs
      exact ⟨⟨s, hSN hs⟩, hle (Subgroup.mem_subgroupOf.2 hs), rfl⟩
    refine le_antisymm (fun q hq => ?_) hle
    rw [Subgroup.mem_subgroupOf, ← hmap]
    exact ⟨q, hq, rfl⟩

@[expose] def GlaubermanTransferControl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ), p.Prime → 5 ≤ p → ∀ S : Subgroup G, IsSylowIn p ⊤ S →
    S ⊓ commutator G =
      S ⊓ (commutator ↥(Subgroup.normalizer ((kLowInfty S : Subgroup G) : Set G))).map
        (Subgroup.normalizer ((kLowInfty S : Subgroup G) : Set G)).subtype

theorem glaubermanTransfer_of_control (hC : GlaubermanTransferControl) : GlaubermanTransfer := by
  intro G _ _ p hp hp5 S hS hN hG
  haveI : Fact p.Prime := ⟨hp⟩
  have hSN : S ≤ Subgroup.normalizer ((kLowInfty S : Subgroup G) : Set G) := fun s hs =>
    mem_normalizer_kLowInfty (Subgroup.le_normalizer hs)
  have hSG : S ≤ commutator G := le_commutator_of_oResidual_eq_top hG hS.2.1
  have hSN' : S ≤ (commutator ↥(Subgroup.normalizer ((kLowInfty S : Subgroup G) : Set G))).map
      (Subgroup.normalizer ((kLowInfty S : Subgroup G) : Set G)).subtype := by
    intro s hs
    have hmem : s ∈ S ⊓ commutator G := ⟨hs, hSG hs⟩
    rw [hC G p hp hp5 S hS] at hmem
    exact hmem.2
  apply hN
  refine oResidual_eq_top_of_sylow_le_commutator (sylowSubgroupOf hS hSN) ?_
  intro t ht
  obtain ⟨t', ht', e⟩ := hSN' (Subgroup.mem_subgroupOf.1 ht)
  have htt : t' = t := Subtype.ext e
  rw [← htt]
  exact ht'

end TransferControl

section OutL2

open CFSG.GorensteinWalter (IsOddPrimePower PSL2 mem_pGammaL2PSLRange_iff)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo (SemilinearQuotient diagonalHom
  quotientFieldProjection quotientFieldProjection_ker fieldAut_isCyclic outerEquivSemilinearQuotient)

theorem le_center_of_card_le_two {Q : Type*} [Group Q] {D : Subgroup Q} (hDn : D.Normal)
    (hD : Nat.card D = 1 ∨ Nat.card D = 2) : D ≤ Subgroup.center Q := by
  rcases hD with h1 | h2
  · rw [Subgroup.card_eq_one] at h1
    rw [h1]
    exact bot_le
  · intro t ht
    rw [Subgroup.mem_center_iff]
    intro g
    by_cases ht1 : t = 1
    · rw [ht1, mul_one, one_mul]
    have hconj : g * t * g⁻¹ ∈ D := hDn.conj_mem t ht g
    have hne : g * t * g⁻¹ ≠ 1 := fun h => ht1 (by
      have h' : t = g⁻¹ * (g * t * g⁻¹) * g := by group
      rw [h', h]
      group)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : D)).mp h2
    have hy1 : (⟨g * t * g⁻¹, hconj⟩ : D) = y := hy _ fun h => hne (congrArg Subtype.val h)
    have hy2 : (⟨t, ht⟩ : D) = y := hy _ fun h => ht1 (congrArg Subtype.val h)
    have hgt : g * t * g⁻¹ = t := congrArg Subtype.val (hy1.trans hy2.symm)
    calc g * t = g * t * g⁻¹ * g := by group
      _ = t * g := by rw [hgt]

theorem semilinearQuotient_comm (F : Type) [Field F] [Finite F] (hodd : IsOddPrimePower (Nat.card F))
    (a b : SemilinearQuotient F) : a * b = b * a := by
  have hker := quotientFieldProjection_ker F
  have hle : (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F)).range ≤
      (diagonalHom F).ker := by
    rintro _ ⟨y, rfl⟩
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (CFSG.GorensteinWalter.pGammaL2PSLRange F))
      (SemidirectProduct.inl (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (mem_pGammaL2PSLRange_iff F _).2 ⟨y, rfl⟩
  have hcard : Nat.card (diagonalHom F).range ∣ 2 := by
    rw [← Subgroup.index_ker (diagonalHom F)]
    exact (Subgroup.index_dvd_of_le hle).trans
      (dvd_of_eq (CFSG.ComponentClassification.AutL2Facts.index_psl2Range hodd))
  have hDn : ((diagonalHom F).range).Normal := by
    rw [← hker]
    infer_instance
  have hDc := le_center_of_card_le_two hDn ((Nat.dvd_prime Nat.prime_two).1 hcard)
  haveI : IsCyclic (F ≃+* F) := fieldAut_isCyclic F
  have hcomm := (quotientFieldProjection F).isMulCommutative_of_isCyclic_of_ker_le_center
    (by rw [hker]; exact hDc)
  exact hcomm.is_comm.comm a b

theorem commutator_mem_innerAut_of_equiv {K : Type} [Group K] (F : Type) [Field F] [Finite F]
    (hodd : IsOddPrimePower (Nat.card F)) (e : K ≃* PSL2 F) (x y : MulAut K) :
    x * y * x⁻¹ * y⁻¹ ∈ innerAut K := by
  have hcomm : ∀ a b : CFSG.ComponentClassification.OuterAutomorphisms.Outer K, a * b = b * a := by
    intro a b
    apply (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective
    rw [map_mul, map_mul]
    obtain ⟨a', ha'⟩ := (outerEquivSemilinearQuotient F).surjective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e a)
    obtain ⟨b', hb'⟩ := (outerEquivSemilinearQuotient F).surjective
      (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e b)
    rw [← ha', ← hb', ← map_mul, ← map_mul, semilinearQuotient_comm F hodd a' b']
  have h : (QuotientGroup.mk (x * y * x⁻¹ * y⁻¹) :
      CFSG.ComponentClassification.OuterAutomorphisms.Outer K) = 1 := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, hcomm (QuotientGroup.mk x) (QuotientGroup.mk y)]
    group
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner K :=
    (QuotientGroup.eq_one_iff _).1 h
  exact hmem

theorem input7_1OutL2_holds :
    ∀ (p : ℕ), p.Prime → 5 ≤ p → ∀ (K : Type) [Group K] [Finite K], IsLpType 2 (p ^ p) K →
      ∀ x y : MulAut K, x * y * x⁻¹ * y⁻¹ ∈ innerAut K := by
  intro p hp hp5 K _ _ hK x y
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := hK
  have hodd : IsOddPrimePower (Nat.card F) :=
    ⟨p, p, hp, hp.odd_of_ne_two (by omega), hp.one_lt.le, hcard⟩
  exact commutator_mem_innerAut_of_equiv F hodd
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm) x y

end OutL2

section Local

variable {G : Type} [Group G] [Finite G]

theorem oResidual_normalizer_ne_top {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}
    (h : Cex1310 G m p B M E A D T R L0 d) (h139a : Prop139a p M D)
    {U : Subgroup G} (hU : IsEkIn p 2 B U) (hUR : U ≤ centerOf R) {z : G} (hzU : z ∈ U)
    (hRB : R ≤ Subgroup.normalizer (B : Set G))
    (hzI : Subgroup.zpowers z = omegaOne p (R ⊓ Iof p M D)) {H : Subgroup G}
    (hNzH : ∀ x ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G),
      x ∈ Subgroup.normalizer (H : Set G))
    (hLp : IsLpType 2 (p ^ p) (barOf p H)) (hninner : ¬ InducesInner p H d) :
    CFSG.GH74.GLS.oResidual p ↥(Subgroup.normalizer ((kLowInfty R : Subgroup G) : Set G)) ≠ ⊤ := by
  have hβ : p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ m ≤ GLATwoLocalRank p G := h.standing.beta
  have hp : p.Prime := hβ.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := h139a.1
    have hne : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  have hBSC : IsSCp p ⊤ B := lemma23_proved G m p h.standing B h.bOne
  have hBR : B ≤ R := le_trans le_sup_right h.hR.2
  have hBK : B ≤ kLowInfty R :=
    le_kLowInfty (mem_Kfam_one hBR (fun a ha b hb => Lemma1315b.comm_of_mem hBSC.2.1 ha hb) hRB)
  have hZK : centerOf R ≤ kLowInfty R := centerOf_le_kLowInfty R
  have hKR : kLowInfty R ≤ R := kLowInfty_le R
  have hXB : omegaOne p (centerOf (kLowInfty R)) ≤ B := l1110_omegaOne_centerOf_le hBSC hBK
  have hUX : U ≤ omegaOne p (centerOf (kLowInfty R)) := fun u hu =>
    Subgroup.subset_closure ⟨Lemma1315.mem_centerOf_iff'.2 ⟨hZK (hUR hu),
      fun k hk => comm_of_mem_centerOf (hUR hu) (hKR hk)⟩, hU.2.1.2 u hu⟩
  have h2 : 2 ≤ CFSG.Open.pRank p (omegaOne p (centerOf (kLowInfty R))) :=
    CFSG.SectionRank.le_pRank hp.one_lt hUX hU.2.1 hU.2.2
  have hNXM : Subgroup.normalizer
      ((omegaOne p (centerOf (kLowInfty R)) : Subgroup G) : Set G) ≤ M := by
    have hmemS : Subgroup.normalizer
        ((omegaOne p (centerOf (kLowInfty R)) : Subgroup G) : Set G) ∈
        {N : Subgroup G | ∃ Q : Subgroup G, Q ≤ B ∧ 2 ≤ CFSG.Open.pRank p Q ∧
          N = Subgroup.normalizer (Q : Set G)} :=
      ⟨omegaOne p (centerOf (kLowInfty R)), hXB, h2, rfl⟩
    exact le_trans (le_sSup hmemS) h.uniq.clause_d
  have hXI : omegaOne p (centerOf (kLowInfty R)) ⊓ Iof p M D = Subgroup.zpowers z := by
    apply le_antisymm
    · intro x hx
      have hxB : x ∈ B := hXB hx.1
      have hxp : x ^ p = 1 := hBSC.2.1.2 x hxB
      rw [hzI]
      exact Subgroup.subset_closure ⟨⟨hBR hxB, hx.2⟩, hxp⟩
    · rw [Subgroup.zpowers_le]
      refine ⟨hUX hzU, ?_⟩
      have hz : z ∈ omegaOne p (R ⊓ Iof p M D) := by
        rw [← hzI]
        exact Subgroup.mem_zpowers z
      exact (omegaOne_le p (R ⊓ Iof p M D) hz).2
  have hKH : Subgroup.normalizer ((kLowInfty R : Subgroup G) : Set G) ≤
      Subgroup.normalizer (H : Set G) := by
    intro g hg
    apply hNzH
    have hgX : g ∈ Subgroup.normalizer
        ((omegaOne p (centerOf (kLowInfty R)) : Subgroup G) : Set G) :=
      Lemma1315.mem_normalizer_omegaOne hg
    have hgI : g ∈ Subgroup.normalizer ((Iof p M D : Subgroup G) : Set G) :=
      Lemma1315b.mem_normalizer_Iof h139a g (hNXM hgX)
    rw [← hXI]
    exact mem_normalizer_inf hgX hgI
  have hdR : d ∈ R := le_trans le_sup_left h.hR.2 (h.hD.1 h.hd.1)
  have hdK : d ∈ Subgroup.normalizer ((kLowInfty R : Subgroup G) : Set G) :=
    mem_normalizer_kLowInfty (Subgroup.le_normalizer hdR)
  have hdp : d ^ p = 1 := h.hD.2.1.2 d h.hd.1
  intro htop
  apply hninner
  have hdKp : (⟨d, hdK⟩ : ↥(Subgroup.normalizer ((kLowInfty R : Subgroup G) : Set G))) ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hdp
  have hcomm := mem_commutator_of_oResidual_eq_top htop (k := 1) (by rw [pow_one]; exact hdKp)
  let θ : ↥(Subgroup.normalizer ((kLowInfty R : Subgroup G) : Set G)) →* MulAut (barOf p H) :=
    (barAut p H).comp (Subgroup.inclusion hKH)
  have hθ : commutator ↥(Subgroup.normalizer ((kLowInfty R : Subgroup G) : Set G)) ≤
      (innerAut (barOf p H)).comap θ := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_comap, map_commutatorElement, commutatorElement_def]
    exact input7_1OutL2_holds p hp hp5 (barOf p H) hLp (θ a) (θ b)
  have hinn : θ ⟨d, hdK⟩ ∈ innerAut (barOf p H) := hθ hcomm
  have hθd : θ ⟨d, hdK⟩ = barAut p H ⟨d, hKH hdK⟩ := by
    simp only [θ, MonoidHom.coe_comp, Function.comp_apply]
    rfl
  rw [hθd] at hinn
  exact inducesInner_of_barAut_mem (hKH hdK) hinn

end Local

theorem localPFactor_of_inputs (h1312 : Lemma1312Statement) (h1314 : Lemma1314Statement)
    (h1315 : Lemma1315Statement) (hext : Lemma1315b.ExtrasStatement) :
    Lemma1316.LocalPFactorStatement := by
  intro G _ _ m p B M E A D T R L0 d h h139a
  obtain ⟨U, hU, hUR'⟩ := h1312 h
  have hUR : U ≤ centerOf R := hUR' h139a
  obtain ⟨z, hzU, hz1, H0, hH0, hH0M, hH0t⟩ := (h1314 h h139a).2.2.1 U hU hUR
  obtain ⟨⟨-, -, hLp, -, -, hninner⟩, -, hRB, hzI⟩ :=
    h1315 h h139a hU hUR ⟨hzU, hz1⟩ hH0 hH0M hH0t
  obtain ⟨-, -, -, hNzH, -⟩ := hext h h139a hU hUR ⟨hzU, hz1⟩ hH0 hH0M hH0t
  exact oResidual_normalizer_ne_top h h139a hU.1 hUR hzU hRB hzI hNzH hLp hninner

theorem lemma1316_of_transfer (h1312 : Lemma1312Statement) (hGT : GlaubermanTransfer)
    (hloc : Lemma1316.LocalPFactorStatement) : Lemma1316Statement := by
  intro G _ _ m p B M E A D T R L0 d h h139a
  obtain ⟨U, hU, hUR⟩ := h1312 h
  have hRG : IsSylowIn p ⊤ R := Lemma1315.sylow_of_central_rank_two h hU.1 (hUR h139a)
  have hβ : p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G ∧ m ≤ GLATwoLocalRank p G := h.standing.beta
  have hp : p.Prime := hβ.1
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := h139a.1
    have hne : p ≠ 4 := by
      rintro rfl
      exact absurd hp (by norm_num)
    omega
  haveI : IsSimpleGroup G := h.standing.simple
  have hG : CFSG.GH74.GLS.oResidual p G ≠ ⊤ := hGT G p hp hp5 R hRG (hloc h h139a)
  haveI : (CFSG.GH74.GLS.oResidual p G).Normal := Lemma1316.oResidual_normal p G
  have hbot : CFSG.GH74.GLS.oResidual p G = ⊥ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.GH74.GLS.oResidual p G)).resolve_right hG
  have hPG : IsPGroup p G := Lemma1316.isPGroup_of_oResidual_eq_bot hp hbot
  haveI : Fact p.Prime := ⟨hp⟩
  have hZbot : Subgroup.center G ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).1 hPG.center_nontrivial
  have hZtop : Subgroup.center G = ⊤ :=
    (IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G)).resolve_left hZbot
  obtain ⟨a, b, hab⟩ := h.standing.nonabelian
  have ha : a ∈ Subgroup.center G := by
    rw [hZtop]
    exact Subgroup.mem_top a
  exact hab ((Subgroup.mem_center_iff.1 ha b).symm)

theorem lemma1316_of_siblings (h1312 : Lemma1312Statement) (h1314 : Lemma1314Statement)
    (h1315 : Lemma1315Statement) (hext : Lemma1315b.ExtrasStatement)
    (hGT : GlaubermanTransfer) : Lemma1316Statement :=
  lemma1316_of_transfer h1312 hGT (localPFactor_of_inputs h1312 h1314 h1315 hext)

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1316

end
