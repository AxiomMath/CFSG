module

public import CFSG.HardMathSupport.Solomon.Coordinator.I10_21Reduce
public import CFSG.HardMathSupport.Solomon.Coordinator.I10_20
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CenterHopf
import CFSG.Quasithin.Background.G8Dihedral

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

open CFSG.Open Subgroup CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.Assembly.RankThreeEven (localRank)

section Witness

variable {X : Type} [Group X] [Finite X]

theorem le_twoLocalRank_of_witness {q n : ℕ} (hq : q.Prime) {S E : Subgroup X}
    (hS : IsPGroup 2 S) (hSne : S ≠ ⊥) (hES : E ≤ normalizer (S : Set X))
    (hE : IsElemAbelian q E) (hEc : Nat.card E = q ^ n) : n ≤ GLATwoLocalRank q X :=
  i1020_le_glaTwoLocalRank hq hS hSne hES hE hEc

theorem exists_witness_of_le {q n : ℕ} (hq : q.Prime) (hn : 0 < n)
    (h : n ≤ GLATwoLocalRank q X) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ S ≠ ⊥ ∧ ∃ E : Subgroup X, E ≤ normalizer (S : Set X) ∧
      IsElemAbelian q E ∧ Nat.card E = q ^ n := by
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨P, hP, hP2, hrk⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_twoLocal_of_le hq.one_lt hn h
  obtain ⟨E₀, hE₀N, hE₀, hE₀c⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (normalizer (P : Set X))
  obtain ⟨E, hEE₀, hE, hEc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hE₀
    (n := n) (by rw [hE₀c]; exact pow_dvd_pow q hrk)
  exact ⟨P, hP2, hP, E, hEE₀.trans hE₀N, hE, hEc⟩

end Witness

section Lift

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem exists_witness_caseA {X : Type} [Group X] [Finite X] {q n : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {V : Subgroup F} (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ (n + 1))
    (ψ : X →* F) (hψ : Function.Surjective ψ) (hY : IsPGroup q ψ.ker) (hYne : ψ.ker ≠ ⊥)
    (hC : centralizer (ψ.ker : Set X) ≤ ψ.ker) :
    ∃ S : Subgroup X, IsPGroup 2 S ∧ S ≠ ⊥ ∧ ∃ E : Subgroup X, E ≤ normalizer (S : Set X) ∧
      IsElemAbelian q E ∧ Nat.card E = q ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hY
  have hYodd : Odd (Nat.card ψ.ker) := by rw [ha]; exact (hq.odd_of_ne_two hq2).pow
  obtain ⟨T, -, hT, hTc⟩ := i1020_coprime_lift (p := 2) ψ ⊤
    (by rw [top_inf_eq]; exact hYodd.not_two_dvd_nat)
    (by rw [map_top_of_surjective ψ hψ]; exact le_top) hV hVc
  have hTY : T ⊓ ψ.ker = ⊥ := by
    rw [← disjoint_iff]
    refine disjoint_of_coprime_natCard ?_
    rw [hTc, ha]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hq).2 (Ne.symm hq2))
  have hfaith : T ⊓ centralizer (ψ.ker : Set X) = ⊥ :=
    le_bot_iff.1 (hTY ▸ inf_le_inf_left T hC)
  have h81 : CFSG.Quasithin.G81 ψ.ker T T :=
    ⟨hT, le_rfl, IsPGroup.of_card hTc, le_normalizer_of_normal, hY.isNilpotent, hYodd, hYne⟩
  obtain ⟨Hs, p, hDF, -, -, hx⟩ := CFSG.Quasithin.g8_6 h81 (Nat.succ_pos n) hTc hfaith
  choose x hxY hxH hxo using hx
  have hp : ∀ i, p i = q := by
    intro i
    obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.1 hY ⟨x i, hxY i⟩
    rw [orderOf_mk, hxo i] at hm
    have h1 : p i ∣ q ^ m := hm ▸ dvd_rfl
    exact (Nat.prime_dvd_prime_iff_eq (hDF.prime i) hq).1 ((hDF.prime i).dvd_of_dvd_pow h1)
  set i0 : Fin (n + 1) := 0
  obtain ⟨e⟩ := hDF.iso i0
  set t : X := (e.symm (DihedralGroup.sr 0) : X) with ht_def
  have ht : orderOf t = 2 := by
    rw [ht_def, orderOf_coe, MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have htH : t ∈ Hs i0 := (e.symm (DihedralGroup.sr 0)).2
  have hemb0 : ∀ j : Fin n, j.succ ≠ i0 := fun j => Fin.succ_ne_zero j
  obtain ⟨hE, hEc⟩ := i1020_family (fun j : Fin n => x j.succ) (fun j => (hxo _).trans (hp _))
    (fun j j' hjj' => hDF.commute _ _ (Fin.succ_injective _ |>.ne hjj') _ (hxH _) _ (hxH _))
    ((hDF.independent.comp (Fin.succ_injective _)).mono fun j => zpowers_le.2 (hxH j.succ))
  refine ⟨zpowers t, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one]), ?_,
    ⨆ j : Fin n, zpowers (x j.succ), ?_, hE, by rw [hEc, Fintype.card_fin]⟩
  · intro hbot
    have : t ∈ (⊥ : Subgroup X) := hbot ▸ mem_zpowers t
    rw [mem_bot] at this
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  · refine iSup_le fun j => zpowers_le.2 (centralizer_le_normalizer _ ?_)
    rw [mem_centralizer_iff]
    intro h hh
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 hh
    exact (Commute.zpow_left (hDF.commute _ _ (hemb0 j).symm t htH _ (hxH _)) m).eq

theorem exists_witness_of_surj (hnc : ∃ a b : F, a * b ≠ b * a) {q n : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hn : 0 < n) {V : Subgroup F} (hV : IsElemAbelian 2 V)
    (hVc : Nat.card V = 2 ^ (n + 1))
    (hcen : ∀ (L : Type) [Group L] [Finite L] (ψ : L →* F), Function.Surjective ψ →
      commutator L = ⊤ → ψ.ker ≤ center L → IsPGroup q ψ.ker → n ≤ GLATwoLocalRank q L) :
    ∀ (m : ℕ) (X : Type) [Group X] [Finite X], Nat.card X ≤ m → ∀ φ : X →* F,
      Function.Surjective φ → ∃ S : Subgroup X, IsPGroup 2 S ∧ S ≠ ⊥ ∧ ∃ E : Subgroup X,
        E ≤ normalizer (S : Set X) ∧ IsElemAbelian q E ∧ Nat.card E = q ^ n := by
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨a₀, b₀, hab₀⟩ := hnc
  have hF1 : ⁅(⊤ : Subgroup F), (⊤ : Subgroup F)⁆ = ⊤ := i1020_commutator_top ⟨a₀, b₀, hab₀⟩
  intro m
  induction m with
  | zero =>
    intro X _ _ hX
    have := Nat.card_pos (α := X)
    omega
  | succ m ih =>
    intro X _ _ hX φ hφ
    by_cases hYq : IsPGroup q φ.ker
    · by_cases hC : centralizer (φ.ker : Set X) ≤ φ.ker
      ·
        have hYne : φ.ker ≠ ⊥ := by
          intro hbot
          obtain ⟨a, ha⟩ := exists_ne (1 : F)
          obtain ⟨x, hx⟩ := hφ a
          have hx1 : x ∈ φ.ker := hC (by
            rw [hbot, mem_centralizer_iff]
            intro h hh
            rw [SetLike.mem_coe, mem_bot] at hh
            rw [hh, one_mul, mul_one])
          rw [MonoidHom.mem_ker, hx] at hx1
          exact ha hx1
        exact exists_witness_caseA hq hq2 hV hVc φ hφ hYq hYne hC
      ·
        set C : Subgroup X := centralizer (φ.ker : Set X) with hCdef
        have hCn : C.Normal := inferInstance
        have hCmap : C.map φ = ⊤ := by
          rcases (hCn.map φ hφ).eq_bot_or_eq_top with h | h
          · exact absurd ((Subgroup.map_eq_bot_iff C).1 h) hC
          · exact h
        obtain ⟨L, ⟨hLC, hLtop⟩, hLmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup X))
          {L : Subgroup X | L ≤ C ∧ L.map φ = ⊤} ⟨C, le_rfl, hCmap⟩
        have hcomm_le : ⁅L, L⁆ ≤ L := commutator_le.2 fun a ha b hb => by
          simp only [commutatorElement_def]
          exact L.mul_mem (L.mul_mem (L.mul_mem ha hb) (L.inv_mem ha)) (L.inv_mem hb)
        have hD : ⁅L, L⁆ = L := by
          by_contra hne
          refine hLmin ⁅L, L⁆ ⟨hcomm_le.trans hLC, ?_⟩ (lt_of_le_of_ne hcomm_le hne)
          rw [map_commutator, hLtop]
          exact hF1
        have hLperf : commutator ↥L = ⊤ := (Subgroup.isPerfect_iff.2 hD).commutator_eq_top
        set ψ : ↥L →* F := φ.comp L.subtype with hψdef
        have hψ : Function.Surjective ψ := by
          intro f
          have : f ∈ L.map φ := hLtop ▸ mem_top f
          obtain ⟨l, hl, hlf⟩ := mem_map.1 this
          exact ⟨⟨l, hl⟩, hlf⟩
        have hker : ∀ l : ↥L, l ∈ ψ.ker ↔ φ (l : X) = 1 := fun l => Iff.rfl
        have hcen' : ψ.ker ≤ center ↥L := by
          intro l hl
          rw [mem_center_iff]
          intro g
          have hlY : (l : X) ∈ φ.ker := (hker l).1 hl
          have hgC : (g : X) ∈ C := hLC g.2
          have := (mem_centralizer_iff.1 hgC) (l : X) hlY
          exact Subtype.ext this.symm
        have hpg : IsPGroup q ψ.ker := by
          rw [IsPGroup.iff_orderOf]
          intro g
          have hgY : ((g : ↥L) : X) ∈ φ.ker := (hker g).1 g.2
          obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hYq ⟨_, hgY⟩
          refine ⟨k, ?_⟩
          have e1 : orderOf g = orderOf (g : ↥L) := (Subgroup.orderOf_coe g).symm
          have e2 : orderOf (g : ↥L) = orderOf ((g : ↥L) : X) := (Subgroup.orderOf_coe _).symm
          have e3 : orderOf (⟨((g : ↥L) : X), hgY⟩ : φ.ker) = orderOf ((g : ↥L) : X) :=
            Subgroup.orderOf_mk _ _
          exact e1.trans (e2.trans (e3.symm.trans hk))
        obtain ⟨S, hS, hSne, E, hES, hE, hEc⟩ :=
          exists_witness_of_le hq hn (hcen ↥L ψ hψ hLperf hcen' hpg)
        obtain ⟨hS', hSne', hES', hE', hEc'⟩ :=
          i1020_map_witness L.subtype L.subtype_injective hS hES hE hEc
        exact ⟨_, hS', hSne' hSne, _, hES', hE', hEc'⟩
    ·
      obtain ⟨p, hp, hpq, hpY⟩ := i1021_exists_prime_ne hYq
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p φ.ker))
      set P' : Subgroup X := (P : Subgroup φ.ker).map φ.ker.subtype with hP'def
      have hfr : normalizer (P' : Set X) ⊔ φ.ker = ⊤ := Sylow.normalizer_sup_eq_top P
      have hP'Y : P' ≤ φ.ker := map_subtype_le _
      obtain ⟨m', hm⟩ := IsPGroup.iff_card.1 (P.isPGroup'.map φ.ker.subtype)
      have hP'q : ¬ q ∣ Nat.card P' := by
        rw [hm]
        intro h
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm
      by_cases htop : normalizer (P' : Set X) = ⊤
      ·
        have hP'n : P'.Normal := normalizer_eq_top_iff.1 htop
        have hP'ne : P' ≠ ⊥ :=
          (map_eq_bot_iff_of_injective _ φ.ker.subtype_injective).not.2
            (P.ne_bot_of_dvd_card hpY)
        have hlt : Nat.card (X ⧸ P') < Nat.card X := by
          rw [card_eq_card_quotient_mul_card_subgroup P']
          have h1 : 1 < Nat.card P' := (one_lt_card_iff_ne_bot P').2 hP'ne
          have h2 : 0 < Nat.card (X ⧸ P') := Nat.card_pos
          nlinarith
        have hsurj : Function.Surjective (QuotientGroup.lift P' φ hP'Y) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          exact ⟨x, rfl⟩
        obtain ⟨S, hS, hSne, E, hES, hE, hEc⟩ :=
          ih (X ⧸ P') (by omega) (QuotientGroup.lift P' φ hP'Y) hsurj
        obtain ⟨S₁, hS₁, hS₁ne, E₁, hE₁S₁, hE₁, hE₁c⟩ :=
          i1020_quotient_witness hq P' hP'q True ⟨S, hS, fun _ => hSne, E, hES, hE, hEc⟩
        exact ⟨S₁, hS₁, hS₁ne trivial, E₁, hE₁S₁, hE₁, hE₁c⟩
      ·
        set X₀ : Subgroup X := normalizer (P' : Set X)
        have hφ₀ : Function.Surjective (φ.comp X₀.subtype) := by
          intro f
          obtain ⟨x, rfl⟩ := hφ f
          have hx : x ∈ X₀ ⊔ φ.ker := hfr ▸ mem_top x
          obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_normal_right.1 hx
          refine ⟨⟨a, ha⟩, ?_⟩
          simp [MonoidHom.mem_ker.1 hb]
        have hlt : Nat.card X₀ < Nat.card X := by
          rw [← card_top (G := X)]
          exact card_lt_of_lt (lt_top_iff_ne_top.2 htop)
        obtain ⟨S, hS, hSne, E, hES, hE, hEc⟩ := ih X₀ (by omega) (φ.comp X₀.subtype) hφ₀
        obtain ⟨hS', hSne', hES', hE', hEc'⟩ :=
          i1020_map_witness X₀.subtype X₀.subtype_injective hS hES hE hEc
        exact ⟨_, hS', hSne' hSne, _, hES', hE', hEc'⟩

theorem le_twoLocalRank_of_surj (hnc : ∃ a b : F, a * b ≠ b * a) {q n : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) {V : Subgroup F} (hV : IsElemAbelian 2 V) (hVc : Nat.card V = 2 ^ (n + 1))
    (hcen : ∀ (L : Type) [Group L] [Finite L] (ψ : L →* F), Function.Surjective ψ →
      commutator L = ⊤ → ψ.ker ≤ center L → IsPGroup q ψ.ker → n ≤ GLATwoLocalRank q L)
    {X : Type} [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    n ≤ GLATwoLocalRank q X := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · rw [h0]
    exact Nat.zero_le _
  obtain ⟨S, hS, hSne, E, hES, hE, hEc⟩ :=
    exists_witness_of_surj hnc hq hq2 hn hV hVc hcen (Nat.card X) X le_rfl φ hφ
  exact le_twoLocalRank_of_witness hq hS hSne hES hE hEc

end Lift

section Transfer

variable {F : Type} [Group F] [Finite F] [IsSimpleGroup F]

theorem ker_eq_center_of_surj (hnc : ∃ a b : F, a * b ≠ b * a) {L : Type} [Group L]
    (ψ : L →* F) (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ center L) : ψ.ker = center L := by
  refine le_antisymm hker fun z hz => ?_
  have hZF : center F = ⊥ := i1021_center_eq_bot hnc
  have : ψ z ∈ center F := map_center_le_center hψ ⟨z, hz, rfl⟩
  rw [hZF, mem_bot] at this
  exact this

theorem injective_of_cover_of_multiplier (hnc : ∃ a b : F, a * b ≠ b * a) {q : ℕ}
    (hq : q.Prime) (hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier F)) {L : Type}
    [Group L] [Finite L] (ψ : L →* F) (hψ : Function.Surjective ψ) (hperf : commutator L = ⊤)
    (hker : ψ.ker ≤ center L) (hpg : IsPGroup q ψ.ker) : Function.Injective ψ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hZ := ker_eq_center_of_surj hnc ψ hψ hker
  let e₁ : L ⧸ center L ≃* F :=
    (QuotientGroup.quotientMulEquivOfEq hZ.symm).trans (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hdvd := CFSG.AGLEmbedding.card_center_dvd_card_griessHopfMultiplier
    ⟨hperf⟩ e₁
  rw [← hZ] at hdvd
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hpg
  have hk0 : k = 0 := by
    by_contra hk0
    exact hM ((dvd_pow_self q hk0).trans (hk ▸ hdvd))
  rw [hk0, pow_zero] at hk
  rw [← MonoidHom.ker_eq_bot_iff]
  exact Subgroup.eq_bot_of_card_eq _ hk

theorem twoLocalRank_cover_of_multiplier (hnc : ∃ a b : F, a * b ≠ b * a) {q n : ℕ}
    (hq : q.Prime) (hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier F))
    (hF : n ≤ GLATwoLocalRank q F) :
    ∀ (L : Type) [Group L] [Finite L] (ψ : L →* F), Function.Surjective ψ →
      commutator L = ⊤ → ψ.ker ≤ center L → IsPGroup q ψ.ker → n ≤ GLATwoLocalRank q L := by
  intro L _ _ ψ hψ hperf hker hpg
  have hinj := injective_of_cover_of_multiplier hnc hq hM ψ hψ hperf hker hpg
  have e : L ≃* F := MulEquiv.ofBijective ψ ⟨hinj, hψ⟩
  change n ≤ localRank q L
  rw [CFSG.RankThree.PartTwo.Census.localRank_eq_of_mulEquiv e hq]
  exact hF

theorem pRank_cover_of_multiplier (hnc : ∃ a b : F, a * b ≠ b * a) {q r : ℕ} (hq : q.Prime)
    (hM : ¬ q ∣ Nat.card (CFSG.Open.griessHopfMultiplier F))
    (hF : r ≤ CFSG.Open.pRank q (⊤ : Subgroup F)) :
    ∀ (L : Type) [Group L] [Finite L] (ψ : L →* F), Function.Surjective ψ →
      commutator L = ⊤ → ψ.ker ≤ center L → IsPGroup q ψ.ker →
        r ≤ CFSG.Open.pRank q (⊤ : Subgroup L) := by
  intro L _ _ ψ hψ hperf hker hpg
  have hinj := injective_of_cover_of_multiplier hnc hq hM ψ hψ hperf hker hpg
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hq.one_lt (MulEquiv.ofBijective ψ ⟨hinj, hψ⟩)]
  exact hF

end Transfer

theorem le_twoLocalRank_of_section {F : Type} [Group F] {q r : ℕ} (hq : q.Prime)
    {J U₀ : Subgroup F} (hU₀ : IsPGroup 2 U₀) (hU₀ne : U₀ ≠ ⊥)
    (hJU : J ≤ normalizer (U₀ : Set F))
    (hJ : ∀ (X' : Type) [Group X'] [Finite X'] (φ' : X' →* J), Function.Surjective φ' →
      r ≤ CFSG.Open.pRank q (⊤ : Subgroup X'))
    {X : Type} [Group X] [Finite X] (φ : X →* F) (hφ : Function.Surjective φ) :
    r ≤ GLATwoLocalRank q X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U, hU, hUmap, hN⟩ := i1020_frattini_lift φ hφ hU₀
  have hUne : U ≠ ⊥ := fun h => hU₀ne (by rw [← hUmap, h, Subgroup.map_bot])
  set H₁ : Subgroup X := normalizer (U : Set X) ⊓ J.comap φ with hH₁
  let ψ : ↥H₁ →* ↥J := (φ.comp H₁.subtype).codRestrict J fun x => x.2.2
  have hψ : Function.Surjective ψ := by
    intro j
    obtain ⟨x, hxN, hxj⟩ := hN (hJU j.2)
    have hxH : x ∈ H₁ := ⟨hxN, show φ x ∈ J by rw [hxj]; exact j.2⟩
    exact ⟨⟨x, hxH⟩, Subtype.ext hxj⟩
  have hr := hJ ↥H₁ ψ hψ
  obtain ⟨E₀, -, hE₀, hE₀c⟩ := CFSG.SectionRank.exists_pRank hq.one_lt (⊤ : Subgroup ↥H₁)
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨E, -, hE, hEc⟩ := CFSG.LocalAnalysis.GLTheoremB.exists_le_isElemAbelian_card hE₀
    (n := r) (by rw [hE₀c]; exact pow_dvd_pow q hr)
  refine le_twoLocalRank_of_witness hq hU hUne (E := E.map H₁.subtype) ?_
    (CFSG.SectionRank.isElemAbelian_map hE _) ?_
  · rintro _ ⟨x, -, rfl⟩
    exact x.2.1
  · rw [Subgroup.card_map_of_injective H₁.subtype_injective, hEc]

end CFSG.LocalAnalysis.GLTheoremA.S267.HqRank

end
